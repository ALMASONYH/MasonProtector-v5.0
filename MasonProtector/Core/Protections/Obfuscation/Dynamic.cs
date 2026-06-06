using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using dnlib.DotNet;
using dnlib.DotNet.Emit;

using DnFieldAttributes = dnlib.DotNet.FieldAttributes;
using DnMethodAttributes = dnlib.DotNet.MethodAttributes;
using DnMethodImplAttributes = dnlib.DotNet.MethodImplAttributes;
using DnTypeAttributes = dnlib.DotNet.TypeAttributes;
using DnOpCodes = dnlib.DotNet.Emit.OpCodes;

namespace MasonProtector.Core
{

    internal class DynamicProtection
    {
        private Obfuscation engine;
        private Random rng;

        internal DynamicProtection(Obfuscation eng)
        {
            engine = eng;
            rng = eng.rng;
        }

        private struct SlotEntry
        {
            internal int RawSlot;
            internal IMethod Target;
            internal MethodSig Sig;
        }

        internal void ApplyDynamic(ModuleDef module, TypeDef modType)
        {
            engine.activeOption = "Dynamic";

            var dispatchType = new TypeDefUser("", engine.MakeName(),
                module.CorLibTypes.Object.TypeDefOrRef);
            dispatchType.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
            module.Types.Add(dispatchType);
            engine.injectedTypes.Add(dispatchType);

            var slotEntries = new List<SlotEntry>();
            var targetKeyToSlot = new Dictionary<string, int>(StringComparer.Ordinal);
            var proxyBySlot = new Dictionary<int, MethodDef>();
            var proxySigBySlot = new Dictionary<int, MethodSig>();

            var newObjFactoryCache = new Dictionary<string, MethodDef>(StringComparer.Ordinal);

            foreach (TypeDef type in module.GetTypes())
            {
                if (type == dispatchType) continue;
                if (engine.IsCompilerGenerated(type)) continue;
                if (engine.injectedTypes.Contains(type)) continue;
                if (engine.IsTypeUserExcluded(type)) continue;
                foreach (MethodDef method in type.Methods)
                {
                    if (!IsEligible(method)) continue;
                    if (engine.MethodHasAsyncOrIteratorAttribute(method)) continue;
                    if (!engine.LevelCoverMethod(method)) continue;
                    try
                    {
                        RewriteMethod(module, method, dispatchType,
                            slotEntries, targetKeyToSlot, proxyBySlot, proxySigBySlot,
                            newObjFactoryCache);
                    }
                    catch { }
                }
            }

            if (slotEntries.Count == 0) return;

            BuildSharedInfrastructure(module, dispatchType, slotEntries,
                proxyBySlot, proxySigBySlot);
        }

        private bool IsEligible(MethodDef m)
        {
            if (m == null) return false;
            if (!m.HasBody || !m.Body.HasInstructions) return false;
            if (engine.injectedMethods.Contains(m)) return false;
            if (engine.IsMethodUserExcluded(m)) return false;
            if (m.IsRuntimeSpecialName && !m.IsStaticConstructor) return false;
            if (m.HasGenericParameters) return false;
            if (m.DeclaringType != null && m.DeclaringType.HasGenericParameters) return false;
            if (m.Name == "Create__Instance__" || m.Name == "Dispose__Instance__") return false;
            return true;
        }

        private static bool IsKnownSafeExternalType(string ns, string nm)
        {
            if (ns == "System.Text" && (nm == "StringBuilder" || nm == "Encoding" || nm == "UTF8Encoding"))
                return true;
            if (ns == "System.IO" && (nm == "StreamReader" || nm == "StreamWriter" ||
                nm == "MemoryStream" || nm == "StringReader" || nm == "StringWriter" ||
                nm == "BinaryReader" || nm == "BinaryWriter"))
                return true;
            if (ns == "System.Collections.Generic" &&
                (nm == "List`1" || nm == "Dictionary`2" || nm == "HashSet`1" || nm == "Queue`1" || nm == "Stack`1"))
                return true;
            if (ns == "System.Collections" && (nm == "ArrayList" || nm == "Hashtable"))
                return true;
            return false;
        }

        private static bool IsKnownValueType(string ns, string nm)
        {
            if (ns == "System")
            {
                switch (nm)
                {
                    case "Int32": case "Int64": case "Int16": case "Byte": case "SByte":
                    case "UInt32": case "UInt64": case "UInt16": case "Char": case "Boolean":
                    case "Single": case "Double": case "Decimal": case "IntPtr": case "UIntPtr":
                    case "DateTime": case "TimeSpan": case "Guid": case "DateTimeOffset":
                    case "Nullable`1": case "ValueType": case "Enum":
                        return true;
                }
            }
            if (ns == "System.Drawing")
            {
                switch (nm)
                {
                    case "Color": case "Point": case "PointF": case "Size": case "SizeF":
                    case "Rectangle": case "RectangleF":
                        return true;
                }
            }
            if (ns == "System.Windows.Forms")
            {
                switch (nm)
                {
                    case "Padding": case "Message": case "TableLayoutPanelCellPosition":
                        return true;
                }
            }
            return false;
        }

        private MethodSig BuildStaticSigForTarget(ModuleDef module, IMethod target, bool hasThis,
            out TypeSig receiverType)
        {
            receiverType = null;
            var targetSig = target.MethodSig;
            if (targetSig == null) return null;
            if (targetSig.GenParamCount > 0) return null;

            if (targetSig.RetType != null && (targetSig.RetType.IsByRef || targetSig.RetType.IsPointer))
                return null;
            foreach (var p in targetSig.Params)
            {
                if (p == null || p.IsByRef || p.IsPointer) return null;
            }

            var cc = targetSig.CallingConvention & dnlib.DotNet.CallingConvention.Mask;
            if (cc == dnlib.DotNet.CallingConvention.VarArg || cc == dnlib.DotNet.CallingConvention.NativeVarArg)
                return null;

            if (hasThis)
            {
                var declType = target.DeclaringType;
                if (declType == null) return null;
                TypeDef td = null;
                try { td = declType.ResolveTypeDef(); } catch { }
                if (td != null)
                {
                    if (td.IsValueType) return null;
                    if (td.HasGenericParameters) return null;
                    if (td.Module != null && td.Module != module)
                    {
                        string extNs = td.Namespace?.String ?? "";
                        string extNm = td.Name?.String ?? "";
                        if (!IsKnownSafeExternalType(extNs, extNm)) return null;
                    }
                }
                else
                {
                    var tr = declType as TypeRef;
                    if (tr == null) return null;
                    string ns2 = tr.Namespace?.String ?? "";
                    string nm2 = tr.Name?.String ?? "";
                    if (nm2.Contains("`")) return null;
                    if (IsKnownValueType(ns2, nm2)) return null;
                    if (!IsKnownSafeExternalType(ns2, nm2)) return null;
                }

                try { receiverType = module.Import(declType.ToTypeSig()); } catch { return null; }
                if (receiverType == null) return null;

                if (targetSig.Params.Count + 1 > 4) return null;

                var allParams = new TypeSig[1 + targetSig.Params.Count];
                allParams[0] = receiverType;
                for (int pi = 0; pi < targetSig.Params.Count; pi++)
                    allParams[pi + 1] = targetSig.Params[pi];

                return MethodSig.CreateStatic(targetSig.RetType, allParams);
            }
            else
            {
                if (targetSig.Params.Count > 4) return null;
                return MethodSig.CreateStatic(targetSig.RetType, targetSig.Params.ToArray());
            }
        }

        private MethodDef BuildNewObjFactory(ModuleDef module, TypeDef dispatchType, IMethod target)
        {
            if (target == null || target.DeclaringType == null) return null;
            var sig = target.MethodSig;
            if (sig == null) return null;
            if (sig.Params.Count > 4) return null;

            TypeSig retType;
            try
            {
                var imported = module.Import(target.DeclaringType);
                var asDefOrRef = imported as ITypeDefOrRef;
                if (asDefOrRef == null) return null;
                retType = asDefOrRef.ToTypeSig();
            }
            catch { return null; }
            if (retType == null) return null;

            var factorySig = MethodSig.CreateStatic(retType, sig.Params.ToArray());
            var factory = new MethodDefUser(engine.MakeName(), factorySig,
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed |
                DnMethodImplAttributes.NoInlining,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            factory.Body = new CilBody();
            var fil = factory.Body.Instructions;

            for (int pi = 0; pi < sig.Params.Count; pi++)
            {
                switch (pi) {
                    case 0: fil.Add(Instruction.Create(DnOpCodes.Ldarg_0)); break;
                    case 1: fil.Add(Instruction.Create(DnOpCodes.Ldarg_1)); break;
                    case 2: fil.Add(Instruction.Create(DnOpCodes.Ldarg_2)); break;
                    case 3: fil.Add(Instruction.Create(DnOpCodes.Ldarg_3)); break;
                }
            }
            fil.Add(Instruction.Create(DnOpCodes.Newobj, module.Import(target)));
            fil.Add(Instruction.Create(DnOpCodes.Ret));

            dispatchType.Methods.Add(factory);
            engine.injectedMethods.Add(factory);
            return factory;
        }

        private void RewriteMethod(ModuleDef module, MethodDef method,
            TypeDef dispatchType,
            List<SlotEntry> slotEntries,
            Dictionary<string, int> targetKeyToSlot,
            Dictionary<int, MethodDef> proxyBySlot,
            Dictionary<int, MethodSig> proxySigBySlot,
            Dictionary<string, MethodDef> newObjFactoryCache = null)
        {
            var il = method.Body.Instructions;
            for (int i = 0; i < il.Count; i++)
            {
                bool isCall     = il[i].OpCode == DnOpCodes.Call;
                bool isCallvirt = il[i].OpCode == DnOpCodes.Callvirt;
                bool isNewObj   = il[i].OpCode == DnOpCodes.Newobj;
                if (!isCall && !isCallvirt && !isNewObj) continue;

                if (i > 0 && il[i - 1].OpCode == DnOpCodes.Constrained) continue;

                if (isNewObj)
                {
                    if (newObjFactoryCache == null) continue;
                    var newobjTarget = il[i].Operand as IMethod;
                    if (newobjTarget == null) continue;
                    if (engine.IsCompilerInfrastructureCall(newobjTarget)) continue;
                    if (engine.IsCompilerGeneratedOwner(newobjTarget)) continue;
                    var newobjSig = newobjTarget.MethodSig;
                    if (newobjSig == null || newobjSig.GenParamCount > 0) continue;
                    if (!engine.IsConfirmedReferenceTypeCtor(newobjTarget.DeclaringType)) continue;

                    string factKey = "DYN-NEW:" + newobjTarget.FullName;
                    MethodDef factMethod;
                    if (!newObjFactoryCache.TryGetValue(factKey, out factMethod))
                    {
                        factMethod = BuildNewObjFactory(module, dispatchType, newobjTarget);
                        if (factMethod == null) continue;
                        newObjFactoryCache[factKey] = factMethod;
                    }

                    il[i].OpCode = DnOpCodes.Call;
                    il[i].Operand = factMethod;
                    continue;
                }

                var target = il[i].Operand as IMethod;
                if (target == null) continue;
                if (engine.IsCompilerInfrastructureCall(target)) continue;
                if (engine.IsCompilerGeneratedOwner(target)) continue;
                MethodDef mdCheck = target as MethodDef;
                if (mdCheck != null && engine.injectedMethods.Contains(mdCheck)) continue;

                if (target.Name == ".ctor" || target.Name == ".cctor") continue;

                var targetSig = target.MethodSig;
                if (targetSig == null) continue;
                if (targetSig.GenParamCount > 0) continue;

                bool hasThis = targetSig.HasThis;

                if (target.DeclaringType != null)
                {
                    var dn = target.DeclaringType.FullName;
                    if (dn == "System.RuntimeMethodHandle" || dn == "System.RuntimeTypeHandle") continue;
                    TypeDef dtd = null;
                    try { dtd = target.DeclaringType.ResolveTypeDef(); } catch { }
                    if (dtd != null && dtd.HasGenericParameters) continue;
                }

                if (hasThis && isCallvirt)
                {
                    MethodDef mdResolved = null;
                    try { mdResolved = target.ResolveMethodDef(); } catch { }
                    if (mdResolved == null) continue;
                    if (mdResolved.IsVirtual && !mdResolved.IsFinal && !mdResolved.IsAbstract)
                    {
                        bool typeFinal = mdResolved.DeclaringType != null && mdResolved.DeclaringType.IsSealed;
                        if (!typeFinal) continue;
                    }
                }

                TypeSig receiverType;
                MethodSig proxySig = BuildStaticSigForTarget(module, target, hasThis, out receiverType);
                if (proxySig == null) continue;

                string cacheKey = (hasThis ? "I:" : "S:") + target.FullName;
                int rawSlot;
                MethodDef proxy;

                if (!targetKeyToSlot.TryGetValue(cacheKey, out rawSlot))
                {
                    rawSlot = slotEntries.Count;
                    slotEntries.Add(new SlotEntry { RawSlot = rawSlot, Target = target, Sig = proxySig });
                    targetKeyToSlot[cacheKey] = rawSlot;

                    proxy = BuildStubProxy(module, dispatchType, proxySig, rawSlot);
                    if (proxy == null) { slotEntries.RemoveAt(rawSlot); targetKeyToSlot.Remove(cacheKey); continue; }

                    proxyBySlot[rawSlot] = proxy;
                    proxySigBySlot[rawSlot] = proxySig;
                }
                else
                {
                    if (!proxyBySlot.TryGetValue(rawSlot, out proxy) || proxy == null) continue;
                }

                il[i].OpCode = DnOpCodes.Call;
                il[i].Operand = proxy;
            }
        }

        private MethodDef BuildStubProxy(ModuleDef module, TypeDef dispatchType,
            MethodSig targetSig, int rawSlot)
        {
            if (targetSig == null) return null;

            var proxySig = MethodSig.CreateStatic(targetSig.RetType, targetSig.Params.ToArray());
            var proxy = new MethodDefUser(engine.MakeName(), proxySig,
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed |
                DnMethodImplAttributes.NoInlining,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            proxy.Body = new CilBody();
            proxy.Body.InitLocals = true;
            proxy.Body.Variables.Add(new Local(module.CorLibTypes.IntPtr));

            var pil = proxy.Body.Instructions;
            pil.Add(Instruction.Create(DnOpCodes.Ldc_I4, rawSlot));
            pil.Add(Instruction.Create(DnOpCodes.Ret));

            dispatchType.Methods.Add(proxy);
            engine.injectedMethods.Add(proxy);
            return proxy;
        }

        private void BuildSharedInfrastructure(ModuleDef module, TypeDef dispatchType,
            List<SlotEntry> slots,
            Dictionary<int, MethodDef> proxyBySlot,
            Dictionary<int, MethodSig> proxySigBySlot)
        {
            int n = slots.Count;

            var ptrCacheField = new FieldDefUser(engine.MakeName(),
                new FieldSig(new SZArraySig(module.CorLibTypes.IntPtr)),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            dispatchType.Fields.Add(ptrCacheField);

            var encTableField = new FieldDefUser(engine.MakeName(),
                new FieldSig(new SZArraySig(module.CorLibTypes.Int32)),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            dispatchType.Fields.Add(encTableField);

            int[] perEntryKeys = new int[n];
            int[] encValues = new int[n];
            for (int i = 0; i < n; i++)
            {
                perEntryKeys[i] = rng.Next(0x1000, int.MaxValue / 2);
                encValues[i] = i ^ perEntryKeys[i];
            }

            var keyTableField = new FieldDefUser(engine.MakeName(),
                new FieldSig(new SZArraySig(module.CorLibTypes.Int32)),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            dispatchType.Fields.Add(keyTableField);

            int seedFieldVal = rng.Next(0x10000, int.MaxValue / 2);
            var seedField = new FieldDefUser(engine.MakeName(),
                new FieldSig(module.CorLibTypes.Int32),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            dispatchType.Fields.Add(seedField);

            var switchResolver = BuildSwitchResolver(module, dispatchType, slots);

            var sharedResolver = BuildSharedResolver(module, dispatchType,
                ptrCacheField, encTableField, keyTableField, seedField, switchResolver);

            RewireProxies(module, proxyBySlot, proxySigBySlot, sharedResolver, seedFieldVal);

            BuildCctor(module, dispatchType, ptrCacheField, encTableField, keyTableField,
                seedField, encValues, perEntryKeys, seedFieldVal, n);
        }

        private MethodDef BuildSwitchResolver(ModuleDef module, TypeDef dispatchType,
            List<SlotEntry> slots)
        {
            int n = slots.Count;
            var sig = MethodSig.CreateStatic(module.CorLibTypes.IntPtr, module.CorLibTypes.Int32);
            var m = new MethodDefUser(engine.MakeName(), sig,
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed |
                DnMethodImplAttributes.NoInlining,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            m.Body = new CilBody();
            m.Body.InitLocals = true;
            m.Body.Variables.Add(new Local(module.CorLibTypes.IntPtr));

            var il = m.Body.Instructions;

            var retLbl = Instruction.Create(DnOpCodes.Ldloc_0);
            var defaultLbl = Instruction.Create(DnOpCodes.Ldc_I4_0);

            Instruction[] caseLabels = new Instruction[n];
            for (int i = 0; i < n; i++)
                caseLabels[i] = Instruction.Create(DnOpCodes.Nop);

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(new Instruction(DnOpCodes.Switch, caseLabels));
            il.Add(Instruction.Create(DnOpCodes.Br, defaultLbl));

            for (int i = 0; i < n; i++)
            {
                il.Add(caseLabels[i]);
                il.Add(Instruction.Create(DnOpCodes.Ldftn, module.Import(slots[i].Target)));
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                il.Add(Instruction.Create(DnOpCodes.Br, retLbl));
            }

            il.Add(defaultLbl);
            il.Add(Instruction.Create(DnOpCodes.Conv_I));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));

            il.Add(retLbl);
            il.Add(Instruction.Create(DnOpCodes.Ret));

            dispatchType.Methods.Add(m);
            engine.injectedMethods.Add(m);
            return m;
        }

        private MethodDef BuildSharedResolver(ModuleDef module, TypeDef dispatchType,
            FieldDef ptrCacheField, FieldDef encTableField, FieldDef keyTableField,
            FieldDef seedField, MethodDef switchResolver)
        {
            var sig = MethodSig.CreateStatic(module.CorLibTypes.IntPtr, module.CorLibTypes.Int32);
            var m = new MethodDefUser(engine.MakeName(), sig,
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed |
                DnMethodImplAttributes.NoInlining,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            m.Body = new CilBody();
            m.Body.InitLocals = true;

            m.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            m.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            m.Body.Variables.Add(new Local(module.CorLibTypes.IntPtr));

            var il = m.Body.Instructions;

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldsfld, seedField));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));

            var haveFp = Instruction.Create(DnOpCodes.Ldloc_2);

            il.Add(Instruction.Create(DnOpCodes.Ldsfld, ptrCacheField));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I));
            il.Add(Instruction.Create(DnOpCodes.Stloc_2));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_2));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Conv_I));
            il.Add(Instruction.Create(DnOpCodes.Bne_Un, haveFp));

            il.Add(Instruction.Create(DnOpCodes.Ldsfld, encTableField));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Ldsfld, keyTableField));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Call, switchResolver));
            il.Add(Instruction.Create(DnOpCodes.Stloc_2));

            il.Add(Instruction.Create(DnOpCodes.Ldsfld, ptrCacheField));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_2));
            il.Add(Instruction.Create(DnOpCodes.Stelem_I));

            il.Add(haveFp);
            il.Add(Instruction.Create(DnOpCodes.Ret));

            dispatchType.Methods.Add(m);
            engine.injectedMethods.Add(m);
            return m;
        }

        private void RewireProxies(ModuleDef module,
            Dictionary<int, MethodDef> proxyBySlot,
            Dictionary<int, MethodSig> proxySigBySlot,
            MethodDef sharedResolver,
            int seedFieldVal)
        {
            foreach (var kv in proxyBySlot)
            {
                int rawSlot = kv.Key;
                var proxy = kv.Value;
                if (proxy == null) continue;

                MethodSig targetSig;
                if (!proxySigBySlot.TryGetValue(rawSlot, out targetSig) || targetSig == null) continue;

                int encodedSlot = rawSlot ^ seedFieldVal;

                var il = proxy.Body.Instructions;
                il.Clear();
                proxy.Body.Variables.Clear();
                proxy.Body.Variables.Add(new Local(module.CorLibTypes.IntPtr));

                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, encodedSlot));
                il.Add(Instruction.Create(DnOpCodes.Call, sharedResolver));
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));

                int paramCount = targetSig.Params.Count;
                for (int i = 0; i < paramCount; i++)
                {
                    switch (i)
                    {
                        case 0: il.Add(Instruction.Create(DnOpCodes.Ldarg_0)); break;
                        case 1: il.Add(Instruction.Create(DnOpCodes.Ldarg_1)); break;
                        case 2: il.Add(Instruction.Create(DnOpCodes.Ldarg_2)); break;
                        case 3: il.Add(Instruction.Create(DnOpCodes.Ldarg_3)); break;
                    }
                }

                il.Add(Instruction.Create(DnOpCodes.Ldloc_0));

                var calliSig = MethodSig.CreateStatic(targetSig.RetType, targetSig.Params.ToArray());
                calliSig.CallingConvention = CallingConvention.Default;
                il.Add(new Instruction(DnOpCodes.Calli, calliSig));
                il.Add(Instruction.Create(DnOpCodes.Ret));
            }
        }

        private void BuildCctor(ModuleDef module, TypeDef dispatchType,
            FieldDef ptrCacheField, FieldDef encTableField, FieldDef keyTableField,
            FieldDef seedField, int[] encValues, int[] perEntryKeys, int seedFieldVal, int n)
        {
            var importer = new Importer(module);
            ITypeDefOrRef sysValueType = importer.Import(typeof(ValueType));
            IMethod rhInitArr = importer.Import(typeof(RuntimeHelpers)
                .GetMethod("InitializeArray",
                    new Type[] { typeof(Array), typeof(RuntimeFieldHandle) }));

            var cctorSig = MethodSig.CreateStatic(module.CorLibTypes.Void);
            var cctor = new MethodDefUser(".cctor", cctorSig,
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Private | DnMethodAttributes.Static |
                DnMethodAttributes.HideBySig | DnMethodAttributes.SpecialName |
                DnMethodAttributes.RTSpecialName);
            cctor.Body = new CilBody();
            cctor.Body.InitLocals = true;

            var il = cctor.Body.Instructions;

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, n));
            il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.IntPtr.ToTypeDefOrRef()));
            il.Add(Instruction.Create(DnOpCodes.Stsfld, ptrCacheField));

            EmitMaskedRvaArrayInit(module, dispatchType, cctor, il,
                encValues, n, encTableField, sysValueType, rhInitArr);

            EmitMaskedRvaArrayInit(module, dispatchType, cctor, il,
                perEntryKeys, n, keyTableField, sysValueType, rhInitArr);

            int seedMask = rng.Next(int.MinValue, int.MaxValue);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, seedFieldVal ^ seedMask));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, seedMask));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stsfld, seedField));

            il.Add(Instruction.Create(DnOpCodes.Ret));

            dispatchType.Methods.Add(cctor);
            engine.injectedMethods.Add(cctor);
        }

        private void EmitMaskedRvaArrayInit(ModuleDef module, TypeDef host,
            MethodDef cctor, IList<Instruction> il,
            int[] values, int n, FieldDef targetField,
            ITypeDefOrRef sysValueType, IMethod rhInitArr)
        {
            int seed = rng.Next(1, int.MaxValue);
            int[] masked = MaskInt32Array(values, seed);
            byte[] maskedBytes = Int32ArrayToLittleEndianBytes(masked);
            FieldDef rvaField = MakeRvaField(module, host, sysValueType, maskedBytes);

            var varArr = new Local(new SZArraySig(module.CorLibTypes.Int32));
            var varIdx = new Local(module.CorLibTypes.Int32);
            var varState = new Local(module.CorLibTypes.Int32);
            cctor.Body.Variables.Add(varArr);
            cctor.Body.Variables.Add(varIdx);
            cctor.Body.Variables.Add(varState);

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, n));
            il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.Int32.ToTypeDefOrRef()));
            il.Add(Instruction.Create(DnOpCodes.Dup));
            il.Add(Instruction.Create(DnOpCodes.Ldtoken, rvaField));
            il.Add(Instruction.Create(DnOpCodes.Call, rhInitArr));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varArr));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, seed));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varState));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varIdx));

            var loopCond = Instruction.Create(DnOpCodes.Ldloc, varIdx);
            var loopBody = Instruction.Create(DnOpCodes.Ldloc, varState);
            il.Add(Instruction.Create(DnOpCodes.Br, loopCond));

            il.Add(loopBody);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 1664525));
            il.Add(Instruction.Create(DnOpCodes.Mul));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 1013904223));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varState));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varArr));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varIdx));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varArr));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varIdx));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varState));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stelem_I4));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varIdx));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varIdx));

            il.Add(loopCond);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, n));
            il.Add(Instruction.Create(DnOpCodes.Blt, loopBody));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varArr));
            il.Add(Instruction.Create(DnOpCodes.Stsfld, targetField));
        }

        private static int[] MaskInt32Array(int[] values, int seed)
        {
            int[] masked = new int[values.Length];
            int state = seed;
            for (int i = 0; i < values.Length; i++)
            {
                state = unchecked(state * 1664525 + 1013904223);
                masked[i] = values[i] ^ state;
            }
            return masked;
        }

        private static byte[] Int32ArrayToLittleEndianBytes(int[] values)
        {
            byte[] bytes = new byte[values.Length * 4];
            for (int i = 0; i < values.Length; i++)
            {
                int v = values[i];
                bytes[i * 4 + 0] = (byte)(v & 0xFF);
                bytes[i * 4 + 1] = (byte)((v >> 8) & 0xFF);
                bytes[i * 4 + 2] = (byte)((v >> 16) & 0xFF);
                bytes[i * 4 + 3] = (byte)((v >> 24) & 0xFF);
            }
            return bytes;
        }

        private FieldDef MakeRvaField(ModuleDef module, TypeDef host, ITypeDefOrRef sysValueType, byte[] data)
        {
            string holderName = engine.MakeName();
            TypeDef holder = new TypeDefUser("", holderName, sysValueType);
            holder.Attributes = DnTypeAttributes.NestedPrivate
                              | DnTypeAttributes.SequentialLayout
                              | DnTypeAttributes.Sealed;
            holder.ClassLayout = new ClassLayoutUser(1, (uint)data.Length);
            host.NestedTypes.Add(holder);
            engine.injectedTypes.Add(holder);

            FieldDef rvaField = new FieldDefUser(engine.MakeName(),
                new FieldSig(holder.ToTypeSig()),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static
                | DnFieldAttributes.HasFieldRVA);
            rvaField.HasFieldRVA = true;
            rvaField.InitialValue = (byte[])data.Clone();
            host.Fields.Add(rvaField);

            return rvaField;
        }
    }
}
