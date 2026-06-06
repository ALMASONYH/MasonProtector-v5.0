using System;
using System.Collections.Generic;
using System.Linq;
using dnlib.DotNet;
using dnlib.DotNet.Emit;

using DnMethodAttributes = dnlib.DotNet.MethodAttributes;
using DnMethodImplAttributes = dnlib.DotNet.MethodImplAttributes;
using DnTypeAttributes = dnlib.DotNet.TypeAttributes;
using DnOpCodes = dnlib.DotNet.Emit.OpCodes;

namespace MasonProtector.Core
{
    internal class ProxyCallsProtection
    {
        private Obfuscation engine;
        private Random rng;

        internal ProxyCallsProtection(Obfuscation eng)
        {
            engine = eng;
            rng = eng.rng;
        }

        internal void ApplyProxyCalls(ModuleDef module)
        {
            const int HOST_COUNT = 12;
            var hosts = new TypeDef[HOST_COUNT];
            for (int h = 0; h < HOST_COUNT; h++)
            {
                var pt = new TypeDefUser("", engine.MakeName(),
                    module.CorLibTypes.Object.TypeDefOrRef);
                pt.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                    DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
                module.Types.Add(pt);
                engine.injectedTypes.Add(pt);
                hosts[h] = pt;

                for (int f = 0; f < rng.Next(6, 14); f++)
                {
                    pt.Fields.Add(new dnlib.DotNet.FieldDefUser(engine.MakeName(),
                        new FieldSig(module.CorLibTypes.Int32),
                        dnlib.DotNet.FieldAttributes.Private | dnlib.DotNet.FieldAttributes.Static));
                }
            }

            var delegateCache = new Dictionary<string, MethodDef>();
            int hostPtr = 0;

            bool allowDesigner = engine.cfg != null && engine.cfg.MaximumEncryption;
            foreach (TypeDef type in module.GetTypes())
            {
                if (engine.IsCompilerGenerated(type)) continue;
                foreach (MethodDef method in type.Methods)
                {
                    if (!engine.CanProcessMethod(method, allowDesigner)) continue;
                    if (engine.MethodHasAsyncOrIteratorAttribute(method)) continue;
                    try { ProxyMethodCalls(module, method, hosts, ref hostPtr, delegateCache); } catch { }
                }
            }

            int totalFakes = HOST_COUNT * 5;
            for (int i = 0; i < totalFakes; i++)
            {
                var host = hosts[i % HOST_COUNT];
                var fake = BuildFakeProxy(module);
                host.Methods.Add(fake);
                engine.injectedMethods.Add(fake);
            }
        }

        private MethodDef BuildFakeProxy(ModuleDef module)
        {
            int paramCount = rng.Next(0, 5);
            var paramTypes = new TypeSig[paramCount];
            for (int i = 0; i < paramCount; i++)
            {
                switch (rng.Next(0, 4))
                {
                    case 0: paramTypes[i] = module.CorLibTypes.Int32; break;
                    case 1: paramTypes[i] = module.CorLibTypes.String; break;
                    case 2: paramTypes[i] = module.CorLibTypes.Object; break;
                    default: paramTypes[i] = module.CorLibTypes.Boolean; break;
                }
            }
            TypeSig retType;
            switch (rng.Next(0, 4))
            {
                case 0: retType = module.CorLibTypes.Int32; break;
                case 1: retType = module.CorLibTypes.Void; break;
                case 2: retType = module.CorLibTypes.Object; break;
                default: retType = module.CorLibTypes.Boolean; break;
            }
            var m = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(retType, paramTypes),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            m.Body = new CilBody();
            var fil = m.Body.Instructions;
            if (retType == module.CorLibTypes.Void)
                fil.Add(Instruction.Create(DnOpCodes.Ret));
            else if (retType == module.CorLibTypes.Int32 || retType == module.CorLibTypes.Boolean)
            {
                fil.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                fil.Add(Instruction.Create(DnOpCodes.Ret));
            }
            else
            {
                fil.Add(Instruction.Create(DnOpCodes.Ldnull));
                fil.Add(Instruction.Create(DnOpCodes.Ret));
            }
            return m;
        }

        private bool IsInstanceTargetSafe(ModuleDef module, IMethod target, out TypeSig receiverTypeSig)
        {
            receiverTypeSig = null;
            if (target == null) return false;
            var declType = target.DeclaringType;
            if (declType == null) return false;

            TypeDef td = null;
            try { td = declType.ResolveTypeDef(); } catch { }

            if (td != null)
            {
                if (td.IsValueType) return false;
                if (td.HasGenericParameters) return false;
                if (td.Module != null && td.Module != module)
                {
                    string extNs = td.Namespace?.String ?? "";
                    string extNm = td.Name?.String ?? "";
                    if (!IsKnownSafeExternalType(extNs, extNm)) return false;
                }
            }
            else
            {
                var tr = declType as TypeRef;
                if (tr == null) return false;
                string ns = tr.Namespace?.String ?? "";
                string nm = tr.Name?.String ?? "";
                if (nm.Contains("`")) return false;
                if (IsKnownValueType(ns, nm)) return false;
                if (!IsKnownSafeExternalType(ns, nm)) return false;
            }

            try { receiverTypeSig = module.Import(declType.ToTypeSig()); }
            catch { return false; }
            return receiverTypeSig != null;
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

        private void ProxyMethodCalls(ModuleDef module, MethodDef method, TypeDef[] hosts,
            ref int hostPtr, Dictionary<string, MethodDef> cache)
        {
            bool maxEnc = engine.cfg != null && engine.cfg.MaximumEncryption;
            var il = method.Body.Instructions;
            for (int i = 0; i < il.Count; i++)
            {
                bool isCall     = il[i].OpCode == DnOpCodes.Call;
                bool isCallvirt = il[i].OpCode == DnOpCodes.Callvirt;
                bool isNewObj   = il[i].OpCode == DnOpCodes.Newobj;
                if (!isCall && !isCallvirt && !isNewObj) continue;

                if (i > 0 && il[i - 1].OpCode == DnOpCodes.Constrained) continue;

                var target = il[i].Operand as IMethod;
                if (target == null) continue;
                if (engine.IsCompilerInfrastructureCall(target)) continue;
                if (engine.IsCompilerGeneratedOwner(target)) continue;
                if (engine.IsInaccessibleOwnedType(target.DeclaringType)) continue;
                MethodDef mdCheck = target as MethodDef;
                if (mdCheck != null && engine.injectedMethods.Contains(mdCheck)) continue;

                if (!isNewObj && (target.Name == ".ctor" || target.Name == ".cctor")) continue;

                if (mdCheck != null)
                {
                    bool isAccessible = mdCheck.IsPublic ||
                        (mdCheck.IsAssembly || mdCheck.IsFamilyOrAssembly || mdCheck.IsFamilyAndAssembly);
                    if (!isAccessible) continue;
                }

                var targetSig = target.MethodSig;
                if (targetSig == null) continue;
                if (targetSig.GenParamCount > 0) continue;

                bool hasThis = targetSig.HasThis;

                bool hasBadParam = false;
                foreach (var p in targetSig.Params) { if (p == null || p.IsByRef || p.IsPointer) { hasBadParam = true; break; } }
                if (hasBadParam) continue;
                if (targetSig.RetType != null && (targetSig.RetType.IsByRef || targetSig.RetType.IsPointer)) continue;

                TypeSig receiverTypeSig = null;
                int effectiveParamCount = targetSig.Params.Count + (hasThis ? 1 : 0);

                if (hasThis && !isNewObj)
                {
                    if (!IsInstanceTargetSafe(module, target, out receiverTypeSig)) continue;
                    if (effectiveParamCount > 4) continue;
                }
                else if (!isNewObj)
                {
                    if (targetSig.Params.Count > 4) continue;
                }

                if (isNewObj && !engine.IsConfirmedReferenceTypeCtor(target.DeclaringType))
                    continue;

                string callKind = isNewObj ? "NEW" : (hasThis ? (isCallvirt ? "CVIRT" : "CCALL") : "CALL");
                string cacheKey = callKind + ":" + target.FullName;
                bool useCallvirt = hasThis && isCallvirt;
                MethodDef proxy;
                if (!cache.TryGetValue(cacheKey, out proxy))
                {
                    var host = hosts[hostPtr % hosts.Length];
                    hostPtr++;
                    proxy = BuildProxyMethod(module, target, host, isNewObj, maxEnc, hasThis, receiverTypeSig, useCallvirt);
                    if (proxy == null) continue;
                    cache[cacheKey] = proxy;
                    host.Methods.Add(proxy);
                    engine.injectedMethods.Add(proxy);
                }

                il[i].OpCode = DnOpCodes.Call;
                il[i].Operand = proxy;
            }
        }

        private MethodDef BuildProxyMethod(ModuleDef module, IMethod target,
            TypeDef proxyType, bool isNewObj, bool maxEnc,
            bool hasThis = false, TypeSig receiverTypeSig = null, bool useCallvirt = false)
        {
            var targetSig = target.MethodSig;
            if (targetSig == null) return null;

            TypeSig retType;
            if (isNewObj)
            {
                if (target.DeclaringType == null) return null;
                try
                {
                    var imported = module.Import(target.DeclaringType);
                    var asDefOrRef = imported as ITypeDefOrRef;
                    if (asDefOrRef == null) return null;
                    retType = asDefOrRef.ToTypeSig();
                }
                catch { return null; }
                if (retType == null) return null;
            }
            else
            {
                retType = targetSig.RetType;
            }

            TypeSig[] proxyParams;
            if (hasThis && receiverTypeSig != null)
            {
                proxyParams = new TypeSig[1 + targetSig.Params.Count];
                proxyParams[0] = receiverTypeSig;
                for (int pi = 0; pi < targetSig.Params.Count; pi++)
                    proxyParams[pi + 1] = targetSig.Params[pi];
            }
            else
            {
                proxyParams = targetSig.Params.ToArray();
            }

            var proxySig = MethodSig.CreateStatic(retType, proxyParams);

            var implFlags = DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed |
                            DnMethodImplAttributes.NoInlining;
            var attrFlags = maxEnc
                ? (DnMethodAttributes.Public | DnMethodAttributes.Static | DnMethodAttributes.HideBySig)
                : (DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            var proxy = new MethodDefUser(engine.MakeName(),
                proxySig, implFlags, attrFlags);

            proxy.Body = new CilBody();
            var il = proxy.Body.Instructions;

            if (maxEnc)
            {
                try
                {
                    var assertM = module.Import(typeof(System.Diagnostics.Debug)
                        .GetMethod("Assert", new Type[] { typeof(bool) }));
                    if (assertM != null)
                    {
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
                        il.Add(Instruction.Create(DnOpCodes.Call, assertM));
                    }
                }
                catch { }
            }

            var tickCount = module.Import(typeof(Environment).GetProperty("TickCount").GetGetMethod());
            Instruction deadStart = Instruction.Create(DnOpCodes.Ldnull);
            il.Add(Instruction.Create(DnOpCodes.Call, tickCount));
            il.Add(Instruction.Create(DnOpCodes.Dup));
            il.Add(Instruction.Create(DnOpCodes.Dup));
            il.Add(Instruction.Create(DnOpCodes.Mul));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.And));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, deadStart));

            int totalParams = proxyParams.Length;
            for (int i = 0; i < totalParams; i++)
            {
                switch (i)
                {
                    case 0: il.Add(Instruction.Create(DnOpCodes.Ldarg_0)); break;
                    case 1: il.Add(Instruction.Create(DnOpCodes.Ldarg_1)); break;
                    case 2: il.Add(Instruction.Create(DnOpCodes.Ldarg_2)); break;
                    case 3: il.Add(Instruction.Create(DnOpCodes.Ldarg_3)); break;
                }
            }

            OpCode callOpcode;
            if (isNewObj) callOpcode = DnOpCodes.Newobj;
            else if (hasThis && useCallvirt) callOpcode = DnOpCodes.Callvirt;
            else callOpcode = DnOpCodes.Call;

            il.Add(Instruction.Create(callOpcode, module.Import(target)));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            il.Add(deadStart);
            il.Add(Instruction.Create(DnOpCodes.Throw));

            return proxy;
        }
    }
}

