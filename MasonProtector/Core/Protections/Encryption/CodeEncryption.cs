using System;
using System.Collections.Generic;
using System.Linq;
using dnlib.DotNet;
using dnlib.DotNet.Emit;

using DnFieldAttributes = dnlib.DotNet.FieldAttributes;
using DnMethodAttributes = dnlib.DotNet.MethodAttributes;
using DnMethodImplAttributes = dnlib.DotNet.MethodImplAttributes;
using DnTypeAttributes = dnlib.DotNet.TypeAttributes;
using DnOpCodes = dnlib.DotNet.Emit.OpCodes;

namespace MasonProtector.Core
{
    internal class CodeEncryptionProtection
    {
        private Obfuscation engine;
        private Random rng;

        internal CodeEncryptionProtection(Obfuscation eng)
        {
            engine = eng;
            rng = eng.rng;
        }

        private struct CallEntry
        {
            internal int RawSlot;
            internal IMethod Target;
            internal MethodSig Sig;
        }

        private struct NewobjEntry
        {
            internal int RawSlot;
            internal IMethod Ctor;
            internal MethodSig CtorSig;
            internal TypeSig ResultType;
        }

        internal void ApplyCodeEncryption(ModuleDef module)
        {
            engine.activeOption = "CodeEncryption";

            var vaultType = new TypeDefUser("", engine.MakeName(),
                module.CorLibTypes.Object.TypeDefOrRef);
            vaultType.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
            module.Types.Add(vaultType);
            engine.injectedTypes.Add(vaultType);

            var callEntries = new List<CallEntry>();
            var callKeyToSlot = new Dictionary<string, int>(StringComparer.Ordinal);
            var callHelperBySlot = new Dictionary<int, MethodDef>();

            var newobjEntries = new List<NewobjEntry>();
            var newobjKeyToSlot = new Dictionary<string, int>(StringComparer.Ordinal);
            var newobjHelperBySlot = new Dictionary<int, MethodDef>();

            foreach (TypeDef type in module.GetTypes())
            {
                if (type == vaultType) continue;
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
                        RewriteMethod(module, method, vaultType,
                            callEntries, callKeyToSlot, callHelperBySlot,
                            newobjEntries, newobjKeyToSlot, newobjHelperBySlot);
                    }
                    catch { }
                }
            }

            if (callEntries.Count == 0 && newobjEntries.Count == 0) return;

            BuildSharedCallInfrastructure(module, vaultType, callEntries,
                callHelperBySlot);

            if (newobjEntries.Count > 0)
                BuildNewobjInfrastructure(module, vaultType, newobjEntries,
                    newobjHelperBySlot);
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

        private void RewriteMethod(ModuleDef module, MethodDef method,
            TypeDef vaultType,
            List<CallEntry> callEntries, Dictionary<string, int> callKeyToSlot,
            Dictionary<int, MethodDef> callHelperBySlot,
            List<NewobjEntry> newobjEntries, Dictionary<string, int> newobjKeyToSlot,
            Dictionary<int, MethodDef> newobjHelperBySlot)
        {
            var il = method.Body.Instructions;
            for (int i = 0; i < il.Count; i++)
            {
                bool isCall = il[i].OpCode == DnOpCodes.Call;
                bool isNewObj = il[i].OpCode == DnOpCodes.Newobj;
                if (!isCall && !isNewObj) continue;

                var target = il[i].Operand as IMethod;
                if (target == null) continue;
                if (engine.IsCompilerInfrastructureCall(target)) continue;
                if (engine.IsInaccessibleOwnedType(target.DeclaringType)) continue;

                MethodDef mdCheck = target as MethodDef;
                if (mdCheck != null)
                {
                    if (engine.injectedMethods.Contains(mdCheck)) continue;
                    bool accessible = mdCheck.IsPublic || mdCheck.IsAssembly ||
                        mdCheck.IsFamilyOrAssembly || mdCheck.IsFamilyAndAssembly;
                    if (!accessible) continue;
                }

                var targetSig = target.MethodSig;
                if (targetSig == null) continue;
                if (targetSig.GenParamCount > 0) continue;

                if (isCall)
                {
                    if (targetSig.HasThis) continue;
                    if (targetSig.Params.Count > 4) continue;

                    string key = target.FullName;
                    int rawSlot;
                    MethodDef helper;
                    if (!callKeyToSlot.TryGetValue(key, out rawSlot))
                    {
                        rawSlot = callEntries.Count;
                        callEntries.Add(new CallEntry
                        {
                            RawSlot = rawSlot,
                            Target = target,
                            Sig = targetSig
                        });
                        callKeyToSlot[key] = rawSlot;

                        helper = BuildCallStub(module, vaultType, targetSig, rawSlot);
                        if (helper == null)
                        {
                            callEntries.RemoveAt(rawSlot);
                            callKeyToSlot.Remove(key);
                            continue;
                        }
                        callHelperBySlot[rawSlot] = helper;
                        vaultType.Methods.Add(helper);
                        engine.injectedMethods.Add(helper);
                    }
                    else
                    {
                        if (!callHelperBySlot.TryGetValue(rawSlot, out helper) || helper == null)
                            continue;
                    }

                    il[i].OpCode = DnOpCodes.Call;
                    il[i].Operand = helper;
                }
                else
                {
                    if (!engine.IsConfirmedReferenceTypeCtor(target.DeclaringType)) continue;
                    if (targetSig.Params.Count > 4) continue;

                    TypeSig resultType;
                    try
                    {
                        var imp = module.Import(target.DeclaringType);
                        var asDor = imp as ITypeDefOrRef;
                        if (asDor == null) continue;
                        resultType = asDor.ToTypeSig();
                    }
                    catch { continue; }
                    if (resultType == null) continue;

                    string key = "NEW:" + target.FullName;
                    int rawSlot;
                    MethodDef helper;
                    if (!newobjKeyToSlot.TryGetValue(key, out rawSlot))
                    {
                        rawSlot = newobjEntries.Count;
                        newobjEntries.Add(new NewobjEntry
                        {
                            RawSlot = rawSlot,
                            Ctor = target,
                            CtorSig = targetSig,
                            ResultType = resultType
                        });
                        newobjKeyToSlot[key] = rawSlot;

                        helper = BuildNewobjStub(module, vaultType, targetSig, resultType, rawSlot);
                        if (helper == null)
                        {
                            newobjEntries.RemoveAt(rawSlot);
                            newobjKeyToSlot.Remove(key);
                            continue;
                        }
                        newobjHelperBySlot[rawSlot] = helper;
                        vaultType.Methods.Add(helper);
                        engine.injectedMethods.Add(helper);
                    }
                    else
                    {
                        if (!newobjHelperBySlot.TryGetValue(rawSlot, out helper) || helper == null)
                            continue;
                    }

                    il[i].OpCode = DnOpCodes.Call;
                    il[i].Operand = helper;
                }
            }
        }

        private MethodDef BuildCallStub(ModuleDef module, TypeDef vaultType,
            MethodSig targetSig, int rawSlot)
        {
            if (targetSig == null) return null;
            var stubSig = MethodSig.CreateStatic(targetSig.RetType, targetSig.Params.ToArray());
            var stub = new MethodDefUser(engine.MakeName(), stubSig,
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed |
                DnMethodImplAttributes.NoInlining,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            stub.Body = new CilBody();
            stub.Body.InitLocals = true;
            stub.Body.Variables.Add(new Local(module.CorLibTypes.IntPtr));

            var il = stub.Body.Instructions;
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rawSlot));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            return stub;
        }

        private MethodDef BuildNewobjStub(ModuleDef module, TypeDef vaultType,
            MethodSig ctorSig, TypeSig resultType, int rawSlot)
        {
            if (ctorSig == null || resultType == null) return null;
            var stubSig = MethodSig.CreateStatic(resultType, ctorSig.Params.ToArray());
            var stub = new MethodDefUser(engine.MakeName(), stubSig,
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed |
                DnMethodImplAttributes.NoInlining,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            stub.Body = new CilBody();
            stub.Body.InitLocals = true;

            var il = stub.Body.Instructions;
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rawSlot));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            return stub;
        }

        private void BuildSharedCallInfrastructure(ModuleDef module, TypeDef vaultType,
            List<CallEntry> entries, Dictionary<int, MethodDef> helperBySlot)
        {
            if (entries.Count == 0) return;
            int n = entries.Count;

            var ptrCacheField = new FieldDefUser(engine.MakeName(),
                new FieldSig(new SZArraySig(module.CorLibTypes.IntPtr)),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            vaultType.Fields.Add(ptrCacheField);

            var encTableField = new FieldDefUser(engine.MakeName(),
                new FieldSig(new SZArraySig(module.CorLibTypes.Int32)),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            vaultType.Fields.Add(encTableField);

            var keyTableField = new FieldDefUser(engine.MakeName(),
                new FieldSig(new SZArraySig(module.CorLibTypes.Int32)),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            vaultType.Fields.Add(keyTableField);

            int seedVal = rng.Next(0x10000, int.MaxValue / 2);
            int seed2Val = rng.Next(0x10000, int.MaxValue / 2);

            var seedField = new FieldDefUser(engine.MakeName(),
                new FieldSig(module.CorLibTypes.Int32),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            vaultType.Fields.Add(seedField);

            var seed2Field = new FieldDefUser(engine.MakeName(),
                new FieldSig(module.CorLibTypes.Int32),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            vaultType.Fields.Add(seed2Field);

            int[] perEntryKeys = new int[n];
            int[] encValues = new int[n];
            for (int i = 0; i < n; i++)
            {
                perEntryKeys[i] = rng.Next(0x1000, int.MaxValue / 2);
                int twist = (seed2Val >> (i & 7)) ^ (i * 0x1337);
                encValues[i] = i ^ perEntryKeys[i] ^ twist;
            }

            var decoyTargets = CollectDecoyTargets(module);

            var switchResolver = BuildCallSwitchResolver(module, vaultType, entries, decoyTargets, n);

            var sharedResolver = BuildCallSharedResolver(module, vaultType,
                ptrCacheField, encTableField, keyTableField, seedField, seed2Field, switchResolver);

            RewireCallHelpers(module, helperBySlot, entries, sharedResolver, seedVal);

            BuildCallCctor(module, vaultType,
                ptrCacheField, encTableField, keyTableField,
                seedField, seed2Field,
                encValues, perEntryKeys, seedVal, seed2Val, n);
        }

        private List<IMethod> CollectDecoyTargets(ModuleDef module)
        {
            var result = new List<IMethod>();
            try
            {
                result.Add(module.Import(typeof(string).GetMethod("IsNullOrEmpty",
                    new Type[] { typeof(string) })));
            }
            catch { }
            try
            {
                result.Add(module.Import(typeof(string).GetMethod("IsNullOrWhiteSpace",
                    new Type[] { typeof(string) })));
            }
            catch { }
            try
            {
                result.Add(module.Import(typeof(Math).GetMethod("Abs",
                    new Type[] { typeof(int) })));
            }
            catch { }
            try
            {
                result.Add(module.Import(typeof(Math).GetMethod("Max",
                    new Type[] { typeof(int), typeof(int) })));
            }
            catch { }
            try
            {
                result.Add(module.Import(typeof(string).GetMethod("Concat",
                    new Type[] { typeof(string), typeof(string) })));
            }
            catch { }
            return result;
        }

        private MethodDef BuildCallSwitchResolver(ModuleDef module, TypeDef vaultType,
            List<CallEntry> entries, List<IMethod> decoyTargets, int realCount)
        {
            int decoyBase = realCount + 1000;
            int totalCases = realCount + decoyTargets.Count;

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

            Instruction[] caseLabels = new Instruction[totalCases];
            for (int i = 0; i < totalCases; i++)
                caseLabels[i] = Instruction.Create(DnOpCodes.Nop);

            int[] switchOrder = BuildSwitchOrder(totalCases, decoyBase, decoyTargets.Count, realCount);

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));

            Instruction[] switchTargets = new Instruction[realCount];
            for (int i = 0; i < realCount; i++)
                switchTargets[i] = caseLabels[i];

            il.Add(new Instruction(DnOpCodes.Switch, switchTargets));
            il.Add(Instruction.Create(DnOpCodes.Br, defaultLbl));

            for (int i = 0; i < realCount; i++)
            {
                il.Add(caseLabels[i]);
                il.Add(Instruction.Create(DnOpCodes.Ldftn, module.Import(entries[i].Target)));
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                il.Add(Instruction.Create(DnOpCodes.Br, retLbl));
            }

            for (int d = 0; d < decoyTargets.Count; d++)
            {
                il.Add(caseLabels[realCount + d]);
                il.Add(Instruction.Create(DnOpCodes.Ldftn, decoyTargets[d]));
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                il.Add(Instruction.Create(DnOpCodes.Br, retLbl));
            }

            il.Add(defaultLbl);
            il.Add(Instruction.Create(DnOpCodes.Conv_I));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));

            il.Add(retLbl);
            il.Add(Instruction.Create(DnOpCodes.Ret));

            vaultType.Methods.Add(m);
            engine.injectedMethods.Add(m);
            return m;
        }

        private int[] BuildSwitchOrder(int totalCases, int decoyBase, int decoyCount, int realCount)
        {
            var arr = new int[totalCases];
            for (int i = 0; i < realCount; i++) arr[i] = i;
            for (int d = 0; d < decoyCount; d++) arr[realCount + d] = decoyBase + d;
            return arr;
        }

        private MethodDef BuildCallSharedResolver(ModuleDef module, TypeDef vaultType,
            FieldDef ptrCacheField, FieldDef encTableField, FieldDef keyTableField,
            FieldDef seedField, FieldDef seed2Field, MethodDef switchResolver)
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
            m.Body.Variables.Add(new Local(module.CorLibTypes.Int32));

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

            il.Add(Instruction.Create(DnOpCodes.Ldsfld, seed2Field));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_7));
            il.Add(Instruction.Create(DnOpCodes.And));
            il.Add(Instruction.Create(DnOpCodes.Shr));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 0x1337));
            il.Add(Instruction.Create(DnOpCodes.Mul));
            il.Add(Instruction.Create(DnOpCodes.Xor));
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

            vaultType.Methods.Add(m);
            engine.injectedMethods.Add(m);
            return m;
        }

        private void RewireCallHelpers(ModuleDef module,
            Dictionary<int, MethodDef> helperBySlot,
            List<CallEntry> entries,
            MethodDef sharedResolver,
            int seedVal)
        {
            foreach (var kv in helperBySlot)
            {
                int rawSlot = kv.Key;
                var helper = kv.Value;
                if (helper == null) continue;

                MethodSig targetSig;
                if (rawSlot >= entries.Count) continue;
                targetSig = entries[rawSlot].Sig;
                if (targetSig == null) continue;

                int encodedSlot = rawSlot ^ seedVal;

                var il = helper.Body.Instructions;
                il.Clear();
                helper.Body.Variables.Clear();
                helper.Body.Variables.Add(new Local(module.CorLibTypes.IntPtr));

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

                var calliSig = MethodSig.CreateStatic(targetSig.RetType,
                    targetSig.Params.ToArray());
                calliSig.CallingConvention = CallingConvention.Default;
                il.Add(new Instruction(DnOpCodes.Calli, calliSig));
                il.Add(Instruction.Create(DnOpCodes.Ret));
            }
        }

        private void BuildCallCctor(ModuleDef module, TypeDef vaultType,
            FieldDef ptrCacheField, FieldDef encTableField, FieldDef keyTableField,
            FieldDef seedField, FieldDef seed2Field,
            int[] encValues, int[] perEntryKeys, int seedVal, int seed2Val, int n)
        {
            var cctorSig = MethodSig.CreateStatic(module.CorLibTypes.Void);
            var cctor = new MethodDefUser(".cctor", cctorSig,
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Private | DnMethodAttributes.Static |
                DnMethodAttributes.HideBySig | DnMethodAttributes.SpecialName |
                DnMethodAttributes.RTSpecialName);
            cctor.Body = new CilBody();
            cctor.Body.InitLocals = false;

            var il = cctor.Body.Instructions;

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, n));
            il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.IntPtr.ToTypeDefOrRef()));
            il.Add(Instruction.Create(DnOpCodes.Stsfld, ptrCacheField));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, n));
            il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.Int32.ToTypeDefOrRef()));
            il.Add(Instruction.Create(DnOpCodes.Stsfld, encTableField));

            for (int i = 0; i < n; i++)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldsfld, encTableField));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, i));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, encValues[i]));
                il.Add(Instruction.Create(DnOpCodes.Stelem_I4));
            }

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, n));
            il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.Int32.ToTypeDefOrRef()));
            il.Add(Instruction.Create(DnOpCodes.Stsfld, keyTableField));

            for (int i = 0; i < n; i++)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldsfld, keyTableField));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, i));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, perEntryKeys[i]));
                il.Add(Instruction.Create(DnOpCodes.Stelem_I4));
            }

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, seedVal));
            il.Add(Instruction.Create(DnOpCodes.Stsfld, seedField));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, seed2Val));
            il.Add(Instruction.Create(DnOpCodes.Stsfld, seed2Field));

            il.Add(Instruction.Create(DnOpCodes.Ret));

            vaultType.Methods.Add(cctor);
            engine.injectedMethods.Add(cctor);
        }

        private void BuildNewobjInfrastructure(ModuleDef module, TypeDef vaultType,
            List<NewobjEntry> entries, Dictionary<int, MethodDef> helperBySlot)
        {
            int n = entries.Count;

            int noSeedVal = rng.Next(0x10000, int.MaxValue / 2);

            var noSeedField = new FieldDefUser(engine.MakeName(),
                new FieldSig(module.CorLibTypes.Int32),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            vaultType.Fields.Add(noSeedField);

            int[] noPerKeys = new int[n];
            int[] noEncValues = new int[n];
            for (int i = 0; i < n; i++)
            {
                noPerKeys[i] = rng.Next(0x1000, int.MaxValue / 2);
                noEncValues[i] = i ^ noPerKeys[i] ^ noSeedVal;
            }

            var noEncTableField = new FieldDefUser(engine.MakeName(),
                new FieldSig(new SZArraySig(module.CorLibTypes.Int32)),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            vaultType.Fields.Add(noEncTableField);

            var noKeyTableField = new FieldDefUser(engine.MakeName(),
                new FieldSig(new SZArraySig(module.CorLibTypes.Int32)),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            vaultType.Fields.Add(noKeyTableField);

            var noSwitchDispatcher = BuildNewobjSwitchDispatcher(module, vaultType, entries);

            RewireNewobjHelpers(module, helperBySlot, entries,
                noEncTableField, noKeyTableField, noSeedField, noSwitchDispatcher, noSeedVal);

            BuildNewobjCctor(module, vaultType,
                noEncTableField, noKeyTableField, noSeedField,
                noEncValues, noPerKeys, noSeedVal, n);
        }

        private MethodDef BuildNewobjSwitchDispatcher(ModuleDef module, TypeDef vaultType,
            List<NewobjEntry> entries)
        {
            int n = entries.Count;
            var sig = MethodSig.CreateStatic(module.CorLibTypes.Object, module.CorLibTypes.Int32,
                new SZArraySig(module.CorLibTypes.Object));
            var m = new MethodDefUser(engine.MakeName(), sig,
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed |
                DnMethodImplAttributes.NoInlining,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            m.Body = new CilBody();
            m.Body.InitLocals = true;
            m.Body.Variables.Add(new Local(module.CorLibTypes.Object));

            var il = m.Body.Instructions;
            var retLbl = Instruction.Create(DnOpCodes.Ldloc_0);
            var defaultLbl = Instruction.Create(DnOpCodes.Ldnull);

            Instruction[] caseLabels = new Instruction[n];
            for (int i = 0; i < n; i++)
                caseLabels[i] = Instruction.Create(DnOpCodes.Nop);

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(new Instruction(DnOpCodes.Switch, caseLabels));
            il.Add(Instruction.Create(DnOpCodes.Br, defaultLbl));

            for (int i = 0; i < n; i++)
            {
                il.Add(caseLabels[i]);
                var entry = entries[i];
                int pc = entry.CtorSig.Params.Count;
                for (int p = 0; p < pc; p++)
                {
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, p));
                    il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
                    var paramType = entry.CtorSig.Params[p];
                    if (paramType.IsValueType)
                        il.Add(Instruction.Create(DnOpCodes.Unbox_Any,
                            paramType.ToTypeDefOrRef()));
                }
                il.Add(Instruction.Create(DnOpCodes.Newobj, module.Import(entry.Ctor)));
                il.Add(Instruction.Create(DnOpCodes.Box, entry.ResultType.ToTypeDefOrRef()));
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                il.Add(Instruction.Create(DnOpCodes.Br, retLbl));
            }

            il.Add(defaultLbl);
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));

            il.Add(retLbl);
            il.Add(Instruction.Create(DnOpCodes.Ret));

            vaultType.Methods.Add(m);
            engine.injectedMethods.Add(m);
            return m;
        }

        private void RewireNewobjHelpers(ModuleDef module,
            Dictionary<int, MethodDef> helperBySlot,
            List<NewobjEntry> entries,
            FieldDef encTableField, FieldDef keyTableField, FieldDef seedField,
            MethodDef switchDispatcher, int seedVal)
        {
            foreach (var kv in helperBySlot)
            {
                int rawSlot = kv.Key;
                var helper = kv.Value;
                if (helper == null || rawSlot >= entries.Count) continue;

                var entry = entries[rawSlot];
                int paramCount = entry.CtorSig.Params.Count;

                var il = helper.Body.Instructions;
                il.Clear();
                helper.Body.Variables.Clear();
                helper.Body.Variables.Add(new Local(new SZArraySig(module.CorLibTypes.Object)));
                helper.Body.Variables.Add(new Local(module.CorLibTypes.Object));

                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, paramCount));
                il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.Object.ToTypeDefOrRef()));
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));

                for (int p = 0; p < paramCount; p++)
                {
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, p));
                    switch (p)
                    {
                        case 0: il.Add(Instruction.Create(DnOpCodes.Ldarg_0)); break;
                        case 1: il.Add(Instruction.Create(DnOpCodes.Ldarg_1)); break;
                        case 2: il.Add(Instruction.Create(DnOpCodes.Ldarg_2)); break;
                        case 3: il.Add(Instruction.Create(DnOpCodes.Ldarg_3)); break;
                    }
                    var paramType = entry.CtorSig.Params[p];
                    if (paramType.IsValueType)
                        il.Add(Instruction.Create(DnOpCodes.Box, paramType.ToTypeDefOrRef()));
                    il.Add(Instruction.Create(DnOpCodes.Stelem_Ref));
                }

                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rawSlot));
                il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                il.Add(Instruction.Create(DnOpCodes.Call, switchDispatcher));
                il.Add(Instruction.Create(DnOpCodes.Stloc_1));
                il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                il.Add(Instruction.Create(DnOpCodes.Unbox_Any, entry.ResultType.ToTypeDefOrRef()));
                il.Add(Instruction.Create(DnOpCodes.Ret));
            }
        }

        private void BuildNewobjCctor(ModuleDef module, TypeDef vaultType,
            FieldDef encTableField, FieldDef keyTableField, FieldDef seedField,
            int[] encValues, int[] perKeys, int seedVal, int n)
        {
            var cctorSig = MethodSig.CreateStatic(module.CorLibTypes.Void);

            MethodDef existing = null;
            foreach (var md in vaultType.Methods)
            {
                if (md.IsStaticConstructor) { existing = md; break; }
            }

            List<Instruction> extra = new List<Instruction>();

            extra.Add(Instruction.Create(DnOpCodes.Ldc_I4, n));
            extra.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.Int32.ToTypeDefOrRef()));
            extra.Add(Instruction.Create(DnOpCodes.Stsfld, encTableField));

            for (int i = 0; i < n; i++)
            {
                extra.Add(Instruction.Create(DnOpCodes.Ldsfld, encTableField));
                extra.Add(Instruction.Create(DnOpCodes.Ldc_I4, i));
                extra.Add(Instruction.Create(DnOpCodes.Ldc_I4, encValues[i]));
                extra.Add(Instruction.Create(DnOpCodes.Stelem_I4));
            }

            extra.Add(Instruction.Create(DnOpCodes.Ldc_I4, n));
            extra.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.Int32.ToTypeDefOrRef()));
            extra.Add(Instruction.Create(DnOpCodes.Stsfld, keyTableField));

            for (int i = 0; i < n; i++)
            {
                extra.Add(Instruction.Create(DnOpCodes.Ldsfld, keyTableField));
                extra.Add(Instruction.Create(DnOpCodes.Ldc_I4, i));
                extra.Add(Instruction.Create(DnOpCodes.Ldc_I4, perKeys[i]));
                extra.Add(Instruction.Create(DnOpCodes.Stelem_I4));
            }

            extra.Add(Instruction.Create(DnOpCodes.Ldc_I4, seedVal));
            extra.Add(Instruction.Create(DnOpCodes.Stsfld, seedField));

            if (existing != null)
            {
                var il = existing.Body.Instructions;
                var retInstr = il.Count > 0 ? il[il.Count - 1] : null;
                if (retInstr != null && retInstr.OpCode == DnOpCodes.Ret)
                    il.RemoveAt(il.Count - 1);
                foreach (var instr in extra)
                    il.Add(instr);
                il.Add(Instruction.Create(DnOpCodes.Ret));
            }
            else
            {
                var cctor = new MethodDefUser(".cctor", cctorSig,
                    DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                    DnMethodAttributes.Private | DnMethodAttributes.Static |
                    DnMethodAttributes.HideBySig | DnMethodAttributes.SpecialName |
                    DnMethodAttributes.RTSpecialName);
                cctor.Body = new CilBody();
                cctor.Body.InitLocals = false;
                foreach (var instr in extra)
                    cctor.Body.Instructions.Add(instr);
                cctor.Body.Instructions.Add(Instruction.Create(DnOpCodes.Ret));
                vaultType.Methods.Add(cctor);
                engine.injectedMethods.Add(cctor);
            }
        }
    }
}
