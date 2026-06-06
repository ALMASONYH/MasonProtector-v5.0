using System;
using System.Collections.Generic;
using System.IO;
using System.IO.Compression;
using System.Linq;
using System.Security.Cryptography;
using dnlib.DotNet;
using dnlib.DotNet.Emit;

using DnFieldAttributes = dnlib.DotNet.FieldAttributes;
using DnMethodAttributes = dnlib.DotNet.MethodAttributes;
using DnMethodImplAttributes = dnlib.DotNet.MethodImplAttributes;
using DnTypeAttributes = dnlib.DotNet.TypeAttributes;
using DnOpCodes = dnlib.DotNet.Emit.OpCodes;

namespace MasonProtector.Core
{
    internal class RuntimeEncryptionProtection
    {
        private Obfuscation engine;
        private Random rng;

        private FieldDef _rpCfZeroField;

        internal RuntimeEncryptionProtection(Obfuscation eng)
        {
            engine = eng;
            rng = eng.rng;
        }

        private FieldDef EnsureRPCfZeroField(ModuleDef module)
        {
            if (_rpCfZeroField != null) return _rpCfZeroField;
            try
            {
                TypeDef host = module.GlobalType;
                if (host == null) return null;
                var f = new FieldDefUser(engine.MakeName(),
                    new FieldSig(module.CorLibTypes.Int32),
                    DnFieldAttributes.Assembly | DnFieldAttributes.Static);
                host.Fields.Add(f);
                _rpCfZeroField = f;
                return f;
            }
            catch { return null; }
        }

        private void EmitObfuscatedStringIL(IList<Instruction> il, ModuleDef module, string value)
        {
            if (string.IsNullOrEmpty(value))
            {
                il.Add(Instruction.Create(DnOpCodes.Ldstr, ""));
                return;
            }

            var stringCtorCharArr = module.Import(
                typeof(string).GetConstructor(new[] { typeof(char[]) }));
            var charTypeRef = module.CorLibTypes.Char.TypeDefOrRef;

            int kAdd  = 1 + rng.Next(0x0100, 0x3FFF);
            int kMul  = 1 | rng.Next(0x0003, 0x007F);
            int kXor1 = 1 + rng.Next(0x0020, 0x00FF);
            int kXor2 = 1 + rng.Next(0x0100, 0x1FFF);
            int kShr  = 1 + (rng.Next() & 3);
            int kAnd  = 0xFFFF & rng.Next();

            il.Add(engine.LoadInt(value.Length));
            il.Add(Instruction.Create(DnOpCodes.Newarr, charTypeRef));

            for (int ci = 0; ci < value.Length; ci++)
            {
                int orig = (int)value[ci];

                il.Add(Instruction.Create(DnOpCodes.Dup));
                il.Add(engine.LoadInt(ci));

                int variant = (ci + rng.Next(4)) & 3;
                switch (variant)
                {
                    case 0:
                    {
                        int step1 = (orig + kAdd) & 0xFFFF;
                        int encoded = step1 ^ kXor1;
                        il.Add(engine.LoadInt(encoded));
                        il.Add(engine.LoadInt(kXor1));
                        il.Add(Instruction.Create(DnOpCodes.Xor));
                        il.Add(engine.LoadInt(kAdd));
                        il.Add(Instruction.Create(DnOpCodes.Sub));
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 0xFFFF));
                        il.Add(Instruction.Create(DnOpCodes.And));
                        break;
                    }
                    case 1:
                    {
                        int intermed = (orig ^ kXor2) & 0xFFFF;
                        int encoded2 = (intermed ^ kXor1) & 0xFFFF;
                        il.Add(engine.LoadInt(encoded2));
                        il.Add(engine.LoadInt(kXor1));
                        il.Add(Instruction.Create(DnOpCodes.Or));
                        il.Add(engine.LoadInt(encoded2));
                        il.Add(engine.LoadInt(kXor1));
                        il.Add(Instruction.Create(DnOpCodes.And));
                        il.Add(Instruction.Create(DnOpCodes.Sub));
                        il.Add(engine.LoadInt(kXor2));
                        il.Add(Instruction.Create(DnOpCodes.Xor));
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 0xFFFF));
                        il.Add(Instruction.Create(DnOpCodes.And));
                        break;
                    }
                    case 2:
                    {
                        int encoded3 = (orig ^ kXor1) & 0xFFFF;
                        il.Add(engine.LoadInt(encoded3));
                        il.Add(engine.LoadInt(kXor1));
                        il.Add(Instruction.Create(DnOpCodes.Or));
                        il.Add(engine.LoadInt(encoded3));
                        il.Add(engine.LoadInt(kXor1));
                        il.Add(Instruction.Create(DnOpCodes.And));
                        il.Add(Instruction.Create(DnOpCodes.Sub));
                        il.Add(engine.LoadInt(kAdd));
                        il.Add(Instruction.Create(DnOpCodes.Add));
                        il.Add(engine.LoadInt(kAdd));
                        il.Add(Instruction.Create(DnOpCodes.Sub));
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 0xFFFF));
                        il.Add(Instruction.Create(DnOpCodes.And));
                        break;
                    }
                    default:
                    {
                        int step1d = (orig + kAdd) & 0xFFFF;
                        int enc4   = step1d ^ kXor2;
                        il.Add(engine.LoadInt(enc4));
                        il.Add(engine.LoadInt(kXor2));
                        il.Add(Instruction.Create(DnOpCodes.Xor));
                        il.Add(engine.LoadInt(kXor1));
                        il.Add(Instruction.Create(DnOpCodes.Add));
                        il.Add(engine.LoadInt(kXor1));
                        il.Add(Instruction.Create(DnOpCodes.Sub));
                        il.Add(engine.LoadInt(kAdd));
                        il.Add(Instruction.Create(DnOpCodes.Sub));
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 0xFFFF));
                        il.Add(Instruction.Create(DnOpCodes.And));
                        break;
                    }
                }

                il.Add(Instruction.Create(DnOpCodes.Conv_U2));
                il.Add(Instruction.Create(DnOpCodes.Stelem_I2));
            }

            il.Add(Instruction.Create(DnOpCodes.Newobj, stringCtorCharArr));
        }

        private MethodDef BuildDecryptorProxy(ModuleDef module, TypeDef proxyHost,
            MethodDef helperMethod, FieldDef cfZero)
        {
            var assemblyTypeSig = module.Import(typeof(System.Reflection.Assembly)).ToTypeSig();
            var streamTypeSig   = module.Import(typeof(System.IO.Stream)).ToTypeSig();
            var stringTypeSig   = module.CorLibTypes.String;
            var int32TypeSig    = module.CorLibTypes.Int32;

            var proxy = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(streamTypeSig, assemblyTypeSig, stringTypeSig),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            proxy.Body = new CilBody();
            proxy.Body.InitLocals = true;

            var lResult = new Local(streamTypeSig);
            var lNoise  = new Local(int32TypeSig);
            proxy.Body.Variables.Add(lResult);
            proxy.Body.Variables.Add(lNoise);

            var il = proxy.Body.Instructions;

            var skipNoise = Instruction.Create(DnOpCodes.Ldarg_0);
            if (cfZero != null)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldsfld, cfZero));
                il.Add(Instruction.Create(DnOpCodes.Brfalse, skipNoise));
                il.Add(engine.LoadInt(rng.Next()));
                il.Add(engine.LoadInt(rng.Next()));
                il.Add(Instruction.Create(DnOpCodes.Mul));
                il.Add(Instruction.Create(DnOpCodes.Stloc, lNoise));
            }

            il.Add(skipNoise);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Call, helperMethod));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lResult));

            if (cfZero != null)
            {
                var skipNoise2 = Instruction.Create(DnOpCodes.Ldloc, lResult);
                il.Add(Instruction.Create(DnOpCodes.Ldsfld, cfZero));
                il.Add(Instruction.Create(DnOpCodes.Brfalse, skipNoise2));
                il.Add(engine.LoadInt(rng.Next()));
                il.Add(Instruction.Create(DnOpCodes.Stloc, lNoise));
                il.Add(skipNoise2);
            }
            else
            {
                il.Add(Instruction.Create(DnOpCodes.Ldloc, lResult));
            }

            il.Add(Instruction.Create(DnOpCodes.Ret));

            proxyHost.Methods.Add(proxy);
            engine.injectedMethods.Add(proxy);
            return proxy;
        }

        private List<Instruction> BuildAlgebraicOpaquePredicate(ModuleDef module,
            Local lA, Local lB, int patternIdx, int seedA, int seedB)
        {
            var ins = new List<Instruction>();
            switch (patternIdx % 5)
            {
                case 0:
                    ins.Add(engine.LoadInt(seedA));
                    ins.Add(Instruction.Create(DnOpCodes.Stloc, lA));
                    ins.Add(engine.LoadInt(seedB));
                    ins.Add(Instruction.Create(DnOpCodes.Stloc, lB));
                    ins.Add(Instruction.Create(DnOpCodes.Ldloc, lA));
                    ins.Add(Instruction.Create(DnOpCodes.Ldloc, lA));
                    ins.Add(Instruction.Create(DnOpCodes.Mul));
                    ins.Add(Instruction.Create(DnOpCodes.Ldloc, lB));
                    ins.Add(Instruction.Create(DnOpCodes.Ldloc, lB));
                    ins.Add(Instruction.Create(DnOpCodes.Mul));
                    ins.Add(Instruction.Create(DnOpCodes.Sub));
                    ins.Add(Instruction.Create(DnOpCodes.Ldloc, lA));
                    ins.Add(Instruction.Create(DnOpCodes.Ldloc, lB));
                    ins.Add(Instruction.Create(DnOpCodes.Add));
                    ins.Add(Instruction.Create(DnOpCodes.Ldloc, lA));
                    ins.Add(Instruction.Create(DnOpCodes.Ldloc, lB));
                    ins.Add(Instruction.Create(DnOpCodes.Sub));
                    ins.Add(Instruction.Create(DnOpCodes.Mul));
                    ins.Add(Instruction.Create(DnOpCodes.Sub));
                    break;

                case 1:
                    ins.Add(engine.LoadInt(seedA));
                    ins.Add(Instruction.Create(DnOpCodes.Stloc, lA));
                    ins.Add(engine.LoadInt(seedB));
                    ins.Add(Instruction.Create(DnOpCodes.Stloc, lB));
                    ins.Add(Instruction.Create(DnOpCodes.Ldloc, lA));
                    ins.Add(Instruction.Create(DnOpCodes.Ldloc, lB));
                    ins.Add(Instruction.Create(DnOpCodes.Or));
                    ins.Add(Instruction.Create(DnOpCodes.Ldloc, lA));
                    ins.Add(Instruction.Create(DnOpCodes.Ldloc, lB));
                    ins.Add(Instruction.Create(DnOpCodes.And));
                    ins.Add(Instruction.Create(DnOpCodes.Sub));
                    ins.Add(Instruction.Create(DnOpCodes.Ldloc, lA));
                    ins.Add(Instruction.Create(DnOpCodes.Ldloc, lB));
                    ins.Add(Instruction.Create(DnOpCodes.Xor));
                    ins.Add(Instruction.Create(DnOpCodes.Sub));
                    break;

                case 2:
                    ins.Add(engine.LoadInt(seedA));
                    ins.Add(Instruction.Create(DnOpCodes.Stloc, lA));
                    ins.Add(Instruction.Create(DnOpCodes.Ldloc, lA));
                    ins.Add(Instruction.Create(DnOpCodes.Ldc_I4_2));
                    ins.Add(Instruction.Create(DnOpCodes.Mul));
                    ins.Add(Instruction.Create(DnOpCodes.Ldloc, lA));
                    ins.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
                    ins.Add(Instruction.Create(DnOpCodes.Shl));
                    ins.Add(Instruction.Create(DnOpCodes.Sub));
                    break;

                case 3:
                    ins.Add(engine.LoadInt(seedA | 2));
                    ins.Add(Instruction.Create(DnOpCodes.Stloc, lA));
                    ins.Add(Instruction.Create(DnOpCodes.Ldloc, lA));
                    ins.Add(Instruction.Create(DnOpCodes.Ldloc, lA));
                    ins.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
                    ins.Add(Instruction.Create(DnOpCodes.Add));
                    ins.Add(Instruction.Create(DnOpCodes.Mul));
                    ins.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
                    ins.Add(Instruction.Create(DnOpCodes.And));
                    break;

                default:
                    ins.Add(engine.LoadInt(seedA));
                    ins.Add(Instruction.Create(DnOpCodes.Stloc, lA));
                    ins.Add(engine.LoadInt(seedB));
                    ins.Add(Instruction.Create(DnOpCodes.Stloc, lB));
                    ins.Add(Instruction.Create(DnOpCodes.Ldloc, lA));
                    ins.Add(Instruction.Create(DnOpCodes.Ldloc, lB));
                    ins.Add(Instruction.Create(DnOpCodes.Xor));
                    ins.Add(Instruction.Create(DnOpCodes.Ldloc, lA));
                    ins.Add(Instruction.Create(DnOpCodes.Xor));
                    ins.Add(Instruction.Create(DnOpCodes.Ldloc, lB));
                    ins.Add(Instruction.Create(DnOpCodes.Xor));
                    break;
            }
            return ins;
        }

        private List<Instruction> BuildMBADeadBody(Local lJunk, Local lA, Local lB,
            int chainLen, int c1, int c2, int c3)
        {
            var ins = new List<Instruction>();
            ins.Add(Instruction.Create(DnOpCodes.Ldloc, lA));
            ins.Add(Instruction.Create(DnOpCodes.Ldloc, lB));
            ins.Add(Instruction.Create(DnOpCodes.Xor));
            ins.Add(Instruction.Create(DnOpCodes.Stloc, lJunk));

            int[] ops = new int[chainLen];
            int[] consts = new int[chainLen];
            for (int jj = 0; jj < chainLen; jj++)
            {
                ops[jj] = rng.Next(6);
                consts[jj] = rng.Next() | 1;
            }

            for (int jj = 0; jj < chainLen; jj++)
            {
                ins.Add(Instruction.Create(DnOpCodes.Ldloc, lJunk));
                switch (ops[jj])
                {
                    case 0:
                        ins.Add(engine.LoadInt(consts[jj]));
                        ins.Add(Instruction.Create(DnOpCodes.Add));
                        break;
                    case 1:
                        ins.Add(engine.LoadInt(consts[jj]));
                        ins.Add(Instruction.Create(DnOpCodes.Sub));
                        break;
                    case 2:
                        ins.Add(engine.LoadInt(consts[jj]));
                        ins.Add(Instruction.Create(DnOpCodes.Xor));
                        break;
                    case 3:
                        ins.Add(engine.LoadInt(consts[jj] & 0x1F));
                        ins.Add(Instruction.Create(DnOpCodes.Shl));
                        break;
                    case 4:
                        ins.Add(engine.LoadInt(consts[jj] & 0x1F));
                        ins.Add(Instruction.Create(DnOpCodes.Shr_Un));
                        break;
                    default:
                        ins.Add(Instruction.Create(DnOpCodes.Pop));
                        ins.Add(Instruction.Create(DnOpCodes.Ldloc, lJunk));
                        ins.Add(engine.LoadInt(c1));
                        ins.Add(Instruction.Create(DnOpCodes.Or));
                        ins.Add(Instruction.Create(DnOpCodes.Ldloc, lJunk));
                        ins.Add(engine.LoadInt(c1));
                        ins.Add(Instruction.Create(DnOpCodes.And));
                        ins.Add(Instruction.Create(DnOpCodes.Sub));
                        break;
                }
                ins.Add(Instruction.Create(DnOpCodes.Stloc, lJunk));
            }

            ins.Add(Instruction.Create(DnOpCodes.Ldloc, lJunk));
            ins.Add(engine.LoadInt(c2));
            ins.Add(Instruction.Create(DnOpCodes.Mul));
            ins.Add(engine.LoadInt(c3));
            ins.Add(Instruction.Create(DnOpCodes.Xor));
            ins.Add(Instruction.Create(DnOpCodes.Stloc, lJunk));

            return ins;
        }

        private void ApplyInlineFlowToBody(ModuleDef module, MethodDef method, FieldDef cfZero)
        {
            if (!method.HasBody || !method.Body.HasInstructions) return;

            var body = method.Body;
            body.SimplifyBranches();
            body.SimplifyMacros(method.Parameters);

            var il = body.Instructions;
            int n = il.Count;
            if (n < 2) return;

            var ehBoundary = new HashSet<Instruction>();
            if (body.HasExceptionHandlers)
            {
                foreach (var eh in body.ExceptionHandlers)
                {
                    if (eh.TryStart     != null) ehBoundary.Add(eh.TryStart);
                    if (eh.TryEnd       != null) ehBoundary.Add(eh.TryEnd);
                    if (eh.HandlerStart != null) ehBoundary.Add(eh.HandlerStart);
                    if (eh.HandlerEnd   != null) ehBoundary.Add(eh.HandlerEnd);
                    if (eh.FilterStart  != null) ehBoundary.Add(eh.FilterStart);
                }
            }

            var injectionPoints = new List<Instruction>();
            int depth = 0;
            for (int i = 0; i < n; i++)
            {
                var instr = il[i];
                if (depth == 0 && !ehBoundary.Contains(instr))
                {
                    if (i > 0 && instr.OpCode != DnOpCodes.Ret &&
                        instr.OpCode != DnOpCodes.Leave &&
                        instr.OpCode != DnOpCodes.Leave_S)
                    {
                        injectionPoints.Add(instr);
                    }
                }
                depth += GetSimpleStackDelta(instr);
                if (depth < 0) depth = 0;
            }

            if (injectionPoints.Count == 0) return;

            var lJunk = new Local(module.CorLibTypes.Int32);
            var lA    = new Local(module.CorLibTypes.Int32);
            var lB    = new Local(module.CorLibTypes.Int32);
            body.Variables.Add(lJunk);
            body.Variables.Add(lA);
            body.Variables.Add(lB);
            body.InitLocals = true;

            int seedA = rng.Next(2, 0x7FFF);
            int seedB = rng.Next(2, 0x7FFF);
            int c1 = rng.Next() | 1;
            int c2 = rng.Next() | 1;
            int c3 = rng.Next() | 1;

            int maxForks = Math.Max(1, Math.Min(injectionPoints.Count, 3));
            int step = Math.Max(1, injectionPoints.Count / maxForks);

            int predicateIdx = rng.Next(5);

            for (int k = 0; k < maxForks; k++)
            {
                int idx = k * step;
                if (idx >= injectionPoints.Count) break;
                var target = injectionPoints[idx];
                int pi = il.IndexOf(target);
                if (pi < 0) continue;

                var predIns = BuildAlgebraicOpaquePredicate(module, lA, lB,
                    (predicateIdx + k) % 5, seedA + k, seedB + k);

                var brFalse = Instruction.Create(DnOpCodes.Brfalse, target);
                predIns.Add(brFalse);

                int chainLen = 2 + rng.Next(3);
                var deadBody = BuildMBADeadBody(lJunk, lA, lB, chainLen, c1, c2, c3);
                predIns.AddRange(deadBody);

                for (int j = 0; j < predIns.Count; j++)
                    il.Insert(pi + j, predIns[j]);

                injectionPoints.Clear();
                int newN = il.Count;
                depth = 0;
                for (int i = 0; i < newN; i++)
                {
                    var instr2 = il[i];
                    if (depth == 0 && !ehBoundary.Contains(instr2) && i > 0 &&
                        instr2.OpCode != DnOpCodes.Ret &&
                        instr2.OpCode != DnOpCodes.Leave &&
                        instr2.OpCode != DnOpCodes.Leave_S)
                    {
                        injectionPoints.Add(instr2);
                    }
                    depth += GetSimpleStackDelta(instr2);
                    if (depth < 0) depth = 0;
                }
            }

            body.OptimizeBranches();
        }

        private static int GetSimpleStackDelta(Instruction instr)
        {
            if (instr == null) return 0;
            int push = 0, pop = 0;
            switch (instr.OpCode.StackBehaviourPush)
            {
                case StackBehaviour.Push0: push = 0; break;
                case StackBehaviour.Push1:
                case StackBehaviour.Pushi:
                case StackBehaviour.Pushi8:
                case StackBehaviour.Pushr4:
                case StackBehaviour.Pushr8:
                case StackBehaviour.Pushref: push = 1; break;
                case StackBehaviour.Push1_push1: push = 2; break;
                default: push = 0; break;
            }
            switch (instr.OpCode.StackBehaviourPop)
            {
                case StackBehaviour.Pop0: pop = 0; break;
                case StackBehaviour.Pop1:
                case StackBehaviour.Popi:
                case StackBehaviour.Popref: pop = 1; break;
                case StackBehaviour.Pop1_pop1:
                case StackBehaviour.Popi_pop1:
                case StackBehaviour.Popi_popi:
                case StackBehaviour.Popi_popi8:
                case StackBehaviour.Popi_popr4:
                case StackBehaviour.Popi_popr8:
                case StackBehaviour.Popref_pop1:
                case StackBehaviour.Popref_popi: pop = 2; break;
                case StackBehaviour.Popi_popi_popi:
                case StackBehaviour.Popref_popi_popi:
                case StackBehaviour.Popref_popi_popi8:
                case StackBehaviour.Popref_popi_popr4:
                case StackBehaviour.Popref_popi_popr8:
                case StackBehaviour.Popref_popi_popref: pop = 3; break;
                case StackBehaviour.PopAll: pop = 999; break;
                default: pop = 0; break;
            }
            return push - pop;
        }

        internal void ApplyRuntimeEncryption(ModuleDef module, TypeDef modType)
        {
            byte[] masterKey = engine.CryptoRandom(32);
            byte[] masterSalt = engine.CryptoRandom(16);

            var storageType = new TypeDefUser("", engine.MakeName(),
                module.CorLibTypes.Object.TypeDefOrRef);
            storageType.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
            module.Types.Add(storageType);
            engine.injectedTypes.Add(storageType);

            var targetMethods = new List<MethodDef>();
            foreach (TypeDef type in module.GetTypes())
            {
                if (engine.IsCompilerGenerated(type)) continue;
                if (type == storageType) continue;

                if (type.HasGenericParameters) continue;
                if (engine.IsVBInfrastructure(type)) continue;

                if (engine.IsTypeUserExcluded(type)) continue;
                foreach (MethodDef method in type.Methods)
                {
                    if (!method.HasBody || !method.Body.HasInstructions) continue;
                    if (engine.injectedMethods.Contains(method)) continue;
                    if (method.IsConstructor || method.IsStaticConstructor) continue;

                    if (method.HasGenericParameters) continue;
                    if (method.Name == "Create__Instance__" || method.Name == "Dispose__Instance__") continue;
                    if (engine.IsMethodUserExcluded(method)) continue;
                    targetMethods.Add(method);
                }
            }

            if (targetMethods.Count == 0) return;

            foreach (MethodDef method in targetMethods)
            {
                try
                {
                    WrapAndEncryptMethod(module, method, masterKey, masterSalt);
                }
                catch { }
            }

            for (int d = 0; d < rng.Next(3, 8); d++)
            {
                var decoyMethod = new MethodDefUser(engine.MakeName(),
                    MethodSig.CreateStatic(module.CorLibTypes.Void),
                    DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                    DnMethodAttributes.Private | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
                decoyMethod.Body = new CilBody();
                var dIl = decoyMethod.Body.Instructions;
                for (int x = 0; x < rng.Next(5, 20); x++)
                    dIl.Add(Instruction.Create(DnOpCodes.Nop));
                dIl.Add(Instruction.Create(DnOpCodes.Ret));
                storageType.Methods.Add(decoyMethod);
                engine.injectedMethods.Add(decoyMethod);
            }
        }

        private void WrapAndEncryptMethod(ModuleDef module, MethodDef method,
            byte[] masterKey, byte[] masterSalt)
        {
            var il = method.Body.Instructions;
            if (il.Count < 2) return;

            bool hasExistingHandlers = method.Body.HasExceptionHandlers;

            bool isVoid = method.ReturnType.ElementType == ElementType.Void;

            int methodSeed;
            unchecked { methodSeed = method.MDToken.ToInt32() ^ BitConverter.ToInt32(masterKey, 0); }
            int xorA = methodSeed ^ BitConverter.ToInt32(masterSalt, 0);
            int xorB = methodSeed ^ BitConverter.ToInt32(masterSalt, 4);
            int xorC = methodSeed ^ BitConverter.ToInt32(masterSalt, 8);

            int encEnd = il.Count;
            for (int i = 0; i < encEnd; i++)
            {
                if (!engine.IsIntLoad(il[i])) continue;
                int origVal = engine.ExtractInt(il[i]);
                if (origVal == int.MinValue) continue;

                int pattern = rng.Next(0, 3);
                switch (pattern)
                {
                    case 0:
                    {
                        int layer1 = origVal ^ xorA;
                        int layer2 = layer1 + xorB;
                        int layer3 = ~layer2;
                        il[i].OpCode = DnOpCodes.Ldc_I4;
                        il[i].Operand = layer3;
                        il.Insert(i + 1, Instruction.Create(DnOpCodes.Not));
                        il.Insert(i + 2, Instruction.Create(DnOpCodes.Ldc_I4, xorB));
                        il.Insert(i + 3, Instruction.Create(DnOpCodes.Sub));
                        il.Insert(i + 4, Instruction.Create(DnOpCodes.Ldc_I4, xorA));
                        il.Insert(i + 5, Instruction.Create(DnOpCodes.Xor));
                        i += 5; encEnd += 5;
                        break;
                    }
                    case 1:
                    {
                        int k = rng.Next(int.MinValue + 1, int.MaxValue);
                        il[i].OpCode = DnOpCodes.Ldc_I4;
                        il[i].Operand = k;
                        il.Insert(i + 1, Instruction.Create(DnOpCodes.Ldc_I4, k ^ origVal));
                        il.Insert(i + 2, Instruction.Create(DnOpCodes.Xor));
                        i += 2; encEnd += 2;
                        break;
                    }
                    default:
                    {
                        int layer1 = origVal ^ xorC;
                        int layer2 = ~layer1;
                        il[i].OpCode = DnOpCodes.Ldc_I4;
                        il[i].Operand = layer2;
                        il.Insert(i + 1, Instruction.Create(DnOpCodes.Not));
                        il.Insert(i + 2, Instruction.Create(DnOpCodes.Ldc_I4, xorC));
                        il.Insert(i + 3, Instruction.Create(DnOpCodes.Xor));
                        i += 3; encEnd += 3;
                        break;
                    }
                }
            }

            if (hasExistingHandlers) return;
            {
                var exceptionTypeRef = module.Import(typeof(Exception)).ToTypeSig().ToTypeDefOrRef();

                Local returnLocal = null;
                Instruction trySuccessTarget;
                Instruction finalRet = Instruction.Create(DnOpCodes.Ret);

                if (isVoid)
                {
                    trySuccessTarget = finalRet;
                }
                else
                {
                    returnLocal = new Local(method.ReturnType);
                    method.Body.Variables.Add(returnLocal);
                    trySuccessTarget = Instruction.Create(DnOpCodes.Ldloc, returnLocal);
                }

                for (int i = 0; i < il.Count; i++)
                {
                    if (il[i].OpCode == DnOpCodes.Ret)
                    {
                        if (!isVoid)
                        {
                            il.Insert(i, Instruction.Create(DnOpCodes.Stloc, returnLocal));
                            i++;
                        }
                        il[i].OpCode = DnOpCodes.Leave;
                        il[i].Operand = trySuccessTarget;
                    }
                }

                var catchRethrow = Instruction.Create(DnOpCodes.Rethrow);
                il.Add(catchRethrow);

                if (!isVoid)
                {
                    il.Add(trySuccessTarget);
                }
                il.Add(finalRet);

                var handlerEnd = isVoid ? finalRet : trySuccessTarget;
                method.Body.ExceptionHandlers.Add(new ExceptionHandler(ExceptionHandlerType.Catch)
                {
                    TryStart     = il[0],
                    TryEnd       = catchRethrow,
                    HandlerStart = catchRethrow,
                    HandlerEnd   = handlerEnd,
                    CatchType    = exceptionTypeRef
                });

                method.Body.InitLocals = true;
            }

        }

        private static uint ResKeyMvidToSeed(Guid mvid)
        {
            byte[] b = mvid.ToByteArray();
            uint h = 0x9E3779B9u;
            for (int i = 0; i < 16; i += 4)
            {
                uint chunk = unchecked((uint)(b[i] | (b[i + 1] << 8) | (b[i + 2] << 16) | (b[i + 3] << 24)));
                h = unchecked((h ^ chunk) * 0x85EBCA6Bu);
                h = unchecked(((h << 13) | (h >> 19)) * 0xC2B2AE35u);
            }
            h ^= h >> 16;
            h = unchecked(h * 0x85EBCA6Bu);
            h ^= h >> 13;
            h = unchecked(h * 0xC2B2AE35u);
            h ^= h >> 16;
            return h | 1u;
        }

        private static byte[] ResKeyMaskBytes(byte[] plain, uint seed)
        {
            byte[] masked = (byte[])plain.Clone();
            uint state = seed;
            for (int i = 0; i < masked.Length; i++)
            {
                state ^= state << 13;
                state ^= state >> 17;
                state ^= state << 5;
                masked[i] ^= (byte)state;
            }
            return masked;
        }

        private FieldDef EmitResKeyRvaField(ModuleDef module, TypeDef owner,
            MethodDef initMethod, IList<Instruction> il, byte[] plainBytes)
        {
            uint mvidSeed = ResKeyMvidToSeed(module.Mvid ?? Guid.Empty);
            byte[] maskedBytes = ResKeyMaskBytes(plainBytes, mvidSeed);

            var importer = new Importer(module);
            ITypeDefOrRef sysValueType = importer.Import(typeof(ValueType));
            ITypeDefOrRef sysByte      = importer.Import(typeof(byte));
            IMethod rhInitArr = importer.Import(typeof(System.Runtime.CompilerServices.RuntimeHelpers)
                .GetMethod("InitializeArray", new Type[] { typeof(Array), typeof(RuntimeFieldHandle) }));
            IMethod getTypeFromHandle = importer.Import(typeof(Type)
                .GetMethod("GetTypeFromHandle", new Type[] { typeof(RuntimeTypeHandle) }));
            IMethod getModule = importer.Import(typeof(Type).GetProperty("Module").GetGetMethod());
            IMethod getMvid   = importer.Import(typeof(System.Reflection.Module)
                .GetProperty("ModuleVersionId").GetGetMethod());
            IMethod toByteArr = importer.Import(typeof(Guid).GetMethod("ToByteArray", Type.EmptyTypes));

            TypeDef holder = new TypeDefUser("", engine.MakeName(), sysValueType);
            holder.Attributes = DnTypeAttributes.NestedPrivate | DnTypeAttributes.SequentialLayout
                              | DnTypeAttributes.Sealed;
            holder.ClassLayout = new ClassLayoutUser(1, (uint)maskedBytes.Length);
            owner.NestedTypes.Add(holder);
            engine.injectedTypes.Add(holder);

            FieldDef rvaField = new FieldDefUser(engine.MakeName(),
                new FieldSig(holder.ToTypeSig()),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static | DnFieldAttributes.HasFieldRVA);
            rvaField.HasFieldRVA = true;
            rvaField.InitialValue = maskedBytes;
            owner.Fields.Add(rvaField);

            FieldDef arrField = new FieldDefUser(engine.MakeName(),
                new FieldSig(new SZArraySig(module.CorLibTypes.Byte)),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            owner.Fields.Add(arrField);

            var varArr   = new Local(new SZArraySig(module.CorLibTypes.Byte));
            var varIdx   = new Local(module.CorLibTypes.Int32);
            var varGuid  = new Local(importer.ImportAsTypeSig(typeof(Guid)));
            var varMvidB = new Local(new SZArraySig(module.CorLibTypes.Byte));
            var varH     = new Local(module.CorLibTypes.UInt32);
            var varChunk = new Local(module.CorLibTypes.UInt32);
            var varJ     = new Local(module.CorLibTypes.Int32);
            var varState = new Local(module.CorLibTypes.UInt32);

            initMethod.Body.Variables.Add(varArr);
            initMethod.Body.Variables.Add(varIdx);
            initMethod.Body.Variables.Add(varGuid);
            initMethod.Body.Variables.Add(varMvidB);
            initMethod.Body.Variables.Add(varH);
            initMethod.Body.Variables.Add(varChunk);
            initMethod.Body.Variables.Add(varJ);
            initMethod.Body.Variables.Add(varState);

            il.Add(engine.LoadInt(maskedBytes.Length));
            il.Add(Instruction.Create(DnOpCodes.Newarr, sysByte));
            il.Add(Instruction.Create(DnOpCodes.Dup));
            il.Add(Instruction.Create(DnOpCodes.Ldtoken, rvaField));
            il.Add(Instruction.Create(DnOpCodes.Call, rhInitArr));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varArr));

            il.Add(Instruction.Create(DnOpCodes.Ldtoken, (ITypeDefOrRef)owner));
            il.Add(Instruction.Create(DnOpCodes.Call, getTypeFromHandle));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, getModule));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, getMvid));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varGuid));
            il.Add(Instruction.Create(DnOpCodes.Ldloca, varGuid));
            il.Add(Instruction.Create(DnOpCodes.Call, toByteArr));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varMvidB));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, unchecked((int)0x9E3779B9u)));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varH));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varJ));

            var mixCond = Instruction.Create(DnOpCodes.Ldloc, varJ);
            var mixBody = Instruction.Create(DnOpCodes.Ldloc, varMvidB);
            il.Add(Instruction.Create(DnOpCodes.Br, mixCond));
            il.Add(mixBody);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varJ));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varMvidB));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varJ));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_8));
            il.Add(Instruction.Create(DnOpCodes.Shl));
            il.Add(Instruction.Create(DnOpCodes.Or));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varMvidB));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varJ));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_2));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 16));
            il.Add(Instruction.Create(DnOpCodes.Shl));
            il.Add(Instruction.Create(DnOpCodes.Or));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varMvidB));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varJ));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_3));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 24));
            il.Add(Instruction.Create(DnOpCodes.Shl));
            il.Add(Instruction.Create(DnOpCodes.Or));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varChunk));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varChunk));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, unchecked((int)0x85EBCA6Bu)));
            il.Add(Instruction.Create(DnOpCodes.Mul));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varH));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 13));
            il.Add(Instruction.Create(DnOpCodes.Shl));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 19));
            il.Add(Instruction.Create(DnOpCodes.Shr_Un));
            il.Add(Instruction.Create(DnOpCodes.Or));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, unchecked((int)0xC2B2AE35u)));
            il.Add(Instruction.Create(DnOpCodes.Mul));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varH));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varJ));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_4));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varJ));

            il.Add(mixCond);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 16));
            il.Add(Instruction.Create(DnOpCodes.Blt, mixBody));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 16));
            il.Add(Instruction.Create(DnOpCodes.Shr_Un));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, unchecked((int)0x85EBCA6Bu)));
            il.Add(Instruction.Create(DnOpCodes.Mul));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varH));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 13));
            il.Add(Instruction.Create(DnOpCodes.Shr_Un));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, unchecked((int)0xC2B2AE35u)));
            il.Add(Instruction.Create(DnOpCodes.Mul));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varH));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 16));
            il.Add(Instruction.Create(DnOpCodes.Shr_Un));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varH));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Or));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varState));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varIdx));

            var loopCond = Instruction.Create(DnOpCodes.Ldloc, varIdx);
            var loopBody = Instruction.Create(DnOpCodes.Nop);
            il.Add(Instruction.Create(DnOpCodes.Br, loopCond));

            il.Add(loopBody);

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varState));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varState));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 13));
            il.Add(Instruction.Create(DnOpCodes.Shl));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varState));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varState));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varState));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 17));
            il.Add(Instruction.Create(DnOpCodes.Shr_Un));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varState));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varState));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varState));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_5));
            il.Add(Instruction.Create(DnOpCodes.Shl));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varState));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varArr));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varIdx));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varArr));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varIdx));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varState));
            il.Add(Instruction.Create(DnOpCodes.Conv_U1));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Conv_U1));
            il.Add(Instruction.Create(DnOpCodes.Stelem_I1));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varIdx));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varIdx));

            il.Add(loopCond);
            il.Add(engine.LoadInt(maskedBytes.Length));
            il.Add(Instruction.Create(DnOpCodes.Blt, loopBody));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varArr));
            il.Add(Instruction.Create(DnOpCodes.Stsfld, arrField));

            return arrField;
        }

        private static byte[] DerivePerResourceKeyStrong(byte[] masterKey, byte[] salt, byte[] nameBytes)
        {
            byte[] r1material = new byte[masterKey.Length + salt.Length + nameBytes.Length];
            Buffer.BlockCopy(masterKey, 0, r1material, 0, masterKey.Length);
            Buffer.BlockCopy(salt, 0, r1material, masterKey.Length, salt.Length);
            Buffer.BlockCopy(nameBytes, 0, r1material, masterKey.Length + salt.Length, nameBytes.Length);
            byte[] r1;
            using (var sha = SHA256.Create()) r1 = sha.ComputeHash(r1material);

            byte[] r2material = new byte[r1.Length + nameBytes.Length + masterKey.Length];
            Buffer.BlockCopy(r1, 0, r2material, 0, r1.Length);
            Buffer.BlockCopy(nameBytes, 0, r2material, r1.Length, nameBytes.Length);
            Buffer.BlockCopy(masterKey, 0, r2material, r1.Length + nameBytes.Length, masterKey.Length);
            byte[] r2;
            using (var sha = SHA256.Create()) r2 = sha.ComputeHash(r2material);

            byte[] r3material = new byte[salt.Length + r2.Length + r1.Length];
            Buffer.BlockCopy(salt, 0, r3material, 0, salt.Length);
            Buffer.BlockCopy(r2, 0, r3material, salt.Length, r2.Length);
            Buffer.BlockCopy(r1, 0, r3material, salt.Length + r2.Length, r1.Length);
            using (var sha = SHA256.Create()) return sha.ComputeHash(r3material);
        }

        private static byte[] GenerateXorKeystream(byte[] mvidBytes, byte[] salt, byte[] nameBytes, int length)
        {
            byte[] seedMat = new byte[mvidBytes.Length + salt.Length + nameBytes.Length];
            Buffer.BlockCopy(mvidBytes, 0, seedMat, 0, mvidBytes.Length);
            Buffer.BlockCopy(salt, 0, seedMat, mvidBytes.Length, salt.Length);
            Buffer.BlockCopy(nameBytes, 0, seedMat, mvidBytes.Length + salt.Length, nameBytes.Length);
            byte[] seed;
            using (var sha = SHA256.Create()) seed = sha.ComputeHash(seedMat);

            byte[] ks = new byte[length];
            int pos = 0;
            int counter = 0;
            while (pos < length)
            {
                byte[] blkMat = new byte[seed.Length + 4];
                Buffer.BlockCopy(seed, 0, blkMat, 0, seed.Length);
                blkMat[seed.Length]     = (byte)(counter);
                blkMat[seed.Length + 1] = (byte)(counter >> 8);
                blkMat[seed.Length + 2] = (byte)(counter >> 16);
                blkMat[seed.Length + 3] = (byte)(counter >> 24);
                byte[] block;
                using (var sha = SHA256.Create()) block = sha.ComputeHash(blkMat);
                int take = Math.Min(32, length - pos);
                Buffer.BlockCopy(block, 0, ks, pos, take);
                pos += take;
                counter++;
            }
            return ks;
        }

        internal void ApplyResourceProtection(ModuleDef module, TypeDef modType)
        {
            bool deepResources = true;
            var resources = module.Resources.OfType<EmbeddedResource>()
                .Where(r => !engine.injectedResources.Contains(r.Name))
                .Where(r => deepResources || r.Name.String == null ||
                            !r.Name.String.EndsWith(".resources", StringComparison.OrdinalIgnoreCase))
                .ToList();
            if (resources.Count == 0) return;

            byte[] masterKey = engine.CryptoRandom(32);
            byte[] perBuildSalt = engine.CryptoRandom(16);
            byte[] mvidBytes = (module.Mvid ?? Guid.Empty).ToByteArray();

            var encryptedNames = new List<string>();
            foreach (var res in resources)
            {
                byte[] nameBytes = System.Text.Encoding.UTF8.GetBytes(res.Name.String ?? "");
                byte[] perKey = DerivePerResourceKeyStrong(masterKey, perBuildSalt, nameBytes);

                byte[] perIv = engine.CryptoRandom(16);

                byte[] raw = res.CreateReader().ReadRemainingBytes();

                byte[] compressed;
                using (var ms = new MemoryStream())
                {
                    using (var ds = new DeflateStream(ms, CompressionMode.Compress, true))
                        ds.Write(raw, 0, raw.Length);
                    compressed = ms.ToArray();
                }

                byte[] ks = GenerateXorKeystream(mvidBytes, perBuildSalt, nameBytes, compressed.Length);
                for (int xi = 0; xi < compressed.Length; xi++)
                    compressed[xi] ^= ks[xi];
                Array.Clear(ks, 0, ks.Length);

                byte[] aesOut;
                using (var aes = Aes.Create())
                {
                    aes.Key = perKey;
                    aes.IV = perIv;
                    aes.Mode = CipherMode.CBC;
                    aes.Padding = PaddingMode.PKCS7;
                    using (var enc = aes.CreateEncryptor())
                        aesOut = enc.TransformFinalBlock(compressed, 0, compressed.Length);
                }

                byte[] blob2 = new byte[16 + aesOut.Length];
                Buffer.BlockCopy(perIv, 0, blob2, 0, 16);
                Buffer.BlockCopy(aesOut, 0, blob2, 16, aesOut.Length);

                Array.Clear(perKey, 0, perKey.Length);
                Array.Clear(compressed, 0, compressed.Length);

                module.Resources.Remove(res);
                module.Resources.Add(new EmbeddedResource(res.Name, blob2, res.Attributes));
                encryptedNames.Add(res.Name);
                engine.injectedResources.Add(res.Name);
            }

            var byteArrSig = new SZArraySig(module.CorLibTypes.Byte);
            var strArrSig = new SZArraySig(module.CorLibTypes.String);

            var namesField = new FieldDefUser(engine.MakeName(),
                new FieldSig(strArrSig),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            modType.Fields.Add(namesField);

            var initMethod = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Void),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            initMethod.Body = new CilBody();
            initMethod.Body.InitLocals = true;
            var initIl = initMethod.Body.Instructions;

            FieldDef keyField  = EmitResKeyRvaField(module, modType, initMethod, initIl, masterKey);
            FieldDef saltField = EmitResKeyRvaField(module, modType, initMethod, initIl, perBuildSalt);

            byte[] blob;
            using (var ms = new System.IO.MemoryStream())
            {
                var bw = new System.IO.BinaryWriter(ms);
                bw.Write((int)encryptedNames.Count);
                foreach (var n in encryptedNames)
                {
                    byte[] u8 = System.Text.Encoding.UTF8.GetBytes(n);
                    bw.Write((int)u8.Length);
                    bw.Write(u8);
                }
                bw.Flush();
                blob = ms.ToArray();
            }

            var encodingUtf8Get = module.Import(typeof(System.Text.Encoding).GetProperty("UTF8").GetGetMethod());
            var encodingGetString = module.Import(typeof(System.Text.Encoding)
                .GetMethod("GetString", new[] { typeof(byte[]), typeof(int), typeof(int) }));
            var bitConvToInt32 = module.Import(typeof(BitConverter)
                .GetMethod("ToInt32", new[] { typeof(byte[]), typeof(int) }));

            Local lBlob = new Local(byteArrSig); initMethod.Body.Variables.Add(lBlob);
            Local lOff  = new Local(module.CorLibTypes.Int32); initMethod.Body.Variables.Add(lOff);
            Local lCnt  = new Local(module.CorLibTypes.Int32); initMethod.Body.Variables.Add(lCnt);
            Local lIdx  = new Local(module.CorLibTypes.Int32); initMethod.Body.Variables.Add(lIdx);
            Local lLen  = new Local(module.CorLibTypes.Int32); initMethod.Body.Variables.Add(lLen);
            initMethod.Body.InitLocals = true;

            EmitLoadByteArray(initIl, module, blob);
            initIl.Add(Instruction.Create(DnOpCodes.Stloc, lBlob));

            initIl.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            initIl.Add(Instruction.Create(DnOpCodes.Stloc, lOff));

            initIl.Add(Instruction.Create(DnOpCodes.Ldloc, lBlob));
            initIl.Add(Instruction.Create(DnOpCodes.Ldloc, lOff));
            initIl.Add(Instruction.Create(DnOpCodes.Call, bitConvToInt32));
            initIl.Add(Instruction.Create(DnOpCodes.Stloc, lCnt));

            initIl.Add(Instruction.Create(DnOpCodes.Ldloc, lOff));
            initIl.Add(Instruction.Create(DnOpCodes.Ldc_I4_4));
            initIl.Add(Instruction.Create(DnOpCodes.Add));
            initIl.Add(Instruction.Create(DnOpCodes.Stloc, lOff));

            initIl.Add(Instruction.Create(DnOpCodes.Ldloc, lCnt));
            initIl.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.String.TypeDefOrRef));
            initIl.Add(Instruction.Create(DnOpCodes.Stsfld, namesField));

            initIl.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            initIl.Add(Instruction.Create(DnOpCodes.Stloc, lIdx));

            var loopTop = Instruction.Create(DnOpCodes.Ldloc, lIdx);
            var loopEnd = Instruction.Create(DnOpCodes.Ret);
            initIl.Add(loopTop);
            initIl.Add(Instruction.Create(DnOpCodes.Ldloc, lCnt));
            initIl.Add(Instruction.Create(DnOpCodes.Bge, loopEnd));

            initIl.Add(Instruction.Create(DnOpCodes.Ldloc, lBlob));
            initIl.Add(Instruction.Create(DnOpCodes.Ldloc, lOff));
            initIl.Add(Instruction.Create(DnOpCodes.Call, bitConvToInt32));
            initIl.Add(Instruction.Create(DnOpCodes.Stloc, lLen));

            initIl.Add(Instruction.Create(DnOpCodes.Ldloc, lOff));
            initIl.Add(Instruction.Create(DnOpCodes.Ldc_I4_4));
            initIl.Add(Instruction.Create(DnOpCodes.Add));
            initIl.Add(Instruction.Create(DnOpCodes.Stloc, lOff));

            initIl.Add(Instruction.Create(DnOpCodes.Ldsfld, namesField));
            initIl.Add(Instruction.Create(DnOpCodes.Ldloc, lIdx));
            initIl.Add(Instruction.Create(DnOpCodes.Call, encodingUtf8Get));
            initIl.Add(Instruction.Create(DnOpCodes.Ldloc, lBlob));
            initIl.Add(Instruction.Create(DnOpCodes.Ldloc, lOff));
            initIl.Add(Instruction.Create(DnOpCodes.Ldloc, lLen));
            initIl.Add(Instruction.Create(DnOpCodes.Callvirt, encodingGetString));
            initIl.Add(Instruction.Create(DnOpCodes.Stelem_Ref));

            initIl.Add(Instruction.Create(DnOpCodes.Ldloc, lOff));
            initIl.Add(Instruction.Create(DnOpCodes.Ldloc, lLen));
            initIl.Add(Instruction.Create(DnOpCodes.Add));
            initIl.Add(Instruction.Create(DnOpCodes.Stloc, lOff));

            initIl.Add(Instruction.Create(DnOpCodes.Ldloc, lIdx));
            initIl.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            initIl.Add(Instruction.Create(DnOpCodes.Add));
            initIl.Add(Instruction.Create(DnOpCodes.Stloc, lIdx));
            initIl.Add(Instruction.Create(DnOpCodes.Br, loopTop));

            initIl.Add(loopEnd);
            modType.Methods.Add(initMethod);
            engine.injectedMethods.Add(initMethod);
            engine.InjectCallInCctor(module, modType, initMethod);

            Array.Clear(masterKey, 0, masterKey.Length);
            Array.Clear(perBuildSalt, 0, perBuildSalt.Length);

            MethodDef helperMethod;
            try
            {
                helperMethod = BuildResourceDecryptor(module, modType,
                    keyField, saltField, namesField);
            }
            catch
            {
                return;
            }

            try { ApplyInlineFlowToBody(module, helperMethod, EnsureRPCfZeroField(module)); } catch { }

            try
            {
                RewriteResourceCallsites(module, helperMethod);
            }
            catch { }

            bool hasAnyResourcesFile = false;
            foreach (var n in encryptedNames)
            {
                if (n.EndsWith(".resources", StringComparison.OrdinalIgnoreCase))
                {
                    hasAnyResourcesFile = true;
                    break;
                }
            }
            if (hasAnyResourcesFile)
            {
                try
                {
                    MethodDef customRMStrAsmCtor;
                    MethodDef customRMTypeFactory;
                    BuildCustomResourceManager(module, helperMethod,
                        out customRMStrAsmCtor, out customRMTypeFactory);
                    RewriteResourceManagerCtorCalls(module, customRMStrAsmCtor, customRMTypeFactory);
                }
                catch
                {

                }

                try
                {
                    MethodDef customCRMCtor = BuildCustomComponentResourceManager(module, helperMethod);
                    RewriteComponentResourceManagerCtorCalls(module, customCRMCtor);
                }
                catch
                {

                }
            }

            string[] decoyExtensions = new string[] { ".resources", ".resources", ".resources", "" };
            for (int d = 0; d < rng.Next(8, 20); d++)
            {
                byte[] fakeData = engine.CryptoRandom(rng.Next(100, 2000));
                string decoyExt = decoyExtensions[rng.Next(decoyExtensions.Length)];
                module.Resources.Add(new EmbeddedResource(engine.MakeName() + decoyExt, fakeData));
            }
        }

        private void BuildCustomResourceManager(ModuleDef module, MethodDef helperMethod,
            out MethodDef strAsmCtorOut, out MethodDef typeCtorOut)
        {
            var rmTypeRef       = module.Import(typeof(System.Resources.ResourceManager));
            var rsTypeRef       = module.Import(typeof(System.Resources.ResourceSet));
            var cultureTypeRef  = module.Import(typeof(System.Globalization.CultureInfo));
            var streamTypeRef   = module.Import(typeof(System.IO.Stream));
            var assemblyTypeRef = module.Import(typeof(System.Reflection.Assembly));
            var typeTypeRef     = module.Import(typeof(System.Type));
            var exceptionRef    = module.Import(typeof(Exception)).ToTypeSig().ToTypeDefOrRef();

            var stringType = module.CorLibTypes.String;
            var boolType   = module.CorLibTypes.Boolean;
            var voidType   = module.CorLibTypes.Void;

            var baseCtorRef = module.Import(typeof(System.Resources.ResourceManager)
                .GetConstructor(new[] { typeof(string), typeof(System.Reflection.Assembly) }));
            var baseCtorTypeRef = module.Import(typeof(System.Resources.ResourceManager)
                .GetConstructor(new[] { typeof(Type) }));
            var typeFullNameGet = module.Import(typeof(Type).GetProperty("FullName").GetGetMethod());
            var typeAssemblyGet = module.Import(typeof(Type).GetProperty("Assembly").GetGetMethod());
            var baseInternalGetRsRef = module.Import(typeof(System.Resources.ResourceManager)
                .GetMethod("InternalGetResourceSet",
                    System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Instance,
                    null,
                    new[]
                    {
                        typeof(System.Globalization.CultureInfo),
                        typeof(bool), typeof(bool)
                    },
                    null));
            var rsCtorRef = module.Import(typeof(System.Resources.ResourceSet)
                .GetConstructor(new[] { typeof(System.IO.Stream) }));
            var strConcatRef = module.Import(typeof(string)
                .GetMethod("Concat", new[] { typeof(string), typeof(string) }));

            var customRM = new TypeDefUser("", engine.MakeName(), rmTypeRef);
            customRM.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Class |
                                  DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
            module.Types.Add(customRM);
            engine.injectedTypes.Add(customRM);

            var rsField = new FieldDefUser(engine.MakeName(),
                new FieldSig(rsTypeRef.ToTypeSig()),
                DnFieldAttributes.Private);
            customRM.Fields.Add(rsField);

            var rmCfZero = EnsureRPCfZeroField(module);
            var rmProxy = BuildDecryptorProxy(module, customRM, helperMethod, rmCfZero);

            var ctor = new MethodDefUser(".ctor",
                MethodSig.CreateInstance(voidType, stringType, assemblyTypeRef.ToTypeSig()),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Public | DnMethodAttributes.HideBySig |
                DnMethodAttributes.SpecialName | DnMethodAttributes.RTSpecialName);
            ctor.Body = new CilBody();
            ctor.Body.InitLocals = true;
            var streamLocal = new Local(streamTypeRef.ToTypeSig());
            ctor.Body.Variables.Add(streamLocal);

            var cIl = ctor.Body.Instructions;

            cIl.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            cIl.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            cIl.Add(Instruction.Create(DnOpCodes.Ldarg_2));
            cIl.Add(Instruction.Create(DnOpCodes.Call, baseCtorRef));

            var finalRet       = Instruction.Create(DnOpCodes.Ret);
            var tryStart       = Instruction.Create(DnOpCodes.Ldarg_2);
            var leaveAfterTry  = Instruction.Create(DnOpCodes.Leave, finalRet);
            var catchStart     = Instruction.Create(DnOpCodes.Pop);
            var leaveAfterCatch= Instruction.Create(DnOpCodes.Leave, finalRet);

            cIl.Add(tryStart);
            cIl.Add(Instruction.Create(DnOpCodes.Ldarg_2));
            cIl.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            EmitObfuscatedStringIL(cIl, module, ".resources");
            cIl.Add(Instruction.Create(DnOpCodes.Call, strConcatRef));
            cIl.Add(Instruction.Create(DnOpCodes.Call, rmProxy));
            cIl.Add(Instruction.Create(DnOpCodes.Stloc, streamLocal));
            cIl.Add(Instruction.Create(DnOpCodes.Ldloc, streamLocal));
            cIl.Add(Instruction.Create(DnOpCodes.Brfalse, leaveAfterTry));
            cIl.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            cIl.Add(Instruction.Create(DnOpCodes.Ldloc, streamLocal));
            cIl.Add(Instruction.Create(DnOpCodes.Newobj, rsCtorRef));
            cIl.Add(Instruction.Create(DnOpCodes.Stfld, rsField));
            cIl.Add(leaveAfterTry);
            cIl.Add(catchStart);
            cIl.Add(leaveAfterCatch);
            cIl.Add(finalRet);

            ctor.Body.ExceptionHandlers.Add(new ExceptionHandler(ExceptionHandlerType.Catch)
            {
                TryStart     = tryStart,
                TryEnd       = catchStart,
                HandlerStart = catchStart,
                HandlerEnd   = finalRet,
                CatchType    = exceptionRef
            });

            customRM.Methods.Add(ctor);
            engine.injectedMethods.Add(ctor);

            string overrideRandName = engine.MakeName();
            var overrideMethod = new MethodDefUser(overrideRandName,
                MethodSig.CreateInstance(rsTypeRef.ToTypeSig(),
                    cultureTypeRef.ToTypeSig(), boolType, boolType),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Private | DnMethodAttributes.HideBySig |
                DnMethodAttributes.Virtual | DnMethodAttributes.NewSlot);
            overrideMethod.Body = new CilBody();
            var oIl = overrideMethod.Body.Instructions;

            var callBase = Instruction.Create(DnOpCodes.Ldarg_0);
            oIl.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            oIl.Add(Instruction.Create(DnOpCodes.Ldfld, rsField));
            oIl.Add(Instruction.Create(DnOpCodes.Brfalse, callBase));
            oIl.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            oIl.Add(Instruction.Create(DnOpCodes.Ldfld, rsField));
            oIl.Add(Instruction.Create(DnOpCodes.Ret));
            oIl.Add(callBase);
            oIl.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            oIl.Add(Instruction.Create(DnOpCodes.Ldarg_2));
            oIl.Add(Instruction.Create(DnOpCodes.Ldarg_3));
            oIl.Add(Instruction.Create(DnOpCodes.Call, baseInternalGetRsRef));
            oIl.Add(Instruction.Create(DnOpCodes.Ret));

            overrideMethod.Overrides.Add(new MethodOverride(overrideMethod, (IMethodDefOrRef)baseInternalGetRsRef));

            customRM.Methods.Add(overrideMethod);
            engine.injectedMethods.Add(overrideMethod);

            try { ApplyInlineFlowToBody(module, overrideMethod, rmCfZero); } catch { }

            strAsmCtorOut = ctor;
            typeCtorOut = null;
        }

        private void RewriteResourceManagerCtorCalls(ModuleDef module,
            MethodDef strAsmCtor, MethodDef unused)
        {
            var typeRef = module.Import(typeof(System.Type));
            var typeFullNameGet = module.Import(typeof(Type).GetProperty("FullName").GetGetMethod());
            var typeAssemblyGet = module.Import(typeof(Type).GetProperty("Assembly").GetGetMethod());

            foreach (TypeDef type in module.GetTypes())
            {
                if (engine.injectedTypes.Contains(type)) continue;
                if (engine.IsTypeUserExcluded(type)) continue;
                foreach (MethodDef method in type.Methods)
                {
                    if (!method.HasBody || !method.Body.HasInstructions) continue;
                    if (engine.injectedMethods.Contains(method)) continue;
                    if (engine.IsMethodUserExcluded(method)) continue;
                    var ins = method.Body.Instructions;

                    for (int i = 0; i < ins.Count; i++)
                    {
                        var instr = ins[i];
                        if (instr.OpCode != DnOpCodes.Newobj) continue;
                        var target = instr.Operand as IMethod;
                        if (target == null) continue;
                        if (target.Name != ".ctor") continue;
                        var decl = target.DeclaringType;
                        if (decl == null) continue;
                        if (decl.FullName != "System.Resources.ResourceManager") continue;
                        var sig = target.MethodSig;
                        if (sig == null) continue;

                        if (sig.Params.Count == 2
                            && sig.Params[0].FullName == "System.String"
                            && sig.Params[1].FullName == "System.Reflection.Assembly")
                        {
                            instr.Operand = strAsmCtor;
                        }
                        else if (sig.Params.Count == 3
                            && sig.Params[0].FullName == "System.String"
                            && sig.Params[1].FullName == "System.Reflection.Assembly"
                            && sig.Params[2].FullName == "System.Type")
                        {
                            ins.Insert(i, Instruction.Create(DnOpCodes.Pop));
                            i++;
                            instr.Operand = strAsmCtor;
                        }
                        else if (sig.Params.Count == 1
                            && sig.Params[0].FullName == "System.Type")
                        {
                            Local tempType = new Local(typeRef.ToTypeSig());
                            method.Body.Variables.Add(tempType);
                            method.Body.InitLocals = true;

                            instr.OpCode = DnOpCodes.Stloc;
                            instr.Operand = tempType;

                            int insertAt = i + 1;
                            ins.Insert(insertAt++, Instruction.Create(DnOpCodes.Ldloc, tempType));
                            ins.Insert(insertAt++, Instruction.Create(DnOpCodes.Callvirt, typeFullNameGet));
                            ins.Insert(insertAt++, Instruction.Create(DnOpCodes.Ldloc, tempType));
                            ins.Insert(insertAt++, Instruction.Create(DnOpCodes.Callvirt, typeAssemblyGet));
                            ins.Insert(insertAt++, Instruction.Create(DnOpCodes.Newobj, strAsmCtor));
                            i = insertAt - 1;
                        }
                    }
                }
            }
        }

        private MethodDef BuildCustomComponentResourceManager(ModuleDef module, MethodDef helperMethod)
        {
            var crmTypeRef      = module.Import(typeof(System.ComponentModel.ComponentResourceManager));
            var rsTypeRef       = module.Import(typeof(System.Resources.ResourceSet));
            var cultureTypeRef  = module.Import(typeof(System.Globalization.CultureInfo));
            var streamTypeRef   = module.Import(typeof(System.IO.Stream));
            var typeTypeRef     = module.Import(typeof(System.Type));
            var exceptionRef    = module.Import(typeof(Exception)).ToTypeSig().ToTypeDefOrRef();

            var boolType = module.CorLibTypes.Boolean;
            var voidType = module.CorLibTypes.Void;

            var baseCtorRef = module.Import(typeof(System.ComponentModel.ComponentResourceManager)
                .GetConstructor(new[] { typeof(Type) }));
            var baseInternalGetRsRef = module.Import(typeof(System.Resources.ResourceManager)
                .GetMethod("InternalGetResourceSet",
                    System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Instance,
                    null,
                    new[]
                    {
                        typeof(System.Globalization.CultureInfo),
                        typeof(bool), typeof(bool)
                    },
                    null));
            var rsCtorRef = module.Import(typeof(System.Resources.ResourceSet)
                .GetConstructor(new[] { typeof(System.IO.Stream) }));
            var typeFullNameGet = module.Import(typeof(Type).GetProperty("FullName").GetGetMethod());
            var typeAssemblyGet = module.Import(typeof(Type).GetProperty("Assembly").GetGetMethod());
            var strConcatRef = module.Import(typeof(string)
                .GetMethod("Concat", new[] { typeof(string), typeof(string) }));

            var customCRM = new TypeDefUser("", engine.MakeName(), crmTypeRef);
            customCRM.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Class |
                                   DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
            module.Types.Add(customCRM);
            engine.injectedTypes.Add(customCRM);

            var rsField = new FieldDefUser(engine.MakeName(),
                new FieldSig(rsTypeRef.ToTypeSig()),
                DnFieldAttributes.Private);
            customCRM.Fields.Add(rsField);

            var crmCfZero = EnsureRPCfZeroField(module);
            var crmProxy = BuildDecryptorProxy(module, customCRM, helperMethod, crmCfZero);

            var ctor = new MethodDefUser(".ctor",
                MethodSig.CreateInstance(voidType, typeTypeRef.ToTypeSig()),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Public | DnMethodAttributes.HideBySig |
                DnMethodAttributes.SpecialName | DnMethodAttributes.RTSpecialName);
            ctor.Body = new CilBody();
            ctor.Body.InitLocals = true;
            var streamLocal = new Local(streamTypeRef.ToTypeSig());
            ctor.Body.Variables.Add(streamLocal);

            var cIl = ctor.Body.Instructions;

            cIl.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            cIl.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            cIl.Add(Instruction.Create(DnOpCodes.Call, baseCtorRef));

            var finalRet        = Instruction.Create(DnOpCodes.Ret);
            var tryStart        = Instruction.Create(DnOpCodes.Ldarg_1);
            var leaveAfterTry   = Instruction.Create(DnOpCodes.Leave, finalRet);
            var catchStart      = Instruction.Create(DnOpCodes.Pop);
            var leaveAfterCatch = Instruction.Create(DnOpCodes.Leave, finalRet);

            cIl.Add(tryStart);
            cIl.Add(Instruction.Create(DnOpCodes.Callvirt, typeAssemblyGet));
            cIl.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            cIl.Add(Instruction.Create(DnOpCodes.Callvirt, typeFullNameGet));
            EmitObfuscatedStringIL(cIl, module, ".resources");
            cIl.Add(Instruction.Create(DnOpCodes.Call, strConcatRef));
            cIl.Add(Instruction.Create(DnOpCodes.Call, crmProxy));
            cIl.Add(Instruction.Create(DnOpCodes.Stloc, streamLocal));
            cIl.Add(Instruction.Create(DnOpCodes.Ldloc, streamLocal));
            cIl.Add(Instruction.Create(DnOpCodes.Brfalse, leaveAfterTry));
            cIl.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            cIl.Add(Instruction.Create(DnOpCodes.Ldloc, streamLocal));
            cIl.Add(Instruction.Create(DnOpCodes.Newobj, rsCtorRef));
            cIl.Add(Instruction.Create(DnOpCodes.Stfld, rsField));
            cIl.Add(leaveAfterTry);
            cIl.Add(catchStart);
            cIl.Add(leaveAfterCatch);
            cIl.Add(finalRet);

            ctor.Body.ExceptionHandlers.Add(new ExceptionHandler(ExceptionHandlerType.Catch)
            {
                TryStart     = tryStart,
                TryEnd       = catchStart,
                HandlerStart = catchStart,
                HandlerEnd   = finalRet,
                CatchType    = exceptionRef
            });

            customCRM.Methods.Add(ctor);
            engine.injectedMethods.Add(ctor);

            string crmOverrideRandName = engine.MakeName();
            var overrideMethod = new MethodDefUser(crmOverrideRandName,
                MethodSig.CreateInstance(rsTypeRef.ToTypeSig(),
                    cultureTypeRef.ToTypeSig(), boolType, boolType),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Private | DnMethodAttributes.HideBySig |
                DnMethodAttributes.Virtual | DnMethodAttributes.NewSlot);
            overrideMethod.Body = new CilBody();
            var oIl = overrideMethod.Body.Instructions;

            var callBase = Instruction.Create(DnOpCodes.Ldarg_0);
            oIl.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            oIl.Add(Instruction.Create(DnOpCodes.Ldfld, rsField));
            oIl.Add(Instruction.Create(DnOpCodes.Brfalse, callBase));
            oIl.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            oIl.Add(Instruction.Create(DnOpCodes.Ldfld, rsField));
            oIl.Add(Instruction.Create(DnOpCodes.Ret));
            oIl.Add(callBase);
            oIl.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            oIl.Add(Instruction.Create(DnOpCodes.Ldarg_2));
            oIl.Add(Instruction.Create(DnOpCodes.Ldarg_3));
            oIl.Add(Instruction.Create(DnOpCodes.Call, baseInternalGetRsRef));
            oIl.Add(Instruction.Create(DnOpCodes.Ret));

            overrideMethod.Overrides.Add(new MethodOverride(overrideMethod, (IMethodDefOrRef)baseInternalGetRsRef));

            customCRM.Methods.Add(overrideMethod);
            engine.injectedMethods.Add(overrideMethod);

            try { ApplyInlineFlowToBody(module, overrideMethod, crmCfZero); } catch { }

            return ctor;
        }

        private void RewriteComponentResourceManagerCtorCalls(ModuleDef module, MethodDef customCRMCtor)
        {
            foreach (TypeDef type in module.GetTypes())
            {
                if (engine.injectedTypes.Contains(type)) continue;
                if (engine.IsTypeUserExcluded(type)) continue;
                foreach (MethodDef method in type.Methods)
                {
                    if (!method.HasBody || !method.Body.HasInstructions) continue;
                    if (engine.injectedMethods.Contains(method)) continue;
                    if (engine.IsMethodUserExcluded(method)) continue;
                    var ins = method.Body.Instructions;
                    for (int i = 0; i < ins.Count; i++)
                    {
                        var instr = ins[i];
                        if (instr.OpCode != DnOpCodes.Newobj) continue;
                        var target = instr.Operand as IMethod;
                        if (target == null) continue;
                        if (target.Name != ".ctor") continue;
                        var decl = target.DeclaringType;
                        if (decl == null) continue;
                        if (decl.FullName != "System.ComponentModel.ComponentResourceManager") continue;
                        var sig = target.MethodSig;
                        if (sig == null || sig.Params.Count != 1) continue;
                        if (sig.Params[0].FullName != "System.Type") continue;
                        instr.Operand = customCRMCtor;
                    }
                }
            }
        }

        private void EmitLoadByteArray(IList<Instruction> il, ModuleDef module, byte[] data)
        {
            il.Add(engine.LoadInt(data.Length));
            il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.Byte.TypeDefOrRef));
            for (int i = 0; i < data.Length; i++)
            {
                il.Add(Instruction.Create(DnOpCodes.Dup));
                il.Add(engine.LoadInt(i));
                il.Add(engine.LoadInt(data[i]));
                il.Add(Instruction.Create(DnOpCodes.Conv_U1));
                il.Add(Instruction.Create(DnOpCodes.Stelem_I1));
            }
        }

        private void EmitSha256Hash(IList<Instruction> il, ModuleDef module,
            IMethod sha256Create, IMethod hashAlgComputeHash,
            Local lShaTemp, Local lMat, Local lResult)
        {
            il.Add(Instruction.Create(DnOpCodes.Call, sha256Create));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lShaTemp));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lShaTemp));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMat));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, hashAlgComputeHash));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lResult));
        }

        private void EmitLoadMvidBytes(IList<Instruction> il, ModuleDef module,
            TypeDef owner, Local lGuid, Local lMvidB,
            IMethod getTypeFromHandle, IMethod getModule, IMethod getMvid, IMethod toByteArr)
        {
            il.Add(Instruction.Create(DnOpCodes.Ldtoken, (ITypeDefOrRef)owner));
            il.Add(Instruction.Create(DnOpCodes.Call, getTypeFromHandle));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, getModule));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, getMvid));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lGuid));
            il.Add(Instruction.Create(DnOpCodes.Ldloca, lGuid));
            il.Add(Instruction.Create(DnOpCodes.Call, toByteArr));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lMvidB));
        }

        private MethodDef BuildResourceDecryptor(ModuleDef module, TypeDef modType,
            FieldDef keyField, FieldDef saltField, FieldDef namesField)
        {
            var importer = new Importer(module);
            var assemblyType = module.Import(typeof(System.Reflection.Assembly));
            var streamType   = module.Import(typeof(System.IO.Stream));
            var memStreamType= module.Import(typeof(System.IO.MemoryStream));
            var deflateType  = module.Import(typeof(System.IO.Compression.DeflateStream));
            var aesType      = module.Import(typeof(System.Security.Cryptography.Aes));
            var cryptoXformType = module.Import(typeof(System.Security.Cryptography.ICryptoTransform));
            var byteArrSig   = new SZArraySig(module.CorLibTypes.Byte);
            var sha256Type   = module.Import(typeof(System.Security.Cryptography.SHA256));
            var arrayClearRef= module.Import(typeof(Array)
                .GetMethod("Clear", new[] { typeof(Array), typeof(int), typeof(int) }));

            var getManifestRef = module.Import(typeof(System.Reflection.Assembly)
                .GetMethod("GetManifestResourceStream", new[] { typeof(string) }));
            var streamGetLength = module.Import(typeof(System.IO.Stream).GetMethod("get_Length"));
            var streamRead = module.Import(typeof(System.IO.Stream)
                .GetMethod("Read", new[] { typeof(byte[]), typeof(int), typeof(int) }));
            var streamCopyTo = module.Import(typeof(System.IO.Stream)
                .GetMethod("CopyTo", new[] { typeof(System.IO.Stream) }));
            var stringOpEq = module.Import(typeof(string)
                .GetMethod("op_Equality", new[] { typeof(string), typeof(string) }));
            var aesCreate = module.Import(typeof(System.Security.Cryptography.Aes)
                .GetMethod("Create", Type.EmptyTypes));
            var setMode = module.Import(typeof(System.Security.Cryptography.SymmetricAlgorithm)
                .GetMethod("set_Mode", new[] { typeof(System.Security.Cryptography.CipherMode) }));
            var setPadding = module.Import(typeof(System.Security.Cryptography.SymmetricAlgorithm)
                .GetMethod("set_Padding", new[] { typeof(System.Security.Cryptography.PaddingMode) }));
            var setKey = module.Import(typeof(System.Security.Cryptography.SymmetricAlgorithm)
                .GetMethod("set_Key", new[] { typeof(byte[]) }));
            var setIV = module.Import(typeof(System.Security.Cryptography.SymmetricAlgorithm)
                .GetMethod("set_IV", new[] { typeof(byte[]) }));
            var createDecryptor = module.Import(typeof(System.Security.Cryptography.SymmetricAlgorithm)
                .GetMethod("CreateDecryptor", Type.EmptyTypes));
            var transformFinal = module.Import(typeof(System.Security.Cryptography.ICryptoTransform)
                .GetMethod("TransformFinalBlock", new[] { typeof(byte[]), typeof(int), typeof(int) }));
            var memStreamCtorBytes = module.Import(typeof(System.IO.MemoryStream)
                .GetConstructor(new[] { typeof(byte[]) }));
            var memStreamCtorDefault = module.Import(typeof(System.IO.MemoryStream)
                .GetConstructor(Type.EmptyTypes));
            var memStreamToArray = module.Import(typeof(System.IO.MemoryStream).GetMethod("ToArray"));
            var deflateCtor = module.Import(typeof(System.IO.Compression.DeflateStream)
                .GetConstructor(new[] { typeof(System.IO.Stream), typeof(System.IO.Compression.CompressionMode) }));
            var sha256Create = module.Import(typeof(System.Security.Cryptography.SHA256)
                .GetMethod("Create", Type.EmptyTypes));
            var hashAlgComputeHash = module.Import(typeof(System.Security.Cryptography.HashAlgorithm)
                .GetMethod("ComputeHash", new[] { typeof(byte[]) }));
            var encodingUtf8Get = module.Import(typeof(System.Text.Encoding).GetProperty("UTF8").GetGetMethod());
            var encodingGetBytes = module.Import(typeof(System.Text.Encoding)
                .GetMethod("GetBytes", new[] { typeof(string) }));
            var arrayCopyRef = module.Import(typeof(Array)
                .GetMethod("Copy", new[] { typeof(Array), typeof(int), typeof(Array), typeof(int), typeof(int) }));
            var getTypeFromHandle = module.Import(typeof(Type)
                .GetMethod("GetTypeFromHandle", new Type[] { typeof(RuntimeTypeHandle) }));
            var getModule2 = module.Import(typeof(Type).GetProperty("Module").GetGetMethod());
            var getMvid2   = module.Import(typeof(System.Reflection.Module)
                .GetProperty("ModuleVersionId").GetGetMethod());
            var toByteArr2 = module.Import(typeof(Guid).GetMethod("ToByteArray", Type.EmptyTypes));

            var helper = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(streamType.ToTypeSig(),
                    assemblyType.ToTypeSig(), module.CorLibTypes.String),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            helper.Body = new CilBody();
            helper.Body.InitLocals = true;
            var v = helper.Body.Variables;

            Local lRaw       = v.Add(new Local(streamType.ToTypeSig()));
            Local lNames     = v.Add(new Local(new SZArraySig(module.CorLibTypes.String)));
            Local lI         = v.Add(new Local(module.CorLibTypes.Int32));
            Local lLen       = v.Add(new Local(module.CorLibTypes.Int32));
            Local lBuf       = v.Add(new Local(byteArrSig));
            Local lAes       = v.Add(new Local(aesType.ToTypeSig()));
            Local lDec       = v.Add(new Local(cryptoXformType.ToTypeSig()));
            Local lPlain     = v.Add(new Local(byteArrSig));
            Local lMs        = v.Add(new Local(memStreamType.ToTypeSig()));
            Local lDs        = v.Add(new Local(deflateType.ToTypeSig()));
            Local lOut       = v.Add(new Local(memStreamType.ToTypeSig()));
            Local lMaster    = v.Add(new Local(byteArrSig));
            Local lSalt      = v.Add(new Local(byteArrSig));
            Local lPerKey    = v.Add(new Local(byteArrSig));
            Local lPerIv     = v.Add(new Local(byteArrSig));
            Local lShaTemp   = v.Add(new Local(sha256Type.ToTypeSig()));
            Local lNameBytes = v.Add(new Local(byteArrSig));
            Local lMat       = v.Add(new Local(byteArrSig));
            Local lJ         = v.Add(new Local(module.CorLibTypes.Int32));
            Local lMvidB     = v.Add(new Local(byteArrSig));
            Local lGuid      = v.Add(new Local(importer.ImportAsTypeSig(typeof(Guid))));
            Local lR1        = v.Add(new Local(byteArrSig));
            Local lR2        = v.Add(new Local(byteArrSig));
            Local lKsSeed    = v.Add(new Local(byteArrSig));
            Local lKsBlock   = v.Add(new Local(byteArrSig));
            Local lKsPos     = v.Add(new Local(module.CorLibTypes.Int32));
            Local lKsCtr     = v.Add(new Local(module.CorLibTypes.Int32));
            Local lKsTake    = v.Add(new Local(module.CorLibTypes.Int32));

            var il = helper.Body.Instructions;

            var retNullInst = Instruction.Create(DnOpCodes.Ldnull);
            var loopHead    = Instruction.Create(DnOpCodes.Ldloc, lI);
            var loopAfter   = Instruction.Create(DnOpCodes.Nop);
            var returnRaw   = Instruction.Create(DnOpCodes.Ldloc, lRaw);

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, getManifestRef));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lRaw));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lRaw));
            var afterNullCheck = Instruction.Create(DnOpCodes.Ldsfld, namesField);
            il.Add(Instruction.Create(DnOpCodes.Brtrue, afterNullCheck));
            il.Add(retNullInst);
            il.Add(Instruction.Create(DnOpCodes.Ret));

            il.Add(afterNullCheck);
            il.Add(Instruction.Create(DnOpCodes.Stloc, lNames));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lNames));
            var afterNamesNull = Instruction.Create(DnOpCodes.Ldc_I4_0);
            il.Add(Instruction.Create(DnOpCodes.Brtrue, afterNamesNull));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lRaw));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            il.Add(afterNamesNull);
            il.Add(Instruction.Create(DnOpCodes.Stloc, lI));

            il.Add(loopHead);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lNames));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Bge, returnRaw));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lNames));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lI));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Call, stringOpEq));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, loopAfter));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lI));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lI));
            il.Add(Instruction.Create(DnOpCodes.Br, loopHead));

            il.Add(returnRaw);
            il.Add(Instruction.Create(DnOpCodes.Ret));

            il.Add(loopAfter);

            il.Add(Instruction.Create(DnOpCodes.Ldsfld, keyField));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lMaster));
            il.Add(Instruction.Create(DnOpCodes.Ldsfld, saltField));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lSalt));

            il.Add(Instruction.Create(DnOpCodes.Call, encodingUtf8Get));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, encodingGetBytes));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lNameBytes));

            il.Add(engine.LoadInt(32));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lSalt));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lNameBytes));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.Byte.TypeDefOrRef));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lMat));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMaster));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMat));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(engine.LoadInt(32));
            il.Add(Instruction.Create(DnOpCodes.Call, arrayCopyRef));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lSalt));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMat));
            il.Add(engine.LoadInt(32));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lSalt));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Call, arrayCopyRef));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lNameBytes));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMat));
            il.Add(engine.LoadInt(32));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lSalt));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lNameBytes));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Call, arrayCopyRef));

            EmitSha256Hash(il, module, sha256Create, hashAlgComputeHash, lShaTemp, lMat, lR1);

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lR1));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lNameBytes));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(engine.LoadInt(32));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.Byte.TypeDefOrRef));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lMat));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lR1));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMat));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lR1));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Call, arrayCopyRef));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lNameBytes));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMat));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lR1));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lNameBytes));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Call, arrayCopyRef));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMaster));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMat));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lR1));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lNameBytes));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(engine.LoadInt(32));
            il.Add(Instruction.Create(DnOpCodes.Call, arrayCopyRef));

            EmitSha256Hash(il, module, sha256Create, hashAlgComputeHash, lShaTemp, lMat, lR2);

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lSalt));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lR2));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lR1));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.Byte.TypeDefOrRef));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lMat));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lSalt));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMat));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lSalt));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Call, arrayCopyRef));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lR2));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMat));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lSalt));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lR2));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Call, arrayCopyRef));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lR1));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMat));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lSalt));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lR2));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lR1));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Call, arrayCopyRef));

            EmitSha256Hash(il, module, sha256Create, hashAlgComputeHash, lShaTemp, lMat, lPerKey);

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lRaw));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, streamGetLength));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lLen));

            var retNullLenCheck = Instruction.Create(DnOpCodes.Ldnull);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lLen));
            il.Add(engine.LoadInt(16));
            il.Add(Instruction.Create(DnOpCodes.Ble, retNullLenCheck));

            il.Add(engine.LoadInt(16));
            il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.Byte.TypeDefOrRef));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lPerIv));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lRaw));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lPerIv));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(engine.LoadInt(16));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, streamRead));
            il.Add(Instruction.Create(DnOpCodes.Pop));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lLen));
            il.Add(engine.LoadInt(16));
            il.Add(Instruction.Create(DnOpCodes.Sub));
            il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.Byte.TypeDefOrRef));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lBuf));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lRaw));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lBuf));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lBuf));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, streamRead));
            il.Add(Instruction.Create(DnOpCodes.Pop));

            il.Add(Instruction.Create(DnOpCodes.Call, aesCreate));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lAes));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lAes));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, setMode));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lAes));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_2));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, setPadding));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lAes));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lPerKey));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, setKey));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lAes));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lPerIv));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, setIV));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lAes));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, createDecryptor));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lDec));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lDec));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lBuf));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lBuf));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, transformFinal));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lPlain));

            EmitLoadMvidBytes(il, module, modType, lGuid, lMvidB,
                getTypeFromHandle, getModule2, getMvid2, toByteArr2);

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMvidB));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lSalt));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lNameBytes));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.Byte.TypeDefOrRef));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lMat));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMvidB));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMat));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMvidB));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Call, arrayCopyRef));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lSalt));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMat));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMvidB));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lSalt));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Call, arrayCopyRef));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lNameBytes));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMat));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMvidB));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lSalt));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lNameBytes));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Call, arrayCopyRef));

            EmitSha256Hash(il, module, sha256Create, hashAlgComputeHash, lShaTemp, lMat, lKsSeed);

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lKsPos));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lKsCtr));

            var ksLoopCond = Instruction.Create(DnOpCodes.Ldloc, lKsPos);
            var ksLoopEnd  = Instruction.Create(DnOpCodes.Nop);
            il.Add(Instruction.Create(DnOpCodes.Br, ksLoopCond));

            var ksLoopBody = Instruction.Create(DnOpCodes.Nop);
            il.Add(ksLoopBody);

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lKsSeed));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_4));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.Byte.TypeDefOrRef));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lMat));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lKsSeed));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMat));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lKsSeed));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Call, arrayCopyRef));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMat));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lKsSeed));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lKsCtr));
            il.Add(Instruction.Create(DnOpCodes.Conv_U1));
            il.Add(Instruction.Create(DnOpCodes.Stelem_I1));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMat));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lKsSeed));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lKsCtr));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_8));
            il.Add(Instruction.Create(DnOpCodes.Shr_Un));
            il.Add(Instruction.Create(DnOpCodes.Conv_U1));
            il.Add(Instruction.Create(DnOpCodes.Stelem_I1));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMat));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lKsSeed));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_2));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lKsCtr));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 16));
            il.Add(Instruction.Create(DnOpCodes.Shr_Un));
            il.Add(Instruction.Create(DnOpCodes.Conv_U1));
            il.Add(Instruction.Create(DnOpCodes.Stelem_I1));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMat));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lKsSeed));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_3));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lKsCtr));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 24));
            il.Add(Instruction.Create(DnOpCodes.Shr_Un));
            il.Add(Instruction.Create(DnOpCodes.Conv_U1));
            il.Add(Instruction.Create(DnOpCodes.Stelem_I1));

            EmitSha256Hash(il, module, sha256Create, hashAlgComputeHash, lShaTemp, lMat, lKsBlock);

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lPlain));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lKsPos));
            il.Add(Instruction.Create(DnOpCodes.Sub));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lKsTake));

            var skipClamp = Instruction.Create(DnOpCodes.Nop);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lKsTake));
            il.Add(engine.LoadInt(32));
            il.Add(Instruction.Create(DnOpCodes.Ble, skipClamp));
            il.Add(engine.LoadInt(32));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lKsTake));
            il.Add(skipClamp);

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lJ));

            var innerCond = Instruction.Create(DnOpCodes.Ldloc, lJ);
            var innerBody = Instruction.Create(DnOpCodes.Ldloc, lPlain);
            il.Add(Instruction.Create(DnOpCodes.Br, innerCond));
            il.Add(innerBody);

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lKsPos));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lJ));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lPlain));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lKsPos));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lJ));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lKsBlock));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lJ));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Conv_U1));
            il.Add(Instruction.Create(DnOpCodes.Stelem_I1));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lJ));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lJ));

            il.Add(innerCond);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lKsTake));
            il.Add(Instruction.Create(DnOpCodes.Blt, innerBody));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lKsPos));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lKsTake));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lKsPos));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lKsCtr));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lKsCtr));

            il.Add(ksLoopCond);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lPlain));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Blt, ksLoopBody));
            il.Add(ksLoopEnd);

            il.Add(Instruction.Create(DnOpCodes.Ldloc, lPlain));
            il.Add(Instruction.Create(DnOpCodes.Newobj, memStreamCtorBytes));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lMs));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lMs));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Newobj, deflateCtor));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lDs));
            il.Add(Instruction.Create(DnOpCodes.Newobj, memStreamCtorDefault));
            il.Add(Instruction.Create(DnOpCodes.Stloc, lOut));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lDs));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lOut));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, streamCopyTo));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, lOut));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, memStreamToArray));
            il.Add(Instruction.Create(DnOpCodes.Newobj, memStreamCtorBytes));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            il.Add(retNullLenCheck);
            il.Add(Instruction.Create(DnOpCodes.Ret));

            modType.Methods.Add(helper);
            engine.injectedMethods.Add(helper);
            return helper;
        }

        private void RewriteResourceCallsites(ModuleDef module, MethodDef helperMethod)
        {
            foreach (TypeDef type in module.GetTypes())
            {
                if (engine.IsTypeUserExcluded(type)) continue;
                foreach (MethodDef method in type.Methods)
                {
                    if (!method.HasBody || !method.Body.HasInstructions) continue;
                    if (engine.injectedMethods.Contains(method)) continue;
                    if (engine.IsMethodUserExcluded(method)) continue;
                    var ins = method.Body.Instructions;
                    for (int i = 0; i < ins.Count; i++)
                    {
                        var instr = ins[i];
                        if (instr.OpCode != DnOpCodes.Callvirt && instr.OpCode != DnOpCodes.Call)
                            continue;
                        var target = instr.Operand as IMethod;
                        if (target == null) continue;
                        if (target.Name != "GetManifestResourceStream") continue;
                        var decl = target.DeclaringType;
                        if (decl == null || decl.FullName != "System.Reflection.Assembly") continue;
                        var sig = target.MethodSig;
                        if (sig == null || sig.Params.Count != 1) continue;
                        if (sig.Params[0].FullName != "System.String") continue;
                        instr.OpCode = DnOpCodes.Call;
                        instr.Operand = helperMethod;
                    }
                }
            }
        }
    }
}

