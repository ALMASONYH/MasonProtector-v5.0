using System;
using System.Collections.Generic;
using dnlib.DotNet;
using dnlib.DotNet.Emit;

using DnMethodAttributes = dnlib.DotNet.MethodAttributes;
using DnMethodImplAttributes = dnlib.DotNet.MethodImplAttributes;
using DnOpCodes = dnlib.DotNet.Emit.OpCodes;

namespace MasonProtector.Core
{
    internal class GateHardenerProtection
    {
        private readonly Obfuscation engine;
        private readonly Random rng;

        internal GateHardenerProtection(Obfuscation eng)
        {
            engine = eng;
            rng = eng.rng;
        }

        internal void EncryptStrings(ModuleDef module, List<TypeDef> gateTypes, MethodDef wrapper)
        {
            if (gateTypes == null || gateTypes.Count == 0) return;

            MethodDef decStr = BuildDecStr(module);
            gateTypes[0].Methods.Add(decStr);
            engine.injectedMethods.Add(decStr);

            if (wrapper != null) EncryptStringsIn(wrapper, decStr);
            foreach (TypeDef t in gateTypes)
                foreach (MethodDef m in AllMethods(t))
                    if (m != decStr) EncryptStringsIn(m, decStr);
        }

        private static IEnumerable<MethodDef> AllMethods(TypeDef t)
        {
            foreach (MethodDef m in t.Methods) yield return m;
            foreach (TypeDef n in t.NestedTypes)
                foreach (MethodDef m in AllMethods(n)) yield return m;
        }

        private void EncryptStringsIn(MethodDef m, MethodDef decStr)
        {
            if (m == null || !m.HasBody || m.Body == null || m.Body.Instructions == null) return;
            if (m.IsPinvokeImpl) return;

            var il = m.Body.Instructions;
            for (int i = 0; i < il.Count; i++)
            {
                if (il[i].OpCode != DnOpCodes.Ldstr) continue;
                string s = il[i].Operand as string;
                if (string.IsNullOrEmpty(s)) continue;

                int key = 1 + rng.Next(60000);
                il[i].Operand = Xor(s, key);
                il.Insert(i + 1, Instruction.Create(DnOpCodes.Ldc_I4, key));
                il.Insert(i + 2, Instruction.Create(DnOpCodes.Call, decStr));
                i += 2;
            }

            try { m.Body.SimplifyBranches(); m.Body.OptimizeBranches(); } catch { }
        }

        private static string Xor(string s, int key)
        {
            char[] c = s.ToCharArray();
            for (int i = 0; i < c.Length; i++)
                c[i] = (char)(c[i] ^ (key & 0xFFFF));
            return new string(c);
        }

        private MethodDef BuildDecStr(ModuleDef module)
        {
            var m = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.String,
                    module.CorLibTypes.String, module.CorLibTypes.Int32),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            var toCharArray = module.Import(typeof(string).GetMethod("ToCharArray", Type.EmptyTypes));
            var strCtor = module.Import(typeof(string).GetConstructor(new[] { typeof(char[]) }));

            m.Body = new CilBody();
            m.Body.InitLocals = true;
            m.Body.Variables.Add(new Local(new SZArraySig(module.CorLibTypes.Char)));
            m.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            var il = m.Body.Instructions;

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, toCharArray));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));

            var check = Instruction.Create(DnOpCodes.Ldloc_1);
            il.Add(Instruction.Create(DnOpCodes.Br, check));

            var loop = Instruction.Create(DnOpCodes.Ldloc_0);
            il.Add(loop);
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U2));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 0xFFFF));
            il.Add(Instruction.Create(DnOpCodes.And));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Conv_U2));
            il.Add(Instruction.Create(DnOpCodes.Stelem_I2));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));

            il.Add(check);
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Blt, loop));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Newobj, strCtor));
            il.Add(Instruction.Create(DnOpCodes.Ret));
            return m;
        }
    }
}
