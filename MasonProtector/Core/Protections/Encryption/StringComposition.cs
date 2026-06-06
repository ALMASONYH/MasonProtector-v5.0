using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using dnlib.DotNet;
using dnlib.DotNet.Emit;

using DnFieldAttributes = dnlib.DotNet.FieldAttributes;
using DnMethodAttributes = dnlib.DotNet.MethodAttributes;
using DnMethodImplAttributes = dnlib.DotNet.MethodImplAttributes;
using DnTypeAttributes = dnlib.DotNet.TypeAttributes;
using DnOpCodes = dnlib.DotNet.Emit.OpCodes;
using System.Runtime.CompilerServices;

namespace MasonProtector.Core
{
    internal class StringCompositionProtection
    {
        private Obfuscation engine;
        private Random rng;

        private const int DECRYPTOR_COUNT = 6;
        private const int FAKE_DECRYPTOR_COUNT = 14;
        private const int NOISE_TYPE_COUNT = 3;

        private TypeDef payloadHost;
        private FieldDef payloadField;
        private FieldDef cacheField;
        private FieldDef masterXorField;
        private int masterXorValue;

        private List<char> payloadChars;
        private int payloadPtr;

        private List<MethodDef> decryptors;

        private IMethod dictContainsKey;
        private IMethod dictGetItem;
        private IMethod dictSetItem;
        private IMethod dictCtor;
        private IMethod strIntern;
        private IMethod stringCtorCharArr;

        internal StringCompositionProtection(Obfuscation eng)
        {
            engine = eng;
            rng = eng.rng;
        }

        internal void ApplyStringComposition(ModuleDef module, TypeDef modType)
        {
            payloadChars = new List<char>();
            payloadPtr = 0;
            decryptors = new List<MethodDef>();

            ResolveFrameworkMethods(module);
            BuildInfrastructure(module);

            int total = 0;
            foreach (TypeDef type in module.GetTypes())
            {
                if (engine.IsCompilerGenerated(type)) continue;
                foreach (MethodDef method in type.Methods)
                {
                    if (!engine.CanProcessMethod(method)) continue;
                    try
                    {
                        total += TransformStrings(module, method);
                        method.Body.SimplifyBranches();
                        method.Body.OptimizeBranches();
                    }
                    catch { }
                }
            }

            if (total > 0)
            {
                BuildPayloadCctor(module);
            }
        }

        private void ResolveFrameworkMethods(ModuleDef module)
        {
            module.Import(typeof(Dictionary<int, string>));

            dictContainsKey = module.Import(typeof(Dictionary<int, string>).GetMethod("ContainsKey"));
            dictGetItem = module.Import(typeof(Dictionary<int, string>).GetProperty("Item").GetGetMethod());
            dictSetItem = module.Import(typeof(Dictionary<int, string>).GetProperty("Item").GetSetMethod());
            dictCtor = module.Import(typeof(Dictionary<int, string>).GetConstructor(Type.EmptyTypes));
            strIntern = module.Import(typeof(string).GetMethod("Intern", new[] { typeof(string) }));
            stringCtorCharArr = module.Import(typeof(string).GetConstructor(new[] { typeof(char[]) }));
        }

        private void BuildInfrastructure(ModuleDef module)
        {
            payloadHost = new TypeDefUser("", engine.MakeName(),
                module.CorLibTypes.Object.TypeDefOrRef);
            payloadHost.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
            module.Types.Add(payloadHost);
            engine.injectedTypes.Add(payloadHost);

            payloadField = new FieldDefUser(engine.MakeName(),
                new FieldSig(new SZArraySig(module.CorLibTypes.Char)),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            payloadHost.Fields.Add(payloadField);

            var dictTypeSig = new GenericInstSig(
                new ClassSig(module.Import(typeof(Dictionary<int, string>)).ScopeType),
                module.CorLibTypes.Int32,
                module.CorLibTypes.String);
            cacheField = new FieldDefUser(engine.MakeName(),
                new FieldSig(dictTypeSig),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            payloadHost.Fields.Add(cacheField);

            masterXorValue = rng.Next(1, 0x7FFFFFFF);
            masterXorField = new FieldDefUser(engine.MakeName(),
                new FieldSig(module.CorLibTypes.Int32),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            payloadHost.Fields.Add(masterXorField);

            for (int d = 0; d < DECRYPTOR_COUNT; d++)
            {
                var dec = BuildDecryptor(module, d);
                payloadHost.Methods.Add(dec);
                engine.injectedMethods.Add(dec);
                decryptors.Add(dec);
            }

            for (int f = 0; f < FAKE_DECRYPTOR_COUNT; f++)
            {
                var fake = BuildFakeDecryptor(module);
                payloadHost.Methods.Add(fake);
                engine.injectedMethods.Add(fake);
            }

            for (int n = 0; n < NOISE_TYPE_COUNT; n++)
            {
                var nt = new TypeDefUser("", engine.MakeName(),
                    module.CorLibTypes.Object.TypeDefOrRef);
                nt.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                    DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
                module.Types.Add(nt);
                engine.injectedTypes.Add(nt);
                for (int fi = 0; fi < rng.Next(3, 7); fi++)
                {
                    nt.Fields.Add(new FieldDefUser(engine.MakeName(),
                        new FieldSig(module.CorLibTypes.Int32),
                        DnFieldAttributes.Private | DnFieldAttributes.Static));
                }
            }
        }

        private int TransformStrings(ModuleDef module, MethodDef method)
        {
            var il = method.Body.Instructions;
            int count = 0;

            for (int i = 0; i < il.Count; i++)
            {
                if (il[i].OpCode != DnOpCodes.Ldstr) continue;
                string str = il[i].Operand as string;
                if (str == null || str.Length == 0 || str.Length > 512) continue;

                int offset = payloadPtr;
                int perStringKey = rng.Next(0, 0x10000);
                int posMult = (rng.Next(1, 0x7FFF) * 2) + 1;

                for (int c = 0; c < str.Length; c++)
                {
                    int charVal = (int)str[c];
                    int posSalt = (c * posMult) & 0xFFFF;
                    int encoded = (charVal ^ perStringKey ^ posSalt) & 0xFFFF;
                    payloadChars.Add((char)encoded);
                    payloadPtr++;
                }

                int encodedKey = perStringKey ^ masterXorValue;

                int decIdx = rng.Next(0, DECRYPTOR_COUNT);
                var callInsts = new List<Instruction>
                {
                    Instruction.Create(DnOpCodes.Ldc_I4, offset),
                    Instruction.Create(DnOpCodes.Ldc_I4, str.Length),
                    Instruction.Create(DnOpCodes.Ldc_I4, encodedKey),
                    Instruction.Create(DnOpCodes.Ldc_I4, posMult),
                    Instruction.Create(DnOpCodes.Call, decryptors[decIdx])
                };

                il[i].OpCode = callInsts[0].OpCode;
                il[i].Operand = callInsts[0].Operand;
                for (int j = 1; j < callInsts.Count; j++)
                    il.Insert(i + j, callInsts[j]);
                i += callInsts.Count - 1;
                count++;
            }

            return count;
        }

        private MethodDef BuildDecryptor(ModuleDef module, int variant)
        {
            var method = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.String,
                    module.CorLibTypes.Int32,
                    module.CorLibTypes.Int32,
                    module.CorLibTypes.Int32,
                    module.CorLibTypes.Int32),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            method.Body = new CilBody();
            method.Body.InitLocals = true;

            var varChars = new Local(new SZArraySig(module.CorLibTypes.Char));
            var varIdx = new Local(module.CorLibTypes.Int32);
            var varCh = new Local(module.CorLibTypes.Int32);
            var varCached = new Local(module.CorLibTypes.String);
            var varRealKey = new Local(module.CorLibTypes.Int32);
            var varPosSalt = new Local(module.CorLibTypes.Int32);

            method.Body.Variables.Add(varChars);
            method.Body.Variables.Add(varIdx);
            method.Body.Variables.Add(varCh);
            method.Body.Variables.Add(varCached);
            method.Body.Variables.Add(varRealKey);
            method.Body.Variables.Add(varPosSalt);

            var il = method.Body.Instructions;

            var lookupStart = Instruction.Create(DnOpCodes.Ldsfld, cacheField);

            il.Add(Instruction.Create(DnOpCodes.Ldsfld, cacheField));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, lookupStart));
            il.Add(Instruction.Create(DnOpCodes.Newobj, dictCtor));
            il.Add(Instruction.Create(DnOpCodes.Stsfld, cacheField));

            il.Add(lookupStart);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, dictContainsKey));
            var doDecrypt = Instruction.Create(DnOpCodes.Nop);
            il.Add(Instruction.Create(DnOpCodes.Brfalse, doDecrypt));

            il.Add(Instruction.Create(DnOpCodes.Ldsfld, cacheField));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, dictGetItem));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            il.Add(doDecrypt);

            il.Add(Instruction.Create(DnOpCodes.Ldarg_2));
            il.Add(Instruction.Create(DnOpCodes.Ldsfld, masterXorField));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 0xFFFF));
            il.Add(Instruction.Create(DnOpCodes.And));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varRealKey));

            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.Char.TypeDefOrRef));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varChars));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varIdx));

            var loopCheck = Instruction.Create(DnOpCodes.Ldloc, varIdx);
            var loopBody = Instruction.Create(DnOpCodes.Ldsfld, payloadField);
            il.Add(Instruction.Create(DnOpCodes.Br, loopCheck));

            il.Add(loopBody);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varIdx));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U2));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varCh));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varIdx));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_3));
            il.Add(Instruction.Create(DnOpCodes.Mul));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 0xFFFF));
            il.Add(Instruction.Create(DnOpCodes.And));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varPosSalt));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varChars));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varIdx));

            switch (variant % DECRYPTOR_COUNT)
            {
                case 0:
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, varCh));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, varRealKey));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, varPosSalt));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    break;
                case 1:
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, varPosSalt));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, varRealKey));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, varCh));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    break;
                case 2:
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, varCh));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, varPosSalt));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, varRealKey));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    break;
                case 3:
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, varRealKey));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, varCh));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, varPosSalt));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    break;
                case 4:
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, varRealKey));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, varPosSalt));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, varCh));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    break;
                default:
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, varPosSalt));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, varCh));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, varRealKey));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    break;
            }

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 0xFFFF));
            il.Add(Instruction.Create(DnOpCodes.And));
            il.Add(Instruction.Create(DnOpCodes.Conv_U2));
            il.Add(Instruction.Create(DnOpCodes.Stelem_I2));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varIdx));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varIdx));

            il.Add(loopCheck);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Blt, loopBody));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varChars));
            il.Add(Instruction.Create(DnOpCodes.Newobj, stringCtorCharArr));
            il.Add(Instruction.Create(DnOpCodes.Call, strIntern));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varCached));

            il.Add(Instruction.Create(DnOpCodes.Ldsfld, cacheField));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varCached));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, dictSetItem));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varCached));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            return method;
        }

        private MethodDef BuildFakeDecryptor(ModuleDef module)
        {
            int sig = rng.Next(0, 3);
            MethodSig msig;
            if (sig == 0)
                msig = MethodSig.CreateStatic(module.CorLibTypes.String,
                    module.CorLibTypes.Int32, module.CorLibTypes.Int32, module.CorLibTypes.Int32);
            else if (sig == 1)
                msig = MethodSig.CreateStatic(module.CorLibTypes.String,
                    module.CorLibTypes.Int32, module.CorLibTypes.Int32);
            else
                msig = MethodSig.CreateStatic(module.CorLibTypes.String,
                    module.CorLibTypes.Int32, module.CorLibTypes.Int32,
                    module.CorLibTypes.Int32, module.CorLibTypes.Int32,
                    module.CorLibTypes.Int32);

            var method = new MethodDefUser(engine.MakeName(), msig,
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            method.Body = new CilBody();
            method.Body.InitLocals = true;
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            var il = method.Body.Instructions;

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            for (int n = 0; n < rng.Next(2, 5); n++)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                int op = rng.Next(0, 3);
                if (op == 0) il.Add(Instruction.Create(DnOpCodes.Xor));
                else if (op == 1) il.Add(Instruction.Create(DnOpCodes.Add));
                else il.Add(Instruction.Create(DnOpCodes.Sub));
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            }
            il.Add(Instruction.Create(DnOpCodes.Ldnull));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            return method;
        }

        private void BuildPayloadCctor(ModuleDef module)
        {
            var importer = new Importer(module);
            ITypeDefOrRef sysValueType = importer.Import(typeof(ValueType));
            IMethod rhInitArr = importer.Import(typeof(RuntimeHelpers)
                .GetMethod("InitializeArray",
                    new Type[] { typeof(Array), typeof(RuntimeFieldHandle) }));

            var cctor = new MethodDefUser(".cctor",
                MethodSig.CreateStatic(module.CorLibTypes.Void),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Private | DnMethodAttributes.Static | DnMethodAttributes.HideBySig |
                DnMethodAttributes.SpecialName | DnMethodAttributes.RTSpecialName);

            cctor.Body = new CilBody();
            cctor.Body.InitLocals = true;
            var il = cctor.Body.Instructions;

            int msk = rng.Next(int.MinValue, int.MaxValue);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, masterXorValue ^ msk));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, msk));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stsfld, masterXorField));

            int count = payloadChars.Count;
            int seed = rng.Next(1, int.MaxValue);
            char[] chars = payloadChars.ToArray();
            ushort[] maskedWords = MaskCharArray(chars, seed);
            byte[] maskedBytes = UInt16ArrayToLittleEndianBytes(maskedWords);
            FieldDef rvaField = MakeRvaField(module, payloadHost, sysValueType, maskedBytes);

            var varArr = new Local(new SZArraySig(module.CorLibTypes.Char));
            var varIdx = new Local(module.CorLibTypes.Int32);
            var varState = new Local(module.CorLibTypes.Int32);
            cctor.Body.Variables.Add(varArr);
            cctor.Body.Variables.Add(varIdx);
            cctor.Body.Variables.Add(varState);

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, count));
            il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.Char.TypeDefOrRef));
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
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U2));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varState));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 0xFFFF));
            il.Add(Instruction.Create(DnOpCodes.And));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Conv_U2));
            il.Add(Instruction.Create(DnOpCodes.Stelem_I2));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varIdx));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varIdx));

            il.Add(loopCond);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, count));
            il.Add(Instruction.Create(DnOpCodes.Blt, loopBody));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varArr));
            il.Add(Instruction.Create(DnOpCodes.Stsfld, payloadField));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            payloadHost.Methods.Add(cctor);
            engine.injectedMethods.Add(cctor);
        }

        private static ushort[] MaskCharArray(char[] chars, int seed)
        {
            ushort[] masked = new ushort[chars.Length];
            int state = seed;
            for (int i = 0; i < chars.Length; i++)
            {
                state = unchecked(state * 1664525 + 1013904223);
                masked[i] = (ushort)((ushort)chars[i] ^ (state & 0xFFFF));
            }
            return masked;
        }

        private static byte[] UInt16ArrayToLittleEndianBytes(ushort[] values)
        {
            byte[] bytes = new byte[values.Length * 2];
            for (int i = 0; i < values.Length; i++)
            {
                ushort v = values[i];
                bytes[i * 2 + 0] = (byte)(v & 0xFF);
                bytes[i * 2 + 1] = (byte)((v >> 8) & 0xFF);
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
