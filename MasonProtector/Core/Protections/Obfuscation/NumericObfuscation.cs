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
using System.Runtime.CompilerServices;

namespace MasonProtector.Core
{
    internal class NumericObfuscationProtection
    {
        private Obfuscation engine;
        private Random rng;

        private const int KEY_FIELD_COUNT = 32;
        private const int CIPHER_TABLE_SIZE = 384;
        private const int CIPHER_TABLE_COUNT = 14;
        private const int DECODER_METHOD_COUNT = 24;
        private const int FAKE_METHOD_COUNT = 24;

        private TypeDef engineType;
        private TypeDef storageType;
        private TypeDef resolverType;

        private List<FieldDef> keyFields;
        private int[] keyValues;

        private List<FieldDef> tableFields;
        private int[][] cipherTables;

        private List<MethodDef> decoderMethods;

        private int masterSeed;

        private IMethod _getTickCount;

        internal NumericObfuscationProtection(Obfuscation eng)
        {
            engine = eng;
            rng = eng.rng;
        }

        internal void ApplyNumericObfuscation(ModuleDef module, TypeDef modType)
        {
            engine.activeOption = "NumericObfuscation";
            keyFields = new List<FieldDef>();
            keyValues = new int[KEY_FIELD_COUNT];
            tableFields = new List<FieldDef>();
            cipherTables = new int[CIPHER_TABLE_COUNT][];
            decoderMethods = new List<MethodDef>();
            masterSeed = rng.Next(100000, int.MaxValue / 2);

            try
            {
                _getTickCount = module.Import(
                    typeof(System.Environment).GetProperty("TickCount").GetGetMethod());
            }
            catch
            {
                _getTickCount = null;
            }

            CreateEngineType(module);
            CreateStorageType(module);
            CreateResolverType(module);

            CreateKeyFields(module);
            CreateCipherTables(module);
            CreateDecoderMethods(module);
            CreateFakeMethods(module);

            EncryptIntegers(module);

            BuildHostCctor(module, engineType, 0);
            BuildHostCctor(module, storageType, 1);
            BuildHostCctor(module, resolverType, 2);
        }

        private void CreateEngineType(ModuleDef module)
        {
            engineType = new TypeDefUser("", engine.MakeName(),
                module.CorLibTypes.Object.TypeDefOrRef);
            engineType.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
            module.Types.Add(engineType);
            engine.injectedTypes.Add(engineType);
        }

        private void CreateStorageType(ModuleDef module)
        {
            storageType = new TypeDefUser("", engine.MakeName(),
                module.CorLibTypes.Object.TypeDefOrRef);
            storageType.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
            module.Types.Add(storageType);
            engine.injectedTypes.Add(storageType);
        }

        private void CreateResolverType(ModuleDef module)
        {
            resolverType = new TypeDefUser("", engine.MakeName(),
                module.CorLibTypes.Object.TypeDefOrRef);
            resolverType.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
            module.Types.Add(resolverType);
            engine.injectedTypes.Add(resolverType);
        }

        private void CreateKeyFields(ModuleDef module)
        {
            for (int i = 0; i < KEY_FIELD_COUNT; i++)
            {
                keyValues[i] = rng.Next(10000, int.MaxValue / 2);
                TypeDef host;
                int hostPick = i % 3;
                if (hostPick == 0) host = engineType;
                else if (hostPick == 1) host = storageType;
                else host = resolverType;

                var field = new FieldDefUser(engine.MakeName(),
                    new FieldSig(module.CorLibTypes.Int32),
                    DnFieldAttributes.Assembly | DnFieldAttributes.Static);
                host.Fields.Add(field);
                keyFields.Add(field);
            }

            for (int d = 0; d < engine.LevelRange(2, 4, 3, 5, 4, 7); d++)
            {
                TypeDef host;
                int pick = rng.Next(0, 3);
                if (pick == 0) host = engineType;
                else if (pick == 1) host = storageType;
                else host = resolverType;

                host.Fields.Add(new FieldDefUser(engine.MakeName(),
                    new FieldSig(module.CorLibTypes.Int32),
                    DnFieldAttributes.Private | DnFieldAttributes.Static));
            }
        }

        private void CreateCipherTables(ModuleDef module)
        {
            for (int t = 0; t < CIPHER_TABLE_COUNT; t++)
            {
                cipherTables[t] = new int[CIPHER_TABLE_SIZE];
                for (int s = 0; s < CIPHER_TABLE_SIZE; s++)
                {
                    cipherTables[t][s] = rng.Next(int.MinValue, int.MaxValue);
                }

                TypeDef host;
                int pick = t % 3;
                if (pick == 0) host = engineType;
                else if (pick == 1) host = storageType;
                else host = resolverType;

                var field = new FieldDefUser(engine.MakeName(),
                    new FieldSig(new SZArraySig(module.CorLibTypes.Int32)),
                    DnFieldAttributes.Assembly | DnFieldAttributes.Static);
                host.Fields.Add(field);
                tableFields.Add(field);
            }
        }

        private void CreateDecoderMethods(ModuleDef module)
        {
            for (int d = 0; d < DECODER_METHOD_COUNT; d++)
            {
                var method = BuildDecoderMethod(module, d);
                TypeDef host;
                int pick = d % 3;
                if (pick == 0) host = engineType;
                else if (pick == 1) host = storageType;
                else host = resolverType;

                host.Methods.Add(method);
                engine.injectedMethods.Add(method);
                decoderMethods.Add(method);
            }
        }

        private void CreateFakeMethods(ModuleDef module)
        {
            for (int f = 0; f < FAKE_METHOD_COUNT; f++)
            {
                var method = BuildFakeMethod(module, f);
                TypeDef host;
                int pick = rng.Next(0, 3);
                if (pick == 0) host = engineType;
                else if (pick == 1) host = storageType;
                else host = resolverType;

                host.Methods.Add(method);
                engine.injectedMethods.Add(method);
            }
        }

        private MethodDef BuildDecoderMethod(ModuleDef module, int variant)
        {
            var method = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Int32, module.CorLibTypes.Int32, module.CorLibTypes.Int32),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            method.Body = new CilBody();
            method.Body.InitLocals = true;
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            var il = method.Body.Instructions;

            switch (variant % DECODER_METHOD_COUNT)
            {
                case 0:
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Ret));
                    break;
                case 1:
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
                    il.Add(Instruction.Create(DnOpCodes.Add));
                    il.Add(Instruction.Create(DnOpCodes.Ret));
                    break;
                case 2:
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Not));
                    il.Add(Instruction.Create(DnOpCodes.Not));
                    il.Add(Instruction.Create(DnOpCodes.Ret));
                    break;
                case 3:
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                    il.Add(Instruction.Create(DnOpCodes.Not));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
                    il.Add(Instruction.Create(DnOpCodes.Not));
                    il.Add(Instruction.Create(DnOpCodes.And));
                    il.Add(Instruction.Create(DnOpCodes.Not));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
                    il.Add(Instruction.Create(DnOpCodes.And));
                    il.Add(Instruction.Create(DnOpCodes.Not));
                    il.Add(Instruction.Create(DnOpCodes.And));
                    il.Add(Instruction.Create(DnOpCodes.Ret));
                    break;
                case 4:
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
                    il.Add(Instruction.Create(DnOpCodes.Sub));
                    il.Add(Instruction.Create(DnOpCodes.Ret));
                    break;
                case 5:
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Add));
                    il.Add(Instruction.Create(DnOpCodes.Ret));
                    break;
                case 6:
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
                    il.Add(Instruction.Create(DnOpCodes.Neg));
                    il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Sub));
                    il.Add(Instruction.Create(DnOpCodes.Ret));
                    break;
                default:
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, masterSeed));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, masterSeed));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Ret));
                    break;
            }

            return method;
        }

        private MethodDef BuildFakeMethod(ModuleDef module, int variant)
        {
            var method = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Int32, module.CorLibTypes.Int32),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            method.Body = new CilBody();
            var il = method.Body.Instructions;

            switch (variant % FAKE_METHOD_COUNT)
            {
                case 0:
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                    il.Add(Instruction.Create(DnOpCodes.Add));
                    il.Add(Instruction.Create(DnOpCodes.Ret));
                    break;
                case 1:
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                    il.Add(Instruction.Create(DnOpCodes.Not));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Ret));
                    break;
                case 2:
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                    il.Add(Instruction.Create(DnOpCodes.Mul));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                    il.Add(Instruction.Create(DnOpCodes.Sub));
                    il.Add(Instruction.Create(DnOpCodes.Ret));
                    break;
                case 3:
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next(1, 16)));
                    il.Add(Instruction.Create(DnOpCodes.Shl));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Ret));
                    break;
                case 4:
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                    il.Add(Instruction.Create(DnOpCodes.Neg));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                    il.Add(Instruction.Create(DnOpCodes.Add));
                    il.Add(Instruction.Create(DnOpCodes.Ret));
                    break;
                default:
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                    il.Add(Instruction.Create(DnOpCodes.And));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                    il.Add(Instruction.Create(DnOpCodes.Or));
                    il.Add(Instruction.Create(DnOpCodes.Ret));
                    break;
            }

            return method;
        }

        private void EncryptIntegers(ModuleDef module)
        {
            foreach (TypeDef type in module.GetTypes())
            {
                if (engine.IsCompilerGenerated(type)) continue;
                foreach (MethodDef method in type.Methods)
                {
                    if (!engine.CanProcessMethod(method)) continue;
                    try
                    {
                        EncryptMethodIntegers(module, method);
                        method.Body.SimplifyBranches();
                        method.Body.OptimizeBranches();
                    }
                    catch { }
                }
            }
        }

        private void EncryptMethodIntegers(ModuleDef module, MethodDef method)
        {
            if (engine.SkipConstantExpansion(method)) return;
            var il = method.Body.Instructions;
            for (int i = il.Count - 1; i >= 0; i--)
            {
                if (!engine.IsIntLoad(il[i])) continue;
                int val = engine.ExtractInt(il[i]);
                if (val == int.MinValue) continue;
                if (val >= -1 && val <= 8) continue;
                if (rng.Next(0, 4) == 0) continue;

                int pattern = rng.Next(0, 14);
                List<Instruction> replacement;

                switch (pattern)
                {
                    case 0:
                        replacement = EmitKeyXor(module, val);
                        break;
                    case 1:
                        replacement = EmitKeyAdd(module, val);
                        break;
                    case 2:
                        replacement = EmitMasterSeedXor(module, val);
                        break;
                    case 3:
                        replacement = EmitTableLookup(module, val);
                        break;
                    case 4:
                        replacement = EmitDoubleTableXor(module, val);
                        break;
                    case 5:
                        replacement = EmitNotXor(module, val);
                        break;
                    case 6:
                        replacement = EmitChainField(module, val);
                        break;
                    case 7:
                        replacement = EmitRotorCompute(module, val);
                        break;
                    case 8:
                        replacement = EmitMbaFullAdder(module, val);
                        break;
                    case 9:
                        replacement = EmitMbaNegComplement(module, val);
                        break;
                    case 10:
                        replacement = EmitMbaXorFromOr(module, val);
                        break;
                    case 11:
                        replacement = EmitTripleKeyChain(module, val);
                        break;
                    case 12:
                        replacement = EmitOpaqueTickXor(module, val);
                        break;
                    default:
                        replacement = EmitMbaLayered(module, val);
                        break;
                }

                if (replacement == null || replacement.Count == 0) continue;

                il[i].OpCode = replacement[0].OpCode;
                il[i].Operand = replacement[0].Operand;
                for (int r = 1; r < replacement.Count; r++)
                    il.Insert(i + r, replacement[r]);
            }
        }

        private List<Instruction> EmitKeyXor(ModuleDef module, int target)
        {
            var insts = new List<Instruction>();
            int keyIdx = rng.Next(0, KEY_FIELD_COUNT);
            int keyVal = keyValues[keyIdx];
            int encoded = target ^ keyVal;

            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, encoded));
            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, keyFields[keyIdx]));
            insts.Add(Instruction.Create(DnOpCodes.Xor));
            return insts;
        }

        private List<Instruction> EmitKeyAdd(ModuleDef module, int target)
        {
            var insts = new List<Instruction>();
            int keyIdx = rng.Next(0, KEY_FIELD_COUNT);
            int keyVal = keyValues[keyIdx];
            int encoded = target - keyVal;

            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, encoded));
            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, keyFields[keyIdx]));
            insts.Add(Instruction.Create(DnOpCodes.Add));
            return insts;
        }

        private List<Instruction> EmitMasterSeedXor(ModuleDef module, int target)
        {
            var insts = new List<Instruction>();
            int keyIdx = rng.Next(0, KEY_FIELD_COUNT);
            int keyVal = keyValues[keyIdx];
            int intermediate = target ^ masterSeed;
            int encoded = intermediate ^ keyVal;

            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, encoded));
            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, keyFields[keyIdx]));
            insts.Add(Instruction.Create(DnOpCodes.Xor));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, masterSeed));
            insts.Add(Instruction.Create(DnOpCodes.Xor));
            return insts;
        }

        private List<Instruction> EmitTableLookup(ModuleDef module, int target)
        {
            var insts = new List<Instruction>();
            int tableIdx = rng.Next(0, CIPHER_TABLE_COUNT);
            int slot = rng.Next(0, CIPHER_TABLE_SIZE);
            int tableVal = cipherTables[tableIdx][slot];
            int encoded = target ^ tableVal;

            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, tableFields[tableIdx]));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, slot));
            insts.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, encoded));
            insts.Add(Instruction.Create(DnOpCodes.Xor));
            return insts;
        }

        private List<Instruction> EmitDoubleTableXor(ModuleDef module, int target)
        {
            var insts = new List<Instruction>();
            int tblA = rng.Next(0, CIPHER_TABLE_COUNT);
            int tblB = rng.Next(0, CIPHER_TABLE_COUNT);
            while (tblB == tblA && CIPHER_TABLE_COUNT > 1) tblB = rng.Next(0, CIPHER_TABLE_COUNT);
            int slotA = rng.Next(0, CIPHER_TABLE_SIZE);
            int slotB = rng.Next(0, CIPHER_TABLE_SIZE);
            int valA = cipherTables[tblA][slotA];
            int valB = cipherTables[tblB][slotB];
            int encoded = target ^ valA ^ valB;

            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, encoded));
            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, tableFields[tblA]));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, slotA));
            insts.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            insts.Add(Instruction.Create(DnOpCodes.Xor));
            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, tableFields[tblB]));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, slotB));
            insts.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            insts.Add(Instruction.Create(DnOpCodes.Xor));
            return insts;
        }

        private List<Instruction> EmitNotXor(ModuleDef module, int target)
        {
            var insts = new List<Instruction>();
            int keyIdx = rng.Next(0, KEY_FIELD_COUNT);
            int keyVal = keyValues[keyIdx];
            int notKey = ~keyVal;
            int encoded = target ^ notKey;

            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, encoded));
            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, keyFields[keyIdx]));
            insts.Add(Instruction.Create(DnOpCodes.Not));
            insts.Add(Instruction.Create(DnOpCodes.Xor));
            return insts;
        }

        private List<Instruction> EmitChainField(ModuleDef module, int target)
        {
            var insts = new List<Instruction>();
            int keyA = rng.Next(0, KEY_FIELD_COUNT);
            int keyB = rng.Next(0, KEY_FIELD_COUNT);
            while (keyB == keyA && KEY_FIELD_COUNT > 1) keyB = rng.Next(0, KEY_FIELD_COUNT);
            int valA = keyValues[keyA];
            int valB = keyValues[keyB];
            int combined = valA ^ valB;
            int encoded = target ^ combined;

            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, encoded));
            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, keyFields[keyA]));
            insts.Add(Instruction.Create(DnOpCodes.Xor));
            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, keyFields[keyB]));
            insts.Add(Instruction.Create(DnOpCodes.Xor));
            return insts;
        }

        private List<Instruction> EmitRotorCompute(ModuleDef module, int target)
        {
            var insts = new List<Instruction>();
            int keyIdx = rng.Next(0, KEY_FIELD_COUNT);
            int keyVal = keyValues[keyIdx];
            int tableIdx = rng.Next(0, CIPHER_TABLE_COUNT);
            int slot = rng.Next(0, CIPHER_TABLE_SIZE);
            int tableVal = cipherTables[tableIdx][slot];
            int rotor = keyVal ^ tableVal;
            int encoded = target - rotor;

            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, encoded));
            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, keyFields[keyIdx]));
            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, tableFields[tableIdx]));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, slot));
            insts.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            insts.Add(Instruction.Create(DnOpCodes.Xor));
            insts.Add(Instruction.Create(DnOpCodes.Add));
            return insts;
        }

        private List<Instruction> EmitMbaFullAdder(ModuleDef module, int target)
        {
            var insts = new List<Instruction>();
            int keyIdx = rng.Next(0, KEY_FIELD_COUNT);
            int k = keyValues[keyIdx];
            int b;
            unchecked { b = target - k; }

            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, keyFields[keyIdx]));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, b));
            insts.Add(Instruction.Create(DnOpCodes.Xor));

            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, keyFields[keyIdx]));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, b));
            insts.Add(Instruction.Create(DnOpCodes.And));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, 2));
            insts.Add(Instruction.Create(DnOpCodes.Mul));

            insts.Add(Instruction.Create(DnOpCodes.Add));

            return insts;
        }

        private List<Instruction> EmitMbaNegComplement(ModuleDef module, int target)
        {
            var insts = new List<Instruction>();
            int keyIdx = rng.Next(0, KEY_FIELD_COUNT);
            int tableIdx = rng.Next(0, CIPHER_TABLE_COUNT);
            int slot = rng.Next(0, CIPHER_TABLE_SIZE);
            int k = keyValues[keyIdx];
            int tval = cipherTables[tableIdx][slot];

            int composite;
            int negComposite;
            int encoded;
            unchecked
            {
                composite = k ^ tval;
                negComposite = ~composite + 1;
                encoded = target - negComposite;
            }

            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, keyFields[keyIdx]));
            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, tableFields[tableIdx]));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, slot));
            insts.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            insts.Add(Instruction.Create(DnOpCodes.Xor));
            insts.Add(Instruction.Create(DnOpCodes.Not));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, 1));
            insts.Add(Instruction.Create(DnOpCodes.Add));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, encoded));
            insts.Add(Instruction.Create(DnOpCodes.Add));

            return insts;
        }

        private List<Instruction> EmitMbaXorFromOr(ModuleDef module, int target)
        {
            var insts = new List<Instruction>();
            int keyIdx = rng.Next(0, KEY_FIELD_COUNT);
            int k = keyValues[keyIdx];
            int b;
            unchecked { b = target ^ k; }

            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, keyFields[keyIdx]));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, b));
            insts.Add(Instruction.Create(DnOpCodes.Or));

            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, keyFields[keyIdx]));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, b));
            insts.Add(Instruction.Create(DnOpCodes.And));

            insts.Add(Instruction.Create(DnOpCodes.Sub));

            return insts;
        }

        private List<Instruction> EmitTripleKeyChain(ModuleDef module, int target)
        {
            var insts = new List<Instruction>();
            int idxA = rng.Next(0, KEY_FIELD_COUNT);
            int idxB = rng.Next(0, KEY_FIELD_COUNT);
            while (idxB == idxA && KEY_FIELD_COUNT > 1) idxB = rng.Next(0, KEY_FIELD_COUNT);
            int idxC = rng.Next(0, KEY_FIELD_COUNT);
            while ((idxC == idxA || idxC == idxB) && KEY_FIELD_COUNT > 2) idxC = rng.Next(0, KEY_FIELD_COUNT);

            int encoded;
            unchecked { encoded = target ^ keyValues[idxA] ^ keyValues[idxB] ^ keyValues[idxC]; }

            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, encoded));
            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, keyFields[idxA]));
            insts.Add(Instruction.Create(DnOpCodes.Xor));
            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, keyFields[idxB]));
            insts.Add(Instruction.Create(DnOpCodes.Xor));
            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, keyFields[idxC]));
            insts.Add(Instruction.Create(DnOpCodes.Xor));
            return insts;
        }

        private List<Instruction> EmitOpaqueTickXor(ModuleDef module, int target)
        {
            if (_getTickCount == null)
                return EmitTripleKeyChain(module, target);

            var insts = new List<Instruction>();
            int keyIdx = rng.Next(0, KEY_FIELD_COUNT);
            int keyVal = keyValues[keyIdx];
            int encoded;
            unchecked { encoded = target ^ keyVal; }

            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, encoded));
            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, keyFields[keyIdx]));
            insts.Add(Instruction.Create(DnOpCodes.Xor));
            insts.Add(Instruction.Create(DnOpCodes.Call, _getTickCount));
            insts.Add(Instruction.Create(DnOpCodes.Dup));
            insts.Add(Instruction.Create(DnOpCodes.Xor));
            insts.Add(Instruction.Create(DnOpCodes.Add));

            return insts;
        }

        private List<Instruction> EmitMbaLayered(ModuleDef module, int target)
        {
            var insts = new List<Instruction>();
            int keyA = rng.Next(0, KEY_FIELD_COUNT);
            int keyB = rng.Next(0, KEY_FIELD_COUNT);
            while (keyB == keyA && KEY_FIELD_COUNT > 1) keyB = rng.Next(0, KEY_FIELD_COUNT);
            int tableIdx = rng.Next(0, CIPHER_TABLE_COUNT);
            int slot = rng.Next(0, CIPHER_TABLE_SIZE);

            int kA = keyValues[keyA];
            int kB = keyValues[keyB];
            int tval = cipherTables[tableIdx][slot];

            int encoded;
            unchecked
            {
                int inner = kA ^ kB;
                int sum = inner + tval;
                encoded = target - sum;
            }

            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, keyFields[keyA]));
            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, keyFields[keyB]));
            insts.Add(Instruction.Create(DnOpCodes.Xor));
            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, tableFields[tableIdx]));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, slot));
            insts.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            insts.Add(Instruction.Create(DnOpCodes.Xor));

            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, keyFields[keyA]));
            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, keyFields[keyB]));
            insts.Add(Instruction.Create(DnOpCodes.Xor));
            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, tableFields[tableIdx]));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, slot));
            insts.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            insts.Add(Instruction.Create(DnOpCodes.And));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, 2));
            insts.Add(Instruction.Create(DnOpCodes.Mul));

            insts.Add(Instruction.Create(DnOpCodes.Add));

            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, encoded));
            insts.Add(Instruction.Create(DnOpCodes.Add));

            return insts;
        }

        private void BuildHostCctor(ModuleDef module, TypeDef host, int hostMod)
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

            for (int i = 0; i < KEY_FIELD_COUNT; i++)
            {
                if (i % 3 != hostMod) continue;
                int pattern = rng.Next(0, 5);
                switch (pattern)
                {
                    case 0:
                    {
                        int msk = rng.Next(int.MinValue, int.MaxValue);
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, keyValues[i] ^ msk));
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, msk));
                        il.Add(Instruction.Create(DnOpCodes.Xor));
                        break;
                    }
                    case 1:
                    {
                        int k = rng.Next(int.MinValue, int.MaxValue);
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, k));
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, k ^ keyValues[i]));
                        il.Add(Instruction.Create(DnOpCodes.Xor));
                        break;
                    }
                    case 2:
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, ~keyValues[i]));
                        il.Add(Instruction.Create(DnOpCodes.Not));
                        break;
                    case 3:
                    {
                        int a = rng.Next(1000, 999999);
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, a));
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, a - keyValues[i]));
                        il.Add(Instruction.Create(DnOpCodes.Sub));
                        break;
                    }
                    default:
                    {
                        int p = rng.Next(int.MinValue, int.MaxValue);
                        int q = rng.Next(int.MinValue, int.MaxValue);
                        int r = keyValues[i] ^ p ^ q;
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, p));
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, q));
                        il.Add(Instruction.Create(DnOpCodes.Xor));
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, r));
                        il.Add(Instruction.Create(DnOpCodes.Xor));
                        break;
                    }
                }
                il.Add(Instruction.Create(DnOpCodes.Stsfld, keyFields[i]));
            }

            for (int t = 0; t < CIPHER_TABLE_COUNT; t++)
            {
                if (t % 3 != hostMod) continue;

                int seed = rng.Next(1, int.MaxValue);
                int[] masked = MaskInt32Array(cipherTables[t], seed);
                byte[] maskedBytes = Int32ArrayToLittleEndianBytes(masked);
                FieldDef rvaField = MakeRvaField(module, host, sysValueType, maskedBytes);

                var varArr = new Local(new SZArraySig(module.CorLibTypes.Int32));
                var varIdx = new Local(module.CorLibTypes.Int32);
                var varState = new Local(module.CorLibTypes.Int32);
                cctor.Body.Variables.Add(varArr);
                cctor.Body.Variables.Add(varIdx);
                cctor.Body.Variables.Add(varState);

                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, CIPHER_TABLE_SIZE));
                il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.Int32.TypeDefOrRef));
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
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, CIPHER_TABLE_SIZE));
                il.Add(Instruction.Create(DnOpCodes.Blt, loopBody));

                il.Add(Instruction.Create(DnOpCodes.Ldloc, varArr));
                il.Add(Instruction.Create(DnOpCodes.Stsfld, tableFields[t]));
            }

            il.Add(Instruction.Create(DnOpCodes.Ret));
            host.Methods.Add(cctor);
            engine.injectedMethods.Add(cctor);
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
