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
    internal class ConstantsEncodingProtection
    {
        private Obfuscation engine;
        private Random rng;

        private const int TABLE_COUNT = 16;
        private const int TABLE_SIZE = 512;
        private List<FieldDef> constTables;
        private List<int[]> tableData;
        private List<int[]> tablePermutation;
        private int[] tableAllocIdx;
        private List<MethodDef> decoderMethods;
        private TypeDef containerType;
        private FieldDef masterSeed;
        private int masterSeedValue;

        private List<FieldDef> chainFields;
        private List<int> chainFieldValues;
        private const int CHAIN_FIELD_COUNT = 6;

        private FieldDef tableScrambleField;
        private int tableScrambleValue;

        internal ConstantsEncodingProtection(Obfuscation eng)
        {
            engine = eng;
            rng = eng.rng;
        }

        internal void ApplyConstantsEncoding(ModuleDef module, TypeDef modType)
        {
            engine.activeOption = "ConstantsEncoding";
            constTables = new List<FieldDef>();
            tableData = new List<int[]>();
            tablePermutation = new List<int[]>();
            tableAllocIdx = new int[TABLE_COUNT];
            decoderMethods = new List<MethodDef>();
            chainFields = new List<FieldDef>();
            chainFieldValues = new List<int>();

            containerType = new TypeDefUser("", engine.MakeName(),
                module.CorLibTypes.Object.TypeDefOrRef);
            containerType.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
            module.Types.Add(containerType);
            engine.injectedTypes.Add(containerType);

            masterSeedValue = rng.Next(100000, int.MaxValue / 2);
            masterSeed = new FieldDefUser(engine.MakeName(),
                new FieldSig(module.CorLibTypes.Int32),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            containerType.Fields.Add(masterSeed);

            tableScrambleValue = rng.Next(0x10001, int.MaxValue / 3);
            tableScrambleField = new FieldDefUser(engine.MakeName(),
                new FieldSig(module.CorLibTypes.Int32),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            containerType.Fields.Add(tableScrambleField);

            for (int c = 0; c < CHAIN_FIELD_COUNT; c++)
            {
                int cv = rng.Next(int.MinValue, int.MaxValue);
                chainFieldValues.Add(cv);
                var cf = new FieldDefUser(engine.MakeName(),
                    new FieldSig(module.CorLibTypes.Int32),
                    DnFieldAttributes.Assembly | DnFieldAttributes.Static);
                containerType.Fields.Add(cf);
                chainFields.Add(cf);
            }

            for (int d = 0; d < engine.LevelRange(2, 4, 3, 6, 5, 9); d++)
            {
                containerType.Fields.Add(new FieldDefUser(engine.MakeName(),
                    new FieldSig(module.CorLibTypes.Int32),
                    DnFieldAttributes.Private | DnFieldAttributes.Static));
            }

            for (int t = 0; t < TABLE_COUNT; t++)
            {
                var tableField = new FieldDefUser(engine.MakeName(),
                    new FieldSig(new SZArraySig(module.CorLibTypes.Int32)),
                    DnFieldAttributes.Assembly | DnFieldAttributes.Static);
                containerType.Fields.Add(tableField);
                constTables.Add(tableField);

                var data = new int[TABLE_SIZE];
                for (int i = 0; i < TABLE_SIZE; i++)
                    data[i] = rng.Next(int.MinValue, int.MaxValue);
                tableData.Add(data);

                var perm = new int[TABLE_SIZE];
                for (int i = 0; i < TABLE_SIZE; i++) perm[i] = i;
                for (int i = TABLE_SIZE - 1; i > 0; i--)
                {
                    int j = rng.Next(0, i + 1);
                    int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
                }
                tablePermutation.Add(perm);
                tableAllocIdx[t] = 0;
            }

            for (int m = 0; m < 8; m++)
            {
                var decoder = BuildDecoderMethod(module, m);
                containerType.Methods.Add(decoder);
                engine.injectedMethods.Add(decoder);
                decoderMethods.Add(decoder);
            }

            for (int m = 0; m < 4; m++)
            {
                var mbaDecoder = BuildMbaDecoderMethod(module, m);
                containerType.Methods.Add(mbaDecoder);
                engine.injectedMethods.Add(mbaDecoder);
                decoderMethods.Add(mbaDecoder);
            }

            for (int f = 0; f < 4; f++)
            {
                var fake = BuildFakeDecoder(module);
                containerType.Methods.Add(fake);
                engine.injectedMethods.Add(fake);
            }

            int counter = 0;
            foreach (TypeDef type in module.GetTypes())
            {
                if (engine.IsCompilerGenerated(type)) continue;
                foreach (MethodDef method in type.Methods)
                {
                    if (!engine.CanProcessMethod(method)) continue;
                    try
                    {
                        counter += EncodeConstants(module, method);
                        method.Body.SimplifyBranches();
                        method.Body.OptimizeBranches();
                    }
                    catch { }
                }
            }

            foreach (TypeDef type in module.GetTypes())
            {
                if (engine.injectedTypes.Contains(type)) continue;
                if (engine.IsCompilerGenerated(type)) continue;
                if (!engine.IsWinFormsType(type)) continue;
                if (engine.IsTypeUserExcluded(type)) continue;
                foreach (MethodDef method in type.Methods)
                {
                    if (!method.HasBody || !method.Body.HasInstructions) continue;
                    if (engine.injectedMethods.Contains(method)) continue;
                    if (method.HasGenericParameters) continue;
                    if (engine.IsMethodUserExcluded(method)) continue;

                    bool isDesignerScope = method.Name == "InitializeComponent"
                        || engine.designerSplitSubMethods.Contains(method);
                    if (!isDesignerScope) continue;
                    try
                    {
                        counter += EncodeConstants(module, method);
                        method.Body.SimplifyBranches();
                        method.Body.OptimizeBranches();
                    }
                    catch { }
                }
            }

            if (counter > 0)
            {
                var initMethod = BuildTableInitializer(module);
                containerType.Methods.Add(initMethod);
                engine.injectedMethods.Add(initMethod);
                engine.InjectCallInCctor(module, modType, initMethod);
            }
        }

        private int AllocSlot(int tableIdx)
        {
            if (tableAllocIdx[tableIdx] >= TABLE_SIZE) return -1;
            return tablePermutation[tableIdx][tableAllocIdx[tableIdx]++];
        }

        private int EncodeConstants(ModuleDef module, MethodDef method)
        {
            if (engine.SkipConstantExpansion(method)) return 0;
            var il = method.Body.Instructions;
            int encoded = 0;

            for (int i = 0; i < il.Count; i++)
            {
                if (il[i].OpCode == DnOpCodes.Ldc_I8)
                {
                    long val = (long)il[i].Operand;
                    int hi = (int)(val >> 32);
                    int lo = (int)(val & 0xFFFFFFFFL);

                    var hiInsts = BuildIntRetrieval(hi);
                    var loInsts = BuildIntRetrieval(lo);

                    if (hiInsts != null && loInsts != null)
                    {
                        var replacement = new List<Instruction>();
                        replacement.AddRange(hiInsts);
                        replacement.Add(Instruction.Create(DnOpCodes.Conv_I8));
                        replacement.Add(Instruction.Create(DnOpCodes.Ldc_I4, 32));
                        replacement.Add(Instruction.Create(DnOpCodes.Shl));
                        replacement.AddRange(loInsts);

                        replacement.Add(Instruction.Create(DnOpCodes.Conv_U4));
                        replacement.Add(Instruction.Create(DnOpCodes.Conv_U8));
                        replacement.Add(Instruction.Create(DnOpCodes.Or));

                        il[i].OpCode = replacement[0].OpCode;
                        il[i].Operand = replacement[0].Operand;
                        for (int j = 1; j < replacement.Count; j++)
                            il.Insert(i + j, replacement[j]);
                        i += replacement.Count - 1;
                        encoded++;
                    }
                }
                else if (il[i].OpCode == DnOpCodes.Ldc_R4)
                {
                    float fval = (float)il[i].Operand;
                    byte[] fBytes = BitConverter.GetBytes(fval);
                    int ival = BitConverter.ToInt32(fBytes, 0);

                    var insts = BuildIntRetrieval(ival);
                    if (insts != null)
                    {
                        var bitsToSingle = module.Import(
                            typeof(BitConverter).GetMethod("ToSingle", new[] { typeof(byte[]), typeof(int) }));
                        var getBytes = module.Import(
                            typeof(BitConverter).GetMethod("GetBytes", new[] { typeof(int) }));

                        var replacement = new List<Instruction>();
                        replacement.AddRange(insts);
                        replacement.Add(Instruction.Create(DnOpCodes.Call, getBytes));
                        replacement.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
                        replacement.Add(Instruction.Create(DnOpCodes.Call, bitsToSingle));

                        il[i].OpCode = replacement[0].OpCode;
                        il[i].Operand = replacement[0].Operand;
                        for (int j = 1; j < replacement.Count; j++)
                            il.Insert(i + j, replacement[j]);
                        i += replacement.Count - 1;
                        encoded++;
                    }
                }
                else if (il[i].OpCode == DnOpCodes.Ldc_R8)
                {
                    double dval = (double)il[i].Operand;
                    long dbits = BitConverter.DoubleToInt64Bits(dval);
                    int lo = (int)(dbits & 0xFFFFFFFFL);
                    int hi = (int)((dbits >> 32) & 0xFFFFFFFFL);

                    var loInsts = BuildIntRetrieval(lo);
                    var hiInsts = BuildIntRetrieval(hi);

                    if (loInsts != null && hiInsts != null)
                    {
                        var int64BitsToDouble = module.Import(
                            typeof(BitConverter).GetMethod("Int64BitsToDouble", new[] { typeof(long) }));

                        var replacement = new List<Instruction>();
                        replacement.AddRange(hiInsts);
                        replacement.Add(Instruction.Create(DnOpCodes.Conv_I8));
                        replacement.Add(Instruction.Create(DnOpCodes.Ldc_I4, 32));
                        replacement.Add(Instruction.Create(DnOpCodes.Shl));
                        replacement.AddRange(loInsts);
                        replacement.Add(Instruction.Create(DnOpCodes.Conv_U4));
                        replacement.Add(Instruction.Create(DnOpCodes.Conv_U8));
                        replacement.Add(Instruction.Create(DnOpCodes.Or));
                        replacement.Add(Instruction.Create(DnOpCodes.Call, int64BitsToDouble));

                        il[i].OpCode = replacement[0].OpCode;
                        il[i].Operand = replacement[0].Operand;
                        for (int j = 1; j < replacement.Count; j++)
                            il.Insert(i + j, replacement[j]);
                        i += replacement.Count - 1;
                        encoded++;
                    }
                }
            }

            return encoded;
        }

        private List<Instruction> BuildIntRetrieval(int target)
        {
            int pattern = rng.Next(0, 7);
            switch (pattern)
            {
                case 0: return BuildTableLookup(target);
                case 1: return BuildCrossTableLookup(target);
                case 2: return BuildSeedMath(target);
                case 3: return BuildChainedLookup(target);
                case 4: return BuildArithmeticChain(target);
                case 5: return BuildMbaArithmeticChain(target);
                default: return BuildChainFieldMath(target);
            }
        }

        private List<Instruction> BuildTableLookup(int target)
        {
            int decoderIdx = rng.Next(0, decoderMethods.Count);
            int tableMode = decoderIdx % 4;
            int t = tableMode;
            int s1 = AllocSlot(t);
            int s2 = AllocSlot(t);
            if (s1 < 0 || s2 < 0) return BuildArithmeticChain(target);

            SetTablePairForDecoder(t, s1, s2, target, decoderIdx);

            var insts = new List<Instruction>();
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, s1));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, s2));
            insts.Add(Instruction.Create(DnOpCodes.Call, decoderMethods[decoderIdx]));
            return insts;
        }

        private List<Instruction> BuildCrossTableLookup(int target)
        {
            int dmA = rng.Next(0, decoderMethods.Count);
            int dmB = rng.Next(0, decoderMethods.Count);
            while (dmB == dmA) dmB = rng.Next(0, decoderMethods.Count);
            int tA = dmA % 4;
            int tB = dmB % 4;
            while (tB == tA) { dmB = rng.Next(0, decoderMethods.Count); tB = dmB % 4; }

            int a1 = AllocSlot(tA); int a2 = AllocSlot(tA);
            int b1 = AllocSlot(tB); int b2 = AllocSlot(tB);
            if (a1 < 0 || a2 < 0 || b1 < 0 || b2 < 0) return BuildArithmeticChain(target);

            int partial = rng.Next(int.MinValue, int.MaxValue);
            int other = partial ^ target;

            SetTablePairForDecoder(tA, a1, a2, partial, dmA);
            SetTablePairForDecoder(tB, b1, b2, other, dmB);

            var insts = new List<Instruction>();
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, a1));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, a2));
            insts.Add(Instruction.Create(DnOpCodes.Call, decoderMethods[dmA]));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, b1));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, b2));
            insts.Add(Instruction.Create(DnOpCodes.Call, decoderMethods[dmB]));
            insts.Add(Instruction.Create(DnOpCodes.Xor));
            return insts;
        }

        private List<Instruction> BuildSeedMath(int target)
        {
            int cfIdx = rng.Next(0, CHAIN_FIELD_COUNT);
            int cfVal = chainFieldValues[cfIdx];
            int diff = target ^ cfVal;
            var insts = new List<Instruction>();
            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, chainFields[cfIdx]));

            int extra = rng.Next(0, 3);
            switch (extra)
            {
                case 0:
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, diff));
                    insts.Add(Instruction.Create(DnOpCodes.Xor));
                    break;
                case 1:
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, unchecked(cfVal - target)));
                    insts.Add(Instruction.Create(DnOpCodes.Sub));
                    break;
                default:
                    insts.Add(Instruction.Create(DnOpCodes.Not));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, unchecked(target - (~cfVal))));
                    insts.Add(Instruction.Create(DnOpCodes.Add));
                    break;
            }
            return insts;
        }

        private List<Instruction> BuildChainedLookup(int target)
        {
            int dmA = rng.Next(0, decoderMethods.Count);
            int dmB = rng.Next(0, decoderMethods.Count);
            while (dmB == dmA) dmB = rng.Next(0, decoderMethods.Count);
            int dmC = rng.Next(0, decoderMethods.Count);
            while (dmC == dmA || dmC == dmB) dmC = rng.Next(0, decoderMethods.Count);
            int tA = dmA % 4;
            int tB = dmB % 4;
            int tC = dmC % 4;

            int a1 = AllocSlot(tA); int a2 = AllocSlot(tA);
            int b1 = AllocSlot(tB); int b2 = AllocSlot(tB);
            int c1 = AllocSlot(tC); int c2 = AllocSlot(tC);
            if (a1 < 0 || a2 < 0 || b1 < 0 || b2 < 0 || c1 < 0 || c2 < 0)
                return BuildArithmeticChain(target);

            int p1 = rng.Next(int.MinValue, int.MaxValue);
            int p2 = rng.Next(int.MinValue, int.MaxValue);
            int p3 = target ^ p1 ^ p2;

            SetTablePairForDecoder(tA, a1, a2, p1, dmA);
            SetTablePairForDecoder(tB, b1, b2, p2, dmB);
            SetTablePairForDecoder(tC, c1, c2, p3, dmC);

            var insts = new List<Instruction>();
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, a1));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, a2));
            insts.Add(Instruction.Create(DnOpCodes.Call, decoderMethods[dmA]));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, b1));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, b2));
            insts.Add(Instruction.Create(DnOpCodes.Call, decoderMethods[dmB]));
            insts.Add(Instruction.Create(DnOpCodes.Xor));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, c1));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, c2));
            insts.Add(Instruction.Create(DnOpCodes.Call, decoderMethods[dmC]));
            insts.Add(Instruction.Create(DnOpCodes.Xor));
            return insts;
        }

        private List<Instruction> BuildChainFieldMath(int target)
        {
            int cfIdx = rng.Next(0, CHAIN_FIELD_COUNT);
            int cfVal = chainFieldValues[cfIdx];

            int variant = rng.Next(0, 4);
            var insts = new List<Instruction>();

            switch (variant)
            {
                case 0:
                {
                    int k1 = rng.Next(int.MinValue, int.MaxValue);
                    int k2 = unchecked(target ^ cfVal ^ k1);
                    insts.Add(Instruction.Create(DnOpCodes.Ldsfld, chainFields[cfIdx]));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, k1));
                    insts.Add(Instruction.Create(DnOpCodes.Xor));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, k2));
                    insts.Add(Instruction.Create(DnOpCodes.Xor));
                    break;
                }
                case 1:
                {
                    int k1 = rng.Next(int.MinValue, int.MaxValue);
                    int partial = unchecked(cfVal + k1);
                    int delta = unchecked(target - partial);
                    insts.Add(Instruction.Create(DnOpCodes.Ldsfld, chainFields[cfIdx]));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, k1));
                    insts.Add(Instruction.Create(DnOpCodes.Add));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, delta));
                    insts.Add(Instruction.Create(DnOpCodes.Add));
                    break;
                }
                case 2:
                {
                    int notCf = ~cfVal;
                    int k1 = rng.Next(int.MinValue, int.MaxValue);
                    int k2 = unchecked(target ^ notCf ^ k1);
                    insts.Add(Instruction.Create(DnOpCodes.Ldsfld, chainFields[cfIdx]));
                    insts.Add(Instruction.Create(DnOpCodes.Not));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, k1));
                    insts.Add(Instruction.Create(DnOpCodes.Xor));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, k2));
                    insts.Add(Instruction.Create(DnOpCodes.Xor));
                    break;
                }
                default:
                {
                    int cf2Idx = rng.Next(0, CHAIN_FIELD_COUNT);
                    while (cf2Idx == cfIdx) cf2Idx = rng.Next(0, CHAIN_FIELD_COUNT);
                    int cf2Val = chainFieldValues[cf2Idx];
                    int combined = unchecked(cfVal ^ cf2Val);
                    int k = unchecked(target ^ combined);
                    insts.Add(Instruction.Create(DnOpCodes.Ldsfld, chainFields[cfIdx]));
                    insts.Add(Instruction.Create(DnOpCodes.Ldsfld, chainFields[cf2Idx]));
                    insts.Add(Instruction.Create(DnOpCodes.Xor));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, k));
                    insts.Add(Instruction.Create(DnOpCodes.Xor));
                    break;
                }
            }
            return insts;
        }

        private List<Instruction> BuildMbaArithmeticChain(int target)
        {
            int variant = rng.Next(0, 5);
            var insts = new List<Instruction>();

            switch (variant)
            {
                case 0:
                {
                    int a = rng.Next(int.MinValue, int.MaxValue);
                    int b = rng.Next(int.MinValue, int.MaxValue);
                    int xorAb = unchecked(a ^ b);
                    int andAb = unchecked(a & b);
                    int sumAb = unchecked(a + b);
                    int k = unchecked(target - sumAb);
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, xorAb));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, andAb));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, 2));
                    insts.Add(Instruction.Create(DnOpCodes.Mul));
                    insts.Add(Instruction.Create(DnOpCodes.Add));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, k));
                    insts.Add(Instruction.Create(DnOpCodes.Add));
                    break;
                }
                case 1:
                {
                    int a = rng.Next(int.MinValue, int.MaxValue);
                    int b = rng.Next(int.MinValue, int.MaxValue);
                    int orAb = unchecked(a | b);
                    int andAb = unchecked(a & b);
                    int xorAb = unchecked(a ^ b);
                    int k = unchecked(target - xorAb);
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, orAb));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, andAb));
                    insts.Add(Instruction.Create(DnOpCodes.Sub));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, k));
                    insts.Add(Instruction.Create(DnOpCodes.Add));
                    break;
                }
                case 2:
                {
                    int a = rng.Next(int.MinValue, int.MaxValue);
                    int notA = ~a;
                    int k1 = rng.Next(int.MinValue, int.MaxValue);
                    int k2 = unchecked(target - (notA + 1) - k1);
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, a));
                    insts.Add(Instruction.Create(DnOpCodes.Not));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
                    insts.Add(Instruction.Create(DnOpCodes.Add));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, k1));
                    insts.Add(Instruction.Create(DnOpCodes.Add));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, k2));
                    insts.Add(Instruction.Create(DnOpCodes.Add));
                    break;
                }
                case 3:
                {
                    int a = rng.Next(int.MinValue, int.MaxValue);
                    int b = rng.Next(int.MinValue, int.MaxValue);
                    int xorAb = unchecked(a ^ b);
                    int andAb = unchecked(a & b);
                    int fullAdd = unchecked((a ^ b) + 2 * (a & b));
                    int step2 = unchecked(~fullAdd);
                    int k = unchecked(target - step2);
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, xorAb));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, andAb));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, 2));
                    insts.Add(Instruction.Create(DnOpCodes.Mul));
                    insts.Add(Instruction.Create(DnOpCodes.Add));
                    insts.Add(Instruction.Create(DnOpCodes.Not));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, k));
                    insts.Add(Instruction.Create(DnOpCodes.Add));
                    break;
                }
                default:
                {
                    int a = rng.Next(int.MinValue, int.MaxValue);
                    int b = rng.Next(int.MinValue, int.MaxValue);
                    int orAb = unchecked(a | b);
                    int andAb = unchecked(a & b);
                    int xorAb = unchecked(a ^ b);
                    int notXor = ~xorAb;
                    int k = unchecked(target - notXor);
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, orAb));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, andAb));
                    insts.Add(Instruction.Create(DnOpCodes.Sub));
                    insts.Add(Instruction.Create(DnOpCodes.Not));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, k));
                    insts.Add(Instruction.Create(DnOpCodes.Add));
                    break;
                }
            }
            return insts;
        }

        private void SetTablePair(int table, int s1, int s2, int target, int mode)
        {
            switch (mode)
            {
                case 0: tableData[table][s2] = tableData[table][s1] ^ target; break;
                case 1: tableData[table][s2] = unchecked(target - tableData[table][s1]); break;
                case 2: tableData[table][s2] = ~tableData[table][s1] ^ target; break;
                case 3: tableData[table][s2] = unchecked(target + ~tableData[table][s1]); break;
            }
        }

        private void SetTablePairForDecoder(int table, int s1, int s2, int target, int decoderIdx)
        {
            int v0 = tableData[table][s1];
            unchecked
            {
                switch (decoderIdx % 12)
                {
                    case 0: tableData[table][s2] = v0 ^ target; break;
                    case 1: tableData[table][s2] = target - v0; break;
                    case 2: tableData[table][s2] = ~v0 ^ target; break;
                    case 3: tableData[table][s2] = target + ~v0; break;
                    case 4: tableData[table][s2] = v0 ^ target; break;
                    case 5: tableData[table][s2] = target - v0; break;
                    case 6: tableData[table][s2] = ~v0 ^ target; break;
                    case 7: tableData[table][s2] = target + ~v0; break;
                    case 8: tableData[table][s2] = target - v0; break;
                    case 9: tableData[table][s2] = target ^ v0; break;
                    case 10: tableData[table][s2] = target - v0; break;
                    default: tableData[table][s2] = target ^ v0; break;
                }
            }
        }

        private List<Instruction> BuildArithmeticChain(int target)
        {
            var insts = new List<Instruction>();
            int p = rng.Next(0, 8);
            switch (p)
            {
                case 0:
                    int k1 = rng.Next(int.MinValue, int.MaxValue);
                    int k2 = rng.Next(int.MinValue, int.MaxValue);
                    int k3 = rng.Next(int.MinValue, int.MaxValue);
                    int k4 = target ^ k1 ^ k2 ^ k3;
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, k1));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, k2));
                    insts.Add(Instruction.Create(DnOpCodes.Xor));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, k3));
                    insts.Add(Instruction.Create(DnOpCodes.Xor));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, k4));
                    insts.Add(Instruction.Create(DnOpCodes.Xor));
                    break;
                case 1:
                    int m1 = rng.Next(int.MinValue, int.MaxValue);
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, m1));
                    insts.Add(Instruction.Create(DnOpCodes.Not));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, unchecked(target - (~m1))));
                    insts.Add(Instruction.Create(DnOpCodes.Add));
                    break;
                case 2:
                    int n1 = rng.Next(1000, 999999);
                    int n2 = rng.Next(1000, 999999);
                    int n3 = unchecked(target - (n1 + n2));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, n1));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, n2));
                    insts.Add(Instruction.Create(DnOpCodes.Add));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, n3));
                    insts.Add(Instruction.Create(DnOpCodes.Add));
                    break;
                case 3:
                    int mask = rng.Next(int.MinValue, int.MaxValue);
                    int pa = target & mask;
                    int pb = target & ~mask;
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, pa));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, pb));
                    insts.Add(Instruction.Create(DnOpCodes.Or));
                    break;
                case 4:
                    int r1 = rng.Next(int.MinValue, int.MaxValue);
                    int r2 = rng.Next(int.MinValue, int.MaxValue);
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, r1));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, r2));
                    insts.Add(Instruction.Create(DnOpCodes.Add));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, unchecked((r1 + r2) ^ target)));
                    insts.Add(Instruction.Create(DnOpCodes.Xor));
                    break;
                case 5:
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, ~target));
                    insts.Add(Instruction.Create(DnOpCodes.Not));
                    break;
                case 6:
                    int w1 = rng.Next(int.MinValue, int.MaxValue);
                    int w2 = unchecked(target - w1);
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, w1));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, w2));
                    insts.Add(Instruction.Create(DnOpCodes.Add));
                    break;
                default:
                    int z1 = rng.Next(100000, 9999999);
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, unchecked(z1 + target)));
                    insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, z1));
                    insts.Add(Instruction.Create(DnOpCodes.Sub));
                    break;
            }
            return insts;
        }

        private MethodDef BuildDecoderMethod(ModuleDef module, int mode)
        {
            int tableIdx = mode % 4;
            var method = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Int32,
                    module.CorLibTypes.Int32, module.CorLibTypes.Int32),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            method.Body = new CilBody();
            method.Body.InitLocals = true;
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            var il = method.Body.Instructions;

            il.Add(Instruction.Create(DnOpCodes.Ldsfld, constTables[tableIdx]));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));

            il.Add(Instruction.Create(DnOpCodes.Ldsfld, constTables[tableIdx]));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));

            switch (mode % 4)
            {
                case 0:
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    break;
                case 1:
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                    il.Add(Instruction.Create(DnOpCodes.Add));
                    break;
                case 2:
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Not));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    break;
                case 3:

                    il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Not));
                    il.Add(Instruction.Create(DnOpCodes.Sub));
                    break;
            }

            il.Add(Instruction.Create(DnOpCodes.Ret));
            return method;
        }

        private MethodDef BuildMbaDecoderMethod(ModuleDef module, int mbaMode)
        {
            int tableIdx = (mbaMode + 8) % 4;
            var method = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Int32,
                    module.CorLibTypes.Int32, module.CorLibTypes.Int32),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            method.Body = new CilBody();
            method.Body.InitLocals = true;
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            var il = method.Body.Instructions;

            il.Add(Instruction.Create(DnOpCodes.Ldsfld, constTables[tableIdx]));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));

            il.Add(Instruction.Create(DnOpCodes.Ldsfld, constTables[tableIdx]));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));

            switch (mbaMode)
            {
                case 0:
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                    il.Add(Instruction.Create(DnOpCodes.And));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4_2));
                    il.Add(Instruction.Create(DnOpCodes.Mul));
                    il.Add(Instruction.Create(DnOpCodes.Add));
                    break;
                case 1:
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                    il.Add(Instruction.Create(DnOpCodes.Or));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                    il.Add(Instruction.Create(DnOpCodes.And));
                    il.Add(Instruction.Create(DnOpCodes.Sub));
                    break;
                case 2:
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Not));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                    il.Add(Instruction.Create(DnOpCodes.Not));
                    il.Add(Instruction.Create(DnOpCodes.Add));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
                    il.Add(Instruction.Create(DnOpCodes.Add));
                    il.Add(Instruction.Create(DnOpCodes.Not));
                    break;
                default:
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                    il.Add(Instruction.Create(DnOpCodes.Not));
                    il.Add(Instruction.Create(DnOpCodes.And));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Not));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                    il.Add(Instruction.Create(DnOpCodes.And));
                    il.Add(Instruction.Create(DnOpCodes.Or));
                    break;
            }

            il.Add(Instruction.Create(DnOpCodes.Ret));
            return method;
        }

        private MethodDef BuildFakeDecoder(ModuleDef module)
        {
            var method = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Int32,
                    module.CorLibTypes.Int32, module.CorLibTypes.Int32),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            method.Body = new CilBody();
            var il = method.Body.Instructions;
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Ret));
            return method;
        }

        private MethodDefUser BuildTableInitializer(ModuleDef module)
        {
            var importer = new Importer(module);
            ITypeDefOrRef sysValueType = importer.Import(typeof(ValueType));
            IMethod rhInitArr = importer.Import(typeof(RuntimeHelpers)
                .GetMethod("InitializeArray",
                    new Type[] { typeof(Array), typeof(RuntimeFieldHandle) }));

            var method = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Void),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            method.Body = new CilBody();
            method.Body.InitLocals = true;
            var il = method.Body.Instructions;

            int msk1 = rng.Next(int.MinValue, int.MaxValue);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, masterSeedValue ^ msk1));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, msk1));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stsfld, masterSeed));

            int msk2 = rng.Next(int.MinValue, int.MaxValue);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, tableScrambleValue ^ msk2));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, msk2));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stsfld, tableScrambleField));

            for (int c = 0; c < CHAIN_FIELD_COUNT; c++)
            {
                int v = chainFieldValues[c];
                int k1 = rng.Next(int.MinValue, int.MaxValue);
                int k2 = v ^ k1;
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, k1));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, k2));
                il.Add(Instruction.Create(DnOpCodes.Xor));
                il.Add(Instruction.Create(DnOpCodes.Stsfld, chainFields[c]));
            }

            for (int t = 0; t < TABLE_COUNT; t++)
            {
                int seed = rng.Next(1, int.MaxValue);
                int[] masked = MaskInt32Array(tableData[t], seed);
                byte[] maskedBytes = Int32ArrayToLittleEndianBytes(masked);
                FieldDef rvaField = MakeRvaField(module, containerType, sysValueType, maskedBytes);

                var varArr = new Local(new SZArraySig(module.CorLibTypes.Int32));
                var varIdx = new Local(module.CorLibTypes.Int32);
                var varState = new Local(module.CorLibTypes.Int32);
                method.Body.Variables.Add(varArr);
                method.Body.Variables.Add(varIdx);
                method.Body.Variables.Add(varState);

                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, TABLE_SIZE));
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
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, TABLE_SIZE));
                il.Add(Instruction.Create(DnOpCodes.Blt, loopBody));

                il.Add(Instruction.Create(DnOpCodes.Ldloc, varArr));
                il.Add(Instruction.Create(DnOpCodes.Stsfld, constTables[t]));
            }

            il.Add(Instruction.Create(DnOpCodes.Ret));
            return method;
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
