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
    internal class ArrayEncryptionProtection
    {
        private Obfuscation engine;
        private Random rng;

        private TypeDef hostType;
        private FieldDef splitHiField;
        private FieldDef splitLoField;
        private int splitHiValue;
        private int splitLoValue;
        private List<MethodDef> decryptVariants;
        private const int VariantCount = 6;

        private IMethod initArrayRef;
        private ITypeDefOrRef sysByteRef;

        internal ArrayEncryptionProtection(Obfuscation eng)
        {
            engine = eng;
            rng = eng.rng;
        }

        internal void ApplyArrayEncryption(ModuleDef module, TypeDef modType)
        {
            var importer = new Importer(module);
            initArrayRef = importer.Import(
                typeof(System.Runtime.CompilerServices.RuntimeHelpers)
                    .GetMethod("InitializeArray",
                        new Type[] { typeof(Array), typeof(RuntimeFieldHandle) }));
            sysByteRef = importer.Import(typeof(byte));

            splitHiValue = rng.Next(1, int.MaxValue / 2);
            splitLoValue = rng.Next(1, int.MaxValue / 2);

            hostType = new TypeDefUser("", engine.MakeName(),
                module.CorLibTypes.Object.TypeDefOrRef);
            hostType.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
            module.Types.Add(hostType);
            engine.injectedTypes.Add(hostType);

            splitHiField = new FieldDefUser(engine.MakeName(),
                new FieldSig(module.CorLibTypes.Int32),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            hostType.Fields.Add(splitHiField);

            splitLoField = new FieldDefUser(engine.MakeName(),
                new FieldSig(module.CorLibTypes.Int32),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            hostType.Fields.Add(splitLoField);

            for (int p = 0; p < rng.Next(3, 7); p++)
            {
                hostType.Fields.Add(new FieldDefUser(engine.MakeName(),
                    new FieldSig(module.CorLibTypes.Int32),
                    DnFieldAttributes.Private | DnFieldAttributes.Static));
            }

            decryptVariants = new List<MethodDef>();
            for (int v = 0; v < VariantCount; v++)
            {
                var dm = BuildDecryptVariant(module, v);
                hostType.Methods.Add(dm);
                engine.injectedMethods.Add(dm);
                decryptVariants.Add(dm);
            }

            for (int f = 0; f < rng.Next(6, 12); f++)
            {
                var fake = BuildFakeDecryptMethod(module);
                hostType.Methods.Add(fake);
                engine.injectedMethods.Add(fake);
            }

            var cctor = new MethodDefUser(".cctor",
                MethodSig.CreateStatic(module.CorLibTypes.Void),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Private | DnMethodAttributes.Static |
                DnMethodAttributes.HideBySig | DnMethodAttributes.SpecialName |
                DnMethodAttributes.RTSpecialName);
            cctor.Body = new CilBody();
            var cil = cctor.Body.Instructions;

            int hiMask = rng.Next(int.MinValue, int.MaxValue);
            cil.Add(Instruction.Create(DnOpCodes.Ldc_I4, splitHiValue ^ hiMask));
            cil.Add(Instruction.Create(DnOpCodes.Ldc_I4, hiMask));
            cil.Add(Instruction.Create(DnOpCodes.Xor));
            cil.Add(Instruction.Create(DnOpCodes.Stsfld, splitHiField));

            int loMask = rng.Next(int.MinValue, int.MaxValue);
            cil.Add(Instruction.Create(DnOpCodes.Ldc_I4, splitLoValue ^ loMask));
            cil.Add(Instruction.Create(DnOpCodes.Ldc_I4, loMask));
            cil.Add(Instruction.Create(DnOpCodes.Xor));
            cil.Add(Instruction.Create(DnOpCodes.Stsfld, splitLoField));

            cil.Add(Instruction.Create(DnOpCodes.Ret));
            hostType.Methods.Add(cctor);
            engine.injectedMethods.Add(cctor);

            foreach (TypeDef type in module.GetTypes())
            {
                if (engine.IsCompilerGenerated(type)) continue;
                foreach (MethodDef method in type.Methods)
                {
                    if (!method.HasBody || !method.Body.HasInstructions) continue;
                    if (engine.injectedMethods.Contains(method)) continue;
                    try
                    {
                        TransformMethod(module, method);
                        method.Body.SimplifyBranches();
                        method.Body.OptimizeBranches();
                    }
                    catch { }
                }
            }
        }

        private void TransformMethod(ModuleDef module, MethodDef method)
        {
            var il = method.Body.Instructions;

            for (int i = 0; i + 3 < il.Count; i++)
            {
                if (il[i].OpCode.Code != Code.Newarr) continue;
                if (il[i + 1].OpCode.Code != Code.Dup) continue;
                if (il[i + 2].OpCode.Code != Code.Ldtoken) continue;
                if (il[i + 3].OpCode.Code != Code.Call) continue;

                var rvaField = il[i + 2].Operand as FieldDef;
                if (rvaField == null || !rvaField.HasFieldRVA) continue;
                if (rvaField.InitialValue == null || rvaField.InitialValue.Length == 0) continue;

                var callTarget = il[i + 3].Operand as IMethod;
                if (callTarget == null || !IsInitializeArray(callTarget)) continue;

                var elementTypeRef = il[i].Operand as ITypeDefOrRef;
                if (elementTypeRef == null) continue;

                if (!IsByteArray(elementTypeRef) && !IsRawElementArray(elementTypeRef))
                    continue;

                byte[] original = (byte[])rvaField.InitialValue.Clone();
                int arrayLen = original.Length;

                int perArraySalt = rng.Next(1, int.MaxValue);
                int baseKey = splitHiValue ^ splitLoValue;
                int fullKey = baseKey ^ perArraySalt;

                byte[] encrypted = XorBytes(original, fullKey);
                rvaField.InitialValue = encrypted;

                int encodedSalt = perArraySalt ^ splitLoValue;

                int variantIdx = rng.Next(0, VariantCount);
                var decryptMethod = decryptVariants[variantIdx];

                var replacement = new List<Instruction>();

                if (IsByteArray(elementTypeRef))
                {
                    replacement.Add(Instruction.Create(DnOpCodes.Newarr, sysByteRef));
                    replacement.Add(Instruction.Create(DnOpCodes.Dup));
                    replacement.Add(Instruction.Create(DnOpCodes.Ldtoken, rvaField));
                    replacement.Add(Instruction.Create(DnOpCodes.Call, initArrayRef));
                    replacement.Add(Instruction.Create(DnOpCodes.Ldsfld, splitHiField));
                    replacement.Add(Instruction.Create(DnOpCodes.Ldsfld, splitLoField));
                    replacement.Add(Instruction.Create(DnOpCodes.Ldc_I4, encodedSalt));
                    replacement.Add(Instruction.Create(DnOpCodes.Call, decryptMethod));
                }
                else
                {
                    int elemSize = GetElementSize(elementTypeRef);
                    if (elemSize <= 0) continue;
                    if (arrayLen % elemSize != 0) continue;
                    int elemCount = arrayLen / elemSize;

                    var importer = new Importer(module);
                    IMethod bufferBlockCopy = importer.Import(
                        typeof(Buffer).GetMethod("BlockCopy",
                            new Type[] { typeof(Array), typeof(int), typeof(Array), typeof(int), typeof(int) }));

                    var dstLocal = new Local(new SZArraySig(elementTypeRef.ToTypeSig()));
                    method.Body.Variables.Add(dstLocal);
                    var srcLocal = new Local(new SZArraySig(module.CorLibTypes.Byte));
                    method.Body.Variables.Add(srcLocal);

                    replacement.Add(Instruction.Create(DnOpCodes.Pop));
                    replacement.Add(engine.LoadInt(arrayLen));
                    replacement.Add(Instruction.Create(DnOpCodes.Newarr, sysByteRef));
                    replacement.Add(Instruction.Create(DnOpCodes.Dup));
                    replacement.Add(Instruction.Create(DnOpCodes.Ldtoken, rvaField));
                    replacement.Add(Instruction.Create(DnOpCodes.Call, initArrayRef));
                    replacement.Add(Instruction.Create(DnOpCodes.Ldsfld, splitHiField));
                    replacement.Add(Instruction.Create(DnOpCodes.Ldsfld, splitLoField));
                    replacement.Add(Instruction.Create(DnOpCodes.Ldc_I4, encodedSalt));
                    replacement.Add(Instruction.Create(DnOpCodes.Call, decryptMethod));
                    replacement.Add(Instruction.Create(DnOpCodes.Stloc, srcLocal));
                    replacement.Add(engine.LoadInt(elemCount));
                    replacement.Add(Instruction.Create(DnOpCodes.Newarr, elementTypeRef));
                    replacement.Add(Instruction.Create(DnOpCodes.Stloc, dstLocal));
                    replacement.Add(Instruction.Create(DnOpCodes.Ldloc, srcLocal));
                    replacement.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
                    replacement.Add(Instruction.Create(DnOpCodes.Ldloc, dstLocal));
                    replacement.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
                    replacement.Add(engine.LoadInt(arrayLen));
                    replacement.Add(Instruction.Create(DnOpCodes.Call, bufferBlockCopy));
                    replacement.Add(Instruction.Create(DnOpCodes.Ldloc, dstLocal));
                }

                il[i].OpCode = replacement[0].OpCode;
                il[i].Operand = replacement[0].Operand;

                for (int j = 1; j < replacement.Count; j++)
                    il.Insert(i + j, replacement[j]);

                int insertedExtra = replacement.Count - 1;
                int dupPos = i + 1 + insertedExtra;
                int ldtokenPos = dupPos + 1;
                int callPos = ldtokenPos + 1;

                if (dupPos < il.Count && il[dupPos].OpCode.Code == Code.Dup &&
                    ldtokenPos < il.Count && il[ldtokenPos].OpCode.Code == Code.Ldtoken &&
                    callPos < il.Count && il[callPos].OpCode.Code == Code.Call)
                {
                    il.RemoveAt(callPos);
                    il.RemoveAt(ldtokenPos);
                    il.RemoveAt(dupPos);
                }

                i += replacement.Count - 1;
            }
        }

        private bool IsInitializeArray(IMethod m)
        {
            if (m == null || m.Name != "InitializeArray") return false;
            var dt = m.DeclaringType;
            return dt != null && dt.FullName == "System.Runtime.CompilerServices.RuntimeHelpers";
        }

        private bool IsByteArray(ITypeDefOrRef t)
        {
            if (t == null) return false;
            return t.FullName == "System.Byte";
        }

        private bool IsRawElementArray(ITypeDefOrRef t)
        {
            if (t == null) return false;
            string fn = t.FullName;
            return fn == "System.SByte" || fn == "System.Int16" || fn == "System.UInt16" ||
                   fn == "System.Int32" || fn == "System.UInt32" || fn == "System.Int64" ||
                   fn == "System.UInt64" || fn == "System.Char" ||
                   fn == "System.Single" || fn == "System.Double";
        }

        private int GetElementSize(ITypeDefOrRef t)
        {
            if (t == null) return 0;
            switch (t.FullName)
            {
                case "System.SByte":   return 1;
                case "System.Int16":   return 2;
                case "System.UInt16":  return 2;
                case "System.Char":    return 2;
                case "System.Int32":   return 4;
                case "System.UInt32":  return 4;
                case "System.Single":  return 4;
                case "System.Int64":   return 8;
                case "System.UInt64":  return 8;
                case "System.Double":  return 8;
                default:               return 0;
            }
        }

        private byte[] XorBytes(byte[] data, int key)
        {
            var result = new byte[data.Length];
            for (int i = 0; i < data.Length; i++)
            {
                int shift = (i % 4) * 8;
                byte keyByte = (byte)((key >> shift) & 0xFF);
                result[i] = (byte)(data[i] ^ keyByte);
            }
            return result;
        }

        private MethodDef BuildDecryptVariant(ModuleDef module, int variant)
        {
            var arrTypeSig = new SZArraySig(module.CorLibTypes.Byte);

            var method = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(
                    arrTypeSig,
                    arrTypeSig,
                    module.CorLibTypes.Int32,
                    module.CorLibTypes.Int32,
                    module.CorLibTypes.Int32),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static |
                DnMethodAttributes.HideBySig);

            method.Body = new CilBody();
            method.Body.InitLocals = true;
            var L = method.Body.Variables;
            L.Add(new Local(module.CorLibTypes.Int32));
            L.Add(new Local(module.CorLibTypes.Int32));
            L.Add(new Local(module.CorLibTypes.Int32));
            L.Add(new Local(module.CorLibTypes.Int32));
            var il = method.Body.Instructions;

            EmitKeyDerive(il, variant);

            var loopCheck = Instruction.Create(DnOpCodes.Ldc_I4_0);
            var afterLoop = Instruction.Create(DnOpCodes.Ldarg_0);

            il.Add(loopCheck);
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));

            var checkLabel = Instruction.Create(DnOpCodes.Ldloc_1);
            il.Add(checkLabel);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Bge, afterLoop));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_4));
            il.Add(Instruction.Create(DnOpCodes.Rem));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_8));
            il.Add(Instruction.Create(DnOpCodes.Mul));
            il.Add(Instruction.Create(DnOpCodes.Stloc_2));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_2));
            il.Add(Instruction.Create(DnOpCodes.Shr_Un));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 0xFF));
            il.Add(Instruction.Create(DnOpCodes.And));
            il.Add(Instruction.Create(DnOpCodes.Stloc_3));

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_3));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Conv_U1));
            il.Add(Instruction.Create(DnOpCodes.Stelem_I1));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));
            il.Add(Instruction.Create(DnOpCodes.Br, checkLabel));

            il.Add(afterLoop);
            il.Add(Instruction.Create(DnOpCodes.Ret));

            return method;
        }

        private void EmitKeyDerive(IList<Instruction> il, int variant)
        {
            switch (variant % 6)
            {
                case 0:
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_3));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                    break;
                case 1:
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_3));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                    break;
                case 2:
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_2));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_3));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_2));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                    break;
                case 3:
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_2));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_3));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_2));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                    break;
                case 4:
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_3));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_2));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_2));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                    break;
                default:
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_3));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_2));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_2));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                    break;
            }
        }

        private MethodDef BuildFakeDecryptMethod(ModuleDef module)
        {
            var arrTypeSig = new SZArraySig(module.CorLibTypes.Byte);
            var method = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(
                    arrTypeSig,
                    arrTypeSig,
                    module.CorLibTypes.Int32),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static |
                DnMethodAttributes.HideBySig);

            method.Body = new CilBody();
            method.Body.InitLocals = true;
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            var il = method.Body.Instructions;

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            var loopCheck = Instruction.Create(DnOpCodes.Ldloc_0);
            var afterLoop = Instruction.Create(DnOpCodes.Ldarg_0);
            il.Add(loopCheck);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Bge, afterLoop));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Conv_U1));
            il.Add(Instruction.Create(DnOpCodes.Stelem_I1));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Br, loopCheck));
            il.Add(afterLoop);
            il.Add(Instruction.Create(DnOpCodes.Ret));

            return method;
        }
    }
}
