using System;
using System.Collections.Generic;
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
    internal sealed class IntegrityStampProtection
    {
        internal const int StampLen = 32;
        internal const int InlineLen = 8;
        internal const int TotalStamp = InlineLen + StampLen;
        private const ulong FnvOffset = 14695981039346656037UL;
        private const ulong FnvPrime  = 1099511628211UL;

        private readonly Obfuscation engine;
        private readonly Random rng;

        internal IntegrityStampProtection(Obfuscation eng)
        {
            engine = eng;
            rng = eng.rng;
        }

        internal byte[] Apply(ModuleDef module, TypeDef modType)
        {
            try
            {
                byte[] key = engine.CryptoRandom(32);

                var hostType = new TypeDefUser("", engine.MakeName(),
                    module.CorLibTypes.Object.TypeDefOrRef);
                hostType.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                    DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
                module.Types.Add(hostType);
                engine.injectedTypes.Add(hostType);

                MethodDef cctor = new MethodDefUser(".cctor",
                    MethodSig.CreateStatic(module.CorLibTypes.Void),
                    DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                    DnMethodAttributes.Private | DnMethodAttributes.Static |
                    DnMethodAttributes.HideBySig | DnMethodAttributes.SpecialName |
                    DnMethodAttributes.RTSpecialName);
                cctor.Body = new CilBody();
                cctor.Body.InitLocals = true;
                FieldDef keyField = EmitRvaArrayField(module, hostType, cctor, cctor.Body.Instructions, key);
                cctor.Body.Instructions.Add(Instruction.Create(DnOpCodes.Ret));
                hostType.Methods.Add(cctor);
                engine.injectedMethods.Add(cctor);

                NativeShroud shroud = engine.EnsureShroud(module);

                var bombs = BuildBombPool(module, hostType);
                foreach (var b in bombs)
                {
                    hostType.Methods.Add(b);
                    engine.injectedMethods.Add(b);
                }

                var delegateBombs = new List<MethodDef> { bombs[5], bombs[6] };

                int verifierCount = 3;
                for (int i = 0; i < verifierCount; i++)
                {
                    var bomb = delegateBombs[i % delegateBombs.Count];
                    MethodDef v = BuildVerifier(module, hostType, keyField, shroud, bomb);
                    hostType.Methods.Add(v);
                    engine.injectedMethods.Add(v);
                    engine.InjectCallInCctor(module, modType, v);
                    engine.InjectCallInRandomMethods(module, v, 4, 10);
                }

                int inlineCount = 3;
                for (int i = 0; i < inlineCount; i++)
                {
                    var bomb = delegateBombs[(inlineCount - 1 - i) % delegateBombs.Count];
                    MethodDef v = BuildInlineVerifier(module, hostType, shroud, bomb);
                    hostType.Methods.Add(v);
                    engine.injectedMethods.Add(v);
                    engine.InjectCallInCctor(module, modType, v);
                    engine.InjectCallInRandomMethods(module, v, 4, 10);
                }

                return key;
            }
            catch
            {
                return null;
            }
        }

        private static uint MvidToSeed(Guid mvid)
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

        private static byte[] MaskKeyBytes(byte[] plain, uint seed)
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

        private FieldDef EmitRvaArrayField(ModuleDef module, TypeDef owner,
            MethodDef cctor, System.Collections.Generic.IList<Instruction> cctorIl, byte[] bytes)
        {
            Importer importer = new Importer(module);
            ITypeDefOrRef sysValueType = importer.Import(typeof(ValueType));
            ITypeDefOrRef sysByte = importer.Import(typeof(byte));
            IMethod rhInitArr = importer.Import(typeof(System.Runtime.CompilerServices.RuntimeHelpers)
                .GetMethod("InitializeArray", new Type[] { typeof(Array), typeof(RuntimeFieldHandle) }));

            IMethod getTypeFromHandle = importer.Import(typeof(Type).GetMethod("GetTypeFromHandle",
                new Type[] { typeof(RuntimeTypeHandle) }));
            IMethod getModule = importer.Import(typeof(Type).GetProperty("Module").GetGetMethod());
            IMethod getMvid = importer.Import(typeof(System.Reflection.Module)
                .GetProperty("ModuleVersionId").GetGetMethod());
            IMethod toByteArr = importer.Import(typeof(Guid).GetMethod("ToByteArray", Type.EmptyTypes));

            uint mvidSeed = MvidToSeed(module.Mvid ?? Guid.Empty);
            byte[] maskedBytes = MaskKeyBytes(bytes, mvidSeed);

            TypeDef holder = new TypeDefUser("", engine.MakeName(), sysValueType);
            holder.Attributes = DnTypeAttributes.NestedPrivate
                              | DnTypeAttributes.SequentialLayout
                              | DnTypeAttributes.Sealed;
            holder.ClassLayout = new ClassLayoutUser(1, (uint)maskedBytes.Length);
            owner.NestedTypes.Add(holder);
            engine.injectedTypes.Add(holder);

            FieldDef rvaField = new FieldDefUser(engine.MakeName(),
                new FieldSig(holder.ToTypeSig()),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static
                | DnFieldAttributes.HasFieldRVA);
            rvaField.HasFieldRVA = true;
            rvaField.InitialValue = maskedBytes;
            owner.Fields.Add(rvaField);

            FieldDef arrField = new FieldDefUser(engine.MakeName(),
                new FieldSig(new SZArraySig(module.CorLibTypes.Byte)),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            owner.Fields.Add(arrField);

            var varArr    = new Local(new SZArraySig(module.CorLibTypes.Byte));
            var varIdx    = new Local(module.CorLibTypes.Int32);
            var varGuid   = new Local(importer.ImportAsTypeSig(typeof(Guid)));
            var varMvidB  = new Local(new SZArraySig(module.CorLibTypes.Byte));
            var varH      = new Local(module.CorLibTypes.UInt32);
            var varChunk  = new Local(module.CorLibTypes.UInt32);
            var varJ      = new Local(module.CorLibTypes.Int32);
            var varState  = new Local(module.CorLibTypes.UInt32);

            cctor.Body.Variables.Add(varArr);
            cctor.Body.Variables.Add(varIdx);
            cctor.Body.Variables.Add(varGuid);
            cctor.Body.Variables.Add(varMvidB);
            cctor.Body.Variables.Add(varH);
            cctor.Body.Variables.Add(varChunk);
            cctor.Body.Variables.Add(varJ);
            cctor.Body.Variables.Add(varState);

            cctorIl.Add(engine.LoadInt(maskedBytes.Length));
            cctorIl.Add(Instruction.Create(DnOpCodes.Newarr, sysByte));
            cctorIl.Add(Instruction.Create(DnOpCodes.Dup));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldtoken, rvaField));
            cctorIl.Add(Instruction.Create(DnOpCodes.Call, rhInitArr));
            cctorIl.Add(Instruction.Create(DnOpCodes.Stloc, varArr));

            cctorIl.Add(Instruction.Create(DnOpCodes.Ldtoken, (ITypeDefOrRef)owner));
            cctorIl.Add(Instruction.Create(DnOpCodes.Call, getTypeFromHandle));
            cctorIl.Add(Instruction.Create(DnOpCodes.Callvirt, getModule));
            cctorIl.Add(Instruction.Create(DnOpCodes.Callvirt, getMvid));
            cctorIl.Add(Instruction.Create(DnOpCodes.Stloc, varGuid));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloca, varGuid));
            cctorIl.Add(Instruction.Create(DnOpCodes.Call, toByteArr));
            cctorIl.Add(Instruction.Create(DnOpCodes.Stloc, varMvidB));

            cctorIl.Add(Instruction.Create(DnOpCodes.Ldc_I4, unchecked((int)0x9E3779B9u)));
            cctorIl.Add(Instruction.Create(DnOpCodes.Stloc, varH));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            cctorIl.Add(Instruction.Create(DnOpCodes.Stloc, varJ));

            var mixCond = Instruction.Create(DnOpCodes.Ldloc, varJ);
            var mixBody = Instruction.Create(DnOpCodes.Ldloc, varMvidB);
            cctorIl.Add(Instruction.Create(DnOpCodes.Br, mixCond));
            cctorIl.Add(mixBody);
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varJ));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varMvidB));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varJ));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            cctorIl.Add(Instruction.Create(DnOpCodes.Add));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldc_I4_8));
            cctorIl.Add(Instruction.Create(DnOpCodes.Shl));
            cctorIl.Add(Instruction.Create(DnOpCodes.Or));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varMvidB));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varJ));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldc_I4_2));
            cctorIl.Add(Instruction.Create(DnOpCodes.Add));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldc_I4, 16));
            cctorIl.Add(Instruction.Create(DnOpCodes.Shl));
            cctorIl.Add(Instruction.Create(DnOpCodes.Or));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varMvidB));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varJ));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldc_I4_3));
            cctorIl.Add(Instruction.Create(DnOpCodes.Add));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldc_I4, 24));
            cctorIl.Add(Instruction.Create(DnOpCodes.Shl));
            cctorIl.Add(Instruction.Create(DnOpCodes.Or));
            cctorIl.Add(Instruction.Create(DnOpCodes.Stloc, varChunk));

            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varChunk));
            cctorIl.Add(Instruction.Create(DnOpCodes.Xor));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldc_I4, unchecked((int)0x85EBCA6Bu)));
            cctorIl.Add(Instruction.Create(DnOpCodes.Mul));
            cctorIl.Add(Instruction.Create(DnOpCodes.Stloc, varH));

            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldc_I4, 13));
            cctorIl.Add(Instruction.Create(DnOpCodes.Shl));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldc_I4, 19));
            cctorIl.Add(Instruction.Create(DnOpCodes.Shr_Un));
            cctorIl.Add(Instruction.Create(DnOpCodes.Or));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldc_I4, unchecked((int)0xC2B2AE35u)));
            cctorIl.Add(Instruction.Create(DnOpCodes.Mul));
            cctorIl.Add(Instruction.Create(DnOpCodes.Stloc, varH));

            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varJ));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldc_I4_4));
            cctorIl.Add(Instruction.Create(DnOpCodes.Add));
            cctorIl.Add(Instruction.Create(DnOpCodes.Stloc, varJ));

            cctorIl.Add(mixCond);
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldc_I4, 16));
            cctorIl.Add(Instruction.Create(DnOpCodes.Blt, mixBody));

            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldc_I4, 16));
            cctorIl.Add(Instruction.Create(DnOpCodes.Shr_Un));
            cctorIl.Add(Instruction.Create(DnOpCodes.Xor));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldc_I4, unchecked((int)0x85EBCA6Bu)));
            cctorIl.Add(Instruction.Create(DnOpCodes.Mul));
            cctorIl.Add(Instruction.Create(DnOpCodes.Stloc, varH));

            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldc_I4, 13));
            cctorIl.Add(Instruction.Create(DnOpCodes.Shr_Un));
            cctorIl.Add(Instruction.Create(DnOpCodes.Xor));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldc_I4, unchecked((int)0xC2B2AE35u)));
            cctorIl.Add(Instruction.Create(DnOpCodes.Mul));
            cctorIl.Add(Instruction.Create(DnOpCodes.Stloc, varH));

            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldc_I4, 16));
            cctorIl.Add(Instruction.Create(DnOpCodes.Shr_Un));
            cctorIl.Add(Instruction.Create(DnOpCodes.Xor));
            cctorIl.Add(Instruction.Create(DnOpCodes.Stloc, varH));

            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            cctorIl.Add(Instruction.Create(DnOpCodes.Or));
            cctorIl.Add(Instruction.Create(DnOpCodes.Stloc, varState));

            cctorIl.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            cctorIl.Add(Instruction.Create(DnOpCodes.Stloc, varIdx));

            var loopCond = Instruction.Create(DnOpCodes.Ldloc, varIdx);
            var loopBody = Instruction.Create(DnOpCodes.Nop);
            cctorIl.Add(Instruction.Create(DnOpCodes.Br, loopCond));

            cctorIl.Add(loopBody);

            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varState));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varState));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldc_I4, 13));
            cctorIl.Add(Instruction.Create(DnOpCodes.Shl));
            cctorIl.Add(Instruction.Create(DnOpCodes.Xor));
            cctorIl.Add(Instruction.Create(DnOpCodes.Stloc, varState));

            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varState));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varState));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldc_I4, 17));
            cctorIl.Add(Instruction.Create(DnOpCodes.Shr_Un));
            cctorIl.Add(Instruction.Create(DnOpCodes.Xor));
            cctorIl.Add(Instruction.Create(DnOpCodes.Stloc, varState));

            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varState));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varState));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldc_I4_5));
            cctorIl.Add(Instruction.Create(DnOpCodes.Shl));
            cctorIl.Add(Instruction.Create(DnOpCodes.Xor));
            cctorIl.Add(Instruction.Create(DnOpCodes.Stloc, varState));

            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varArr));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varIdx));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varArr));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varIdx));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varState));
            cctorIl.Add(Instruction.Create(DnOpCodes.Conv_U1));
            cctorIl.Add(Instruction.Create(DnOpCodes.Xor));
            cctorIl.Add(Instruction.Create(DnOpCodes.Conv_U1));
            cctorIl.Add(Instruction.Create(DnOpCodes.Stelem_I1));

            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varIdx));
            cctorIl.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            cctorIl.Add(Instruction.Create(DnOpCodes.Add));
            cctorIl.Add(Instruction.Create(DnOpCodes.Stloc, varIdx));

            cctorIl.Add(loopCond);
            cctorIl.Add(engine.LoadInt(maskedBytes.Length));
            cctorIl.Add(Instruction.Create(DnOpCodes.Blt, loopBody));

            cctorIl.Add(Instruction.Create(DnOpCodes.Ldloc, varArr));
            cctorIl.Add(Instruction.Create(DnOpCodes.Stsfld, arrField));
            return arrField;
        }

        private List<MethodDef> BuildBombPool(ModuleDef module, TypeDef owner)
        {
            var pool = new List<MethodDef>();

            var v1Pair = BuildV1MutualPair(module, owner);
            pool.Add(v1Pair[0]);
            pool.Add(v1Pair[1]);

            pool.Add(BuildV1MutualPair2(module, owner, pool));

            pool.Add(BuildV2ParamRecurse(module, owner, rng.Next(3, 7), rng.Next(11, 99)));
            pool.Add(BuildV2ParamRecurse(module, owner, rng.Next(2, 5), rng.Next(101, 251)));

            pool.Add(BuildV4ReflectSelf(module, owner, rng.Next(3, 17)));
            pool.Add(BuildV5CatchInvoke(module, owner, rng.Next(19, 53)));

            return pool;
        }

        private MethodDef[] BuildV1MutualPair(ModuleDef module, TypeDef owner)
        {
            var a = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Void),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            var b = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Void),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            a.Body = new CilBody();
            a.Body.Instructions.Add(Instruction.Create(DnOpCodes.Call, b));
            a.Body.Instructions.Add(Instruction.Create(DnOpCodes.Ret));

            b.Body = new CilBody();
            b.Body.Instructions.Add(Instruction.Create(DnOpCodes.Call, a));
            b.Body.Instructions.Add(Instruction.Create(DnOpCodes.Ret));

            return new[] { a, b };
        }

        private MethodDef BuildV1MutualPair2(ModuleDef module, TypeDef owner, List<MethodDef> existing)
        {
            var c = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Void),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            var d = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Void),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            c.Body = new CilBody();
            c.Body.Instructions.Add(Instruction.Create(DnOpCodes.Call, d));
            c.Body.Instructions.Add(Instruction.Create(DnOpCodes.Ret));

            d.Body = new CilBody();
            d.Body.Instructions.Add(Instruction.Create(DnOpCodes.Call, existing[0]));
            d.Body.Instructions.Add(Instruction.Create(DnOpCodes.Call, c));
            d.Body.Instructions.Add(Instruction.Create(DnOpCodes.Ret));

            owner.Methods.Add(d);
            engine.injectedMethods.Add(d);

            return c;
        }

        private MethodDef BuildV2ParamRecurse(ModuleDef module, TypeDef owner, int fillerA, int fillerB)
        {
            var m = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Void, module.CorLibTypes.Int32),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            m.Body = new CilBody();
            var il = m.Body.Instructions;

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, fillerA));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, fillerB));
            il.Add(Instruction.Create(DnOpCodes.Mul));
            il.Add(Instruction.Create(DnOpCodes.Call, m));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            return m;
        }

        private MethodDef BuildV4ReflectSelf(ModuleDef module, TypeDef owner, int fillerConst)
        {
            ITypeDefOrRef actionRef = module.Import(typeof(Action));
            var actionSig = new ClassSig(actionRef);

            var field = new FieldDefUser(engine.MakeName(),
                new FieldSig(actionSig),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            owner.Fields.Add(field);

            var m = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Void),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            m.Body = new CilBody();
            m.Body.InitLocals = true;
            m.Body.Variables.Add(new Local(module.Import(typeof(System.Reflection.MethodInfo)).ToTypeSig()));
            var il = m.Body.Instructions;

            var getCurrentMethod = module.Import(
                typeof(System.Reflection.MethodBase).GetMethod("GetCurrentMethod", Type.EmptyTypes));
            var createDelegate = module.Import(
                typeof(System.Delegate).GetMethod("CreateDelegate",
                    new[] { typeof(Type), typeof(System.Reflection.MethodInfo) }));
            var getTypeFromHandle = module.Import(
                typeof(Type).GetMethod("GetTypeFromHandle", new[] { typeof(RuntimeTypeHandle) }));
            var invokeMethod = module.Import(typeof(Action).GetMethod("Invoke", Type.EmptyTypes));
            var typeofAction = module.Import(typeof(Action));

            var skipInit = Instruction.Create(DnOpCodes.Ldsfld, field);

            il.Add(Instruction.Create(DnOpCodes.Ldsfld, field));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, skipInit));

            il.Add(Instruction.Create(DnOpCodes.Call, getCurrentMethod));
            il.Add(Instruction.Create(DnOpCodes.Castclass, module.Import(typeof(System.Reflection.MethodInfo))));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldtoken, typeofAction));
            il.Add(Instruction.Create(DnOpCodes.Call, getTypeFromHandle));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Call, createDelegate));
            il.Add(Instruction.Create(DnOpCodes.Castclass, module.Import(typeof(Action))));
            il.Add(Instruction.Create(DnOpCodes.Stsfld, field));

            il.Add(skipInit);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, fillerConst));
            il.Add(Instruction.Create(DnOpCodes.Pop));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, invokeMethod));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            return m;
        }

        private MethodDef BuildV5CatchInvoke(ModuleDef module, TypeDef owner, int fillerConst)
        {
            ITypeDefOrRef actionRef = module.Import(typeof(Action));
            var actionSig = new ClassSig(actionRef);

            var field = new FieldDefUser(engine.MakeName(),
                new FieldSig(actionSig),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            owner.Fields.Add(field);

            var m = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Void,
                    module.CorLibTypes.Object,
                    module.CorLibTypes.Object,
                    module.CorLibTypes.Object),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            m.Body = new CilBody();
            m.Body.InitLocals = true;
            m.Body.Variables.Add(new Local(module.Import(typeof(System.Reflection.MethodInfo)).ToTypeSig()));
            var il = m.Body.Instructions;

            var getCurrentMethod = module.Import(
                typeof(System.Reflection.MethodBase).GetMethod("GetCurrentMethod", Type.EmptyTypes));
            var createDelegate = module.Import(
                typeof(System.Delegate).GetMethod("CreateDelegate",
                    new[] { typeof(Type), typeof(System.Reflection.MethodInfo) }));
            var getTypeFromHandle = module.Import(
                typeof(Type).GetMethod("GetTypeFromHandle", new[] { typeof(RuntimeTypeHandle) }));
            var invokeMethod = module.Import(typeof(Action).GetMethod("Invoke", Type.EmptyTypes));
            var typeofAction = module.Import(typeof(Action));

            var retInstr = Instruction.Create(DnOpCodes.Ret);
            var skipInit = Instruction.Create(DnOpCodes.Ldsfld, field);

            var tryStart = Instruction.Create(DnOpCodes.Ldsfld, field);
            il.Add(tryStart);
            il.Add(Instruction.Create(DnOpCodes.Brtrue, skipInit));

            il.Add(Instruction.Create(DnOpCodes.Call, getCurrentMethod));
            il.Add(Instruction.Create(DnOpCodes.Castclass, module.Import(typeof(System.Reflection.MethodInfo))));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldtoken, typeofAction));
            il.Add(Instruction.Create(DnOpCodes.Call, getTypeFromHandle));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Call, createDelegate));
            il.Add(Instruction.Create(DnOpCodes.Castclass, module.Import(typeof(Action))));
            il.Add(Instruction.Create(DnOpCodes.Stsfld, field));

            il.Add(skipInit);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, fillerConst));
            il.Add(Instruction.Create(DnOpCodes.Pop));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Pop));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Pop));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_2));
            il.Add(Instruction.Create(DnOpCodes.Pop));
            var leaveOk = Instruction.Create(DnOpCodes.Leave, retInstr);
            il.Add(Instruction.Create(DnOpCodes.Callvirt, invokeMethod));
            il.Add(leaveOk);

            var catchStart = Instruction.Create(DnOpCodes.Pop);
            il.Add(catchStart);
            il.Add(Instruction.Create(DnOpCodes.Ldsfld, field));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, invokeMethod));
            il.Add(Instruction.Create(DnOpCodes.Leave, retInstr));

            il.Add(retInstr);

            m.Body.ExceptionHandlers.Add(new ExceptionHandler(ExceptionHandlerType.Catch)
            {
                TryStart = tryStart,
                TryEnd = catchStart,
                HandlerStart = catchStart,
                HandlerEnd = retInstr,
                CatchType = module.CorLibTypes.Object.TypeDefOrRef
            });

            return m;
        }

        private MethodDef BuildVerifier(ModuleDef module, TypeDef owner, FieldDef keyField, NativeShroud shroud, MethodDef bomb)
        {
            var method = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Void),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            method.Body = new CilBody();
            method.Body.InitLocals = true;
            var L = method.Body.Variables;
            L.Add(new Local(module.CorLibTypes.String));
            L.Add(new Local(new SZArraySig(module.CorLibTypes.Byte)));
            L.Add(new Local(module.CorLibTypes.Int32));
            L.Add(new Local(new SZArraySig(module.CorLibTypes.Byte)));
            L.Add(new Local(module.Import(typeof(HMACSHA256)).ToTypeSig()));
            L.Add(new Local(module.CorLibTypes.Int32));

            var getExecAsm = module.Import(typeof(System.Reflection.Assembly).GetMethod("GetExecutingAssembly", Type.EmptyTypes));
            var getLocation = module.Import(typeof(System.Reflection.Assembly).GetProperty("Location").GetGetMethod());
            var fileReadAll = module.Import(typeof(System.IO.File).GetMethod("ReadAllBytes", new[] { typeof(string) }));
            var strIsNullOrEmpty = module.Import(typeof(string).GetMethod("IsNullOrEmpty", new[] { typeof(string) }));
            var hmacCtor = module.Import(typeof(HMACSHA256).GetConstructor(new[] { typeof(byte[]) }));
            var computeRange = module.Import(typeof(HashAlgorithm).GetMethod("ComputeHash", new[] { typeof(byte[]), typeof(int), typeof(int) }));
            var dbgIsAttached = module.Import(typeof(System.Diagnostics.Debugger).GetProperty("IsAttached").GetGetMethod());

            var il = method.Body.Instructions;

            var leaveEnd = Instruction.Create(DnOpCodes.Leave, (Instruction)null);
            var retInstr = Instruction.Create(DnOpCodes.Ret);
            var termAt = Instruction.Create(DnOpCodes.Call, shroud.GetCurrentProcess);

            var tryStart = Instruction.Create(DnOpCodes.Call, dbgIsAttached);
            il.Add(tryStart);
            il.Add(Instruction.Create(DnOpCodes.Brtrue, termAt));
            il.Add(Instruction.Create(DnOpCodes.Call, shroud.IsDebuggerPresent));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, termAt));

            il.Add(Instruction.Create(DnOpCodes.Call, getExecAsm));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, getLocation));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Call, strIsNullOrEmpty));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, termAt));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Call, fileReadAll));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, StampLen));
            il.Add(Instruction.Create(DnOpCodes.Sub));
            il.Add(Instruction.Create(DnOpCodes.Stloc_2));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_2));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ble, leaveEnd));

            il.Add(Instruction.Create(DnOpCodes.Ldsfld, keyField));
            il.Add(Instruction.Create(DnOpCodes.Newobj, hmacCtor));
            il.Add(Instruction.Create(DnOpCodes.Stloc_S, L[4]));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_S, L[4]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_2));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, computeRange));
            il.Add(Instruction.Create(DnOpCodes.Stloc_3));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc_S, L[5]));

            var loopCond = Instruction.Create(DnOpCodes.Ldloc_S, L[5]);
            var loopBody = Instruction.Create(DnOpCodes.Ldloc_3);
            il.Add(Instruction.Create(DnOpCodes.Br, loopCond));

            il.Add(loopBody);
            il.Add(Instruction.Create(DnOpCodes.Ldloc_S, L[5]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_2));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_S, L[5]));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            var nextIter = Instruction.Create(DnOpCodes.Ldloc_S, L[5]);
            il.Add(Instruction.Create(DnOpCodes.Beq, nextIter));

            il.Add(termAt);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_M1));
            il.Add(Instruction.Create(DnOpCodes.Call, shroud.TerminateProcess));
            il.Add(Instruction.Create(DnOpCodes.Pop));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_M1));
            il.Add(Instruction.Create(DnOpCodes.Call, shroud.ExitProcess));
            EmitBombCall(il, bomb);

            il.Add(nextIter);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc_S, L[5]));

            il.Add(loopCond);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, StampLen));
            il.Add(Instruction.Create(DnOpCodes.Blt, loopBody));

            leaveEnd.Operand = retInstr;
            il.Add(leaveEnd);

            var catchStart = Instruction.Create(DnOpCodes.Pop);
            il.Add(catchStart);
            il.Add(Instruction.Create(DnOpCodes.Leave, retInstr));

            il.Add(retInstr);

            method.Body.ExceptionHandlers.Add(new ExceptionHandler(ExceptionHandlerType.Catch)
            {
                TryStart = tryStart,
                TryEnd = catchStart,
                HandlerStart = catchStart,
                HandlerEnd = retInstr,
                CatchType = module.CorLibTypes.Object.TypeDefOrRef
            });

            return method;
        }

        private MethodDef BuildInlineVerifier(ModuleDef module, TypeDef owner, NativeShroud shroud, MethodDef bomb)
        {
            var method = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Void),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            method.Body = new CilBody();
            method.Body.InitLocals = true;
            var L = method.Body.Variables;
            L.Add(new Local(module.CorLibTypes.String));
            L.Add(new Local(new SZArraySig(module.CorLibTypes.Byte)));
            L.Add(new Local(module.CorLibTypes.Int32));
            L.Add(new Local(module.CorLibTypes.UInt64));
            L.Add(new Local(module.CorLibTypes.Int32));

            var getExecAsm = module.Import(typeof(System.Reflection.Assembly).GetMethod("GetExecutingAssembly", Type.EmptyTypes));
            var getLocation = module.Import(typeof(System.Reflection.Assembly).GetProperty("Location").GetGetMethod());
            var fileReadAll = module.Import(typeof(System.IO.File).GetMethod("ReadAllBytes", new[] { typeof(string) }));
            var strIsNullOrEmpty = module.Import(typeof(string).GetMethod("IsNullOrEmpty", new[] { typeof(string) }));
            var dbgIsAttached = module.Import(typeof(System.Diagnostics.Debugger).GetProperty("IsAttached").GetGetMethod());

            var il = method.Body.Instructions;
            var leaveEnd = Instruction.Create(DnOpCodes.Leave, (Instruction)null);
            var retInstr = Instruction.Create(DnOpCodes.Ret);
            var termAt = Instruction.Create(DnOpCodes.Call, shroud.GetCurrentProcess);

            var tryStart = Instruction.Create(DnOpCodes.Call, dbgIsAttached);
            il.Add(tryStart);
            il.Add(Instruction.Create(DnOpCodes.Brtrue, termAt));
            il.Add(Instruction.Create(DnOpCodes.Call, shroud.IsDebuggerPresent));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, termAt));

            il.Add(Instruction.Create(DnOpCodes.Call, getExecAsm));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, getLocation));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Call, strIsNullOrEmpty));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, termAt));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Call, fileReadAll));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, TotalStamp));
            il.Add(Instruction.Create(DnOpCodes.Sub));
            il.Add(Instruction.Create(DnOpCodes.Stloc_2));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_2));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ble, leaveEnd));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I8, unchecked((long)FnvOffset)));
            il.Add(Instruction.Create(DnOpCodes.Stloc_3));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc_S, L[4]));

            var hashCond = Instruction.Create(DnOpCodes.Ldloc_S, L[4]);
            var hashBody = Instruction.Create(DnOpCodes.Ldloc_3);
            il.Add(Instruction.Create(DnOpCodes.Br, hashCond));

            il.Add(hashBody);
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_S, L[4]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            il.Add(Instruction.Create(DnOpCodes.Conv_U8));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I8, unchecked((long)FnvPrime)));
            il.Add(Instruction.Create(DnOpCodes.Mul));
            il.Add(Instruction.Create(DnOpCodes.Stloc_3));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_S, L[4]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc_S, L[4]));

            il.Add(hashCond);
            il.Add(Instruction.Create(DnOpCodes.Ldloc_2));
            il.Add(Instruction.Create(DnOpCodes.Blt, hashBody));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc_S, L[4]));
            var cmpCond = Instruction.Create(DnOpCodes.Ldloc_S, L[4]);
            var cmpBody = Instruction.Create(DnOpCodes.Ldloc_3);
            il.Add(Instruction.Create(DnOpCodes.Br, cmpCond));

            il.Add(cmpBody);
            il.Add(Instruction.Create(DnOpCodes.Ldloc_S, L[4]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_8));
            il.Add(Instruction.Create(DnOpCodes.Mul));
            il.Add(Instruction.Create(DnOpCodes.Shr_Un));
            il.Add(Instruction.Create(DnOpCodes.Conv_U1));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_2));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_S, L[4]));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            var cmpNext = Instruction.Create(DnOpCodes.Ldloc_S, L[4]);
            il.Add(Instruction.Create(DnOpCodes.Beq, cmpNext));
            il.Add(Instruction.Create(DnOpCodes.Br, termAt));

            il.Add(cmpNext);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc_S, L[4]));
            il.Add(cmpCond);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, InlineLen));
            il.Add(Instruction.Create(DnOpCodes.Blt, cmpBody));

            il.Add(Instruction.Create(DnOpCodes.Br, leaveEnd));

            il.Add(termAt);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_M1));
            il.Add(Instruction.Create(DnOpCodes.Call, shroud.TerminateProcess));
            il.Add(Instruction.Create(DnOpCodes.Pop));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_M1));
            il.Add(Instruction.Create(DnOpCodes.Call, shroud.ExitProcess));
            EmitBombCall(il, bomb);

            leaveEnd.Operand = retInstr;
            il.Add(leaveEnd);

            var catchStart = Instruction.Create(DnOpCodes.Pop);
            il.Add(catchStart);
            il.Add(Instruction.Create(DnOpCodes.Leave, retInstr));
            il.Add(retInstr);

            method.Body.ExceptionHandlers.Add(new ExceptionHandler(ExceptionHandlerType.Catch)
            {
                TryStart = tryStart,
                TryEnd = catchStart,
                HandlerStart = catchStart,
                HandlerEnd = retInstr,
                CatchType = module.CorLibTypes.Object.TypeDefOrRef
            });

            return method;
        }

        private void EmitBombCall(IList<Instruction> il, MethodDef bomb)
        {
            int pc = bomb.Parameters.Count;
            if (pc == 0)
            {
                il.Add(Instruction.Create(DnOpCodes.Call, bomb));
            }
            else if (pc == 1)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
                il.Add(Instruction.Create(DnOpCodes.Call, bomb));
            }
            else
            {
                il.Add(Instruction.Create(DnOpCodes.Ldnull));
                il.Add(Instruction.Create(DnOpCodes.Ldnull));
                il.Add(Instruction.Create(DnOpCodes.Ldnull));
                il.Add(Instruction.Create(DnOpCodes.Call, bomb));
            }
        }

        internal static void StampFile(string path, byte[] key)
        {
            if (key == null || string.IsNullOrEmpty(path)) return;
            byte[] body = System.IO.File.ReadAllBytes(path);

            ulong h64 = FnvOffset;
            for (int i = 0; i < body.Length; i++) h64 = (h64 ^ body[i]) * FnvPrime;
            byte[] inlineBytes = new byte[InlineLen];
            for (int j = 0; j < InlineLen; j++) inlineBytes[j] = (byte)(h64 >> (j * 8));

            byte[] bodyPlusInline = new byte[body.Length + InlineLen];
            Buffer.BlockCopy(body, 0, bodyPlusInline, 0, body.Length);
            Buffer.BlockCopy(inlineBytes, 0, bodyPlusInline, body.Length, InlineLen);
            byte[] mac;
            using (var h = new HMACSHA256(key))
                mac = h.ComputeHash(bodyPlusInline);

            using (var fs = new System.IO.FileStream(path, System.IO.FileMode.Append,
                System.IO.FileAccess.Write, System.IO.FileShare.None))
            {
                fs.Write(inlineBytes, 0, InlineLen);
                fs.Write(mac, 0, mac.Length);
            }
        }
    }
}
