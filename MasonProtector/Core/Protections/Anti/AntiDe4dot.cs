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
    internal class AntiDe4dotProtection
    {
        private Obfuscation engine;
        private Random rng;

        internal AntiDe4dotProtection(Obfuscation eng)
        {
            engine = eng;
            rng = eng.rng;
        }

        internal void ApplyAntiDe4dot(ModuleDef module, TypeDef modType)
        {
            var markerCtor = InjectFakeObfuscatorMarker(module);
            InjectMarkerReference(module, modType, markerCtor);
            InjectDecoyTraps(module);
        }

        private MemberRef InjectFakeObfuscatorMarker(ModuleDef module)
        {
            var attrType = new TypeDefUser("CryptoObfuscator", "ProtectedWithCryptoObfuscatorAttribute",
                module.CorLibTypes.GetTypeRef("System", "Attribute"));
            attrType.Attributes = DnTypeAttributes.Public | DnTypeAttributes.Sealed |
                DnTypeAttributes.BeforeFieldInit;
            module.Types.Add(attrType);
            engine.injectedTypes.Add(attrType);

            var ctor = new MethodDefUser(".ctor",
                MethodSig.CreateInstance(module.CorLibTypes.Void),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Public | DnMethodAttributes.HideBySig |
                DnMethodAttributes.SpecialName | DnMethodAttributes.RTSpecialName);
            ctor.Body = new CilBody();
            ctor.Body.Instructions.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            var baseCtorRef = new MemberRefUser(module, ".ctor",
                MethodSig.CreateInstance(module.CorLibTypes.Void),
                module.CorLibTypes.GetTypeRef("System", "Attribute"));
            ctor.Body.Instructions.Add(Instruction.Create(DnOpCodes.Call, baseCtorRef));
            ctor.Body.Instructions.Add(Instruction.Create(DnOpCodes.Ret));
            attrType.Methods.Add(ctor);
            engine.injectedMethods.Add(ctor);

            var versionField = new FieldDefUser("Version",
                new FieldSig(module.CorLibTypes.String),
                DnFieldAttributes.Public);
            attrType.Fields.Add(versionField);

            var attrRef = new MemberRefUser(module, ".ctor",
                MethodSig.CreateInstance(module.CorLibTypes.Void),
                attrType);
            var ca = new CustomAttribute(attrRef);
            module.CustomAttributes.Add(ca);

            var hexChars = "0123456789abcdef";
            var hashBuf = new char[32];
            for (int i = 0; i < 32; i++)
                hashBuf[i] = hexChars[rng.Next(16)];
            var hashName = "c" + new string(hashBuf);

            var hashType = new TypeDefUser("A", hashName,
                module.CorLibTypes.Object.TypeDefOrRef);
            hashType.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
            module.Types.Add(hashType);
            engine.injectedTypes.Add(hashType);

            for (int f = 0; f < rng.Next(2, 5); f++)
            {
                hashType.Fields.Add(new FieldDefUser(engine.MakeName(rng.Next(4, 10)),
                    new FieldSig(module.CorLibTypes.Int32),
                    DnFieldAttributes.Private | DnFieldAttributes.Static));
            }

            var helperType = new TypeDefUser("CryptoObfuscator", engine.MakeName(rng.Next(8, 16)),
                module.CorLibTypes.Object.TypeDefOrRef);
            helperType.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
            module.Types.Add(helperType);
            engine.injectedTypes.Add(helperType);

            for (int i = 0; i < rng.Next(3, 6); i++)
            {
                helperType.Fields.Add(new FieldDefUser(engine.MakeName(rng.Next(4, 12)),
                    new FieldSig(module.CorLibTypes.Int32),
                    DnFieldAttributes.Private | DnFieldAttributes.Static));
            }

            var decryptMethod = new MethodDefUser(engine.MakeName(rng.Next(6, 14)),
                MethodSig.CreateStatic(module.CorLibTypes.String, module.CorLibTypes.Int32),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            decryptMethod.Body = new CilBody();
            decryptMethod.Body.InitLocals = true;
            decryptMethod.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            var dil = decryptMethod.Body.Instructions;
            dil.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            dil.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
            dil.Add(Instruction.Create(DnOpCodes.Xor));
            dil.Add(Instruction.Create(DnOpCodes.Stloc_0));
            dil.Add(Instruction.Create(DnOpCodes.Ldnull));
            dil.Add(Instruction.Create(DnOpCodes.Ret));
            helperType.Methods.Add(decryptMethod);
            engine.injectedMethods.Add(decryptMethod);

            var resDecryptMethod = new MethodDefUser(engine.MakeName(rng.Next(6, 14)),
                MethodSig.CreateStatic(module.CorLibTypes.Object,
                    module.CorLibTypes.String, module.CorLibTypes.Int32),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            resDecryptMethod.Body = new CilBody();
            var rdil = resDecryptMethod.Body.Instructions;
            rdil.Add(Instruction.Create(DnOpCodes.Ldnull));
            rdil.Add(Instruction.Create(DnOpCodes.Ret));
            helperType.Methods.Add(resDecryptMethod);
            engine.injectedMethods.Add(resDecryptMethod);
            return attrRef;
        }

        private void InjectMarkerReference(ModuleDef module, TypeDef modType, MemberRef markerCtor)
        {
            if (markerCtor == null) return;

            var cctor = modType.FindStaticConstructor();
            if (cctor == null)
            {
                cctor = new MethodDefUser(".cctor",
                    MethodSig.CreateStatic(module.CorLibTypes.Void),
                    DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                    DnMethodAttributes.Private | DnMethodAttributes.Static |
                    DnMethodAttributes.HideBySig | DnMethodAttributes.SpecialName |
                    DnMethodAttributes.RTSpecialName);
                cctor.Body = new CilBody();
                cctor.Body.Instructions.Add(Instruction.Create(DnOpCodes.Ret));
                modType.Methods.Add(cctor);
            }

            var il = cctor.Body.Instructions;
            int insertAt = 0;
            for (int i = 0; i < il.Count; i++)
            {
                if (il[i].OpCode == DnOpCodes.Ret) { insertAt = i; break; }
            }
            il.Insert(insertAt, Instruction.Create(DnOpCodes.Pop));
            il.Insert(insertAt, Instruction.Create(DnOpCodes.Newobj, markerCtor));
        }

        private void InjectDecoyTraps(ModuleDef module)
        {
            for (int i = 0; i < rng.Next(18, 38); i++)
            {
                var trapType = new TypeDefUser("", engine.MakeName(rng.Next(8, 24)),
                    module.CorLibTypes.Object.TypeDefOrRef);

                if (rng.Next(0, 3) == 0)
                {
                    trapType.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Interface |
                        DnTypeAttributes.Abstract;
                }
                else
                {
                    trapType.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                        DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
                }

                for (int f = 0; f < rng.Next(2, 8); f++)
                {
                    TypeSig fType;
                    switch (rng.Next(0, 5))
                    {
                        case 0: fType = module.CorLibTypes.IntPtr; break;
                        case 1: fType = module.CorLibTypes.UIntPtr; break;
                        case 2: fType = new SZArraySig(module.CorLibTypes.Byte); break;
                        case 3: fType = module.CorLibTypes.Object; break;
                        default: fType = module.CorLibTypes.Int32; break;
                    }

                    trapType.Fields.Add(new FieldDefUser(engine.MakeName(rng.Next(4, 16)),
                        new FieldSig(fType),
                        DnFieldAttributes.Private | DnFieldAttributes.Static));
                }

                for (int m = 0; m < rng.Next(1, 4); m++)
                {
                    var trapMethod = new MethodDefUser(engine.MakeName(rng.Next(6, 16)),
                        MethodSig.CreateStatic(module.CorLibTypes.Void),
                        DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                        DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
                    trapMethod.Body = new CilBody();
                    trapMethod.Body.Instructions.Add(Instruction.Create(DnOpCodes.Ret));
                    trapType.Methods.Add(trapMethod);
                    engine.injectedMethods.Add(trapMethod);
                }

                if (rng.Next(0, 3) == 0)
                {
                    var iface = new TypeDefUser("", engine.MakeName(rng.Next(8, 20)),
                        null);
                    iface.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Interface | DnTypeAttributes.Abstract;
                    module.Types.Add(iface);
                    engine.injectedTypes.Add(iface);

                    var ifaceImpl = new InterfaceImplUser(iface);
                    trapType.Interfaces.Add(ifaceImpl);
                }

                module.Types.Add(trapType);
                engine.injectedTypes.Add(trapType);
            }

            for (int i = 0; i < rng.Next(10, 22); i++)
            {
                var loopType = new TypeDefUser("", engine.MakeName(rng.Next(8, 20)),
                    module.CorLibTypes.Object.TypeDefOrRef);
                loopType.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                    DnTypeAttributes.Sealed;

                var nested = new TypeDefUser("", engine.MakeName(rng.Next(6, 14)),
                    module.CorLibTypes.Object.TypeDefOrRef);
                nested.Attributes = DnTypeAttributes.NestedPrivate | DnTypeAttributes.Abstract |
                    DnTypeAttributes.Sealed;
                loopType.NestedTypes.Add(nested);

                nested.Fields.Add(new FieldDefUser(engine.MakeName(),
                    new FieldSig(module.CorLibTypes.IntPtr),
                    DnFieldAttributes.Private | DnFieldAttributes.Static));

                module.Types.Add(loopType);
                engine.injectedTypes.Add(loopType);
                engine.injectedTypes.Add(nested);
            }
        }

        private void InjectSwitchBombs(ModuleDef module)
        {
            var hostType = new TypeDefUser("", engine.MakeName(rng.Next(8, 20)),
                module.CorLibTypes.Object.TypeDefOrRef);
            hostType.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
            module.Types.Add(hostType);
            engine.injectedTypes.Add(hostType);

            for (int b = 0; b < rng.Next(2, 4); b++)
            {
                var m = new MethodDefUser(engine.MakeName(rng.Next(6, 14)),
                    MethodSig.CreateStatic(module.CorLibTypes.Void),
                    DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                    DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
                m.Body = new CilBody();
                m.Body.InitLocals = true;
                m.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
                var il = m.Body.Instructions;

                var ret = Instruction.Create(DnOpCodes.Ret);
                var retBlock = Instruction.Create(DnOpCodes.Ldc_I4_0);

                int switchSize = rng.Next(8000, 12000);
                var targets = new Instruction[switchSize];
                for (int t = 0; t < switchSize; t++)
                    targets[t] = retBlock;

                il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
                il.Add(new Instruction(DnOpCodes.Switch, targets));
                il.Add(Instruction.Create(DnOpCodes.Br, ret));
                il.Add(retBlock);
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                il.Add(Instruction.Create(DnOpCodes.Xor));
                il.Add(Instruction.Create(DnOpCodes.Pop));
                il.Add(ret);

                hostType.Methods.Add(m);
                engine.injectedMethods.Add(m);
            }

            var hostType2 = new TypeDefUser("", engine.MakeName(rng.Next(8, 20)),
                module.CorLibTypes.Object.TypeDefOrRef);
            hostType2.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
            module.Types.Add(hostType2);
            engine.injectedTypes.Add(hostType2);

            for (int b = 0; b < rng.Next(2, 4); b++)
            {
                var m = new MethodDefUser(engine.MakeName(rng.Next(6, 14)),
                    MethodSig.CreateStatic(module.CorLibTypes.Int32, module.CorLibTypes.Int32),
                    DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                    DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
                m.Body = new CilBody();
                m.Body.InitLocals = true;
                m.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
                var il = m.Body.Instructions;

                int outerSize = rng.Next(3000, 5000);
                int outerNesting = rng.Next(3, 6);

                var innerBlocks = new List<Instruction[]>();
                var ret = Instruction.Create(DnOpCodes.Ldloc_0);

                for (int n = 0; n < outerNesting; n++)
                {
                    int sz = outerSize / outerNesting;
                    var tgts = new Instruction[sz];
                    var tgt = Instruction.Create(DnOpCodes.Nop);
                    for (int t = 0; t < sz; t++) tgts[t] = tgt;
                    innerBlocks.Add(new Instruction[] {
                        Instruction.Create(DnOpCodes.Ldarg_0),
                        new Instruction(DnOpCodes.Switch, tgts),
                        Instruction.Create(DnOpCodes.Br, ret),
                        tgt,
                        Instruction.Create(DnOpCodes.Ldarg_0),
                        Instruction.Create(DnOpCodes.Stloc_0)
                    });
                }

                il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                foreach (var block in innerBlocks)
                    foreach (var ins in block)
                        il.Add(ins);
                il.Add(ret);
                il.Add(Instruction.Create(DnOpCodes.Ret));

                hostType2.Methods.Add(m);
                engine.injectedMethods.Add(m);
            }
        }

        private void InjectEhDepthBombs(ModuleDef module)
        {
            var hostType = new TypeDefUser("", engine.MakeName(rng.Next(8, 20)),
                module.CorLibTypes.Object.TypeDefOrRef);
            hostType.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
            module.Types.Add(hostType);
            engine.injectedTypes.Add(hostType);

            for (int b = 0; b < rng.Next(2, 4); b++)
            {
                var m = BuildDeepEhMethod(module);
                hostType.Methods.Add(m);
                engine.injectedMethods.Add(m);
            }

            for (int b = 0; b < rng.Next(1, 3); b++)
            {
                var m = BuildMultiHandlerEhMethod(module);
                hostType.Methods.Add(m);
                engine.injectedMethods.Add(m);
            }
        }

        private MethodDef BuildDeepEhMethod(ModuleDef module)
        {
            var m = new MethodDefUser(engine.MakeName(rng.Next(6, 14)),
                MethodSig.CreateStatic(module.CorLibTypes.Int32),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            m.Body = new CilBody();
            m.Body.InitLocals = true;
            m.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            var il = m.Body.Instructions;

            var exTypeRef = module.CorLibTypes.GetTypeRef("System", "Exception");
            int depth = rng.Next(100, 160);

            var tryStarts = new Instruction[depth];
            var handlerStarts = new Instruction[depth];
            var handlerEnds = new Instruction[depth];

            for (int i = 0; i < depth; i++)
            {
                tryStarts[i] = Instruction.Create(DnOpCodes.Ldc_I4, rng.Next());
                handlerStarts[i] = Instruction.Create(DnOpCodes.Pop);
                handlerEnds[i] = Instruction.Create(DnOpCodes.Nop);
            }

            var ret = Instruction.Create(DnOpCodes.Ldloc_0);
            var finalRet = Instruction.Create(DnOpCodes.Ret);

            for (int i = 0; i < depth; i++)
            {
                il.Add(tryStarts[i]);
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                il.Add(Instruction.Create(DnOpCodes.Leave, ret));
                il.Add(handlerStarts[i]);
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                il.Add(Instruction.Create(DnOpCodes.Leave, ret));
                il.Add(handlerEnds[i]);
            }

            il.Add(ret);
            il.Add(finalRet);

            for (int i = 0; i < depth; i++)
            {
                var eh = new ExceptionHandler(ExceptionHandlerType.Catch);
                eh.TryStart = tryStarts[i];
                eh.TryEnd = handlerStarts[i];
                eh.HandlerStart = handlerStarts[i];
                eh.HandlerEnd = handlerEnds[i];
                eh.CatchType = exTypeRef;
                m.Body.ExceptionHandlers.Add(eh);
            }

            return m;
        }

        private MethodDef BuildMultiHandlerEhMethod(ModuleDef module)
        {
            var m = new MethodDefUser(engine.MakeName(rng.Next(6, 14)),
                MethodSig.CreateStatic(module.CorLibTypes.Void),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            m.Body = new CilBody();
            m.Body.InitLocals = true;
            m.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            var il = m.Body.Instructions;

            var exTypeRef = module.CorLibTypes.GetTypeRef("System", "Exception");
            int chainLen = rng.Next(60, 100);

            var tryStarts = new Instruction[chainLen];
            var handlerStarts = new Instruction[chainLen];
            var leaves = new Instruction[chainLen];
            var hLeaves = new Instruction[chainLen];

            var ret = Instruction.Create(DnOpCodes.Ret);

            for (int i = 0; i < chainLen; i++)
            {
                tryStarts[i] = Instruction.Create(DnOpCodes.Ldc_I4, rng.Next());
                handlerStarts[i] = Instruction.Create(DnOpCodes.Pop);
                leaves[i] = Instruction.Create(DnOpCodes.Leave, ret);
                hLeaves[i] = Instruction.Create(DnOpCodes.Leave, ret);
            }

            for (int i = 0; i < chainLen; i++)
            {
                il.Add(tryStarts[i]);
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                il.Add(leaves[i]);
                il.Add(handlerStarts[i]);
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                il.Add(hLeaves[i]);
            }

            il.Add(ret);

            for (int i = 0; i < chainLen; i++)
            {
                var handlerEnd = i + 1 < chainLen ? tryStarts[i + 1] : ret;
                var eh = new ExceptionHandler(ExceptionHandlerType.Catch);
                eh.TryStart = tryStarts[i];
                eh.TryEnd = handlerStarts[i];
                eh.HandlerStart = handlerStarts[i];
                eh.HandlerEnd = handlerEnd;
                eh.CatchType = exTypeRef;
                m.Body.ExceptionHandlers.Add(eh);
            }

            return m;
        }
    }
}
