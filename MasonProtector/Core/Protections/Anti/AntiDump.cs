using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.InteropServices;
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
    internal class AntiDumpProtection
    {
        private Obfuscation engine;
        private Random rng;

        internal AntiDumpProtection(Obfuscation eng)
        {
            engine = eng;
            rng = eng.rng;
        }

        private MethodDef BuildDumpBackground(ModuleDef module, TypeDef owner, MethodDef erase)
        {
            var m = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Void),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Private | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            m.Body = new CilBody();
            m.Body.InitLocals = true;
            var threadSleep = module.Import(typeof(System.Threading.Thread).GetMethod("Sleep", new[] { typeof(int) }));
            var il = m.Body.Instructions;
            var loopStart = Instruction.Create(DnOpCodes.Ldc_I4, 1500 + rng.Next(0, 2000));
            var afterCatch = Instruction.Create(DnOpCodes.Br, loopStart);
            il.Add(loopStart);
            il.Add(Instruction.Create(DnOpCodes.Call, threadSleep));
            var tryStart = Instruction.Create(DnOpCodes.Call, erase);
            il.Add(tryStart);
            il.Add(Instruction.Create(DnOpCodes.Leave, afterCatch));
            var catchStart = Instruction.Create(DnOpCodes.Pop);
            il.Add(catchStart);
            il.Add(Instruction.Create(DnOpCodes.Leave, afterCatch));
            il.Add(afterCatch);
            m.Body.ExceptionHandlers.Add(new ExceptionHandler(ExceptionHandlerType.Catch)
            {
                TryStart = tryStart, TryEnd = catchStart,
                HandlerStart = catchStart, HandlerEnd = afterCatch,
                CatchType = module.CorLibTypes.Object.TypeDefOrRef
            });
            return m;
        }

        private MethodDef BuildStartDumpBackground(ModuleDef module, TypeDef owner, MethodDef bgMon)
        {
            var m = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Void),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            m.Body = new CilBody();
            m.Body.InitLocals = true;
            m.Body.Variables.Add(new Local(module.Import(typeof(System.Threading.Thread)).ToTypeSig()));
            var threadStartCtor = module.Import(typeof(System.Threading.ThreadStart).GetConstructor(new[] { typeof(object), typeof(IntPtr) }));
            var threadCtor = module.Import(typeof(System.Threading.Thread).GetConstructor(new[] { typeof(System.Threading.ThreadStart) }));
            var threadSetBg = module.Import(typeof(System.Threading.Thread).GetProperty("IsBackground").GetSetMethod());
            var threadStart = module.Import(typeof(System.Threading.Thread).GetMethod("Start", Type.EmptyTypes));
            var il = m.Body.Instructions;
            var tryStart = Instruction.Create(DnOpCodes.Ldnull);
            il.Add(tryStart);
            il.Add(Instruction.Create(DnOpCodes.Ldftn, bgMon));
            il.Add(Instruction.Create(DnOpCodes.Newobj, threadStartCtor));
            il.Add(Instruction.Create(DnOpCodes.Newobj, threadCtor));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, threadSetBg));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, threadStart));
            var retInst = Instruction.Create(DnOpCodes.Ret);
            il.Add(Instruction.Create(DnOpCodes.Leave, retInst));
            var catchStart = Instruction.Create(DnOpCodes.Pop);
            il.Add(catchStart);
            il.Add(Instruction.Create(DnOpCodes.Leave, retInst));
            il.Add(retInst);
            m.Body.ExceptionHandlers.Add(new ExceptionHandler(ExceptionHandlerType.Catch)
            {
                TryStart = tryStart, TryEnd = catchStart,
                HandlerStart = catchStart, HandlerEnd = retInst,
                CatchType = module.CorLibTypes.Object.TypeDefOrRef
            });
            return m;
        }

        internal void ApplyAntiDump(ModuleDef module, TypeDef modType)
        {
            engine.activeOption = "AntiDump";
            var dumpType = new TypeDefUser("", engine.MakeName(),
                module.CorLibTypes.Object.TypeDefOrRef);
            dumpType.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;

            for (int i = 0; i < engine.LevelRange(6, 12, 10, 24, 18, 36); i++)
            {
                dumpType.Fields.Add(new FieldDefUser(engine.MakeName(),
                    new FieldSig(module.CorLibTypes.IntPtr),
                    DnFieldAttributes.Private | DnFieldAttributes.Static));
            }

            var eraseMethod = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Void),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            eraseMethod.Body = new CilBody();
            eraseMethod.Body.InitLocals = true;
            var procArrSig = new SZArraySig(module.Import(typeof(System.Diagnostics.Process)).ToTypeSig());
            eraseMethod.Body.Variables.Add(new Local(procArrSig));
            eraseMethod.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            eraseMethod.Body.Variables.Add(new Local(module.CorLibTypes.String));

            var il = eraseMethod.Body.Instructions;

            NativeShroud shroud = engine.antiShroud;
            if (shroud == null)
            {
                shroud = new NativeShroud(engine, module, dumpType);
                shroud.Build();
                engine.antiShroud = shroud;
            }
            var getProcs    = module.Import(typeof(System.Diagnostics.Process).GetMethod("GetProcesses", Type.EmptyTypes));
            var getProcName = module.Import(typeof(System.Diagnostics.Process).GetProperty("ProcessName").GetGetMethod());
            var toLower     = module.Import(typeof(string).GetMethod("ToLowerInvariant", Type.EmptyTypes));
            var strContains = module.Import(typeof(string).GetMethod("Contains", new[] { typeof(string) }));

            string[] dumperNames = {
                "extremedumper", "megadumper", "megadumpernet", "dotdumper",
                "scylla", "scyllahide", "pe-sieve", "pesieve", "netdumper",
                "minidumpwritedump", "procdump", "createdump", "petdumper",
                "dumppe", "extremedumpergui",
                "comae", "winpmem", "dumpit", "magnet", "memdump"
            };

            var eraseRet = Instruction.Create(DnOpCodes.Ret);
            var loopHead = Instruction.Create(DnOpCodes.Nop);

            var tryStart = Instruction.Create(DnOpCodes.Call, getProcs);
            il.Add(tryStart);
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));
            il.Add(Instruction.Create(DnOpCodes.Br, loopHead));
            var bodyStart = Instruction.Create(DnOpCodes.Ldloc_0);
            il.Add(bodyStart);
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, getProcName));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, toLower));
            il.Add(Instruction.Create(DnOpCodes.Stloc_2));
            foreach (string dn in dumperNames)
            {
                var nextChk = Instruction.Create(DnOpCodes.Nop);
                il.Add(Instruction.Create(DnOpCodes.Ldloc_2));
                il.Add(Instruction.Create(DnOpCodes.Ldstr, dn));
                il.Add(Instruction.Create(DnOpCodes.Callvirt, strContains));
                il.Add(Instruction.Create(DnOpCodes.Brfalse, nextChk));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4_M1));
                il.Add(Instruction.Create(DnOpCodes.Call, shroud.ExitProcess));
                il.Add(nextChk);
            }
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));
            il.Add(loopHead);
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Blt, bodyStart));
            il.Add(Instruction.Create(DnOpCodes.Leave, eraseRet));

            var eraseCatch = Instruction.Create(DnOpCodes.Pop);
            il.Add(eraseCatch);
            il.Add(Instruction.Create(DnOpCodes.Leave, eraseRet));
            il.Add(eraseRet);

            eraseMethod.Body.ExceptionHandlers.Add(new ExceptionHandler(ExceptionHandlerType.Catch)
            {
                TryStart     = tryStart,
                TryEnd       = eraseCatch,
                HandlerStart = eraseCatch,
                HandlerEnd   = eraseRet,
                CatchType    = module.CorLibTypes.Object.TypeDefOrRef
            });

            dumpType.Methods.Add(eraseMethod);
            engine.injectedMethods.Add(eraseMethod);
            module.Types.Add(dumpType);
            engine.injectedTypes.Add(dumpType);
            engine.InjectCallInCctor(module, modType, eraseMethod);
            engine.InjectCallInRandomMethods(module, eraseMethod, 5, 12);

            MethodDef bgMon = BuildDumpBackground(module, dumpType, eraseMethod);
            dumpType.Methods.Add(bgMon);
            engine.injectedMethods.Add(bgMon);
            MethodDef startBg = BuildStartDumpBackground(module, dumpType, bgMon);
            dumpType.Methods.Add(startBg);
            engine.injectedMethods.Add(startBg);
            engine.InjectCallInCctor(module, modType, startBg);

            for (int i = 0; i < rng.Next(8, 18); i++)
            {
                var trapType = new TypeDefUser("", engine.MakeName(),
                    module.CorLibTypes.Object.TypeDefOrRef);
                trapType.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                    DnTypeAttributes.Sealed;

                trapType.Fields.Add(new FieldDefUser(engine.MakeName(),
                    new FieldSig(module.CorLibTypes.IntPtr),
                    DnFieldAttributes.Private | DnFieldAttributes.Static));

                module.Types.Add(trapType);
                engine.injectedTypes.Add(trapType);
            }
        }
    }
}
