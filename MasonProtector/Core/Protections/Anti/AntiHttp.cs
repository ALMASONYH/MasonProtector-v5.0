using System;
using System.Linq;
using dnlib.DotNet;
using dnlib.DotNet.Emit;

using DnMethodAttributes = dnlib.DotNet.MethodAttributes;
using DnMethodImplAttributes = dnlib.DotNet.MethodImplAttributes;
using DnTypeAttributes = dnlib.DotNet.TypeAttributes;
using DnOpCodes = dnlib.DotNet.Emit.OpCodes;

namespace MasonProtector.Core
{
    internal class AntiHttpProtection
    {
        private readonly Obfuscation engine;
        private readonly Random rng;

        private static readonly string[] httpTools = new string[]
        {
            "fiddler", "wireshark", "charles", "mitmproxy", "mitmdump",
            "httpdebuggerui", "httpdebugger", "tshark", "dumpcap",
            "rawcap", "proxifier", "networkminer", "smsniff"
        };

        internal AntiHttpProtection(Obfuscation eng)
        {
            engine = eng;
            rng = eng.rng;
        }

        internal void ApplyAntiHttp(ModuleDef module, TypeDef modType)
        {
            var antiType = new TypeDefUser("", engine.MakeName(),
                module.CorLibTypes.Object.TypeDefOrRef);
            antiType.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
            module.Types.Add(antiType);
            engine.injectedTypes.Add(antiType);

            NativeShroud shroud = engine.EnsureShroud(module);

            MethodDef tlsInit = BuildTlsInitMethod(module);
            antiType.Methods.Add(tlsInit);
            engine.injectedMethods.Add(tlsInit);

            MethodDef suicide = BuildSuicideMethod(module, shroud);
            MethodDef scan = BuildScanMethod(module, suicide);

            antiType.Methods.Add(suicide);
            antiType.Methods.Add(scan);
            engine.injectedMethods.Add(suicide);
            engine.injectedMethods.Add(scan);

            engine.InjectCallInCctor(module, modType, tlsInit);
            engine.InjectCallInCctor(module, modType, scan);

            MethodDef bgMonitor = BuildBackgroundMonitor(module, scan);
            antiType.Methods.Add(bgMonitor);
            engine.injectedMethods.Add(bgMonitor);

            MethodDef startBg = BuildBackgroundStarter(module, bgMonitor);
            antiType.Methods.Add(startBg);
            engine.injectedMethods.Add(startBg);
            engine.InjectCallInCctor(module, modType, startBg);
        }

        private MethodDef BuildTlsInitMethod(ModuleDef module)
        {
            var initMethod = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Void),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            initMethod.Body = new CilBody();
            initMethod.Body.InitLocals = true;

            var il = initMethod.Body.Instructions;

            var setSecProto = module.Import(typeof(System.Net.ServicePointManager).GetProperty("SecurityProtocol").GetSetMethod());
            var getSecProto = module.Import(typeof(System.Net.ServicePointManager).GetProperty("SecurityProtocol").GetGetMethod());

            var afterTry = Instruction.Create(DnOpCodes.Ret);

            var tryStart = Instruction.Create(DnOpCodes.Call, getSecProto);
            il.Add(tryStart);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 3072));
            il.Add(Instruction.Create(DnOpCodes.Or));
            il.Add(Instruction.Create(DnOpCodes.Call, setSecProto));

            il.Add(Instruction.Create(DnOpCodes.Leave, afterTry));

            var handlerStart = Instruction.Create(DnOpCodes.Pop);
            il.Add(handlerStart);
            il.Add(Instruction.Create(DnOpCodes.Leave, afterTry));
            il.Add(afterTry);

            initMethod.Body.ExceptionHandlers.Add(new ExceptionHandler(ExceptionHandlerType.Catch)
            {
                TryStart = tryStart,
                TryEnd = handlerStart,
                HandlerStart = handlerStart,
                HandlerEnd = afterTry,
                CatchType = new TypeRefUser(module, "System", "Exception",
                    module.CorLibTypes.AssemblyRef),
            });

            return initMethod;
        }

        private MethodDef BuildSuicideMethod(ModuleDef module, NativeShroud shroud)
        {
            var method = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Void),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            method.Body = new CilBody();
            method.Body.InitLocals = true;

            var il = method.Body.Instructions;

            engine.EmitAntiCrackHook(il);

            il.Add(Instruction.Create(DnOpCodes.Call, shroud.GetCurrentProcess));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_M1));
            il.Add(Instruction.Create(DnOpCodes.Call, shroud.TerminateProcess));
            il.Add(Instruction.Create(DnOpCodes.Pop));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_M1));
            il.Add(Instruction.Create(DnOpCodes.Call, shroud.ExitProcess));

            il.Add(Instruction.Create(DnOpCodes.Ret));
            return method;
        }

        private MethodDef BuildScanMethod(ModuleDef module, MethodDef suicide)
        {
            var method = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Void),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            method.Body = new CilBody();
            method.Body.InitLocals = true;

            method.Body.Variables.Add(new Local(module.Import(typeof(System.Diagnostics.Process[])).ToTypeSig()));
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            method.Body.Variables.Add(new Local(module.CorLibTypes.String));
            method.Body.Variables.Add(new Local(module.Import(typeof(System.Diagnostics.Process)).ToTypeSig()));

            var il = method.Body.Instructions;

            var getProcs = module.Import(typeof(System.Diagnostics.Process).GetMethod("GetProcesses", Type.EmptyTypes));
            var getProcName = module.Import(typeof(System.Diagnostics.Process).GetProperty("ProcessName").GetGetMethod());
            var toLower = module.Import(typeof(string).GetMethod("ToLowerInvariant", Type.EmptyTypes));
            var strContains = module.Import(typeof(string).GetMethod("Contains", new Type[] { typeof(string) }));

            var retInst = Instruction.Create(DnOpCodes.Ret);
            var loopBody = Instruction.Create(DnOpCodes.Ldloc_0);
            var loopCond = Instruction.Create(DnOpCodes.Ldloc_1);

            var tryStart = Instruction.Create(DnOpCodes.Call, getProcs);
            il.Add(tryStart);
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));
            il.Add(Instruction.Create(DnOpCodes.Br, loopCond));

            il.Add(loopBody);
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Stloc_3));

            var innerTry = Instruction.Create(DnOpCodes.Ldloc_3);
            il.Add(innerTry);
            il.Add(Instruction.Create(DnOpCodes.Callvirt, getProcName));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, toLower));
            il.Add(Instruction.Create(DnOpCodes.Stloc_2));

            var doKill = Instruction.Create(DnOpCodes.Call, suicide);
            var afterChecks = Instruction.Create(DnOpCodes.Nop);
            foreach (string tool in httpTools)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldloc_2));
                il.Add(Instruction.Create(DnOpCodes.Ldstr, tool));
                il.Add(Instruction.Create(DnOpCodes.Callvirt, strContains));
                il.Add(Instruction.Create(DnOpCodes.Brtrue, doKill));
            }
            il.Add(Instruction.Create(DnOpCodes.Br, afterChecks));
            il.Add(doKill);
            il.Add(afterChecks);

            var innerEnd = Instruction.Create(DnOpCodes.Nop);
            il.Add(Instruction.Create(DnOpCodes.Leave, innerEnd));
            var innerCatch = Instruction.Create(DnOpCodes.Pop);
            il.Add(innerCatch);
            il.Add(Instruction.Create(DnOpCodes.Leave, innerEnd));
            il.Add(innerEnd);

            method.Body.ExceptionHandlers.Add(new ExceptionHandler(ExceptionHandlerType.Catch)
            {
                TryStart = innerTry,
                TryEnd = innerCatch,
                HandlerStart = innerCatch,
                HandlerEnd = innerEnd,
                CatchType = module.CorLibTypes.Object.TypeDefOrRef
            });

            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));

            il.Add(loopCond);
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Blt, loopBody));

            il.Add(Instruction.Create(DnOpCodes.Leave, retInst));

            var outerCatch = Instruction.Create(DnOpCodes.Pop);
            il.Add(outerCatch);
            il.Add(Instruction.Create(DnOpCodes.Leave, retInst));
            il.Add(retInst);

            method.Body.ExceptionHandlers.Add(new ExceptionHandler(ExceptionHandlerType.Catch)
            {
                TryStart = tryStart,
                TryEnd = outerCatch,
                HandlerStart = outerCatch,
                HandlerEnd = retInst,
                CatchType = module.CorLibTypes.Object.TypeDefOrRef
            });

            return method;
        }

        private MethodDef BuildBackgroundMonitor(ModuleDef module, MethodDef scanner)
        {
            var method = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Void),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Private | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            method.Body = new CilBody();

            var threadSleep = module.Import(typeof(System.Threading.Thread).GetMethod("Sleep", new[] { typeof(int) }));
            var il = method.Body.Instructions;

            var tryStart = Instruction.Create(DnOpCodes.Call, scanner);
            var handlerStart = Instruction.Create(DnOpCodes.Pop);
            var beforeSleep = Instruction.Create(DnOpCodes.Ldc_I4, 1500 + rng.Next(0, 2500));

            il.Add(tryStart);
            il.Add(Instruction.Create(DnOpCodes.Leave, beforeSleep));
            il.Add(handlerStart);
            il.Add(Instruction.Create(DnOpCodes.Leave, beforeSleep));
            il.Add(beforeSleep);
            il.Add(Instruction.Create(DnOpCodes.Call, threadSleep));
            il.Add(Instruction.Create(DnOpCodes.Br, tryStart));

            method.Body.ExceptionHandlers.Add(new ExceptionHandler(ExceptionHandlerType.Catch)
            {
                TryStart = tryStart,
                TryEnd = handlerStart,
                HandlerStart = handlerStart,
                HandlerEnd = beforeSleep,
                CatchType = module.CorLibTypes.Object.TypeDefOrRef
            });

            return method;
        }

        private MethodDef BuildBackgroundStarter(ModuleDef module, MethodDef bgEntry)
        {
            var startBg = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Void),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            startBg.Body = new CilBody();
            startBg.Body.InitLocals = true;
            startBg.Body.Variables.Add(new Local(module.Import(typeof(System.Threading.Thread)).ToTypeSig()));

            var sbIl = startBg.Body.Instructions;

            var threadStartCtor = module.Import(typeof(System.Threading.ThreadStart).GetConstructor(
                new[] { typeof(object), typeof(IntPtr) }));
            var threadCtor = module.Import(typeof(System.Threading.Thread).GetConstructor(
                new[] { typeof(System.Threading.ThreadStart) }));
            var threadSetBg = module.Import(typeof(System.Threading.Thread).GetProperty("IsBackground").GetSetMethod());
            var threadStart = module.Import(typeof(System.Threading.Thread).GetMethod("Start", Type.EmptyTypes));

            var tryStart = Instruction.Create(DnOpCodes.Ldnull);
            sbIl.Add(tryStart);
            sbIl.Add(Instruction.Create(DnOpCodes.Ldftn, bgEntry));
            sbIl.Add(Instruction.Create(DnOpCodes.Newobj, threadStartCtor));
            sbIl.Add(Instruction.Create(DnOpCodes.Newobj, threadCtor));
            sbIl.Add(Instruction.Create(DnOpCodes.Stloc_0));
            sbIl.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            sbIl.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            sbIl.Add(Instruction.Create(DnOpCodes.Callvirt, threadSetBg));
            sbIl.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            sbIl.Add(Instruction.Create(DnOpCodes.Callvirt, threadStart));

            var retInst = Instruction.Create(DnOpCodes.Ret);
            sbIl.Add(Instruction.Create(DnOpCodes.Leave, retInst));
            var catchInst = Instruction.Create(DnOpCodes.Pop);
            sbIl.Add(catchInst);
            sbIl.Add(Instruction.Create(DnOpCodes.Leave, retInst));
            sbIl.Add(retInst);

            startBg.Body.ExceptionHandlers.Add(new ExceptionHandler(ExceptionHandlerType.Catch)
            {
                TryStart = tryStart,
                TryEnd = catchInst,
                HandlerStart = catchInst,
                HandlerEnd = retInst,
                CatchType = module.CorLibTypes.Object.TypeDefOrRef
            });

            return startBg;
        }
    }
}
