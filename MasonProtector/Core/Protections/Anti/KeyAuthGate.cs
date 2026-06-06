using System.Collections.Generic;
using dnlib.DotNet;
using dnlib.DotNet.Emit;

using DnOpCodes = dnlib.DotNet.Emit.OpCodes;
using DnMethodAttributes = dnlib.DotNet.MethodAttributes;
using DnMethodImplAttributes = dnlib.DotNet.MethodImplAttributes;
using DnCallingConvention = dnlib.DotNet.CallingConvention;

namespace MasonProtector.Core
{
    internal class KeyAuthGateProtection
    {
        private readonly Obfuscation engine;

        internal KeyAuthGateProtection(Obfuscation eng)
        {
            engine = eng;
        }

        private void WireKillProcess(ModuleDef module, List<TypeDef> clones, TypeCloner cloner,
            TypeDef srcRuntime, NativeShroud shroud)
        {
            MethodDef killClone = null;
            foreach (MethodDef m in srcRuntime.Methods)
            {
                if (m.Name != "KillProcess") continue;
                killClone = cloner.MapMethod(m);
                break;
            }

            if (killClone == null)
            {
                foreach (TypeDef t in clones)
                    foreach (MethodDef m in t.Methods)
                        if (m.HasBody && MethodBodyContainsKillSignature(m))
                        { killClone = m; break; }
            }

            if (killClone == null) return;

            killClone.Body = new CilBody();
            killClone.Body.InitLocals = false;
            var il = killClone.Body.Instructions;

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Conv_U4));
            il.Add(Instruction.Create(DnOpCodes.Call, shroud.ExitProcess));
            il.Add(Instruction.Create(DnOpCodes.Call, shroud.GetCurrentProcess));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_M1));
            il.Add(Instruction.Create(DnOpCodes.Conv_U4));
            il.Add(Instruction.Create(DnOpCodes.Call, shroud.TerminateProcess));
            il.Add(Instruction.Create(DnOpCodes.Pop));
            il.Add(Instruction.Create(DnOpCodes.Ret));
        }

        private static bool MethodBodyContainsKillSignature(MethodDef m)
        {
            foreach (var instr in m.Body.Instructions)
            {
                if (instr.OpCode == DnOpCodes.Call || instr.OpCode == DnOpCodes.Callvirt)
                {
                    IMethod t = instr.Operand as IMethod;
                    if (t == null) continue;
                    string fn = t.FullName ?? "";
                    if (fn.Contains("Environment::FailFast") || fn.Contains("Process::Kill"))
                        return true;
                }
            }
            return false;
        }

        private void PatchEnvironmentExitCalls(List<TypeDef> clones, NativeShroud shroud)
        {
            foreach (TypeDef t in clones)
                PatchEnvironmentExitCallsInType(t, shroud);
        }

        private void PatchEnvironmentExitCallsInType(TypeDef t, NativeShroud shroud)
        {
            foreach (MethodDef m in t.Methods)
                PatchEnvironmentExitCallsInMethod(m, shroud);
            foreach (TypeDef n in t.NestedTypes)
                PatchEnvironmentExitCallsInType(n, shroud);
        }

        private void PatchEnvironmentExitCallsInMethod(MethodDef m, NativeShroud shroud)
        {
            if (!m.HasBody || m.Body == null) return;
            var il = m.Body.Instructions;
            for (int i = 0; i < il.Count; i++)
            {
                var opc = il[i].OpCode;
                if (opc != DnOpCodes.Call && opc != DnOpCodes.Callvirt) continue;
                IMethod target = il[i].Operand as IMethod;
                if (target == null) continue;
                string fullName = target.FullName ?? "";

                bool isExitWithIntArg = fullName.Contains("System.Environment::Exit") ||
                                        fullName.Contains("System.Environment::FailFast");
                bool isProcessKill    = fullName.Contains("System.Diagnostics.Process::Kill");

                if (!isExitWithIntArg && !isProcessKill) continue;

                if (isExitWithIntArg)
                {
                    il[i] = Instruction.Create(DnOpCodes.Pop);
                    il.Insert(i + 1, Instruction.Create(DnOpCodes.Ldc_I4_0));
                    il.Insert(i + 2, Instruction.Create(DnOpCodes.Conv_U4));
                    il.Insert(i + 3, Instruction.Create(DnOpCodes.Call, shroud.ExitProcess));
                    il.Insert(i + 4, Instruction.Create(DnOpCodes.Call, shroud.GetCurrentProcess));
                    il.Insert(i + 5, Instruction.Create(DnOpCodes.Ldc_I4_M1));
                    il.Insert(i + 6, Instruction.Create(DnOpCodes.Conv_U4));
                    il.Insert(i + 7, Instruction.Create(DnOpCodes.Call, shroud.TerminateProcess));
                    il.Insert(i + 8, Instruction.Create(DnOpCodes.Pop));
                    i += 8;
                }
                else if (isProcessKill)
                {
                    il[i] = Instruction.Create(DnOpCodes.Pop);
                    il.Insert(i + 1, Instruction.Create(DnOpCodes.Ldc_I4_0));
                    il.Insert(i + 2, Instruction.Create(DnOpCodes.Conv_U4));
                    il.Insert(i + 3, Instruction.Create(DnOpCodes.Call, shroud.ExitProcess));
                    il.Insert(i + 4, Instruction.Create(DnOpCodes.Call, shroud.GetCurrentProcess));
                    il.Insert(i + 5, Instruction.Create(DnOpCodes.Ldc_I4_M1));
                    il.Insert(i + 6, Instruction.Create(DnOpCodes.Conv_U4));
                    il.Insert(i + 7, Instruction.Create(DnOpCodes.Call, shroud.TerminateProcess));
                    il.Insert(i + 8, Instruction.Create(DnOpCodes.Pop));
                    i += 8;
                }
            }
        }

        internal bool ApplyKeyAuth(ModuleDef module, TypeDef modType)
        {
            MethodDef ep = module.EntryPoint;
            if (ep == null || ep.MethodSig == null) return false;

            string tool = engine.cfg.KeyAuthToolName ?? "";
            string pass = engine.cfg.KeyAuthPassword ?? "";
            bool keepConsole = engine.cfg.KeyAuthKeepConsole;
            bool alwaysPrompt = engine.cfg.KeyAuthAlwaysPrompt;
            bool showConsole = engine.cfg.KeyAuthShowConsole;

            byte[] seed;
            string alphabet;
            string asymPub = engine.cfg.KeyAuthPublicKey;
            if (engine.cfg.KeyAuthAsymmetric && !string.IsNullOrEmpty(asymPub))
            {

                seed = LicenseEngine.FromHex(asymPub);
                alphabet = LicenseEngine.IsValidAlphabet(engine.cfg.KeyAuthAlphabet)
                    ? engine.cfg.KeyAuthAlphabet
                    : LicenseEngine.Canonical;
            }
            else
            {
                seed = LicenseEngine.DeriveSeedFromCredentials(tool, pass);
                alphabet = LicenseEngine.IsValidAlphabet(engine.cfg.KeyAuthAlphabet)
                    ? engine.cfg.KeyAuthAlphabet
                    : LicenseEngine.DeriveAlphabet(seed);
            }
            string seedHex = LicenseEngine.ToHex(seed);

            ModuleDefMD self = ModuleDefMD.Load(typeof(LicenseRuntime).Assembly.Location);

            TypeDef srcEngine  = self.Find("MasonProtector.Core.LicenseEngine", false);
            TypeDef srcVendor  = self.Find("MasonProtector.Core.VendorProfile", false);
            TypeDef srcRuntime = self.Find("MasonProtector.Core.LicenseRuntime", false);

            TypeDef srcSign    = self.Find("MasonProtector.Core.LicenseSign", false);
            if (srcEngine == null || srcVendor == null || srcRuntime == null || srcSign == null) return false;

            var cloner = new TypeCloner(self, module);
            var srcs  = new List<TypeDef> { srcEngine, srcVendor, srcRuntime, srcSign };
            var names = new List<string>  { engine.MakeName(), engine.MakeName(), engine.MakeName(), engine.MakeName() };
            var clones = cloner.CloneTypesShared(srcs, "", names);

            foreach (TypeDef c in clones)
            {
                engine.injectedTypes.Add(c);
                AddMethodsRecursive(c);
            }

            NativeShroud shroud = engine.EnsureShroud(module);

            WireKillProcess(module, clones, cloner, srcRuntime, shroud);

            PatchEnvironmentExitCalls(clones, shroud);

            MethodDef clonedRunGate = FindCloned(cloner, srcRuntime, "RunGateHex");
            MethodDef clonedPause   = FindCloned(cloner, srcRuntime, "PauseExit");
            MethodDef clonedVerify  = FindCloned(cloner, srcRuntime, "Verify");
            MethodDef clonedReap    = FindCloned(cloner, srcRuntime, "Reap");
            if (clonedRunGate == null) return false;

            TypeSig retType = ep.MethodSig.RetType;
            var pars = ep.MethodSig.Params;
            TypeSig[] parr = new TypeSig[pars.Count];
            for (int i = 0; i < pars.Count; i++) parr[i] = pars[i];
            MethodSig wsig = parr.Length > 0
                ? MethodSig.CreateStatic(retType, parr)
                : MethodSig.CreateStatic(retType);

            var wrapper = new MethodDefUser(engine.MakeName(), wsig,
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed | DnMethodImplAttributes.NoInlining,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            var body = new CilBody();
            body.InitLocals = true;
            var il = body.Instructions;
            il.Add(Instruction.Create(DnOpCodes.Ldstr, seedHex));
            il.Add(Instruction.Create(DnOpCodes.Ldstr, alphabet));
            il.Add(Instruction.Create(DnOpCodes.Ldstr, tool));
            il.Add(keepConsole ? Instruction.Create(DnOpCodes.Ldc_I4_1)
                               : Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(alwaysPrompt ? Instruction.Create(DnOpCodes.Ldc_I4_1)
                                : Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(showConsole ? Instruction.Create(DnOpCodes.Ldc_I4_1)
                               : Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Call, clonedRunGate));

            if (clonedVerify != null) il.Add(Instruction.Create(DnOpCodes.Call, clonedVerify));
            if (clonedReap   != null) il.Add(Instruction.Create(DnOpCodes.Call, clonedReap));
            for (int i = 0; i < pars.Count; i++)
                il.Add(LoadArg(i));
            il.Add(Instruction.Create(DnOpCodes.Call, ep));
            if (clonedPause != null)
                il.Add(Instruction.Create(DnOpCodes.Call, clonedPause));
            il.Add(Instruction.Create(DnOpCodes.Ret));
            wrapper.Body = body;

            TypeDef host = ep.DeclaringType ?? modType;
            host.Methods.Add(wrapper);
            engine.injectedMethods.Add(wrapper);

            foreach (CustomAttribute ca in ep.CustomAttributes)
            {
                if (ca == null || ca.AttributeType == null) continue;
                string caName = ca.AttributeType.FullName;
                if (caName == "System.STAThreadAttribute" || caName == "System.MTAThreadAttribute")
                {
                    try { wrapper.CustomAttributes.Add(new CustomAttribute(ca.Constructor)); }
                    catch { }
                }
            }

            if (ep.IsPrivate || ep.IsFamily)
            {
                try { ep.Access = DnMethodAttributes.Assembly; } catch { }
            }

            try { new GateHardenerProtection(engine).EncryptStrings(module, clones, wrapper); }
            catch { }

            try
            {
                if (clonedVerify != null) engine.InjectCallInRandomMethods(module, clonedVerify, 6, 12);
                if (clonedReap   != null) engine.InjectCallInRandomMethods(module, clonedReap,   6, 12);
            }
            catch { }

            try { InjectEntryGuard(ep, clonedVerify, clonedReap); }
            catch { }

            module.EntryPoint = wrapper;
            return true;
        }

        private void InjectEntryGuard(MethodDef ep, MethodDef verify, MethodDef reap)
        {
            if (ep == null || verify == null || reap == null) return;
            if (!ep.HasBody || ep.Body == null) return;
            var il = ep.Body.Instructions;
            if (il.Count == 0) return;
            il.Insert(0, Instruction.Create(DnOpCodes.Call, reap));
            il.Insert(0, Instruction.Create(DnOpCodes.Call, verify));
        }

        private static MethodDef FindCloned(TypeCloner c, TypeDef srcType, string name)
        {
            foreach (MethodDef m in srcType.Methods)
                if (m.Name == name) return c.MapMethod(m);
            return null;
        }

        private static Instruction LoadArg(int i)
        {
            switch (i)
            {
                case 0:  return Instruction.Create(DnOpCodes.Ldarg_0);
                case 1:  return Instruction.Create(DnOpCodes.Ldarg_1);
                case 2:  return Instruction.Create(DnOpCodes.Ldarg_2);
                case 3:  return Instruction.Create(DnOpCodes.Ldarg_3);
                default: return Instruction.Create(DnOpCodes.Ldarg, (ushort)i);
            }
        }

        private void AddMethodsRecursive(TypeDef t)
        {
            foreach (MethodDef m in t.Methods)
                engine.injectedMethods.Add(m);
            foreach (TypeDef n in t.NestedTypes)
                AddMethodsRecursive(n);
        }
    }
}
