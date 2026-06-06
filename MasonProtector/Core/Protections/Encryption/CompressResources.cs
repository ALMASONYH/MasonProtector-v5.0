using System;
using System.Collections.Generic;
using System.IO;
using System.IO.Compression;
using dnlib.DotNet;
using dnlib.DotNet.Emit;

using DnOpCodes = dnlib.DotNet.Emit.OpCodes;

namespace MasonProtector.Core
{
    internal class CompressResourcesProtection
    {
        private static readonly byte[] Magic = new byte[] { 0xCF, 0xBE, 0xEF, 0xD1 };

        private Obfuscation engine;

        internal CompressResourcesProtection(Obfuscation eng)
        {
            engine = eng;
        }

        internal int Apply(ModuleDef module, TypeDef modType)
        {
            var toCompress = new List<KeyValuePair<EmbeddedResource, byte[]>>();

            foreach (Resource r in module.Resources)
            {
                EmbeddedResource er = r as EmbeddedResource;
                if (er == null) continue;
                if (engine.injectedResources.Contains(er.Name)) continue;

                string rname = er.Name;
                if (rname != null && rname.EndsWith(".resources", StringComparison.OrdinalIgnoreCase))
                    continue;

                byte[] original;
                try
                {
                    using (Stream s = er.CreateReader().AsStream())
                    using (MemoryStream ms = new MemoryStream())
                    {
                        s.CopyTo(ms);
                        original = ms.ToArray();
                    }
                }
                catch { continue; }

                if (original == null || original.Length < 16) continue;

                byte[] deflated = TryDeflate(original);
                if (deflated == null) continue;

                int payloadLen = Magic.Length + 4 + deflated.Length;
                if (payloadLen >= original.Length) continue;

                byte[] payload = new byte[payloadLen];
                Buffer.BlockCopy(Magic, 0, payload, 0, Magic.Length);
                int olen = original.Length;
                payload[4] = (byte)(olen & 0xFF);
                payload[5] = (byte)((olen >> 8) & 0xFF);
                payload[6] = (byte)((olen >> 16) & 0xFF);
                payload[7] = (byte)((olen >> 24) & 0xFF);
                Buffer.BlockCopy(deflated, 0, payload, 8, deflated.Length);

                toCompress.Add(new KeyValuePair<EmbeddedResource, byte[]>(er, payload));
            }

            if (toCompress.Count == 0) return 0;

            MethodDef resolveMethod = CloneResolverRuntime(module);
            if (resolveMethod == null) return 0;

            foreach (var pair in toCompress)
            {
                EmbeddedResource er = pair.Key;
                byte[] payload = pair.Value;
                var replacement = new EmbeddedResource(er.Name, payload, er.Attributes);
                module.Resources.Remove(er);
                module.Resources.Add(replacement);
            }

            PatchGetManifestResourceStream(module, resolveMethod);

            return toCompress.Count;
        }

        private static byte[] TryDeflate(byte[] data)
        {
            try
            {
                using (MemoryStream ms = new MemoryStream())
                {
                    using (DeflateStream ds = new DeflateStream(ms, CompressionMode.Compress, true))
                        ds.Write(data, 0, data.Length);
                    return ms.ToArray();
                }
            }
            catch { return null; }
        }

        private MethodDef CloneResolverRuntime(ModuleDef module)
        {
            string protectorPath = typeof(CompressResourcesProtection).Assembly.Location;
            ModuleDefMD srcModule;
            try { srcModule = ModuleDefMD.Load(protectorPath); }
            catch { return null; }

            TypeDef srcType = srcModule.Find(
                "MasonProtector.Core.RuntimeStubs.CompressResourcesRuntime", false);
            if (srcType == null) return null;

            TypeCloner cloner = new TypeCloner(srcModule, module);
            string helperName = engine.MakeName();
            TypeDef dstType = cloner.CloneType(srcType, "", helperName);
            engine.injectedTypes.Add(dstType);

            MethodDef resolveMethod = dstType.FindMethod("Resolve");

            foreach (MethodDef dm in dstType.Methods)
            {
                engine.injectedMethods.Add(dm);
                if (!dm.IsConstructor && !dm.IsStaticConstructor)
                    dm.Name = engine.MakeName();
            }

            return resolveMethod;
        }

        private void PatchGetManifestResourceStream(ModuleDef module, MethodDef resolver)
        {
            TypeDef helperType = resolver.DeclaringType;
            foreach (TypeDef t in module.GetTypes())
            {
                if (t == helperType) continue;
                if (engine.injectedTypes.Contains(t)) continue;
                foreach (MethodDef m in t.Methods)
                {
                    if (m == null || m.Body == null || !m.Body.HasInstructions) continue;
                    if (engine.injectedMethods.Contains(m)) continue;

                    IList<Instruction> instr = m.Body.Instructions;
                    for (int i = 0; i < instr.Count; i++)
                    {
                        Instruction inst = instr[i];
                        if (inst.OpCode != DnOpCodes.Callvirt && inst.OpCode != DnOpCodes.Call) continue;

                        IMethod op = inst.Operand as IMethod;
                        if (op == null) continue;
                        if (op.Name != "GetManifestResourceStream") continue;

                        ITypeDefOrRef decl = op.DeclaringType;
                        if (decl == null) continue;
                        if (decl.FullName != "System.Reflection.Assembly") continue;

                        MethodSig sig = op.MethodSig;
                        if (sig == null || sig.Params == null || sig.Params.Count != 1) continue;
                        if (sig.Params[0].FullName != "System.String") continue;

                        inst.OpCode = DnOpCodes.Call;
                        inst.Operand = resolver;
                    }
                }
            }
        }
    }
}
