using System;
using System.IO;
using System.IO.Compression;
using System.Reflection;

namespace MasonProtector.Core.RuntimeStubs
{
    internal static class CompressResourcesRuntime
    {
        internal static Stream Resolve(Assembly asm, string name)
        {
            Stream raw = asm != null ? asm.GetManifestResourceStream(name) : null;
            if (raw == null) return null;
            byte[] buf;
            using (raw)
            using (MemoryStream tmp = new MemoryStream())
            {
                raw.CopyTo(tmp);
                buf = tmp.ToArray();
            }
            if (buf.Length < 8 || buf[0] != 0xCF || buf[1] != 0xBE || buf[2] != 0xEF || buf[3] != 0xD1)
                return new MemoryStream(buf, false);
            int olen = buf[4] | (buf[5] << 8) | (buf[6] << 16) | (buf[7] << 24);
            if (olen < 0) olen = 0;
            byte[] inflated = new byte[olen];
            int pos = 0;
            using (MemoryStream msIn = new MemoryStream(buf, 8, buf.Length - 8, false))
            using (DeflateStream ds = new DeflateStream(msIn, CompressionMode.Decompress))
            {
                while (pos < inflated.Length)
                {
                    int n = ds.Read(inflated, pos, inflated.Length - pos);
                    if (n <= 0) break;
                    pos += n;
                }
            }
            return new MemoryStream(inflated, 0, pos, false, false);
        }
    }
}
