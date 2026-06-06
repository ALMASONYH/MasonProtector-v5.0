using System;
using System.Security.Cryptography;
using System.Text;

namespace MasonProtector.Core
{

    internal static class LicenseSign
    {

        internal static readonly byte[] Magic = Utf8("MASNECDS");
        private const int CoordLen = 32;
        private const int SigLen = 64;

        internal static bool IsAsymmetricBlob(byte[] blob)
        {
            if (blob == null || blob.Length < Magic.Length + 1) return false;
            for (int i = 0; i < Magic.Length; i++)
                if (blob[i] != Magic[i]) return false;
            return true;
        }

        internal static byte[] PublicKeyFromBlob(byte[] blob)
        {
            int n = blob.Length - Magic.Length;
            byte[] pub = new byte[n];
            Buffer.BlockCopy(blob, Magic.Length, pub, 0, n);
            return pub;
        }

        internal static byte[] BuildAsymmetricBlob(byte[] publicXY)
        {
            byte[] blob = new byte[Magic.Length + publicXY.Length];
            Buffer.BlockCopy(Magic, 0, blob, 0, Magic.Length);
            Buffer.BlockCopy(publicXY, 0, blob, Magic.Length, publicXY.Length);
            return blob;
        }

        internal static void GenerateKeyPair(out byte[] privateKey, out byte[] publicXY)
        {
            using (ECDsa ec = ECDsa.Create(ECCurve.NamedCurves.nistP256))
            {
                ECParameters p = ec.ExportParameters(true);
                byte[] d = LeftPad(p.D, CoordLen);
                byte[] x = LeftPad(p.Q.X, CoordLen);
                byte[] y = LeftPad(p.Q.Y, CoordLen);
                privateKey = new byte[CoordLen * 3];
                Buffer.BlockCopy(d, 0, privateKey, 0, CoordLen);
                Buffer.BlockCopy(x, 0, privateKey, CoordLen, CoordLen);
                Buffer.BlockCopy(y, 0, privateKey, CoordLen * 2, CoordLen);
                publicXY = new byte[CoordLen * 2];
                Buffer.BlockCopy(x, 0, publicXY, 0, CoordLen);
                Buffer.BlockCopy(y, 0, publicXY, CoordLen, CoordLen);
            }
        }

        internal static byte[] PublicBlobFromPrivate(byte[] privateKey)
        {
            if (privateKey == null || privateKey.Length < CoordLen * 3) return null;
            byte[] xy = new byte[CoordLen * 2];
            Buffer.BlockCopy(privateKey, CoordLen, xy, 0, CoordLen * 2);
            return BuildAsymmetricBlob(xy);
        }

        internal static string Sign(byte[] privateKey, byte[] deviceId, uint expiryDays, string alphabet)
        {
            if (privateKey == null || privateKey.Length < CoordLen * 3) return "";
            byte[] d = new byte[CoordLen], x = new byte[CoordLen], y = new byte[CoordLen];
            Buffer.BlockCopy(privateKey, 0, d, 0, CoordLen);
            Buffer.BlockCopy(privateKey, CoordLen, x, 0, CoordLen);
            Buffer.BlockCopy(privateKey, CoordLen * 2, y, 0, CoordLen);
            using (ECDsa ec = ECDsa.Create())
            {
                var prm = new ECParameters
                {
                    Curve = ECCurve.NamedCurves.nistP256,
                    D = d,
                    Q = new ECPoint { X = x, Y = y }
                };
                ec.ImportParameters(prm);
                byte[] msg = WithExpiry(deviceId, expiryDays);
                byte[] sig = Normalize(ec.SignData(msg, HashAlgorithmName.SHA256), SigLen);

                byte[] keyData = new byte[4 + SigLen];
                keyData[0] = (byte)expiryDays; keyData[1] = (byte)(expiryDays >> 8);
                keyData[2] = (byte)(expiryDays >> 16); keyData[3] = (byte)(expiryDays >> 24);
                Buffer.BlockCopy(sig, 0, keyData, 4, SigLen);
                return Format(Base32Encode(keyData, alphabet));
            }
        }

        internal static bool Verify(byte[] publicXY, byte[] deviceId, string enteredKey, string alphabet)
        {
            try
            {
                if (publicXY == null || publicXY.Length < CoordLen * 2) return false;
                byte[] x = new byte[CoordLen]; byte[] y = new byte[CoordLen];
                Buffer.BlockCopy(publicXY, 0, x, 0, CoordLen);
                Buffer.BlockCopy(publicXY, CoordLen, y, 0, CoordLen);
                byte[] data = Base32Decode(Strip(enteredKey), alphabet);
                if (data == null || data.Length < 4 + SigLen) return false;
                uint expiryDays = (uint)(data[0] | (data[1] << 8) | (data[2] << 16) | (data[3] << 24));
                byte[] sig = new byte[SigLen];
                Buffer.BlockCopy(data, 4, sig, 0, SigLen);
                byte[] msg = WithExpiry(deviceId, expiryDays);
                using (ECDsa ec = ECDsa.Create())
                {
                    var prm = new ECParameters
                    {
                        Curve = ECCurve.NamedCurves.nistP256,
                        Q = new ECPoint { X = x, Y = y }
                    };
                    ec.ImportParameters(prm);
                    if (!ec.VerifyData(msg, sig, HashAlgorithmName.SHA256)) return false;
                }
                if (expiryDays != 0 && NowDays() > expiryDays) return false;
                return true;
            }
            catch { return false; }
        }

        internal static uint GetExpiryDays(string enteredKey, string alphabet)
        {
            try
            {
                byte[] data = Base32Decode(Strip(enteredKey), alphabet);
                if (data == null || data.Length < 4) return 0;
                return (uint)(data[0] | (data[1] << 8) | (data[2] << 16) | (data[3] << 24));
            }
            catch { return 0; }
        }

        internal static uint NowDays()
        {
            return (uint)((long)(DateTime.UtcNow - new DateTime(1970, 1, 1, 0, 0, 0, DateTimeKind.Utc)).TotalDays);
        }

        private static byte[] WithExpiry(byte[] deviceId, uint expiryDays)
        {
            byte[] m = new byte[(deviceId == null ? 0 : deviceId.Length) + 4];
            if (deviceId != null) Buffer.BlockCopy(deviceId, 0, m, 0, deviceId.Length);
            int o = deviceId == null ? 0 : deviceId.Length;
            m[o] = (byte)expiryDays; m[o + 1] = (byte)(expiryDays >> 8);
            m[o + 2] = (byte)(expiryDays >> 16); m[o + 3] = (byte)(expiryDays >> 24);
            return m;
        }

        private static string Format(string s)
        {
            var sb = new StringBuilder();
            for (int i = 0; i < s.Length; i++)
            {
                if (i > 0 && i % 5 == 0) sb.Append('-');
                sb.Append(s[i]);
            }
            return sb.ToString();
        }

        private static string Strip(string key)
        {
            if (key == null) return "";
            var sb = new StringBuilder();
            foreach (char c in key)
            {
                char u = char.ToUpperInvariant(c);
                if (u == '-' || u == ' ' || u == '\t' || u == '\r' || u == '\n') continue;
                if (u == 'O') u = '0';
                if (u == 'I' || u == 'L') u = '1';
                sb.Append(u);
            }
            return sb.ToString();
        }

        private static string Alpha(string alphabet)
        {
            if (alphabet != null && alphabet.Length == 32) return alphabet;
            return LicenseEngine.Canonical;
        }

        private static string Base32Encode(byte[] data, string alphabet)
        {
            string a = Alpha(alphabet);
            var sb = new StringBuilder();
            int buffer = 0, bits = 0;
            for (int i = 0; i < data.Length; i++)
            {
                buffer = (buffer << 8) | data[i];
                bits += 8;
                while (bits >= 5)
                {
                    bits -= 5;
                    sb.Append(a[(buffer >> bits) & 31]);
                }
            }
            if (bits > 0)
                sb.Append(a[(buffer << (5 - bits)) & 31]);
            return sb.ToString();
        }

        private static byte[] Base32Decode(string s, string alphabet)
        {
            string a = Alpha(alphabet);
            int[] map = new int[128];
            for (int i = 0; i < 128; i++) map[i] = -1;
            for (int i = 0; i < a.Length; i++) map[a[i]] = i;

            int buffer = 0, bits = 0;
            var outBytes = new System.Collections.Generic.List<byte>();
            foreach (char c in s)
            {
                if (c >= 128 || map[c] < 0) return null;
                buffer = (buffer << 5) | map[c];
                bits += 5;
                if (bits >= 8)
                {
                    bits -= 8;
                    outBytes.Add((byte)((buffer >> bits) & 0xFF));
                }
            }
            return outBytes.ToArray();
        }

        private static byte[] Normalize(byte[] b, int len)
        {
            if (b == null) return new byte[len];
            if (b.Length == len) return b;
            byte[] r = new byte[len];
            if (b.Length > len) Buffer.BlockCopy(b, b.Length - len, r, 0, len);
            else Buffer.BlockCopy(b, 0, r, len - b.Length, b.Length);
            return r;
        }

        private static byte[] LeftPad(byte[] b, int len)
        {
            if (b != null && b.Length == len) return b;
            byte[] r = new byte[len];
            if (b == null) return r;
            if (b.Length > len) Buffer.BlockCopy(b, b.Length - len, r, 0, len);
            else Buffer.BlockCopy(b, 0, r, len - b.Length, b.Length);
            return r;
        }

        private static byte[] Utf8(string s) { return Encoding.ASCII.GetBytes(s); }
    }
}
