using System;
using System.Security.Cryptography;
using System.Text;

namespace MasonProtector.Core
{
    internal sealed class VendorProfile
    {
        public byte[] Seed;
        public string Alphabet;

        public byte[] PrivateKey;

        public uint ExpiryDays;

        public string Export()
        {
            var sb = new StringBuilder();
            sb.AppendLine("MASON-VENDOR-1");
            sb.AppendLine("seed=" + LicenseEngine.ToHex(Seed));
            sb.AppendLine("alphabet=" + Alphabet);
            return sb.ToString();
        }

        public static VendorProfile Import(string text)
        {
            if (string.IsNullOrEmpty(text)) return null;
            byte[] seed = null;
            string alphabet = null;
            foreach (string raw in text.Replace("\r", "").Split('\n'))
            {
                string line = raw.Trim();
                if (line.Length == 0 || line[0] == '#') continue;
                int eq = line.IndexOf('=');
                if (eq <= 0) continue;
                string k = line.Substring(0, eq).Trim();
                string v = line.Substring(eq + 1).Trim();
                if (k == "seed") seed = LicenseEngine.FromHex(v);
                else if (k == "alphabet") alphabet = v;
            }
            if (seed == null || seed.Length == 0) return null;
            if (!LicenseEngine.IsValidAlphabet(alphabet))
                alphabet = LicenseEngine.DeriveAlphabet(seed);
            return new VendorProfile { Seed = seed, Alphabet = alphabet };
        }
    }

    internal static class LicenseEngine
    {
        internal const string Canonical = "0123456789ABCDEFGHJKMNPQRSTVWXYZ";
        private const ulong P = 2305843009213693951UL;
        private const int Rounds = 9;
        private const int PayloadDigits = 12;
        private const int CheckDigits = 4;

        internal static VendorProfile CreateVendor(byte[] vendorFingerprint)
        {
            byte[] seed = Hash(Concat(vendorFingerprint ?? new byte[0], Utf8("MASON-VENDOR-SEED-v1")));
            return new VendorProfile { Seed = seed, Alphabet = DeriveAlphabet(seed) };
        }

        private const int CredIterations = 100000;

        internal static byte[] DeriveSeedFromCredentials(string toolName, string password)
        {
            byte[] salt = Hash(Concat(
                Utf8(toolName == null ? "" : toolName.Trim()),
                Utf8("MASON-TOOL-KEYAUTH-SALT-v1")));
            byte[] secret = Concat(Utf8(password ?? ""), Utf8("MASON-TOOL-PEPPER-v1"));
            try
            {
                using (var kdf = new Rfc2898DeriveBytes(secret, salt, CredIterations, HashAlgorithmName.SHA256))
                    return kdf.GetBytes(32);
            }
            catch (MissingMethodException)
            {
                using (var kdf = new Rfc2898DeriveBytes(secret, salt, CredIterations))
                    return kdf.GetBytes(32);
            }
        }

        internal static VendorProfile CreateVendorFromCredentials(string toolName, string password, string customAlphabet)
        {
            byte[] seed = DeriveSeedFromCredentials(toolName, password);
            string alpha = IsValidAlphabet(customAlphabet) ? customAlphabet : DeriveAlphabet(seed);
            return new VendorProfile { Seed = seed, Alphabet = alpha };
        }

        internal static byte[] CanonicalizeDeviceId(string rawFingerprint)
        {
            byte[] h = Hash(Utf8(rawFingerprint ?? ""));
            byte[] id = new byte[16];
            Buffer.BlockCopy(h, 0, id, 0, 16);
            return id;
        }

        internal static byte[] CanonicalizeDeviceIdBytes(byte[] rawFingerprint)
        {
            byte[] h = Hash(rawFingerprint ?? new byte[0]);
            byte[] id = new byte[16];
            Buffer.BlockCopy(h, 0, id, 0, 16);
            return id;
        }

        internal static string FormatDeviceId(byte[] id)
        {
            var sb = new StringBuilder();
            for (int i = 0; i < id.Length; i++)
            {
                sb.Append(Canonical[id[i] & 31]);
                sb.Append(Canonical[(id[i] >> 3) & 31]);
                if ((i + 1) % 4 == 0 && i + 1 < id.Length) sb.Append('-');
            }
            return sb.ToString();
        }

        internal static byte[] ParseDeviceId(string display)
        {
            if (display == null) return null;
            var sb = new StringBuilder();
            foreach (char ch in display)
            {
                char c = char.ToUpperInvariant(ch);
                if (c == '-' || c == ' ' || c == '\t' || c == '\r' || c == '\n') continue;
                if (c == 'O') c = '0';
                if (c == 'I' || c == 'L') c = '1';
                if (Canonical.IndexOf(c) < 0) return null;
                sb.Append(c);
            }
            if (sb.Length != 32) return null;
            byte[] id = new byte[16];
            for (int i = 0; i < 16; i++)
            {
                int low = Canonical.IndexOf(sb[i * 2]);
                int high = Canonical.IndexOf(sb[i * 2 + 1]);
                id[i] = (byte)((low & 7) | (high << 3));
            }
            return id;
        }

        internal static byte[] ResolveDeviceId(string input)
        {
            byte[] parsed = ParseDeviceId(input);
            if (parsed != null) return parsed;
            return CanonicalizeDeviceId(input);
        }

        internal static string GenerateKey(byte[] deviceId, VendorProfile vendor)
        {

            if (vendor != null && vendor.PrivateKey != null && vendor.PrivateKey.Length > 0)
                return LicenseSign.Sign(vendor.PrivateKey, deviceId, vendor.ExpiryDays, vendor.Alphabet);

            int[] digits = ComputeDigits(deviceId, vendor);
            string alpha = (vendor.Alphabet != null && vendor.Alphabet.Length == 32) ? vendor.Alphabet : Canonical;
            var sb = new StringBuilder();
            for (int i = 0; i < digits.Length; i++)
            {
                sb.Append(alpha[digits[i] & 31]);
                if ((i + 1) % 4 == 0 && i + 1 < digits.Length) sb.Append('-');
            }
            return sb.ToString();
        }

        internal static bool ValidateKey(byte[] deviceId, VendorProfile vendor, string enteredKey)
        {
            if (vendor == null || deviceId == null) return false;

            if (vendor.Seed != null && LicenseSign.IsAsymmetricBlob(vendor.Seed))
                return LicenseSign.Verify(LicenseSign.PublicKeyFromBlob(vendor.Seed),
                                          deviceId, enteredKey, vendor.Alphabet);

            string expected = GenerateKey(deviceId, vendor);
            string a = Normalize(expected, vendor);
            string b = Normalize(enteredKey, vendor);
            if (a == null || b == null) return false;
            return ConstantTimeEquals(a, b);
        }

        private static int[] ComputeDigits(byte[] deviceId, VendorProfile vendor)
        {
            byte[] seed = vendor.Seed;
            byte[] h1 = Hmac(seed, deviceId);
            byte[] h2 = Hmac(h1, Concat(deviceId, seed, Utf8("MASON-LIC-BIND-v1")));

            ulong acc = ReadU64(h2, 0) % P;
            for (int r = 0; r < Rounds; r++)
            {
                ulong a = ReadU64(Hmac(seed, Utf8("A" + r)), 0) % P;
                if (a < 2) a += 2;
                ulong c = ReadU64(Hmac(seed, Utf8("C" + r)), 0) % P;
                ulong x = ReadU64(Hmac(h1, Utf8("X" + r)), 0) % P;
                acc = (MulMod(acc, a, P) + c) % P;
                acc ^= (x & 0x0FFFFFFFFFFFFFFFUL);
                acc %= P;
            }

            ulong payload = acc & ((1UL << 60) - 1);
            int[] sbox = DerivePermutation(Hash(Concat(seed, Utf8("SBOX"))), 32);

            int[] payDigits = new int[PayloadDigits];
            int prev = (int)(ReadU64(h2, 8) & 31);
            for (int i = 0; i < PayloadDigits; i++)
            {
                int v = (int)((payload >> (5 * i)) & 31);
                v = (v + prev + i) & 31;
                v = sbox[v];
                payDigits[i] = v;
                prev = v;
            }

            byte[] csInput = new byte[PayloadDigits + deviceId.Length];
            for (int i = 0; i < PayloadDigits; i++) csInput[i] = (byte)payDigits[i];
            Buffer.BlockCopy(deviceId, 0, csInput, PayloadDigits, deviceId.Length);
            byte[] cs = Hmac(seed, csInput);

            int[] all = new int[PayloadDigits + CheckDigits];
            Array.Copy(payDigits, all, PayloadDigits);
            for (int i = 0; i < CheckDigits; i++)
                all[PayloadDigits + i] = sbox[(cs[i] + cs[i + CheckDigits]) & 31];
            return all;
        }

        private static string Normalize(string key, VendorProfile vendor)
        {
            if (key == null) return null;
            string alpha = (vendor.Alphabet != null && vendor.Alphabet.Length == 32) ? vendor.Alphabet : Canonical;
            var sb = new StringBuilder();
            foreach (char ch in key)
            {
                char c = char.ToUpperInvariant(ch);
                if (c == '-' || c == ' ' || c == '\t' || c == '\r' || c == '\n') continue;
                if (c == 'O') c = '0';
                if (c == 'I' || c == 'L') c = '1';
                if (alpha.IndexOf(c) < 0) return null;
                sb.Append(c);
            }
            return sb.ToString();
        }

        internal static string DeriveAlphabet(byte[] seed)
        {
            int[] perm = DerivePermutation(Hash(Concat(seed, Utf8("ALPHABET"))), 32);
            var chars = new char[32];
            for (int i = 0; i < 32; i++) chars[i] = Canonical[perm[i]];
            return new string(chars);
        }

        internal static bool IsValidAlphabet(string a)
        {
            if (a == null || a.Length != 32) return false;
            var seen = new bool[128];
            foreach (char c in a)
            {
                if (Canonical.IndexOf(c) < 0) return false;
                if (c >= 128 || seen[c]) return false;
                seen[c] = true;
            }
            return true;
        }

        private static int[] DerivePermutation(byte[] seedHash, int n)
        {
            int[] perm = new int[n];
            for (int i = 0; i < n; i++) perm[i] = i;
            byte[] stream = seedHash;
            int si = 0;
            for (int i = n - 1; i > 0; i--)
            {
                if (si + 4 > stream.Length) { stream = Hash(stream); si = 0; }
                uint r = (uint)((stream[si] << 24) | (stream[si + 1] << 16) | (stream[si + 2] << 8) | stream[si + 3]);
                si += 4;
                int j = (int)(r % (uint)(i + 1));
                int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
            }
            return perm;
        }

        private static ulong MulMod(ulong a, ulong b, ulong p)
        {
            ulong x0 = (uint)a, x1 = a >> 32;
            ulong y0 = (uint)b, y1 = b >> 32;
            ulong p00 = x0 * y0;
            ulong p01 = x0 * y1;
            ulong p10 = x1 * y0;
            ulong p11 = x1 * y1;
            ulong middle = p10 + (p00 >> 32) + (uint)p01;
            ulong lo = (middle << 32) | (uint)p00;
            ulong hi = p11 + (middle >> 32) + (p01 >> 32);

            ulong loRed = (lo & p) + (lo >> 61);
            ulong sum = loRed + (hi << 3);
            sum = (sum & p) + (sum >> 61);
            if (sum >= p) sum -= p;
            return sum;
        }

        private static ulong ReadU64(byte[] b, int offset)
        {
            ulong v = 0;
            for (int i = 0; i < 8; i++) v = (v << 8) | b[(offset + i) % b.Length];
            return v;
        }

        private static bool ConstantTimeEquals(string a, string b)
        {
            if (a.Length != b.Length) return false;
            int diff = 0;
            for (int i = 0; i < a.Length; i++) diff |= a[i] ^ b[i];
            return diff == 0;
        }

        private static byte[] Hash(byte[] data)
        {
            using (var sha = SHA256.Create()) return sha.ComputeHash(data);
        }

        private static byte[] Hmac(byte[] key, byte[] data)
        {
            using (var h = new HMACSHA256(key.Length == 0 ? new byte[1] : key)) return h.ComputeHash(data);
        }

        private static byte[] Utf8(string s) { return Encoding.UTF8.GetBytes(s ?? ""); }

        private static byte[] Concat(params byte[][] parts)
        {
            int len = 0;
            foreach (var p in parts) len += p.Length;
            byte[] r = new byte[len];
            int o = 0;
            foreach (var p in parts) { Buffer.BlockCopy(p, 0, r, o, p.Length); o += p.Length; }
            return r;
        }

        internal static string ToHex(byte[] b)
        {
            var sb = new StringBuilder(b.Length * 2);
            foreach (byte x in b) sb.Append(x.ToString("x2"));
            return sb.ToString();
        }

        internal static byte[] FromHex(string s)
        {

            if (string.IsNullOrEmpty(s) || (s.Length & 1) != 0) return new byte[0];
            byte[] r = new byte[s.Length / 2];
            for (int i = 0; i < r.Length; i++)
            {
                int hi = HexVal(s[i * 2]);
                int lo = HexVal(s[i * 2 + 1]);
                if (hi < 0 || lo < 0) return new byte[0];
                r[i] = (byte)((hi << 4) | lo);
            }
            return r;
        }

        private static int HexVal(char c)
        {
            if (c >= '0' && c <= '9') return c - '0';
            if (c >= 'a' && c <= 'f') return c - 'a' + 10;
            if (c >= 'A' && c <= 'F') return c - 'A' + 10;
            return -1;
        }
    }
}
