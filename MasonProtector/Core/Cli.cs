using System;
using System.Collections.Generic;
using System.IO;
using System.Reflection;
using System.Runtime.InteropServices;

namespace MasonProtector.Core
{
    internal static class Cli
    {
        [DllImport("kernel32.dll")] private static extern bool AttachConsole(int dwProcessId);
        private const int ATTACH_PARENT_PROCESS = -1;

        internal static void EnsureConsole()
        {
            try { AttachConsole(ATTACH_PARENT_PROCESS); } catch { }
        }

        internal static bool IsCliInvocation(string[] args)
        {
            if (args == null || args.Length == 0) return false;
            string a = args[0];
            return string.Equals(a, "--protect", StringComparison.OrdinalIgnoreCase) ||
                   string.Equals(a, "-p", StringComparison.OrdinalIgnoreCase) ||
                   string.Equals(a, "--vendor-new", StringComparison.OrdinalIgnoreCase) ||
                   string.Equals(a, "--keygen", StringComparison.OrdinalIgnoreCase) ||
                   string.Equals(a, "--keyverify", StringComparison.OrdinalIgnoreCase) ||
                   string.Equals(a, "--deviceid", StringComparison.OrdinalIgnoreCase) ||
                   string.Equals(a, "--keygen-tool", StringComparison.OrdinalIgnoreCase) ||
                   string.Equals(a, "--keyverify-tool", StringComparison.OrdinalIgnoreCase) ||
                   string.Equals(a, "--genkeypair", StringComparison.OrdinalIgnoreCase) ||
                   string.Equals(a, "--keygen-asym", StringComparison.OrdinalIgnoreCase) ||
                   string.Equals(a, "--keyverify-asym", StringComparison.OrdinalIgnoreCase) ||
                   string.Equals(a, "--hwid", StringComparison.OrdinalIgnoreCase) ||
                   string.Equals(a, "--help", StringComparison.OrdinalIgnoreCase) ||
                   string.Equals(a, "-h", StringComparison.OrdinalIgnoreCase);
        }

        internal static int Run(string[] args)
        {
            EnsureConsole();
            try
            {
                if (args.Length == 0 ||
                    string.Equals(args[0], "--help", StringComparison.OrdinalIgnoreCase) ||
                    string.Equals(args[0], "-h", StringComparison.OrdinalIgnoreCase))
                {
                    PrintUsage();
                    return 0;
                }

                string verb = args[0].ToLowerInvariant();
                if (verb == "--vendor-new")  return RunVendorNew(args);
                if (verb == "--keygen")      return RunKeygen(args);
                if (verb == "--keyverify")   return RunKeyverify(args);
                if (verb == "--deviceid")    return RunDeviceId(args);
                if (verb == "--keygen-tool")    return RunKeygenTool(args);
                if (verb == "--keyverify-tool") return RunKeyverifyTool(args);
                if (verb == "--genkeypair")     return RunGenKeyPair(args);
                if (verb == "--keygen-asym")    return RunKeygenAsym(args);
                if (verb == "--keyverify-asym") return RunKeyverifyAsym(args);
                if (verb == "--hwid")        return RunHwid(args);

                if (args.Length < 3)
                {
                    Console.Error.WriteLine("error: --protect requires <input> <output>");
                    PrintUsage();
                    return 2;
                }

                string input = args[1];
                string output = args[2];

                if (!File.Exists(input))
                {
                    Console.Error.WriteLine("error: input not found: " + input);
                    return 2;
                }

                var settings = new ProtectionSettings();
                string preset = "default";
                var overrides = new List<KeyValuePair<string, string>>();

                for (int i = 3; i < args.Length; i++)
                {
                    string a = args[i];
                    if (string.Equals(a, "--preset", StringComparison.OrdinalIgnoreCase) && i + 1 < args.Length)
                    {
                        preset = args[++i];
                    }
                    else if (string.Equals(a, "--config", StringComparison.OrdinalIgnoreCase) && i + 1 < args.Length)
                    {
                        string cfgPath = args[++i];
                        if (File.Exists(cfgPath))
                        {
                            foreach (string raw in File.ReadAllLines(cfgPath))
                            {
                                string line = raw.Trim();
                                if (line.Length == 0 || line[0] == '#' || line[0] == ';') continue;
                                int eq = line.IndexOf('=');
                                if (eq <= 0) continue;
                                overrides.Add(new KeyValuePair<string, string>(
                                    line.Substring(0, eq).Trim(), line.Substring(eq + 1).Trim()));
                            }
                        }
                    }
                    else if (string.Equals(a, "--set", StringComparison.OrdinalIgnoreCase) && i + 1 < args.Length)
                    {
                        string kv = args[++i];
                        int eq = kv.IndexOf('=');
                        if (eq > 0)
                            overrides.Add(new KeyValuePair<string, string>(
                                kv.Substring(0, eq).Trim(), kv.Substring(eq + 1).Trim()));
                    }
                }

                ApplyPreset(settings, preset);
                foreach (var kv in overrides) ApplyOverride(settings, kv.Key, kv.Value);

                if (settings.KeyAuth && settings.KeyAuthAsymmetric &&
                    string.IsNullOrEmpty(settings.KeyAuthPublicKey))
                {
                    byte[] priv, pub;
                    LicenseSign.GenerateKeyPair(out priv, out pub);
                    settings.KeyAuthPublicKey = LicenseEngine.ToHex(LicenseSign.BuildAsymmetricBlob(pub));
                    string keyFile = output + ".vendor-private.txt";
                    try
                    {
                        File.WriteAllText(keyFile,
                            "MASON ASYMMETRIC VENDOR PRIVATE KEY - KEEP SECRET\r\n" +
                            "private=" + LicenseEngine.ToHex(priv) + "\r\n" +
                            "public=" + settings.KeyAuthPublicKey + "\r\n\r\n" +
                            "Issue a key for a customer device with:\r\n" +
                            "  MasonProtector --keygen-asym <private> <deviceId>\r\n");
                        Console.Out.WriteLine("  Asymmetric keypair generated -> private key saved to: " + keyFile);
                        Console.Out.WriteLine("  KEEP THAT FILE SECRET. It is the only way to issue keys and is NEVER embedded.");
                    }
                    catch { }
                }

                var engine = new Obfuscation();
                string lastStatus = "";
                engine.PerformProtection(input, output, settings,
                    s => { if (!string.IsNullOrEmpty(s) && s != lastStatus) { lastStatus = s; Console.Out.WriteLine("  " + s); } },
                    v => { });

                if (!File.Exists(output))
                {
                    Console.Error.WriteLine("error: protection produced no output file");
                    return 1;
                }

                long inLen = new FileInfo(input).Length;
                long outLen = new FileInfo(output).Length;
                Console.Out.WriteLine("ok: " + output + "  (" + inLen + " -> " + outLen + " bytes)");
                return 0;
            }
            catch (Exception ex)
            {
                Console.Error.WriteLine("fatal: " + ex.GetType().Name + ": " + ex.Message);
                var inner = ex.InnerException;
                int depth = 0;
                while (inner != null && depth < 6)
                {
                    Console.Error.WriteLine("  -> " + inner.GetType().Name + ": " + inner.Message);
                    inner = inner.InnerException;
                    depth++;
                }
                return 1;
            }
        }

        private static int RunVendorNew(string[] args)
        {
            if (args.Length < 3) { Console.Error.WriteLine("usage: --vendor-new <vendorFingerprint> <outProfile>"); return 2; }
            string fingerprint = args[1];
            string outPath = args[2];
            var vendor = LicenseEngine.CreateVendor(System.Text.Encoding.UTF8.GetBytes(fingerprint));
            File.WriteAllText(outPath, vendor.Export());
            Console.Out.WriteLine("vendor profile written: " + outPath);
            Console.Out.WriteLine("alphabet: " + vendor.Alphabet);
            return 0;
        }

        private static int RunKeygen(string[] args)
        {
            if (args.Length < 3) { Console.Error.WriteLine("usage: --keygen <profile> <deviceId>"); return 2; }
            var vendor = LoadVendor(args[1]);
            if (vendor == null) { Console.Error.WriteLine("error: cannot load vendor profile"); return 2; }
            byte[] dev = LicenseEngine.ResolveDeviceId(args[2]);
            Console.Out.WriteLine(LicenseEngine.GenerateKey(dev, vendor));
            return 0;
        }

        private static int RunKeyverify(string[] args)
        {
            if (args.Length < 4) { Console.Error.WriteLine("usage: --keyverify <profile> <deviceId> <key>"); return 2; }
            var vendor = LoadVendor(args[1]);
            if (vendor == null) { Console.Error.WriteLine("error: cannot load vendor profile"); return 2; }
            byte[] dev = LicenseEngine.ResolveDeviceId(args[2]);
            bool ok = LicenseEngine.ValidateKey(dev, vendor, args[3]);
            Console.Out.WriteLine(ok ? "VALID" : "INVALID");
            return ok ? 0 : 1;
        }

        private static int RunDeviceId(string[] args)
        {
            if (args.Length < 2) { Console.Error.WriteLine("usage: --deviceid <rawFingerprint>"); return 2; }
            byte[] dev = LicenseEngine.CanonicalizeDeviceId(args[1]);
            Console.Out.WriteLine(LicenseEngine.FormatDeviceId(dev));
            return 0;
        }

        private static int RunKeygenTool(string[] args)
        {
            if (args.Length < 4) { Console.Error.WriteLine("usage: --keygen-tool <toolName> <password> <deviceId>"); return 2; }
            var vendor = LicenseEngine.CreateVendorFromCredentials(args[1], args[2], null);
            byte[] dev = LicenseEngine.ResolveDeviceId(args[3]);
            Console.Out.WriteLine(LicenseEngine.GenerateKey(dev, vendor));
            return 0;
        }

        private static int RunKeyverifyTool(string[] args)
        {
            if (args.Length < 5) { Console.Error.WriteLine("usage: --keyverify-tool <toolName> <password> <deviceId> <key>"); return 2; }
            var vendor = LicenseEngine.CreateVendorFromCredentials(args[1], args[2], null);
            byte[] dev = LicenseEngine.ResolveDeviceId(args[3]);
            bool ok = LicenseEngine.ValidateKey(dev, vendor, args[4]);
            Console.Out.WriteLine(ok ? "VALID" : "INVALID");
            return ok ? 0 : 1;
        }

        private static int RunGenKeyPair(string[] args)
        {
            byte[] priv, pub;
            LicenseSign.GenerateKeyPair(out priv, out pub);
            byte[] blob = LicenseSign.BuildAsymmetricBlob(pub);
            Console.Out.WriteLine("private: " + LicenseEngine.ToHex(priv));
            Console.Out.WriteLine("public:  " + LicenseEngine.ToHex(blob));
            return 0;
        }

        private static int RunKeygenAsym(string[] args)
        {
            if (args.Length < 3) { Console.Error.WriteLine("usage: --keygen-asym <privateHex> <deviceId> [durationDays] [alphabet]"); return 2; }
            var vendor = new VendorProfile { PrivateKey = LicenseEngine.FromHex(args[1]) };
            int durDays = 0;
            if (args.Length > 3) int.TryParse(args[3], out durDays);
            if (durDays != 0) { long e = (long)LicenseSign.NowDays() + durDays; vendor.ExpiryDays = (uint)(e < 1 ? 1 : e); }
            vendor.Alphabet = args.Length > 4 ? args[4] : null;
            byte[] dev = LicenseEngine.ResolveDeviceId(args[2]);
            Console.Out.WriteLine(LicenseEngine.GenerateKey(dev, vendor));
            return 0;
        }

        private static int RunKeyverifyAsym(string[] args)
        {
            if (args.Length < 4) { Console.Error.WriteLine("usage: --keyverify-asym <publicBlobHex> <deviceId> <key> [alphabet]"); return 2; }
            var vendor = new VendorProfile { Seed = LicenseEngine.FromHex(args[1]) };
            vendor.Alphabet = args.Length > 4 ? args[4] : null;
            byte[] dev = LicenseEngine.ResolveDeviceId(args[2]);
            bool ok = LicenseEngine.ValidateKey(dev, vendor, args[3]);
            Console.Out.WriteLine(ok ? "VALID" : "INVALID");
            return ok ? 0 : 1;
        }

        private static int RunHwid(string[] args)
        {
            string raw = LicenseRuntime.GatherRawFingerprint();
            byte[] dev = LicenseEngine.CanonicalizeDeviceId(raw);
            Console.Out.WriteLine("fingerprint: " + raw);
            Console.Out.WriteLine("deviceid:    " + LicenseEngine.FormatDeviceId(dev));
            return 0;
        }

        private static VendorProfile LoadVendor(string path)
        {
            try { return File.Exists(path) ? VendorProfile.Import(File.ReadAllText(path)) : null; }
            catch { return null; }
        }

        private static void ApplyPreset(ProtectionSettings s, string preset)
        {
            switch ((preset ?? "default").ToLowerInvariant())
            {
                case "none":
                    break;
                case "max":
                case "maximum":
                    s.MaximumEncryption = true;
                    break;
                case "hide":
                    ApplyHidePreset(s);
                    break;
                case "all":
                    ApplyAll(s, true);
                    break;
                case "default":
                default:
                    s.EnableRenamer = true;
                    s.RenameNamespaces = true;
                    s.SeparateNamespacePerClass = true;
                    s.RenameTypes = true;
                    s.RenameMethods = true;
                    s.RenameFields = true;
                    s.RenameProperties = true;
                    s.RenameEvents = true;
                    s.StringEncryption = true;
                    s.IntEncoding = true;
                    s.ControlFlow = true;
                    break;
            }
        }

        private static void ApplyAll(ProtectionSettings s, bool value)
        {
            foreach (var pi in typeof(ProtectionSettings).GetProperties())
            {
                if (pi.PropertyType != typeof(bool) || !pi.CanWrite) continue;
                if (pi.Name == "MaximumEncryption" || pi.Name == "HideEncryption" ||
                    pi.Name == "HiddenRename" || pi.Name == "ExportCodeToDll" ||
                    pi.Name == "EncryptFormResources" ||
                    pi.Name == "AntiDebugAggressive" ||
                    pi.Name.StartsWith("KeyAuth") ||
                    pi.Name.StartsWith("AntiCrack")) continue;
                pi.SetValue(s, value, null);
            }
        }

        private static void ApplyHidePreset(ProtectionSettings s)
        {
            string[] on =
            {
                "EnableRenamer","RenameNamespaces","RenameTypes","RenameMethods","RenameFields",
                "RenameProperties","RenameEvents","HiddenRename",
                "IntEncoding","ConstantsEncoding","FieldEncryption","CrossReferenceEncryption","MutationEncoding",
                "ProxyCalls","ReferenceProxy","CallHiding","CalliConversion","DelegateEncryption",
                "ControlFlow","ControlFlowFlattening2","BranchConfusion","OpaquePredicates","NumericObfuscation",
                "Local2Field","MethodInliner","MethodScattering","HideMethods",
                "AntiTamper","AntiDebug","AntiDump",
            };
            foreach (string n in on) SetBool(s, n, true);
        }

        private static void SetBool(ProtectionSettings s, string name, bool value)
        {
            var pi = typeof(ProtectionSettings).GetProperty(name, BindingFlags.Public | BindingFlags.Instance);
            if (pi != null && pi.PropertyType == typeof(bool) && pi.CanWrite)
                pi.SetValue(s, value, null);
        }

        private static void ApplyOverride(ProtectionSettings s, string name, string value)
        {
            var pi = typeof(ProtectionSettings).GetProperty(name, BindingFlags.Public | BindingFlags.Instance);
            if (pi == null || !pi.CanWrite) return;
            try
            {
                if (pi.PropertyType == typeof(bool))
                {
                    bool b = value == "1" || value.Equals("true", StringComparison.OrdinalIgnoreCase) ||
                             value.Equals("on", StringComparison.OrdinalIgnoreCase) ||
                             value.Equals("yes", StringComparison.OrdinalIgnoreCase);
                    pi.SetValue(s, b, null);
                }
                else if (pi.PropertyType == typeof(int))
                {
                    int n;
                    if (int.TryParse(value, out n)) pi.SetValue(s, n, null);
                }
                else if (pi.PropertyType == typeof(string))
                {
                    pi.SetValue(s, value, null);
                }
            }
            catch { }
        }

        private static void PrintUsage()
        {
            Console.Out.WriteLine("Mason Protector - command line");
            Console.Out.WriteLine("usage: MasonProtector --protect <input> <output> [options]");
            Console.Out.WriteLine("  --preset <none|default|max|hide|all>   base protection set");
            Console.Out.WriteLine("  --set <Option=value>                   override a single option (repeatable)");
            Console.Out.WriteLine("  --config <file>                        read Option=value lines from a file");
            Console.Out.WriteLine("license tooling:");
            Console.Out.WriteLine("  --vendor-new <fingerprint> <outProfile>   create an editable vendor key-map profile");
            Console.Out.WriteLine("  --keygen <profile> <deviceId>             generate a machine-bound license key");
            Console.Out.WriteLine("  --keyverify <profile> <deviceId> <key>    validate a license key");
            Console.Out.WriteLine("  --deviceid <rawFingerprint>               show the canonical device id");
            Console.Out.WriteLine("  --hwid                                     show this machine's fingerprint + device id");
        }
    }
}
