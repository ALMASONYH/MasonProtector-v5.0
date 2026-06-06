using System;
using System.Net.NetworkInformation;
using System.Runtime.InteropServices;
using System.Text;
using Microsoft.Win32;

namespace MasonProtector.Core
{
    internal static class LicenseRuntime
    {
        internal static void KillProcess()
        {
            try { System.Diagnostics.Process.GetCurrentProcess().Kill(); } catch { }
            try { Environment.FailFast(""); } catch { }
        }

        internal static string GatherRawFingerprint()
        {
            var sb = new StringBuilder();
            Append(sb, "MN", SafeMachineName());
            Append(sb, "PC", SafeProcessorCount());
            Append(sb, "OS", SafeOsVersion());
            Append(sb, "MG", SafeMachineGuid());
            Append(sb, "PA", SafeProcessorArchitecture());
            Append(sb, "MA", SafePrimaryMac());
            return sb.ToString();
        }

        internal static byte[] DeviceId()
        {
            return LicenseEngine.CanonicalizeDeviceId(GatherRawFingerprint());
        }

        internal static string DeviceIdDisplay()
        {
            return LicenseEngine.FormatDeviceId(DeviceId());
        }

        internal static void RunGateHex(string seedHex, string alphabet, string toolName, int keepConsole, int alwaysPrompt, int showConsole)
        {
            try
            {
                byte[] seed = LicenseEngine.FromHex(seedHex ?? "");
                byte[] dev = DeviceId();
                VendorProfile vendor = new VendorProfile();
                vendor.Seed = seed;
                vendor.Alphabet = alphabet ?? "";

                string baseDir;
                try { baseDir = Environment.GetFolderPath(Environment.SpecialFolder.ApplicationData); }
                catch { baseDir = "."; }
                string dir = System.IO.Path.Combine(System.IO.Path.Combine(baseDir, "MasonLicense"), SanitizeName(toolName));
                try { System.IO.Directory.CreateDirectory(dir); } catch { }
                string keyPath = System.IO.Path.Combine(dir, "license.key");

                GuardClock(dir, toolName);

                if (alwaysPrompt == 0 && System.IO.File.Exists(keyPath))
                {
                    string existing = null;
                    try { existing = System.IO.File.ReadAllText(keyPath); } catch { }
                    if (!string.IsNullOrEmpty(existing) && LicenseEngine.ValidateKey(dev, vendor, existing))
                    {
                        RecordValid(dev, seed, alphabet ?? "", existing);
                        return;
                    }
                }

                if (showConsole == 0)
                {
                    RunGuiGate(dev, vendor, toolName, keyPath, alwaysPrompt);
                    return;
                }

                EnsureConsole();
                string disp = LicenseEngine.FormatDeviceId(dev);
                string tn = string.IsNullOrEmpty(toolName) ? "This program" : toolName;

                for (int attempt = 0; attempt < 5; attempt++)
                {
                    try
                    {
                        Console.WriteLine();
                        Console.WriteLine("==================================================");
                        Console.WriteLine("   " + tn + " - license activation");
                        Console.WriteLine("==================================================");
                        Console.WriteLine();
                        Console.WriteLine("   This copy is not activated on this machine.");
                        Console.WriteLine();
                        Console.WriteLine("   Your device ID:");
                        Console.WriteLine("      " + disp);
                        Console.WriteLine();
                        Console.WriteLine("   Send this ID to the vendor to receive your license key.");
                        Console.Write("   Enter license key (leave blank to exit): ");
                    }
                    catch { }

                    string entered = null;
                    try { entered = Console.ReadLine(); } catch { }

                    if (entered == null || entered.Trim().Length == 0)
                    {
                        try { Console.WriteLine("   No key entered. Exiting."); } catch { }
                        KillProcess();
                    }

                    if (LicenseEngine.ValidateKey(dev, vendor, entered))
                    {
                        if (alwaysPrompt == 0)
                            try { System.IO.File.WriteAllText(keyPath, entered.Trim()); } catch { }
                        try
                        {
                            Console.WriteLine();
                            Console.WriteLine("   Activated. Starting " + tn + "...");
                            Console.WriteLine();
                        }
                        catch { }
                        RecordValid(dev, seed, alphabet ?? "", entered);
                        MaybeHideConsole(keepConsole);
                        return;
                    }

                    try
                    {
                        Console.WriteLine();
                        Console.WriteLine("   Invalid key for this machine. Please try again.");
                    }
                    catch { }
                }

                try { Console.WriteLine("   Too many invalid attempts. Exiting."); } catch { }
                KillProcess();
            }
            catch { }
        }

        private static void RunGuiGate(byte[] dev, VendorProfile vendor, string toolName, string keyPath, int alwaysPrompt)
        {
            string disp = LicenseEngine.FormatDeviceId(dev);
            string tn = string.IsNullOrEmpty(toolName) ? "This program" : toolName;
            try { System.Windows.Forms.Clipboard.SetText(disp); } catch { }

            for (int attempt = 0; attempt < 5; attempt++)
            {
                string entered = null;
                bool confirmed = false;
                try { confirmed = ShowKeyDialog(tn, disp, attempt, out entered); }
                catch { entered = null; confirmed = false; }

                if (!confirmed || entered == null || entered.Trim().Length == 0)
                    KillProcess();

                if (LicenseEngine.ValidateKey(dev, vendor, entered))
                {
                    if (alwaysPrompt == 0)
                        try { System.IO.File.WriteAllText(keyPath, entered.Trim()); } catch { }
                    RecordValid(dev, vendor.Seed, vendor.Alphabet, entered);
                    return;
                }
            }
            KillProcess();
        }

        private static bool ShowKeyDialog(string tn, string disp, int attempt, out string entered)
        {
            entered = null;
            System.Windows.Forms.Form form = new System.Windows.Forms.Form();
            form.Text = tn + " - Activation";
            form.FormBorderStyle = System.Windows.Forms.FormBorderStyle.FixedDialog;
            form.StartPosition = System.Windows.Forms.FormStartPosition.CenterScreen;
            form.ClientSize = new System.Drawing.Size(474, 236);
            form.MaximizeBox = false;
            form.MinimizeBox = false;
            form.ShowInTaskbar = true;
            form.TopMost = true;

            System.Windows.Forms.Label lbl = new System.Windows.Forms.Label();
            lbl.Text = (attempt > 0 ? "Invalid key for this machine. Please try again.\r\n\r\n" : "")
                + "This copy is not activated on this machine.\r\nYour device ID (copied to clipboard) - send it to the vendor:";
            lbl.SetBounds(14, 12, 446, 52);
            form.Controls.Add(lbl);

            System.Windows.Forms.TextBox txtDev = new System.Windows.Forms.TextBox();
            txtDev.Text = disp;
            txtDev.ReadOnly = true;
            txtDev.TabStop = false;
            txtDev.SetBounds(14, 68, 446, 22);
            form.Controls.Add(txtDev);

            System.Windows.Forms.Label lblKey = new System.Windows.Forms.Label();
            lblKey.Text = "Enter your license key:";
            lblKey.SetBounds(14, 100, 446, 18);
            form.Controls.Add(lblKey);

            System.Windows.Forms.TextBox txtKey = new System.Windows.Forms.TextBox();
            txtKey.SetBounds(14, 120, 446, 22);
            form.Controls.Add(txtKey);

            System.Windows.Forms.Button btnOk = new System.Windows.Forms.Button();
            btnOk.Text = "Activate";
            btnOk.DialogResult = System.Windows.Forms.DialogResult.OK;
            btnOk.SetBounds(280, 172, 88, 30);
            form.Controls.Add(btnOk);

            System.Windows.Forms.Button btnQuit = new System.Windows.Forms.Button();
            btnQuit.Text = "Quit";
            btnQuit.DialogResult = System.Windows.Forms.DialogResult.Cancel;
            btnQuit.SetBounds(374, 172, 88, 30);
            form.Controls.Add(btnQuit);

            form.AcceptButton = btnOk;
            form.CancelButton = btnQuit;

            System.Windows.Forms.DialogResult r = form.ShowDialog();
            entered = txtKey.Text;
            form.Dispose();
            return r == System.Windows.Forms.DialogResult.OK;
        }

        internal static void PauseExit()
        {
            try
            {
                if (GetConsoleWindow() == IntPtr.Zero) return;
                try
                {
                    Console.WriteLine();
                    Console.Write("Press Enter to close...");
                }
                catch { }
                try { Console.ReadLine(); } catch { }
            }
            catch { }
        }

        private static void EnsureConsole()
        {
            try
            {
                if (GetConsoleWindow() == IntPtr.Zero)
                {
                    AllocConsole();
                    _consoleAllocated = true;
                    try
                    {
                        var so = new System.IO.StreamWriter(Console.OpenStandardOutput());
                        so.AutoFlush = true;
                        Console.SetOut(so);
                        Console.SetIn(new System.IO.StreamReader(Console.OpenStandardInput()));
                    }
                    catch { }
                }
            }
            catch { }
        }

        [DllImport("kernel32.dll")] private static extern bool AllocConsole();
        [DllImport("kernel32.dll")] private static extern bool FreeConsole();
        [DllImport("kernel32.dll")] private static extern IntPtr GetConsoleWindow();

        private static bool _consoleAllocated = false;

        internal static int _p0;
        internal static int _p1;
        internal static int _p2;

        internal static byte[] _sDev;
        internal static byte[] _sSeed;
        internal static string _sAlpha;
        internal static string _sKey;

        internal static void Verify()
        {
            try
            {
                bool ok = false;
                if (_sDev != null && _sSeed != null && _sKey != null)
                {
                    VendorProfile v = new VendorProfile();
                    v.Seed = _sSeed;
                    v.Alphabet = _sAlpha ?? "";
                    ok = LicenseEngine.ValidateKey(_sDev, v, _sKey);
                }
                if (!ok)
                {
                    _p0 = (_p0 | 0x55) + 1;
                    _p1 = (_p1 ^ 0xAA) | 1;
                    _p2 = ~_p2 + 1;
                }
            }
            catch
            {
                _p0 = (_p0 | 0x55) + 1;
                _p1 = (_p1 ^ 0xAA) | 1;
                _p2 = ~_p2 + 1;
            }
        }

        internal static void Reap()
        {
            try
            {
                if (_p0 != 0) { KillProcess(); return; }
                if (_p1 != 0) { KillProcess(); return; }
                if (_p2 != 0) { KillProcess(); return; }
            }
            catch { KillProcess(); }
        }

        private static void RecordValid(byte[] dev, byte[] seed, string alpha, string key)
        {
            _sDev = dev;
            _sSeed = seed;
            _sAlpha = alpha;
            _sKey = key;
        }

        private static void MaybeHideConsole(int keepConsole)
        {
            try
            {
                if (keepConsole == 0 && _consoleAllocated)
                {
                    FreeConsole();
                    _consoleAllocated = false;
                }
            }
            catch { }
        }

        private static uint NowDays()
        {
            try { return (uint)((long)(DateTime.UtcNow - new DateTime(1970, 1, 1, 0, 0, 0, DateTimeKind.Utc)).TotalDays); }
            catch { return 0; }
        }

        private static void GuardClock(string dir, string toolName)
        {
            try
            {
                uint now = NowDays();
                if (now == 0) return;
                uint stored = 0;
                string tp = System.IO.Path.Combine(dir, ".ts");
                try { uint v; if (uint.TryParse((System.IO.File.ReadAllText(tp) ?? "").Trim(), out v) && v > stored) stored = v; }
                catch { }
                string regName = "h" + (SanitizeName(toolName).GetHashCode() & 0x7fffffff).ToString("x");
                try
                {
                    using (RegistryKey k = Registry.CurrentUser.OpenSubKey(@"Software\Mason\State"))
                    {
                        if (k != null)
                        {
                            object o = k.GetValue(regName);
                            uint v;
                            if (o != null && uint.TryParse(o.ToString(), out v) && v > stored) stored = v;
                        }
                    }
                }
                catch { }
                if (stored > 2 && now + 2 < stored)
                {
                    KillProcess();
                }
                uint nw = now > stored ? now : stored;
                try { System.IO.File.WriteAllText(tp, nw.ToString()); } catch { }
                try
                {
                    using (RegistryKey k = Registry.CurrentUser.CreateSubKey(@"Software\Mason\State"))
                    { if (k != null) k.SetValue(regName, nw.ToString()); }
                }
                catch { }
            }
            catch { }
        }

        private static string SanitizeName(string s)
        {
            if (string.IsNullOrEmpty(s)) return "app";
            var sb = new StringBuilder();
            foreach (char c in s)
            {
                if (char.IsLetterOrDigit(c) || c == '-' || c == '_' || c == ' ') sb.Append(c);
            }
            string r = sb.ToString().Trim();
            return r.Length == 0 ? "app" : r;
        }

        private static void Append(StringBuilder sb, string tag, string value)
        {
            if (sb.Length > 0) sb.Append('|');
            sb.Append(tag).Append(':').Append(value ?? "");
        }

        private static string SafeMachineName()
        {
            try { return Environment.MachineName ?? ""; } catch { return ""; }
        }

        private static string SafeProcessorCount()
        {
            try { return Environment.ProcessorCount.ToString(); } catch { return "0"; }
        }

        private static string SafeOsVersion()
        {
            try { return Environment.OSVersion.Version.ToString(); } catch { return ""; }
        }

        private static string SafeProcessorArchitecture()
        {
            try
            {
                string a = Environment.GetEnvironmentVariable("PROCESSOR_ARCHITEW6432");
                if (string.IsNullOrEmpty(a))
                    a = Environment.GetEnvironmentVariable("PROCESSOR_ARCHITECTURE");
                string b = Environment.GetEnvironmentVariable("PROCESSOR_IDENTIFIER");
                return (a ?? "") + ";" + (b ?? "");
            }
            catch { return ""; }
        }

        private static string SafeMachineGuid()
        {
            try
            {
                using (RegistryKey baseKey = RegistryKey.OpenBaseKey(RegistryHive.LocalMachine, RegistryView.Registry64))
                using (RegistryKey k = baseKey.OpenSubKey(@"SOFTWARE\Microsoft\Cryptography"))
                {
                    if (k != null)
                    {
                        object v = k.GetValue("MachineGuid");
                        if (v != null) return v.ToString();
                    }
                }
            }
            catch { }
            return "";
        }

        private static string SafePrimaryMac()
        {
            try
            {
                string best = "";
                long bestSpeed = -1;
                foreach (NetworkInterface ni in NetworkInterface.GetAllNetworkInterfaces())
                {
                    if (ni == null) continue;
                    if (ni.NetworkInterfaceType == NetworkInterfaceType.Loopback) continue;
                    if (ni.NetworkInterfaceType == NetworkInterfaceType.Tunnel) continue;
                    byte[] mac = ni.GetPhysicalAddress().GetAddressBytes();
                    if (mac == null || mac.Length == 0) continue;
                    long speed = -1;
                    try { speed = ni.Speed; } catch { }
                    string hex = LicenseEngine.ToHex(mac);
                    if (speed > bestSpeed) { bestSpeed = speed; best = hex; }
                }
                return best;
            }
            catch { return ""; }
        }
    }
}
