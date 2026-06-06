using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Diagnostics;
using System.Drawing;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Runtime.InteropServices;
using System.Text;
using System.Windows.Forms;
using MasonProtector.Core;

namespace MasonProtector
{
    [DesignerCategory("Code")]
    public class Builder : Form
    {

        private IContainer components;
        private HtmlView MASON_appView;
        private AppBridge MASON_bridge;

        private readonly ProtectionSettings _settings = new ProtectionSettings();
        private readonly Obfuscation _engine = new Obfuscation();
        private string _selectedFile = "";
        private readonly List<string> _libPaths = new List<string>();
        private readonly List<bool> _libChecked = new List<bool>();

        [DllImport("user32.dll")] private static extern bool ReleaseCapture();
        [DllImport("user32.dll")] private static extern int  SendMessage(IntPtr h, int msg, int wParam, int lParam);
        private const int WM_NCLBUTTONDOWN = 0xA1;
        private const int HTCAPTION        = 0x2;

        private const int CS_DROPSHADOW = 0x00020000;
        protected override CreateParams CreateParams
        {
            get
            {
                var cp = base.CreateParams;
                cp.ClassStyle |= CS_DROPSHADOW;
                return cp;
            }
        }

        public Builder()
        {
            Theme.Load();
            BuildUi();
            BuildBridge();
            LoadHtml();

            Theme.AccentChanged += PushAccentToHtml;
        }

        protected override void Dispose(bool disposing)
        {
            if (disposing && components != null) components.Dispose();
            base.Dispose(disposing);
        }

        private void BuildUi()
        {
            this.components = new Container();
            this.SuspendLayout();
            this.AutoScaleMode = AutoScaleMode.None;
            this.ClientSize = new Size(1180, 760);
            this.FormBorderStyle = FormBorderStyle.None;
            this.Text = "Mason Protector";
            this.BackColor = Theme.Background;
            this.ForeColor = Theme.Text;
            this.Font = new Font("Segoe UI", 9F);
            this.StartPosition = FormStartPosition.CenterScreen;
            this.DoubleBuffered = true;
            this.MinimumSize = new Size(900, 600);

            try
            {
                Icon appIcon = Icon.ExtractAssociatedIcon(Application.ExecutablePath);
                if (appIcon != null) this.Icon = appIcon;
            }
            catch { }

            this.FormBorderStyle = FormBorderStyle.None;

            MASON_appView = new HtmlView { Dock = DockStyle.Fill };
            this.Controls.Add(MASON_appView);

            this.ResumeLayout(false);
        }

        private void BuildBridge()
        {
            MASON_bridge = new AppBridge
            {
                OnWindowDrag     = () => { ReleaseCapture(); SendMessage(Handle, WM_NCLBUTTONDOWN, HTCAPTION, 0); },
                OnWindowMinimize = () => { WindowState = FormWindowState.Minimized; },
                OnWindowMaximize = () =>
                {
                    WindowState = WindowState == FormWindowState.Maximized
                        ? FormWindowState.Normal
                        : FormWindowState.Maximized;
                },
                OnWindowClose    = () => Application.Exit(),

                OnSetBoolOption  = SetBoolOption,
                OnSetIntOption   = SetIntOption,
                OnSetTextOption  = SetTextOption,
                OnSetEnableAll   = SetEnableAll,
                OnSetOptionLevel = (name, lvl) => _settings.SetLevel(name, lvl),

                OnAuthGetDeviceId     = AuthDeviceId,
                OnAuthGenerateKey     = AuthGenerateKey,
                OnAuthGetVendorMap    = AuthGetVendorMap,
                OnAuthSaveVendorMap   = AuthSaveVendorMap,
                OnAuthRegenVendorMap  = AuthRegenVendor,
                OnAuthExportVendorMap = AuthExportVendorMap,
                OnAuthListKeys        = AuthListKeys,
                OnAuthIssueKey        = AuthIssueKey,
                OnAuthRemoveKey       = AuthRemoveKey,
                OnAuthVerifyKey       = AuthVerifyKey,
                OnAuthGetCredentials  = AuthGetCredentials,
                OnAuthSetCredentials  = AuthSetCredentials,
                OnAuthGenKeyPair      = AuthGenKeyPair,
                OnAuthSignAsym        = AuthSignAsym,
                OnAuthIssueTimed      = AuthIssueTimed,

                OnBrowse         = OpenBrowse,
                OnProtect        = DoProtect,
                OnScanLibraries  = DoScanLibraries,
                OnToggleLibrary  = (idx, chk) =>
                {
                    if (idx >= 0 && idx < _libChecked.Count) _libChecked[idx] = chk;
                },

                OnPickColor      = PickColorDialog,
                OnResetTheme     = () => Theme.SetAccent(Color.FromArgb(102, 192, 244)),
                OnApplyColor     = (r, g, b) => Theme.SetAccent(Color.FromArgb(r, g, b)),

                OnLog            = msg => { try { Debug.WriteLine("[HTML] " + msg); } catch { } },

                OnScanTarget     = ScanTargetJson,
                OnSetExcluded    = SetSymbolExcluded,

                OnOpenUrl        = OpenExternalUrl,
            };
            MASON_appView.RegisterBridge(MASON_bridge);
        }

        private void LoadHtml()
        {
            string html = BuildHtml();
            if (string.IsNullOrEmpty(html))
            {
                MessageBox.Show(this, "AppPage.html not found in resources.", "Mason Protector",
                    MessageBoxButtons.OK, MessageBoxIcon.Error);
                return;
            }
            MASON_appView.DocumentReady += (s, e) => PushInitialState();
            MASON_appView.LoadHtml(html);
        }

        private string BuildHtml()
        {
            string html = ReadEmbedded("AppPage.html");
            if (string.IsNullOrEmpty(html)) return null;
            return html
                .Replace("{{ACCENT}}",      ToHex(Theme.Accent))
                .Replace("{{ACCENT_DARK}}", ToHex(Theme.AccentDark))
                .Replace("{{ACCENT_R}}",    Theme.Accent.R.ToString())
                .Replace("{{ACCENT_G}}",    Theme.Accent.G.ToString())
                .Replace("{{ACCENT_B}}",    Theme.Accent.B.ToString())
                .Replace("{{BG}}",          ToHex(Theme.Background))
                .Replace("{{LOGO_BASE64}}", Logo.GetBase64Png(64));
        }

        private void PushInitialState()
        {
            foreach (var pi in typeof(ProtectionSettings).GetProperties())
            {
                if (!pi.CanRead) continue;
                object v = pi.GetValue(_settings, null);
                if (pi.PropertyType == typeof(bool))
                    MASON_appView.InvokeJs("setOption", pi.Name, (bool)v);
                else if (pi.PropertyType == typeof(int))
                    MASON_appView.InvokeJs("setNumeric", pi.Name, (int)v);
                else if (pi.PropertyType == typeof(string))
                    MASON_appView.InvokeJs("setText", pi.Name, (string)v ?? "");
            }
            MASON_appView.InvokeJs("setFilePath", _selectedFile);
            MASON_appView.InvokeJs("setStatus", "Idle.");
        }

        private void PushAccentToHtml()
        {
            if (MASON_appView == null) return;

            string html = BuildHtml();
            if (string.IsNullOrEmpty(html)) return;
            MASON_appView.LoadHtml(html);
        }

        private void ShowToast(string title, string body, string type)
        {
            if (MASON_appView == null) return;
            try { MASON_appView.InvokeJs("showToast", title ?? "", body ?? "", type ?? "info"); }
            catch { }
        }
        private void SetLoading(bool visible, string text, string sub)
        {
            if (MASON_appView == null) return;
            try { MASON_appView.InvokeJs("setLoading", visible, text ?? "", sub ?? ""); }
            catch { }
        }

        private void SetBoolOption(string name, bool value)
        {
            var pi = typeof(ProtectionSettings).GetProperty(name, BindingFlags.Public | BindingFlags.Instance);
            if (pi != null && pi.PropertyType == typeof(bool) && pi.CanWrite)
                pi.SetValue(_settings, value, null);

            if (name == "AntiCrack" && value)
            {

                string[] companions = new string[]
                {
                    "AntiDebug",
                    "AntiTamper",
                    "AntiDump",
                    "AntiDe4dot",
                    "AntiILDasm",
                };
                foreach (string c in companions)
                {
                    var cpi = typeof(ProtectionSettings).GetProperty(c, BindingFlags.Public | BindingFlags.Instance);
                    if (cpi == null || cpi.PropertyType != typeof(bool) || !cpi.CanWrite) continue;
                    cpi.SetValue(_settings, true, null);
                    SyncToggleToHtml(c, true);
                }
            }

            if (name == "MaximumEncryption" && value)
            {

                var hidePi = typeof(ProtectionSettings).GetProperty("HideEncryption", BindingFlags.Public | BindingFlags.Instance);
                if (hidePi != null) hidePi.SetValue(_settings, false, null);
                SyncToggleToHtml("HideEncryption", false);
                if (MASON_appView != null) try { MASON_appView.InvokeJs("setEnableAllChecked", false); } catch {  }

                string[] maxEncStack = new string[]
                {

                    "EnableRenamer", "RenameNamespaces", "SeparateNamespacePerClass",
                    "RenameTypes", "RenameMethods", "RenameFields", "RenameProperties", "RenameEvents",

                    "StringEncryption", "IntEncoding", "ConstantsEncoding",
                    "FieldEncryption", "PolymorphicEncryption",
                    "StringComposition",
                    "RuntimeEncryption", "MethodBodyEncryption", "DelegateEncryption",
                    "ResourceProtection",

                    "ControlFlow", "ControlFlowFlattening2", "BranchConfusion",
                    "OpaquePredicates", "NumericObfuscation",

                    "ProxyCalls", "ReferenceProxy", "CallHiding", "CalliConversion",
                    "Local2Field", "MethodInliner",

                    "JunkCode", "DnSpyCrasher",
                    "HideMethods", "FakeAttributes", "Watermark", "DecompilerPoison",
                    "HideDesignerCode", "EntryPointMover",

                    "AntiTamper", "AntiDump",
                    "AntiDe4dot", "AntiILDasm",

                };
                foreach (string c in maxEncStack)
                {
                    var cpi = typeof(ProtectionSettings).GetProperty(c, BindingFlags.Public | BindingFlags.Instance);
                    if (cpi == null || cpi.PropertyType != typeof(bool) || !cpi.CanWrite) continue;
                    cpi.SetValue(_settings, true, null);
                    SyncToggleToHtml(c, true);
                }
            }

            if (name == "HideEncryption" && value)
            {

                var maxPi = typeof(ProtectionSettings).GetProperty("MaximumEncryption", BindingFlags.Public | BindingFlags.Instance);
                if (maxPi != null) maxPi.SetValue(_settings, false, null);
                SyncToggleToHtml("MaximumEncryption", false);
                if (MASON_appView != null) try { MASON_appView.InvokeJs("setEnableAllChecked", false); } catch {  }

                string[] hideStack = new string[]
                {

                    "EnableRenamer", "RenameNamespaces", "RenameTypes",
                    "RenameMethods", "RenameFields", "RenameProperties", "RenameEvents",
                    "HiddenRename",

                    "IntEncoding", "ConstantsEncoding", "FieldEncryption",
                    "CrossReferenceEncryption", "MutationEncoding",

                    "ProxyCalls", "ReferenceProxy", "CallHiding", "CalliConversion",
                    "DelegateEncryption",

                    "ControlFlow", "ControlFlowFlattening2", "BranchConfusion",
                    "OpaquePredicates", "NumericObfuscation",
                    "Local2Field", "MethodInliner", "MethodScattering",
                    "HideMethods",

                    "AntiTamper", "AntiDebug", "AntiDump", "AntiHook", "AntiHttp",
                    "AntiMemoryDump", "AntiVM",
                };
                foreach (string c in hideStack)
                {
                    var cpi = typeof(ProtectionSettings).GetProperty(c, BindingFlags.Public | BindingFlags.Instance);
                    if (cpi == null || cpi.PropertyType != typeof(bool) || !cpi.CanWrite) continue;
                    cpi.SetValue(_settings, true, null);
                    SyncToggleToHtml(c, true);
                }

                string[] noisy = new string[]
                {

                    "StringEncryption",

                    "Watermark", "FakeAttributes", "DecompilerPoison", "DnSpyCrasher",
                    "AntiILDasm", "AntiDe4dot", "InvalidMetadata", "TokenConfusion",
                    "JunkCode", "StackUnderflow", "TypeScrambler",

                    "MaximumEncryption", "SeparateNamespacePerClass",
                };
                foreach (string c in noisy)
                {
                    var cpi = typeof(ProtectionSettings).GetProperty(c, BindingFlags.Public | BindingFlags.Instance);
                    if (cpi == null || cpi.PropertyType != typeof(bool) || !cpi.CanWrite) continue;
                    cpi.SetValue(_settings, false, null);
                    SyncToggleToHtml(c, false);
                }
            }
        }

        private void SyncToggleToHtml(string name, bool value)
        {
            if (MASON_appView == null) return;
            try { MASON_appView.InvokeJs("setOption", name, value); } catch { }
        }
        private void SetIntOption(string name, int value)
        {
            var pi = typeof(ProtectionSettings).GetProperty(name, BindingFlags.Public | BindingFlags.Instance);
            if (pi != null && pi.PropertyType == typeof(int) && pi.CanWrite)
                pi.SetValue(_settings, value, null);
        }
        private void SetTextOption(string name, string value)
        {
            var pi = typeof(ProtectionSettings).GetProperty(name, BindingFlags.Public | BindingFlags.Instance);
            if (pi != null && pi.PropertyType == typeof(string) && pi.CanWrite)
                pi.SetValue(_settings, value ?? "", null);
        }
        private void SetEnableAll(bool value)
        {

            if (value)
            {
                var maxPi = typeof(ProtectionSettings).GetProperty("MaximumEncryption", BindingFlags.Public | BindingFlags.Instance);
                if (maxPi != null) maxPi.SetValue(_settings, false, null);
                var hidePi = typeof(ProtectionSettings).GetProperty("HideEncryption", BindingFlags.Public | BindingFlags.Instance);
                if (hidePi != null) hidePi.SetValue(_settings, false, null);
                SyncToggleToHtml("MaximumEncryption", false);
                SyncToggleToHtml("HideEncryption", false);
            }

            foreach (var pi in typeof(ProtectionSettings).GetProperties())
            {
                if (pi.PropertyType != typeof(bool) || !pi.CanWrite) continue;
                if (pi.Name == "MaximumEncryption") continue;
                if (pi.Name == "HideEncryption") continue;
                if (pi.Name == "HiddenRename") continue;
                if (pi.Name == "ExportCodeToDll") continue;

                if (pi.Name.StartsWith("KeyAuth")) continue;
                if (pi.Name == "EncryptFormResources") continue;
                if (pi.Name == "AntiDebugAggressive") continue;
                if (pi.Name.StartsWith("AntiCrack")) continue;
                pi.SetValue(_settings, value, null);
            }
            PushInitialState();
        }

        private void OpenBrowse()
        {
            using (var ofd = new OpenFileDialog())
            {
                ofd.Filter = "Executable Files (*.exe)|*.exe|DLL Files (*.dll)|*.dll|All Files (*.*)|*.*";
                if (ofd.ShowDialog(this) == DialogResult.OK)
                {
                    _selectedFile = ofd.FileName;

                    _engine.userExcluded.Clear();
                    MASON_appView.InvokeJs("setFilePath", _selectedFile);
                    MASON_appView.InvokeJs("setStatus", "File selected.");
                    try { MASON_appView.InvokeJs("onFileSelected"); } catch { }
                }
            }
        }

        private string ScanTargetJson()
        {
            if (string.IsNullOrEmpty(_selectedFile) || !File.Exists(_selectedFile))
                return "{\"error\":\"no-target\"}";

            try
            {
                var sb = new StringBuilder();
                sb.Append("{\"namespaces\":[");

                using (var mod = dnlib.DotNet.ModuleDefMD.Load(_selectedFile))
                {
                    var nsBuckets = new SortedDictionary<string, List<dnlib.DotNet.TypeDef>>(StringComparer.Ordinal);
                    foreach (var t in mod.GetTypes())
                    {
                        if (t == null) continue;
                        if (t.IsGlobalModuleType) continue;
                        string tn = ((object)t.Name == null) ? "" : t.Name.String;
                        if (string.IsNullOrEmpty(tn) || tn == "<Module>") continue;
                        if (tn.StartsWith("<", StringComparison.Ordinal)) continue;
                        if (t.IsSpecialName || t.IsRuntimeSpecialName) continue;
                        try { if (_engine.IsCompilerGenerated(t)) continue; } catch { }
                        string ns = ((object)t.Namespace == null) ? "" : t.Namespace.String;
                        List<dnlib.DotNet.TypeDef> list;
                        if (!nsBuckets.TryGetValue(ns, out list))
                            nsBuckets[ns] = list = new List<dnlib.DotNet.TypeDef>();
                        list.Add(t);
                    }

                    bool firstNs = true;
                    foreach (var nsKv in nsBuckets)
                    {
                        if (!firstNs) sb.Append(',');
                        firstNs = false;
                        string nsName = nsKv.Key ?? "";
                        sb.Append("{\"name\":").Append(JsonStr(string.IsNullOrEmpty(nsName) ? "(global)" : nsName));
                        sb.Append(",\"key\":").Append(JsonStr("ns:" + nsName));
                        sb.Append(",\"excluded\":").Append(_engine.userExcluded.Contains("ns:" + nsName) ? "true" : "false");
                        sb.Append(",\"types\":[");
                        bool firstT = true;
                        var typeList = nsKv.Value;
                        typeList.Sort((a, b) => string.CompareOrdinal(((object)a.Name == null) ? "" : a.Name.String,
                                                                     ((object)b.Name == null) ? "" : b.Name.String));
                        foreach (var t in typeList)
                        {
                            string typeFullName = t.FullName ?? "";
                            string typeName = ((object)t.Name == null) ? typeFullName : t.Name.String;
                            if (!firstT) sb.Append(',');
                            firstT = false;
                            sb.Append("{\"name\":").Append(JsonStr(typeName));
                            sb.Append(",\"key\":").Append(JsonStr(typeFullName));
                            sb.Append(",\"excluded\":").Append(_engine.userExcluded.Contains(typeFullName) ? "true" : "false");
                            sb.Append(",\"methods\":[");
                            bool firstM = true;
                            var methodList = new List<dnlib.DotNet.MethodDef>();
                            if (t.Methods != null)
                            {
                                foreach (var m in t.Methods)
                                {
                                    if (m == null) continue;
                                    if (m.IsRuntimeSpecialName) continue;
                                    if (m.IsConstructor) continue;
                                    string mn = ((object)m.Name == null) ? "" : m.Name.String;
                                    if (string.IsNullOrEmpty(mn)) continue;
                                    if (mn.StartsWith("<", StringComparison.Ordinal)) continue;
                                    if (m.IsPinvokeImpl || m.IsAbstract || m.IsSpecialName) continue;
                                    methodList.Add(m);
                                }
                                methodList.Sort((a, b) => string.CompareOrdinal(((object)a.Name == null) ? "" : a.Name.String,
                                                                                ((object)b.Name == null) ? "" : b.Name.String));
                            }
                            foreach (var m in methodList)
                            {
                                string mFullName = m.FullName ?? "";
                                string mName = ((object)m.Name == null) ? mFullName : m.Name.String;
                                int paramCount = (m.MethodSig != null && m.MethodSig.Params != null) ? m.MethodSig.Params.Count : 0;
                                string sig = mName + "(" + paramCount + ")";
                                if (!firstM) sb.Append(',');
                                firstM = false;
                                sb.Append("{\"name\":").Append(JsonStr(sig));
                                sb.Append(",\"key\":").Append(JsonStr(mFullName));
                                sb.Append(",\"excluded\":").Append(_engine.userExcluded.Contains(mFullName) ? "true" : "false");
                                sb.Append("}");
                            }
                            sb.Append("]}");
                        }
                        sb.Append("]}");
                    }
                }

                sb.Append("]}");
                return sb.ToString();
            }
            catch (Exception ex)
            {
                return "{\"error\":" + JsonStr(ex.GetType().Name + ": " + ex.Message) + "}";
            }
        }

        private void SetSymbolExcluded(string fullName, bool excluded)
        {
            if (string.IsNullOrEmpty(fullName)) return;
            if (excluded) _engine.userExcluded.Add(fullName);
            else          _engine.userExcluded.Remove(fullName);
            DiagLog("SetExcluded: name=\"" + fullName + "\" excluded=" + excluded +
                    " set.Count=" + _engine.userExcluded.Count);
        }

        private static string AuthDir()
        {
            string d = Path.Combine(
                Environment.GetFolderPath(Environment.SpecialFolder.ApplicationData), "MasonProtector");
            try { Directory.CreateDirectory(d); } catch { }
            return d;
        }
        private static string CredsPath()  { return Path.Combine(AuthDir(), "vendor.creds"); }
        private static string KeysPath()    { return Path.Combine(AuthDir(), "issued.keys"); }

        private void LoadCreds(out string tool, out string pass, out string alpha)
        {
            tool = ""; pass = ""; alpha = "";
            try
            {
                if (!File.Exists(CredsPath())) return;
                foreach (var raw in File.ReadAllLines(CredsPath()))
                {
                    string line = raw;
                    int eq = line.IndexOf('=');
                    if (eq <= 0) continue;
                    string k = line.Substring(0, eq);
                    string val = line.Substring(eq + 1);
                    if (k == "tool") tool = Unescape(val);
                    else if (k == "pass") pass = Unescape(val);
                    else if (k == "alphabet") alpha = val.Trim();
                }
            }
            catch { }
        }
        private void SaveCreds(string tool, string pass, string alpha)
        {
            try
            {
                var sb = new StringBuilder();
                sb.Append("tool=").Append(Escape(tool ?? "")).Append("\r\n");
                sb.Append("pass=").Append(Escape(pass ?? "")).Append("\r\n");
                sb.Append("alphabet=").Append(Core.LicenseEngine.IsValidAlphabet(alpha) ? alpha : "").Append("\r\n");
                File.WriteAllText(CredsPath(), sb.ToString());
            }
            catch { }
        }
        private static string Escape(string s)
        {
            return (s ?? "").Replace("\\", "\\\\").Replace("\r", "\\r").Replace("\n", "\\n");
        }
        private static string Unescape(string s)
        {
            if (string.IsNullOrEmpty(s)) return "";
            var sb = new StringBuilder(s.Length);
            for (int i = 0; i < s.Length; i++)
            {
                if (s[i] == '\\' && i + 1 < s.Length)
                {
                    char n = s[++i];
                    if (n == 'r') sb.Append('\r');
                    else if (n == 'n') sb.Append('\n');
                    else if (n == '\\') sb.Append('\\');
                    else sb.Append(n);
                }
                else sb.Append(s[i]);
            }
            return sb.ToString();
        }

        private Core.VendorProfile LoadOrCreateVendor()
        {
            string tool, pass, alpha;
            LoadCreds(out tool, out pass, out alpha);
            return Core.LicenseEngine.CreateVendorFromCredentials(tool, pass, alpha);
        }

        private string AuthDeviceId()
        {
            try { return Core.LicenseRuntime.DeviceIdDisplay(); } catch { return ""; }
        }
        private string AuthGenerateKey(string deviceId)
        {
            if (string.IsNullOrEmpty(deviceId)) return "";
            try
            {
                var v = LoadOrCreateVendor();
                byte[] dev = Core.LicenseEngine.ResolveDeviceId(deviceId.Trim());
                return Core.LicenseEngine.GenerateKey(dev, v);
            }
            catch (Exception ex) { return "error: " + ex.Message; }
        }
        private string AuthGenKeyPair()
        {
            try
            {
                byte[] priv, pub;
                Core.LicenseSign.GenerateKeyPair(out priv, out pub);
                byte[] blob = Core.LicenseSign.BuildAsymmetricBlob(pub);
                string privHex = Core.LicenseEngine.ToHex(priv);
                string pubHex  = Core.LicenseEngine.ToHex(blob);
                return "{\"private\":\"" + privHex + "\",\"public\":\"" + pubHex + "\"}";
            }
            catch (Exception ex) { return "{\"error\":\"" + ex.Message.Replace("\"", "'") + "\"}"; }
        }
        private string AuthSignAsym(string privateHex, string deviceId)
        {
            if (string.IsNullOrEmpty(privateHex) || string.IsNullOrEmpty(deviceId)) return "";
            try
            {
                var v = new Core.VendorProfile { PrivateKey = Core.LicenseEngine.FromHex(privateHex.Trim()) };
                byte[] dev = Core.LicenseEngine.ResolveDeviceId(deviceId.Trim());
                return Core.LicenseEngine.GenerateKey(dev, v);
            }
            catch (Exception ex) { return "error: " + ex.Message; }
        }
        private string AuthGetVendorMap()
        {
            try { return LoadOrCreateVendor().Export(); } catch (Exception ex) { return "error: " + ex.Message; }
        }
        private string AuthSaveVendorMap(string text)
        {
            string alphaLine = null;
            foreach (var raw in (text ?? "").Replace("\r", "").Split('\n'))
            {
                string line = raw.Trim();
                if (line.StartsWith("alphabet=")) alphaLine = line.Substring("alphabet=".Length).Trim();
            }
            if (alphaLine == null) return "error: no alphabet= line found";
            if (!Core.LicenseEngine.IsValidAlphabet(alphaLine))
                return "error: alphabet must be a 32-symbol permutation of " + Core.LicenseEngine.Canonical;
            string tool, pass, oldAlpha;
            LoadCreds(out tool, out pass, out oldAlpha);
            SaveCreds(tool, pass, alphaLine);
            return "ok: vendor map saved";
        }
        private string AuthRegenVendor()
        {
            try
            {
                string tool, pass, alpha;
                LoadCreds(out tool, out pass, out alpha);
                SaveCreds(tool, pass, "");
                return LoadOrCreateVendor().Export();
            }
            catch (Exception ex) { return "error: " + ex.Message; }
        }
        private string AuthGetCredentials()
        {
            string tool, pass, alpha;
            LoadCreds(out tool, out pass, out alpha);
            return "{\"tool\":" + JsonStr(tool) + ",\"pass\":" + JsonStr(pass) + "}";
        }
        private string AuthSetCredentials(string tool, string pass)
        {
            string oldTool, oldPass, alpha;
            LoadCreds(out oldTool, out oldPass, out alpha);
            if ((tool ?? "") != (oldTool ?? "") || (pass ?? "") != (oldPass ?? "")) alpha = "";
            SaveCreds(tool ?? "", pass ?? "", alpha);
            return LoadOrCreateVendor().Export();
        }
        private string AuthExportVendorMap()
        {
            try
            {
                using (var sfd = new SaveFileDialog())
                {
                    sfd.Filter = "Vendor profile (*.profile)|*.profile|Text file (*.txt)|*.txt";
                    sfd.FileName = "vendor.profile";
                    if (sfd.ShowDialog(this) == DialogResult.OK)
                    {
                        File.WriteAllText(sfd.FileName, LoadOrCreateVendor().Export());
                        return "ok: exported to " + sfd.FileName;
                    }
                }
            }
            catch (Exception ex) { return "error: " + ex.Message; }
            return "cancelled";
        }
        private string AuthListKeys()
        {
            var sb = new StringBuilder("[");
            try
            {
                if (File.Exists(KeysPath()))
                {
                    bool first = true;
                    foreach (var line in File.ReadAllLines(KeysPath()))
                    {
                        if (string.IsNullOrWhiteSpace(line)) continue;
                        var p = line.Split('\t');
                        if (p.Length < 3) continue;
                        if (!first) sb.Append(',');
                        first = false;
                        sb.Append("{\"device\":").Append(JsonStr(p[0]))
                          .Append(",\"label\":").Append(JsonStr(p[1]))
                          .Append(",\"key\":").Append(JsonStr(p[2]))
                          .Append(",\"date\":").Append(JsonStr(p.Length > 3 ? p[3] : ""))
                          .Append(",\"duration\":").Append(JsonStr(p.Length > 4 ? p[4] : ""))
                          .Append(",\"expiry\":").Append(JsonStr(p.Length > 5 ? p[5] : ""))
                          .Append('}');
                    }
                }
            }
            catch { }
            sb.Append(']');
            return sb.ToString();
        }
        private string AuthIssueKey(string deviceId, string label)
        {
            if (string.IsNullOrEmpty(deviceId)) return "";
            try
            {
                var v = LoadOrCreateVendor();
                byte[] dev = Core.LicenseEngine.ResolveDeviceId(deviceId.Trim());
                string key = Core.LicenseEngine.GenerateKey(dev, v);
                string line = deviceId.Trim() + "\t" + (label ?? "").Replace('\t', ' ').Replace('\r', ' ').Replace('\n', ' ')
                            + "\t" + key + "\t" + DateTime.Now.ToString("yyyy-MM-dd HH:mm");
                File.AppendAllText(KeysPath(), line + "\r\n");
                return "{\"key\":" + JsonStr(key) + "}";
            }
            catch (Exception ex) { return "{\"error\":" + JsonStr(ex.Message) + "}"; }
        }

        private string AuthIssueTimed(string deviceId, string label, string durationDays, string privateHex)
        {
            if (string.IsNullOrEmpty(deviceId)) return "{\"error\":\"no device id\"}";
            try
            {
                int dur = 0; int.TryParse((durationDays ?? "").Trim(), out dur);
                byte[] dev = Core.LicenseEngine.ResolveDeviceId(deviceId.Trim());
                string key;
                if (!string.IsNullOrEmpty(privateHex))
                {
                    var v = new Core.VendorProfile { PrivateKey = Core.LicenseEngine.FromHex(privateHex.Trim()) };
                    if (dur > 0) v.ExpiryDays = Core.LicenseSign.NowDays() + (uint)dur;
                    key = Core.LicenseEngine.GenerateKey(dev, v);
                }
                else
                {
                    key = Core.LicenseEngine.GenerateKey(dev, LoadOrCreateVendor());
                    dur = 0;
                }
                string created = DateTime.Now.ToString("yyyy-MM-dd HH:mm");
                string expiry = dur > 0 ? DateTime.Now.AddDays(dur).ToString("yyyy-MM-dd") : "perpetual";
                string durTxt = dur > 0 ? (dur + " days") : "perpetual";
                string line = deviceId.Trim() + "\t"
                            + (label ?? "").Replace('\t', ' ').Replace('\r', ' ').Replace('\n', ' ') + "\t"
                            + key + "\t" + created + "\t" + durTxt + "\t" + expiry;
                File.AppendAllText(KeysPath(), line + "\r\n");
                return "{\"key\":" + JsonStr(key) + ",\"created\":" + JsonStr(created)
                     + ",\"duration\":" + JsonStr(durTxt) + ",\"expiry\":" + JsonStr(expiry) + "}";
            }
            catch (Exception ex) { return "{\"error\":" + JsonStr(ex.Message) + "}"; }
        }
        private void AuthRemoveKey(string deviceId)
        {
            try
            {
                if (string.IsNullOrEmpty(deviceId) || !File.Exists(KeysPath())) return;
                var kept = new List<string>();
                foreach (var l in File.ReadAllLines(KeysPath()))
                {
                    if (string.IsNullOrWhiteSpace(l)) continue;
                    var p = l.Split('\t');
                    if (p.Length >= 1 && p[0] == deviceId.Trim()) continue;
                    kept.Add(l);
                }
                File.WriteAllLines(KeysPath(), kept);
            }
            catch { }
        }
        private string AuthVerifyKey(string deviceId, string key)
        {
            if (string.IsNullOrEmpty(deviceId)) return "INVALID";
            try
            {
                var v = LoadOrCreateVendor();
                byte[] dev = Core.LicenseEngine.ResolveDeviceId(deviceId.Trim());
                return Core.LicenseEngine.ValidateKey(dev, v, key) ? "VALID" : "INVALID";
            }
            catch { return "INVALID"; }
        }

        private static void DiagLog(string line)
        {
            try
            {
                string p = Path.Combine(Path.GetTempPath(), "eiym_manual.log");
                File.AppendAllText(p, DateTime.Now.ToString("HH:mm:ss.fff") + "  " + line + "\r\n");
            }
            catch { }
        }

        private static string JsonStr(string s)
        {
            if (s == null) return "null";
            var sb = new StringBuilder(s.Length + 2);
            sb.Append('"');
            foreach (char c in s)
            {
                if      (c == '"')  sb.Append("\\\"");
                else if (c == '\\') sb.Append("\\\\");
                else if (c == '\n') sb.Append("\\n");
                else if (c == '\r') sb.Append("\\r");
                else if (c == '\t') sb.Append("\\t");
                else if (c < 0x20)  sb.Append("\\u").Append(((int)c).ToString("X4"));
                else                sb.Append(c);
            }
            sb.Append('"');
            return sb.ToString();
        }

        private void DoScanLibraries()
        {
            if (string.IsNullOrEmpty(_selectedFile) || !File.Exists(_selectedFile))
            {
                ShowToast("No target file", "Pick a target file on the Home tab first.", "info");
                return;
            }
            _libPaths.Clear();
            _libChecked.Clear();
            try
            {
                foreach (var p in ScanReferencedDlls(_selectedFile))
                {
                    _libPaths.Add(p);
                    _libChecked.Add(false);
                }
            }
            catch (Exception ex)
            {
                ShowToast("Scan failed", ex.Message, "error");
                return;
            }

            var sb = new StringBuilder("[");
            for (int i = 0; i < _libPaths.Count; i++)
            {
                if (i > 0) sb.Append(',');
                sb.Append("{\"name\":\"").Append(JsEscape(Path.GetFileName(_libPaths[i])))
                  .Append("\",\"checked\":").Append(_libChecked[i] ? "true" : "false")
                  .Append('}');
            }
            sb.Append(']');
            MASON_appView.InvokeJs("setLibraries", sb.ToString());
        }
        private static string JsEscape(string s)
        {
            if (string.IsNullOrEmpty(s)) return s ?? "";
            return s.Replace("\\", "\\\\").Replace("\"", "\\\"");
        }
        private static List<string> ScanReferencedDlls(string inputPath)
        {
            var result = new List<string>();
            string baseDir = Path.GetDirectoryName(inputPath);
            if (string.IsNullOrEmpty(baseDir) || !Directory.Exists(baseDir)) return result;
            var lookup = new Dictionary<string, string>(StringComparer.OrdinalIgnoreCase);
            try
            {
                foreach (string f in Directory.GetFiles(baseDir, "*.dll", SearchOption.AllDirectories))
                {
                    string n = Path.GetFileNameWithoutExtension(f);
                    if (!lookup.ContainsKey(n)) lookup[n] = f;
                }
            } catch { }
            try
            {
                using (var mod = dnlib.DotNet.ModuleDefMD.Load(inputPath))
                {
                    foreach (var asmRef in mod.GetAssemblyRefs())
                    {
                        if (asmRef == null) continue;
                        string n = asmRef.Name;
                        if (string.IsNullOrEmpty(n)) continue;
                        if (IsSystemAsm(n)) continue;
                        string path;
                        if (lookup.TryGetValue(n, out path) && !result.Contains(path))
                            result.Add(path);
                    }
                }
            } catch { }
            return result;
        }
        private static bool IsSystemAsm(string n)
        {
            if (n == "mscorlib" || n == "System" || n == "WindowsBase") return true;
            if (n.StartsWith("System.")) return true;
            if (n == "PresentationCore" || n == "PresentationFramework") return true;
            if (n == "Microsoft.CSharp" || n == "Microsoft.VisualBasic") return true;
            if (n == "netstandard") return true;
            return false;
        }

        private void PickColorDialog()
        {
            using (var dlg = new ColorDialog())
            {
                dlg.FullOpen = true;
                dlg.Color = Theme.Accent;
                if (dlg.ShowDialog(this) == DialogResult.OK) Theme.SetAccent(dlg.Color);
            }
        }

        private void OpenExternalUrl(string url)
        {
            try
            {
                if (string.IsNullOrEmpty(url)) return;
                url = url.Trim();
                if (!url.StartsWith("http://", StringComparison.OrdinalIgnoreCase) &&
                    !url.StartsWith("https://", StringComparison.OrdinalIgnoreCase))
                    return;

                Uri parsed;
                if (!Uri.TryCreate(url, UriKind.Absolute, out parsed)) return;
                if (parsed.Scheme != Uri.UriSchemeHttp && parsed.Scheme != Uri.UriSchemeHttps) return;

                var psi = new ProcessStartInfo(parsed.AbsoluteUri) { UseShellExecute = true };
                using (Process.Start(psi)) { }
            }
            catch {  }
        }

        private void DoProtect()
        {
            if (string.IsNullOrEmpty(_selectedFile) || !File.Exists(_selectedFile))
            {
                ShowToast("No file selected", "Pick a valid .exe / .dll on the Home tab first.", "error");
                return;
            }

            DiagLog("DoProtect START  selectedFile=" + _selectedFile +
                    "  userExcluded.Count=" + _engine.userExcluded.Count);
            foreach (var k in _engine.userExcluded)
                DiagLog("  userExcluded: " + k);

            string sourceDir = Path.GetDirectoryName(_selectedFile) ?? "";
            string sourceName = Path.GetFileNameWithoutExtension(_selectedFile);
            string sourceExt = Path.GetExtension(_selectedFile);
            string outputPath = Path.Combine(sourceDir, sourceName + "_protected" + sourceExt);

            var libsSnapshot = new List<string>();
            for (int i = 0; i < _libPaths.Count; i++)
                if (_libChecked[i]) libsSnapshot.Add(_libPaths[i]);
            _settings.LibrariesToMerge = libsSnapshot;
            _settings.MergeLibraries = libsSnapshot.Count > 0;

            if (_settings.KeyAuth)
            {
                string kaTool, kaPass, kaAlpha;
                LoadCreds(out kaTool, out kaPass, out kaAlpha);
                _settings.KeyAuthToolName = kaTool;
                _settings.KeyAuthPassword = kaPass;
                _settings.KeyAuthAlphabet = kaAlpha;

                if (_settings.KeyAuthAsymmetric && string.IsNullOrEmpty(_settings.KeyAuthPublicKey))
                {
                    try
                    {
                        byte[] priv, pub;
                        Core.LicenseSign.GenerateKeyPair(out priv, out pub);
                        _settings.KeyAuthPublicKey = Core.LicenseEngine.ToHex(Core.LicenseSign.BuildAsymmetricBlob(pub));
                        string keyFile = outputPath + ".vendor-private.txt";
                        File.WriteAllText(keyFile,
                            "MASON ASYMMETRIC VENDOR PRIVATE KEY - KEEP SECRET\r\n" +
                            "private=" + Core.LicenseEngine.ToHex(priv) + "\r\n" +
                            "public=" + _settings.KeyAuthPublicKey + "\r\n");
                    }
                    catch { }
                }
            }

            SetLoading(true, "Protecting your assembly…", "Initialising pipeline");

            if (_protectInFlight)
            {
                ShowToast("Already protecting", "A protection run is already in progress.", "info");
                return;
            }
            _protectInFlight = true;

            var bgThread = new System.Threading.Thread(() =>
            {
                Exception threadEx = null;
                try
                {
                    _engine.PerformProtection(
                        _selectedFile, outputPath, _settings,
                        s => UiInvoke(() => {
                            if (MASON_appView != null)
                                try { MASON_appView.InvokeJs("setStatus", s ?? ""); } catch { }
                            SetLoading(true, "Protecting your assembly…", s ?? "");
                        }),
                        v => UiInvoke(() => {
                            if (MASON_appView != null)
                                try { MASON_appView.InvokeJs("setProgress", Math.Min(v, 100)); } catch { }
                        }));
                }
                catch (Exception ex) { threadEx = ex; }

                UiInvoke(() =>
                {
                    _protectInFlight = false;
                    SetLoading(false, "", "");
                    if (threadEx == null)
                        ShowToast("Protection completed",
                            "Saved to: " + Path.GetFileName(outputPath), "success");
                    else
                        ShowToast("Protection failed", threadEx.Message, "error");
                    try { MASON_appView.InvokeJs("setProgress", 0); } catch { }
                    try { MASON_appView.InvokeJs("setStatus", "Idle."); } catch { }
                });
            });
            bgThread.IsBackground = true;
            bgThread.Name = "MasonProtect";

            bgThread.SetApartmentState(System.Threading.ApartmentState.STA);
            bgThread.Start();
        }

        private bool _protectInFlight;

        private void UiInvoke(Action action)
        {
            if (action == null) return;
            try
            {
                if (InvokeRequired) BeginInvoke(action);
                else action();
            }
            catch {  }
        }

        private static string ToHex(Color c)
        {
            return string.Format("#{0:X2}{1:X2}{2:X2}", c.R, c.G, c.B);
        }

        private static string ReadEmbedded(string fileName)
        {
            var asm = Assembly.GetExecutingAssembly();
            string[] candidates = { "MasonProtector.Resources." + fileName,
                                    "MasonProtector." + fileName, fileName };
            foreach (var n in candidates)
            {
                using (var s = asm.GetManifestResourceStream(n))
                {
                    if (s == null) continue;
                    using (var r = new StreamReader(s, Encoding.UTF8))
                        return r.ReadToEnd();
                }
            }
            return "";
        }
    }
}

