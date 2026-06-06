using System;
using System.Runtime.InteropServices;

namespace MasonProtector.Core
{

    [ComVisible(true)]
    [ClassInterface(ClassInterfaceType.AutoDispatch)]
    public class AppBridge
    {
        [ComVisible(false)] public Action OnWindowDrag      { get; set; }
        [ComVisible(false)] public Action OnWindowMinimize  { get; set; }
        [ComVisible(false)] public Action OnWindowMaximize  { get; set; }
        [ComVisible(false)] public Action OnWindowClose     { get; set; }

        [ComVisible(false)] public Action<string, bool>   OnSetBoolOption  { get; set; }
        [ComVisible(false)] public Action<string, int>    OnSetIntOption   { get; set; }
        [ComVisible(false)] public Action<string, string> OnSetTextOption  { get; set; }
        [ComVisible(false)] public Action<bool>           OnSetEnableAll   { get; set; }
        [ComVisible(false)] public Action<string, int>    OnSetOptionLevel { get; set; }

        [ComVisible(false)] public Func<string>                 OnAuthGetDeviceId    { get; set; }
        [ComVisible(false)] public Func<string, string>         OnAuthGenerateKey    { get; set; }
        [ComVisible(false)] public Func<string>                 OnAuthGetVendorMap   { get; set; }
        [ComVisible(false)] public Func<string, string>         OnAuthSaveVendorMap  { get; set; }
        [ComVisible(false)] public Func<string>                 OnAuthRegenVendorMap { get; set; }
        [ComVisible(false)] public Func<string>                 OnAuthExportVendorMap{ get; set; }
        [ComVisible(false)] public Func<string>                 OnAuthListKeys       { get; set; }
        [ComVisible(false)] public Func<string, string, string> OnAuthIssueKey       { get; set; }
        [ComVisible(false)] public Action<string>               OnAuthRemoveKey      { get; set; }
        [ComVisible(false)] public Func<string, string, string> OnAuthVerifyKey      { get; set; }
        [ComVisible(false)] public Func<string>                 OnAuthGetCredentials { get; set; }
        [ComVisible(false)] public Func<string, string, string> OnAuthSetCredentials { get; set; }
        [ComVisible(false)] public Func<string>                 OnAuthGenKeyPair     { get; set; }
        [ComVisible(false)] public Func<string, string, string> OnAuthSignAsym       { get; set; }

        [ComVisible(false)] public Func<string, string, string, string, string> OnAuthIssueTimed { get; set; }

        [ComVisible(false)] public Action       OnBrowse         { get; set; }
        [ComVisible(false)] public Action       OnProtect        { get; set; }
        [ComVisible(false)] public Action       OnScanLibraries  { get; set; }
        [ComVisible(false)] public Action<int, bool> OnToggleLibrary { get; set; }

        [ComVisible(false)] public Action       OnPickColor      { get; set; }
        [ComVisible(false)] public Action       OnResetTheme     { get; set; }
        [ComVisible(false)] public Action<int, int, int> OnApplyColor { get; set; }

        [ComVisible(false)] public Action<string> OnLog          { get; set; }

        [ComVisible(false)] public Func<string>           OnScanTarget  { get; set; }
        [ComVisible(false)] public Action<string, bool>   OnSetExcluded { get; set; }

        [ComVisible(false)] public Action<string>         OnOpenUrl     { get; set; }

        public void WindowDrag()     { Try(OnWindowDrag); }
        public void WindowMinimize() { Try(OnWindowMinimize); }
        public void WindowMaximize() { Try(OnWindowMaximize); }
        public void WindowClose()    { Try(OnWindowClose); }

        public void SetOption(string name, bool value)
        {
            try { var h = OnSetBoolOption; if (h != null) h(name, value); } catch { }
        }
        public void SetNumeric(string name, int value)
        {
            try { var h = OnSetIntOption; if (h != null) h(name, value); } catch { }
        }
        public void SetText(string name, string value)
        {
            try { var h = OnSetTextOption; if (h != null) h(name, value ?? ""); } catch { }
        }
        public void EnableAll(bool value)
        {
            try { var h = OnSetEnableAll; if (h != null) h(value); } catch { }
        }
        public void SetOptionLevel(string name, int level)
        {
            try { var h = OnSetOptionLevel; if (h != null) h(name, level); } catch { }
        }

        public string AuthGetDeviceId()
        {
            try { var h = OnAuthGetDeviceId; if (h != null) return h() ?? ""; } catch { }
            return "";
        }
        public string AuthGenerateKey(string deviceId)
        {
            try { var h = OnAuthGenerateKey; if (h != null) return h(deviceId ?? "") ?? ""; } catch { }
            return "";
        }
        public string AuthGetVendorMap()
        {
            try { var h = OnAuthGetVendorMap; if (h != null) return h() ?? ""; } catch { }
            return "";
        }
        public string AuthSaveVendorMap(string text)
        {
            try { var h = OnAuthSaveVendorMap; if (h != null) return h(text ?? "") ?? ""; } catch { }
            return "";
        }
        public string AuthRegenVendorMap()
        {
            try { var h = OnAuthRegenVendorMap; if (h != null) return h() ?? ""; } catch { }
            return "";
        }
        public string AuthExportVendorMap()
        {
            try { var h = OnAuthExportVendorMap; if (h != null) return h() ?? ""; } catch { }
            return "";
        }
        public string AuthListKeys()
        {
            try { var h = OnAuthListKeys; if (h != null) return h() ?? ""; } catch { }
            return "[]";
        }
        public string AuthIssueKey(string deviceId, string label)
        {
            try { var h = OnAuthIssueKey; if (h != null) return h(deviceId ?? "", label ?? "") ?? ""; } catch { }
            return "";
        }
        public void AuthRemoveKey(string deviceId)
        {
            try { var h = OnAuthRemoveKey; if (h != null) h(deviceId ?? ""); } catch { }
        }
        public string AuthVerifyKey(string deviceId, string key)
        {
            try { var h = OnAuthVerifyKey; if (h != null) return h(deviceId ?? "", key ?? "") ?? ""; } catch { }
            return "";
        }
        public string AuthGetCredentials()
        {
            try { var h = OnAuthGetCredentials; if (h != null) return h() ?? ""; } catch { }
            return "{\"tool\":\"\",\"pass\":\"\"}";
        }
        public string AuthSetCredentials(string tool, string pass)
        {
            try { var h = OnAuthSetCredentials; if (h != null) return h(tool ?? "", pass ?? "") ?? ""; } catch { }
            return "";
        }

        public string AuthGenKeyPair()
        {
            try { var h = OnAuthGenKeyPair; if (h != null) return h() ?? ""; } catch { }
            return "";
        }

        public string AuthSignAsym(string privateHex, string deviceId)
        {
            try { var h = OnAuthSignAsym; if (h != null) return h(privateHex ?? "", deviceId ?? "") ?? ""; } catch { }
            return "";
        }

        public string AuthIssueTimed(string deviceId, string label, string durationDays, string privateHex)
        {
            try { var h = OnAuthIssueTimed; if (h != null) return h(deviceId ?? "", label ?? "", durationDays ?? "", privateHex ?? "") ?? ""; } catch { }
            return "";
        }

        public void Browse()        { Try(OnBrowse); }
        public void Protect()       { Try(OnProtect); }
        public void ScanLibraries() { Try(OnScanLibraries); }
        public void ToggleLibrary(int index, bool isChecked)
        {
            try { var h = OnToggleLibrary; if (h != null) h(index, isChecked); } catch { }
        }

        public void PickColor()  { Try(OnPickColor); }
        public void ResetTheme() { Try(OnResetTheme); }
        public void ApplyColor(int r, int g, int b)
        {
            try { var h = OnApplyColor; if (h != null) h(r, g, b); } catch { }
        }

        public void Log(string msg)
        {
            try { var h = OnLog; if (h != null) h(msg ?? ""); } catch { }
        }

        public string ScanTarget()
        {
            try { var h = OnScanTarget; if (h != null) return h() ?? ""; } catch { }
            return "";
        }
        public void SetExcluded(string fullName, bool excluded)
        {
            try { var h = OnSetExcluded; if (h != null) h(fullName ?? "", excluded); } catch { }
        }
        public void OpenUrl(string url)
        {
            try { var h = OnOpenUrl; if (h != null) h(url ?? ""); } catch { }
        }

        private static void Try(Action a)
        {
            try { if (a != null) a(); } catch { }
        }
    }
}

