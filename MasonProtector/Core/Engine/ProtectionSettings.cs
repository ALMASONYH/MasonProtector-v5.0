namespace MasonProtector.Core
{
    public enum Level
    {
        Light = 0,
        Medium = 1,
        Strong = 2
    }

    public class ProtectionSettings
    {
        public int ProtectionLevel { get; set; }

        private readonly System.Collections.Generic.Dictionary<string, int> _optionLevels =
            new System.Collections.Generic.Dictionary<string, int>(System.StringComparer.Ordinal);

        public System.Collections.Generic.Dictionary<string, int> OptionLevels { get { return _optionLevels; } }

        public int GetLevel(string name)
        {
            if (MaximumEncryption) return (int)Level.Strong;
            int v;
            if (!string.IsNullOrEmpty(name) && _optionLevels.TryGetValue(name, out v))
            {
                if (v < 0) v = 0;
                if (v > 2) v = 2;
                return v;
            }
            int g = ProtectionLevel;
            if (g < 0) g = 0;
            if (g > 2) g = 2;
            return g;
        }

        public void SetLevel(string name, int level)
        {
            if (string.IsNullOrEmpty(name)) return;
            if (level < 0) level = 0;
            if (level > 2) level = 2;
            _optionLevels[name] = level;
        }

        public int HwidBanThreshold { get; set; }

        public bool EnableRenamer { get; set; }
        public bool RenameNamespaces { get; set; }
        public bool FlattenNamespaces { get; set; }
        public bool SeparateNamespacePerClass { get; set; }
        public bool RenameTypes { get; set; }
        public bool RenameMethods { get; set; }
        public bool RenameFields { get; set; }
        public bool RenameProperties { get; set; }
        public bool RenameEvents { get; set; }
        public bool HiddenRename { get; set; }
        public bool MaximumEncryption { get; set; }
        public bool HideEncryption { get; set; }

        public bool CodeEncryption { get; set; }

        public bool Dynamic { get; set; }
        public int RenameLength { get; set; }
        public string RenamePrefix { get; set; }
        public string RandomChars { get; set; }
        public bool StringEncryption { get; set; }
        public bool IntEncoding { get; set; }
        public bool ControlFlow { get; set; }
        public bool AntiDebug { get; set; }

        public bool AntiDebugAggressive { get; set; }
        public bool AntiVM { get; set; }
        public bool JunkCode { get; set; }
        public int JunkCount { get; set; }
        public bool ResourceProtection { get; set; }
        public bool EncryptFormResources { get; set; }
        public bool AntiDump { get; set; }
        public bool AntiTamper { get; set; }
        public bool AntiDe4dot { get; set; }
        public bool ProxyCalls { get; set; }
        public bool HideMethods { get; set; }
        public bool FakeAttributes { get; set; }
        public bool Watermark { get; set; }
        public bool VMObfuscation { get; set; }
        public bool VMObfuscationV2 { get; set; }
        public bool CalliConversion { get; set; }
        public bool Local2Field { get; set; }
        public bool MutationEncoding { get; set; }
        public bool RuntimeEncryption { get; set; }
        public bool ConstantsEncoding { get; set; }
        public bool OpaquePredicates { get; set; }
        public bool ReferenceProxy { get; set; }
        public bool CallHiding { get; set; }
        public bool MethodBodyEncryption { get; set; }
        public bool AntiILDasm { get; set; }
        public bool TokenConfusion { get; set; }
        public bool FieldEncryption { get; set; }
        public bool StackUnderflow { get; set; }
        public bool CrossReferenceEncryption { get; set; }
        public bool PolymorphicEncryption { get; set; }
        public bool StringComposition { get; set; }
        public bool MethodScattering { get; set; }
        public bool GlobalMethodVault { get; set; }
        public bool DelegateEncryption { get; set; }
        public bool ControlFlowFlattening2 { get; set; }
        public bool InvalidMetadata { get; set; }
        public bool ArrayEncryption { get; set; }
        public bool TypeScrambler { get; set; }
        public bool NumericObfuscation { get; set; }
        public bool AntiMemoryDump { get; set; }
        public bool BranchConfusion { get; set; }
        public bool CodeVirtualization { get; set; }
        public bool EntryPointMover { get; set; }
        public bool MethodInliner { get; set; }
        public bool AntiHook { get; set; }
        public bool AntiHttp { get; set; }
        public bool DnSpyCrasher { get; set; }

        public bool DecompilerPoison { get; set; }

        public bool HideDesignerCode { get; set; }

        public bool MergeLibraries { get; set; }
        public System.Collections.Generic.List<string> LibrariesToMerge { get; set; }
        public bool ExportCodeToDll { get; set; }
        public string CodeDllName { get; set; }

        public bool AntiCrack { get; set; }

        public bool   AntiCrackMessageBox        { get; set; }
        public string AntiCrackMessageBoxSender  { get; set; }
        public string AntiCrackMessageBoxText    { get; set; }
        public int    AntiCrackMessageBoxAttempt { get; set; }

        public bool   AntiCrackWebhook           { get; set; }
        public string AntiCrackWebhookUrl        { get; set; }
        public int    AntiCrackWebhookAttempt    { get; set; }
        public bool   AntiCrackWebhookScreenshot { get; set; }
        public bool   AntiCrackWebhookSysInfo    { get; set; }

        public bool   AntiCrackRemoteFile        { get; set; }
        public string AntiCrackRemoteFileUrl     { get; set; }
        public int    AntiCrackRemoteFileAttempt { get; set; }

        public bool   AntiCrackSelfDestruct        { get; set; }
        public int    AntiCrackSelfDestructAttempt { get; set; }

        public bool Compress { get; set; }

        public bool   KeyAuth         { get; set; }
        public string KeyAuthToolName { get; set; }
        public string KeyAuthPassword { get; set; }
        public string KeyAuthAlphabet { get; set; }

        public bool   KeyAuthAsymmetric { get; set; }
        public string KeyAuthPublicKey  { get; set; }
        public bool   KeyAuthKeepConsole { get; set; }
        public bool   KeyAuthAlwaysPrompt { get; set; }
        public bool   KeyAuthShowConsole { get; set; }

        public ProtectionSettings()
        {
            ProtectionLevel = (int)Level.Medium;
            HwidBanThreshold = 10;

            RenameLength = 12;
            RenamePrefix = "";
            RandomChars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";

            JunkCount = 20;
            LibrariesToMerge = new System.Collections.Generic.List<string>();
            CodeDllName = "MasonCore.dll";

            AntiCrack                    = false;
            AntiCrackMessageBox          = false;
            AntiCrackMessageBoxSender    = "Security Notice";
            AntiCrackMessageBoxText      = "Unauthorized analysis detected.";
            AntiCrackMessageBoxAttempt   = 5;
            AntiCrackWebhook             = false;
            AntiCrackWebhookUrl          = "";
            AntiCrackWebhookAttempt      = 3;
            AntiCrackWebhookScreenshot   = false;
            AntiCrackWebhookSysInfo      = false;
            AntiCrackRemoteFile          = false;
            AntiCrackRemoteFileUrl       = "";
            AntiCrackRemoteFileAttempt   = 10;
            AntiCrackSelfDestruct        = false;
            AntiCrackSelfDestructAttempt = 15;

            KeyAuth            = false;
            KeyAuthToolName    = "";
            KeyAuthPassword    = "";
            KeyAuthAlphabet     = "";
            KeyAuthAsymmetric   = false;
            KeyAuthPublicKey    = "";
            KeyAuthKeepConsole  = true;
            KeyAuthAlwaysPrompt = false;
            KeyAuthShowConsole  = true;
        }
    }
}

