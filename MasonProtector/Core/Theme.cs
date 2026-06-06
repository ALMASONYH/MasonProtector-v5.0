using System;
using System.Drawing;
using System.IO;
using System.Windows.Forms;

namespace MasonProtector.Core
{
    internal static class Theme
    {

        public static Color Background    = Color.FromArgb(23, 26, 33);
        public static Color Surface       = Color.FromArgb(22, 32, 45);
        public static Color SurfaceAlt    = Color.FromArgb(34, 51, 73);
        public static Color Accent        = Color.FromArgb(102, 192, 244);
        public static Color AccentDark    = Color.FromArgb(40, 110, 165);
        public static Color Text          = Color.FromArgb(199, 213, 224);
        public static Color TextMuted     = Color.FromArgb(122, 138, 153);
        public static Color Danger        = Color.FromArgb(179, 65, 58);

        public static event Action AccentChanged;

        public static void SetAccent(Color c)
        {
            Accent = c;

            AccentDark = Darken(c, 0.35);
            Save();
            if (AccentChanged != null) AccentChanged();
        }

        private static Color Darken(Color c, double pct)
        {
            int r = (int)Math.Max(0, c.R * (1.0 - pct));
            int g = (int)Math.Max(0, c.G * (1.0 - pct));
            int b = (int)Math.Max(0, c.B * (1.0 - pct));
            return Color.FromArgb(c.A, r, g, b);
        }

        private static string ConfigPath
        {
            get
            {
                string dir = Path.Combine(
                    Environment.GetFolderPath(Environment.SpecialFolder.ApplicationData),
                    "MasonProtector");
                try { Directory.CreateDirectory(dir); } catch { }
                return Path.Combine(dir, "theme.config");
            }
        }

        public static void Load()
        {
            try
            {
                if (!File.Exists(ConfigPath)) return;
                string txt = File.ReadAllText(ConfigPath).Trim();

                if (txt.Length >= 6)
                {

                    uint argbU = uint.Parse(txt, System.Globalization.NumberStyles.HexNumber,
                        System.Globalization.CultureInfo.InvariantCulture);
                    var c = Color.FromArgb(unchecked((int)argbU));

                    if (c.R == 138 && c.G == 92 && c.B == 245)
                        return;

                    Accent = c;
                    AccentDark = Darken(c, 0.35);
                }
            }
            catch { }
        }

        public static void Save()
        {
            try { File.WriteAllText(ConfigPath, Accent.ToArgb().ToString("X8")); }
            catch { }
        }

        public static void Apply(Control root)
        {
            if (root == null) return;
            ApplyToOne(root);
            foreach (Control child in root.Controls)
                Apply(child);
        }

        private static void ApplyToOne(Control c)
        {

            if (c is Form)
            {
                c.BackColor = Background;
                c.ForeColor = Text;
                return;
            }

            if (c is FlowLayoutPanel || c is Panel || c is TabPage)
            {
                c.BackColor = Surface;
                c.ForeColor = Text;
            }
            else
            {
                c.ForeColor = Text;
            }
        }

    }
}

