using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.Runtime.InteropServices;
using System.IO;
using System.Text.RegularExpressions ;


namespace Logic
{
    public partial class SolveLGC : Form

    {
        const string path = "Inferencer.dll";
        [DllImport(path)]
        static extern string inferencer(string str);
        string[] arraystr;
        int step = 0;        
        bool isclick = false;
        public SolveLGC()
        {            
            InitializeComponent();
        }
        private void button1_Click(object sender, EventArgs e)
        {   
            
            float maxlength = 0;
            int t = 0;

            string o = inferencer(convert2Normal(Input.Text));
            if (o == "Cannot SOLVE...")
                Output.Text = o;
            else if (o.StartsWith("Unexpected"))
                Output.Text = o;
            else
            {
                string pattern = "\n";
                string[] substrings = Regex.Split(o, pattern);    // Split on hyphens
                string[] result = new string[substrings.Length];
                string[] tail = new string[substrings.Length];
                foreach (string match in substrings)
                {
                    string[] substr = Regex.Split(match, "#");
                    if (substr.Length > 1)
                    {
                        result[t] = convert2Lgc(substr[0]);
                        tail[t] = convert2Lgc(substr[1]);
                    }
                    t++;
                }

                Graphics g = CreateGraphics();
                //maxlenght
                for (int i = 0; i < result.Length; i++)
                {
                    SizeF size = g.MeasureString(result[i], Output.Font);
                    if (maxlength < size.Width)
                        maxlength = size.Width;
                }
                for (int i = 0; i < result.Length; i++)
                {
                    int num_space = 0;
                    SizeF size = g.MeasureString(result[i], Output.Font);
                    if (size.Width <= maxlength)
                    {
                        num_space = (int)((maxlength - size.Width) / 7);
                        result[i] = result[i] + add_space(num_space) + "\t" + "\t";
                    }
                }
                Output.Text = result[0] + tail[0];
                for (int i = 1; i < result.Length; i++)
                {
                    Output.Text = Output.Text + "\n" + result[i] + tail[i];
                }
            }
            Output.Select(Output.Text.Length, 0);
            Output.ScrollToCaret();
        }
        string add_space(int i)
        {
            string s = "";
            for (int t = 0; t < i; t++)
            {
                s += " ";
            }
            return s;
        }


        private void richTextBox1_TextChanged(object sender, EventArgs e)
        {
            
        }

        private void Input_TextChange(object sender, EventArgs e)
        {
            string s1 = convert2Lgc(Input.Text.Substring(0, Input.SelectionStart ));
            string s2 = Input.Text.Substring(Input.SelectionStart, Input.Text.Length - Input.SelectionStart);
            Input.Text = s1 + s2; 
            Input.SelectionStart = s1.Length;        
        }
        string convert2Lgc(string text)
        {   
            text = text.Replace("&", "∧");
            text = text.Replace(" AND ", "∧");
            text = text.Replace(" and ", "∧");
            text = text.Replace("v", "∨");
            text = text.Replace(" OR ", "∨");
            text = text.Replace(" or ", "∨");
            text = text.Replace("|","∨");
            text = text.Replace("!", "¬");
            text = text.Replace("~", "¬");
            text = text.Replace(" NOT ", "¬");
            text = text.Replace("->", "→");
            text = text.Replace("∨-", "┠");
            text = text.Replace(" all ","∀ ");
            text = text.Replace(" exists ","∃");
            text = text.Replace("-]","∃");
            text = text.Replace("V-","∀");
            text = text.Replace("_|_", "⊥");
            //           ¬   →   ∧    ∨      ┠      ∃   ∀ 
            return text;
        }
 
        string convert2Normal(string text)
        {
            text = text.Replace("∧","&" );
            text = text.Replace("∨","|" );
            text = text.Replace("¬","!" );
            text = text.Replace("→","->");
            text = text.Replace("┠","|-");
            text = text.Replace("∀"," all ");
            text = text.Replace("∃"," exists ");
            text = text.Replace("⊥", "_|_");
            return text;
        }

        private void label1_Click(object sender, EventArgs e)
        {

        }

        private void openToolStripMenuItem_Click(object sender, EventArgs e)
        {
            OpenFileDialog openFile = new OpenFileDialog();
            if (openFile.ShowDialog() != DialogResult.OK)
                return;
            Input.Text = File.ReadAllText(openFile.FileName);
        }

        private void pasteToolStripMenuItem_Click(object sender, EventArgs e)
        {
            if (Clipboard.ContainsText())
                Input.Text = Clipboard.GetText();
        }

        private void newToolStripMenuItem_Click(object sender, EventArgs e)
        {
            Input.Clear();
            Output.Clear();
        }

        private void saveToolStripMenuItem_Click(object sender, EventArgs e)
        {
            SaveFileDialog saveFile = new SaveFileDialog();
            saveFile.ShowDialog();    
        }

        private void copyToolStripMenuItem_Click(object sender, EventArgs e)
        {
            Input.Copy();
            Output.Copy();
            Input.Text = Clipboard.GetText();
        }

        private void cutToolStripMenuItem_Click(object sender, EventArgs e)
        {
            Input.Cut();
        }

        private void selectAllToolStripMenuItem_Click(object sender, EventArgs e)
        {
            if (Input.IsAccessible)
            {
                Input.SelectAll();           
            }
            else if (Output.IsAccessible)
                Output.SelectAll();
        }

        private void exitToolStripMenuItem_Click(object sender, EventArgs e)
        {
            
        }

        private void SolveLGC_Load(object sender, EventArgs e)
        {

        }
        
        private void button2_Click(object sender, EventArgs e)
        {
            
            if (!isclick)
            {             
                float maxlength = 0;
                int t = 0;

                string o = inferencer(convert2Normal(Input.Text));
                if (o == "Cannot SOLVE...")
                    Output.Text = o;
                else if (o.StartsWith("Unexpected"))
                    Output.Text = o;
                else
                {
                    string pattern = "\n";
                    string[] substrings = Regex.Split(o, pattern);    // Split on hyphens
                    string[] result = new string[substrings.Length];
                    arraystr = new string[substrings.Length];
                    string[] tail = new string[substrings.Length];
                    foreach (string match in substrings)
                    {
                        string[] substr = Regex.Split(match, "#");
                        if (substr.Length > 1)
                        {
                            result[t] = convert2Lgc(substr[0]);
                            tail[t] = convert2Lgc(substr[1]);
                        }
                        t++;
                    }

                    Graphics g = CreateGraphics();
                    //maxlenght
                    for (int i = 0; i < result.Length; i++)
                    {
                        SizeF size = g.MeasureString(result[i], Output.Font);
                        if (maxlength < size.Width)
                            maxlength = size.Width;
                    }
                    for (int i = 0; i < result.Length; i++)
                    {
                        int num_space = 0;
                        SizeF size = g.MeasureString(result[i], Output.Font);
                        if (size.Width <= maxlength)
                        {
                            num_space = (int)((maxlength - size.Width) / 7);
                            result[i] = result[i] + add_space(num_space) + "\t" + "\t";
                        }
                    }
                    for (int i = 0; i < result.Length; i++)
                    {
                        arraystr[i] = result[i] + tail[i];
                    }                    
                }
                isclick = true;
            }
            if (arraystr != null   )
            {
                if (step < arraystr.Length)
                {
                    Output.Text += arraystr[step] + "\n";
                    step++;
                }
            }
            Output.Select(Output.Text.Length, 0);
            Output.ScrollToCaret();
            
        }

        private void label2_Click(object sender, EventArgs e)
        {

        }

        private void button7_Click(object sender, EventArgs e)
        {
            int select = Input.SelectionStart;
            Input.Text = Input.Text.Insert(select, "∀");
            Input.Select(); Input.SelectionStart = select + 1;
        }
        //           ∧  ¬   →      ∨      ┠      ∃   ∀  ⊥
        private void button3_Click(object sender, EventArgs e)
        {
            int select = Input.SelectionStart;
            Input.Text = Input.Text.Insert(select, "∧");
            Input.Select(); Input.SelectionStart = select + 1;
        }

        private void button4_Click(object sender, EventArgs e)
        {
            int select = Input.SelectionStart;
            Input.Text = Input.Text.Insert(select, "∨");
            Input.Select(); Input.SelectionStart = select + 1;
        }

        private void button5_Click(object sender, EventArgs e)
        {
            int select = Input.SelectionStart;
            Input.Text = Input.Text.Insert(select, "¬");
            Input.Select(); Input.SelectionStart = select + 1;
        }

        private void button6_Click(object sender, EventArgs e)
        {
            int select = Input.SelectionStart;
            Input.Text = Input.Text.Insert(select, "→");
            Input.Select(); Input.SelectionStart = select + 1;
        }

        private void button8_Click(object sender, EventArgs e)
        {
            int select = Input.SelectionStart;
            Input.Text = Input.Text.Insert(select, "∃");
            Input.Select(); Input.SelectionStart = select + 1;
        }

        private void button10_Click(object sender, EventArgs e)
        {
            int select = Input.SelectionStart;
            Input.Text = Input.Text.Insert(select, "┠");
            Input.Select(); Input.SelectionStart = select + 1;
        }

        private void button9_Click(object sender, EventArgs e)
        {
            int select = Input.SelectionStart;
            Input.Text = Input.Text.Insert(select, "⊥");
            Input.Select(); Input.SelectionStart = select+1;
        }

        
    }
}