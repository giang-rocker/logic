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
using System.Threading;

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
        bool iserror = false;
        int charStart, charFinish, lineStart, lineFinish;
        string inputt;
        string outputt;
 //       Thread inference;
        private void prove()
        {
            try
            {
                inputt = convert2Normal(Input.Text);          
                outputt = inferencer(inputt);
                //File.WriteAllText("C:\\a.txt", outputt);
            }
            catch
            {
                outputt = "Cannot SOLVE...";
            }
            finally
            {
                showAll();
  //              button2.Enabled = true;
            }
        }
        public SolveLGC()
        {            
            InitializeComponent();            
        }
        private void button1_Click(object sender, EventArgs e)
        {
            btnProveAll.Enabled = false;
            btnStep.Enabled = false;
            if (Input.Text.Trim().Length == 0)
                MessageBox.Show("Vui lòng nhập đề toán!!!");
            else
            {
                //inference = new Thread(new ThreadStart(prove));
                //inference.Start();  
                prove();
                isclick = false;
                arraystr = null;
                step = 0;
            }
        }
        #region abc
        private void showAll()
        {
            float maxlength = 0;
            int t = 0;

            if (outputt == "Cannot SOLVE...")
            {
                MessageBox.Show("Bài toán không giải được!");
                return;
            }
            else if (outputt.StartsWith("Unexpected"))
            {
                iserror = true;
                Output.Text = convert2Lgc(outputt);
                string[] instr = Regex.Split(outputt, "CharStart:");
                string[] cStart = Regex.Split(instr[1], "\tCharFinish:");
                charStart = Int32.Parse((string)cStart[0]);
                string[] cFinish = Regex.Split(cStart[1], "\tLineStart:");
                charFinish = Int32.Parse((string)cFinish[0]);
                string[] lStart = Regex.Split(cFinish[1], "\tLineFinish:");
                lineStart = Int32.Parse((string)lStart[0]);
                lineFinish = Int32.Parse((string)lStart[1]);
                if (lineFinish == 1)
                {
                    string in_text = Input.Text;
                    char[] intext = in_text.ToCharArray();
                    for (int v = 0; v < charStart - 1; v++)
                    {
                        if ((intext[v]).ToString() == "→" || (intext[v]).ToString() == "┠" || (intext[v]).ToString() == "∀" || (intext[v]).ToString() == "∃")
                        {
                            charStart--;
                            charFinish--;
                        }
                        if ((intext[v]).ToString() == "⊥")
                        {
                            charStart -= 2;
                            charFinish -= 2;
                        }
                    }
                    Input.SelectionStart = charStart - 1;
                    Input.SelectionLength = charFinish - charStart + 1;
                    Input.SelectionBackColor = Color.SeaGreen;
                    Input.SelectionColor = Color.Red;
                }
                else
                {
                    
                    int x;
                    string in_text = Input.Text;
                    char[] intext = in_text.ToCharArray();
                    for (int v = 0; v < in_text.Length; v++)
                    {
                        if ((intext[v]).ToString() == "\n")
                            lineFinish--;

                        if (lineFinish == 1)
                        {
                            x = v;
                            for (int u = 0; u < charStart - 1; u++)
                            {
                                if ((intext[v + 1]).ToString() == "→" || (intext[v + 1]).ToString() == "┠" || (intext[v + 1]).ToString() == "∀" || (intext[v + 1]).ToString() == "∃")
                                {
                                    charStart--;
                                    charFinish--;
                                }
                                if ((intext[v + 1]).ToString() == "⊥")
                                {
                                    charStart -= 2;
                                    charFinish -= 2;
                                }
                                v++;
                            }
                            if (charStart == 1)
                            {
                                Input.SelectionStart = x + charStart - 1;
                                Input.SelectionLength = charFinish - charStart + 2;
                            }
                            else
                            {
                                Input.SelectionStart = x + charStart;
                                Input.SelectionLength = charFinish - charStart + 1;
                            }
                            Input.SelectionBackColor = Color.SeaGreen;
                            Input.SelectionColor = Color.Red;
                            break;
                        }
                    }
                }
                iserror = false;
                return;
            }

            else
            {
                string pattern = "\n";
                string[] substrings = Regex.Split(outputt, pattern);    // Split on hyphens
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
                        num_space = (int)((maxlength - size.Width) / 7) + 8 ;
                        result[i] = result[i] + add_space(num_space) + "\t" ;
                    }
                }
                Output.Text = result[0] + tail[0];
                for (int i = 1; i < result.Length-1; i++)
                {
                    Output.Text = Output.Text + "\n" + result[i] + tail[i];
                }
                Output.Select(Output.Text.Length, 0);
                Output.ScrollToCaret();
            }
            btnStep.Enabled = true;
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
            try
            {
                if (!iserror)
                {
                    string s1 = convert2Lgc(Input.Text.Substring(0, Input.SelectionStart));
                    string s2 = Input.Text.Substring(Input.SelectionStart, Input.Text.Length - Input.SelectionStart);
                    Input.Text = convert2Lgc(s1 + s2);
                    Input.SelectionStart = s1.Length;                
                    isclick = false;
                    arraystr = null;
                    step = 0;
                    btnProveAll.Enabled = true;
                    btnStep.Enabled = true; 
                }          
            }
            catch
            {
            }
        }

        string convert2Lgc(string text)
        {
            text = text.Replace("_|_", "⊥");
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
            text = text.Replace("∀","V-");
            text = text.Replace("∃","-]");
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
            iserror = false;
            if (Clipboard.ContainsText())
            {
                Input.Text = Clipboard.GetText();
                richTextBox1_TextChanged(null, null);
            }
            else
            {
                pasteToolStripMenuItem.Enabled = false;
            }

        }

        private void newToolStripMenuItem_Click(object sender, EventArgs e)
        {
            Input.Clear();
            Output.Clear();
        }

        private void saveToolStripMenuItem_Click(object sender, EventArgs e)
        {
            SaveFileDialog saveFile = new SaveFileDialog();
            saveFile.Filter = "Text files (*.txt)|*.txt|All files (*.*)|*.*";
            if (saveFile.ShowDialog() != DialogResult.OK) return;
            File.WriteAllText(saveFile.FileName, convert2Normal(Input.Text));
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

        private void exitToolStripMenuItem_Click(object sender, EventArgs e)
        {
            Application.Exit();
        }

        private void SolveLGC_Load(object sender, EventArgs e)
        {

        }
        #endregion
        private void proveStep()
        {
            try
            {
                inputt = convert2Normal(Input.Text);
                outputt = inferencer(inputt);
            }
            catch 
            {                
                outputt = "Cannot SOLVE...";
            }
            finally
            {               
               ShowStep();              
            }
        }
        private void button2_Click(object sender, EventArgs e)
        {
            btnProveAll.Enabled = false;
            btnStep.Enabled = false;
            if (Input.Text.Trim().Length == 0)
                MessageBox.Show("Vui lòng nhập đề toán!!!");
            else if (!isclick)
            {
                isclick = true;
                //inference = new Thread(new ThreadStart(proveStep));
                //inference.Start();
                proveStep();               
            }
            else 
            {
                if (arraystr != null)
                {
                    if (step < arraystr.Length-1)
                    {
                        Output.Text += arraystr[step] + "\n";
                        step++;
                    }
                    if (step >= (arraystr.Length - 1))
                        btnProveAll.Enabled = true;
                    btnProveAll.Enabled = true;
                }
                Output.Select(Output.Text.Length, 0);
                Output.ScrollToCaret();
                btnStep.Enabled = true;                
            }            
        }
        private void ShowStep()
        {
            Output.Text = "";
            float maxlength = 0;
            int t = 0;
            if (outputt == "Cannot SOLVE..." )
            {
                MessageBox.Show("Bài toán không giải được!");
                return;
            }
            else if (outputt.StartsWith("Unexpected"))
            {
                iserror = true;
                Output.Text = convert2Lgc(outputt);
                string[] instr = Regex.Split(outputt, "CharStart:");
                string[] cStart = Regex.Split(instr[1], "\tCharFinish:");
                charStart = Int32.Parse((string)cStart[0]);
                string[] cFinish = Regex.Split(cStart[1], "\tLineStart:");
                charFinish = Int32.Parse((string)cFinish[0]);
                string[] lStart = Regex.Split(cFinish[1], "\tLineFinish:");
                lineStart = Int32.Parse((string)lStart[0]);
                lineFinish = Int32.Parse((string)lStart[1]);
                if (lineFinish == 1)
                {
                    string in_text = Input.Text;
                    char[] intext = in_text.ToCharArray();
                    for (int v = 0; v < charStart - 1; v++)
                    {
                        if ((intext[v]).ToString() == "→" || (intext[v]).ToString() == "┠" || (intext[v]).ToString() == "∀" || (intext[v]).ToString() == "∃")
                        {
                            charStart--;
                            charFinish--;
                        }
                        if ((intext[v]).ToString() == "⊥")
                        {
                            charStart -= 2;
                            charFinish -= 2;
                        }
                    }
                    Input.SelectionStart = charStart - 1;
                    Input.SelectionLength = charFinish - charStart + 1;
                    Input.SelectionBackColor = Color.SeaGreen;
                    Input.SelectionColor = Color.Red;
                }
                else
                {
                    int x;
                    string in_text = Input.Text;
                    char[] intext = in_text.ToCharArray();
                    for (int v = 0; v < in_text.Length; v++)
                    {
                        if ((intext[v]).ToString() == "\n")
                            lineFinish--;

                        if (lineFinish == 1)
                        {
                            x = v;
                            for (int u = 0; u < charStart - 1; u++)
                            {
                                if ((intext[v + 1]).ToString() == "→" || (intext[v + 1]).ToString() == "┠" || (intext[v + 1]).ToString() == "∀" || (intext[v + 1]).ToString() == "∃")
                                {
                                    charStart--;
                                    charFinish--;
                                }
                                if ((intext[v + 1]).ToString() == "⊥")
                                {
                                    charStart -= 2;
                                    charFinish -= 2;
                                }
                                v++;
                            }
                            if (charStart == 1)
                            {
                                Input.SelectionStart = x + charStart - 1;
                                Input.SelectionLength = charFinish - charStart + 2;
                            }
                            else
                            {
                                Input.SelectionStart = x + charStart;
                                Input.SelectionLength = charFinish - charStart + 1;
                            }
                            Input.SelectionBackColor = Color.SeaGreen;
                            Input.SelectionColor = Color.Red;
                            break;
                        }
                    }
                }
                iserror = false;
                return;
            }
            else
            {
                string pattern = "\n";
                string[] substrings = Regex.Split(outputt, pattern);    // Split on hyphens
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
                if (arraystr != null)
                {
                    Output.Text += arraystr[step] + "\n";
                    step++;
                }
                btnProveAll.Enabled = true;
            }
            isclick = true;
            btnStep.Enabled = true;
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
        private void aboutToolStripMenuItem_Click(object sender, EventArgs e)
        {
            frmAbout about = new frmAbout();
            about.ShowDialog();
        }

        private void toolStripMenuItem1_Click(object sender, EventArgs e)
        {
            frmInstruction about = new frmInstruction();
            about.ShowDialog();
        }

        private void searchToolStripMenuItem_Click(object sender, EventArgs e)
        {
            frmEquiv about = new frmEquiv();
            about.ShowDialog();
        }     

    }
}