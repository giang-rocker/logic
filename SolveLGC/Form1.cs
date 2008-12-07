using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.Runtime.InteropServices;
using System.IO;

/*class DirectoryCurrent
{

    public static void a()
    {
        Console.WriteLine("Current directory: \"{0}\"",
           Directory.GetCurrentDirectory());
    }
}*/

namespace Logic
{
    public partial class SolveLGC : Form

    {
 /*       string s = Directory.GetCurrentDirectory();
        DirectoryInfo di = Directory.GetParent(s);
        DirectoryInfo dip = di.Parent;
        DirectoryInfo dipp = dip.Parent;
        string currentdir = dipp.FullName;      */
        [DllImport( "Inferencer.dll")]
        static extern string inferencer(string str);
        public SolveLGC()
        {
            InitializeComponent();
        }

        private void button1_Click(object sender, EventArgs e)
        {
            Output.Text = convert2Lgc(inferencer(convert2Normal(Input.Text)));
        }

        private void richTextBox1_TextChanged(object sender, EventArgs e)
        {

        }

        private void Input_TextChange(object sender, EventArgs e)
        {
            Input.Text = convert2Lgc(Input.Text);
            Input.SelectionStart = Input.Text.Length ;
        }
        string convert2Lgc(string text)
        {   
            text = text.Replace("&", "∧");
            text = text.Replace("AND", "∧");
            text = text.Replace("and", "∧");
            text = text.Replace("v", "∨");
            text = text.Replace("OR", "∨");
            text = text.Replace("or", "∨");
            text = text.Replace("!", "¬");
            text = text.Replace("~", "¬");
            text = text.Replace("NOT", "¬");
            text = text.Replace("->", "→");
            text = text.Replace("|-", "┠");
            text = text.Replace("all","∀ ");
            text = text.Replace("exists","∃");
            text = text.Replace("-]","∃");
            text = text.Replace("V-","∀");
 //           ¬   →   ∧    ∨      ┠      ∃   ∀
            return text;
        }
 
        string convert2Normal(string text)
        {
            text = text.Replace("∧","&" );
            text = text.Replace("∨","|" );
            text = text.Replace("¬","!" );
            text = text.Replace("→","->");
            text = text.Replace("┠","|-");
            text = text.Replace("∀","all");
            text = text.Replace("∃","exists");
            return text;
        }

        private void label1_Click(object sender, EventArgs e)
        {

        }

 /*       private void button2_Click(object sender, EventArgs e)
        {    
            string s = Directory.GetCurrentDirectory();
            DirectoryInfo di = Directory.GetParent(s);
            DirectoryInfo dip = di.Parent;
            DirectoryInfo dipp = dip.Parent;
            string currentdir = dipp.FullName;


            Output.Text = dipp.FullName;
        }*/
    }
}