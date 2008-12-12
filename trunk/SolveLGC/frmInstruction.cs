using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.IO;

namespace Logic
{
    public partial class frmInstruction : Form
    {
        public frmInstruction()
        {
            InitializeComponent();
            string dir = Directory.GetCurrentDirectory().Replace("/", @"\");
            webBrowser1.Navigate(dir + @"\Instruction.html");
        }

        private void frmInstruction_Load(object sender, EventArgs e)
        {

        }

        
    }
}