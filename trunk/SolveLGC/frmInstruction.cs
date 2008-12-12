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
            webBrowser1.Navigate(@"C:\Documents and Settings\Ngoc Phuoc\Desktop\About.html");
            MessageBox.Show(Directory.GetCurrentDirectory());
        }

        private void frmInstruction_Load(object sender, EventArgs e)
        {

        }

        private void webBrowser1_DocumentCompleted(object sender, WebBrowserDocumentCompletedEventArgs e)
        {           
            webBrowser1.Navigate(@"C:\Documents and Settings\Ngoc Phuoc\Desktop\About.html");
            MessageBox.Show(Directory.GetCurrentDirectory());
        }
    }
}