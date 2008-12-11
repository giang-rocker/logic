using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;

namespace Logic
{
    public partial class frmAbout : Form
    {
        public frmAbout()
        {
            InitializeComponent();
            webBrowser1.Navigate(@"C:\Documents and Settings\Ngoc Phuoc\Desktop\About.html");
        }
    }
}