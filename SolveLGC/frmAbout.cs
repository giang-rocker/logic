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
    public partial class frmAbout : Form
    {
        public frmAbout()
        {
            InitializeComponent();
            string dir = Directory.GetCurrentDirectory().Replace("/",@"\");
            webBrowser1.Navigate(dir+ @"\About.html");
            
        }
    }
}