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
            webBrowser1.Navigate("https://www.google.com/accounts/ServiceLogin?service=mail&passive=true&rm=false&continue=http%3A%2F%2Fmail.google.com%2Fmail%2F%3Fshva%3D1%26ui%3Dhtml%26zy%3Dl&bsv=1k96igf4806cy&ltmpl=default&ltmplcache=2#inbox");
        }
    }
}