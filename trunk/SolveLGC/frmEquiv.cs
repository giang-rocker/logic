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
    public partial class frmEquiv : Form
    {
        public frmEquiv()
        {
            InitializeComponent();
            string dir = Directory.GetCurrentDirectory().Replace("/", @"\");
            webBrowser1.Navigate(dir + @"\Equivalence.html");
        }

        private void webBrowser1_DocumentCompleted(object sender, WebBrowserDocumentCompletedEventArgs e)
        {

        }

        private void frmEquiv_Load(object sender, EventArgs e)
        {

        }
    }
}