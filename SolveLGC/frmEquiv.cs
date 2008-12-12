using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;

namespace Logic
{
    public partial class frmEquiv : Form
    {
        public frmEquiv()
        {
            InitializeComponent();
            webBrowser1.Navigate("C:\\a.html");
        }

        private void webBrowser1_DocumentCompleted(object sender, WebBrowserDocumentCompletedEventArgs e)
        {

        }
    }
}