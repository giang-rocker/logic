using System;
using System.Collections.Generic;
using System.Windows.Forms;

using System.IO;
namespace Logic
{
    static class Program
    {
        /// <summary>
        /// The main entry point for the application.
        /// </summary>
        [STAThread]
        static void Main()
        {             
            Application.EnableVisualStyles();
            Application.SetCompatibleTextRenderingDefault(false);
            Directory.SetCurrentDirectory("../../..");
            Application.Run(new SolveLGC());           
            
        }
    }
}