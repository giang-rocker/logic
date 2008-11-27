#include <iostream>
#include "Analyser/Scanner.h"
#include "Parser/Parser.h"
using namespace std;
#include <windows.h>
int main()
{

	char*data = (char*) GetCommandLineW();
	cout<<data;
	//"a<->a<>abc a V- -]kdj aa ";
	string text = "p(Xo,Yo) , all x exists y (p (x,y) -> not q(x,y))  |-  q(Xo,Yo) or p (x,y)and p (y,x) ";
	//string text = "P and Q";
	Scanner* scanner = new Scanner(text);
	Parser* p = new Parser(scanner);
	p->parse();
	if ( p->s != "")
	{
		cout<< p->s <<endl;
	}
	else
	{
		p->data.print();
	}	
	return 0;
	
}
