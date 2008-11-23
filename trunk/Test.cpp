#include <iostream>
#include "Analyser/Scanner.h"
#include "Parser/Parser.h"
using namespace std;

int main()
{


	//"a<->a<>abc a V- -]kdj aa ";
	string text = "p(Xo,Yo) , all x exists y p (x,y) -> not q(x,y)   ";
//	string text = "P and Q";
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