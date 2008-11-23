#include <iostream>
#include "Analyser/Scanner.h"
#include "Parser/Parser.h"
using namespace std;

int main()
{


	//"a<->a<>abc a V- -]kdj aa ";
//	string text = "p(x,y), q(X) AND NOT all x h(y,k(l)) -> r(M) ";
	string text = "P and Q";
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