#include <iostream>
#include "Analyser/Scanner.h"
#include "Parser/Parser.h"
#include "NaturalDeduction/NaturalDeduction.h"
using namespace std;
#include <windows.h>
int main()
{


	string text = "Q,Q and P" ;//"p(Xo,Yo) and ( q(Xo,Yo) -> Q ) and K and A and all x (p(x) -> q(x))  ";
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
	NaturalDeduction nd(p->data);
	nd.Eliminate();
	nd.print();
	return 0;
	
}
