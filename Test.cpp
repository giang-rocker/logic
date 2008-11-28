#include <iostream>
#include "Analyser/Scanner.h"
#include "Parser/Parser.h"
#include "NaturalDeduction/NaturalDeduction.h"

using namespace std;
int main()
{


	string text = " P,Q |- Q and P ";
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
		
		NaturalDeduction nd(p->data);
		nd.ProveIt();
		nd.print();	
	}	
	return 0;
	
}
