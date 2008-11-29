#include <iostream>
#include "Analyser/Scanner.h"
#include "Parser/Parser.h"
#include "NaturalDeduction/NaturalDeduction.h"

using namespace std;
int main()
{



	string text = "!B,  B | A  , A -> Q |- A & Q | X";
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
		p->data.print();
		nd.ProveIt();
		nd.print();	
	}	
	return 0;
	
}
