#include <iostream>
#include "Analyser/Scanner.h"

using namespace std;

int main()
{


	//"a<->a<>abc a V- -]kdj aa ";
	string text = "a<->a<>abc a V- -]kdj aa ";
	Scanner*s = new Scanner(text);
	Token token;
	cout << "\n\n\tResult:\n------------------------------------------------\n|  \tKind\t\t\t|\tLexeme\t\t\n------------------------------------------------\n";
	do
	{
		token = s->nextToken();
		cout<<"|  "<< "\t\t\t"<<(string)token <<"\t\t"<<endl;
	}
	while((TokenKind)token!= LGC_NIL);
	cout << "------------------------------------------------\n\n";
	return 0;
	
}