#include <iostream>
#include "Analyser/Scanner.h"
using namespace std;

int main()
{
	string text = "a";
	Scanner*s = new Scanner(text);
	Token token;
	cout << "\n\n\tResult:\n-----------------------------------------\n|  \tKind\t\t|\tLexeme\t|\n-----------------------------------------\n";
	do
	{
		token = s->nextToken();
		cout<<"|  "<<token.convertToken() << "\t|\t"<<(string)token <<"\t|"<<endl;
	}
	while((TokenKind)token!= LGC_NIL);
	cout << "-----------------------------------------\n\n";
	return 0;
}