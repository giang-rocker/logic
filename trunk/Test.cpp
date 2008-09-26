#include <iostream>
#include "Analyser/Scanner.h"
using namespace std;

int main()
{
	Scanner*s = new Scanner();
	Token token;
	cout << "\n\n\tResult:\n-------------------------\n|  Kind\t|\tLexeme\t|\n-------------------------\n";
	do
	{
		token = s->nextToken();
		cout<<"|  "<<(TokenKind)token << "\t|\t"<<(string)token <<"\t|"<<endl;
	}
	while((TokenKind)token!=NIL);
	cout << "-------------------------\n\n";
	return 0;
}