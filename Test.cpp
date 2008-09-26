#include <iostream>
#include "Analyser/Scanner.h"
using namespace std;

int main()
{
	Scanner*s = new Scanner();
	Token token;
	do
	{
		token = s->nextToken();
		cout<<(string)token<<endl;
	}
	while((TokenKind)token!=NIL);
	
	return 0;
}