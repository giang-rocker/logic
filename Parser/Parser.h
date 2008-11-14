#include <iostream>
#include "../Analyser/Scanner.h"

using namespace std;


class Parser 
{
public:
	Parser(Scanner* s);
	void match(TokenKind tokenKind);
	bool check(TokenKind tokenKind);
	Token getLookAheadToken();
	int parse();
private:
	Scanner* scanner; 
	Token lookAheadToken;
	string error = "" ;
}
;


