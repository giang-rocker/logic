#include <iostream>
#include "../Analyser/Scanner.h"

using namespace std;


class Parser 
{
public:
	Parser(Scanner* s);
	void match(Token tokenKind);
	bool check(Token tokenKind);
	Token getLookAheadToken();
	void parse();
private:
	Scanner* scanner; 
	Token lookAheadToken;
}
;


