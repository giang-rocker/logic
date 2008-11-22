#include <iostream>
#include "../Analyser/Scanner.h"
#include "../Analyser/Token.h"
using namespace std;


class Parser 
{
public:
	Parser(Scanner* s);
	void match(TokenKind tokenKind);
	bool check(TokenKind tokenKind);
	Token getLookAheadToken();
	void parse();
	void parseSource();
	void parseFormula();
	void parseTail();
	void parseBin_operator();
	void parseQuantifier();
	void parseArg_list();
	void parseArg();
	void parseArg_tail();
private:
	Scanner* scanner; 
	Token lookAheadToken;
//	string error = "" ;
}
;
