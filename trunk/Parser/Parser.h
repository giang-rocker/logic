#include <iostream>
#include "../Analyser/Scanner.h"
#include "../Analyser/Token.h"
#include "../TermVector/TermVector.h"
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
	void parseFormulaTail();
	string s ;
	TermVector data;
private:
	Scanner* scanner; 
	Token lookAheadToken;
	Token currentToken;
	bool isStarted ;
//	bool first;
//	string error = "" ;
}
;
