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
	void parseInput();
	void parseSource();	
	void parseGoal();
	void parseFormula();
	void parseTail();
	void parseBin_operator();
	void parseQuantifier();
	void parseArg_list();
	void parseArg();
	void parseArg_tail();
	void parseFormulaTail();
	string s ;
	xWam data;
private:
	Scanner* scanner; 
	Token lookAheadToken;
	Token currentToken;
	bool enterGoal ;
	string semantic;
//	bool first;
//	string error = "" ;
}
;
