#include <iostream>
#include "../Analyser/Scanner.h"

using namespace std;


class Parser 
{
public:
	Parser(Scanner s);
	void match(int tokenKind);
	bool check(int tokenKind);
	Token getLookAheadToken();
	void parse();
private:
	Scanner scanner;
	Token lookAheadToken;
}
;


