// Parser.cpp : Defines the entry point for the console application.
//

#include "Parser.h"

Parser::Parser(Scanner* s)
{
	scanner = s;
	lookAheadToken = Token(LGC_NIL);
}

void Parser::match(Token tokenKind)
{
	if( lookAheadToken.convertToken == tokenKind.convertToken)
		lookAheadToken = scanner->nextToken();
	else
		cout<<"Unexpected Token"<<endl;
}

bool Parser::check(Token tokenKind)
{
	return lookAheadToken.convertToken == tokenKind.convertToken;
}

Token Parser::getLookAheadToken()
{
	return lookAheadToken;	
}

void Parser::parse()
{
	parseSource();
}

//<source>		::= 	<formula> <tail>  
void parseSource()
{
	parseFormula();
	parseTail();
}

//<tail>			::= 	',' <source>  	|  <binary-operator><source>  	|
voi parseFormula()
{
	if(check(LGC_COMMA){
		match(LGC_COMMA);
		parseSource();
	}
	else if (check(LGC_AND) || check(LGC_OR) || check(LGC_MODUS)){
		parseBOperator();
		parseSource();
	}
	else 
		parseEmptyTail();
}

//<formula>		::=   con	|  'not' <formula>  |  <quantifier> <formula> 	| con <argument-list>	| var <argument-list>	|'(' <source> ')'
void parseFormula()
{
	
}