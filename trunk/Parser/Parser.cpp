// Parser.cpp : Defines the entry point for the console application.
//

#include "Parser.h"

Parser::Parser(Scanner* s)
{
	scanner = s;
	lookAheadToken = Token(LGC_NIL);
}

void Parser::match(TokenKind tokenKind)
{
	if((TokenKind)lookAheadToken == (TokenKind)tokenKind)
		lookAheadToken = scanner->nextToken();
	else
		cout<<"Unexpected Token"<<endl;
}

bool Parser::check(TokenKind tokenKind)
{
	return (TokenKind)lookAheadToken == (TokenKind)tokenKind;
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

//<formula>		::=   con	|  'not' <formula>  |  <quantifier> <formula> 	| con <argument-list>	| var <argument-list>	|'(' <source> ')'
void parseFormula()
{
	if(check(LGC_COMMA)){
		match(LGC_COMMA);
		parseSource();
	}
	else if (check(LGC_AND) || check(LGC_OR) || check(LGC_MODUS)){
		parseBOperator();
		parseSource();
	}
	else 
		match(LGC_NIL)
}

//<tail>			::= 	',' <source>  	|  <binary-operator><source>  	
if(check,)
{

}

/*
var		= 	[abcdefghijklmnopqrstuvwxyz] {Alphanumeric}*
con		= 	[ABCDEFGHIJKLMNOPQRSTUVWXYZ] {Alphanumeric}*

<source>		::= 	<formula> <tail>  
<tail>			::= 	',' <source>  
				|  <binary-operator><source>  
				|
<formula>		::= 	con
				|  'not' <formula>  
				|  <quantifier> <formula> 
				| con <argument-list>
				| var <argument-list>
				|'(' <source> ')'
<argument-list>	::=	'(' <term-list> ')'
<term-list> 		::= 	<term> 
				| <term-list> ',' <term>
<term> 			::= 	var
				| con
<binary-operator> 	::= 	'and' 
				| 'or' 
				| 'modus'
<quantifier> 		::= 	  'all' var  
				|  'exists' var
				| '('<quantifier>')'

*/