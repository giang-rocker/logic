// Parser.cpp : Defines the entry point for the console application.
//

#include "Parser.h"

Parser::Parser(Scanner* s)
{
	//scanner = s;
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
	
}

