// Parser.cpp : Defines the entry point for the console application.
//

#include "Parser.h"

Parser::Parser(Scanner s)
{
	scanner = s;
	lookAheadToken = NULL;
}

void Parser::match(int tokenKind)
{
	if( (TokenKind)lookAheadToken == (TokenKind)tokenKind))
		lookAheadToken = scanner->nextToken;
	else
		return NULL;
}

bool Parser::check(int tokenKind)
{
	return (TokenKind)lookAheadToken == (TokenKind)tokenKind;
}

Token Parser::getLookAheadToken()
{
	return lookAheadToken;	
}

void Parser::parse()
{
	
}
