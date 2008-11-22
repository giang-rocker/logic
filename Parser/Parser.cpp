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
void Parser::parseSource()
{
	if (check(LGC_CON)||check(LGC_VAR)||check(LGC_ALL_OP)||check(LGC_NEGATION_OP)||check(LGC_EXIST_OP)||check(LGC_LEFTPAR))
	{
		parseFormula();
		parseTail();
	}
	else
		s = (string)(((Token)getLookAheadToken()).tostring());
}

//<formula>		::=   con	|  'not' <formula>  |  <quantifier> <formula> 	| con <argument-list>	| var <argument-list>	|'(' <source> ')'
void Parser::parseFormula()
{
	if(check(LGC_CON)){
		match(LGC_CON);
		if(check(LGC_LEFTPAR))
			parseArg_list();
	}
	else if (check(LGC_VAR))
	{
		match(LGC_VAR);
		parseArg_list();
	}
	else if (check(LGC_NEGATION_OP))
	{
		match(LGC_NEGATION_OP);
		parseFormula();
	}
	else if (check(LGC_ALL_OP) || check(LGC_EXIST_OP))
	{
		parseQuantifier();
		parseFormula();
	}
	else if (check(LGC_LEFTPAR))
	{
		match(LGC_LEFTPAR);
		parseSource();
		match(LGC_RIGHTPAR);
	}
	else
		s = (string)(((Token)getLookAheadToken()).tostring());
}

//<tail>				::= 	',' <source> |  <binary-operator><source>  |	eof
void Parser::parseTail()
{
	if(check(LGC_COMMA)){
		match(LGC_COMMA);
		parseSource();
	}
	else if (check(LGC_ALL_OP) || check(LGC_UNION_OP) || check(LGC_MAPPING_OP)){
		parseBin_operator();
		parseSource();
	}
	else if (check(LGC_NIL))
		match(LGC_NIL);	
	else
		s = (string)(((Token)getLookAheadToken()).tostring()) ;
}

//<argument-list>		::=	'(' <arg> <arg-tail> 
void Parser::parseArg_list()
{
	if (check(LGC_LEFTPAR)){
		match(LGC_LEFTPAR);
		parseArg();
		parseArg_tail();
	}
	else
		s = (string)(((Token)getLookAheadToken()).tostring()) ;
}	

//<arg-tail> 			::= 	','<arg><arg-tail> 	|  ')'
void Parser::parseArg_tail()
{
	if (check(LGC_COMMA)){
		match(LGC_COMMA);
		parseArg();
		parseArg_tail();
	}
	else if (check (LGC_RIGHTPAR))
		match(LGC_RIGHTPAR);
	else
		s = (string)(((Token)getLookAheadToken()).tostring()) ;
}

//<arg> 				::= 	var		|	const | var <argument-list>|'not' <formula> |<quantifier> <formula>
void Parser::parseArg()
{
	if (check(LGC_VAR))
	{
		match(LGC_VAR);
		if(check(LGC_LEFTPAR))
			parseArg_list();
	}
	else if(check (LGC_CON))
		match(LGC_CON);
	else if (check(LGC_NEGATION_OP))
	{
		match(LGC_NEGATION_OP);
		parseFormula();
	}
	else if (check(LGC_ALL_OP)|| check(LGC_EXIST_OP))
	{
		parseQuantifier();
		parseFormula();
	}
	else
		s = (string)(((Token)getLookAheadToken()).tostring()) ;
}

//<binary-operator> 	::= 	'and' 		| 'or' 		| 'modus'
void Parser::parseBin_operator()
{
	if(check(LGC_INTERSECTION_OP))
		match(LGC_INTERSECTION_OP);
	else if (check(LGC_UNION_OP))
		match(LGC_UNION_OP);
	else if (check (LGC_MAPPING_OP))
		match(LGC_MAPPING_OP);
	else 
		s = (string)(((Token)getLookAheadToken()).tostring()) ;
}

//<quantifier> 		::= 	  'all' var  	|  'exists' var
void Parser::parseQuantifier()
{
	if (check(LGC_ALL_OP)){
		match(LGC_ALL_OP);
		match(LGC_VAR);
	}
	else if (check(LGC_EXIST_OP))
	{
		match(LGC_EXIST_OP);
		match(LGC_CON);
	}
	else
		s = (string)(((Token)getLookAheadToken()).tostring()) ;
}
