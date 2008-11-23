// Parser.cpp : Defines the entry point for the console application.
//

#include "Parser.h"
#define str	 (string)currentToken

Parser::Parser(Scanner* s)
{
	scanner = s;
	lookAheadToken = Token(LGC_NIL);
	isStarted = false;
}

void Parser::match(TokenKind tokenKind)
{
	//if((TokenKind)lookAheadToken == (TokenKind)LGC_NIL)
	if((TokenKind)lookAheadToken == (TokenKind)tokenKind)
	{
		currentToken = lookAheadToken;
		lookAheadToken = scanner->nextToken();
	}
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
	s = "";
	lookAheadToken = scanner->nextToken();
	data.BeginSentence();
	parseSource();
	if (!check(LGC_NIL))
	{
		s = (string)(((Token)getLookAheadToken()).tostring());
	}
	data.EndSentence(); 	
}

//<source>		::= 	<formula> <tail>  
void Parser::parseSource()
{
	if (s=="")
	{
		if (check(LGC_CON)||check(LGC_VAR)||check(LGC_ALL_OP)||check(LGC_NEGATION_OP)||check(LGC_EXIST_OP)||check(LGC_LEFTPAR))
		{
			
			parseFormula();
			parseTail();
		}
		else
			s = (string)(((Token)getLookAheadToken()).tostring());
	}
}

//<formula>		::=   const	|  'not' <formula>  |  <quantifier> <formula> 	| const <argument-list>	| var <argument-list>	|'(' <source> ')'
void Parser::parseFormula()
{
	if (s == "")
	{	if(check(LGC_CON))
		{
			
			match(LGC_CON);
			if(check(LGC_LEFTPAR))
			{
				data.BeginFunction(str);
				parseArg_list();
				data.EndFunction();
			}
			else
			{
				data.NewVar(str,LGC_TERM_CONST);
			}
		}
		else if (check(LGC_VAR))
		{
			match(LGC_VAR);
			data.BeginFunction(str);
			parseArg_list();
			data.EndFunction();
		}
		else if (check(LGC_NEGATION_OP))
		{
			match(LGC_NEGATION_OP);
			data.NewLogicOp(LGC_OP_NOT);
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
			data.LeftPar();
			parseSource();
			match(LGC_RIGHTPAR);
			data.RightPar();
		}
		else
			s = (string)(((Token)getLookAheadToken()).tostring());
	}	
}

//<tail>				::= 	',' <source> |  <binary-operator><source>  |	
void Parser::parseTail()
{
	if (s == "")
	{
		if(check(LGC_COMMA))
		{
			data.EndSentence();
			match(LGC_COMMA);
			data.BeginSentence();
			parseSource();
		}
		else if (check(LGC_INTERSECTION_OP) || check(LGC_UNION_OP) || check(LGC_MAPPING_OP))
		{
			parseBin_operator();
			parseSource();
		}

	}
}

//<argument-list>		::=	'(' <arg> <arg-tail> 
void Parser::parseArg_list()
{
	if (s=="")
	{
		if (check(LGC_LEFTPAR))
		{
			match(LGC_LEFTPAR);
			parseArg();
			parseArg_tail();
		}
		else
			s = (string)(((Token)getLookAheadToken()).tostring()) ;
	}
}	

//<arg-tail> 			::= 	','<arg><arg-tail> 	|  ')'
void Parser::parseArg_tail()
{
	if (s=="")
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
}

//<arg> 				::= 	var		|	const | var <argument-list>|'not' <formula> |<quantifier> <formula>
void Parser::parseArg()
{
	if (s=="")
	{
		data.BeginArg();

		if (check(LGC_VAR))
		{
			match(LGC_VAR);

			if(check(LGC_LEFTPAR))
			{
				data.BeginFunction(str);
				parseArg_list();
				data.EndFunction();
			}
			else
			{
				data.NewVar(str,LGC_TERM_VAR);
			}
		}
		else if(check (LGC_CON))
		{
			match(LGC_CON);
			data.NewVar(str,LGC_TERM_CONST);
		}
		else if (check(LGC_NEGATION_OP))
		{
			match(LGC_NEGATION_OP);
			data.NewLogicOp(LGC_OP_NOT);
			parseFormula();
		}
		else if (check(LGC_ALL_OP)|| check(LGC_EXIST_OP))
		{
			parseQuantifier();
			parseFormula();
		}
		else
			s = (string)(((Token)getLookAheadToken()).tostring()) ;

		data.EndArg();
	}
}

//<binary-operator> 	::= 	'and' 		| 'or' 		| 'modus'
void Parser::parseBin_operator()
{
	if (s=="")
	{
		if(check(LGC_INTERSECTION_OP))
		{
			match(LGC_INTERSECTION_OP);
			data.NewLogicOp(LGC_OP_AND);
		}
		else if (check(LGC_UNION_OP))
		{
			match(LGC_UNION_OP);
			data.NewLogicOp(LGC_OP_OR);
		}
		else if (check (LGC_MAPPING_OP))
		{
			match(LGC_MAPPING_OP);
			data.NewLogicOp(LGC_OP_MAP);
		}
		else 
			s = (string)(((Token)getLookAheadToken()).tostring()) ;
	}
}

//<quantifier> 		::= 	  'all' var  	|  'exists' var
void Parser::parseQuantifier()
{
	if (s=="")
	{
		if (check(LGC_ALL_OP))
		{
			match(LGC_ALL_OP);
			match(LGC_VAR);
			data.NewQuan(str,LGC_QUAN_ALL);
		}
		else if (check(LGC_EXIST_OP))
		{
			match(LGC_EXIST_OP);
			match(LGC_VAR);
			data.NewQuan(str,LGC_QUAN_EXIST);
		}
		else
			s = (string)(((Token)getLookAheadToken()).tostring()) ;
	}
}
