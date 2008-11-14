// Token.cpp: implementation of the Token class.
//
//////////////////////////////////////////////////////////////////////

#include "Token.h"

//////////////////////////////////////////////////////////////////////
// Construction/Destruction
//////////////////////////////////////////////////////////////////////

Token::Token()
{
	m_lexeme="";
}

Token::~Token()
{

}

Token::Token(TokenKind kind)
{
	m_kind = kind;
	m_lexeme = "";
}

Token::Token(TokenKind kind, const string& lexeme)
{
	m_kind = kind;
	m_lexeme = lexeme;
}

Token::Token(TokenKind kind, const string& lexeme, SourcePosition position)
{
	m_kind = kind;
	m_lexeme = lexeme;
	m_position = position;
}

Token::Token(const Token& t)
{
	m_kind = t.m_kind;
	m_lexeme = t.m_lexeme;
	m_position = t.m_position;
}

Token::operator =(const Token& t)
{
	m_kind = t.m_kind;
	m_lexeme = t.m_lexeme;
	m_position = t.m_position;
}

Token::operator string() const
{		
	return m_lexeme;
}

Token::operator TokenKind() const
{
	return m_kind;
}

Token::operator SourcePosition()const
{
	return m_position;
} 

string Token::convertToken()
{
	switch (m_kind){
		case LGC_VAR : 
			return "Token.LGC_VAR";
		case LGC_INTERSECTION_OP:
            return "Token.LGC_INTERSECTION_OP";
		case LGC_UNION_OP:
            return "Token.LGC_UNION_OP";
		case LGC_NEGATION_OP:
            return "Token.LGC_NEGATION_OP";
		case LGC_MAPPING_OP:
            return "Token.LGC_MAPPING_OP";
		case LGC_EQUIVALENT_OP:
            return "Token.LGC_EQUIVALENT_OP";
		case LGC_LEFTPAR:
            return "Token.LGC_LEFTPAR";
		case LGC_RIGHTPAR:
            return "Token.LGC_RIGHTPAR";
		case LGC_BOOLEANLITERAL:
            return "Token.LGC_BOOLEANLITERAL";
		case LGC_CONTRADITION_OP:
            return "Token.LGC_CONTRADITION_OP";
		case LGC_ALL_OP:
            return "Token.LGC_ALL_OP";
		case LGC_EXIST_OP:
            return "Token.LGC_EXIST_OP";
		case LGC_RESULT_OP:
            return "Token.LGC_RESULT_OP";
		case LGC_NIL:
            return "Token.LGC_NIL";
		case LGC_COMMA:
			return "Token.COMMA";
		case LGC_CON:
			return "Token.CON"
		default: 
			return "Token.LGC_ERROR";	
	}
}