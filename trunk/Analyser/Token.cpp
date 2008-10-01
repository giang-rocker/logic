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
		int i = m_kind;
		if (i == 2) {
            return "Token.LGC_IDENTIFER";
        } else if (i == 3) {
            return "Token.LGC_INTERSECTION_OP";
        } else if (i == 4) {
            return "Token.LGC_UNION_OP";
        } else if (i == 5) {
            return "Token.LGC_NEGATION_OP";
        } else if (i == 6) {
            return "Token.LGC_MAPPING_OP";
        } else if (i == 7) {
            return "Token.LGC_EQUIVALENT_OP";
        } else if (i == 8) {
            return "Token.LGC_LEFTPAR";
        } else if (i == 9) {
            return "Token.LGC_RIGHTPAR";
        } else if (i == 10) {
            return "Token.LGC_BOOLEANLITERAL";
        } else if (i == 11) {
            return "Token.LGC_CONTRADITION_OP";
        } else if (i == 12) {
            return "Token.LGC_ALL_OP";
        } else if (i == 13) {
            return "Token.LGC_EXIST_OP";
		} else if (i == 14) {
            return "Token.LGC_RESULT_OP";
        } else if (i == 15) {
            return "Token.LGC_NIL";
        } else {
            return "Token.LGC_ERROR";
		}
}