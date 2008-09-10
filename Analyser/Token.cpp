// Token.cpp: implementation of the Token class.
//
//////////////////////////////////////////////////////////////////////

#include "Token.h"

//////////////////////////////////////////////////////////////////////
// Construction/Destruction
//////////////////////////////////////////////////////////////////////

Token::Token()
{

}

Token::~Token()
{

}

Token::Token(TokenKind kind)
{

}

Token::Token(TokenKind kind, const string& lexeme)
{

}

Token::Token(TokenKind kind, const string& lexeme, SourcePosition position)
{

}

Token::Token(const Token& t)
{

}

Token::operator =(const Token& t)
{

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