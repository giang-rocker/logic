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