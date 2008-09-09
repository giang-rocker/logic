#include "Token.h"

Token::Token()
{
	m_Sp_Position = new SourcePosition(); 
}

Token::Token(int kind)
{
	m_Sp_Position = new SourcePosition();
	m_iKind = kind;
}

Token::Token(int kind, const char *lexeme)
{
	m_Sp_Position = new SourcePosition();
	m_iKind = kind;
	memcpy(
}