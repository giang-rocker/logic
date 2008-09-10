// Token.h: interface for the Token class.
//
//////////////////////////////////////////////////////////////////////

#if !defined(AFX_TOKEN_H__3D82A5A2_765D_4611_879D_1DEAE17211B9__INCLUDED_)
#define AFX_TOKEN_H__3D82A5A2_765D_4611_879D_1DEAE17211B9__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000
#include <string>
#include "SourcePosition.h"	// Added by ClassView
using namespace std;

///Kind of token
enum TokenKind
{
	
	ERROR			=	1,	// Error
	IDENTIFER		=	2,	// Identifier
	INTERSECTION_OP	=	3,	// AND operator
	UNION_OP		=	4,	// OR  operator
	NEGATION_OP		=	5,	// NOT operator
	MAPPING_OP		=	6,	// =>
	EQUIVALENT_OP	=	7,	// <=>
	LEFTPAR			=	8,	// (
	RIGHTPAR		=	9,	// )
	BOOLEANLITERAL	=	10,	//	TRUE FALSE true false
	CONTRADITION_OP	=	11,	//	<>
	NIL				=	12, // End of text
	
};


class Token  
{
public:
	Token(TokenKind kind,const string& lexeme, SourcePosition position);
	Token(TokenKind kind,const string& lexeme);
	Token(TokenKind kind);
	Token();
	Token(const Token& t);
	virtual ~Token();
	operator = (const Token& t);
	operator string() const;
	operator TokenKind() const;
	operator SourcePosition() const;

private:
	SourcePosition m_position;
	TokenKind m_kind;
	string m_lexeme;
};

#endif // !defined(AFX_TOKEN_H__3D82A5A2_765D_4611_879D_1DEAE17211B9__INCLUDED_)
