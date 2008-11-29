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
	
	LGC_ERROR			=	1,	// Error
	LGC_VAR				=	2,	// Identifier
	LGC_INTERSECTION_OP	=	3,	// AND operator
	LGC_UNION_OP		=	4,	// OR  operator
	LGC_NEGATION_OP		=	5,	// NOT operator
	LGC_MAPPING_OP		=	6,	// => or ->
	LGC_EQUIVALENT_OP	=	7,	// <=> or <->
	LGC_LEFTPAR			=	8,	// (
	LGC_RIGHTPAR		=	9,	// )
	LGC_BOOLEANLITERAL	=	10,	//	TRUE FALSE true false
	LGC_CONTRADITION_OP	=	11,	//	<>
	LGC_ALL_OP			=	12, // V-	
	LGC_EXIST_OP		=	13, // -]
	LGC_RESULT_OP		=	14, // =|
	LGC_NIL				=	15, // End of text
	LGC_COMMA			=	16, // ,
	LGC_CON				=	17,
	
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
	string tostring();
	operator TokenKind() const;
	operator SourcePosition() const;
	operator string()const;
	string convertToken();

private:
	SourcePosition m_position;
	TokenKind m_kind;
	string m_lexeme;
};

#endif // !defined(AFX_TOKEN_H__3D82A5A2_765D_4611_879D_1DEAE17211B9__INCLUDED_)

