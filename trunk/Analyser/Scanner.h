// Scanner.h: interface for the Scanner class.
//
//////////////////////////////////////////////////////////////////////

#if !defined(AFX_SCANNER_H__C606F88E_1CCF_436A_AE97_A7C35E6832AA__INCLUDED_)
#define AFX_SCANNER_H__C606F88E_1CCF_436A_AE97_A7C35E6832AA__INCLUDED_

#include "Token.h"	// Added by ClassView
#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000

//////////////////////////////////////////////////////////////////////////
#define  CHAR_AND_OP	'&'
#define  CHAR_OR_OP		'|'
#define  CHAR_NOT_OP	'!'
#define  CHAR_END		0
//////////////////////////////////////////////////////////////////////////
#include "Token.h"

class Scanner  
{
public:
	int Scanner::NextToken(Token& t);
	Scanner(const string& text);
	Scanner();
	virtual ~Scanner();
	
private:
	char* m_text;
	int m_current;
	int m_forward;
	int m_state;

	char nextChar();
	bool isLetter(char c)const;
	string retractToken(int lookAhead)const;
	SourcePosition retractPosition(int lookAhead)const;
	
};

#endif // !defined(AFX_SCANNER_H__C606F88E_1CCF_436A_AE97_A7C35E6832AA__INCLUDED_)
