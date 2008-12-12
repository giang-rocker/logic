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
#include <iostream>
#include <stdio.h>
#include <ctype.h>
using namespace std;


class Scanner  
{
public:
	Token nextToken();
	Scanner(const string& text);
	virtual ~Scanner();
	
private:
	string m_text;
	int index;
	int m_state;
	SourcePosition position;
		
	void goBackOneChar();
	char goAheadOneChar();
	char goAheadTwoChar();
	char nextChar();
};



#endif // !defined(AFX_SCANNER_H__C606F88E_1CCF_436A_AE97_A7C35E6832AA__INCLUDED_)
