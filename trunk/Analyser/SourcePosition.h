// SourcePosition.h: interface for the SourcePosition class.
//
//////////////////////////////////////////////////////////////////////

#if !defined(AFX_SOURCEPOSITION_H__A941B298_29A8_4E28_B09B_046F9DD0A893__INCLUDED_)
#define AFX_SOURCEPOSITION_H__A941B298_29A8_4E28_B09B_046F9DD0A893__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000
#include <string>
#include <iostream>
using namespace std;

class SourcePosition  
{
public:

	void EndToken();
	void NewLine();
	SourcePosition(int iCharStart, int iCharFinish, int iLineStart, int iLineFinish);
	SourcePosition();
	virtual ~SourcePosition();
	SourcePosition(const SourcePosition& s);
	operator = (const SourcePosition& s);
	string toString();
	int m_iLineFinish;
	int m_iLineStart;
	int m_iCharFinish;
	int m_iCharStart;
	
};

#endif // !defined(AFX_SOURCEPOSITION_H__A941B298_29A8_4E28_B09B_046F9DD0A893__INCLUDED_)
