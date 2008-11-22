// SourcePosition.cpp: implementation of the SourcePosition class.
//
//////////////////////////////////////////////////////////////////////

#include "SourcePosition.h"
#include < sstream >

//////////////////////////////////////////////////////////////////////
// Construction/Destruction
//////////////////////////////////////////////////////////////////////

SourcePosition::SourcePosition()
{
	m_iCharStart = 1 ;
	m_iCharFinish = 0 ;
	m_iLineStart = 1 ;
	m_iLineFinish = 1 ;

}

SourcePosition::~SourcePosition()
{

}


SourcePosition::SourcePosition(int iCharStart, int iCharFinish, int iLineStart, int iLineFinish)
{

	m_iCharStart = iCharStart ;
	m_iCharFinish = iCharFinish ;
	m_iLineStart = iLineStart ;
	m_iLineFinish = iLineFinish ;
}


SourcePosition::SourcePosition(const SourcePosition& s)
{
	m_iCharStart = s.m_iCharStart ;
	m_iCharFinish = s.m_iCharFinish ;
	m_iLineStart = s.m_iLineStart ;
	m_iLineFinish = s.m_iLineFinish ;
}


SourcePosition::operator =(const SourcePosition& s)
{
	m_iCharStart = s.m_iCharStart ;
	m_iCharFinish = s.m_iCharFinish ;
	m_iLineStart = s.m_iLineStart ;
	m_iLineFinish = s.m_iLineFinish ;	
}


void SourcePosition::NewLine()
{
	m_iCharStart = ++m_iLineFinish;
	m_iCharStart = 1;
	m_iCharFinish = 0;
}


void SourcePosition::EndToken()
{
	m_iCharStart = m_iCharFinish;
	m_iCharFinish--;
	m_iLineStart = m_iLineFinish;
}

string Int2Str(int value)
{
	ostringstream os;
	os << value;
	return os.str();
}


string SourcePosition::toString()
{
	return "CharStart:"+ Int2Str(m_iCharStart)+"\tCharFinish:"+ Int2Str(m_iCharFinish);
}
