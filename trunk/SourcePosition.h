#ifndef _SOURCE_POSITION_
#define _SOURCE_POSITION_

class SourcePosition
{


public:
	SourcePosition();
	SourcePosition(int iCharStart, int iCharFinish, int iLineStart, int iLineFinish);
	SourcePosition(const SourcePosition&s);
	operator = (const SourcePosition &s);
	
	void NewLine();
	void EndToken();

private:
	int m_iCharStart;
	int m_iCharFinish;
	int m_iLineStart;
	int m_iLineFinish;


};


#endif