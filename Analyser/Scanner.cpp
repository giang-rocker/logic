// Scanner.cpp: implementation of the Scanner class.
//
//////////////////////////////////////////////////////////////////////

#include "Scanner.h"
#include <stdio.h>


//////////////////////////////////////////////////////////////////////
// Construction/Destruction
//////////////////////////////////////////////////////////////////////

Scanner::Scanner()
{
	m_state  = 0;
}

Scanner::~Scanner()
{

}

Scanner::Scanner(const string &text)
{
	m_state = 0;
}

char Scanner::nextChar()
{	
	position.m_iCharFinish++;
	return buff.goAheadOneChar();
}

char Scanner::goAheadOneChar()
{
	char c = buff.goAheadOneChar();		
	buff.bcurrent--;
	return c;
}

void Scanner::goBackOneChar()
{
	buff.bcurrent--;
}

bool Scanner::isLetter(char c)
{
	return ('a'<=c && c <='z')||('A'<=c&& c<='Z');
}
bool Scanner::isLetterOrDigit(char c)
{
	int code = (int) c;
	return ((int)'a' <= code && code <= (int)'z' ) || ((int)'A' <= code && code <= (int)'Z' ) || ((int)'0' <= code && code <= (int)'9' ) ;
}

Token Scanner::nextToken()
{
	m_state = 0;
	Token result;
	char c= NULL;
	char t= NULL;
	while (true)
	{
		switch (m_state)
		{
		case 0 :
			c = nextChar();
			m_text=c;
                if (c == ' ' || c == '\t' || c== '\r' || c == '\n' ) 
				{
                    if (c == '\n') 
					{
                    	    position.NewLine();
                    }	          	    
                    else if(c== '\t')
					{
                    	position.m_iCharStart += 8;
                    	position.m_iCharFinish = position.m_iCharStart-1;
					}
	                else 
					{
	                	position.m_iCharStart++;//charFinish has already increased by 1
					}
				}				
				else if (isLetter(c)) 
				{
						m_state = 1;
				}
				else if (c== '=') 
				{
						c = goAheadOneChar();
						if(c== '>')
						{
								m_text += c;
								c=nextChar();
								result = Token(MAPPING_OP,m_text,position);
								position.m_iCharFinish++;
								position.EndToken();
								return result;
						}
						else
						{
								result = Token(ERROR,m_text,position)	;
								position.m_iCharFinish++;
								position.EndToken();
								return result;
						}
				}
				else if (c== '<') 
				{
						c = goAheadOneChar();
						if(c== '>')
						{ // <>
								m_text += c;
								c=nextChar();
								result = Token(CONTRADITION_OP,m_text,position);
								position.m_iCharFinish++;
								position.EndToken();
								return result;
						}

						else if (c == '=')
						{ //<=
								m_text += c;
								c = goAheadOneChar();
								if (c == '>') 
								{ // <=>
										m_text += c;
										c = nextChar();
										c = nextChar();
										result = Token(EQUIVALENT_OP,m_text,position);
										position.EndToken();
										return result;
								}
								else 
								{
										result = Token(ERROR,m_text,position)	;
										position.m_iCharFinish++;
										position.EndToken();
										return result;
								}
						}
								
						else
						{
								result = Token(ERROR,m_text,position)	;
								position.m_iCharFinish++;
								position.EndToken();
								return result;
						}
					}
				else if( c=='&'){
						result = Token(INTERSECTION_OP,"&",position);
						position.m_iCharFinish++;
						position.EndToken();
						return result;
					}
				else if( c=='|'){
						result = Token(UNION_OP,"|",position);
						position.m_iCharFinish++;
						position.EndToken();
						return result;
					}
				else if( c=='!'){
						result = Token(NEGATION_OP,"!",position);
						position.m_iCharFinish++;
						position.EndToken();
						return result;
					}
				else if( c=='('){
						result = Token(LEFTPAR,"(",position);
						position.m_iCharFinish++;
						position.EndToken();
						return result;
					}
				else if( c==')'){
						result = Token(RIGHTPAR,")",position);
						position.m_iCharFinish++;
						position.EndToken();
						return result;
					}
				else if((int)c == 0)
					{
						m_text="$";
						result = Token(NIL,m_text,position)	;
						position.m_iCharFinish++;
						position.EndToken();
						return result;
					}
				else{
						result = Token(ERROR,m_text,position)	;
						position.m_iCharFinish++;
						position.EndToken();
						return result;
					}
				break;
		case 1:
				m_text = "";
				while (true){
						if (!(isLetterOrDigit(c) || c == '_'))
							break;
						else{
	                			m_text += c;
							}
						c = nextChar();
					}
				if (m_text == "AND" || m_text == "and")
						result = Token(INTERSECTION_OP,m_text,SourcePosition(position.m_iCharStart,position.m_iCharFinish-1,position.m_iLineStart,position.m_iLineFinish));
				else if (m_text == "OR" || m_text == "or")
						result = Token(UNION_OP,m_text,SourcePosition(position.m_iCharStart,position.m_iCharFinish-1,position.m_iLineStart,position.m_iLineFinish));
				else if (m_text == "NOT" )
						result = Token(NEGATION_OP,m_text,SourcePosition(position.m_iCharStart,position.m_iCharFinish-1,position.m_iLineStart,position.m_iLineFinish));
				else if (m_text == "true" || m_text == "TRUE"|| m_text == "FALSE"|| m_text == "false")
						result = Token(BOOLEANLITERAL,m_text,SourcePosition(position.m_iCharStart,position.m_iCharFinish-1,position.m_iLineStart,position.m_iLineFinish));
				else 
						result = Token(IDENTIFER,m_text,SourcePosition(position.m_iCharStart,position.m_iCharFinish-1,position.m_iLineStart,position.m_iLineFinish));

				position.EndToken();
				goBackOneChar();
				return result;
		}
	}
}


Buffer::Buffer(string filename)
{
	buffer = new char[1024];
	for(int i = 0;i < 1024  ; i++)
	{
		buffer[i] = 0;
	}
	bcurrent = -1;
	FILE* file = fopen("filename","r");
	fread(buffer,sizeof(char),1024,file);
	fclose(file);
}
Buffer::Buffer() 
{
	buffer = new char[1024];

	for(int i = 0;i < 1024  ; i++)
	{
		buffer[i] = 0;
	}
	bcurrent = -1;
	cout<<"Nhap bai toan: ";
	cin.getline(buffer,1024);
	
}
char Buffer::goAheadOneChar()
{	
	bcurrent++;
	return buffer[bcurrent];
}
