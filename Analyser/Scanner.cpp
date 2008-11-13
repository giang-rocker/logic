// Scanner.cpp: implementation of the Scanner class.
//
//////////////////////////////////////////////////////////////////////

#include "Scanner.h"
#include <stdio.h>


//////////////////////////////////////////////////////////////////////
// Construction/Destruction
//////////////////////////////////////////////////////////////////////

Scanner::~Scanner()
{
	
}

Scanner::Scanner(const string &text)
{
	m_text.assign(text);
	index = -1;
	m_state = 0;
}

char Scanner::nextChar()
{	
	index++;
	position.m_iCharFinish++;

	if(index == m_text.length())
	{
		return (char)0;
	}

	return m_text.at(index);
}

char Scanner::goAheadOneChar()
{

	if(index == m_text.length() - 1)
	{
		return (char)0;
	}
	return m_text.at(index+1);
}

void Scanner::goBackOneChar()
{
	index--;
}

Token Scanner::nextToken()
{
	m_state = 0;
	Token result;
	char c = NULL;
	string lexeme="";
	while (true)
	{
		switch (m_state)
		{
		case 0 :
			c = nextChar();
			lexeme = c;
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
				else if (c== 'V') 
				{
						c = goAheadOneChar();
						if(c== '-')
						{ // V-
								lexeme += c;
								c=nextChar();
								result = Token(LGC_ALL_OP,lexeme,position);
								position.m_iCharFinish++;
								position.EndToken();
								return result;
						}
						else
						{
								result = Token(LGC_ERROR,lexeme,position)	;
								position.m_iCharFinish++;
								position.EndToken();
								return result;
						}
				}

				else if (isalpha(c)) 
				{
						m_state = 1; 
						break;
				}

				else if (c== '=' ) 
				{
						c = goAheadOneChar();
						if(c== '>') // => or ->
						{
								lexeme += c;
								c=nextChar();
								result = Token(LGC_MAPPING_OP,lexeme,position);
								position.m_iCharFinish++;
								position.EndToken();
								return result;
						}
						if(c== '|') // =| 
						{
								lexeme += c;
								c=nextChar();
								result = Token(LGC_RESULT_OP,lexeme,position);
								position.m_iCharFinish++;
								position.EndToken();
								return result;
						}
						else
						{
								result = Token(LGC_ERROR,lexeme,position)	;
								position.m_iCharFinish++;
								position.EndToken();
								return result;
						}
				}

				

				else if (c== '-') 
				{
						c = goAheadOneChar();
						if(c== ']')
						{								// -]
								lexeme += c;
								c=nextChar();
								result = Token(LGC_EXIST_OP,lexeme,position);
								position.m_iCharFinish++;
								position.EndToken();
								return result;
						}
						else if(c== '|')				// -| 
						{
								lexeme += c;
								c=nextChar();
								result = Token(LGC_RESULT_OP,lexeme,position);
								position.m_iCharFinish++;
								position.EndToken();
								return result;
						}
						else
						{
								result = Token(LGC_ERROR,lexeme,position)	;
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
								lexeme += c;
								c=nextChar();
								result = Token(LGC_CONTRADITION_OP,lexeme,position);
								position.m_iCharFinish++;
								position.EndToken();
								return result;
						}

						else if (c == '=' || c =='-')
						{ //<=	
								string temp = lexeme;
								c = nextChar();
								lexeme += c;
								c = goAheadOneChar();
								if (c == '>') 
								{ // <=> or <->
										lexeme += c;
										c = nextChar();
										position.m_iCharFinish++;
										result = Token(LGC_EQUIVALENT_OP,lexeme,position);
										position.EndToken();
										return result;
								}
								else 
								{
										index-=1;
										result = Token(LGC_ERROR,temp,position)	;
										position.m_iCharFinish++;
										position.EndToken();
										return result;
								}
						}
								
						else
						{
							
								result = Token(LGC_ERROR,lexeme,position)	;
								position.m_iCharFinish++;
								position.EndToken();
								return result;
						}
				}
				else if( c=='&')
				{
						result = Token(LGC_INTERSECTION_OP,"&",position);
						position.m_iCharFinish++;
						position.EndToken();
						return result;
				}
				else if( c=='|')
				{
						result = Token(LGC_UNION_OP,"|",position);
						position.m_iCharFinish++;
						position.EndToken();
						return result;
				}
				else if( c=='!')
				{
						result = Token(LGC_NEGATION_OP,"!",position);
						position.m_iCharFinish++;
						position.EndToken();
						return result;
				}
				else if( c=='(')
				{
						result = Token(LGC_LEFTPAR,"(",position);
						position.m_iCharFinish++;
						position.EndToken();
						return result;
				}
				else if( c==')')
				{
						result = Token(LGC_RIGHTPAR,")",position);
						position.m_iCharFinish++;
						position.EndToken();
						return result;
				}
				else if((int)c == 0)
				{
					lexeme ="$";
					result = Token(LGC_NIL,"$",position)	;
					position.m_iCharFinish++;
					position.EndToken();
					return result;
				}
				else
				{
						result = Token(LGC_ERROR,lexeme,position)	;
						position.m_iCharFinish++;
						position.EndToken();
						return result;
				}
				break;

		case 1:
				lexeme = "";
				while (true)
				{
					
					if ((isalnum(c)))
					{
						lexeme += c;
						c = nextChar();
					}
					else
					{
						break;
					}
					
				}

				if (lexeme == "AND" || lexeme == "and")
				{
					result = Token(LGC_INTERSECTION_OP,lexeme,SourcePosition(position.m_iCharStart,position.m_iCharFinish-1,position.m_iLineStart,position.m_iLineFinish));
				}
				else if (lexeme == "OR" || lexeme == "or")
				{
					result = Token(LGC_UNION_OP,lexeme,SourcePosition(position.m_iCharStart,position.m_iCharFinish-1,position.m_iLineStart,position.m_iLineFinish));
				}
				else if (lexeme == "NOT" || lexeme == "not")
				{
					result = Token(LGC_NEGATION_OP,lexeme,SourcePosition(position.m_iCharStart,position.m_iCharFinish-1,position.m_iLineStart,position.m_iLineFinish));
				}
				else if (lexeme == "true" || lexeme == "TRUE"|| lexeme == "FALSE"|| lexeme == "false")
				{
						result = Token(LGC_BOOLEANLITERAL,lexeme,SourcePosition(position.m_iCharStart,position.m_iCharFinish-1,position.m_iLineStart,position.m_iLineFinish));
				}
				else if (lexeme == "all" || lexeme == "ALL")
				{
						result = Token(LGC_ALL_OP,lexeme,SourcePosition(position.m_iCharStart,position.m_iCharFinish-1,position.m_iLineStart,position.m_iLineFinish));
				}
				else if (lexeme == "exists" || lexeme == "EXISTS")
				{
						result = Token(LGC_EXIST_OP,lexeme,SourcePosition(position.m_iCharStart,position.m_iCharFinish-1,position.m_iLineStart,position.m_iLineFinish));
				}
				else 
				{
						result = Token(LGC_IDENTIFER,lexeme,SourcePosition(position.m_iCharStart,position.m_iCharFinish-1,position.m_iLineStart,position.m_iLineFinish));
						
				}
				position.EndToken();
				goBackOneChar();
				return result;
		}
	}
}