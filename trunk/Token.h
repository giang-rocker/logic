#ifndef _TOKEN_
#define _TOKEN_
#include"SourcePosition.h"


class Token
{
public:

		static const int EOF		=	0;
		static const int ERROR		=	1;
		static const int ID			=	2;
		static const int AND		=	3;	//	& 
		static const int OR			=	4;	//	|
		static const int NOT		=	5;	//	~  or !
		static const int IMPLY		=	6;	//	=>
		static const int EQUI		=	7;	//	<=>
		
		Token();
		Token(int kind);
		Token(int kind, const char* lexeme);
		Token(int kind, const char* lexeme,const SourcePosition& sp);

		
private:
		int m_iKind;		
		char *m_str_Lexeme;	
		SourcePosition *m_Sp_Position;

};
#endif