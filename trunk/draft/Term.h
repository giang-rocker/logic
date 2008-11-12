// Term.h: interface for the Term class.
//
//////////////////////////////////////////////////////////////////////
#include <string>
using namespace std;

#if !defined(AFX_TERM_H__DF7363EB_8D45_46DF_8160_151A29AB07FC__INCLUDED_)
#define AFX_TERM_H__DF7363EB_8D45_46DF_8160_151A29AB07FC__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000




//Quantifier
const int LGC_ALL_QUAN		= 1;
const int LGC_EXIST_QUAN	= 2;



//Term kind
const int LGC_VAR			= 1;
const int LGC_CONST			= 2;
const int LGC_PRE			= 3;
const int LGC_REF			= 4;
const int LGC_QUA			= 5;
const int LGC_

//System operators
const int LGC_NOT_OP		= -1;
const int LGC_AND_OP		= -2;
const int LGC_OR_OP			= -3;
const int LGC_MAP_OP		= -4;
const int LGC_LEFT_PAR		= -5;
const int LGC_RIGHT_PAR		= -6;	
const int LGC_MARK_PRE		= -7;
const int LGC_MARK_ARG		= -8;
const int LGC_MARK_TERM		= -9;
const int LGC_MARK_OP		= -10;

//System operators name
const string LGC_NOT_FUNC("~");
const string LGC_AND_FUNC("&");
const string LGC_OR_FUNC("|");
const string LGC_MAP_FUNC("->");	



class Term  
{

public:
	Term();
	Term(int kind);			//only kind
	Term(int kind,string name);// Var or const
	Term(int kind,int ref);    // Reference kind
	Term(int kind,string name,int args);//predicate
	//Term(int kind,string name,int quantifier);	  // Use for its quantifier
	virtual ~Term();


	int m_kind;		// term type
	string m_name;	// term name (exist when not reference kind)
	int m_iRef;		// point to exist terms
	int m_iArgs;	// number of args iff it's FUNCTION
};

#endif // !defined(AFX_TERM_H__DF7363EB_8D45_46DF_8160_151A29AB07FC__INCLUDED_)
