// Term.cpp: implementation of the Term class.
//
//////////////////////////////////////////////////////////////////////

#include "Term.h"

//////////////////////////////////////////////////////////////////////
// Construction/Destruction
//////////////////////////////////////////////////////////////////////



Term::Term(int kind)
{
	m_kind = kind;
}


Term::Term(int kind,string name)
{
	m_kind = kind;
	m_name = name;
}


Term::Term(int kind,int ref)
{
	m_kind = kind;
	m_iRef  = ref;
}


Term::Term(int kind,string name,int args)
{
	m_kind = kind;
	m_name = name;
	m_iArgs = args;

}

Term::Term()
{

}

//deduction
Term::~Term()
{

}
