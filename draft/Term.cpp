// Term.cpp: implementation of the Term class.
//
//////////////////////////////////////////////////////////////////////

#include "Term.h"

//////////////////////////////////////////////////////////////////////
// Construction/Destruction
//////////////////////////////////////////////////////////////////////


//Only kind
Term::Term(int kind)
{
	m_kind = kind;
}

//var or const
Term::Term(int kind,string name)
{
	m_kind = kind;
	m_name = name;
}

//reference
Term::Term(int kind,int ref)
{
	m_kind = kind;
	m_iRef  = ref;
}

//predicate
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
