// NaturalDeduction.h: interface for the NaturalDeduction class.
//
//////////////////////////////////////////////////////////////////////

#if !defined(AFX_NATURALDEDUCTION_H__492CA570_429A_43E2_B2B6_E40C8EFCCA2C__INCLUDED_)
#define AFX_NATURALDEDUCTION_H__492CA570_429A_43E2_B2B6_E40C8EFCCA2C__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000
#include "../TermVector/TermVector.h"

#define LGC_FLAG_ANY	1
#define LGC_FLAG_SOME	0
#define LGC_FLAG_RES	-1


struct NDTerm
{
	int m_index;		//Index in term vector
	bool m_isMarked;	//Self deduction allowed or not
	int m_parent1;		//First parent
	int m_parent2;		//Second parent
	int m_rule;			//Which rule creates it from its parent(s)
	NDTerm(int index = 0,bool marked = false,int parent1 = 0, int parent2 = 0, int rule =0)
	{
		m_index = index;
		m_isMarked = marked;
		m_parent1 = parent1;
		m_parent2 = parent2;
		m_rule = rule;
	}
};

class NaturalDeduction  
{
public:
	int Contradiction();
	int Introduction();
	int Eliminate();
	bool isCompatible(int father,int son);
	NaturalDeduction(TermVector t);

private:
	list <NDTerm> condition;
	list <NDTerm> goal;
	TermVector database;
};

#endif // !defined(AFX_NATURALDEDUCTION_H__492CA570_429A_43E2_B2B6_E40C8EFCCA2C__INCLUDED_)
