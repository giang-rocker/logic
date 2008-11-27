// NaturalDeduction.h: interface for the NaturalDeduction class.
//
//////////////////////////////////////////////////////////////////////

#if !defined(AFX_NATURALDEDUCTION_H__492CA570_429A_43E2_B2B6_E40C8EFCCA2C__INCLUDED_)
#define AFX_NATURALDEDUCTION_H__492CA570_429A_43E2_B2B6_E40C8EFCCA2C__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000
#include "../TermVector/TermVector.h"

#define LGC_FLAG_ABSOLUTE	1		//Eliminate from all
#define LGC_FLAG_RELATIVE	2		//Eliminate from exists			


//////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////
//Eliminate rules
#define LGC_E_AND_1		1
#define LGC_E_AND_2		2
#define LGC_E_OR		3
#define LGC_E_MODUS		4
#define LGC_E_NOT		5
#define LGC_E_ALL		6
#define LGC_E_EXISTS	7

//introduction rules
#define LGC_I_AND		8
#define LGC_I_OR_1		9
#define LGC_I_OR_2		10
#define LGC_I_MODUS		11
#define LGC_I_NOT		12
#define LGC_I_ALL		13
#define LGC_I_EXISTS	14
/////////////////////////

#define LGC_ID			15
//////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////

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
	int print();

private:
	list <NDTerm> condition;
	list <NDTerm> goal;
	vector <int> andMarked;
	vector <int> notMarked;
	vector <int> mdMarked;
	TermVector database;
};

#endif // !defined(AFX_NATURALDEDUCTION_H__492CA570_429A_43E2_B2B6_E40C8EFCCA2C__INCLUDED_)
