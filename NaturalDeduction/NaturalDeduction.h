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
#define LGC_E_OR_1		3
#define LGC_E_OR_2		4
#define LGC_E_MODUS		5
#define LGC_E_NOT		6
#define LGC_E_ALL		7
#define LGC_E_EXISTS	8

//introduction rules
#define LGC_I_AND		9
#define LGC_I_OR_1		10
#define LGC_I_OR_2		11
#define LGC_I_MODUS		12
#define LGC_I_NOT		13
#define LGC_I_ALL		14
#define LGC_I_EXISTS	15
/////////////////////////

#define LGC_ID			16
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
	int ProveIt();
	bool isComplement(int active, int negative) const;
	int Contradiction();
	int Introduction(int subgoal);
	int Eliminate();
	bool isCompatible(int father,int son)const;
	NaturalDeduction(TermVector t);
	int print();

private:
	int isReached(int subgoal);
	list <NDTerm> condition;
	list <NDTerm> goal;
	vector <int> andMarked;
	vector <int> notMarked;
	vector <int> mdMarked;
	vector <int> or1Marked;
	vector <int> or2Marked;

	TermVector database;
	int intro;
};

#endif // !defined(AFX_NATURALDEDUCTION_H__492CA570_429A_43E2_B2B6_E40C8EFCCA2C__INCLUDED_)
