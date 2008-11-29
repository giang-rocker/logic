// NaturalDeduction.h: interface for the NaturalDeduction class.
//
//////////////////////////////////////////////////////////////////////

#if !defined(AFX_NATURALDEDUCTION_H__492CA570_429A_43E2_B2B6_E40C8EFCCA2C__INCLUDED_)
#define AFX_NATURALDEDUCTION_H__492CA570_429A_43E2_B2B6_E40C8EFCCA2C__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000
#include "../TermVector/TermVector.h"



//////////////////////////////////////////////////////////////////////////
#define LGC_FLAG_ABSOLUTE	1		//Eliminate from all
#define LGC_FLAG_RELATIVE	2		//Eliminate from exists			


//////////////////////////////////////////////////////////////////////////

#define LGC_RULE_PREMISE	0
#define LGC_RULE_ID			1


//////////////////////////////////////////////////////////////////////////

#define LGC_E_AND_1		2
#define LGC_E_AND_2		3
#define LGC_E_OR_1		4
#define LGC_E_OR_2		5
#define LGC_E_MODUS		6
#define LGC_E_NOT		7
#define LGC_E_ALL		8
#define LGC_E_EXISTS	9


//////////////////////////////////////////////////////////////////////////


#define LGC_I_AND		10
#define LGC_I_OR_1		11
#define LGC_I_OR_2		12
#define LGC_I_MODUS		13
#define LGC_I_NOT		14
#define LGC_I_ALL		15
#define LGC_I_EXISTS	16


//////////////////////////////////////////////////////////////////////////

#define LGC_LST_GOAL		1
#define LGC_LST_PROVED		2
#define LGC_LST_CONDITION	3

//////////////////////////////////////////////////////////////////////////
#define LGC_FLAG_E_NOT	0x0001
#define LGC_FLAG_E_AND	0x0002
#define LGC_FLAG_E_OR1	0x0004
#define LGC_FLAG_E_OR2	0x0008
#define LGC_FLAG_E_OR3	0x0010
#define LGC_FLAG_E_MAP	0x0011

#define LGC_FLAG_I_OR1	0x1000
#define LGC_FLAG_I_OR2	0x1001
#define LGC_FLAG_I_OR3	0x1002


//////////////////////////////////////////////////////////////////////////

struct NDTerm
{
	int m_index;	
	int m_first;		
	int m_second;		
	int m_rule;	
	int m_path;
	int m_assume;
	int m_pendings;
	int m_status;
	NDTerm(int index = 0, int rule = 0, int first = 0, int second = 0)
	{
		m_index = index ;
		m_rule = rule ;
		m_first = first ;
		m_second = second ;
		m_assume = 0 ;
		m_pendings = 0 ;
		m_path = 0;
		m_status = 0;
	}

};


class NaturalDeduction  
{
public:
	int InsertTerm(NDTerm term);
	int ProveIt();
	bool isComplement(int active, int negative) const;
	int Contradiction();
	int Introduction();
	int Eliminate();
	bool isCompatible(int father,int son)const;
	NaturalDeduction(TermVector t);
	int print();

private:
	int isReached(int subgoal);
	list <NDTerm> conditions;
	list <NDTerm> goals;
	list <NDTerm> proveds;


	TermVector database;

};

#endif // !defined(AFX_NATURALDEDUCTION_H__492CA570_429A_43E2_B2B6_E40C8EFCCA2C__INCLUDED_)
