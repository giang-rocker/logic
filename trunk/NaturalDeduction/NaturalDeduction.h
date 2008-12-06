// NaturalDeduction.h: interface for the NaturalDeduction class.
//
//////////////////////////////////////////////////////////////////////

#if !defined(AFX_NATURALDEDUCTION_H__492CA570_429A_43E2_B2B6_E40C8EFCCA2C__INCLUDED_)
#define AFX_NATURALDEDUCTION_H__492CA570_429A_43E2_B2B6_E40C8EFCCA2C__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000
#include "../TermVector/TermVector.h"
#include "Utils.h"
#include <sstream>


//////////////////////////////////////////////////////////////////////////
#define LGC_FLAG_ABSOLUTE	1		//Eliminate from all
#define LGC_FLAG_RELATIVE	2		//Eliminate from exists			


////////////////////////////
#define LGC_RULE_PREMISE	0x00000001
#define LGC_RULE_ID			0x00000002
////////////////////////////
#define LGC_E_AND_1			0x00000004
#define LGC_E_AND_2			0x00000008
#define LGC_E_OR_1			0x00000010
#define LGC_E_OR_2			0x00000020
#define LGC_E_MODUS			0x00000040
#define LGC_E_DNEG			0x00000080
#define LGC_E_ALL			0x00000100
#define LGC_E_EXISTS		0x00000200
#define LGC_E_NOT			0x00000400
////////////////////////////
#define LGC_I_AND			0x00000800
#define LGC_I_OR_1			0x00001000
#define LGC_I_OR_2			0x00002000
#define LGC_I_MODUS			0x00004000
#define LGC_I_NOT			0x00008000
#define LGC_I_ALL			0x00010000
#define LGC_I_EXISTS		0x00020000
////////////////////////////
#define LGC_DEMOR_OR		0x00040000
#define LGC_DEMOR_AND		0x00080000
#define LGC_PRC_DEMOR		0x000C0000
#define LGC_MORGAN_OR		0x00100000
#define LGC_MORGAN_AND		0x00200000
#define LGC_PRC_MORGAN		0x00300000
//////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////
#define LGC_PRC_E_NOT		0x00000001
#define LGC_PRC_E_AND		0x00000002
#define LGC_PRC_E_OR1		0x00000004
#define LGC_PRC_E_OR2		0x00000008
#define LGC_PRC_E_MAP		0x00000010

#define LGC_PRC_I_OR1		0x00000020
#define LGC_PRC_I_OR2		0x00000040
#define LGC_PRC_I_OR3		0x00000080
#define LGC_PRC_I_NOT		0x00000100
#define LGC_PRC_I_MAP		0x00000200
#define LGC_PRC_I_AND		0x00000400
//////////////////////////////////////////////////////////////////////////

#define LGC_PRC_C_OR1		0x01000000
#define LGC_PRC_C_OR2		0x02000000
#define LGC_PRC_C_NOT		0x04000000
#define LGC_PRC_C_MAP		0x08000000
#define LGC_PRC_CONTR		0x0F000000

//////////////////////////////////////////////////////////////////////////
#define LGC_SRC_DISABLE		0x00000001	
#define LGC_SRC_ASSUME		0x00000002
#define LGC_SRC_CONCLUSION  0x00000004
#define LGC_SRC_PREMISE		0x00000008
#define LGC_SRC_HOPING		0x00000010
#define LGC_SRC_DUPLICATE	0x00000020
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
	int m_proceed;
	int m_source;
	int m_line;
	
	NDTerm(int index = -1, int rule = 0, int first = -1, int second = -1)
	{
		m_index = index ;
		m_rule = rule ;
		m_first = first ;
		m_second = second ;
		m_assume = -1 ;
		m_pendings = 0 ;
		m_path = 0;
		m_proceed = 0;
		m_source = 0;
	}
	
};


class NaturalDeduction  
{
public:
	string Result();
	
	int ProveIt();
	NaturalDeduction(TermVector t);

private:
	string rule2Str (int rule);



	bool isReached(int &active);
	bool isReached(int &active, int& negative);
	bool isCompatible(int father,int son)const;
	bool isComplement(int active, int negative) const;
	int disable(int assume);
	int insertCondition(NDTerm term,int&index);
	int insertGoal(NDTerm term);
	int contradiction();
	int introduction();
	int eliminate();
	int getNDTerm(int index);
	int getString(int index);


	int turnIt();
	list <NDTerm> conditions;
	list <NDTerm> goals;
	list <int> proveds; 
	list <int> branches;
	TermVector database;
	list<NDTerm>::iterator cond;


	int lastLine;
	int ifs;
	vector<pLine> lstpLines;

};

#endif // !defined(AFX_NATURALDEDUCTION_H__492CA570_429A_43E2_B2B6_E40C8EFCCA2C__INCLUDED_)
