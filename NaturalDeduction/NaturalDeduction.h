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


///////////////////////////////////////


#define LGC_OFFSET_VAR			40000		
#define LGC_OFFSET_PRO			50000
#define LGC_OFFSET_CONST		55000
#define LGC_OFFSET_QUANT		60000

//////////////////////////////////////
#define LGC_RULE_PREMISE	0x00000001
#define LGC_RULE_ID			0x00000002
#define LGC_RULE_LEM		0x00000004
//////////////////////////////////////
#define LGC_E_AND_1			0x00000008
#define LGC_E_AND_2			0x00000010
#define LGC_E_OR			0x00000020
#define LGC_E_MAP			0x00000040
#define LGC_E_DNEG			0x00000080
#define LGC_E_ALL			0x00000100
#define LGC_E_EXISTS		0x00000200
#define LGC_E_NOT			0x00000400
//////////////////////////////////////
#define LGC_I_AND			0x00000800
#define LGC_I_OR_1			0x00001000
#define LGC_I_OR_2			0x00002000 
#define LGC_I_MAP			0x00004000
#define LGC_I_NOT			0x00008000
#define LGC_I_ALL			0x00010000
#define LGC_I_EXISTS		0x00020000
#define LGC_I_INTRO			0x0003F000

//////////////////////////////////////
#define LGC_DEMOR_OR		0x00040000
#define LGC_DEMOR_AND		0x00080000
#define LGC_PRC_DEMOR		0x000C0000
#define LGC_MORGAN_OR		0x00100000
#define LGC_MORGAN_AND		0x00200000
#define LGC_PRC_MORGAN		0x00300000
//////////////////////////////////////


//////////////////////////////////////
#define LGC_PRC_E_NOT		0x00000001
#define LGC_PRC_E_AND		0x00000002
#define LGC_PRC_E_OR1		0x00000004
#define LGC_PRC_E_OR2		0x00000008
#define LGC_PRC_E_MAP		0x00000010
#define LGC_PRC_E_EXI		0x00000020
#define LGC_PRC_E_ALL		0x00000040
//////////////////////////////////////
#define LGC_PRC_I_OR1		0x00000080
#define LGC_PRC_I_OR2		0x00000100
#define LGC_PRC_I_OR3		0x00000200
#define LGC_PRC_I_OR4		0x00000400

#define LGC_PRC_I_NOT		0x00000800
#define LGC_PRC_I_MAP		0x00001000
#define LGC_PRC_I_AND		0x00002000
#define LGC_PRC_I_ALL		0x00004000
#define LGC_PRC_I_EXI		0x00008000
//////////////////////////////////////
#define LGC_PRC_C_OR1		0x01000000
#define LGC_PRC_C_OR2		0x02000000
#define LGC_PRC_C_NOT		0x04000000
#define LGC_PRC_C_MAP		0x08000000
#define LGC_PRC_CONTR		0x0F000000

//////////////////////////////////////
#define LGC_SRC_DISABLE		0x00000001	
#define LGC_SRC_ASSUME		0x00000002
#define LGC_SRC_CONCLUSION	0x00000004
#define LGC_SRC_PREMISE		0x00000008
#define LGC_SRC_HOPING		0x00000010
#define LGC_SRC_DUPLICATE	0x00000020
#define LGC_SRC_LEM			0x00000040
//////////////////////////////////////
#define LGC_SRC_OR_GOAL		0x10000000
#define LGC_SRC_OR_SUB_1	0x20000000
#define LGC_SRC_OR_SUB_2	0x40000000
#define LGC_SRC_OR_CONC		0x80000000
#define LGC_SRC_OR_PART1	0x01000000
#define LGC_SRC_OR_PART2	0x02000000
//////////////////////////////////////
#define LGC_SRC_ALL_GOAL	0x04000000

#define LGC_SRC_EE_GOAL		0x00100000
#define LGC_SRC_EE_CONC		0x00200000
#define LGC_SRC_EE_ASSU		0x00400000

#define LGC_SRC_EI_GOAL		0x00800000
#define LGC_SRC_EI_CONC		0x00010000
//////////////////////////////////////



class NDWAM 
{
	
public:
	NDWAM(int index, Term t)
	{
		m_term =  t;
		m_index = index;
	}
	NDWAM()
	{
		m_term = Term(LGC_NULL);
	}
	inline bool operator == (NDWAM wam)const
	{
		if (m_index == wam.m_index && m_term.m_kind == wam.m_term.m_kind)
		{
			return true;
		}
		else if (m_term.m_kind == wam.m_term.m_kind && m_term.m_kind != LGC_TERM_FUNC && m_term.m_ref == wam.m_term.m_ref)
		{
			return true;
		}
		return false;
	}
	inline int Index()const
	{
		return m_index;
	}
	inline int Info()const
	{
		return m_term.m_info;
	}
	inline int Ref()const
	{
		return m_term.m_ref;
	}
	inline int Kind()const
	{
		return m_term.m_kind;
	}
	inline bool IsNull()const
	{
		return m_term.m_kind == LGC_NULL;
	}
	Term m_term;
	int	 m_index;

};

struct NDTerm
{

	int m_index;	
	int m_first;		
	int m_second;
	int m_third;
	int m_rule;	
	int m_path;
	int m_assume;
	int m_pendings;
	int m_proceed;
	int m_source;
	int m_line;
	int m_derivation;
	bool m_isPremise;
	bool m_OrEnable;
	bool m_isOrStart;
	int m_OrAssume;
	int m_NewVar;
	int m_OldVarIndex;
	int m_cutExists;
	int m_nexts;

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
		m_derivation = -1;
		m_isPremise = false;
		m_OrEnable = true;
		m_third = -1;
		m_isOrStart = false;
		m_line = -1;
		m_NewVar = -1;
		m_OldVarIndex = -1;
		m_cutExists = -1;
		m_OrAssume = -1;
		m_nexts = 0;
	
	}
	list<int>substed;
	NDWAM substion;
	
};

struct NDBackup 
{
	NDBackup(	list <NDTerm> conditions,
			list <NDTerm> goals,
			list <int> proveds, 
			list<int>exists, xWam knowledgeBase)
	{
		m_conditions = conditions;
		m_goals = goals;
		m_proveds = proveds;
		m_Exists = exists;
		m_knowledgeBase = knowledgeBase;
	}
	list <NDTerm>m_conditions;
	list <NDTerm>m_goals;
	list <int>m_proveds; 
	list<int>m_Exists;
	xWam m_knowledgeBase;

};


class NaturalDeduction  
{
public:
	string Result();
	
	int ProveIt();
	NaturalDeduction(xWam t);
	int insertLEMs();

private:

	NDWAM ndWam(int index);
	int unify(NDWAM x, NDWAM y, list<NDWAM>& theta);
	int unify(list<NDWAM> x, list<NDWAM> y, list<NDWAM>& theta);
	int unifyVar(NDWAM var, NDWAM y, list<NDWAM>& theta);
	bool occurCheck(list<NDWAM>theta,NDWAM var, NDWAM node )const;
	

	int  getFarest(int& first, int& second, int sub1, int sub2);
	int  NegContradiction();
	int  NegIntrodution();
	int  OrEliminate();
	string rule2Str (int rule);
	inline void backup();
	inline int setCutExists(int goal,int assume);
	inline int existsEliminate();
	inline int disableVar (int varRef);
	inline bool isReached(int &active);
	inline bool isReached(int &active, int& negative);
	inline bool isCompatible(int father,int son);
	inline bool isComplement(int active, int negative);
	inline int  disable(int assume);
	inline int  contradiction();
	inline int  introduction();
	inline int  eliminate();
	inline int  getNDTerm(int index);
	
	int  getString(int index, bool isFixed = false, bool prefix = false);
	int  insertCondition(NDTerm term,int&index);
	int  insertGoal(NDTerm term);

	int turnIt();
	list <NDTerm> conditions;
	list <NDTerm> goals;
	list <int> proveds; 
	//list <int> branches;
	xWam knowledgeBase;
	list<NDTerm>::iterator cond;
	
	int isDerived(int child, int parent);
	int lastLine;
	int ifs;
	vector<pLine> lstpLines;
	list<int>ndAssumes;
	list<int>lstExists;
	bool isInsert;
	bool isRenaming;

	list<NDBackup>lst_backup;

#if _DEBUG
	void dprintLines();
	int debug(int n);
	void printAssumption();
#endif


};

#endif // !defined(AFX_NATURALDEDUCTION_H__492CA570_429A_43E2_B2B6_E40C8EFCCA2C__INCLUDED_)
