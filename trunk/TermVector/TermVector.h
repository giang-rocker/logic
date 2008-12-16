// TermVector.h: interface for the TermVector class.
//
//////////////////////////////////////////////////////////////////////

#if !defined(AFX_TERMVECTOR_H__A8AD395A_B758_42CD_A49B_8E488503B9E0__INCLUDED_)
#define AFX_TERMVECTOR_H__A8AD395A_B758_42CD_A49B_8E488503B9E0__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000

#include <iostream>
#include <list>
#include <vector>
#include <string>
#include <algorithm>
#include "../NaturalDeduction/Utils.h"
#if _DEBUG
//#undef  _DEBUG
#include <crtdbg.h>
#endif

using namespace std;

#define LGC_VAR_UNDEFINE		0x00000000
#define LGC_VAR_ABS_UNFLAG		0x00000001
#define LGC_VAR_ABS_FLAGGED		0x00000002
#define LGC_VAR_REL_UNFLAG		0x00000004
#define LGC_VAR_REL_FLAGGED		0x00000010
#define LGC_VAR_ANY_VALUE		0x00000020
#define LGC_VAR_DUPLICATE		0x00000040

//////////////////////////////////////////////////////////////////////////
#define LGC_ERR_SUCC	1
#define LGC_ERR_PARS	2
//////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////
#define LGC_NULL		0
//////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////
#define LGC_FUN_DEF		1
#define LGC_TERM_VAR	2
#define LGC_TERM_CONST	3
#define LGC_TERM_PROP	4
#define LGC_TERM_FUNC	5
#define LGC_TERM_FALSE	6

#define LGC_REF			8

#define LGC_MARK_SEN	9
#define LGC_MARK_FUNC	10
#define LGC_MARK_ARG	11
//////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////
#define LGC_OP_MARK		-1
#define LGC_OP_LPAR		-2
#define LGC_OP_QUAN		-3

#define LGC_OP_NOT		-4
#define LGC_OP_AND		-5
#define LGC_OP_OR		-6
#define LGC_OP_MAP		-7
//////////////////////////////////////////////////////////////////////////



//////////////////////////////////////////////////////////////////////////
#define LGC_QUAN_SIZE	1
#define LGC_QUAN_ALL	2
#define LGC_QUAN_EXIST	3
//////////////////////////////////////////////////////////////////////////



//////////////////////////////////////////////////////////////////////////
#define LGC_STR_NOT		"~"
#define LGC_STR_AND		"&"
#define LGC_STR_OR		"|"
#define LGC_STR_MAP		"->"
//////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////
#define LGC_ADDR_NOT	0
#define LGC_ADDR_AND	1
#define LGC_ADDR_OR		2
#define LGC_ADDR_MAP	3
#define LGC_ADDR_FALSE	4
//////////////////////////////////////////////////////////////////////////


struct Term  
{
	int m_kind;
	int m_ref;
	int m_info;
	int m_extra;
	Term(int kind = 0, int ref = 0, int info = 0)
	{
		m_kind = kind;
		m_ref = ref;
		m_info = info;
		m_extra = 0;
	}
	string toString()
	{
		return ToString(m_kind) + ":" + ToString(m_ref) + ":"  + ToString(m_info) + ":" + ToString(m_extra) ;
	}
};

struct Names  
{

public:
	
	int GetIndex(string name)
	{
		p = names.begin();
		int index = 0;
		while (p!=names.end())
		{
			if ((*p).str ==name)
			{
				return index;
			}
			++index;
			++p;
		}
		names.push_back(name_(name));
		return names.size() - 1;
	}
	string GetString(int index)const
	{
		if(index >= 0 && index < names.size())
		return names[index].str;
		return "";
	}
	int print()
	{
		vector<name_>::const_iterator p = names.begin();
		int i = 0;
		for (;p!=names.end();++p)
		{
			cout<<i++<<".\t"<<(*p).str<<endl;
		}
		return LGC_ERR_SUCC;
	}
private:
	struct name_
	{
		string str;
		name_(string s)
		{
			str = s;
		}
	};
	vector<name_>names;
	vector<name_>::const_iterator p;

};


class xWam  
{

public:
	int RightPar();
	int LeftPar();
	int NewLogicOp(int op);
	int NewVar(string name,int kind, int flag = 0);
	int NewQuan(string var, int kind);
	int EndArg();
	int BeginArg();
	int EndFunction();
	int BeginFunction(string name);
	int EndSentence(bool isCondition = true);
	int BeginSentence();
	int DupVar(int index, int flag);
	int print();
	string GetString(int index)const;
	xWam();
	virtual ~xWam();
	operator string()const;
	vector<Term>clauses;
	vector<Term>variables;
	vector<Term>quantifiers;
	Names names;
	list<int> goals;
	list<int> conditions;
	int SubVars(int index, int flag = 0);
	Term Get1stQuan(int index);
	int GetRemainQuan(int index);
	list<int>RestValidTerm(int index)const;
	int ClauseVars(int index, list<int>&theta)const;
	int CopyClause(int index,int oldVar,int newVar);

private:
	bool isOperator(int index)const;
	list<Term>lstTerms;
	list<int>lstOpers;
	list<int>lstQuans;
	


	int quanSize;
	vector<Term>::const_iterator p;


	int times ;

};

#endif // !defined(AFX_TERMVECTOR_H__A8AD395A_B758_42CD_A49B_8E488503B9E0__INCLUDED_)


