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

using namespace std;

//////////////////////////////////////////////////////////////////////////
#define LGC_ERR_SUCC	1
#define LGC_ERR_PARS	2
//////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////
#define LGC_NULL		0
//////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////
#define LGC_TERM_FUNC	1
#define LGC_TERM_VAR	2
#define LGC_TERM_CONST	3
#define LGC_TERM_PROP	4



#define LGC_USE_FUNC	5
#define LGC_USE_VAR		6
#define LGC_USE_QUAN	7

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
#define LGC_STR_NOT	"~"
#define LGC_STR_AND	"&"
#define LGC_STR_OR	"|"
#define LGC_STR_MAP	"->"
//////////////////////////////////////////////////////////////////////////



struct Term  
{
	int m_kind;
	int m_ref;
	int m_info;
	Term(int kind = 0, int ref = 0, int info = 0)
	{
		m_kind = kind;
		m_ref = ref;
		m_info = info;
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
		if(index>=0 && index<names.size())
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


class TermVector  
{
public:
	int RightPar();
	int LeftPar();
	int NewLogicOp(int op);
	int NewVar(string name,int kind);
	int NewQuan(string var, int kind);
	int EndArg();
	int BeginArg();
	int EndFunction();
	int BeginFunction(string name);
	int EndSentence(bool isCondition = true);
	int BeginSentence();
	int print();
	TermVector();
	virtual ~TermVector();
	operator string()const;

	vector<Term>functions;
	vector<Term>variables;
	vector<Term>quantifiers;
	Names names;
	list<int> goals;
	list<int> conditions;

private:
	list<Term>lstTerms;
	list<int>lstOpers;
	list<int>lstQuans;
	
	int addrNOT;
	int addrAND;
	int addrOR;
	int addrMAP;

	int quanSize;
	vector<Term>::const_iterator p;
	int debug();

	int times ;

};

#endif // !defined(AFX_TERMVECTOR_H__A8AD395A_B758_42CD_A49B_8E488503B9E0__INCLUDED_)


