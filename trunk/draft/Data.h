// Data.h: interface for the Data class.
//
//////////////////////////////////////////////////////////////////////

#if !defined(AFX_DATA_H__3354AEDB_6511_4571_A3BB_64C8256B3605__INCLUDED_)
#define AFX_DATA_H__3354AEDB_6511_4571_A3BB_64C8256B3605__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000
#include "Term.h"
#include <vector>
#include <list>
#include <stack>
#include <iostream>
using namespace std;


const Term MARK_TERM(LGC_MARK_TERM,"------");

class Data  
{

public:
	void EndArg();
	void BeginArg();
	void RightPar();
	void LeftPar();
	void AllOp(string name);
	void ExistsOp(string name);
	void Operator(int op);
	void NewConstVar(string name, int kind);
	int EndPredicate();
	void BeginPredicate (string name);
	void EndTerm(bool isCondition = true);
	void BeginTerm();
	Data();
	virtual ~Data();

	vector<Term>bank;

	list<int>lstConditions;
	list<int>lstGoals;
	

	stack<int>operators;
	
	stack<Term>lstTerms;
	list<int>lstIndexes;

	void print();
};

#endif // !defined(AFX_DATA_H__3354AEDB_6511_4571_A3BB_64C8256B3605__INCLUDED_)
