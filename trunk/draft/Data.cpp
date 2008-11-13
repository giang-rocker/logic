// Data.cpp: implementation of the Data class.
//
//////////////////////////////////////////////////////////////////////

#include "Data.h"

//////////////////////////////////////////////////////////////////////
// Construction/Destruction
//////////////////////////////////////////////////////////////////////

Data::Data()
{
	//Mark start start bank
	//bank.push_back(MARK_TERM);
	
}


Data::~Data()
{

}



void Data::BeginTerm()
{
	while(!operators.empty())
	{
		operators.pop();
	}
	
	while(!lstIndexes.empty())
	{
		lstIndexes.pop_back();
	}
	
	operators.push(LGC_MARK_OP);
	lstIndexes.push_back(LGC_MARK_TERM);
}


void Data::EndTerm(bool isCondition)
{
	while(operators.top()!=LGC_MARK_OP)
	{
		lstIndexes.push_back(operators.top());
		operators.pop();
	}
	operators.pop();
	

	list<int>::iterator p = lstIndexes.end();
	for(;*p!=LGC_MARK_TERM;--p)
	{
		//NOP
	}
	p = lstIndexes.erase(p);


	Term op(LGC_PRE_TERM);
	Term arg(LGC_REF_TERM);
	
	while(p!=lstIndexes.end())
	{
		
		switch(*p)
		{

		case LGC_NOT_OP:
			op.m_name = LGC_NOT_FUNC;
			op.m_iArgs = 1;
			bank.push_back(op);
			--p;
			arg.m_iRef = *p;
			bank.push_back(arg);
			p = lstIndexes.erase(p);
			*p = bank.size()-2;
			break;

		case LGC_AND_OP:
			op.m_name = LGC_AND_FUNC;
			op.m_iArgs = 2;
			bank.push_back(op);
			--p;
			--p;
			arg.m_iRef = *p;
			bank.push_back(arg);
			p = lstIndexes.erase(p);
			arg.m_iRef = *p;
			bank.push_back(arg);
			p = lstIndexes.erase(p);
			*p = bank.size()-3;
			break;

		case LGC_OR_OP:
			op.m_name = LGC_OR_FUNC;
			op.m_iArgs = 2;
			bank.push_back(op);
			--p;
			--p;
			arg.m_iRef = *p;
			bank.push_back(arg);
			p = lstIndexes.erase(p);
			arg.m_iRef = *p;
			bank.push_back(arg);
			p = lstIndexes.erase(p);
			*p = bank.size()-3;
			break;


		case LGC_MAP_OP:
			op.m_name = LGC_MAP_FUNC;
			op.m_iArgs = 2;
			bank.push_back(op);
			--p;
			--p;
			arg.m_iRef = *p;
			bank.push_back(arg);
			p = lstIndexes.erase(p);
			arg.m_iRef = *p;
			bank.push_back(arg);
			p = lstIndexes.erase(p);
			*p = bank.size()-3;
			break;

		}
		++p;
	}
	if(isCondition)
	{
		lstConditions.push_back(*(lstIndexes.begin()));
	}
	else
	{
		lstGoals.push_back(*(lstIndexes.begin()));
	}
}



void Data::BeginPredicate(string name)
{
	lstTerms.push(Term(LGC_PRE_TERM,name));
	lstIndexes.push_back(LGC_MARK_PRE);
}

int Data::EndPredicate()
{

	Term predicate = lstTerms.top();
	lstTerms.pop();
	predicate.m_iArgs = 0;
	list<int>::iterator p = lstIndexes.end();
	--p;
	while(*p!=LGC_MARK_PRE)
	{
		--p;
		predicate.m_iArgs++;
	}
	bank.push_back(predicate);
	*p = bank.size()-1;
	++p;
	Term t(LGC_REF_TERM);
	while(p!=lstIndexes.end())
	{
		t.m_iRef = *p;
		bank.push_back(t);
		p = lstIndexes.erase(p);
	}
	return 0;

}



int Data::NewConstVar(string name,int kind)
{
	vector<Term>::const_iterator p = bank.begin();
	int index  = 0;
	for(;p!=bank.end();++p)
	{
		index++;
		if((*p).m_name == name && (*p).m_kind == kind)
		{
			break;
		}
	}
	if(index == bank.size())
	{
		index = bank.size();
		Term t(kind,name);
		bank.push_back(t);
	}
	lstIndexes.push_back(index);
	return index;
}


void Data::NewQuantifiers()
{
	LogicOp(LGC_QUAN_OP);
	Term t(LGC_QUAN_TERM);
	t.m_iArgs = 0;
	quantifiers.push(bank.size());
	bank.push_back(t);
	
}


void Data::QuanOp(string varName, int quanKind)
{
	
	Term t(LGC_QUAN_TERM);
	t.m_iQuan = quanKind;
	
	vector<Term>::const_iterator p = bank.begin();
	int index  = 0;
	for(;p!=bank.end();++p)
	{
		index++;
		if((*p).m_name == varName && (*p).m_kind == LGC_VAR_TERM)
		{
			break;
		}
	}
	if(index == bank.size())
	{
		index = bank.size();
		Term var(LGC_VAR_TERM,varName);
		bank.push_back(var);
	}

	bank.push_back(t);
	bank[quantifiers.top()].m_iArgs++;

}



void Data::LogicOp(int op)
{

	while(operators.top() > op && operators.top()!=LGC_MARK_OP)
	{
		lstIndexes.push_back(operators.top());
		operators.pop();
	}
	operators.push(op);

}


void Data::LeftPar()
{
	operators.push(LGC_LEFT_PAR);
}

void Data::RightPar()
{
	while(operators.top()!=LGC_LEFT_PAR )
	{
		lstIndexes.push_back(operators.top());
		operators.pop();
	}
}



void Data::BeginArg()
{
	lstIndexes.push_back(LGC_MARK_ARG);
	operators.push(LGC_MARK_OP);
}

void Data::EndArg()
{
	

	while(operators.top()!=LGC_MARK_OP)
	{
		lstIndexes.push_back(operators.top());
		operators.pop();
	}
	operators.pop();
	

	list<int>::iterator p = lstIndexes.end();
	for(;*p!=LGC_MARK_ARG;--p)
	{
		//NOP
	}
	p = lstIndexes.erase(p);


	Term op(LGC_PRE_TERM);
	Term arg(LGC_REF_TERM);
	
	while(p!=lstIndexes.end())
	{
		
		switch(*p)
		{

		case LGC_NOT_OP:
			op.m_name = LGC_NOT_FUNC;
			op.m_iArgs = 1;
			bank.push_back(op);
			--p;
			arg.m_iRef = *p;
			bank.push_back(arg);
			p = lstIndexes.erase(p);
			*p = bank.size()-2;
			break;

		case LGC_AND_OP:
			op.m_name = LGC_AND_FUNC;
			op.m_iArgs = 2;
			bank.push_back(op);
			--p;
			--p;
			arg.m_iRef = *p;
			bank.push_back(arg);
			p = lstIndexes.erase(p);
			arg.m_iRef = *p;
			bank.push_back(arg);
			p = lstIndexes.erase(p);
			*p = bank.size()-3;
			break;

		case LGC_OR_OP:
			op.m_name = LGC_OR_FUNC;
			op.m_iArgs = 2;
			bank.push_back(op);
			--p;
			--p;
			arg.m_iRef = *p;
			bank.push_back(arg);
			p = lstIndexes.erase(p);
			arg.m_iRef = *p;
			bank.push_back(arg);
			p = lstIndexes.erase(p);
			*p = bank.size()-3;
			break;


		case LGC_MAP_OP:
			op.m_name = LGC_MAP_FUNC;
			op.m_iArgs = 2;
			bank.push_back(op);
			--p;
			--p;
			arg.m_iRef = *p;
			bank.push_back(arg);
			p = lstIndexes.erase(p);
			arg.m_iRef = *p;
			bank.push_back(arg);
			p = lstIndexes.erase(p);
			*p = bank.size()-3;
			break;

		case LGC_QUAN_OP:
			break;
		}
		++p;
	}
	
	
}

void Data::print()
{
	vector<Term>::iterator p = bank.begin();
	for(;p!=bank.end();++p)
	{
		Term t = *p;
		cout<<"Kind = "<< t.m_kind<<"\t";
		switch (t.m_kind)
		{
		case LGC_REF_TERM:
			cout<<"Ref = " << t.m_iRef << "\t";
			break;
		case LGC_PRE_TERM:
			cout<<"Args = " << t.m_iArgs << "\t" << "Name = "<< t.m_name<<"\t";
			break;
		default:
			cout<<"Name = " << t.m_name;
		}
		cout<<endl;
	}
	
}
