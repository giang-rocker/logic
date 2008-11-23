
// TermVector.cpp: implementation of the TermVector class.
//
//////////////////////////////////////////////////////////////////////

#include "TermVector.h"
//#define DEBUG
//////////////////////////////////////////////////////////////////////
// Construction/Destruction
//////////////////////////////////////////////////////////////////////

TermVector::TermVector()
{

	quantifiers.push_back(Term(LGC_NULL));
	functions.push_back(Term(LGC_NULL));

	addrNOT = functions.size();
	functions.push_back(Term(LGC_OP_NOT,names.GetIndex(LGC_STR_NOT),1));

	addrAND = functions.size();
	functions.push_back(Term(LGC_OP_AND,names.GetIndex(LGC_STR_AND),2));

	addrOR = functions.size();
	functions.push_back(Term(LGC_OP_OR,names.GetIndex(LGC_STR_OR),2));

	addrMAP = functions.size();
	functions.push_back(Term(LGC_OP_MAP,names.GetIndex(LGC_STR_MAP),2));

	
	
}
TermVector::~TermVector()
{

}

int TermVector::BeginSentence()
{
	lstTerms.clear();
	lstOpers.clear();
	quanSize = 0;
	lstTerms.push_back(LGC_MARK_SEN);
	lstOpers.push_back(LGC_OP_MARK);
	return LGC_ERR_SUCC;
}

int TermVector::EndSentence(bool isCondition)
{
	quanSize = 0;

	while ((!lstOpers.empty()) &&lstOpers.back()!=LGC_OP_MARK )
	{
		lstTerms.push_back(Term(lstOpers.back()));
		lstOpers.pop_back();
	}
	lstOpers.pop_back();

	list<Term>::iterator p = lstTerms.begin();
	p = lstTerms.erase(p);
 
	while (p!=lstTerms.end())
	{
#ifdef DEBUG
		debug();
#endif
		switch ((*p).m_kind)
		{
		case LGC_OP_NOT:
			functions.push_back(Term(LGC_REF_FUNC,addrNOT,0));
			--p;
			functions.push_back(*p);
			p = lstTerms.erase(p);
			*p = Term(LGC_REF_FUNC,functions.size() - 2,0);
			break;
		case LGC_OP_AND:
			functions.push_back(Term(LGC_REF_FUNC,addrAND,0));
			--p;
			--p;
			functions.push_back(*p);
			p = lstTerms.erase(p);
			functions.push_back(*p);
			p = lstTerms.erase(p);
			*p = Term(LGC_REF_FUNC,functions.size() - 3,-0);
			break;
		case LGC_OP_OR:
			functions.push_back(Term(LGC_REF_FUNC,addrOR,0));
			--p;
			--p;
			functions.push_back(*p);
			p = lstTerms.erase(p);
			functions.push_back(*p);
			p = lstTerms.erase(p);
			*p = Term(LGC_REF_FUNC,functions.size() - 3,0);
			break;
		case LGC_OP_MAP:
			functions.push_back(Term(LGC_REF_FUNC,addrMAP,0));
			--p;
			--p;
			functions.push_back(*p);
			p = lstTerms.erase(p);
			functions.push_back(*p);
			p = lstTerms.erase(p);
			*p = Term(LGC_REF_FUNC,functions.size() - 3,0);
			break;
		case LGC_OP_QUAN:
			p = lstTerms.erase(p);
			--p;
			functions[(*p).m_ref].m_info = lstQuans.back();
			lstQuans.pop_back();
			break;
		}
		++p;
	}
	Term t = lstTerms.back();
	//int index;
	//if (t.m_kind == LGC_REF_FUNC && functions[t.m_ref].m_kind == LGC_REF_FUNC)
	//{
		//functions.pop_back();
		//index = t.m_ref;
	//}
	//else
	//{
	//	index = functions.size() - 1;
	//}
	if (isCondition)
	{

		goals.push_back(t.m_ref);
	}
	return LGC_ERR_SUCC;
}
int TermVector::BeginFunction(string name)
{
	quanSize = 0;
	int index  = names.GetIndex(name);
	p = functions.begin();
	int func = 0;
	
	for (;p != functions.end();++p)
	{
		if ((*p).m_ref == index && (*p).m_kind == LGC_TERM_FUNC)
		{
			func++;
		}
	}

	if(p == functions.end())
	{
		func = functions.size();
		functions.push_back(Term(LGC_TERM_FUNC,index,0));
	}

	Term t(LGC_REF_FUNC,func,0);
	if (lstOpers.back()==LGC_OP_QUAN)
	{
		t.m_info = lstQuans.back();
		lstQuans.pop_back();
		lstOpers.pop_back();
	}

	lstTerms.push_back(Term(LGC_MARK_FUNC));
	lstTerms.push_back(t);
	lstOpers.push_back(LGC_OP_MARK);

	return LGC_ERR_SUCC;
}

int TermVector::EndFunction()
{

	quanSize = 0;
	list<Term>::iterator p = lstTerms.end();
	int args = 0;
	--p;
	while ((*p).m_kind != LGC_MARK_FUNC)
	{
		--p;
		++args;
	}
	--args;
	p = lstTerms.erase(p);
	functions[(*p).m_ref].m_info = args;
	int next = functions.size();
	while (p!=lstTerms.end())
	{
		functions.push_back(*p);
		p = lstTerms.erase(p);
	} 
	--p;
	lstTerms.push_back(Term(LGC_REF_FUNC,next,0));

	lstOpers.pop_back();
	/*
	if ((*p).m_kind == LGC_MARK_SEN)
	{
		lstTerms.push_back(functions[next]);
	}
	else
	{
		lstTerms.push_back(Term(LGC_REF_FUNC,next,0));
	}
	*/


	return LGC_ERR_SUCC;
}
int TermVector::BeginArg()
{
	quanSize = 0;
	lstTerms.push_back(Term(LGC_MARK_ARG));
	lstOpers.push_back(LGC_OP_MARK);
	return LGC_ERR_SUCC;
}

int TermVector::EndArg()
{


	
	quanSize = 0;
	while ((!lstOpers.empty()) && lstOpers.back()!=LGC_OP_MARK)
	{
		lstTerms.push_back(Term(lstOpers.back()));
		lstOpers.pop_back();
	}
	lstOpers.pop_back();
	

	list<Term>::iterator p = lstTerms.end();
	while ((*p).m_kind != LGC_MARK_ARG)
	{
		--p;
	}
	p = lstTerms.erase(p);
	while (p!=lstTerms.end())
	{
		switch ((*p).m_kind)
		{
		case LGC_OP_NOT:
			functions.push_back(Term(LGC_REF_FUNC,addrNOT,0));
			--p;
			functions.push_back(*p);
			p = lstTerms.erase(p);
			*p = Term(LGC_REF_FUNC,functions.size(),0);
			break;
		case LGC_OP_AND:
			functions.push_back(Term(LGC_REF_FUNC,addrAND,0));
			--p;
			functions.push_back(*p);
			p = lstTerms.erase(p);
			functions.push_back(*p);
			p = lstTerms.erase(p);
			*p = Term(LGC_REF_FUNC,functions.size() - 1,0);
			break;
		case LGC_OP_OR:
			functions.push_back(Term(LGC_REF_FUNC,addrOR,0));
			--p;
			functions.push_back(*p);
			p = lstTerms.erase(p);
			functions.push_back(*p);
			p = lstTerms.erase(p);
			*p = Term(LGC_REF_FUNC,functions.size() - 1,0);
			break;
		case LGC_OP_MAP:
			functions.push_back(Term(LGC_REF_FUNC,addrMAP,0));
			--p;
			functions.push_back(*p);
			p = lstTerms.erase(p);
			functions.push_back(*p);
			p = lstTerms.erase(p);
			*p = Term(LGC_REF_FUNC,functions.size() - 1,0);
			break;
		case LGC_OP_QUAN:
			p = lstTerms.erase(p);
			(*p).m_kind = lstQuans.back();
			lstQuans.pop_back();
			break;
		}
		++p;
	}

	return LGC_ERR_SUCC;
}

int TermVector::NewQuan(string var, int kind)
{
	if (quanSize == 0)
	{
		quanSize++;
		quantifiers.push_back(Term(LGC_QUAN_SIZE,0,0));
		lstQuans.push_back(quantifiers.size()-1);
		lstOpers.push_back(LGC_OP_QUAN);
	}
	int index = names.GetIndex(var);
	vector<Term>::iterator p = variables.begin();
	Term t(LGC_REF_VAR);
	int next = 0;
	for (;p!=variables.end();++p)
	{
		
		if ((*p).m_ref == index)
		{
			t.m_ref = next;
		}
		++next;
	}
	if (p == variables.end())
	{
		variables.push_back(Term(kind,index));
		t.m_ref = variables.size() - 1;
	}
	quantifiers[lstQuans.back()].m_info++;
	quantifiers.push_back(Term(kind,next));
	return LGC_ERR_SUCC;
}
int TermVector::NewVar(string name,int kind)
{
	quanSize = 0;
	int index = names.GetIndex(name);
	vector<Term>::iterator p = variables.begin();
	Term t(LGC_REF_VAR);
	int next = 0;
	for (;p!=variables.end();++p)
	{
		
		if ((*p).m_ref == index)
		{
			t.m_ref = next;
		}
		++next;
	}
	if (p == variables.end())
	{
		variables.push_back(Term(kind,index));
		t.m_ref = variables.size() - 1;
	}
	lstTerms.push_back(t);
	return LGC_ERR_SUCC;
}
int TermVector::NewConst(string name)
{
	return LGC_ERR_SUCC;
}

int TermVector::NewProposition(string name)
{
	return LGC_ERR_SUCC;
}

int TermVector::NewLogicOp(int op)
{
	
	quanSize = 0;
	while ((!lstOpers.empty()) && lstOpers.back() > op && lstOpers.back() <= LGC_OP_NOT )
	{
		lstTerms.push_back(Term(lstOpers.back()));
		lstOpers.pop_back();
	}
	lstOpers.push_back(op);



	return LGC_ERR_SUCC;
}

int TermVector::LeftPar()
{
	
	quanSize = 0;
	lstOpers.push_back(LGC_OP_LPAR);
	
	return LGC_ERR_SUCC;
}

int TermVector::RightPar()
{

	while ((!lstOpers.empty()) && lstOpers.back()!=LGC_OP_LPAR)
	{
		lstTerms.push_back(Term(lstOpers.back()));
		lstOpers.pop_back();
	}
	lstOpers.pop_back();


	
	return LGC_ERR_SUCC;
}
TermVector::operator string()const
{
	
	return "";
}
int TermVector::print()
{
	cout<<"---------------Goals-----------------------\n";
	list<int>::const_iterator lst = goals.begin();
	for (;lst!=goals.end();++lst)
	{
		cout<<"\t"<<*lst;
	}
	cout<<"\n\n---------------Main---------------------\n";
	vector<Term>::const_iterator p = functions.begin();
	int i = 0;
	for (;p!=functions.end();++p)
	{
		cout<<i++<<".\t";
		switch ((*p).m_kind)
		{
		case LGC_TERM_FUNC:
			cout<<"FunDef\t"<<names.GetString((*p).m_ref)<<"\tArgs="<<(*p).m_info<<"\n";
			break;
		case LGC_REF_FUNC:
			cout<<"FunRef\t"<<(*p).m_ref<<"\tQuan="<<(*p).m_info<<"\n";
			break;
		case LGC_REF_VAR:
			cout<<"VarRef\t"<<names.GetString(variables[(*p).m_ref].m_ref)<<"\n";
			break;
		default:
			cout<<(*p).m_kind<<"\t"<<(*p).m_ref<<"\t"<<(*p).m_info<<"\n";
		}
		
	}
	cout<<"------------------Variable------------------------\n";
	p = variables.begin();
	i = 0;
	for (;p!=variables.end();++p)
	{
		cout<<i++<<".\t"<<(*p).m_kind<<"\t"<<(*p).m_ref<<"\t"<<(*p).m_info<<"\n";
	}
	cout<<"----------------------Quantifier---------------------\n";
	p = quantifiers.begin();
	i = 0;
	for (;p!=quantifiers.end();++p)
	{
		cout<<i++<<".\t"<<(*p).m_kind<<"\t"<<(*p).m_ref<<"\t"<<(*p).m_info<<"\n";
	}
	cout<<"-----------------------names-------------------------\n";
	names.print();
	return LGC_ERR_SUCC;
}

int TermVector::debug()
{
	list<Term>::iterator p = lstTerms.begin();
	for (;p!=lstTerms.end();++p)
	{
		cout<<(*p).m_kind<<"\t"<<(*p).m_ref<<"\t"<<(*p).m_info<<endl;
	}
	cout<<endl<<endl;
	return LGC_ERR_SUCC;
}