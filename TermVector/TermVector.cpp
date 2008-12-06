
// TermVector.cpp: implementation of the TermVector class.
//
//////////////////////////////////////////////////////////////////////

#include "TermVector.h"

//////////////////////////////////////////////////////////////////////
// Construction/Destruction
//////////////////////////////////////////////////////////////////////

TermVector::TermVector()
{

	quantifiers.push_back(Term(LGC_NULL));

	functions.push_back(Term(LGC_FUN_DEF ,names.GetIndex(LGC_STR_NOT),1));
	functions.push_back(Term(LGC_FUN_DEF,names.GetIndex(LGC_STR_AND),2));
	functions.push_back(Term(LGC_FUN_DEF,names.GetIndex(LGC_STR_OR),2));
	functions.push_back(Term(LGC_FUN_DEF,names.GetIndex(LGC_STR_MAP),2));
	functions.push_back(Term(LGC_TERM_FALSE));



	
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

		switch ((*p).m_kind)
		{
		case LGC_OP_NOT:
			functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT,0));
			--p;
			functions.push_back(*p);
			p = lstTerms.erase(p);
			*p = Term(LGC_REF,functions.size() - 2,0);
			break;
		case LGC_OP_AND:
			functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_AND,0));
			--p;
			--p;
			functions.push_back(*p);
			p = lstTerms.erase(p);
			functions.push_back(*p);
			p = lstTerms.erase(p);
			*p = Term(LGC_REF,functions.size() - 3,-0);
			break;
		case LGC_OP_OR:
			functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_OR,0));
			--p;
			--p;
			functions.push_back(*p);
			p = lstTerms.erase(p);
			functions.push_back(*p);
			p = lstTerms.erase(p);
			*p = Term(LGC_REF,functions.size() - 3,0);
			break;
		case LGC_OP_MAP:
			functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_MAP,0));
			--p;
			--p;
			functions.push_back(*p);
			p = lstTerms.erase(p);
			functions.push_back(*p);
			p = lstTerms.erase(p);
			*p = Term(LGC_REF,functions.size() - 3,0);
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
	int t = lstTerms.back().m_ref;
	if (lstTerms.back().m_kind == LGC_TERM_PROP)
	{
		t = functions.size();
		functions.push_back(Term(LGC_TERM_PROP,lstTerms.back().m_ref));
	}
	if (isCondition)
	{

		conditions.push_back(t);
	}
	else
	{
		goals.push_back(t);
	}
	return LGC_ERR_SUCC;
}
int TermVector::BeginFunction(string name)
{

#ifdef PRINT_METHOD
	cout<<"Begin Function : "<<name<<endl ;
	if (name == "p")
	{
		times++;
		if (times == 2)
		{
			cout<<"Waiting";
		}
	}
#endif

	quanSize = 0;
	int index  = names.GetIndex(name);
	p = functions.begin();
	int func = 0;

	for (;p != functions.end();++p)
	{
		if ((*p).m_ref == index && (*p).m_kind == LGC_FUN_DEF)
		{
			
			break;
		}
		func++;
	}

	if(p == functions.end())
	{
		func = functions.size();
		functions.push_back(Term(LGC_FUN_DEF,index,0));
	}

	Term t(LGC_TERM_FUNC,func,0);
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
	lstTerms.push_back(Term(LGC_REF,next,0));

	lstOpers.pop_back();
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
	switch ((*p).m_kind)
	{
	case LGC_OP_NOT:
		functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT,0));
		--p;
		functions.push_back(*p);
		p = lstTerms.erase(p);
		*p = Term(LGC_REF,functions.size() - 2,0);
		break;
	case LGC_OP_AND:
		functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_AND,0));
		--p;
		--p;
		functions.push_back(*p);
		p = lstTerms.erase(p);
		functions.push_back(*p);
		p = lstTerms.erase(p);
		*p = Term(LGC_REF,functions.size() - 3,-0);
		break;
	case LGC_OP_OR:
		functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_OR,0));
		--p;
		--p;
		functions.push_back(*p);
		p = lstTerms.erase(p);
		functions.push_back(*p);
		p = lstTerms.erase(p);
		*p = Term(LGC_REF,functions.size() - 3,0);
		break;
	case LGC_OP_MAP:
		functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_MAP,0));
		--p;
		--p;
		functions.push_back(*p);
		p = lstTerms.erase(p);
		functions.push_back(*p);
		p = lstTerms.erase(p);
		*p = Term(LGC_REF,functions.size() - 3,0);
		break;
	case LGC_OP_QUAN:
		p = lstTerms.erase(p);
		--p;
		functions[(*p).m_ref].m_info = lstQuans.back();
		lstQuans.pop_back();
		break;
	}
		++p;


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
	Term t(LGC_TERM_VAR);
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
		variables.push_back(Term(LGC_TERM_VAR,index));
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
	Term t(kind);
	int next = 0;
	for (;p!=variables.end();++p)
	{
		
		if ((*p).m_ref == index)
		{
			t.m_ref = next;
			break;
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
	/*
	cout<<"\n\n---------------Conditions-----------------------\n";
	list<int>::const_iterator lst = conditions.begin();
	for (;lst!=conditions.end();++lst)
	{
		cout<<"\t"<<*lst;
	}
	cout<<"\n\n---------------Goals-----------------------\n";
	lst = goals.begin();
	for (;lst!=goals.end();++lst)
	{
		cout<<"\t"<<*lst;
	}
	*/
	cout<<"\n\n---------------Main---------------------\n";
	vector<Term>::const_iterator p = functions.begin();
	int i = 0;
	for (;p!=functions.end();++p)
	{
		
		switch ((*p).m_kind)
		{
		case LGC_FUN_DEF:
			cout<<i++<<"\tFun:\t"<<names.GetString((*p).m_ref)<<"\tArgs="<<(*p).m_info<<"\n";
			break;

		case LGC_REF:
			cout<<i++<<"\tRef:\t"<<(*p).m_ref<<"\n";
			break;

		case LGC_TERM_VAR:
			cout<<i++<<"\tVar:\t"<<names.GetString(variables[(*p).m_ref].m_ref)<<"\n";
			break;

		case LGC_TERM_PROP:
			cout<<i++<<"\tProp:\t"<<names.GetString(variables[(*p).m_ref].m_ref)<<"\n";
			break;

		case LGC_TERM_CONST:
			cout<<i++<<"\tConst:\t"<<names.GetString(variables[(*p).m_ref].m_ref)<<"\n";
			break;

		case LGC_TERM_FUNC:
			cout<<"\n"<<i++<<"\tCall :\t"<<names.GetString(functions[(*p).m_ref].m_ref)<<"\tQuan="<<(*p).m_info<<"\n";
			break;
		case LGC_TERM_FALSE:
			cout<<i++<<"\t _|_ \n";
			break;
		default:
			cout<<i++<<(*p).m_kind<<"\t"<<(*p).m_ref<<"\t"<<(*p).m_info<<"\n";
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



string TermVector::GetString(int index)const
{
	string result = "";
	switch (functions[index].m_kind)
	{
	case LGC_REF:
		result =GetString(functions[index].m_ref);
		break;

	case LGC_TERM_FALSE:
		result = "_|_";
		break;

	case LGC_FUN_DEF:
		result = names.GetString(functions[index].m_ref);
		break;

	case LGC_TERM_CONST:
		result = names.GetString(variables[functions[index].m_ref].m_ref);
		break;

	case LGC_TERM_PROP:
		result = names.GetString(variables[functions[index].m_ref].m_ref);
		break;

	case LGC_TERM_VAR:
		result = names.GetString(variables[functions[index].m_ref].m_ref);
		break;

	case LGC_TERM_FUNC:
		int quan = functions[index].m_info;
		if (quan > 0)
		{
			int size = quantifiers[quan].m_info;
			for (int i = quan; i < size; i++)
			{
				if(quantifiers[i+quan].m_kind == LGC_QUAN_ALL)
				{
					result += " all ";
				}
				else if(quantifiers[i+quan].m_kind == LGC_QUAN_EXIST)
				{
					result += " exists ";
				}
				result += names.GetString(quantifiers[i+quan].m_ref)+ " ";
			}
		}

		int func = functions[index].m_ref;
		bool pars =  false;
		switch (func)
		{
		case LGC_ADDR_NOT:
			result += "!";
			pars  = isOperator(index+1);
			if (pars)
			{
				result += "(";
			}
			result += GetString(index + 1);
			if (pars)
			{
				result += ")";
			}
			result += " ";
			break;
		case LGC_ADDR_AND:
			pars  = isOperator(index+1);
			if (pars)
			{
				result += "(";
			}
			result += GetString(index + 1);
			if (pars)
			{
				result += ")";
			}
			result += " & ";
			pars  = isOperator(index+2);
			if (pars)
			{
				result += "(";
			}
			result += GetString(index + 2);
			pars  = isOperator(index+2);
			if (pars)
			{
				result += ")";
			}
			break;
		case LGC_ADDR_OR:
			pars  = isOperator(index+1);
			if (pars)
			{
				result += "(";
			}
			result += GetString(index + 1);
			if (pars)
			{
				result += ")";
			}
			result += " | ";
			pars  = isOperator(index+2);
			if (pars)
			{
				result += "(";
			}
			result += GetString(index + 2);
			if (pars)
			{
				result += ")";
			}
			break;
		case LGC_ADDR_MAP:
			pars  = isOperator(index+1);
			if (pars)
			{
				result += "(";
			}
			result += GetString(index + 1);
			if (pars)
			{
				result += ")";
			}
			result += " -> ";
			pars  = isOperator(index+2);
			if (pars)
			{
				result += "(";
			}
			result += GetString(index + 2);
			if (pars)
			{
				result += ")";
			}
			break;
		default:
			int args = functions[index].m_info;
			result += names.GetString(functions[index].m_ref);
			result += " ( ";
			for (int i = 0; i < args ; i++)
			{
				result += GetString(index + i);
				result += " , ";
			}
			result += " ) ";
			break;
		}
		break;
	}
	return result;
}

bool TermVector::isOperator(int index)const
{
	int i = index;
	while (functions[i].m_kind ==LGC_REF)
	{
		i = functions[i].m_ref;
	}
	if (functions[i].m_kind == LGC_TERM_FUNC)
	{
		if ( functions[i].m_ref == LGC_ADDR_AND ||functions[i].m_ref == LGC_ADDR_OR ||functions[i].m_ref == LGC_ADDR_MAP)
		{
			return true;
		}
	}
	return false;
}

