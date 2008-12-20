
// TermVector.cpp: implementation of the TermVector class.
//
//////////////////////////////////////////////////////////////////////

#include "TermVector.h"

//////////////////////////////////////////////////////////////////////
// Construction/Destruction
//////////////////////////////////////////////////////////////////////

xWam::xWam()
{

	quantifiers.push_back(Term(LGC_NULL));

	clauses.push_back(Term(LGC_FUN_DEF ,names.GetIndex(LGC_STR_NOT),1));
	clauses.push_back(Term(LGC_FUN_DEF,names.GetIndex(LGC_STR_AND),2));
	clauses.push_back(Term(LGC_FUN_DEF,names.GetIndex(LGC_STR_OR),2));
	clauses.push_back(Term(LGC_FUN_DEF,names.GetIndex(LGC_STR_MAP),2));
	clauses.push_back(Term(LGC_TERM_FALSE));



	
}
xWam::~xWam()
{

}

int xWam::BeginSentence()
{


	lstTerms.clear();
	lstOpers.clear();
	quanSize = 0;
	lstTerms.push_back(LGC_MARK_SEN);
	lstOpers.push_back(LGC_OP_MARK);
	return LGC_ERR_SUCC;
}

int xWam::EndSentence(bool isCondition)
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
			clauses.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT,0));
			--p;
			clauses.push_back(*p);
			p = lstTerms.erase(p);
			*p = Term(LGC_REF,clauses.size() - 2,0);
			break;
		case LGC_OP_AND:
			clauses.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_AND,0));
			--p;
			--p;
			clauses.push_back(*p);
			p = lstTerms.erase(p);
			clauses.push_back(*p);
			p = lstTerms.erase(p);
			*p = Term(LGC_REF,clauses.size() - 3,-0);
			break;
		case LGC_OP_OR:
			clauses.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_OR,0));
			--p;
			--p;
			clauses.push_back(*p);
			p = lstTerms.erase(p);
			clauses.push_back(*p);
			p = lstTerms.erase(p);
			*p = Term(LGC_REF,clauses.size() - 3,0);
			break;
		case LGC_OP_MAP:
			clauses.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_MAP,0));
			--p;
			--p;
			clauses.push_back(*p);
			p = lstTerms.erase(p);
			clauses.push_back(*p);
			p = lstTerms.erase(p);
			*p = Term(LGC_REF,clauses.size() - 3,0);
			break;
		case LGC_OP_QUAN:
			p = lstTerms.erase(p);
			--p;
			clauses[(*p).m_ref].m_info = lstQuans.back();
			lstQuans.pop_back();
			break;
		}
		++p;
	}
	int t = lstTerms.back().m_ref;
	if (lstTerms.back().m_kind == LGC_TERM_PROP)
	{
		t = clauses.size();
		clauses.push_back(Term(LGC_TERM_PROP,lstTerms.back().m_ref));
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
int xWam::BeginFunction(string name)
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
	p = clauses.begin();
	int func = 0;

	for (;p != clauses.end();++p)
	{
		if ((*p).m_ref == index && (*p).m_kind == LGC_FUN_DEF)
		{
			
			break;
		}
		func++;
	}

	if(p == clauses.end())
	{
		func = clauses.size();
		clauses.push_back(Term(LGC_FUN_DEF,index,0));
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

int xWam::EndFunction()
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
	clauses[(*p).m_ref].m_info = args;
	int next = clauses.size();
	while (p!=lstTerms.end())
	{
		clauses.push_back(*p);
		p = lstTerms.erase(p);
	} 
	--p;
	lstTerms.push_back(Term(LGC_REF,next,0));

	lstOpers.pop_back();
	return LGC_ERR_SUCC;
}
int xWam::BeginArg()
{

	quanSize = 0;
	lstTerms.push_back(Term(LGC_MARK_ARG));
	lstOpers.push_back(LGC_OP_MARK);
	return LGC_ERR_SUCC;
}

int xWam::EndArg()
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
		clauses.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT,0));
		--p;
		clauses.push_back(*p);
		p = lstTerms.erase(p);
		*p = Term(LGC_REF,clauses.size() - 2,0);
		break;
	case LGC_OP_AND:
		clauses.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_AND,0));
		--p;
		--p;
		clauses.push_back(*p);
		p = lstTerms.erase(p);
		clauses.push_back(*p);
		p = lstTerms.erase(p);
		*p = Term(LGC_REF,clauses.size() - 3,-0);
		break;
	case LGC_OP_OR:
		clauses.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_OR,0));
		--p;
		--p;
		clauses.push_back(*p);
		p = lstTerms.erase(p);
		clauses.push_back(*p);
		p = lstTerms.erase(p);
		*p = Term(LGC_REF,clauses.size() - 3,0);
		break;
	case LGC_OP_MAP:
		clauses.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_MAP,0));
		--p;
		--p;
		clauses.push_back(*p);
		p = lstTerms.erase(p);
		clauses.push_back(*p);
		p = lstTerms.erase(p);
		*p = Term(LGC_REF,clauses.size() - 3,0);
		break;
	case LGC_OP_QUAN:
		p = lstTerms.erase(p);
		--p;
		clauses[(*p).m_ref].m_info = lstQuans.back();
		lstQuans.pop_back();
		break;
	}
		++p;


	return LGC_ERR_SUCC;
}

int xWam::NewQuan(string var, int kind)
{
	if (quanSize == 0)
	{
		quanSize++;
		quantifiers.push_back(Term(LGC_QUAN_SIZE,1,0));
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
			break;
		}
		++next;
	}
	if (next >= variables.size())
	{
		variables.push_back(Term(LGC_TERM_VAR,index));
		t.m_ref = variables.size() - 1;
	}
	quantifiers[lstQuans.back()].m_info++;
	quantifiers.push_back(Term(kind,next));
	return LGC_ERR_SUCC;
}


int xWam::NewVar(string name,int kind,int flag)
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
	if (next >= variables.size())
	{
		variables.push_back(Term(kind,index,flag));
		t.m_ref = variables.size() - 1;
	}
	if (flag == 0)
	{
		lstTerms.push_back(t);
	}
	return LGC_ERR_SUCC;
}


int xWam::NewLogicOp(int op)
{

	quanSize = 0;
	if (op == LGC_OP_NOT && lstOpers.back() == op)
	{
		lstOpers.push_back(op);
		return LGC_ERR_SUCC;
	}
	while ((!lstOpers.empty()) && lstOpers.back() >= op && lstOpers.back() <= LGC_OP_NOT )
	{
		lstTerms.push_back(Term(lstOpers.back()));
		lstOpers.pop_back();
	}
	lstOpers.push_back(op);	

	return LGC_ERR_SUCC;
}

int xWam::LeftPar()
{

	quanSize = 0;
	lstOpers.push_back(LGC_OP_LPAR);
	
	return LGC_ERR_SUCC;
}

int xWam::RightPar()
{

	while ((!lstOpers.empty()) && lstOpers.back()!=LGC_OP_LPAR)
	{
		lstTerms.push_back(Term(lstOpers.back()));
		lstOpers.pop_back();
	}
	lstOpers.pop_back();


	
	return LGC_ERR_SUCC;
}
xWam::operator string()const
{
	
	return "";
}
int xWam::print()
{
	cout<<"\n\n---------------Main---------------------\n";
	vector<Term>::const_iterator p = clauses.begin();
	int i = 0;
	for (;p!=clauses.end();++p)
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
			cout<<"\n"<<i++<<"\tCall :\t"<<names.GetString(clauses[(*p).m_ref].m_ref)<<"\tQuan="<<(*p).m_info<<"\n";
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



string xWam::GetString(int index)const
{
#if _DEBUG
	_ASSERT(index >=0 && index < clauses.size());
#endif
	if (index < 0 || index >= clauses.size())
	{
		cout << "Error while retrieve string!";
	}
	string result = "";
	int quan = clauses[index].m_info;
	if (quan > 0)
	{
		int size = quantifiers[quan].m_info;
		int offset = quantifiers[quan].m_ref;
		for (int i = 0; i < size; i++)
		{
			if(quantifiers[i + quan + offset].m_kind == LGC_QUAN_ALL)
			{
#if _DEBUG
				result += "all ";
#else
				result += "\\-";
#endif
				
			}
			else if(quantifiers[ i + quan + offset ].m_kind == LGC_QUAN_EXIST)
			{
#if _DEBUG
				result += "exists ";
#else
				result += "-]";
#endif
			}
			result += names.GetString(variables[quantifiers[i + quan + offset].m_ref].m_ref)+ " ";
		}
	}
	switch (clauses[index].m_kind)
	{
	case LGC_REF:
		result = GetString(clauses[index].m_ref);
		break;

	case LGC_TERM_FALSE:
		result = "_|_";
		break;

	case LGC_FUN_DEF:
		result = names.GetString(clauses[index].m_ref);
		break;

	case LGC_TERM_CONST:
		result = names.GetString(variables[clauses[index].m_ref].m_ref);
		break;

	case LGC_TERM_PROP:
		result += names.GetString(variables[clauses[index].m_ref].m_ref);
		break;

	case LGC_TERM_VAR:
		result = names.GetString(variables[clauses[index].m_ref].m_ref);
		break;

	case LGC_TERM_FUNC:
		int func = clauses[index].m_ref;
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
			break;
		case LGC_ADDR_AND:
			pars  = isOperator(index+1);
			if (quan)
			{
				result += "(";
			}
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
			if (quan)
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
			int args = clauses[func].m_info;
			result += GetString(func);
			result += "(";
			for (int i = 1; i < args ; i++)
			{
				result += GetString(index + i);
				result += ",";
			}
			result += GetString(index + args) + ")";
			break;
		}
		break;
	}
	return result;
}

bool xWam::isOperator(int index)const
{
	int i = index;
	while (clauses[i].m_kind ==LGC_REF)
	{
		i = clauses[i].m_ref;
	}
	if (clauses[i].m_kind == LGC_TERM_FUNC)
	{
		if ( clauses[i].m_ref == LGC_ADDR_AND ||clauses[i].m_ref == LGC_ADDR_OR ||clauses[i].m_ref == LGC_ADDR_MAP)
		{
			return true;
		}
	}
	return false;
}

int xWam:: ClauseVars(int index, list<int>&theta)const
{
#if _DEBUG
	_ASSERT(index >= 0 && index < clauses.size());
#endif	
	if (index < 0 || index >= clauses.size())
	{
		return 0;
	}


		while (clauses[index].m_kind == LGC_REF)
		{
			index = clauses[index].m_ref;
		}
   	    if( clauses[index].m_kind  == LGC_TERM_VAR)
		{
			if (find(theta.begin(),theta.end(),clauses[index].m_ref) == theta.end())
			{
				theta.push_back(clauses[index].m_ref);
#if _DEBUG
				cout<<"Var: "<<clauses[index].m_ref<<endl;
#endif
			}
		}
		else if( clauses[index].m_kind == LGC_TERM_FUNC)
		{
			int func = clauses[index].m_ref;
			int args = clauses[func].m_info;
			for (int i = 1; i <= args ; i++)
			{
				ClauseVars(index + i,theta);
			}
		}
		return 0;
}


int xWam::SubVars(int index, int flag)
{
#if _DEBUG
	_ASSERT(index >= 0 && index < variables.size());
#endif
	index = names.GetIndex(names.GetString(variables[index].m_ref) + ToString(variables[index].m_extra++));
	variables.push_back(Term(LGC_TERM_VAR,index,flag));
	return variables.size() - 1;
}

Term xWam::Get1stQuan(int index)
{
	int offset = quantifiers[index].m_ref;
	return quantifiers[index + offset];
}

int xWam::GetRemainQuan(int index)
{
	if (quantifiers[index].m_info > 1)
	{
		int position = quantifiers[index].m_ref + index;
		position =  position - quantifiers.size() + 1;
		quantifiers.push_back(Term(LGC_QUAN_SIZE,position,quantifiers[index].m_info - 1));
		return quantifiers.size() - 1;
	}
	return 0;
}

list<int>xWam::RestValidTerm(int index)const
{

	list<int>funVar;
	ClauseVars(index,funVar);
	list<int>vars;
	for (int i = 0; i < variables.size(); i++)
	{
		{
			if (find(funVar.begin(),funVar.end(),i) == funVar.end())
			{
				vars.push_back(i);
			}
			
		}
	}
	return vars;
}

int xWam::CopyClause(int index,int oldVar,int newVar)
{
	int size =  clauses[clauses[index].m_ref].m_info;
	Term* arg =new Term[size];
	for (int i = 1; i <= size; i++)
	{
		if (clauses[i + index].m_kind == LGC_TERM_VAR)
		{
			if (clauses[i+index].m_ref == oldVar)
			{
				arg[ i - 1] = Term(variables[newVar].m_kind,newVar);
			}
			else
			{
				arg[i - 1] = clauses[i + index];
			}
		}
		else if (clauses[i + index].m_kind == LGC_REF)
		{
			int pos = i + index;
			while (clauses[pos].m_kind == LGC_REF)
			{
				pos = clauses[pos].m_ref;
			}
			arg[i-1] = Term(LGC_REF,CopyClause(pos,oldVar,newVar));
		}
		else
		{
			arg[i - 1] =  clauses[i + index];
		}
	}

	int result = clauses.size();
	clauses.push_back(clauses[index]);
	for (i = 0; i < size; i++)
	{
		clauses.push_back(arg[i]);
	}
	delete[] arg;
	return result;
}

int xWam::DupVar(int index, int flag)
{
#if _DEBUG
	_ASSERT(index >=0 && index < variables.size());
#endif
	int ref = variables[index].m_ref;
	for (int i = 0; i < variables.size(); i++)
	{
		if (variables[i].m_ref == ref && (variables[i].m_info & LGC_VAR_DUPLICATE) == LGC_VAR_DUPLICATE)
		{
			return i;
		}
	}
	Term t(LGC_TERM_VAR,ref,variables[index].m_info);
	t.m_info |= LGC_VAR_DUPLICATE | flag;
	variables.push_back(t);
	return variables.size() - 1;
}