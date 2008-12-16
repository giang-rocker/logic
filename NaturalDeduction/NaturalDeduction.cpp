// NaturalDeduction.cpp: implementation of the NaturalDeduction class.
//
//////////////////////////////////////////////////////////////////////

#include "NaturalDeduction.h"
#include <algorithm>
#include <math.h>

//////////////////////////////////////////////////////////////////////
// Construction/Destruction
//////////////////////////////////////////////////////////////////////

NaturalDeduction::NaturalDeduction(xWam t)
{
	knowledgeBase = t;
	list<int>::const_iterator p = t.conditions.begin();
	for (;p!=t.conditions.end();++p)
	{
		NDTerm t(*p);
		t.m_source = LGC_SRC_PREMISE;
		t.m_rule = LGC_RULE_PREMISE;
		t.m_isPremise = true;
		conditions.push_back(t);
	}
	for (p = t.goals.begin();p!=t.goals.end();++p)
	{
		goals.push_back(NDTerm(*p));
	}

	lastLine = 1;
	ifs = 0;
	isInsert = false;
}



bool NaturalDeduction::isCompatible(int father, int son)const
{

	if (knowledgeBase.clauses[father].m_kind == LGC_REF)
	{
		return isCompatible(knowledgeBase.clauses[father].m_ref,son);
	}

	if (knowledgeBase.clauses[son].m_kind == LGC_REF)
	{
		return isCompatible(father,knowledgeBase.clauses[son].m_ref);
	}
	if (knowledgeBase.clauses[son].m_kind == LGC_TERM_VAR)
	{
		Term var = knowledgeBase.variables[knowledgeBase.clauses[son].m_ref];
		if (var.m_info == LGC_VAR_ANY_VALUE)
		{
			return true;			
		}
		if (var.m_info == LGC_VAR_ABS_UNFLAG)
		{
			Term fVar =  knowledgeBase.variables[knowledgeBase.clauses[father].m_ref];
			return fVar.m_info == LGC_VAR_ABS_UNFLAG;
		}	
	}
	if (knowledgeBase.clauses[son].m_kind == knowledgeBase.clauses[father].m_kind)
	{
		int r1 = knowledgeBase.clauses[father].m_ref;
		int r2 = knowledgeBase.clauses[son].m_ref;
		switch (knowledgeBase.clauses[father].m_kind)
		{
		case LGC_TERM_VAR:
			return r1 == r2;
		case LGC_TERM_PROP:
			return r1 == r2;
		case LGC_TERM_CONST:
			return r1 == r2;
		case LGC_TERM_FUNC:
			if(r1 == r2)
			{
				int sonLink  = knowledgeBase.clauses[son].m_info;
				int fatherLink = knowledgeBase.clauses[father].m_info;
				if (sonLink > 0  || fatherLink> 0)
				{
					int size = knowledgeBase.quantifiers[fatherLink].m_info;
					if(size != knowledgeBase.quantifiers[sonLink].m_info)
					{
						return false;
					}
					sonLink = knowledgeBase.quantifiers[sonLink].m_ref + sonLink;
					fatherLink = knowledgeBase.quantifiers[fatherLink].m_ref + fatherLink;
					for (int i = 0; i <size; i++)
					{
						if (	knowledgeBase.quantifiers[sonLink+i].m_info != knowledgeBase.quantifiers[fatherLink+i].m_info
							 || knowledgeBase.quantifiers[sonLink+i].m_kind != knowledgeBase.quantifiers[fatherLink+i].m_kind
							 || knowledgeBase.quantifiers[sonLink+i].m_ref != knowledgeBase.quantifiers[fatherLink+i].m_ref
							)
						{
							return false;
						}
					}
					
				} 
				int args = knowledgeBase.clauses[r1].m_info;
				for (int i = 1; i<= args;i++)
				{
					if (!isCompatible(father+i,son+i))
					{
						return false;
					}
				}
				return true;
			}
		}
	}
	return false;
}

int NaturalDeduction::eliminate()
{

	list<NDTerm>::iterator p ;
	
	int added = 0;
	int arg1 = 0;
	int arg2 = 0;
	int outside = -1;
	int index;
	for (p = conditions.begin();p!=conditions.end();++p)
	{;
		outside++;

		if ((*p).m_source & LGC_SRC_DISABLE == LGC_SRC_DISABLE)
		{
			continue;
		}
		NDTerm ndTerm;
		int main = (*p).m_index;
		while (knowledgeBase.clauses[main].m_kind == LGC_REF)
		{
			main = knowledgeBase.clauses[main].m_ref;
		}

		if (knowledgeBase.clauses[main].m_info <= 0)
		{

			if (knowledgeBase.clauses[main].m_kind == LGC_TERM_FUNC)
			{
				switch (knowledgeBase.clauses[main].m_ref)
				{

				case LGC_ADDR_NOT:
					arg1 = main + 1;
					while (knowledgeBase.clauses[arg1].m_kind == LGC_REF)
					{
						arg1 = knowledgeBase.clauses[arg1].m_ref;
					}
					
					if (knowledgeBase.clauses[arg1].m_kind == LGC_TERM_FUNC )
					{
						if (knowledgeBase.clauses[arg1].m_ref == LGC_ADDR_NOT && ((*p).m_proceed & LGC_PRC_E_NOT) != LGC_PRC_E_NOT)
						{
							(*p).m_proceed |= LGC_PRC_E_NOT;
							arg2 = arg1 + 1;
							while (knowledgeBase.clauses[arg2].m_kind == LGC_REF)
							{
								arg2 = knowledgeBase.clauses[arg2].m_ref;
							}
							ndTerm.m_index = arg2;
							ndTerm.m_rule = LGC_E_DNEG;
							ndTerm.m_path = (*p).m_path + 1;
							ndTerm.m_first = outside;
							ndTerm.m_derivation = outside;
							ndTerm.m_isPremise = (*p).m_isPremise;
							added += insertCondition(ndTerm,index);
						}
						/*else if(database.functions[arg1].m_ref == LGC_ADDR_OR && ((*p).m_proceed & LGC_PRC_DEMOR)!=LGC_PRC_DEMOR)
						{
							(*p).m_proceed |=LGC_PRC_DEMOR;
							database.functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT));
							database.functions.push_back(database.functions[arg1 +1]);
							database.functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT));
							database.functions.push_back(database.functions[arg1 +2]);
							database.functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_AND));
							database.functions.push_back(Term(LGC_REF,database.functions.size()-5));
							database.functions.push_back(Term(LGC_REF,database.functions.size()-4));
							ndTerm.m_index = database.functions.size() - 3;
							ndTerm.m_first = outside;
							ndTerm.m_rule = LGC_DEMOR_OR;
							ndTerm.m_proceed |= LGC_PRC_MORGAN;
							ndTerm.m_deviring = outside;
							ndTerm.isPremise = (*p).isPremise;
							added +=insertCondition(ndTerm,index);
							
						}
						else if(database.functions[arg1].m_ref == LGC_ADDR_AND && ((*p).m_proceed & LGC_PRC_DEMOR)!=LGC_PRC_DEMOR)
						{
							(*p).m_proceed |=LGC_PRC_DEMOR;
							database.functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT));
							database.functions.push_back(database.functions[arg1 +1]);
							database.functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT));
							database.functions.push_back(database.functions[arg1 +2]);
							database.functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_OR));
							database.functions.push_back(Term(LGC_REF,database.functions.size()-5));
							database.functions.push_back(Term(LGC_REF,database.functions.size()-4));
							ndTerm.m_index = database.functions.size() - 3;
							ndTerm.m_first = outside;
							ndTerm.m_rule = LGC_DEMOR_AND;
							ndTerm.m_proceed |= LGC_PRC_MORGAN;
							ndTerm.m_deviring = outside;
							ndTerm.isPremise = (*p).isPremise;
							added += insertCondition(ndTerm,index);
						}
						*/
					}

					break;
	
				case LGC_ADDR_AND:
					if (((*p).m_proceed & LGC_PRC_E_AND) != LGC_PRC_E_AND)
					{
						(*p).m_proceed |= LGC_PRC_E_AND;
						int arg1 = main + 1;
						while (knowledgeBase.clauses[arg1].m_kind == LGC_REF)
						{
							arg1 = knowledgeBase.clauses[arg1].m_ref;
						}

						ndTerm.m_index = arg1;
						ndTerm.m_rule = LGC_E_AND_1;
						ndTerm.m_first = outside;
						ndTerm.m_path = (*p).m_path + 1;
						ndTerm.m_derivation = outside;
						ndTerm.m_isPremise = (*p).m_isPremise;
						added += insertCondition(ndTerm,index);

						arg2 = main + 2;
						while (knowledgeBase.clauses[arg2].m_kind == LGC_REF)
						{
							arg2 = knowledgeBase.clauses[arg2].m_ref;
						}

						ndTerm.m_index = arg2;
						ndTerm.m_rule = LGC_E_AND_2;
						added += insertCondition(ndTerm,index);

					}
					break;


				/*case LGC_ADDR_OR:		
					// A v B , not(A) -> B
					
					if ( ((*p).m_proceed & LGC_PRC_E_OR1) != LGC_PRC_E_OR1)
					{
						arg1 = main + 1;
						arg2 = main + 2;
						while (database.functions[arg1].m_kind == LGC_REF)
						{
							arg1 = database.functions[arg1].m_ref;
						}
						
						list<NDTerm>::const_iterator leftOp = conditions.begin();
						int inside = -1;
						for (;leftOp!=conditions.end();++leftOp)
						{
							++inside;
							NDTerm ndTerm;
							if ((*leftOp).m_source & LGC_SRC_DISABLE == LGC_SRC_DISABLE)
							{
								continue;
							}
							int left = (*leftOp).m_index;
							while (database.functions[left].m_kind == LGC_REF)
							{
								left = database.functions[left].m_ref;
							}
							if (isComplement(arg1,left) || isComplement(left,arg1))
							{
								while (database.functions[arg2].m_kind == LGC_REF)
								{
									arg2 = database.functions[arg2].m_ref;
								}

								ndTerm.m_index = arg2;
								ndTerm.m_first =  outside;
								ndTerm.m_second = inside;
								ndTerm.m_path = (*p).m_path < (*leftOp).m_path ? (*p).m_path + 1 : (*leftOp).m_path + 1; 
								ndTerm.m_rule = LGC_E_OR_1;
								ndTerm.m_deviring = outside;
								ndTerm.isPremise = (*p).isPremise && (*leftOp).isPremise; 
								added += insertCondition(ndTerm,index);
								(*p).m_proceed |= LGC_PRC_E_OR1;
								(*p).m_proceed |= LGC_PRC_C_OR1;
							}
							
						}
						
					}
					// A v B , not(B) -> A
					if (((*p).m_proceed & LGC_PRC_E_OR2) != LGC_PRC_E_OR2)
					{
						arg1 = main + 1;
						arg2 = main + 2;
						while (database.functions[arg2].m_kind == LGC_REF)
						{
							arg2 = database.functions[arg2].m_ref;
						}
						
						list<NDTerm>::const_iterator leftOp = conditions.begin();
						int inside = -1;
						for (;leftOp!=conditions.end();++leftOp)
						{
							++inside;
							NDTerm ndTerm;
							if ((*leftOp).m_source & LGC_SRC_DISABLE == LGC_SRC_DISABLE)
							{
								continue;
							}
							int left = (*leftOp).m_index;
							while (database.functions[left].m_kind == LGC_REF)
							{
								left = database.functions[left].m_ref;
							}

							if (isComplement(arg2,left) || isComplement(left,arg2) )
							{
								while (database.functions[arg1].m_kind == LGC_REF)
								{
									arg1 = database.functions[arg1].m_ref;
								}
								
								ndTerm.m_index = arg1;
								ndTerm.m_first =  outside;
								ndTerm.m_second = inside ;
								ndTerm.m_path = (*p).m_path < (*leftOp).m_path ? (*p).m_path + 1 : (*leftOp).m_path + 1; 
								ndTerm.m_rule = LGC_E_OR_2;
								ndTerm.m_deviring = outside;
								ndTerm.isPremise = (*p).isPremise && (*leftOp).isPremise;
								added += insertCondition(ndTerm,index);
								(*p).m_proceed |= LGC_PRC_E_OR2;
								(*p).m_proceed |= LGC_PRC_C_OR2;
							}
							
						}
						
					}

					break;
				*/

				case LGC_ADDR_MAP:
					if (((*p).m_proceed & LGC_PRC_E_MAP) != LGC_PRC_E_MAP)
					{
						
						arg1 = main + 1;
						arg2 = main + 2;
						while (knowledgeBase.clauses[arg1].m_kind == LGC_REF)
						{
							arg1 = knowledgeBase.clauses[arg1].m_ref;
						}

						list<NDTerm>::const_iterator leftOp = conditions.begin();
						int inside = -1;
						for (;leftOp!=conditions.end();++leftOp)
						{
							++inside;
							NDTerm ndTerm;
							if ((*leftOp).m_source & LGC_SRC_DISABLE == LGC_SRC_DISABLE)
							{
								continue;
							}
							int left = (*leftOp).m_index;
							while (knowledgeBase.clauses[left].m_kind == LGC_REF)
							{
								left = knowledgeBase.clauses[left].m_ref;
							}
							if (isCompatible(left,arg1))
							{
								
								while (knowledgeBase.clauses[arg2].m_kind == LGC_REF)
								{
									arg2 = knowledgeBase.clauses[arg2].m_ref;
								}
								ndTerm.m_index = arg2;
								ndTerm.m_first = outside; 
								ndTerm.m_second = inside ; 
								ndTerm.m_path = (*p).m_path < (*leftOp).m_path ? (*p).m_path + 1 : (*leftOp).m_path + 1; 
								ndTerm.m_rule = LGC_E_MAP;
								ndTerm.m_derivation = outside;
								ndTerm.m_isPremise = (*p).m_isPremise && (*leftOp).m_isPremise;
								added += insertCondition(ndTerm,index);
								(*p).m_proceed |= LGC_PRC_E_MAP;
								(*p).m_proceed |= LGC_PRC_C_MAP;
							}
							
						}
						
					}
					break;

				default:
						
					break;
				}
				
			}
		}

		//////////////////////////////////////////////////////////////////////////
		////////////////////////////Quantifier eliminate//////////////////////////
		else 
		{
		
			Term quant = knowledgeBase.Get1stQuan(knowledgeBase.clauses[main].m_info);
			int qRemain = knowledgeBase.GetRemainQuan(knowledgeBase.clauses[main].m_info);
			if (qRemain >= 0)
			{
				cout << knowledgeBase.quantifiers[qRemain].toString()<<endl;
			}
			if (quant.m_kind == LGC_QUAN_ALL)
			{
				list<int>vars = knowledgeBase.RestValidTerm(main);
				for (list<int>::iterator lst = vars.begin(); lst != vars.end(); ++lst)
				{
					if (find((*p).substed.begin(),(*p).substed.end(),*lst)==(*p).substed.end())
					{
						(*p).substed.push_back(*lst);
						int newVar = *lst;
						if ((knowledgeBase.variables[(*lst)].m_info & LGC_VAR_ANY_VALUE) ==LGC_VAR_ANY_VALUE)
						{
							newVar = knowledgeBase.DupVar(*lst,LGC_VAR_UNDEFINE);
						}
						int clause = knowledgeBase.CopyClause(main,quant.m_ref,newVar);
						knowledgeBase.clauses[clause].m_info = qRemain;
						NDTerm t(clause, LGC_E_ALL,outside);
						t.m_path = (*p).m_path + 1;
						conditions.push_back(t);
						added++;
					}
				}
			}
			else
			{
				int newVar = knowledgeBase.SubVars(quant.m_ref, LGC_VAR_REL_UNFLAG);
				(*p).m_source |= LGC_SRC_DISABLE;
				int clause = knowledgeBase.CopyClause(main,quant.m_ref,newVar);
				knowledgeBase.clauses[clause].m_info = qRemain;
				NDTerm t(clause,LGC_E_EXISTS,outside);
				t.m_path = (*p).m_path+1;
				conditions.push_back(t);
				added++;
			}
			
		}

	}
	
	return added;
}

int NaturalDeduction::introduction()
{

	int subgoal = goals.back().m_index;
	int assume = -1;
	while (knowledgeBase.clauses[subgoal].m_kind == LGC_REF)
	{
		subgoal = knowledgeBase.clauses[subgoal].m_ref;
	}

	int arg1 = 0;
	int arg2 = 0;
	int status = goals.back().m_proceed;
	NDTerm t;
	int added = 0;
	if(knowledgeBase.clauses[subgoal].m_info <= 0)
	{
		if (knowledgeBase.clauses[subgoal].m_kind == LGC_TERM_FUNC)
		{
			switch (knowledgeBase.clauses[subgoal].m_ref)
			{

			// |- NOT F => F |- NOT F, FALSE
			/*case LGC_ADDR_NOT:
				if ((status & LGC_PRC_I_NOT) !=LGC_PRC_I_NOT)
				{
					arg1 = subgoal + 1;
					while (database.functions[arg1].m_kind == LGC_REF)
					{
						arg1 = database.functions[arg1].m_ref;
					}
					t.m_index = arg1;
					t.m_source |= LGC_SRC_ASSUME;
					insertCondition(t,assume);
					goals.back().m_pendings = 1;
					goals.back().m_rule = LGC_I_NOT;
					goals.back().m_proceed |= LGC_PRC_I_NOT;
					goals.back().m_assume = assume;
					goals.back().m_deviring = assume;
					NDTerm conclusion(LGC_ADDR_FALSE);
					conclusion.m_source |= LGC_SRC_CONCLUSION;
					goals.push_back(NDTerm(conclusion));
					return 1;
				}
				break;
			*/
			// |- P ^ Q => |- P ^ Q , P, Q
			case LGC_ADDR_AND:
				if ((status & LGC_PRC_I_AND) !=LGC_PRC_I_AND)
				{
					arg1 = subgoal + 1;
					arg2 = subgoal + 2;
					
					while (knowledgeBase.clauses[arg1].m_kind == LGC_REF)
					{
						arg1 = knowledgeBase.clauses[arg1].m_ref;
					}
					
					while (knowledgeBase.clauses[arg2].m_kind == LGC_REF)
					{
						arg2 = knowledgeBase.clauses[arg2].m_ref;
					}

					goals.back().m_pendings = 2;
					goals.back().m_rule = LGC_I_AND;
					goals.back().m_proceed |= LGC_PRC_I_AND;
					goals.push_back(NDTerm(arg2));
					goals.push_back(NDTerm(arg1));
					return 1;
				}
				break;


			// |- P | Q -> |- P -> |- Q -> NOT(P|Q) |- FALSE
			case LGC_ADDR_OR:
				if ((status & LGC_PRC_I_OR1) !=LGC_PRC_I_OR1)
				{
					arg1 = subgoal + 1;
					while (knowledgeBase.clauses[arg1].m_kind == LGC_REF)
					{
						arg1 = knowledgeBase.clauses[arg1].m_ref;
					}
					goals.back().m_pendings = 1;
					goals.back().m_rule = LGC_I_OR_1;
					goals.back().m_proceed |= LGC_PRC_I_OR1;
					branches.push_back(goals.size());
					branches.push_back(conditions.size());
					branches.push_back(proveds.size());
					
					int m_size = 0;
					int m_or  = -1;
					for (list<NDTerm>::iterator lst = conditions.begin();lst!=conditions.end();++lst)
					{
						m_or++;
						if ((*lst).m_source & LGC_SRC_DISABLE == LGC_SRC_DISABLE)
						{
							continue;
						}
						int main = (*lst).m_index;
						while (knowledgeBase.clauses[main].m_kind == LGC_REF)
						{
							main = knowledgeBase.clauses[main].m_ref;
						}
						
						if (knowledgeBase.clauses[main].m_info == 0)
						{	
							if (knowledgeBase.clauses[main].m_kind == LGC_TERM_FUNC && knowledgeBase.clauses[main].m_ref == LGC_ADDR_OR)
							{
								branches.push_back((*lst).m_OrEnable);
								branches.push_back(m_or);
								m_size++;
							}
						}
					} 
					branches.push_back(m_size);

					goals.push_back(NDTerm(arg1));
				} 

				else if ((status & LGC_PRC_I_OR2) !=LGC_PRC_I_OR2)
				{
					arg2 = subgoal + 2;
					while (knowledgeBase.clauses[arg2].m_kind == LGC_REF)
					{
						arg2 = knowledgeBase.clauses[arg2].m_ref;
					}
					goals.back().m_pendings = 1;
					goals.back().m_rule = LGC_I_OR_2;
					goals.back().m_proceed |= LGC_PRC_I_OR2;
					branches.push_back(goals.size());
					branches.push_back(conditions.size());
					branches.push_back(proveds.size());
					int m_size = 0;
					int m_or  = -1;
					for (list<NDTerm>::iterator lst = conditions.begin();lst!=conditions.end();++lst)
					{
						m_or++;
						if ((*lst).m_source & LGC_SRC_DISABLE == LGC_SRC_DISABLE)
						{
							continue;
						}
						int main = (*lst).m_index;
						while (knowledgeBase.clauses[main].m_kind == LGC_REF)
						{
							main = knowledgeBase.clauses[main].m_ref;
						}
						
						if (knowledgeBase.clauses[main].m_info == 0)
						{	
							if (knowledgeBase.clauses[main].m_kind == LGC_TERM_FUNC && knowledgeBase.clauses[main].m_ref == LGC_ADDR_OR)
							{
								branches.push_back((*lst).m_OrEnable);
								branches.push_back(m_or);
								m_size++;
							}
						}
					} 
					branches.push_back(m_size);

					goals.push_back(NDTerm(arg2));
					
				}

				else if((status & LGC_PRC_I_OR3) !=LGC_PRC_I_OR3)
				{
					knowledgeBase.clauses.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT));
					knowledgeBase.clauses.push_back(Term(LGC_REF,subgoal));
					arg1 = knowledgeBase.clauses.size() - 2;
					t.m_index = arg1;
					t.m_source = LGC_SRC_ASSUME;
					insertCondition(t,assume);
					goals.back().m_pendings = 1;
					goals.back().m_rule = LGC_I_NOT;
					goals.back().m_assume = assume;
					goals.back().m_proceed |= LGC_PRC_I_OR3;
					goals.back().m_derivation = assume;
					NDTerm conclusion(LGC_ADDR_FALSE);
					conclusion.m_source = LGC_SRC_CONCLUSION;
					goals.push_back(NDTerm(conclusion));	
				}
				else
				{
					return 0;
				}
				return 1;

			// |- P -> Q => P |- Q
			case LGC_ADDR_MAP:
				if ((status & LGC_PRC_I_MAP) !=LGC_PRC_I_MAP)
				{
					arg1 = subgoal + 1;
					arg2 = subgoal + 2;
					while (knowledgeBase.clauses[arg1].m_kind == LGC_REF)
					{
						arg1 = knowledgeBase.clauses[arg1].m_ref;
					}
					while (knowledgeBase.clauses[arg2].m_kind == LGC_REF)
					{
						arg2 = knowledgeBase.clauses[arg2].m_ref;
					}
					t.m_index = arg1;
					t.m_source = LGC_SRC_ASSUME;
					conditions.push_back(t);
					added += 1;
					goals.back().m_pendings = 1;
					goals.back().m_rule = LGC_I_MAP;
					goals.back().m_proceed |= LGC_PRC_I_MAP;
					goals.back().m_assume = conditions.size() - 1;
					goals.back().m_derivation = conditions.size() - 1;
					NDTerm conclusion(arg2);
					conclusion.m_source = LGC_SRC_CONCLUSION;
					goals.push_back(NDTerm(conclusion));
				}
				break;

			//	|- P	=>	NOT P |- P , FALSE
			/* default:
				if ((status & LGC_PRC_I_NOT) !=LGC_PRC_I_NOT)
				{
					database.functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT));
					database.functions.push_back(Term(LGC_REF,subgoal));
					arg1 = database.functions.size() - 2;
					t.m_index = arg1;
					t.m_proceed |= LGC_PRC_C_NOT;
					t.m_source = LGC_SRC_ASSUME;
					added += insertCondition(t,assume);
					goals.back().m_pendings = 1;
					goals.back().m_rule = LGC_I_NOT;
					goals.back().m_proceed |= LGC_PRC_I_NOT;
					goals.back().m_assume = assume;
					goals.back().m_deviring = assume;
					NDTerm conclusion(LGC_ADDR_FALSE);
					conclusion.m_source = LGC_SRC_CONCLUSION;
					goals.push_back(NDTerm(conclusion));	
				}
				break;
			*/
			}
		}
		/*
		else if(subgoal!=LGC_ADDR_FALSE)
		{
			if ((status & LGC_PRC_I_NOT) !=LGC_PRC_I_NOT)
			{
				database.functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT));
				database.functions.push_back(Term(LGC_REF,subgoal));
				arg1 = database.functions.size() - 2;
				t.m_index = arg1;
				t.m_proceed |= LGC_PRC_C_NOT;
				t.m_source = LGC_SRC_ASSUME;
				added += insertCondition(t,assume);
				goals.back().m_pendings = 1;
				goals.back().m_rule = LGC_I_NOT;
				goals.back().m_proceed |= LGC_PRC_I_NOT;
				goals.back().m_assume = assume;
				goals.back().m_deviring = assume;
				NDTerm conclusion(LGC_ADDR_FALSE);
				conclusion.m_source = LGC_SRC_CONCLUSION;
				goals.push_back(NDTerm(conclusion));
			}
		}
		*/
	}

	//Quantifier introduction
	else
	{
		Term quant = knowledgeBase.Get1stQuan(knowledgeBase.clauses[subgoal].m_info);
		int qRemain = knowledgeBase.GetRemainQuan(knowledgeBase.clauses[subgoal].m_info);
		if (quant.m_kind == LGC_QUAN_ALL)
		{
			goals.back().m_pendings = 1;
			goals.back().m_rule = LGC_I_ALL;
			goals.back().m_proceed |= LGC_PRC_I_ALL;
			goals.back().m_source |= LGC_SRC_ALL_FLAG;
			int subVar =  knowledgeBase.SubVars(quant.m_ref,LGC_VAR_ABS_UNFLAG);
			goals.back().m_VarRef = subVar;
			int subClause = knowledgeBase.CopyClause(subgoal,quant.m_ref,subVar);
			knowledgeBase.clauses[subClause].m_info = qRemain;
			NDTerm t(subClause);
			added++;
			goals.push_back(t);
		}
		else
		{
			goals.back().m_pendings = 1;
			goals.back().m_rule = LGC_I_EXISTS;
			goals.back().m_proceed |= LGC_PRC_I_EXI;
			goals.back().m_source |= LGC_SRC_EXIST_FLAG;
			int subVar =  knowledgeBase.SubVars(quant.m_ref,LGC_VAR_ANY_VALUE);
			int subClause = knowledgeBase.CopyClause(subgoal,quant.m_ref,subVar);
			knowledgeBase.clauses[subClause].m_info = qRemain;
			NDTerm t(subClause);
			added++;
			goals.push_back(t);
		}
	}

	return added;
}

int NaturalDeduction::contradiction()
{
	list<NDTerm>::iterator p;
	int outside = -1;
	for (p = conditions.begin();p!=conditions.end();++p)
	{
		outside++;
		if ((*p).m_source & LGC_SRC_DISABLE == LGC_SRC_DISABLE)
		{
			continue;
		}
		int source = (*p).m_index;
		while (knowledgeBase.clauses[source].m_kind == LGC_REF)
		{
			source = knowledgeBase.clauses[source].m_ref;
		}
		int arg1 = source + 1;

		NDTerm t;
		if (knowledgeBase.clauses[source].m_info == 0 && knowledgeBase.clauses[source].m_kind == LGC_TERM_FUNC)
		{
			switch (knowledgeBase.clauses[source].m_ref)
			{

			/*case LGC_ADDR_NOT:
				if (((*p).m_proceed & LGC_PRC_C_NOT)!=LGC_PRC_C_NOT)
				{
					(*p).m_proceed |=LGC_PRC_C_NOT;
					while (database.functions[arg1].m_kind == LGC_REF)
					{
						arg1 = database.functions[arg1].m_ref;
					}
					t.m_index = arg1;
					t.m_proceed |= LGC_PRC_C_NOT;
					t.m_source	= LGC_SRC_HOPING;
					t.m_deviring = outside;
					return insertGoal(t);
					
				}
				break; 

			case LGC_ADDR_OR:
				if (((*p).m_proceed & LGC_PRC_C_OR1)!=LGC_PRC_C_OR1)
				{
					(*p).m_proceed |= LGC_PRC_C_OR1;
					while (database.functions[arg1].m_kind == LGC_REF)
					{
						arg1 = database.functions[arg1].m_ref;
					}
					database.functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT));
					database.functions.push_back(Term(LGC_REF,arg1));
					t.m_index = database.functions.size() - 2;
					t.m_source	= LGC_SRC_HOPING;
					t.m_deviring = outside;
					return insertGoal(t);
					
				}
				else if (((*p).m_proceed & LGC_PRC_C_OR2)!=LGC_PRC_C_OR2)
				{
					(*p).m_proceed |= LGC_PRC_C_OR2;
					while (database.functions[arg2].m_kind == LGC_REF)
					{
						arg2 = database.functions[arg1].m_ref;
					}
					database.functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT));
					database.functions.push_back(Term(LGC_REF,arg2));
					t.m_index = database.functions.size() - 2;
					t.m_source |= LGC_SRC_HOPING;
					t.m_deviring = outside;
					return insertGoal(t);
				} 
				break;
			*/
			case LGC_ADDR_MAP:
				if (((*p).m_proceed & LGC_PRC_C_MAP)!=LGC_PRC_C_MAP)
				{
					(*p).m_proceed |=LGC_PRC_C_MAP;
					while (knowledgeBase.clauses[arg1].m_kind == LGC_REF)
					{
						arg1 = knowledgeBase.clauses[arg1].m_ref;
					}
					t.m_index = arg1;
					t.m_proceed |=LGC_PRC_C_MAP;
					t.m_source |= LGC_SRC_HOPING;
					t.m_derivation = outside;
					return insertGoal(t);
				}
				break;

			}
		}
	}

	return 0;
}



bool NaturalDeduction::isComplement(int active, int negative) const
{
	int neg = negative;
	while (knowledgeBase.clauses[neg].m_kind == LGC_REF)
	{
		neg = knowledgeBase.clauses[neg].m_ref;
	}

	if (knowledgeBase.clauses[neg].m_kind == LGC_TERM_FUNC && knowledgeBase.clauses[neg].m_ref == LGC_ADDR_NOT)
	{
		
		neg++;
		while (knowledgeBase.clauses[neg].m_kind == LGC_REF)
		{
			neg = knowledgeBase.clauses[neg].m_ref;
		}
		return isCompatible(active,neg);	
	}
	return false;
}

int NaturalDeduction::ProveIt()
{
	
	int times = 0;
	int active;
	int negative;
	while (!goals.empty())
	{
		active = -1;
		negative = -1;
		debug(times++);
		NDTerm orGoal;
		bool optimized = false;
		while(!proveds.empty())
		{
			int pGoal = proveds.back();
			getNDTerm(pGoal);
			if (((*cond).m_source & LGC_SRC_HOPING) == LGC_SRC_HOPING)
			{
				proveds.pop_back();
			}
			else
			{
				break;
			}
		}
		if ((goals.back().m_source & LGC_SRC_OR_SUB_1 ) == LGC_SRC_OR_SUB_1) 
		{
			getNDTerm(goals.back().m_derivation);
			int subgoal = (*cond).m_index;
			int arg1 = subgoal + 1;
			while (knowledgeBase.clauses[arg1].m_kind == LGC_REF)
			{
				arg1 = knowledgeBase.clauses[arg1].m_ref;
			}
			NDTerm t;
			t.m_isPremise = false;
			t.m_path = (*cond).m_path + 1;
			t.m_index = arg1;
			t.m_source = LGC_SRC_ASSUME;
			t.m_derivation = goals.back().m_derivation;
			int assume = conditions.size();
			conditions.push_back(t);
			goals.back().m_source = LGC_SRC_CONCLUSION | LGC_SRC_OR_CONC  ;
			goals.back().m_derivation = assume;
			goals.back().m_OrAssume = assume;
		}

		else if ((goals.back().m_source & LGC_SRC_OR_SUB_2 ) == LGC_SRC_OR_SUB_2)
		{
			getNDTerm(goals.back().m_derivation);
			int subgoal = (*cond).m_index;
			int arg2= subgoal + 2;
			while (knowledgeBase.clauses[arg2].m_kind == LGC_REF)
			{
				arg2 = knowledgeBase.clauses[arg2].m_ref;
			}
			NDTerm t;
			t.m_isPremise = false;
			t.m_index = arg2;
			t.m_source = LGC_SRC_ASSUME;
			t.m_derivation = goals.back().m_derivation;
			int assume = conditions.size();
			conditions.push_back(t);
			goals.back().m_source = LGC_SRC_CONCLUSION | LGC_SRC_OR_CONC  ;
			goals.back().m_derivation = assume;
			goals.back().m_OrAssume = assume;
		}

		if (goals.back().m_pendings > 0)
		{

			goals.back().m_proceed |= LGC_PRC_CONTR;
			getNDTerm(proveds.back());
			if ((*cond).m_index == LGC_ADDR_FALSE)
			{
				if ((goals.back()).m_assume >= 0 && goals.back().m_assume < conditions.size())
				{
					disable((goals.back()).m_assume);
				}
				if (isReached(active))
				{
					proveds.pop_back();
					conditions.back().m_source |= LGC_SRC_DISABLE;
					getNDTerm(active);
					NDTerm t = (*cond);
					t.m_OrAssume = goals.back().m_OrAssume;
					proveds.push_back(conditions.size());
					conditions.push_back(t);
					if (t.m_OrAssume >= 0 && t.m_OrAssume < conditions.size())
					{
						disable(t.m_OrAssume);
					}
					
					else if (t.m_assume >= 0 && t.m_assume < conditions.size())
					{
						disable(t.m_assume);
					}
					goals.pop_back();
					continue;
				}
			}
			goals.back().m_first = proveds.back();
			proveds.pop_back();
			getNDTerm(goals.back().m_first);
			goals.back().m_isPremise = (*cond).m_isPremise;
			if (goals.back().m_pendings == 2)
			{
				goals.back().m_second = proveds.back();
				proveds.pop_back();
				getNDTerm(goals.back().m_first);
				goals.back().m_isPremise = goals.back().m_isPremise & (*cond).m_isPremise;
				if ((goals.back().m_source & LGC_SRC_OR_GOAL) == LGC_SRC_OR_GOAL)
				{
					PrintIndex();
					int f1 = goals.back().m_first;
					getNDTerm(f1);
					int s1 = (*cond).m_OrAssume;
					int f2 = goals.back().m_second;
					getNDTerm(f2);
					int s2 = (*cond).m_OrAssume;
					getFarest(f1,f2,s1,s2);
					
					
					if ( f1 != goals.back().m_first)
					{

						getNDTerm(goals.back().m_first);
						(*cond).m_source |= LGC_SRC_DISABLE;
						NDTerm nd1 = (*cond);
						getNDTerm(f1);
						(*cond).m_OrAssume = nd1.m_OrAssume;
						(*cond).m_source |= (LGC_SRC_CONCLUSION | LGC_SRC_OR_CONC);

						getNDTerm(goals.back().m_first);
						(*cond).m_source &=  (0xFFFFFFFF ^ LGC_SRC_OR_CONC);
						(*cond).m_OrAssume = -1;
						(*cond).m_derivation = -1;

						getNDTerm(goals.back().m_second);
						(*cond).m_source |= LGC_SRC_DISABLE;
						NDTerm nd2 = (*cond);
						getNDTerm(f2);
						(*cond).m_OrAssume = nd2.m_OrAssume;
						(*cond).m_source |= (LGC_SRC_CONCLUSION | LGC_SRC_OR_CONC);


						getNDTerm(goals.back().m_second);
						(*cond).m_source &=  (0xFFFFFFFF ^ LGC_SRC_OR_CONC);
						(*cond).m_OrAssume = -1;
						(*cond).m_derivation = -1;

						NDTerm subGoal = goals.back();
						goals.back().m_first = f1;
						goals.back().m_second = f2;;
						getNDTerm(f1);
						goals.back().m_index = (*cond).m_index;

						getNDTerm(goals.back().m_third);
						(*cond).m_OrEnable = true;
						goals.back().m_rule = LGC_E_OR;
						goals.back().m_OrAssume = -1;
						conditions.push_back(goals.back());
						goals.pop_back();
						PrintIndex();
						for (int i = 0; i <= conditions.size()-2; i++)
						{
							getNDTerm(i);
							if ((*cond).m_third == f1)
							{
								(*cond).m_third = conditions.size() - 1;
							}
							if ((*cond).m_second == f1)
							{
								(*cond).m_second = conditions.size() - 1;
							}
							if ((*cond).m_first == f1)
							{
								(*cond).m_first = conditions.size() - 1;
							}
						}
						getNDTerm(subGoal.m_first);
						NDTerm lastGoal = *cond;
						lastGoal.m_OrAssume = subGoal.m_OrAssume;
						lastGoal.m_source |= (subGoal.m_source & LGC_SRC_OR_CONC);
						lastGoal.m_source &= (0xFFFFFFFF ^ LGC_SRC_OR_GOAL);
						proveds.push_back(conditions.size());
						conditions.push_back(lastGoal);
						PrintIndex();
						continue;
					} 
					else 
					
					{
						getNDTerm(goals.back().m_third);
						(*cond).m_OrEnable = true;
						goals.back().m_rule = LGC_E_OR;
						goals.back().m_source |= LGC_SRC_DISABLE;

					}
					
				}

			}

			if ((goals.back().m_source & LGC_SRC_ALL_FLAG) == LGC_SRC_ALL_FLAG)
			{
				disableVar(goals.back().m_VarRef);
			}

			conditions.push_back(goals.back());	
			if (goals.back().m_assume >= 0 && goals.back().m_assume < conditions.size())
			{
				disable(goals.back().m_assume);
				
			}
			if (goals.back().m_OrAssume >= 0 && goals.back().m_OrAssume < conditions.size())
			{
				disable(goals.back().m_OrAssume);
			}
			proveds.push_back(conditions.size() - 1);
			
			if ((goals.back().m_source & LGC_SRC_OR_CONC) == LGC_SRC_OR_CONC)
			{	
				
				if (isReached(active))
				{
					conditions.back().m_source &= 0xFFFFFFFF ^ LGC_SRC_OR_CONC;
					conditions.back().m_OrAssume = -1;
					proveds.pop_back();
					if ((goals.back().m_source & LGC_SRC_OR_SUB_2) == LGC_SRC_OR_SUB_2)
					{
						proveds.pop_back(); 
					}	
					else
					{
						goals.pop_back();
					}
					goals.pop_back();
					getNDTerm(active);
					NDTerm term = *cond;
					term.m_source &= 0xFFFFFFFF ^ LGC_SRC_OR_GOAL;
					term.m_third = -1;
					term.m_OrAssume = goals.back().m_OrAssume;
					term.m_source |= (goals.back().m_source & LGC_SRC_OR_CONC);
					proveds.push_back(conditions.size());
					conditions.push_back(term);
					getNDTerm(goals.back().m_third);
					(*cond).m_OrEnable = true;
					if (goals.back().m_OrAssume >=0 && goals.back().m_OrAssume < conditions.size())
					{
						disable(goals.back().m_OrAssume);
					}
					goals.pop_back();
					continue;
				}
				
			}
			goals.pop_back();
			
			
		}
		else
		{
			int subgoal = goals.back().m_index;
			if (subgoal == LGC_ADDR_FALSE)
			{
				if (isReached(active,negative))
				{
					goals.back().m_rule = LGC_E_NOT;
					goals.back().m_first = negative;
					goals.back().m_second = active;
					proveds.push_back(conditions.size());
					conditions.push_back(goals.back());
					if (goals.back().m_assume >= 0 && goals.back().m_assume< conditions.size())
					{
						disable(goals.back().m_assume);
					}
					goals.pop_back();
					continue;
				}
			} 
			else if (isReached(active))
			{
				proveds.push_back(active);
				if ((goals.back().m_source & LGC_SRC_OR_CONC) == LGC_SRC_OR_CONC)
				{	
					if (goals.back().m_OrAssume>=0 && goals.back().m_OrAssume <  conditions.size())
					{
						disable(goals.back().m_OrAssume);
					}
					if (isReached(active))
					{
						proveds.pop_back();
						if ((goals.back().m_source & LGC_SRC_OR_SUB_2) == LGC_SRC_OR_SUB_2)
						{
							proveds.pop_back(); 
						}	
						else
						{
							goals.pop_back();
						}
						goals.pop_back();
						getNDTerm(active);
						NDTerm term = *cond;
						term.m_source &= 0xFFFFFFFF ^ LGC_SRC_OR_GOAL;
						term.m_third = -1;
						term.m_OrAssume = goals.back().m_OrAssume;
						term.m_source |= (goals.back().m_source & LGC_SRC_OR_CONC);
						conditions.push_back(term);
						getNDTerm(goals.back().m_third);
						(*cond).m_OrEnable = true;
						goals.pop_back();
						proveds.push_back(conditions.size());
						continue;
					}
					else
					{
						active = proveds.back();
						getNDTerm(active);
						NDTerm term = *cond;
						term.m_OrAssume = goals.back().m_OrAssume;
						term.m_derivation = goals.back().m_derivation;
						term.m_source |=  (LGC_SRC_OR_CONC|LGC_SRC_CONCLUSION);
						term.m_source |= LGC_SRC_DISABLE;
						proveds.pop_back();
						proveds.push_back(conditions.size());
						conditions.push_back(term);
						goals.pop_back();
						continue;
					}

				}
				else
				{
					if (goals.back().m_assume>=0 && goals.back().m_assume <  conditions.size())
					{
						disable(goals.back().m_assume);
					}
				}
				goals.pop_back();
				continue;
			}


			
			bool applied = false;
			while (eliminate() > 0)
			{ 
				applied = true;
			}

			if (applied)
			{
				continue;
			}

			if (OrEliminate())
			{
				continue;
			}

			if(introduction() > 0)
			{
				continue;
			}
			if (NegIntrodution())
			{
				continue;
			}
			if (contradiction())
			{
				continue;
			}
			
			if ((goals.back().m_proceed & LGC_PRC_CONTR)!= 0)
			{
				goals.pop_back();
				continue;
			}
			
			if (NegContradiction())
			{
				continue;
			}

			if (turnIt())
			{
				continue;
			}
			
			return 0;
		}
		
	}


#if _DEBUG
	
		knowledgeBase.print();
		PrintIndex();
		cout <<++times<<"_________________________Conditions__________________________________\n";
		for (list<NDTerm>::iterator c = conditions.begin();c!=conditions.end();++c)
		{
			if(((*c).m_source&LGC_SRC_DISABLE)!= LGC_SRC_DISABLE )
			cout<<",\t"<<knowledgeBase.GetString((*c).m_index);
			else 
			cout<<",\t*"<<knowledgeBase.GetString((*c).m_index);
		}

		cout <<"\n_______________________________Goals__________________________________\n";
		for (list<NDTerm>::iterator g = goals.begin();g!=goals.end();++g)
		{
			cout<<",\t"<<knowledgeBase.GetString((*g).m_index);
		}
		
		cout <<"\n________________________________Proved________________________________\n";
		for (list<int>::iterator p = proveds.begin();p!=proveds.end();++p)
		{
			getNDTerm(*p);
			cout<<",\t"<<knowledgeBase.GetString((*cond).m_index);
		}
		cout<<"\n______________________________________________________________________\n\n\n";

#endif
		

#if _DEBUG
	cout <<++times<<"_________________________Conditions__________________________________\n";
	int i = 0;
	for (c = conditions.begin();c!=conditions.end();++c)
	{
		cout<<(i++)<<",\t"<<"Index = "<<(*c).m_index<<"\tFirst = "<<(*c).m_first<<"\t Second = "<<(*c).m_second<<"\t Third = "<<(*c).m_third<<"\t Pending = "<<(*c).m_pendings<<"\t Assume = "<<(*c).m_assume<< endl; 
	}
	
	cout <<"\n_______________________________Goals__________________________________\n";
	for (g = goals.begin();g!=goals.end();++g)
	{
		cout<<",\t"<<knowledgeBase.GetString((*g).m_index);
	}
	
	cout <<"\n________________________________Proved________________________________\n";
	for (p = proveds.begin();p!=proveds.end();++p)
	{
		getNDTerm(*p);
		cout<<",\t"<<knowledgeBase.GetString((*cond).m_index);
	}
	cout<<"\n______________________________________________________________________\n\n\n";
#endif


	return 1;
}



int NaturalDeduction::insertCondition(NDTerm term, int&index)
{
	list<NDTerm>::iterator found;
	int outside = -1;
	for(found = conditions.begin();found!=conditions.end();++found)
	{
		++outside;
		if ((*found).m_index != LGC_ADDR_FALSE && (*found).m_index == term.m_index && ((*found).m_source & LGC_SRC_DISABLE) != LGC_SRC_DISABLE )
		{
			index = outside;
			return 0;
		}
	}
	index = conditions.size();
	conditions.push_back(term);
	return 1;
}

int NaturalDeduction::insertGoal(NDTerm term)
{
	list<NDTerm>::iterator found;
	for(found = goals.begin();found!=goals.end();++found)
	{
		if ((*found).m_index == term.m_index)
		{
			return 0;
		}
	}
	goals.push_back(term);
	return 1;
}


int NaturalDeduction::turnIt()
{
	if (!branches.empty())
	{
		int size = branches.back();
		branches.pop_back();
		for (int i = 0; i <size; i++)
		{
			getNDTerm(branches.back());
			branches.pop_back();
			(*cond).m_OrEnable = branches.back() == 1? true : false;
			branches.pop_back();
		}
		size = branches.back();
		branches.pop_back();
		while (proveds.size() > size)
		{
			proveds.pop_back();
		}
		
		size = branches.back();
		branches.pop_back();
		while (conditions.size() > size)
		{
			conditions.pop_back();
		}
		
		size = branches.back();
		branches.pop_back();
		while (goals.size() >  size)
		{
			goals.pop_back();
		}
		goals.back().m_pendings = 0;
		for (list<NDTerm>::iterator p = conditions.begin(); p!= conditions.end();++p)
		{
			(*p).m_proceed = 0x00000000;
		}

		return 1;
	}
	return 0;
}


int NaturalDeduction::getString(int index, bool isFixed, bool prefix) 
{
#if _DEBUG
	if (index == 0)
	{
		cout<<"";
	}
	_ASSERT(index >= 0 && index < conditions.size());
#endif

	string result = "";
	getNDTerm(index);
	NDTerm goal = *cond;
	if (!isFixed)
	{
		if(goal.m_line > 0)
		{
			return 0;
		}
	}
	if (goal.m_VarRef >= 0)
	{
		//string 
	}
	if (goal.m_third >= 0 )
	{
		
		getString(goal.m_third,true);

		getNDTerm(goal.m_second);
		NDTerm second = (*cond);
		getNDTerm(second.m_OrAssume);
		pLine pline2(second.m_OrAssume,lastLine,ifs++,"if   " , knowledgeBase.GetString((*cond).m_index));
		pline2.m_isPrefix = true;
		(*cond).m_line = lastLine++;
		ndAssumes.push_front(second.m_OrAssume);
		lstpLines.push_back(pline2);

		getNDTerm(goal.m_second);
		(*cond).m_assume = -1;
		getString(goal.m_second,true,true);
		ifs--;
		lstpLines.back().m_indent--;
		lstpLines.back().m_assumption = "nif  ";
		lstpLines.back().m_isPrefix = true;


		getNDTerm(goal.m_first);
		NDTerm first = (*cond);
		getNDTerm(first.m_OrAssume);
		pLine pline1(first.m_OrAssume,lastLine,ifs++,"if   " , knowledgeBase.GetString((*cond).m_index));
		pline1.m_isPrefix = true;
		(*cond).m_line = lastLine++;
		ndAssumes.push_front(first.m_OrAssume);
		lstpLines.push_back(pline1);
		getNDTerm(goal.m_first);
		(*cond).m_assume = -1;
		getString(goal.m_first,true,true);
		ifs--;
		lstpLines.back().m_indent--;
		lstpLines.back().m_assumption = "nif  ";
		lstpLines.back().m_isPrefix = true;

		pLine last(index,lastLine++,ifs,"",knowledgeBase.GetString(goal.m_index),rule2Str(goal.m_rule));
		ndAssumes.pop_front();
		
		getNDTerm(goal.m_third);
		last.m_third = (*cond).m_line;
		
		getNDTerm(goal.m_second);
		getNDTerm((*cond).m_OrAssume);
		last.m_second = (*cond).m_line;
		
		getNDTerm(goal.m_first);
		getNDTerm((*cond).m_OrAssume);
		last.m_first = (*cond).m_line;
		lstpLines.push_back(last);	

		getNDTerm(index);
		(*cond).m_line = lastLine - 1;
	
		
#if _DEBUG
		getNDTerm(index);
		cout<<"Call : "<<index << " = " <<(*cond).m_line<<endl;
#endif

		return 0;

	}
	if (goal.m_assume >= 0)
	{
		getNDTerm(goal.m_assume);
		pLine pline(goal.m_assume,lastLine,ifs++,"if   " , knowledgeBase.GetString((*cond).m_index));
		pline.m_isPrefix = true;
		ndAssumes.push_front(goal.m_assume);
		(*cond).m_line = lastLine++;
		lstpLines.push_back(pline);


		getString(goal.m_first,true,true);
		ifs--;
		lstpLines.back().m_indent--;
		lstpLines.back().m_assumption = "nif  ";
		lstpLines.back().m_isPrefix = true;
			
		pLine last(index,lastLine++,ifs,"",knowledgeBase.GetString(goal.m_index),rule2Str(goal.m_rule));
		ndAssumes.pop_front();
			
		getNDTerm(goal.m_assume);
		last.m_second = (*cond).m_line;
			
		getNDTerm(goal.m_first);
		last.m_first= (*cond).m_line;
		lstpLines.push_back(last);	
		getNDTerm(index);
		(*cond).m_line = lastLine - 1;

#if _DEBUG
		getNDTerm(index);
		cout<<"Call : "<<index << " = " <<(*cond).m_line<<endl;
#endif
		return 0;
	}

	if ( goal.m_pendings == 2 || goal.m_second >= 0)
	{
		
		getString(goal.m_second);
		
		getString(goal.m_first);
		
		if (goal.m_line <= 0)
		{
			pLine last(index,lastLine++,ifs,"",knowledgeBase.GetString(goal.m_index),rule2Str(goal.m_rule));
			getNDTerm(goal.m_second);
			last.m_second = (*cond).m_line;
			getNDTerm(goal.m_first);
			last.m_first = (*cond).m_line;
			if (!ndAssumes.empty())
			{
				int locate = lastLine - 1;
				int indent = 0;
				if ( ((goal.m_source & LGC_SRC_ASSUME) != LGC_SRC_ASSUME) && goal.m_index != LGC_ADDR_FALSE )
				{
					list<int>::iterator p =  ndAssumes.begin();
					for (; p != ndAssumes.end(); ++p)
					{
						
						if (isDerived(index,(*p)))
						{
							break;
						}
						else
						{
							indent++;
						}
					}
					if (p == ndAssumes.begin())
					{
						lstpLines.push_back(last);
						getNDTerm(index);
						(*cond).m_line = locate;
					}
					else
					{
						if(p== ndAssumes.end())
						--p;
						getNDTerm((*p));
						locate = (*cond).m_line ;
						last.m_indent = last.m_indent - indent;
						last.m_line = locate;
						while(locate >= 1)
						{
							if (lstpLines[locate - 1].m_isFixed)
								locate--;
							else
								break;
						}
						if (locate == 0)
						{
							locate = 1;
						}
						getNDTerm(index);
						(*cond).m_line = locate;
						vector<pLine>::iterator ip = lstpLines.begin();
						for (int i = 1; i < locate; i++)
						{
							++ip;
						}
						ip = lstpLines.insert(ip,last);
						++ip;
						for (;ip != lstpLines.end(); ++ip)
						{
							(*ip).m_line++;
							if ((*ip).m_first >= locate)
							{
								(*ip).m_first++;
							}
							if ((*ip).m_second >= locate )
							{
								(*ip).m_second++;
							}
							getNDTerm((*ip).m_index);
							(*cond).m_line++;
						}
					}
					dprintLines();
				}
				else
				{
					lstpLines.push_back(last);
					getNDTerm(index);
					(*cond).m_line = lastLine - 1;
				}
			
				
			}
			else
			{
				last.m_isFixed = isFixed;
				lstpLines.push_back(last);
				getNDTerm(index);
				(*cond).m_line = lastLine - 1;
			}

			if (last.m_indent == ifs)
			{
				isFixed = false;
			}

		}
		if (isFixed)
		{

			if (lstpLines.back().m_index == index && (!prefix) )
			{
				lstpLines.back().m_isFixed = true;
			
			}
			else
			{
				pLine last(index,lastLine++,ifs,"",knowledgeBase.GetString(goal.m_index), rule2Str(LGC_RULE_ID) );
				getNDTerm(index);
				last.m_first = (*cond).m_line;
				last.m_isFixed = true;
				lstpLines.push_back(last);
			}
			
		}

#if _DEBUG
		getNDTerm(index);
		cout<<"Call : "<<index << " = " <<(*cond).m_line<<endl;
#endif
		return 0;
	}

	if(goal.m_pendings == 1 || goal.m_first >= 0)
	{
		
		getString(goal.m_first);
		if (goal.m_line <= 0)
		{
			pLine last(index,lastLine++,ifs,"",knowledgeBase.GetString(goal.m_index),rule2Str(goal.m_rule));
			getNDTerm(goal.m_first);
			last.m_first = (*cond).m_line;
			if (!ndAssumes.empty())
			{
				int locate = lastLine - 1;
				int indent = 0;
				if ( ((goal.m_source & LGC_SRC_ASSUME) != LGC_SRC_ASSUME) && goal.m_index != LGC_ADDR_FALSE )
				{
					list<int>::iterator p =  ndAssumes.begin();
					for (; p != ndAssumes.end(); ++p)
					{
						
						if (isDerived(index,(*p)))
						{
							break;
						}
						else
						{
							indent++;
						}
					}
					if (p == ndAssumes.begin())
					{
						lstpLines.push_back(last);
						getNDTerm(index);
						(*cond).m_line = locate;
					}
					else
					{
						if(p== ndAssumes.end())
							--p;
						getNDTerm((*p));
						locate = (*cond).m_line ;
						last.m_indent = last.m_indent - indent;
						last.m_line = locate;
						while(locate >= 1)
						{
							if (lstpLines[locate - 1].m_isFixed)
								locate--;
							else
								break;
						}
						if (locate == 0)
						{
							locate = 1;
						}
						getNDTerm(index);
						(*cond).m_line = locate;
						vector<pLine>::iterator ip = lstpLines.begin();
						for (int i = 1; i < locate; i++)
						{
							++ip;
						}
						ip = lstpLines.insert(ip,last);
						++ip;
						for (;ip != lstpLines.end(); ++ip)
						{
							(*ip).m_line++;
							if ((*ip).m_first >= locate)
							{
								(*ip).m_first++;
							}
							if ((*ip).m_second >= locate )
							{
								(*ip).m_second++;
							}
							getNDTerm((*ip).m_index);
							(*cond).m_line++;
						}
					}
					dprintLines();
				}
				else
				{
					lstpLines.push_back(last);
					getNDTerm(index);
					(*cond).m_line = lastLine - 1;
				}
			
				
			}
			else
			{
				last.m_isFixed = isFixed;
				lstpLines.push_back(last);
				getNDTerm(index);
				(*cond).m_line = lastLine - 1;
			}
			
			if (last.m_indent == ifs)
			{
				isFixed = false;
			}

			
		}
		if (isFixed)
		{
			if (lstpLines.back().m_index == index && (!prefix) )
			{
				lstpLines.back().m_isFixed = true;
				
			}
			else
			{
				pLine last(index,lastLine++,ifs,"",knowledgeBase.GetString(goal.m_index), rule2Str(LGC_RULE_ID) );
				getNDTerm(index);
				last.m_first = (*cond).m_line;
				last.m_isFixed = true;
				lstpLines.push_back(last);
			}
		}

#if _DEBUG
		getNDTerm(index);
		cout<<"Call : "<<index << " = " <<(*cond).m_line<<endl;
#endif
		return 0;

	}
	


	if (goal.m_line <= 0)
	{
		pLine last(index,lastLine++,ifs,"",knowledgeBase.GetString(goal.m_index),rule2Str(goal.m_rule));
		if (!ndAssumes.empty())
		{
			int locate = lastLine - 1;
			int indent = 0;
			if ( ((goal.m_source & LGC_SRC_ASSUME) != LGC_SRC_ASSUME) && goal.m_index != LGC_ADDR_FALSE )
			{
				list<int>::iterator p =  ndAssumes.begin();
				for (; p != ndAssumes.end(); ++p)
				{
					
					if (isDerived(index,(*p)))
					{
						break;
					}
					else
					{
						indent++;
					}
				}
				if (p == ndAssumes.begin())
				{
					lstpLines.push_back(last);
					getNDTerm(index);
					(*cond).m_line = locate;
				}
				else
				{
					if(p== ndAssumes.end())
						--p;
					getNDTerm((*p));
					locate = (*cond).m_line ;
					last.m_indent = last.m_indent - indent;
					last.m_line = locate;
					while(locate >= 1)
					{
						if (lstpLines[locate - 1].m_isFixed)
							locate--;
						else
							break;
					}
					if (locate == 0)
					{
						locate = 1;
					}
					getNDTerm(index);
					(*cond).m_line = locate;
					vector<pLine>::iterator ip = lstpLines.begin();
					for (int i = 1; i < locate; i++)
					{
						++ip;
					}
					ip = lstpLines.insert(ip,last);
					++ip;
					for (;ip != lstpLines.end(); ++ip)
					{
						(*ip).m_line++;
						if ((*ip).m_first >= locate)
						{
							(*ip).m_first++;
						}
						if ((*ip).m_second >= locate )
						{
							(*ip).m_second++;
						}
						getNDTerm((*ip).m_index);
						(*cond).m_line++;
					}
				}
				dprintLines();
			}
			else
			{
				lstpLines.push_back(last);
				getNDTerm(index);
				(*cond).m_line = lastLine - 1;
			}
			
		}
		else
		{
			last.m_isFixed = isFixed;
			lstpLines.push_back(last);
			getNDTerm(index);
			(*cond).m_line = lastLine - 1;
		}
		
		if (last.m_indent == ifs )
		{
			isFixed = false;
		}

		
	}
	if (isFixed)
	{
		if (lstpLines.back().m_index == index && (!prefix) )
		{
			lstpLines.back().m_isFixed = true;
			
		}
		else
		{
			pLine last(index,lastLine++,ifs,"",knowledgeBase.GetString(goal.m_index), rule2Str(LGC_RULE_ID) );
			getNDTerm(index);
			last.m_first = (*cond).m_line;
			last.m_isFixed = true;
			lstpLines.push_back(last);
		}
	}

#if _DEBUG
	getNDTerm(index);
	cout<<"Call : "<<index << " = " <<(*cond).m_line<<endl;
#endif
	return 0;	
}


bool NaturalDeduction::isReached(int &active)
{
	int subgoal = goals.back().m_index;
	int outside = -1;
	active = -1;
	int length = 0x7FFFFFFF;
	bool result = false;
	for (list<NDTerm>::const_iterator p = conditions.begin(); p!= conditions.end();++p)
	{
		++outside;
		if(((*p).m_source & LGC_SRC_DISABLE) == LGC_SRC_DISABLE)
		{
			continue;
		}
		if (isCompatible((*p).m_index,subgoal))
		{
			if (length > (*p).m_path)
			{
				active = outside;
				length = (*p).m_path;
				result = true;
			}
			
		}
	}
	
	return result;
}


bool NaturalDeduction::isReached(int &active, int& negative)
{
	int outside = -1;
	active = -1;
	negative = -1;
	int length = 0x7FFFFFFF;
	bool result = false;
	for (list<NDTerm>::const_iterator p = conditions.begin();p!=conditions.end();++p)
	{
		++outside;
		if(((*p).m_source & LGC_SRC_DISABLE) == LGC_SRC_DISABLE)
		{
			continue;
		}
		int inside = -1;
		for (list<NDTerm>::const_iterator q = conditions.begin();q!=conditions.end();++q)
		{
			++inside;
			if(((*q).m_source & LGC_SRC_DISABLE) == LGC_SRC_DISABLE)
			{
				continue;
			}
			if (isComplement((*p).m_index,(*q).m_index))
			{
				if (length > (*p).m_path + (*q).m_path)
				{
					active= outside;
					negative = inside;
					length = (*p).m_path + (*q).m_path;
					result = true;
				}
			}
		}
	}
	return result;
}

int NaturalDeduction::disable(int assume)
{


	if (assume < 0 || assume >=  conditions.size())
	{
#if _DEBUG
		cout<<"error = "<< assume<<endl;;
#endif
	
		return 0;
	}
	getNDTerm(assume);
	if (((*cond).m_source & LGC_SRC_ASSUME) != LGC_SRC_ASSUME)
	{
		return 0;
	}

	list<int>parents;
	list<int>passed;
	getNDTerm(assume);
	(*cond).m_source |= LGC_SRC_DISABLE;
	parents.push_back(assume);
	while (!parents.empty())
	{
		int last = parents.back();
		parents.pop_back();
		passed.push_back(last);
		int index = assume - 1;
		getNDTerm(assume);
		list<NDTerm>::iterator p = cond;
		for (; p != conditions.end();++p)
		{
			++index;
			if (((*p).m_first == last) || ((*p).m_second == last) ||((*p).m_assume == last))
			{
				if (find(passed.begin(),passed.end(),index)==passed.end())
				{
					if ((*p).m_rule != LGC_I_MAP || (*p).m_assume != assume)
					{
						parents.push_back(index);
						(*p).m_source |= LGC_SRC_DISABLE;
					}
					
				}
				if ((*p).m_derivation >= 0)
				{
					getNDTerm((*p).m_derivation);
					(*cond).m_proceed = 0x00000000;
				}
				
			}
			else if((*p).m_rule == LGC_RULE_ID && (*p).m_first < assume)
			{
				(*p).m_source |= LGC_SRC_DISABLE;
				getNDTerm((*p).m_first);
				if (((*cond).m_source & LGC_SRC_DISABLE) == LGC_SRC_DISABLE)
				{
					(*cond).m_source = 0x00000000;
					 parents.push_back(index);
				}
			}
		
		}
	}
	return 0;
}


int NaturalDeduction::getNDTerm(int index)
{

#if _DEBUG
	_ASSERT(index >= 0 && index < conditions.size());
#endif
	if ( index < 0 || index >= conditions.size())
	{
		cout<<"Error while get NDTerm"<<endl;
		cond = conditions.end();
		return 0;
	}
	cond = conditions.begin();
	for (int i = 0; i < index;i++)
	{
		++cond;
	}
	return 0;
}


string NaturalDeduction::Result()
{	
	cout<<proveds.back()<<"----------\n";
	getString(proveds.back());
	for (int i = 1;i < lstpLines.size() ; i++)
	{
		if (lstpLines[i].m_rule == rule2Str(LGC_RULE_ID))
		{
			int orginal = lstpLines[i].m_first;
			int current_ifs = lstpLines[i].m_indent;
			for (int j = i + 1; j < lstpLines.size(); j++)
			{
			
				if (lstpLines[j].m_first == orginal)
				{
					lstpLines[j].m_first = lstpLines[i].m_line;
				}
				if (lstpLines[j].m_second == orginal)
				{
					lstpLines[j].m_second = lstpLines[i].m_line;
				}
				if (lstpLines[j].m_third == orginal)
				{
					lstpLines[j].m_third = lstpLines[i].m_line;
				}	
				if (lstpLines[j].m_indent < current_ifs)
				{
					break;
				}
			}
		}
	}
	
	string s = "";
	int max = 0;
	for (i = 0; i < lstpLines.size(); i++)
 	{
		s = pLine2Str(lstpLines[i]) +"\n";
		if (max < s.length())
		{
			max =  s.length();
		}
 	}
	s = "";
#if _DEBUG
	s = "\n\n Here a result:\n\n";
#endif
	
	for (i = 0; i < lstpLines.size(); i++)
	{
		s += pLine2Str(lstpLines[i],max) +"\n";
 	}
	
	return s;
}

string NaturalDeduction::rule2Str(int rule)
{
	string result = "";
	switch (rule)
	{
	case LGC_RULE_PREMISE:
		result = "tien de";
		break;
	case LGC_RULE_ID:
		result = "id";
		break;
	case LGC_E_AND_1:
		result = "&e1";
		break;
	case LGC_E_AND_2:
		result = "&e2";
		break;
	case LGC_E_OR:
		result = "|e";
		break;
//	case LGC_E_OR_2:
		//result = "|e2";
		break;
	case LGC_E_MAP:
		result = "->e";
		break;
	case LGC_E_DNEG:
		result = "!!";
		break;
	case LGC_E_ALL:
		result = "Ve";
		break;
	case LGC_E_EXISTS:
		result = "-]e";
		break;
	case LGC_E_NOT:
		result = "!e";
		break;
	case LGC_I_AND:
		result = "&i";
		break;
	case LGC_I_OR_1:
		result = "|i1";
		break;
	case LGC_I_OR_2:
		result = "|i2";
		break;
	case LGC_I_MAP:
		result = "->i";
		break;
	case LGC_I_NOT:
		result = "!i";
		break;
	case LGC_I_ALL:
		result = "Vi";
		break;
	case LGC_I_EXISTS:
		result = "-]i";
		break;
	case LGC_DEMOR_AND:
		result = "Dem";
		break;
	case LGC_DEMOR_OR:
		result = "Dem";
		break;
	default:
		break;

	}
	//return  ToStringX(result + " ",4);
	return  ToString(result + "\t");
}

int NaturalDeduction::isDerived(int child, int parent)
{
	if (child < 0  || child >= conditions.size())
	{
		return 0;
	}

	if (parent < 0  || parent >= conditions.size())
	{
		return 0;
	}

	if(child == parent)return 1;
	list<int>parents;
	list<int>passed;
	parents.push_back(parent);
	while (!parents.empty())
	{
		int last = parents.back();
		passed.push_back(last);
		parents.pop_back();
		int index = parent;
		getNDTerm(index + 1);
		list<NDTerm>::iterator p = cond;
		for (; p != conditions.end();++p)
		{
			++index;
			if (((*p).m_first == last) || ((*p).m_second == last))
			{
				{
					if (index == child)
					{
						return 1;
					}
					if (find(passed.begin(),passed.end(),index)==passed.end())
					{
						parents.push_back(index);
					}
					
				}
			}
		}
	}
	return 0;
}

int NaturalDeduction::OrEliminate()
{
	
	list<NDTerm>::iterator p ;
	

	int outside = -1;
	for (p = conditions.begin();p!=conditions.end();++p)
	{
		outside++;
		if ((*p).m_source & LGC_SRC_DISABLE == LGC_SRC_DISABLE)
		{
			continue;
		}
		NDTerm ndTerm;
		int main = (*p).m_index;
		while (knowledgeBase.clauses[main].m_kind == LGC_REF)
		{
			main = knowledgeBase.clauses[main].m_ref;
		}
		
		if (knowledgeBase.clauses[main].m_info == 0)
		{
			
			if (knowledgeBase.clauses[main].m_kind == LGC_TERM_FUNC)
			{
				switch (knowledgeBase.clauses[main].m_ref)
				{
				case LGC_ADDR_OR:
					if ((*p).m_OrEnable)
					{
						(*p).m_OrEnable = false;
						goals.back().m_source |= LGC_SRC_OR_GOAL;
						goals.back().m_pendings = 2;
						goals.back().m_third = outside;
						ndTerm.m_source = LGC_SRC_OR_SUB_2;
						ndTerm.m_derivation = outside;
						ndTerm.m_index = goals.back().m_index;
						goals.push_back(ndTerm);
						ndTerm.m_source = LGC_SRC_OR_SUB_1;
						goals.push_back(ndTerm);
						return 1;
					}	
					break;
				}
			}
		}
	}
	return 0;
}

int NaturalDeduction::NegIntrodution()
{
	int subgoal = goals.back().m_index;
	int assume = -1;
	while (knowledgeBase.clauses[subgoal].m_kind == LGC_REF)
	{
		subgoal = knowledgeBase.clauses[subgoal].m_ref;
	}

	int arg1 = 0;
	int status = goals.back().m_proceed;
	NDTerm t;
	int added = 0;
	if(knowledgeBase.clauses[subgoal].m_info == 0)
	{
		if (knowledgeBase.clauses[subgoal].m_kind == LGC_TERM_FUNC)
		{
			switch (knowledgeBase.clauses[subgoal].m_ref)
			{
			case LGC_ADDR_NOT:
				if ((status & LGC_PRC_I_NOT) !=LGC_PRC_I_NOT)
				{
					arg1 = subgoal + 1;
					while (knowledgeBase.clauses[arg1].m_kind == LGC_REF)
					{
						arg1 = knowledgeBase.clauses[arg1].m_ref;
					}
					t.m_index = arg1;
					t.m_source |= LGC_SRC_ASSUME;
					insertCondition(t,assume);
					goals.back().m_pendings = 1;
					goals.back().m_rule = LGC_I_NOT;
					goals.back().m_proceed |= LGC_PRC_I_NOT;
					goals.back().m_assume = assume;
					goals.back().m_derivation = assume;
					NDTerm conclusion(LGC_ADDR_FALSE);
					conclusion.m_source |= LGC_SRC_CONCLUSION;
					goals.push_back(NDTerm(conclusion));
					return 1;
				}
				break;
			default:
				if ((status & LGC_PRC_I_NOT) !=LGC_PRC_I_NOT)
				{
					knowledgeBase.clauses.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT));
					knowledgeBase.clauses.push_back(Term(LGC_REF,subgoal));
					arg1 = knowledgeBase.clauses.size() - 2;
					t.m_index = arg1;
					t.m_proceed |= LGC_PRC_C_NOT;
					t.m_source = LGC_SRC_ASSUME;
					added += insertCondition(t,assume);
					goals.back().m_pendings = 1;
					goals.back().m_rule = LGC_I_NOT;
					goals.back().m_proceed |= LGC_PRC_I_NOT;
					goals.back().m_assume = assume;
					goals.back().m_derivation = assume;
					NDTerm conclusion(LGC_ADDR_FALSE);
					conclusion.m_source = LGC_SRC_CONCLUSION;
					goals.push_back(NDTerm(conclusion));	
				}
				break;
			}
		}
		else if(subgoal!=LGC_ADDR_FALSE)
		{
			if ((status & LGC_PRC_I_NOT) !=LGC_PRC_I_NOT)
			{
				knowledgeBase.clauses.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT));
				knowledgeBase.clauses.push_back(Term(LGC_REF,subgoal));
				arg1 = knowledgeBase.clauses.size() - 2;
				t.m_index = arg1;
				t.m_proceed |= LGC_PRC_C_NOT;
				t.m_source = LGC_SRC_ASSUME;
				added += insertCondition(t,assume);
				goals.back().m_pendings = 1;
				goals.back().m_rule = LGC_I_NOT;
				goals.back().m_proceed |= LGC_PRC_I_NOT;
				goals.back().m_assume = assume;
				goals.back().m_derivation = assume;
				NDTerm conclusion(LGC_ADDR_FALSE);
				conclusion.m_source = LGC_SRC_CONCLUSION;
				goals.push_back(NDTerm(conclusion));	
			}
		}
	}
			
	return added;
}

int NaturalDeduction::NegContradiction()
{
	list<NDTerm>::iterator p;
	int outside = -1;
	for (p = conditions.begin();p!=conditions.end();++p)
	{
		outside++;
		if ((*p).m_source & LGC_SRC_DISABLE == LGC_SRC_DISABLE)
		{
			continue;
		}
		int source = (*p).m_index;
		while (knowledgeBase.clauses[source].m_kind == LGC_REF)
		{
			source = knowledgeBase.clauses[source].m_ref;
		}
		int arg1 = source + 1;
		NDTerm t;
		if (knowledgeBase.clauses[source].m_info == 0 && knowledgeBase.clauses[source].m_kind == LGC_TERM_FUNC)
		{
			switch (knowledgeBase.clauses[source].m_ref)
			{

			case LGC_ADDR_NOT:
				if (((*p).m_proceed & LGC_PRC_C_NOT)!=LGC_PRC_C_NOT)
				{
					(*p).m_proceed |=LGC_PRC_C_NOT;
					while (knowledgeBase.clauses[arg1].m_kind == LGC_REF)
					{
						arg1 = knowledgeBase.clauses[arg1].m_ref;
					}
					t.m_index = arg1;
					t.m_proceed |= LGC_PRC_C_NOT;
					t.m_source	= LGC_SRC_HOPING;
					t.m_assume = outside;
					t.m_derivation = outside;
					return insertGoal(t);
					
				}
				break; 
			}
		}

	}
	return 0;
}

int NaturalDeduction::debug(int times)
{
//	return 0;
#if _DEBUG
	int i = 0;
	//database.print();
	cout <<++times<<"_________________________Conditions__________________________________\n";
	for (list<NDTerm>::iterator c = conditions.begin();c!=conditions.end();++c)
	{
		if(((*c).m_source&LGC_SRC_DISABLE)!= LGC_SRC_DISABLE )
			cout<<"\t"<<i++<<"."<<knowledgeBase.GetString((*c).m_index)<<(*c).m_line;
		else 
			cout<<"\t"<<i++<<"."<<knowledgeBase.GetString((*c).m_index)<<(*c).m_line;
		//cout<<"\t"<<"Index = "<<(*c).m_index<<"\tFirst = "<<(*c).m_first<<"\t Second = "<<(*c).m_second<<"\t Third = "<<(*c).m_third<<"\t Pending = "<<(*c).m_pendings<<"\t Assume = "<<(*c).m_assume<< endl; 
	}
	
	cout <<"\n_______________________________Goals__________________________________\n";
	for (list<NDTerm>::iterator g = goals.begin();g!=goals.end();++g)
	{
		cout<<",\t"<<knowledgeBase.GetString((*g).m_index);
	}
	
	cout <<"\n________________________________Proved________________________________\n";
	for (list<int>::iterator p = proveds.begin();p!=proveds.end();++p)
	{
		//getNDTerm(*p);
		//cout<<",\t"<<database.GetString((*cond).m_index);
		cout<<",\t"<<(*p);
	}
	cout<<"\n______________________________________________________________________\n\n\n";
	if (times == 10)
	{
		int dummy = 0;
	}
#endif
	return 0;
}

int NaturalDeduction::insertLEMs()
{
	if (isInsert)
	{
		return 0;
	}
	vector<Term>::const_iterator proposition = knowledgeBase.variables.begin(); 
	int added = 0;
	int prop = -1;
	for (;proposition != knowledgeBase.variables.end(); ++proposition)
	{
		prop++;
		if ((*proposition).m_kind == LGC_TERM_PROP && knowledgeBase.names.GetString((*proposition).m_ref) != "*1")
		{
			knowledgeBase.clauses.push_back(Term(LGC_TERM_PROP,prop));
			knowledgeBase.clauses.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT));
			knowledgeBase.clauses.push_back(Term(LGC_REF,knowledgeBase.clauses.size() - 2));
			knowledgeBase.clauses.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_OR));
			knowledgeBase.clauses.push_back(Term(LGC_REF,knowledgeBase.clauses.size() - 4));
			knowledgeBase.clauses.push_back(Term(LGC_REF,knowledgeBase.clauses.size() - 4));
			NDTerm lem(knowledgeBase.clauses.size()-3,LGC_RULE_LEM);
			lem.m_path = 1;
			lem.m_source |= LGC_SRC_LEM;
			conditions.push_back(lem);
			added++;
		}
	}
	isInsert = true;
	return added;
}

int NaturalDeduction::getFarest(int& first, int& second, int sub1, int sub2)
{
	if (first < 0 || first >=  conditions.size() || second < 0 || second >=  conditions.size()|| sub1 < 0 || sub1 >=  conditions.size()|| sub2 < 0 || sub2 >=  conditions.size())
	{
		return -1;
	}
	getNDTerm(first);
	NDTerm t1 = (*cond);
	getNDTerm(second);
	NDTerm t2 = (*cond);
	if (!isCompatible(t1.m_index,t2.m_index))
	{
		return -1;
	}
	if (t1.m_rule != t2.m_rule)
	{
		return -1;
	}
	int f_1 = t1.m_first;
	int f_2 = t1.m_second;
	int s_1 = t2.m_first;
	int s_2 = t2.m_second;
	bool called = false;
	if (isDerived(f_1,sub1))
	{
		getFarest(f_1,s_1,sub1,sub2);
		called = true;
	}
	if (isDerived(f_2,sub1))
	{
		getFarest(f_2,s_2,sub1,sub2);
		called = true;
	}
	if (called && f_1 >= 0 && s_1 >= 0)
	{
		first = f_1;
		second = s_1;
	}
	if (called && f_2 >= 0 && s_2 >= 0)
	{
		getNDTerm(first);
		t1 = *cond;
		getNDTerm(f_2);
		t2 = *cond;
		if (t1.m_path > t2.m_path)
		{
			first = f_1;
			second = s_1;
		}
		
	}
	return 1;
}

#if _DEBUG
void NaturalDeduction::dprintLines()
{
	return;
	cout<<"Line of: ";
	for (vector<pLine>::const_iterator p = lstpLines.begin();p!=lstpLines.end();++p)
	{
		cout<<ToString(pLine2Str((*p)))<<endl;
	}
}


void NaturalDeduction::PrintIndex()
{
	//database.print();
	cout <<"_________________________Conditions__________________________________\n";
	int i = 0;
	for (list<NDTerm>::iterator c = conditions.begin();c!=conditions.end();++c)
	{
		cout<<(i++)<<",\t"<<"Index = "<<(*c).m_index<<"\tFirst = "<<(*c).m_first<<"\t Second = "<<(*c).m_second<<"\t Third = "<<(*c).m_third<<"\t Pending = "<<(*c).m_pendings<<"\t OrAssume = "<<(*c).m_OrAssume<< endl; 
	}
	
}
#endif


int NaturalDeduction::unify(NDWAM x, NDWAM y, list<NDWAM>& theta)
{
	
	while (x.Kind() == LGC_REF)
	{
		x = ndWam(x.Ref());
	}

	while (y.Kind() == LGC_REF)
	{
		y = ndWam(x.Ref());
	}

	if (theta.front().IsNull())
	{
		return 1;
	}

	else if (x.Kind() == x.Kind() && x.Kind() != LGC_TERM_FUNC && x.Ref() == y.Ref())
	{
		return 0;
	}
	else if (x.Kind() == x.Kind() && x.Kind() != LGC_TERM_FUNC && x.Ref() != y.Ref())
	{
		theta.clear();
		theta.push_back(NDWAM());
		return 1;
	}
	else if (x.Kind() == LGC_TERM_VAR)
	{
		return unifyVar(x,y,theta);
	}
	else if (y.Kind() == LGC_TERM_VAR)
	{
		return unifyVar(y,x,theta);
	}
	else if (x.Kind() == LGC_TERM_FUNC && y.Kind() == LGC_TERM_FUNC)
	{
		int funcX = x.Ref();
		if (funcX != y.Ref())
		{
			theta.clear();
			theta.push_back(NDWAM());
			return 1;
		}

		funcX = knowledgeBase.clauses[funcX].m_info;
		list<NDWAM>argX;
		list<NDWAM>argY;
		for (int i = 1; i <= funcX; i++ )
		{
			argX.push_back(ndWam(x.Index() + i));
			argY.push_back(ndWam(y.Index() + i));
		}
		return unify(argX,argY,theta);
	}
	theta.clear();
	theta.push_back(NDWAM());
	return 1;
}


int NaturalDeduction:: unify(list<NDWAM> x, list<NDWAM> y, list<NDWAM>& theta)
{
	if (theta.front().IsNull())
	{
		theta.clear();
		theta.push_back(NDWAM());
		return 1;
	}
	else if (x.size() != y.size())
	{
		theta.clear();
		theta.push_back(NDWAM());
		return 0;
	}
	else if (x.size() == 0 && y.size() == 0)
	{
		return 0;
	}
	else if (x.size() == 1 && y.size() == 1)
	{
		return unify(x.front(),y.front(),theta);
	}
	else
	{
		NDWAM x1 = x.front();
		NDWAM y1 = y.front();
		x.pop_front();
		y.pop_front();
		unify(x1,y1,theta);
		return unify(x,y,theta);
	}
	theta.clear();
	theta.push_back(NDWAM());
	return 1;
}

int NaturalDeduction::unifyVar(NDWAM var, NDWAM y, list<NDWAM>& theta)
{

	if (theta.front().IsNull())
	{
		theta.clear();
		theta.push_back(NDWAM());
		return 1;
	}
	list<NDWAM>::iterator p = find(theta.begin(),theta.end(),var);
	if(p != theta.end())
	{
		++p;
		return unify((*p),y,theta);
	}
	p = find(theta.begin(),theta.end(),y);
	if (p != theta.end())
	{
		--p;
		return unify(var,(*p),theta);
	}
	else if(occurCheck(theta,var,y))
	{
		theta.clear();
		theta.push_back(NDWAM());
		return 1;
	}
	else
	{
		theta.push_back(var);
		theta.push_back(y);
	}
	return 1;
}

bool NaturalDeduction::occurCheck(list<NDWAM>theta,NDWAM var, NDWAM node )const
{
	if (node.Kind()==LGC_TERM_FUNC)
	{
		list<int> vars;
		knowledgeBase.ClauseVars(node.Index(),vars);
		if ((!vars.empty()) && find(vars.begin(),vars.end(),var.Index()) != vars.end())
		{
			return true;
		}
		list<int> subVars;
		for (list<NDWAM>::iterator p = theta.begin(); p!= theta.end();)
		{
			subVars.clear();
			if ((*p).Kind() == LGC_TERM_FUNC)
			{
				int index = (*p).Index();	
				++p;
				if (!vars.empty() && find(vars.begin(),vars.end(),(*p).Index()) != vars.end())
				{
					knowledgeBase.ClauseVars(index,subVars);
					if (!subVars.empty() && find(subVars.begin(),subVars.end(),var.Index()) != subVars.end())
					{
						return true;
					}
				}
			}
		}
	}
	return false;
}

NDWAM NaturalDeduction::ndWam(int index)
{
	
	while (knowledgeBase.clauses[index].m_kind == LGC_REF)
	{
		index = knowledgeBase.clauses[index].m_kind;
	}
	
	switch (knowledgeBase.clauses[index].m_kind)
	{
		
	case LGC_TERM_FUNC:
		return NDWAM(index,knowledgeBase.clauses[index]);
		
		
	case LGC_FUN_DEF:
		return NDWAM(index,knowledgeBase.clauses[index]);
		
		
	case LGC_TERM_VAR:
		index = knowledgeBase.clauses[index].m_ref;
		return NDWAM(index,knowledgeBase.variables[index]);
		
		
	case LGC_TERM_CONST:
		index = knowledgeBase.clauses[index].m_ref;
		return NDWAM(index,knowledgeBase.variables[index]);
		
		
	case LGC_TERM_PROP:
		index = knowledgeBase.clauses[index].m_ref;
		return NDWAM(index,knowledgeBase.variables[index]);
	}
	return NDWAM();
}


int NaturalDeduction::disableVar(int varRef)
{
	for (list<NDTerm>::iterator p = conditions.begin(); p!= conditions.end(); ++p)
	{
		if (knowledgeBase.clauses[(*p).m_index].m_kind == LGC_TERM_FUNC)
		{
			list<int>funVars;
			knowledgeBase.ClauseVars((*p).m_index,funVars);
			if (!funVars.empty() && find(funVars.begin(),funVars.end(),varRef)!=funVars.end())
			{
				(*p).m_source |= LGC_SRC_DISABLE;
			}
		}
	}
	return 0;
}
