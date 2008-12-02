// NaturalDeduction.cpp: implementation of the NaturalDeduction class.
//
//////////////////////////////////////////////////////////////////////

#include "NaturalDeduction.h"

//////////////////////////////////////////////////////////////////////
// Construction/Destruction
//////////////////////////////////////////////////////////////////////

NaturalDeduction::NaturalDeduction(TermVector t)
{
	database = t;
	list<int>::const_iterator p = t.conditions.begin();
	for (;p!=t.conditions.end();++p)
	{
		conditions.push_back(NDTerm(*p));
	}
	for (p = t.goals.begin();p!=t.goals.end();++p)
	{
		goals.push_back(NDTerm(*p));
	}
}



bool NaturalDeduction::isCompatible(int father, int son)const
{

	if (database.functions[father].m_kind == LGC_REF)
	{
		return isCompatible(database.functions[father].m_ref,son);
	}

	if (database.functions[son].m_kind == LGC_REF)
	{
		return isCompatible(father,database.functions[son].m_ref);
	}

	if (database.functions[son].m_kind == database.functions[father].m_kind)
	{
		int r1 = database.functions[father].m_ref;
		int r2 = database.functions[son].m_ref;
		switch (database.functions[father].m_kind)
		{
		case LGC_TERM_PROP:
			return r1 == r2;
		case LGC_TERM_CONST:
			return r1 == r2 && database.variables[r1].m_info >= database.variables[r2].m_info;
		case LGC_TERM_FUNC:
			if(r1 == r2)
			{
				if (database.functions[son].m_info > 0  || database.functions[father].m_info > 0)
				{
					return false;
				} 
				if (r1!=r2)
				{
					return false;
				}
				int args = database.functions[r1].m_info;
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

int NaturalDeduction::Eliminate()
{

	list<NDTerm>::iterator p ;
	
	int added = 0;
	int arg1 = 0;
	int arg2 = 0;
	NDTerm ndTerm;

	for (p = conditions.begin();p!=conditions.end();++p)
	{
		int main = (*p).m_index;
		while (database.functions[main].m_kind == LGC_REF)
		{
			main = database.functions[main].m_ref;
		}

		if (database.functions[main].m_info == 0)
		{

			if (database.functions[main].m_kind == LGC_TERM_FUNC)
			{
				switch (database.functions[main].m_ref)
				{

				case LGC_ADDR_NOT:
					arg1 = main + 1;
					while (database.functions[arg1].m_kind == LGC_REF)
					{
						arg1 = database.functions[arg1].m_ref;
					}
					
					if (database.functions[arg1].m_kind == LGC_TERM_FUNC && database.functions[arg1].m_ref == LGC_ADDR_NOT)
					{
						if ((*p).m_status & LGC_FLAG_E_NOT == 0)
						{
							(*p).m_status |= LGC_FLAG_E_NOT;
							arg2 = arg1 + 1;
							while (database.functions[arg2].m_kind == LGC_REF)
							{
								arg2 = database.functions[arg2].m_ref;
							}
							ndTerm.m_index = arg2;
							ndTerm.m_rule = LGC_E_DNEG;
							ndTerm.m_path = (*p).m_path + 1;
							ndTerm.m_first = (*p).m_index;
							added += InsertTerm(ndTerm);
							
						}
					}
					break;
	
				case LGC_ADDR_AND:
					if (((*p).m_status & LGC_FLAG_E_AND) == 0)
					{
						(*p).m_status |= LGC_FLAG_E_AND;
						int arg1 = main + 1;
						while (database.functions[arg1].m_kind == LGC_REF)
						{
							arg1 = database.functions[arg1].m_ref;
						}

						ndTerm.m_index = arg1;
						ndTerm.m_rule = LGC_E_AND_1;
						ndTerm.m_first = (*p).m_index;
						ndTerm.m_path = (*p).m_path + 1;
						added += InsertTerm(ndTerm);

						arg2 = main + 2;
						while (database.functions[arg2].m_kind == LGC_REF)
						{
							arg2 = database.functions[arg2].m_ref;
						}

						ndTerm.m_index = arg2;
						ndTerm.m_rule = LGC_E_AND_2;
						added += InsertTerm(ndTerm);

					}
					break;


				case LGC_ADDR_OR:		
					// A v B , not(A) -> B

					if ( ((*p).m_status & LGC_FLAG_E_OR1) == 0)
					{
						arg1 = main + 1;
						arg2 = main + 2;
						while (database.functions[arg1].m_kind == LGC_REF)
						{
							arg1 = database.functions[arg1].m_ref;
						}
						
						list<NDTerm>::const_iterator leftOp = conditions.begin();
						for (;leftOp!=conditions.end();++leftOp)
						{
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
								ndTerm.m_first = (*p).m_index;
								ndTerm.m_second = (*leftOp).m_index;
								ndTerm.m_path = (*p).m_path < (*leftOp).m_path ? (*p).m_path + 1 : (*leftOp).m_path + 1; 
								ndTerm.m_rule = LGC_E_OR_1;
								added += InsertTerm(ndTerm);
								(*p).m_status |= LGC_FLAG_E_OR1;
							}
							
						}
						
					}

					if (((*p).m_status & LGC_FLAG_E_OR2) == 0)
					{
						arg1 = main + 1;
						arg2 = main + 2;
						while (database.functions[arg2].m_kind == LGC_REF)
						{
							arg2 = database.functions[arg2].m_ref;
						}
						
						list<NDTerm>::const_iterator leftOp = conditions.begin();
						for (;leftOp!=conditions.end();++leftOp)
						{
							int left = (*leftOp).m_index;
							while (database.functions[left].m_kind == LGC_REF)
							{
								left = database.functions[left].m_ref;
							}

							if (isComplement(arg2,left) || isComplement(left,arg2) )
							{
								while (database.functions[arg1].m_kind == LGC_REF)
								{
									arg1 = database.functions[arg2].m_ref;
								}
								
								ndTerm.m_index = arg1;
								ndTerm.m_first = (*p).m_index;
								ndTerm.m_second = (*leftOp).m_index;
								ndTerm.m_path = (*p).m_path < (*leftOp).m_path ? (*p).m_path + 1 : (*leftOp).m_path + 1; 
								ndTerm.m_rule = LGC_E_OR_2;
								added += InsertTerm(ndTerm);
								(*p).m_status |= LGC_FLAG_E_OR2;
							}
							
						}
						
					}

					break;

				case LGC_ADDR_MAP:
					if (((*p).m_status & LGC_FLAG_E_MAP) == 0)
					{
						
						arg1 = main + 1;
						arg2 = main + 2;
						while (database.functions[arg1].m_kind == LGC_REF)
						{
							arg1 = database.functions[arg1].m_ref;
						}

						list<NDTerm>::const_iterator leftOp = conditions.begin();
						for (;leftOp!=conditions.end();++leftOp)
						{
							int left = (*leftOp).m_index;
							while (database.functions[left].m_kind == LGC_REF)
							{
								left = database.functions[left].m_ref;
							}
							if (isCompatible(left,arg1))
							{
								
								while (database.functions[arg2].m_kind == LGC_REF)
								{
									arg2 = database.functions[arg2].m_ref;
								}
								ndTerm.m_index = arg2;
								ndTerm.m_first = (*p).m_index;
								ndTerm.m_second = (*leftOp).m_index;
								ndTerm.m_path = (*p).m_path < (*leftOp).m_path ? (*p).m_path + 1 : (*leftOp).m_path + 1; 
								ndTerm.m_rule = LGC_E_MODUS;
								added += InsertTerm(ndTerm);
								(*p).m_status |= LGC_FLAG_E_MAP;
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
			
		}
	}
	


	return added;
}

int NaturalDeduction::Introduction()
{

	int subgoal = goals.back().m_index;

	while (database.functions[subgoal].m_kind == LGC_REF)
	{
		subgoal = database.functions[subgoal].m_ref;
	}

	int arg1 = 0;
	int arg2 = 0;
	int status = goals.back().m_status;
	NDTerm t;
	if(database.functions[subgoal].m_info == 0)
	{
		if (database.functions[subgoal].m_kind == LGC_TERM_FUNC)
		{
			switch (database.functions[subgoal].m_ref)
			{

			// |- NOT F => F |- NOT F, FALSE
			case LGC_ADDR_NOT:
				if ((status & LGC_FLAG_I_NOT) !=LGC_FLAG_I_NOT)
				{
					arg1 = subgoal + 1;
					while (database.functions[arg1].m_kind == LGC_REF)
					{
						arg1 = database.functions[arg1].m_ref;
					}
					t.m_index = arg1;
					t.m_assume = subgoal;
					InsertTerm(t);
					goals.back().m_pendings = 1;
					goals.back().m_rule = LGC_I_NOT;
					goals.back().m_status |= LGC_FLAG_I_NOT;
					goals.back().m_assume = arg1;
					goals.push_back(NDTerm(LGC_ADDR_FALSE));
					return 1;
				}
				break;
			// |- P ^ Q => |- P ^ Q , P, Q
			case LGC_ADDR_AND:
				if ((status & LGC_FLAG_I_AND) !=LGC_FLAG_I_AND)
				{
					arg1 = subgoal + 1;
					arg2 = subgoal + 2;
					
					while (database.functions[arg1].m_kind == LGC_REF)
					{
						arg1 = database.functions[arg1].m_ref;
					}
					
					while (database.functions[arg2].m_kind == LGC_REF)
					{
						arg2 = database.functions[arg2].m_ref;
					}

					goals.back().m_pendings = 2;
					goals.back().m_rule = LGC_I_AND;
					goals.back().m_status |= LGC_FLAG_I_AND;
					goals.push_back(NDTerm(arg1));
					goals.push_back(NDTerm(arg2));
					return 1;
				}
				break;

			// |- P | Q -> |- P -> |- Q -> NOT(P|Q) |- FALSE
			case LGC_ADDR_OR:
				
				if ((status & LGC_FLAG_I_OR1) !=LGC_FLAG_I_OR1)
				{
					arg1 = subgoal + 1;
					while (database.functions[arg1].m_kind == LGC_REF)
					{
						arg1 = database.functions[arg1].m_ref;
					}
					goals.back().m_pendings = 1;
					goals.back().m_rule = LGC_FLAG_I_OR1;
					goals.back().m_status |= LGC_FLAG_I_OR1;
					branches.push_back(goals.back().m_index);
					insertGoal(NDTerm(arg1));
				} 

				else if ((status & LGC_FLAG_I_OR2) !=LGC_FLAG_I_OR2)
				{
					arg2 = subgoal + 2;
					while (database.functions[arg2].m_kind == LGC_REF)
					{
						arg2 = database.functions[arg2].m_ref;
					}
					goals.back().m_pendings = 1;
					goals.back().m_rule = LGC_FLAG_I_OR2;
					goals.back().m_status |= LGC_FLAG_I_OR2;
					branches.push_back(goals.back().m_index);
					insertGoal(NDTerm(arg2));
					
				}

				else if((status & LGC_FLAG_I_OR3) !=LGC_FLAG_I_OR3)
				{
					database.functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT));
					database.functions.push_back(Term(LGC_REF,subgoal));
					arg1 = database.functions.size() - 2;
					t.m_assume = arg1;
					InsertTerm(t);
					goals.back().m_pendings = 1;
					goals.back().m_rule = LGC_I_NOT;
					goals.back().m_assume = arg1;
					goals.back().m_status |= LGC_FLAG_I_OR3;
					goals.push_back(NDTerm(LGC_ADDR_FALSE));	
				}
				else
				{
					return 0;
				};
				return 1;

			// |- P -> Q => P |- Q
			case LGC_ADDR_MAP:
				if ((status & LGC_FLAG_I_OR1) !=LGC_FLAG_I_OR1)
				{
					arg1 = subgoal + 1;
					arg2 = subgoal + 2;
					while (database.functions[arg1].m_kind == LGC_REF)
					{
						arg1 = database.functions[arg1].m_ref;
					}
					
					while (database.functions[arg2].m_kind == LGC_REF)
					{
						arg2 = database.functions[arg2].m_ref;
					}

					t.m_assume = arg1;
					t.m_assume = subgoal;
					InsertTerm(t);
					goals.back().m_pendings = 1;
					goals.back().m_rule = LGC_I_MODUS;
					goals.back().m_status |= LGC_FLAG_I_MAP;
					goals.back().m_assume = arg1;
					insertGoal(NDTerm(arg2));
					return 1;
				}
				break;
			//	|- P	=>	NOT P |- P , FALSE
			default:
				if ((status & LGC_FLAG_I_NOT) !=LGC_FLAG_I_NOT)
				{
					database.functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT));
					database.functions.push_back(Term(LGC_REF,subgoal));
					arg1 = database.functions.size() - 2;
					t.m_index = arg1;
					InsertTerm(t);
					goals.back().m_pendings = 1;
					goals.back().m_rule = LGC_I_NOT;
					goals.back().m_status |= LGC_FLAG_I_NOT;
					goals.back().m_assume = arg1;
					goals.push_back(NDTerm(LGC_ADDR_FALSE));	
					return 1;
				}
				break;
			}
		}
		else if(subgoal!=LGC_ADDR_FALSE)
		{
			database.functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT));
			database.functions.push_back(Term(LGC_REF,subgoal));
			arg1 = database.functions.size() - 2;
			t.m_index = arg1;
			InsertTerm(t);
			goals.back().m_pendings = 1;
			goals.back().m_rule = LGC_I_NOT;
			goals.back().m_assume = arg1;
			goals.back().m_status |= LGC_FLAG_I_NOT;
			goals.push_back(NDTerm(LGC_ADDR_FALSE));	
			return 1;
		}

	}

	//Quantifier introduction
	else
	{
		
	}

	return 0;
}

int NaturalDeduction::Contradiction()
{
	list<NDTerm>::iterator p;
	
	for (p = conditions.begin();p!=conditions.end();++p)
	{
		int source = (*p).m_index;
		while (database.functions[source].m_kind == LGC_REF)
		{
			source = database.functions[source].m_ref;
		}
		int arg1 = source + 1;
		int arg2 = source + 2;
		int status = (*p).m_status;
		NDTerm t;
		if (database.functions[source].m_info == 0 && database.functions[source].m_kind == LGC_TERM_FUNC)
		{
			switch (database.functions[source].m_ref)
			{
			case LGC_ADDR_NOT:
				if (((*p).m_status & LGC_FLAG_C_NOT)!=LGC_FLAG_C_NOT)
				{
					(*p).m_status |=LGC_FLAG_C_NOT;
					while (database.functions[arg1].m_kind == LGC_REF)
					{
						arg1 = database.functions[arg1].m_ref;
					}
					t.m_index = arg1;
					t.m_status |= LGC_FLAG_C_NOT;
					return insertGoal(t);
					
				}
				break;

			case LGC_ADDR_OR:
				if (((*p).m_status & LGC_FLAG_C_OR1)!=LGC_FLAG_C_OR1)
				{
					(*p).m_status |=LGC_FLAG_C_OR1;
					while (database.functions[arg1].m_kind == LGC_REF)
					{
						arg1 = database.functions[arg1].m_ref;
					}
					t.m_index = arg1;
					t.m_status |= LGC_FLAG_C_OR1;
					return insertGoal(t);
					
				}
				else if (((*p).m_status & LGC_FLAG_C_OR2)!=LGC_FLAG_C_OR2)
				{
					(*p).m_status |= LGC_FLAG_C_OR2;
					while (database.functions[arg2].m_kind == LGC_REF)
					{
						arg2 = database.functions[arg1].m_ref;
					}
					t.m_index = arg2;
					t.m_status |= LGC_FLAG_C_OR2;
					return insertGoal(t);
				} 
				break;

			case LGC_ADDR_MAP:
				if (((*p).m_status & LGC_FLAG_C_MAP)!=LGC_FLAG_C_MAP)
				{
					(*p).m_status |=LGC_FLAG_C_MAP;
					while (database.functions[arg1].m_kind == LGC_REF)
					{
						arg1 = database.functions[arg1].m_ref;
					}
					t.m_index = arg1;
					t.m_status |=LGC_FLAG_C_MAP;
					return insertGoal(t);
				}
				break;

			}
		}
	}

	return 0;
}

int NaturalDeduction::print()
{
	string result  = "";
	database.print();
	for (list<NDTerm>::iterator p = proveds.begin();p!=proveds.end();++p)
	{
		cout<<"Rule:" <<(*p).m_rule<<"\t"<<(*p).m_first<<"\t"<<(*p).m_second<<endl;	
	}
	return 0;
}

bool NaturalDeduction::isComplement(int active, int negative) const
{
	int neg = negative;
	while (database.functions[neg].m_kind == LGC_REF)
	{
		neg = database.functions[neg].m_ref;
	}

	if (database.functions[neg].m_kind == LGC_TERM_FUNC && database.functions[neg].m_ref == LGC_ADDR_NOT)
	{
		
		neg++;
		while (database.functions[neg].m_kind == LGC_REF)
		{
			neg = database.functions[neg].m_ref;
		}
		return isCompatible(active,neg);	
	}
	return false;
}

int NaturalDeduction::ProveIt()
{
	

	while (!goals.empty())
	{
#if _DEBUG
		cout<<"Last goal :"<<goals.back().m_index<<endl;
#endif
		if (goals.back().m_pendings > 0)
		{
			conditions.push_back(goals.back());
			proveds.push_back(goals.back());
			goals.pop_back();
			
		}
		else
		{
			if (isReached(goals.back().m_index))
			{
			
				conditions.push_back(goals.back());
				proveds.push_back(goals.back());
				goals.pop_back();
				continue;
				
			}
			else
			{
				bool applied = false;
#if _DEBUG
				cout<<"Conditions\n";
				for (list<NDTerm>::iterator p = conditions.begin();p!=conditions.end();++p)
				{
					cout<<"\t"<<(*p).m_index;
				}
				cout<<"\n";
#endif
				while (Eliminate() > 0)
				{ 

					applied = true;
				}

				if (applied)
				{
					continue;
				}
				if(Introduction() > 0)
				{
					continue;
				}

				if(goals.back().m_index == LGC_ADDR_FALSE)
				{
					
				if (Contradiction())
					{
						continue;
					}
					
				}

				if (turnIt())
				{
					continue;
				}

			if ((goals.back().m_status & LGC_FLAG_CONTR)!= 0)
				{
					goals.pop_back();
					continue;
				}

				return 0;
			}
		}
		
	}
	return 1;
}

int NaturalDeduction::isReached(int subgoal)
{
	if (subgoal == LGC_ADDR_FALSE)
	{
		for (list<NDTerm>::const_iterator p = conditions.begin();p!=conditions.end();++p)
		{
			for (list<NDTerm>::const_iterator q = conditions.begin();q!=conditions.end();++q)
			{
				if (isComplement((*p).m_index,(*q).m_index))
				{
					goals.back().m_first = (*p).m_index;
					goals.back().m_second = (*q).m_index;
					goals.back().m_rule = LGC_E_NOT;
					return 1;
				}
				else if (isComplement((*q).m_index,(*p).m_index))
				{
					goals.back().m_first = (*q).m_index;
					goals.back().m_second = (*p).m_index;
					goals.back().m_rule = LGC_E_NOT;
					return 1;
				}
			}
		}
	}
	else
	{
		for (list<NDTerm>::const_iterator p = conditions.begin(); p!= conditions.end();++p)
		{
			if (isCompatible((*p).m_index,subgoal))
			{
				goals.back().m_assume	=	(*p).m_assume;
				goals.back().m_first	=	(*p).m_first;
				goals.back().m_second	=	(*p).m_second;
				goals.back().m_index	=	(*p).m_index;
				goals.back().m_path		=	(*p).m_path;
				goals.back().m_rule		=	(*p).m_rule;
				return (*p).m_index;
			}
		}
	}
	return 0;
}

int NaturalDeduction::InsertTerm(NDTerm term)
{
	list<NDTerm>::iterator found;
	for(found = conditions.begin();found!=conditions.end();++found)
	{
		if ((*found).m_index == term.m_index)
		{
			return 0;
		}
	}
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
		int lastGoal = branches.back();
		branches.pop_back();
		int lastCondition = branches.back();
		branches.pop_back();
		while (!goals.empty() && goals.back().m_index != lastGoal)
		{
			goals.pop_back();
		}
		goals.back().m_pendings = 0;
		int assume = goals.back().m_assume;
		if (assume > 0)
		{
			while (!conditions.empty() && conditions.back().m_index!=assume)
			{
				conditions.pop_back();
			}
			conditions.pop_back();

			if (!conditions.empty())
			{
				for (list<NDTerm>::iterator p = conditions.begin(); p!= conditions.end();++p)
				{
					//(*p).m_status = 0x00000000;
				}
			}
		}
		return 1;
	}
	return 0;
}