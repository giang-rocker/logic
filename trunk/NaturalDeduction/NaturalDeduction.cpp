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
		conditions.push_back(NDTerm((*p)));

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

	vector<NDTerm>::iterator p ;
	
	int added = 0;
	int arg1 = 0;
	int arg2 = 0;
	NDTerm ndTerm;
	int outside = -1;
	for (p = conditions.begin();p!=end_p;++p)
	{
		++outside;
		if (((*p).m_status&LGC_FLAG_DIS) == LGC_FLAG_DIS)
		{
			continue;
		}

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
						if (((*p).m_status & LGC_FLAG_E_NOT) != LGC_FLAG_E_NOT)
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
							ndTerm.m_first = outside;
							
							added += InsertCondition(ndTerm);
							
						}
					}
					break;
	
				case LGC_ADDR_AND:
					if (((*p).m_status & LGC_FLAG_E_AND) != LGC_FLAG_E_AND)
					{
						(*p).m_status |= LGC_FLAG_E_AND;
						int arg1 = main + 1;
						while (database.functions[arg1].m_kind == LGC_REF)
						{
							arg1 = database.functions[arg1].m_ref;
						}

						ndTerm.m_index = arg1;
						ndTerm.m_rule = LGC_E_AND_1;
						ndTerm.m_first = outside;
						ndTerm.m_path = (*p).m_path + 1;
						added += InsertCondition(ndTerm);

						arg2 = main + 2;
						while (database.functions[arg2].m_kind == LGC_REF)
						{
							arg2 = database.functions[arg2].m_ref;
						}

						ndTerm.m_index = arg2;
						ndTerm.m_rule = LGC_E_AND_2;
						added += InsertCondition(ndTerm);

					}
					break;


				case LGC_ADDR_OR:		
					// A v B , not(A) -> B
					
					if ( ((*p).m_status & LGC_FLAG_E_OR1) != LGC_FLAG_E_OR1)
					{
						arg1 = main + 1;
						arg2 = main + 2;
						while (database.functions[arg1].m_kind == LGC_REF)
						{
							arg1 = database.functions[arg1].m_ref;
						}
						
						vector<NDTerm>::const_iterator leftOp = conditions.begin();
						int inside = -1;
						for (;leftOp!=end_p;++leftOp)
						{
							++inside;
							if (((*leftOp).m_status&LGC_FLAG_DIS) == LGC_FLAG_DIS)
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
								ndTerm.m_first = outside;
								ndTerm.m_second = inside;
								ndTerm.m_path = (*p).m_path < (*leftOp).m_path ? (*p).m_path + 1 : (*leftOp).m_path + 1; 
								ndTerm.m_rule = LGC_E_OR_1;
								added += InsertCondition(ndTerm);
								(*p).m_status |= LGC_FLAG_E_OR1;
								(*p).m_status |= LGC_FLAG_C_OR1;
							}
							
						}
						
					}

					if (((*p).m_status & LGC_FLAG_E_OR2) != LGC_FLAG_E_OR2)
					{
						arg1 = main + 1;
						arg2 = main + 2;
						while (database.functions[arg2].m_kind == LGC_REF)
						{
							arg2 = database.functions[arg2].m_ref;
						}
						
						vector<NDTerm>::const_iterator leftOp = conditions.begin();
						int inside = -1;
						for (;leftOp!=end_p;++leftOp)
						{
							++inside;
							if (((*leftOp).m_status&LGC_FLAG_DIS) == LGC_FLAG_DIS)
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
								ndTerm.m_first = outside;
								ndTerm.m_second = inside;
								ndTerm.m_path = (*p).m_path < (*leftOp).m_path ? (*p).m_path + 1 : (*leftOp).m_path + 1; 
								ndTerm.m_rule = LGC_E_OR_2;
								added += InsertCondition(ndTerm);
								(*p).m_status |= LGC_FLAG_E_OR2;
								(*p).m_status |= LGC_FLAG_C_OR2;
							}
							
						}
						
					}

					break;

				case LGC_ADDR_MAP:
					if (((*p).m_status & LGC_FLAG_E_MAP) != LGC_FLAG_E_MAP)
					{
						
						arg1 = main + 1;
						arg2 = main + 2;
						while (database.functions[arg1].m_kind == LGC_REF)
						{
							arg1 = database.functions[arg1].m_ref;
						}

						vector<NDTerm>::const_iterator leftOp = conditions.begin();
						int inside = -1;
						for (;leftOp!=end_p;++leftOp)
						{
							++inside;
							if (((*leftOp).m_status&LGC_FLAG_DIS) == LGC_FLAG_DIS)
							{
								continue;
							}
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
								ndTerm.m_first = outside;
								ndTerm.m_second = inside;
								ndTerm.m_path = (*p).m_path < (*leftOp).m_path ? (*p).m_path + 1 : (*leftOp).m_path + 1; 
								ndTerm.m_rule = LGC_E_MODUS;
								added += InsertCondition(ndTerm);
								(*p).m_status |= LGC_FLAG_E_MAP;
								(*p).m_status |= LGC_FLAG_C_MAP;
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
					t.m_status |= LGC_FLAG_ASS;
					InsertCondition(t);
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
					branches.push_back(goals.size());
					branches.push_back(conditions.size());
					goals.push_back(NDTerm(arg1));
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
					branches.push_back(goals.size());
					branches.push_back(conditions.size());
					goals.push_back(NDTerm(arg2));
					
				}

				else if((status & LGC_FLAG_I_OR3) !=LGC_FLAG_I_OR3)
				{
					database.functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT));
					database.functions.push_back(Term(LGC_REF,subgoal));
					arg1 = database.functions.size() - 2;
					t.m_index = arg1;
					t.m_status |= LGC_FLAG_ASS;
					InsertCondition(t);
					goals.back().m_pendings = 1;
					goals.back().m_rule = LGC_I_NOT;
					goals.back().m_assume = arg1;
					goals.back().m_status |= LGC_FLAG_I_OR3;
					goals.push_back(NDTerm(LGC_ADDR_FALSE));	
				}
				else
				{
					return 0;
				}
				return 1;

			// |- P -> Q => P |- Q
			case LGC_ADDR_MAP:
				if ((status & LGC_FLAG_I_MAP) !=LGC_FLAG_I_MAP)
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
					t.m_index = arg1;
					t.m_status |= LGC_FLAG_ASS;
					goals.back().m_pendings = 1;
					goals.back().m_rule = LGC_I_MODUS;
					goals.back().m_status |= LGC_FLAG_I_MAP;
					goals.back().m_assume = arg1;
					goals.push_back(NDTerm(arg2));
					return InsertCondition(t);
				}
				break;

			//	|- P	=>	NOT P |- P , FALSE (for functor)
			default:
				if ((status & LGC_FLAG_I_NOT) !=LGC_FLAG_I_NOT)
				{
					database.functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT));
					database.functions.push_back(Term(LGC_REF,subgoal));
					arg1 = database.functions.size() - 2;
					t.m_index = arg1;
					t.m_status |= LGC_FLAG_C_NOT;
					goals.back().m_pendings = 1;
					goals.back().m_rule = LGC_I_NOT;
					goals.back().m_status |= LGC_FLAG_I_NOT;
					goals.back().m_assume = arg1;
					goals.push_back(NDTerm(LGC_ADDR_FALSE));	
					return InsertCondition(t);
				}
				break;
			}
		}
		//	|- P	=>	NOT P |- P , FALSE (for proposition)
		else if(subgoal!=LGC_ADDR_FALSE)
		{
			if ((status & LGC_FLAG_I_NOT) !=LGC_FLAG_I_NOT)
			{
				database.functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT));
				database.functions.push_back(Term(LGC_REF,subgoal));
				arg1 = database.functions.size() - 2;
				t.m_index = arg1;
				t.m_status |= LGC_FLAG_C_NOT;
				goals.back().m_pendings = 1;
				goals.back().m_rule = LGC_I_NOT;
				goals.back().m_status |= LGC_FLAG_I_NOT;
				goals.back().m_assume = arg1;
				goals.push_back(NDTerm(LGC_ADDR_FALSE));	
				return InsertCondition(t);
			}
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
	vector<NDTerm>::iterator p;
	
	for (p = conditions.begin();p!=conditions.end();++p)
	{
		if (((*p).m_status&LGC_FLAG_DIS) == LGC_FLAG_DIS)
		{
			continue;
		}
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
					(*p).m_status |= LGC_FLAG_C_OR1;
					while (database.functions[arg1].m_kind == LGC_REF)
					{
						arg1 = database.functions[arg1].m_ref;
					}
					database.functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT));
					database.functions.push_back(Term(LGC_REF,arg1));
					t.m_index = database.functions.size() - 2;
					return insertGoal(t);
					
				}
				else if (((*p).m_status & LGC_FLAG_C_OR2)!=LGC_FLAG_C_OR2)
				{
					(*p).m_status |= LGC_FLAG_C_OR2;
					while (database.functions[arg2].m_kind == LGC_REF)
					{
						arg2 = database.functions[arg1].m_ref;
					}
					database.functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT));
					database.functions.push_back(Term(LGC_REF,arg2));
					t.m_index = database.functions.size() - 2;
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
	
	int times = 0;
	int active;
	int negative;
	int subgoal;
	int assume = 0;
	
	while (!goals.empty())
	{


#if _DEBUG
		if (times == 4)
		{
			int dummy = 0;
		}
		cout <<++times<<"_________________________Conditions__________________________________\n";
		for (vector<NDTerm>::iterator c = conditions.begin();c!=conditions.end();++c)
		{
			if (((*c).m_status & LGC_FLAG_DIS) == LGC_FLAG_DIS)
			{
				continue;
			}
			cout<<"\t"<<database.GetString((*c).m_index);
		}

		cout <<"\n_______________________________Goals__________________________________\n";
		for (vector<NDTerm>::iterator g = goals.begin();g!=goals.end();++g)
		{
			cout<<"\t"<<database.GetString((*g).m_index);
		}
		cout<<"\n______________________________________________________________________\n\n\n";
#endif


		
		if (goals.back().m_pendings > 0)
		{
			subgoal = goals.back().m_index;

// 			if (isReached(subgoal,active))
// 			{
// 				if (conditions[proved.back()].m_index == LGC_ADDR_FALSE)
// 				{
// 					int ass = conditions.back().m_assume;
// 					proved.pop_back();
// 					proved.push_back(active);
// 
// 				}
// 				//For shorter path
// 				if (conditions)
// 				{
// 
// 				}
// 				continue;
// 			}
			
			goals.back().m_first = proved.back();
			proved.pop_back();
			if (goals.back().m_pendings == 2)
			{
				goals.back().m_second = proved.back();
				proved.pop_back();
			}
			conditions.push_back(goals.back());
			goals.pop_back();
			//disable assume conditions

		}
		else
		{
			
			int subgoal = goals.back().m_index;
			if (subgoal == LGC_ADDR_FALSE)
			{

				if (isReached(active, negative))
				{
					goals.back().m_first = active;
					goals.back().m_second = negative;
					goals.back().m_rule = LGC_E_NOT;
					proved.push_back(conditions.size());
					conditions.push_back(goals.back());
					goals.pop_back();
					continue;
				}
				
			} 
			else if(isReached(active))
			{
				proved.push_back(active);
				goals.pop_back();
				continue;
			}

			bool applied = false;
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

			if ((goals.back().m_status & LGC_FLAG_CONTR)!= 0)
			{
				goals.pop_back();
				continue;
			}

			if (turnIt())
			{
				continue;
			}
			return 0;
			
		}
		
	}
	return 1;
}

bool NaturalDeduction::isReached(int &active)
{
	int subgoal = goals.back().m_index;
	int outside = -1;
	active = -1;
	int length = 0x7FFFFFFF;
	bool result = false;
	for (vector<NDTerm>::const_iterator p = conditions.begin(); p!= conditions.end();++p)
	{
		++outside;
		if(((*p).m_status & LGC_FLAG_DIS) == LGC_FLAG_DIS)
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
		for (vector<NDTerm>::const_iterator p = conditions.begin();p!=conditions.end();++p)
		{
			++outside;
			if(((*p).m_status & LGC_FLAG_DIS) == LGC_FLAG_DIS)
			{
				continue;
			}
			int inside = -1;
			for (vector<NDTerm>::const_iterator q = conditions.begin();q!=conditions.end();++q)
			{
				++inside;
				if(((*q).m_status & LGC_FLAG_DIS) == LGC_FLAG_DIS)
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

int NaturalDeduction::InsertCondition(NDTerm term)
{
	vector<NDTerm>::iterator found;
	for(found = conditions.begin();found!=conditions.end();++found)
	{
		if (((*found).m_status & LGC_FLAG_DIS) == LGC_FLAG_DIS)
		{
			continue;
		}
		if ((*found).m_index != LGC_ADDR_FALSE && (*found).m_index == term.m_index )
		{
			return 0;
		}
	}
	conditions.push_back(term);
	return 1;
}

int NaturalDeduction::insertGoal(NDTerm term)
{
	vector<NDTerm>::iterator found;
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
		for (vector<NDTerm>::iterator p = conditions.begin(); p!= conditions.end();++p)
		{
			(*p).m_status = 0x00000000;
		}

		return 1;
	}
	return 0;
}


string NaturalDeduction::GetString() const
{
	string result = "";
	
	return result;
}



int NaturalDeduction::disable(int assume)
{
	if ((conditions[assume].m_status & LGC_FLAG_ASS) != LGC_FLAG_ASS)
	{
		return 0;
	}
	list<int>parent;
	parent.push_back(assume);
	conditions[assume].m_status |=LGC_FLAG_DIS;
	for (int index = 0; index < conditions.size();index++)
	{
		if ((conditions[index].m_status&LGC_FLAG_DIS)==LGC_FLAG_DIS)
		{
			continue;
		}
		if ((find(parent.begin(),parent.end(),conditions[index].m_first)!= parent.end()) || (find(parent.begin(),parent.end(),conditions[index].m_second)!= parent.end()))
		{
			parent.push_back(index);
			conditions[index].m_status |= LGC_FLAG_DIS;
		}
	}
	return 0;
}
