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
	lastLine = 1;
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
	int outside = -1;
	int index;
	for (p = conditions.begin();p!=conditions.end();++p)
	{
		outside++;
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
							ndTerm.m_first = outside; //(*p).m_index;
							added += InsertCondition(ndTerm,index);
							
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
						ndTerm.m_first = outside; //(*p).m_index;
						ndTerm.m_path = (*p).m_path + 1;
						added += InsertCondition(ndTerm,index);

						arg2 = main + 2;
						while (database.functions[arg2].m_kind == LGC_REF)
						{
							arg2 = database.functions[arg2].m_ref;
						}

						ndTerm.m_index = arg2;
						ndTerm.m_rule = LGC_E_AND_2;
						added += InsertCondition(ndTerm,index);

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
						
						list<NDTerm>::const_iterator leftOp = conditions.begin();
						int inside = -1;
						for (;leftOp!=conditions.end();++leftOp)
						{
							++inside;
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
								ndTerm.m_first =  outside; //(*p).m_index;
								ndTerm.m_second = inside;  //(*leftOp).m_index;
								ndTerm.m_path = (*p).m_path < (*leftOp).m_path ? (*p).m_path + 1 : (*leftOp).m_path + 1; 
								ndTerm.m_rule = LGC_E_OR_1;
								added += InsertCondition(ndTerm,index);
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
						
						list<NDTerm>::const_iterator leftOp = conditions.begin();
						int inside = -1;
						for (;leftOp!=conditions.end();++leftOp)
						{
							++inside;
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
								
								ndTerm.m_index = arg2;
								ndTerm.m_first =  outside;//(*p).m_index;
								ndTerm.m_second = inside ;//(*leftOp).m_index;
								ndTerm.m_path = (*p).m_path < (*leftOp).m_path ? (*p).m_path + 1 : (*leftOp).m_path + 1; 
								ndTerm.m_rule = LGC_E_OR_2;
								added += InsertCondition(ndTerm,index);
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

						list<NDTerm>::const_iterator leftOp = conditions.begin();
						int inside = -1;
						for (;leftOp!=conditions.end();++leftOp)
						{
							++inside;
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
								ndTerm.m_first = outside;  //(*p).m_index;
								ndTerm.m_second = inside ; //(*leftOp).m_index;
								ndTerm.m_path = (*p).m_path < (*leftOp).m_path ? (*p).m_path + 1 : (*leftOp).m_path + 1; 
								ndTerm.m_rule = LGC_E_MODUS;
								added += InsertCondition(ndTerm,index);
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
	int assume = -1;
	while (database.functions[subgoal].m_kind == LGC_REF)
	{
		subgoal = database.functions[subgoal].m_ref;
	}

	int arg1 = 0;
	int arg2 = 0;
	int status = goals.back().m_status;
	NDTerm t;
	int added = 0;
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
					InsertCondition(t,assume);
					goals.back().m_pendings = 1;
					goals.back().m_rule = LGC_I_NOT;
					goals.back().m_status |= LGC_FLAG_I_NOT;
					goals.back().m_assume = assume;
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
					goals.push_back(NDTerm(arg2));
					goals.push_back(NDTerm(arg1));
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
					branches.push_back(proveds.size());
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
					branches.push_back(proveds.size());
					goals.push_back(NDTerm(arg2));
					
				}

				else if((status & LGC_FLAG_I_OR3) !=LGC_FLAG_I_OR3)
				{
					database.functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT));
					database.functions.push_back(Term(LGC_REF,subgoal));
					arg1 = database.functions.size() - 2;
					t.m_index = arg1;
					InsertCondition(t,assume);
					goals.back().m_pendings = 1;
					goals.back().m_rule = LGC_I_NOT;
					goals.back().m_assume = assume;
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
					added += InsertCondition(t,assume);
					goals.back().m_pendings = 1;
					goals.back().m_rule = LGC_I_MODUS;
					goals.back().m_status |= LGC_FLAG_I_MAP;
					goals.back().m_assume = arg1;
					goals.push_back(NDTerm(arg2));
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
					t.m_status |= LGC_FLAG_C_NOT;
					added += InsertCondition(t,assume);
					goals.back().m_pendings = 1;
					goals.back().m_rule = LGC_I_NOT;
					goals.back().m_status |= LGC_FLAG_I_NOT;
					goals.back().m_assume = arg1;
					goals.push_back(NDTerm(LGC_ADDR_FALSE));	
				}
				break;
			}
		}

		else if(subgoal!=LGC_ADDR_FALSE)
		{
			if ((status & LGC_FLAG_I_NOT) !=LGC_FLAG_I_NOT)
			{
				database.functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT));
				database.functions.push_back(Term(LGC_REF,subgoal));
				arg1 = database.functions.size() - 2;
				t.m_index = arg1;
				t.m_status |= LGC_FLAG_C_NOT;
				added += InsertCondition(t,assume);
				goals.back().m_pendings = 1;
				goals.back().m_rule = LGC_I_NOT;
				goals.back().m_status |= LGC_FLAG_I_NOT;
				goals.back().m_assume = arg1;
				goals.push_back(NDTerm(LGC_ADDR_FALSE));
			}
		}

	}

	//Quantifier introduction
	else
	{
		
	}

	return added;
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
	while (!goals.empty())
	{


#if _DEBUG
		if (times == 1)
		{
			int dummy = 0;
		}
		//database.print();
		cout <<++times<<"_________________________Conditions__________________________________\n";
		for (list<NDTerm>::iterator c = conditions.begin();c!=conditions.end();++c)
		{
			cout<<"\t"<<database.GetString((*c).m_index);
		}

		cout <<"\n_______________________________Goals__________________________________\n";
		for (list<NDTerm>::iterator g = goals.begin();g!=goals.end();++g)
		{
			cout<<"\t"<<database.GetString((*g).m_index);
		}
		
		cout <<"\n________________________________Proved________________________________\n";
		for (list<int>::iterator p = proveds.begin();p!=proveds.end();++p)
		{
			GetNDTerm(*p);
			cout<<"\t"<<database.GetString((*cond).m_index);
		}
		cout<<"\n______________________________________________________________________\n\n\n";
#endif
		
		if (goals.back().m_pendings > 0)
		{

			//InsertCondition(goals.back());
			goals.back().m_first = proveds.back();
			proveds.pop_back();
			if (goals.back().m_pendings == 2)
			{
				goals.back().m_second = proveds.back();
				proveds.pop_back();
			}
			proveds.push_back(conditions.size());
			conditions.push_back(goals.back());
			goals.pop_back();
		}
		else
		{
			int subgoal = goals.back().m_index;
			int active;
			int negative;

			if (subgoal == LGC_ADDR_FALSE)
			{
				if (isReached(active,negative))
				{
					goals.back().m_rule = LGC_E_NOT;
					goals.back().m_first = active;
					goals.back().m_second = negative;
					proveds.clear();
					proveds.push_back(conditions.size());
					conditions.push_back(goals.back());
					goals.pop_back();
					continue;
				}
			} 
			else if (isReached(active))
			{
				proveds.push_back(active);
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

#if _DEBUG
	cout <<++times<<"_________________________Conditions__________________________________\n";
	for (list<NDTerm>::iterator c = conditions.begin();c!=conditions.end();++c)
	{
		cout<<"\t"<<"Index = "<<(*c).m_index<<"\tFirst = "<<(*c).m_first<<"\t Second = "<<(*c).m_second<<"\t Pending = "<<(*c).m_pendings<<"\t Assume = "<<(*c).m_assume<< endl; 
	}
	
	cout <<"\n_______________________________Goals__________________________________\n";
	for (list<NDTerm>::iterator g = goals.begin();g!=goals.end();++g)
	{
		cout<<"\t"<<database.GetString((*g).m_index);
	}
	
	cout <<"\n________________________________Proved________________________________\n";
	for (list<int>::iterator p = proveds.begin();p!=proveds.end();++p)
	{
		GetNDTerm(*p);
		cout<<"\t"<<database.GetString((*cond).m_index);
	}
	cout<<"\n______________________________________________________________________\n\n\n";
#endif

	return 1;
}



int NaturalDeduction::InsertCondition(NDTerm term, int&index)
{
	list<NDTerm>::iterator found;
	for(found = conditions.begin();found!=conditions.end();++found)
	{

		if ((*found).m_index != LGC_ADDR_FALSE && (*found).m_index == term.m_index)
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
		int size = branches.back();
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
			(*p).m_status = 0x00000000;
		}

		return 1;
	}
	return 0;
}


string NaturalDeduction::GetString(int index) 
{
	string result = "";
	GetNDTerm(index);
	NDTerm goal = *cond;
	if(goal.m_line > 0)
	{
		return result;
	}

	if (goal.m_assume >= 0)
	{
		result += "if\t"+ToString(lastLine++) + ".\t"+ database.GetString(goal.m_assume) + "\t\t\t\t\t\n";
		result += "nif\t" + GetString(goal.m_first);
		result += ToString(lastLine++) + ".\t\t" + database.GetString(goal.m_index) + "\t\t\t\t\trule = " + ToString(goal.m_rule) +"\n";
		goal.m_line = lastLine - 1;
	}
	
	else
	{
		if(goal.m_pendings == 1)
		{
			result += GetString(goal.m_first);
			result += ToString(lastLine++) + ".\t\t" + database.GetString(goal.m_index) + "\t\t\t\t\trule = " + ToString(goal.m_rule) + "\n";
		}
		else if ( goal.m_pendings ==2)
		{
			result += GetString(goal.m_second);
			result += GetString(goal.m_first);
			result += ToString(lastLine++) + ".\t\t" + database.GetString(goal.m_index) + "\t\t\t\t\trule = " + ToString(goal.m_rule) + "\n";
		}
		else
		{
			if(goal.m_rule == LGC_RULE_PREMISE)
			{
				result = ToString(lastLine++) + ".\t\t"+ database.GetString(goal.m_index) + "\t\t\t\t\tTien de \n";
			}
			else if (goal.m_second == -1)
			{
				result += GetString(goal.m_second);
				result += GetString(goal.m_first);
				result += ToString(lastLine++) + ".\t\t" + database.GetString(goal.m_index) + "\t\t\t\t\trule = " + ToString(goal.m_rule) + "\n";
			}
			else
			{
				result += GetString(goal.m_second);
				result += GetString(goal.m_first);
				result += ToString(lastLine++) + ".\t\t" + database.GetString(goal.m_index) + "\t\t\t\t\trule = " + ToString(goal.m_rule) + "\n";
			}
		}
		
	}
	GetNDTerm(index);
	(*cond).m_line = lastLine - 1;
	return result;
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
	for (list<NDTerm>::const_iterator p = conditions.begin();p!=conditions.end();++p)
	{
		++outside;
		if(((*p).m_status & LGC_FLAG_DIS) == LGC_FLAG_DIS)
		{
			continue;
		}
		int inside = -1;
		for (list<NDTerm>::const_iterator q = conditions.begin();q!=conditions.end();++q)
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

int NaturalDeduction::disable(int assume)
{
	// 	for (list<NDTerm>::iterator p = )
	// 	{
	// 	}
	// 	if ((conditions..m_status & LGC_FLAG_ASS) != LGC_FLAG_ASS)
	// 	{
	// 		return 0;
	// 	}
	// 	list<int>parent;
	// 	parent.push_back(assume);
	// 	conditions[assume].m_status |=LGC_FLAG_DIS;
	// 	for (int index = 0; index < conditions.size();index++)
	// 	{
	// 		if ((conditions[index].m_status&LGC_FLAG_DIS)==LGC_FLAG_DIS)
	// 		{
	// 			continue;
	// 		}
	// 		if ((find(parent.begin(),parent.end(),conditions[index].m_first)!= parent.end()) || (find(parent.begin(),parent.end(),conditions[index].m_second)!= parent.end()))
	// 		{
	// 			parent.push_back(index);
	// 			conditions[index].m_status |= LGC_FLAG_DIS;
	// 		}
	// 	}
	return 0;
}


int NaturalDeduction::GetNDTerm(int index)
{
	cond = conditions.begin();
	for (int i = 0; i < index;i++)
	{
		++cond;
	}
	return 0;
}


string NaturalDeduction::Result()
{	
	database.print();

	cout<<"----------------------------------------------------------------------\n\n\n";
	return GetString(proveds.back());
}
