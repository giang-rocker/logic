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
		condition.push_back(NDTerm(*p));
	}
	for (p = t.goals.begin();p!=t.goals.end();++p)
	{
		goal.push_back(NDTerm(*p));
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

	list<NDTerm>::const_iterator p ;
	

	//////////////////////////////////////////////////////////////////////////
	////////////////////////////////Eliminate AND/////////////////////////////
	int added = 0;
	for (p = condition.begin();p!=condition.end();++p)
	{
		int next = (*p).m_index;
		while (database.functions[next].m_kind == LGC_REF)
		{
			next = database.functions[next].m_ref;
		}

		if (database.functions[next].m_kind == LGC_TERM_FUNC && database.functions[next].m_ref == database.addrAND)
		{
			if (find(andMarked.begin(),andMarked.end(),next) == andMarked.end())
			{
				andMarked.push_back((*p).m_index);
				added++;
				//Create 2 NDTerms
				int sub = next + 1;
				while (database.functions[sub].m_kind == LGC_REF)
				{
					sub = database.functions[sub].m_ref;
				}
				NDTerm ndT(sub,false,next,0,LGC_E_AND_1);
				condition.push_back(ndT);

				sub = next + 2;
				while (database.functions[sub].m_kind == LGC_REF)
				{
					sub = database.functions[sub].m_ref;
				}
				ndT.m_index = sub;
				ndT.m_rule = LGC_E_AND_2;
				condition.push_back(ndT);
			}
		}
	}


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////Eliminate NOT///////////////////////////
	for (p = condition.begin();p!=condition.end();++p)
	{
		int next = (*p).m_index;
		while (database.functions[next].m_kind == LGC_REF)
		{
			next = database.functions[next].m_ref;
		}
	
		if (database.functions[next].m_kind == LGC_TERM_FUNC && database.functions[next].m_ref == database.addrNOT)
		{

			next++;
			while (database.functions[next].m_kind == LGC_REF)
			{
				next = database.functions[next].m_ref;
			}

			if (database.functions[next].m_kind == LGC_TERM_FUNC && database.functions[next].m_ref == database.addrNOT)
			{
				if (find(notMarked.begin(),notMarked.end(),(*p).m_index) == notMarked.end())
				{
					notMarked.push_back((*p).m_index);
					added++;
					int sub = next + 1;
					while (database.functions[sub].m_kind == LGC_REF)
					{
						sub = database.functions[sub].m_ref;
					}
					NDTerm ndT(sub,false,(*p).m_index,0,LGC_E_NOT);
					condition.push_back(ndT);
				}
			}
		}
	}


	//////////////////////////////////////////////////////////////////////////
	////////////////////////////////////Eliminate Modus///////////////////////
	for (p = condition.begin();p!=condition.end();++p)
	{
		int next = (*p).m_index;
		while (database.functions[next].m_kind == LGC_REF)
		{
			next = database.functions[next].m_ref;
		}
		
		if (database.functions[next].m_kind == LGC_TERM_FUNC && database.functions[next].m_ref == database.addrMAP)
		{
			if (find(mdMarked.begin(),mdMarked.end(),next) == mdMarked.end())
			{
				mdMarked.push_back((*p).m_index);
				int arg1 = next + 1;
				while (database.functions[arg1].m_kind == LGC_REF)
				{
					arg1 = database.functions[arg1].m_ref;
				}
				//Searching compatible elements
				list<NDTerm>::const_iterator leftOp = condition.begin();
				for (;leftOp!=condition.end();++leftOp)
				{
					int left = (*leftOp).m_index;
					while (database.functions[left].m_kind == LGC_REF)
					{
						left = database.functions[left].m_ref;
					}

					if (isCompatible(left,arg1))
					{
						int agr2 = next+1;
						while (database.functions[agr2].m_kind == LGC_REF)
						{
							agr2 = database.functions[agr2].m_ref;
						}
						NDTerm ndT(agr2,false,(*p).m_index,left,LGC_E_MODUS);
						condition.push_back(ndT);
						mdMarked.push_back((*p).m_index);
						added++;
					}

				}

			}
		}
			
	}

	//////////////////////////////////////////////////////////////////////////
	///////////////////////////////////OR Eliminate///////////////////////////
	for (p = condition.begin();p!=condition.end();++p)
	{
		int next = (*p).m_index;
		while (database.functions[next].m_kind == LGC_REF)
		{
			next = database.functions[next].m_ref;
		}
		
		if (database.functions[next].m_kind == LGC_TERM_FUNC && database.functions[next].m_ref == database.addrOR)
		{

			// A v B , not(A) -> B
			if (find(or1Marked.begin(),or1Marked.end(),next) == or1Marked.end())
			{
				int arg1 = next + 1;
				while (database.functions[arg1].m_kind == LGC_REF)
				{
					arg1 = database.functions[arg1].m_ref;
				}
				//Searching compatible elements
				list<NDTerm>::const_iterator leftOp = condition.begin();
				for (;leftOp!=condition.end();++leftOp)
				{
					int left = (*leftOp).m_index;
					if (left == next)
					{
						continue;	
					}
					while (database.functions[left].m_kind == LGC_REF)
					{
						left = database.functions[left].m_ref;
					}
					if (isComplement(arg1,left))
					{
						int agr2 = next+1;
						while (database.functions[agr2].m_kind == LGC_REF)
						{
							agr2 = database.functions[agr2].m_ref;
						}
						NDTerm ndT(agr2,false,(*p).m_index,left,LGC_E_OR_1);
						condition.push_back(ndT);
						or1Marked.push_back((*p).m_index);
						added++;
					}
					
				}
				
			}
			
		// A v B , not(B) -> A	
		if (find(or2Marked.begin(),or2Marked.end(),next) == or2Marked.end())
			{
				int arg2 = next + 2;
				while (database.functions[arg2].m_kind == LGC_REF)
				{
					arg2 = database.functions[arg2].m_ref;
				}
				//Searching compatible elements
				list<NDTerm>::const_iterator leftOp = condition.begin();
				for (;leftOp!=condition.end();++leftOp)
				{
					int left = (*leftOp).m_index;
					while (database.functions[left].m_kind == LGC_REF)
					{
						left = database.functions[left].m_ref;
					}
					if (isComplement(arg2,left))
					{
						int agr1 = next+1;
						while (database.functions[agr1].m_kind == LGC_REF)
						{
							agr1 = database.functions[agr1].m_ref;
						}
						NDTerm ndT(agr1,false,(*p).m_index,left,LGC_E_OR_2);
						condition.push_back(ndT);
						or2Marked.push_back((*p).m_index);
						added++;
					}
					
				}
				
			}
			

		}
		
		
	}
	
	//////////////////////////////////////////////////////////////////////////
	///////////////////////////Eliminate Exists///////////////////////////////
	

	//////////////////////////////////////////////////////////////////////////
	///////////////////////////Eliminate All//////////////////////////////////

	return added;
}

int NaturalDeduction::Introduction(int subgoal)
{
	
	while (database.functions[subgoal].m_kind == LGC_REF)
	{
		subgoal = database.functions[subgoal].m_ref;
	}
	if(database.functions[subgoal].m_info == 0)
	{
		cout<<"Dispose:"<<goal.back().m_index<<endl;
		goal.pop_back();

		if (database.functions[subgoal].m_kind == LGC_TERM_FUNC)
		{
			 int addr = database.functions[subgoal].m_ref;
			 // A |- NOT F => A, F |- F, FALSE
			 if (addr == database.addrNOT)
			 {
				cout<<"Dispose:"<<goal.back().m_index<<endl;
				goal.pop_back();
				goal.push_back(NDTerm(database.functions.size()));
				database.functions.push_back(Term(LGC_TERM_FALSE));
				subgoal++;
				while (database.functions[subgoal].m_kind == LGC_REF)
				{
					subgoal = database.functions[subgoal].m_ref;
				}
				condition.push_back(subgoal);
				return 1;
			 } 
			// A |- P ^ Q => A |- P,Q
			 else if (addr == database.addrAND)
			 {
				cout<<"Dispose:"<<goal.back().m_index<<endl;
				goal.pop_back();
				int arg1 = subgoal + 1;
				int arg2 = subgoal + 2;

				while (database.functions[arg1].m_kind == LGC_REF)
				{
					arg1 = database.functions[arg1].m_ref;
				}

				while (database.functions[arg2].m_kind == LGC_REF)
				{
					arg2 = database.functions[arg2].m_ref;
				}
				goal.push_back(NDTerm(arg1));
				goal.push_back(NDTerm(arg2));
				return 1;
			 }
			// A |- P v Q => A |- P or A |- Q or A ,not(P v Q) |- P v Q , FALSE 
			 else if (addr == database.addrOR)
			 {
				cout<<"Dispose:"<<goal.back().m_index<<endl;
				goal.pop_back();
				int arg;
				switch (intro)
				{
				case 3:
					arg = subgoal + 1 ;
					while (database.functions[arg].m_kind == LGC_REF)
					{
						arg = database.functions[arg].m_ref;
					}
					goal.push_back(NDTerm(arg));
					intro = 3;
					return 3;
					
				case 4:
					arg = subgoal + 2 ;
					while (database.functions[arg].m_kind == LGC_REF)
					{
						arg = database.functions[arg].m_ref;
					}
					goal.pop_back();
					goal.push_back(NDTerm(arg));
					intro = 1;
					break;

				case 5:
					database.functions.push_back(Term(LGC_TERM_FUNC,database.addrNOT,0));
					database.functions.push_back(Term(LGC_REF,subgoal));
					condition.push_back(NDTerm(database.functions.size() - 2));
					database.functions.push_back(Term(LGC_TERM_FALSE));
					goal.push_back(database.functions.size()-1);
					break;
				}

			 }
			 //  |- P->Q => P|-Q
			 else if (addr == database.addrMAP)
			 {
				int arg1 = subgoal + 1;
				int arg2 = subgoal + 2;
				cout<<"Dispose:"<<goal.back().m_index<<endl;
				goal.pop_back();
				while (database.functions[arg1].m_kind == LGC_REF)
				{
					arg1 = database.functions[arg1].m_ref;
				}
				
				while (database.functions[arg2].m_kind == LGC_REF)
				{
					arg2 = database.functions[arg2].m_ref;
				}
				
				condition.push_back(NDTerm(arg1));
				goal.push_back(NDTerm(arg2));
			 }
			 else
			 {
				 database.functions.push_back(Term(LGC_TERM_FUNC,database.addrNOT,0));
				 database.functions.push_back(Term(LGC_REF,subgoal));
				 condition.push_back(NDTerm(database.functions.size() - 2));
				 database.functions.push_back(Term(LGC_TERM_FALSE));
				 goal.push_back(database.functions.size()-1);
			 }

		}
	}
	else
	{
		
	}
	return 0;
}

int NaturalDeduction::Contradiction()
{

	return 0;
}

int NaturalDeduction::print()
{
	database.print();
	cout<<"--------------------------CONDITIONS---------------------------------\n";
	for (list<NDTerm>::const_iterator p = condition.begin(); p != condition.end();++p )
	{
		cout<< (*p).m_index <<endl;
	}
	cout<<"----------------------------GOALS-----------------------------------\n";
	for (p = goal.begin(); p != goal.end();++p )
	{
		cout<< (*p).m_index <<endl;
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

	if (database.functions[neg].m_kind == LGC_TERM_FUNC && database.functions[neg].m_ref == database.addrNOT)
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
	while (!goal.empty())
	{
		//print();
		if (isReached(goal.back().m_index))
		{
			cout<<"\nReached "<<goal.back().m_index<<endl;
			goal.pop_back();
			continue;
		}
		else
		{
			bool applied = false;
			while (Eliminate() > 0)
			{
				applied = true;
			}
			if (applied)
			{
				continue;
			}
			while (Introduction(goal.back().m_index) > 0)
			{
				applied = true;
			}
			if (!applied)
			{
				return 0;
			}
		}
		
	}
	return 0;
}

int NaturalDeduction::isReached(int subgoal)
{
	if (database.functions[subgoal].m_kind == LGC_TERM_FALSE)
	{
	
	}
	else
	{
		for (list<NDTerm>::const_iterator p = condition.begin(); p!= condition.end();++p)
		{
			if (isCompatible((*p).m_index,subgoal))
			{
				return 1;
			}
		}
	}
	return 0;
}
