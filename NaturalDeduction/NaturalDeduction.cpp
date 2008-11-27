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
}



bool NaturalDeduction::isCompatible(int father, int son)
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
			return database.variables[r1].m_info >= database.variables[r2].m_info;
		case LGC_TERM_FUNC:
			if(r1 == r2)
			{
				if (database.functions[son].m_info > 0  || database.functions[father].m_info > 0)
				{
					//Unification process
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


	//////////////////////////////////////////////////////////////////////////
	////////////////////////////////////Eliminate NOT/////////////////////////
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
						int agr2 = arg1+1;
						while (database.functions[agr2].m_kind == LGC_REF)
						{
							agr2 = database.functions[agr2].m_ref;
						}
						NDTerm ndT(agr2,false,(*p).m_index,left,LGC_E_MODUS);
						condition.push_back(ndT);
						mdMarked.push_back((*p).m_index);
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
						int agr2 = arg1+1;
						while (database.functions[agr2].m_kind == LGC_REF)
						{
							agr2 = database.functions[agr2].m_ref;
						}
						NDTerm ndT(agr2,false,(*p).m_index,left,LGC_E_MODUS);
						condition.push_back(ndT);
						mdMarked.push_back((*p).m_index);
					}
					
				}
				
			}
		}
		
	}
	//////////////////////////////////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////////////
	
	return 0;
}

int NaturalDeduction::Introduction()
{
	return 0;
}

int NaturalDeduction::Contradiction()
{
	return 0;
}

int NaturalDeduction::print()
{
	database.print();
	cout<<"----------------------------------------------------------------\n";
	for (list<NDTerm>::const_iterator p = condition.begin(); p != condition.end();++p )
	{
		cout<< (*p).m_index <<endl;
	}
	return 0;
}