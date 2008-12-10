// NaturalDeduction.cpp: implementation of the NaturalDeduction class.
//
//////////////////////////////////////////////////////////////////////

#include "NaturalDeduction.h"
#include <algorithm>
#include <math.h>
//////////////////////////////////////////////////////////////////////
// Construction/Destruction
//////////////////////////////////////////////////////////////////////

NaturalDeduction::NaturalDeduction(TermVector t)
{
	database = t;
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

int NaturalDeduction::eliminate()
{

	list<NDTerm>::iterator p ;
	
	int added = 0;
	int arg1 = 0;
	int arg2 = 0;
	int outside = -1;
	int index;
	for (p = conditions.begin();p!=conditions.end();++p)
	{
		outside++;
		if ((*p).m_source & LGC_SRC_DISABLE == LGC_SRC_DISABLE)
		{
			continue;
		}
		NDTerm ndTerm;
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
					
					if (database.functions[arg1].m_kind == LGC_TERM_FUNC )
					{
						if (database.functions[arg1].m_ref == LGC_ADDR_NOT && ((*p).m_proceed & LGC_PRC_E_NOT) != LGC_PRC_E_NOT)
						{
							(*p).m_proceed |= LGC_PRC_E_NOT;
							arg2 = arg1 + 1;
							while (database.functions[arg2].m_kind == LGC_REF)
							{
								arg2 = database.functions[arg2].m_ref;
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
						while (database.functions[arg1].m_kind == LGC_REF)
						{
							arg1 = database.functions[arg1].m_ref;
						}

						ndTerm.m_index = arg1;
						ndTerm.m_rule = LGC_E_AND_1;
						ndTerm.m_first = outside;
						ndTerm.m_path = (*p).m_path + 1;
						ndTerm.m_derivation = outside;
						ndTerm.m_isPremise = (*p).m_isPremise;
						added += insertCondition(ndTerm,index);

						arg2 = main + 2;
						while (database.functions[arg2].m_kind == LGC_REF)
						{
							arg2 = database.functions[arg2].m_ref;
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
							if (isCompatible(left,arg1))
							{
								
								while (database.functions[arg2].m_kind == LGC_REF)
								{
									arg2 = database.functions[arg2].m_ref;
								}
								ndTerm.m_index = arg2;
								ndTerm.m_first = outside; 
								ndTerm.m_second = inside ; 
								ndTerm.m_path = (*p).m_path < (*leftOp).m_path ? (*p).m_path + 1 : (*leftOp).m_path + 1; 
								ndTerm.m_rule = LGC_E_MAP;
								ndTerm.m_derivation = outside;
								//cout<<(*p).m_isPremise << (*leftOp).m_isPremise;
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
			
		}
	}
	


	return added;
}

int NaturalDeduction::introduction()
{

	int subgoal = goals.back().m_index;
	int assume = -1;
	while (database.functions[subgoal].m_kind == LGC_REF)
	{
		subgoal = database.functions[subgoal].m_ref;
	}

	int arg1 = 0;
	int arg2 = 0;
	int status = goals.back().m_proceed;
	NDTerm t;
	int added = 0;
	if(database.functions[subgoal].m_info == 0)
	{
		if (database.functions[subgoal].m_kind == LGC_TERM_FUNC)
		{
			switch (database.functions[subgoal].m_ref)
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
					while (database.functions[arg1].m_kind == LGC_REF)
					{
						arg1 = database.functions[arg1].m_ref;
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
						while (database.functions[main].m_kind == LGC_REF)
						{
							main = database.functions[main].m_ref;
						}
						
						if (database.functions[main].m_info == 0)
						{	
							if (database.functions[main].m_kind == LGC_TERM_FUNC && database.functions[main].m_ref == LGC_ADDR_OR)
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
					while (database.functions[arg2].m_kind == LGC_REF)
					{
						arg2 = database.functions[arg2].m_ref;
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
						while (database.functions[main].m_kind == LGC_REF)
						{
							main = database.functions[main].m_ref;
						}
						
						if (database.functions[main].m_info == 0)
						{	
							if (database.functions[main].m_kind == LGC_TERM_FUNC && database.functions[main].m_ref == LGC_ADDR_OR)
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
					database.functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT));
					database.functions.push_back(Term(LGC_REF,subgoal));
					arg1 = database.functions.size() - 2;
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
					while (database.functions[arg1].m_kind == LGC_REF)
					{
						arg1 = database.functions[arg1].m_ref;
					}
					while (database.functions[arg2].m_kind == LGC_REF)
					{
						arg2 = database.functions[arg2].m_ref;
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
		while (database.functions[source].m_kind == LGC_REF)
		{
			source = database.functions[source].m_ref;
		}
		int arg1 = source + 1;
		int arg2 = source + 2;
		int status = (*p).m_proceed;
		NDTerm t;
		if (database.functions[source].m_info == 0 && database.functions[source].m_kind == LGC_TERM_FUNC)
		{
			switch (database.functions[source].m_ref)
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
					while (database.functions[arg1].m_kind == LGC_REF)
					{
						arg1 = database.functions[arg1].m_ref;
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
	while (!goals.empty())
	{
		debug(times++);
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
			getNDTerm(goals.back().m_assume);
			int subgoal = (*cond).m_index;
			int arg1 = subgoal + 1;
			while (database.functions[arg1].m_kind == LGC_REF)
			{
				arg1 = database.functions[arg1].m_ref;
			}
			NDTerm t;
			t.m_isPremise = false;
			t.m_path = (*cond).m_path + 1;
			t.m_index = arg1;
			t.m_source = LGC_SRC_ASSUME;
			t.m_derivation = goals.back().m_assume;
			int assume;
			insertCondition(t,assume);
			goals.back().m_source = LGC_SRC_CONCLUSION | LGC_SRC_OR_CONC ;
			goals.back().m_assume = assume;
			goals.back().m_derivation = assume;
			goals.back().m_OrGoal = assume;
		}

		else if ((goals.back().m_source & LGC_SRC_OR_SUB_2 ) == LGC_SRC_OR_SUB_2)
		{
			getNDTerm(goals.back().m_assume);
			int subgoal = (*cond).m_index;
			int arg2= subgoal + 2;
			while (database.functions[arg2].m_kind == LGC_REF)
			{
				arg2 = database.functions[arg2].m_ref;
			}
			NDTerm t;
			t.m_isPremise = false;
			t.m_index = arg2;
			t.m_source = LGC_SRC_ASSUME;
			t.m_derivation = goals.back().m_assume;
			int assume;
			insertCondition(t,assume);
			goals.back().m_source = LGC_SRC_CONCLUSION | LGC_SRC_OR_CONC ;
			goals.back().m_assume = assume;
			goals.back().m_derivation = assume;
			goals.back().m_OrGoal = assume;
		}

		if (goals.back().m_pendings > 0)
		{
			goals.back().m_proceed |= LGC_PRC_CONTR;
			
			getNDTerm(proveds.back());
			if ((*cond).m_index == LGC_ADDR_FALSE)
			{
				if (isReached(active))
				{
					proveds.pop_back();
					conditions.back().m_source |= LGC_SRC_DISABLE;
					proveds.push_back(active);
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
					getNDTerm(goals.back().m_third);
					(*cond).m_OrEnable = true;
					goals.back().m_rule = LGC_E_OR;
					//disable(goals.back().m_assume);
					goals.back().m_source |= LGC_SRC_DISABLE;
				}
				getNDTerm(goals.back().m_second);
				goals.back().m_isPremise = (*cond).m_isPremise;
			}
			conditions.push_back(goals.back());	
			if (goals.back().m_assume >= 0)
			{
				disable(goals.back().m_assume);
				
			}
			if ((goals.back().m_source & LGC_SRC_CONCLUSION) ==  LGC_SRC_CONCLUSION && goals.back().m_isPremise)
			{
				NDTerm id(goals.back().m_index,LGC_RULE_ID,conditions.size() -1);
				conditions.push_back(id);
			}
			
			proveds.push_back(conditions.size() - 1);
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
					disable(goals.back().m_assume);
					goals.pop_back();
					continue;
				}
			} 
			else if (isReached(active))
			{
				getNDTerm(active); 
				if ((goals.back().m_source & LGC_SRC_CONCLUSION) ==  LGC_SRC_CONCLUSION && (isDerived(active,goals.back().m_assume)))
				{
					NDTerm id((*cond).m_index,LGC_RULE_ID,active);
					id.m_assume = goals.back().m_assume;
					active = conditions.size();
					conditions.push_back(id);
				}
				if ((goals.back().m_source & LGC_SRC_OR_CONC ) == LGC_SRC_OR_CONC)
				{
					getNDTerm(active); 
					(*cond).m_derivation = goals.back().m_derivation;
				}
				proveds.push_back(active);
				disable(goals.back().m_assume);
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

			if (contradiction())
			{
				continue;
			}
			
			if ((goals.back().m_proceed & LGC_PRC_CONTR)!= 0)
			{
				goals.pop_back();
				continue;
			}
			if (NegIntrodution())
			{
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
	
		//database.print();
		cout <<++times<<"_________________________Conditions__________________________________\n";
		for (list<NDTerm>::iterator c = conditions.begin();c!=conditions.end();++c)
		{
			if(((*c).m_source&LGC_SRC_DISABLE)!= LGC_SRC_DISABLE )
			cout<<"\t"<<database.GetString((*c).m_index);
			else 
			cout<<"\t*"<<database.GetString((*c).m_index);
		}

		cout <<"\n_______________________________Goals__________________________________\n";
		for (list<NDTerm>::iterator g = goals.begin();g!=goals.end();++g)
		{
			cout<<"\t"<<database.GetString((*g).m_index);
		}
		
		cout <<"\n________________________________Proved________________________________\n";
		for (list<int>::iterator p = proveds.begin();p!=proveds.end();++p)
		{
			getNDTerm(*p);
			cout<<"\t"<<database.GetString((*cond).m_index);
		}
		cout<<"\n______________________________________________________________________\n\n\n";
		if (times == 9)
		{
			int dummy = 0;
		}
#endif
		

#if _DEBUG
	cout <<++times<<"_________________________Conditions__________________________________\n";
	int i = 0;
	for (c = conditions.begin();c!=conditions.end();++c)
	{
		cout<<(i++)<<"\t"<<"Index = "<<(*c).m_index<<"\tFirst = "<<(*c).m_first<<"\t Second = "<<(*c).m_second<<"\t Third = "<<(*c).m_third<<"\t Pending = "<<(*c).m_pendings<<"\t Assume = "<<(*c).m_assume<< endl; 
	}
	
	cout <<"\n_______________________________Goals__________________________________\n";
	for (g = goals.begin();g!=goals.end();++g)
	{
		cout<<"\t"<<database.GetString((*g).m_index);
	}
	
	cout <<"\n________________________________Proved________________________________\n";
	for (p = proveds.begin();p!=proveds.end();++p)
	{
		getNDTerm(*p);
		cout<<"\t"<<database.GetString((*cond).m_index);
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


int NaturalDeduction::getString(int index) 
{


	string result = "";
	getNDTerm(index);
	NDTerm goal = *cond;

	if(goal.m_line > 0)
	{
		return 0;
	}
	if (goal.m_third >= 0 )
	{
		
		getString(goal.m_third);
		
		getNDTerm(goal.m_second);
		NDTerm second = (*cond);
		getNDTerm(second.m_derivation);
		pLine pline2(second.m_derivation,lastLine,ifs++,"if   " , database.GetString((*cond).m_index));

		assumptions.push_back(lastLine);
		(*cond).m_line = lastLine++;
		lstpLines.push_back(pline2);
		getNDTerm(goal.m_second);
		(*cond).m_assume = -1;
		getString(goal.m_second);
		ifs--;
		lstpLines.back().m_indent--;
		lstpLines.back().m_assumption = "nif  ";
		
		

		getNDTerm(goal.m_first);
		NDTerm first = (*cond);
		
		getNDTerm(first.m_derivation);
		pLine pline1(first.m_derivation,lastLine,ifs++,"if   " , database.GetString((*cond).m_index));
		
		assumptions.push_back(lastLine);
		(*cond).m_line = lastLine++;
		lstpLines.push_back(pline1);
		getNDTerm(goal.m_first);
		(*cond).m_assume = -1;
		getString(goal.m_first);
		ifs--;
		lstpLines.back().m_indent--;
		lstpLines.back().m_assumption = "nif  ";
		

		pLine last(index,lastLine++,ifs,"",database.GetString(goal.m_index),rule2Str(goal.m_rule));
		assumptions.pop_back();
		
		getNDTerm(goal.m_third);
		last.m_third = (*cond).m_line;
		
		getNDTerm(goal.m_second);
		getNDTerm((*cond).m_derivation);
		last.m_second = (*cond).m_line;
		
		getNDTerm(goal.m_first);
		getNDTerm((*cond).m_derivation);
		last.m_first = (*cond).m_line;

		lstpLines.push_back(last);	

		
			

	}
	else if (goal.m_assume >= 0)
	{
		getNDTerm(goal.m_assume);
		pLine pline(goal.m_assume,lastLine,ifs++,"if   " , database.GetString((*cond).m_index));
		assumptions.push_back(lastLine);
		(*cond).m_line = lastLine++;
		lstpLines.push_back(pline);
		getString(goal.m_first);
		ifs--;
		lstpLines.back().m_indent--;
		lstpLines.back().m_assumption = "nif  ";
			
			
		pLine last(index,lastLine++,ifs,"",database.GetString(goal.m_index),rule2Str(goal.m_rule));
		assumptions.pop_back();
			
		getNDTerm(goal.m_assume);
		last.m_second = (*cond).m_line;
			
		getNDTerm(goal.m_first);
		last.m_first= (*cond).m_line;
			
		lstpLines.push_back(last);	
	}
	else
	{
		if(goal.m_pendings == 1)
		{
			
			getString(goal.m_first);
			pLine last(index, lastLine++,ifs,"",database.GetString(goal.m_index),rule2Str(goal.m_rule));
			getNDTerm(goal.m_first);
			last.m_first = (*cond).m_line;
			if (goal.m_isPremise && !assumptions.empty())
			{
				vector<pLine>::iterator p = lstpLines.begin();
				int min = assumptions.front();
				int max = lastLine ;
				int line = 1;
				last.m_line = min;
				last.m_indent = 0;
				for (;line < min;++line)
				{
					++p;	
				}
				p = lstpLines.insert(p,last);
				getNDTerm(index);
				(*cond).m_line = last.m_line;
				for (++line;line < max;++line)
				{
					++p;
					(*p).m_line++;
					getNDTerm((*p).m_index);
					(*cond).m_line++;
					if (((*p).m_first >= min && (*p).m_first <= max) )
					{
						(*p).m_first++;
					}
					if (((*p).m_second >= min && (*p).m_second <= max) )
					{
						(*p).m_second++;
					}
				}
				for (list<int>::iterator ass = assumptions.begin();ass!=assumptions.end();++ass)
				{
					(*ass)++;
				}
				return 0;
			}
			else
			{
				lstpLines.push_back(last);
			}
			

		}
		else if ( goal.m_pendings ==2)
		{
			getString(goal.m_second);
			getString(goal.m_first);
			pLine last(index, lastLine++,ifs,"",database.GetString(goal.m_index),rule2Str(goal.m_rule));
			getNDTerm(goal.m_second);
			last.m_second = (*cond).m_line;
			getNDTerm(goal.m_first);
			last.m_first = (*cond).m_line;
			if (goal.m_isPremise && !assumptions.empty())
			{
				vector<pLine>::iterator p = lstpLines.begin();
				int min = assumptions.front();
				int max = lastLine ;
				int line = 1;
				last.m_line = min;
				last.m_indent = 0;
				for (;line < min;++line)
				{
					++p;	
				}
				p = lstpLines.insert(p,last);
				getNDTerm(index);
				(*cond).m_line = last.m_line;
				for (++line;line < max;++line)
				{
					++p;
					(*p).m_line++;
					getNDTerm((*p).m_index);
					(*cond).m_line++;
					if (((*p).m_first >= min && (*p).m_first <= max) )
					{
						(*p).m_first++;
					}
					if (((*p).m_second >= min && (*p).m_second <= max) )
					{
						(*p).m_second++;
					}
				}
				for (list<int>::iterator ass = assumptions.begin();ass!=assumptions.end();++ass)
				{
					(*ass)++;
				}
				return 0;
			}
			else
			{
				lstpLines.push_back(last);
			}

		}
		else
		{
			if(goal.m_rule == LGC_RULE_PREMISE)
			{
				pLine last(index,lastLine++,ifs,"",database.GetString(goal.m_index),rule2Str(goal.m_rule));
				if (!assumptions.empty())
				{
					vector<pLine>::iterator p = lstpLines.begin();
					int min = assumptions.front();
					int max = lastLine ;
					int line = 1;
					last.m_line = min;
					last.m_indent = 0;
					for (;line < min;++line)
					{
						++p;	
					}
					p = lstpLines.insert(p,last);
					getNDTerm(index);
					(*cond).m_line = last.m_line;
					for (++line;line < max;++line)
					{
						++p;
						(*p).m_line++;
						getNDTerm((*p).m_index);
						(*cond).m_line++;
						if (((*p).m_first >= min && (*p).m_first <= max) )
						{
							(*p).m_first++;
						}
						if (((*p).m_second >= min && (*p).m_second <= max) )
						{
							(*p).m_second++;
						}
					
					}
					for (list<int>::iterator ass = assumptions.begin();ass!=assumptions.end();++ass)
					{
						(*ass)++;
					}
					return 0;
				}
				else
				{
					lstpLines.push_back(last);
				}
				
			}
			else if (goal.m_second == -1)
			{
				getString(goal.m_first);
				pLine last(index,lastLine++,ifs,"",database.GetString(goal.m_index),rule2Str(goal.m_rule));
				getNDTerm(goal.m_first);
				last.m_first = (*cond).m_line;
				if (goal.m_isPremise && !assumptions.empty())
				{
					vector<pLine>::iterator p = lstpLines.begin();
					int min = assumptions.front();
					int max = lastLine ;
					int line = 1;
					last.m_line = min;
					last.m_indent = 0;
					for (;line < min;++line)
					{
						++p;	
					}
					p = lstpLines.insert(p,last);
					getNDTerm(index);
					(*cond).m_line = last.m_line;
					for (++line;line < max;++line)
					{
						++p;
						(*p).m_line++;
						getNDTerm((*p).m_index);
						(*cond).m_line++;
						if (((*p).m_first >= min && (*p).m_first <= max) )
						{
							(*p).m_first++;
						}
						if (((*p).m_second >= min && (*p).m_second <= max) )
						{
							(*p).m_second++;
						}
					}
					for (list<int>::iterator ass = assumptions.begin();ass!=assumptions.end();++ass)
					{
						(*ass)++;
					}
					return 0;
				}
				else
				{
					lstpLines.push_back(last);
				}
				
			}
			else
			{
				getString(goal.m_second);
				getString(goal.m_first);
				pLine last(index,lastLine++,ifs,"",database.GetString(goal.m_index),rule2Str(goal.m_rule));
				getNDTerm(goal.m_second);
				last.m_second = (*cond).m_line;
				getNDTerm(goal.m_first);
				last.m_first = (*cond).m_line;
				if (goal.m_isPremise && !assumptions.empty())
				{
					vector<pLine>::iterator p = lstpLines.begin();
					int min = assumptions.front();
					int max = lastLine ;
					int line = 1;
					last.m_line = min;
					last.m_indent = 0;
					for (;line < min;++line)
					{
						++p;	
					}
					p = lstpLines.insert(p,last);
					getNDTerm(index);
					(*cond).m_line = last.m_line;
					for (++line;line < max;++line)
					{
						++p;
						(*p).m_line++;
						getNDTerm((*p).m_index);
						(*cond).m_line++;
						if (((*p).m_first >= min && (*p).m_first <= max) )
						{
							(*p).m_first++;
						}
						if (((*p).m_second >= min && (*p).m_second <= max) )
						{
							(*p).m_second++;
						}
					}
					for (list<int>::iterator ass = assumptions.begin();ass!=assumptions.end();++ass)
					{
						(*ass)++;
					}
					return 0;
				}
				else
				{
					lstpLines.push_back(last);
				}
				
			}
		}
		
	}
	getNDTerm(index);
	(*cond).m_line = lastLine - 1;
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
			if (((*p).m_first == last) || ((*p).m_second == last))
			{
				(*p).m_source |= LGC_SRC_DISABLE;
				{
					if (find(passed.begin(),passed.end(),index)==passed.end())
					{
						parents.push_back(index);
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
	if (assume ==1 )
	{
		debug(10);
	}
	return 0;
}


int NaturalDeduction::getNDTerm(int index)
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
	getString(proveds.back());
	//Arrange it
	string s = "";
	int max = 0;
	for (int i = 0; i < lstpLines.size(); i++)
 	{
		s = pLine2Str(lstpLines[i]) +"\n";
		if (max < s.length())
		{
			max =  s.length();
		}
 	}
	s = "";
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
	return  ToStringX(result + " ",4);
}

int NaturalDeduction::isDerived(int child, int parent)
{
	if(child == parent)return 1;
	list<int>parents;
	list<int>passed;
	parents.push_back(parent);
	while (!parents.empty())
	{
		int last = parents.back();
		passed.push_back(last);
		parents.pop_back();
		int index = child - 1;
		getNDTerm(child);
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
	
	int arg1 = 0;
	int arg2 = 0;
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
				case LGC_ADDR_OR:
					if ((*p).m_OrEnable)
					{
						(*p).m_OrEnable = false;
						goals.back().m_source |= LGC_SRC_OR_GOAL;
						goals.back().m_pendings = 2;
						//goals.back().m_derivation  = outside;
						//goals.back().m_assume = outside;
						//goals.back().m_OrGoal = outside;
						goals.back().m_third = outside;
						ndTerm.m_source = LGC_SRC_OR_SUB_2;
						ndTerm.m_derivation = outside;
						ndTerm.m_assume = outside;
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
	while (database.functions[subgoal].m_kind == LGC_REF)
	{
		subgoal = database.functions[subgoal].m_ref;
	}

	int arg1 = 0;
	int arg2 = 0;
	int status = goals.back().m_proceed;
	NDTerm t;
	int added = 0;
	if(database.functions[subgoal].m_info == 0)
	{
		if (database.functions[subgoal].m_kind == LGC_TERM_FUNC)
		{
			switch (database.functions[subgoal].m_ref)
			{
			case LGC_ADDR_NOT:
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
		while (database.functions[source].m_kind == LGC_REF)
		{
			source = database.functions[source].m_ref;
		}
		int arg1 = source + 1;
		int arg2 = source + 2;
		int status = (*p).m_proceed;
		NDTerm t;
		if (database.functions[source].m_info == 0 && database.functions[source].m_kind == LGC_TERM_FUNC)
		{
			switch (database.functions[source].m_ref)
			{

			case LGC_ADDR_NOT:
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
#if _DEBUG
	
	//database.print();
	cout <<++times<<"_________________________Conditions__________________________________\n";
	for (list<NDTerm>::iterator c = conditions.begin();c!=conditions.end();++c)
	{
		if(((*c).m_source&LGC_SRC_DISABLE)!= LGC_SRC_DISABLE )
			cout<<"\t"<<database.GetString((*c).m_index);
		else 
			cout<<"\t*"<<database.GetString((*c).m_index);
	}
	
	cout <<"\n_______________________________Goals__________________________________\n";
	for (list<NDTerm>::iterator g = goals.begin();g!=goals.end();++g)
	{
		cout<<"\t"<<database.GetString((*g).m_index);
	}
	
	cout <<"\n________________________________Proved________________________________\n";
	for (list<int>::iterator p = proveds.begin();p!=proveds.end();++p)
	{
		getNDTerm(*p);
		cout<<"\t"<<database.GetString((*cond).m_index);
	}
	cout<<"\n______________________________________________________________________\n\n\n";
	if (times == 11)
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
	vector<Term>::const_iterator proposition = database.variables.begin(); 
	int added = 0;
	int prop = -1;
	for (;proposition != database.variables.end(); ++proposition)
	{
		prop++;
		if ((*proposition).m_kind == LGC_TERM_PROP && database.names.GetString((*proposition).m_ref) != "*1")
		{
			database.functions.push_back(Term(LGC_TERM_PROP,prop));
			database.functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_NOT));
			database.functions.push_back(Term(LGC_REF,database.functions.size() - 2));
			database.functions.push_back(Term(LGC_TERM_FUNC,LGC_ADDR_OR));
			database.functions.push_back(Term(LGC_REF,database.functions.size()-4));
			database.functions.push_back(Term(LGC_REF,database.functions.size()-4));
			NDTerm lem(database.functions.size()-3,LGC_RULE_LEM);
			lem.m_path = 1;
			lem.m_source |= LGC_SRC_LEM;
			conditions.push_back(lem);
			added++;
		}
	}
	isInsert = true;
	return added;
}
