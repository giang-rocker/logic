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
	list<int>::const_iterator p = t.goals.begin();
	for (;p!=t.goals.end();++p)
	{

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

	if (database.functions[son].m_kind != database.functions[father].m_kind)
	{
		return false;
	}

	int r1 = database.functions[father].m_ref;
	int r2 = database.functions[son].m_ref;
	switch (database.functions[father].m_kind)
	{
	case LGC_TERM_PROP:
		return r1 == r2;

	case LGC_TERM_CONST:
		return database.variables[r1].m_info >= database.variables[r2].m_info;

	case LGC_TERM_FUNC:
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
	return false;
}

int NaturalDeduction::Eliminate()
{
	
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
