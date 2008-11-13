#include <iostream.h>
#include "Data.h"


void main()
{
	
	Data d;

	//Building p(x,y), q(X) AND NOT h(y,k(l)) -> r(M) 
	d.BeginTerm();
	d.BeginPredicate("p");
	d.BeginArg();
	d.NewConstVar("x",LGC_VAR_TERM);
	d.EndArg();
	d.BeginArg();
	d.NewConstVar("y",LGC_VAR_TERM);
	d.EndArg();
	d.EndPredicate();
	d.EndTerm();
	

	d.BeginTerm();
	d.BeginPredicate("q");
	d.BeginArg();
	d.NewConstVar("X",LGC_CONST_TERM);
	d.EndArg();
	d.EndPredicate();
	
	d.LogicOp(LGC_AND_OP);
	d.LogicOp(LGC_OR_OP);

	d.BeginPredicate("h");
	d.BeginArg();
	d.NewConstVar("y",LGC_VAR_TERM);
	d.EndArg();
	d.BeginArg();
	d.BeginPredicate("k");
	d.BeginArg();
	d.NewConstVar("l",LGC_VAR_TERM);
	d.EndArg();
	d.EndPredicate();
	d.EndArg();
	d.EndPredicate();
	
	d.LogicOp(LGC_MAP_OP);
	d.BeginPredicate("r");
	d.BeginArg();
	d.NewConstVar("M",LGC_CONST_TERM);
	d.EndArg();
	d.EndPredicate();
	d.EndTerm();
	
	d.print();
	
}


