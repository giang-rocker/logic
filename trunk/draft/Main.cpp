#include <iostream.h>
#include "Data.h"


void main()
{
	
	Data d;
	//Building p(x,y), q(X) AND h(y,k(l)) -> r(M) 
	d.BeginTerm();
	d.BeginPredicate("p");
	d.BeginArg();
	d.NewConstVar("x",LGC_VAR);
	d.EndArg();
	d.BeginArg();
	d.NewConstVar("y",LGC_VAR);
	d.EndArg();
	d.EndPredicate();
	d.EndTerm();
	

	d.BeginTerm();
	d.BeginPredicate("q");
	d.BeginArg();
	d.NewConstVar("X",LGC_CONST);
	d.EndArg();
	d.EndPredicate();
	
	d.Operator(LGC_AND_OP);
	
	d.BeginPredicate("h");
	d.BeginArg();
	d.NewConstVar("y",LGC_VAR);
	d.EndArg();
	d.BeginArg();
	d.BeginPredicate("k");
	d.BeginArg();
	d.NewConstVar("l",LGC_VAR);
	d.EndArg();
	d.EndPredicate();
	d.EndArg();
	d.EndPredicate();
	
	d.Operator(LGC_MAP_OP);
	d.BeginPredicate("r");
	d.BeginArg();
	d.NewConstVar("M",LGC_CONST);
	d.EndArg();
	d.EndPredicate();
	d.EndTerm();
	
	d.print();
	
}


