#include <iostream>
#include "Analyser/Scanner.h"
#include "Parser/Parser.h"
using namespace std;

int main()
{


		TermVector lgc;
		//Building p(x,y), q(X) AND NOT all x exist y (h(y,k(l)) -> r(M)) 
		lgc.BeginSentence();
		lgc.NewVar("P",LGC_TERM_CONST);
		lgc.NewLogicOp(LGC_OP_AND);
		lgc.NewVar("Q",LGC_TERM_CONST);
		lgc.EndSentence();
		lgc.print();
	return 0;
	
}