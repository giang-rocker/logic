#include <string>
#include <iostream>
#include "../Analyser/Scanner.h"
#include "../Parser/Parser.h"
#include "../NaturalDeduction/NaturalDeduction.h"
using namespace std;

extern "C" __declspec (dllexport) char* inferencer(char* text)
{
	string str (text);
	string result;
	
	Scanner* scanner = new Scanner(str);
	Parser* p = new Parser(scanner);
	p->parse();
	if ( p->s != "")
	{
		result = p->s;
	}
	else
	{
		
		NaturalDeduction nd(p->data);
		//p->data.print();
		if(nd.ProveIt())
			result = nd.Result();
		else
			result = " Cannot prove ";	
	}	
	char* cstr = new char [result.size()+1];
	strcpy (cstr, result.c_str());
	return cstr;
}