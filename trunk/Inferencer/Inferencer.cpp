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
		xWam l = p->data;
		NaturalDeduction nd(p->data);
		if(nd.ProveIt())
			result = nd.Result();
		else
		{
			xWam de = l;
			NaturalDeduction lem(l);
			lem.insertLEMs();
			if (lem.ProveIt())
			{
				result = lem.Result();
			}
			else
			{
				NaturalDeduction morgan(de);
				morgan.EnableDeMorgan = true;
				if (morgan.ProveIt())
				{
					result = lem.Result();
				}
				else
				{
					result = "Cannot SOLVE...";

				}
				
			}
		}
				
	}	
	char* cstr = new char [result.size()+1];
	strcpy (cstr, result.c_str());	

	return cstr;
}
