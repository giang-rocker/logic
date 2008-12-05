#include <sstream>
#include <string>
using namespace std;

template <class T>
inline std::string ToString (const T& t)
{
	std::stringstream ss;
	ss << t;
	return ss.str();
}

template <class T>
inline std::string ToStringX (const T& t,int width, int align = 0)
{
	std::stringstream ss;
	ss.width(width);
	ss << t;
	return ss.str();
}
struct pLine 
{
	pLine(int line, int indent, string assump, string content, string rule = "", int first = -1, int second = -1 )
	{
		m_line = line;
		m_indent = indent;
		m_assumption = assump;
		m_content = content;
		m_rule = rule;
		m_first=  first;
		m_second = second;
	}
	string ToString(int max = 0)
	{
		string s = "";
		//s +=  ToStringX(ToString(m_line)+".",4) ;
		//s += ToStringX("",m_indent * 4) ;
		//s += m_assumption ;
		//s += ToStringX(m_content,max) ;
		//s += m_rule;
		if (m_first > -1)
		{
			s += " " + ToString(m_first);
		}
		if (m_second > -1)
		{
			s += "," + ToString(m_second);
		}
		return s;
	}
	int m_line;
	int m_indent;
	string m_assumption;
	string m_content;
	string m_rule;
	int m_first;
	int m_second;
	
};

inline std::string pLine2Str(const pLine& p, int max)
{
	string s = "";
	s += ToStringX(ToString(p.m_line)+".",4) ;
	s += ToStringX("",p.m_indent * 4) ;
	s += p.m_assumption + " ";
	s += ToStringX(p.m_content,max)+"\t\t\t\t" ;
	s += p.m_rule + " ";
	if (p.m_second > -1)
	{
		s += " " + ToString(p.m_second) + ",";
	}
	if (p.m_first > -1)
	{
		s += ToString(p.m_first);
	}
	return s;
}