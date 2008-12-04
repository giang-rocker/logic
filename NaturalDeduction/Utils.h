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