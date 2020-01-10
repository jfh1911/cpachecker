//Sceletorn taken from  from https://www.geeksforgeeks.org/prefix-infix-conversion/ and modified to needs
// CPP Program to convert prefix to Infix
#include <iostream>
#include <stack>
#include "Converter.h"
using namespace std;
 namespace converter{
// function to check if character is operator or not
bool isOperator(char x) {
	switch (x) {
	case '+':
	case '-':
	case '/':
	case '*':
		return true;
	}
	return false;
}


//Taken from https://stackoverflow.com/questions/1494399/how-do-i-search-find-and-replace-in-a-standard-string
void replace(std::string &str, const std::string &oldStr,
		const std::string &newStr) {
	std::string::size_type pos = 0u;
	while ((pos = str.find(oldStr, pos)) != std::string::npos) {
		str.replace(pos, oldStr.length(), newStr);
		pos += newStr.length();
	}
}

// Convert prefix to Infix expression
string preToInfix(string pre_exp) {

	stack<string> s;

	// length of expression
	int length = pre_exp.size();

	// reading from right to left
	for (int i = length - 1; i >= 0; i--) {
		char currChar = pre_exp[i];
		if (isspace(currChar)) { //Ignore whitespace
			continue;
		}
		// check if symbol is operator
		if (isOperator(pre_exp[i])) {

			string temp = "( ";
			while (!s.empty()) {
				string op = s.top();
				s.pop();
				//Replace '-1*  by -
				replace(op, "-1*","- ");
				// concat the operands and operator
				temp += op + " " + pre_exp[i] + " ";
			}
			//remove the operand and the added whitespace
			temp = temp.substr(0, temp.size()-2);
			temp += " )";
			// Push string temp back to stack
			s.push(temp);
		}

		// if symbol is an operand
		else {

			//search for a whitespace and build operand
			string op = "";

			while (!isspace(currChar) ) {
				op = currChar + op;
				i = i - 1;
				currChar = pre_exp[i];
			}
			i = i + 1; //Since we
			s.push(op);
		}
	}

	// Stack now contains the Infix expression
	return "( "+s.top()+" )";
}
}
//// Driver Code
//int main() {
//	string pre_exp = "+  main@%x.0.i1  main@%y.0.i2  -1*main@%_1";
//	cout << "Infix : " << preToInfix(pre_exp);
//	return 0;
//}
