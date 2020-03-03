#include <cxxabi.h>
#include <iostream>
#include <llvm/IR/CallSite.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DebugLoc.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/IR/User.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Support/SMLoc.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/raw_ostream.h>

#include <memory>
#include "LLVMIRToSrc.h"
#include <fstream>
#include <sstream>
#include <string>
#include <typeinfo>
#include "Converter.h"
#include <set>

using namespace llvm;
using namespace std;

std::string PREFIX = "main@";
std::string DELIMITOR = "\n";

bool debug = true;
//taken from : https://stackoverflow.com/questions/4654636/how-to-determine-if-a-string-is-a-number-with-c
bool is_number(const std::string &s) {
	std::string::const_iterator it = s.begin();
	while (it != s.end() && std::isdigit(*it))
		++it;
	return !s.empty() && it == s.end();
}

std::string cxx_demangle(const std::string &mangled_name) {
	int status = 0;
	char *demangled = abi::__cxa_demangle(mangled_name.c_str(), NULL, NULL,
			&status);
	std::string result(
			(status == 0 && demangled != NULL) ? demangled : mangled_name);
	free(demangled);
	return result;
}

std::string getNameForSourceVar(std::string str) {
	return str.substr(str.find("Var : ") + 6, str.find("\nLine:") - 6);
}

int isOperator(char &c) {
	const char *matches = "()[]{}|&+-*/<>=!% \n\t";
	return (strchr(matches, c) != NULL);
}

//Taken from https://stackoverflow.com/questions/1494399/how-do-i-search-find-and-replace-in-a-standard-string
void replace(std::string &str, const std::string &oldStr,
		const std::string &newStr) {
	std::string::size_type pos = 0;
	while ((pos = str.find(oldStr, pos)) != std::string::npos
			&& isOperator(str[pos + oldStr.length()])) {
		str.replace(pos, oldStr.length(), newStr);
		pos += newStr.length();
	}
}

std::string getLlvmName(Value *inst) {
	std::string type_str;
	llvm::raw_string_ostream rso(type_str);
	inst->print(rso);
	std::string s = rso.str();
	std::string llvmVarName = s.substr(0, s.find('='));
	llvmVarName = llvmVarName.substr(llvmVarName.find(' '));
	rso.flush();
	return llvmVarName;

}

llvm::Instruction* getFirstNonPhiAndNonTailCall(llvm::BasicBlock &BB) {
	for (llvm::Instruction &I : BB) {
		std::string lineStr = "";
		llvm::raw_string_ostream rso(lineStr);
		I.print(rso);
		//Check if the statement is an variabpredecessorsle assignment (needed to parse the variables of the invariant)
		if (auto phi = llvm::dyn_cast<llvm::PHINode>(&I)) {
			continue;
		} else if (lineStr.find("tail call void") != string::npos) {
			continue;
		} else {
			return &I;
		}
	}
	return BB.getFirstNonPHI();
}

void computeVarMappingAndSrcCodeMapping(map<string, string> &foundVars,
		map<string, set<string> > &blocksToScrLines, Function *F) {
	for (BasicBlock &BB : *F) {
		string srcLineOfBasicBlock = "";

		//Now, this is a workatound. I assume that if a basic block has more than one predecessor and the last statement of
		//all predecessors points to the same source code location, and the source code location contains the keyword "for"
		//or while" indicating looop, than we can additionally add this srcCodLoc to the block
		string srcCodeLine = "";
		int i = 0;
		for (BasicBlock *Pred : llvm::predecessors(&BB)) {
			i++;
			//Find the last statement of the block
			Instruction *last;
			for (Instruction &I : *Pred) {
				last = &I;
			}
			if (srcCodeLine == "") {
				srcCodeLine = psr::llvmInstructionToOnlySrcCodeLine(last);
			} else if (srcCodeLine
					!= psr::llvmInstructionToOnlySrcCodeLine(last)) {
				srcCodeLine = "";
				break;
			}
		}
		bool isLoopHead = srcCodeLine.find("while") != string::npos
				|| srcCodeLine.find("for") != string::npos;
		if (srcCodeLine != "" && i > 1 && isLoopHead) {
			//All predecessors associate the jump statement to same location, hence add the sourcecodeline to this location
			set<string> values;
			values.insert(srcCodeLine);
			cout << "Adding at Pos 1:" << PREFIX + BB.getName().str() << "<~~>"
					<< srcCodeLine << "\n";
			blocksToScrLines[PREFIX + BB.getName().str()] = values;
		}

		bool isLast = false;
		for (llvm::Instruction &I : BB) {
			//Check if the current statement is the last of the block and a branch instance.
			if (auto branch = llvm::dyn_cast<llvm::BranchInst>(&I)) {
				isLast = true;
				//				cout << BB.getName().str() << ":  \n";
				//				TODO: Test if this leads to better performance (ignoring, where the last branch is going to
				//				for (unsigned i = 0; i < branch->getNumSuccessors(); i++) {
				//					if (branch->getSuccessor(i) == &BB) {
				srcLineOfBasicBlock = psr::llvmInstructionToOnlySrcCodeLine(&I);
				//					}
				//				}
				//				cout << "line to that is: " <<srcLineOfBasicBlock << "\n";
			} else {
				isLast = false;
			}
			std::string sourceStr = psr::llvmInstructionToSrc(&I, false);
			//Check if the statement is an variable assignment (needed to parse the variables of the invariant)
			if (sourceStr.find("Var") == 0 || (&I)->getName() != "") {
				std::string llvmVarName = getLlvmName(&I);
				if (sourceStr.find("Var") == 0) {
					std::string cVarName = getNameForSourceVar(sourceStr);
					foundVars[llvmVarName] = cVarName;
				} else if (llvm::PHINode *phi = llvm::dyn_cast<llvm::PHINode>(
						&I)) {
					bool alreadyDef = false;
					bool allPhiVarsHaveSameValue = true;
					//To tackle the case where all phi nodes point to the same variable, use varDefOfPhiNodes
					string varDefOfPhiNodes = "";
					for (auto &Operand : (&I)->operands()) {
						std::string llvmOpname = getLlvmName(Operand);
						std::string sourceStrOp = psr::llvmValueToSrc(Operand,
								true);

						if (sourceStrOp != "No source information available!") {
							string opVarName = getNameForSourceVar(sourceStrOp);

							//Check if the source var is used in a previous def:
							bool defUsed = false;
							for (const auto &e : foundVars) {
								if (e.second.compare(opVarName) == 0) {
									defUsed = true;
								}
							}
							if (!defUsed && !alreadyDef) {
								alreadyDef = true;
								foundVars[llvmVarName] = opVarName;
								break;
							} else if (!defUsed && alreadyDef) {
								//the Var is having two definitions, cannot decide (maybe with more complex logic ) --> Hence abort
								cout
										<< "An error occurred! There are more than one valid variable assignments for a variable.";
								//return 1;
							} else if (!alreadyDef && defUsed) {
								//CHeck if all phi vars are equal
								if (varDefOfPhiNodes.size() == 0) {
									//Is first phi var
									varDefOfPhiNodes = opVarName;
								} else {
									//Check if this phi var is not equal to first one, than abort
									if (varDefOfPhiNodes != opVarName) {
										allPhiVarsHaveSameValue = false;
									}
								}
							}
						}
					}
					foundVars[llvmVarName] = varDefOfPhiNodes;
				} else {
					//The variable is probalby an intermediate variable.
					//Hence, check if it is arithmetic operation of two variables that are known

					//TODO: Extend to -,*,/

					if (llvm::BinaryOperator *bin = llvm::dyn_cast<
							llvm::BinaryOperator>(&I)) {

						I.print(outs());
						outs() << "-" << I.getOpcode() << "--"
								<< bin->getNumOperands() << "\n";
						if (bin->getNumOperands() == 2) {
							llvm::Value *lhs = bin->getOperand(0);
							std::string lhsVarName = getLlvmName(lhs);
							llvm::Value *rhs = bin->getOperand(1);
							std::string rhsVarName = getLlvmName(rhs);
							std::string varName = getLlvmName(&I);

//							lhs->print(outs());
//							outs() << "--->" << lhsVarName << "\n";
//							rhs->print(outs());
//							outs() << "--->" << rhsVarName << "\n";
//							outs() << "--------------------------------------\n";
							string opSymbol;
							if (I.getOpcode() == 11) {
								opSymbol = "+";
							} else if (I.getOpcode() == 15) {
								opSymbol = "+";
							} else {
								break;
							}

							if (foundVars.count(lhsVarName) >= 1
									&& foundVars.count(rhsVarName) >= 1) {
								foundVars[varName] = foundVars[lhsVarName]
										+ opSymbol + foundVars[rhsVarName];
							}
						}
					}
				}

			}
		}
		//check if the block is a loop body.
		//THerefore, check if the last statement is a jump containing the block as one target
		set<string> lines;

		if (blocksToScrLines.find(PREFIX + BB.getName().str())
				== blocksToScrLines.end()) {
//			lines = blocksToScrLines[PREFIX + BB.getName().str()]; //TODO: Comment out /remove
//		} //else {
			std::__cxx11::string loc = psr::llvmInstructionToOnlySrcCodeLine(
					getFirstNonPhiAndNonTailCall(BB));
			if (isLast && srcLineOfBasicBlock != "") {
				if (lines.find(srcLineOfBasicBlock) == lines.end()) {
					cout << "Adding at Pos 2:" << PREFIX + BB.getName().str()
							<< "<~~>" << srcCodeLine << "\n";
					lines.insert(srcLineOfBasicBlock);
				} else if (lines.find(loc) == lines.end()) { //TODO Prob. better as else-if
					lines.insert(loc);
					cout << "Adding at Pos 3:" << PREFIX + BB.getName().str()
							<< "<~~>" << loc << "\n";
				}
				blocksToScrLines[PREFIX + BB.getName().str()] = lines;
			} else {
				//If no loop structure, just use the first non phi node of the block
				if (lines.find(loc) == lines.end()) {
					lines.insert(loc);
					cout << "Adding at Pos 4:" << PREFIX + BB.getName().str()
							<< "<~~>" << loc << "\n";
				}
				blocksToScrLines[PREFIX + BB.getName().str()] = lines;
			}
			//}
		}
	}
}

string replaceAllOccurences(string expression, const string &toReplace,
		const string &replacement) {
	size_t start_pos = 0;
	while ((start_pos = expression.find(toReplace, start_pos))
			!= std::string::npos) {
		expression.replace(start_pos, toReplace.size(), replacement);
		start_pos += replacement.size();
	}
	return expression;
}

string trimEnd(string expression) {
	if (expression.find_last_of(' ') == expression.size() - 1) {
		return trimEnd(expression.substr(0, expression.size() - 1));
	}
	return expression;
}

set<string> collectInvats(char **argv) {
//	for (pair<string, string> e : foundVars) {
//		cout << e.first << " <-> " << e.second << "\n";
//	}
//Next, identify the location, where the invariants belong to:
//Next, read and parse the generated invariant
	std::ifstream infile(argv[2]);
	std::string line;
	bool isMainFunc = false;
	set<string> invariants;
	while (!infile.eof()) {
		//Currently only look at invariants for the main method
		if (line.find("Function: main") == 0) {
			isMainFunc = true;
		} else if (line.find("Function:") == 0) {
			isMainFunc = false;
		} else if (isMainFunc) {
			//Firstly, load the invariant for that location
			string currentInv = "";
			currentInv = currentInv.append(line);
			//remove lading whitespace and tabs
			line.erase(0, line.find_first_not_of(" \t"));
			//Check, if the next line contains  a new  invariant, denoted by a location staring with main and a ":" to denote the location
			while (std::getline(infile, line)) {
				if (!(line.find("main") == 0 && line.find(':') != string::npos)) {
					currentInv = currentInv.append(line);
				} else {
					break;
				}
			}
			currentInv.erase(
					std::remove(currentInv.begin(), currentInv.end(), '\t'),
					currentInv.end());
			invariants.insert(currentInv);
			continue;
		}

		std::getline(infile, line);
	}
	return invariants;
}

int main(int argc, char **argv) {
	if (argc != 4) {
		std::cout
				<< "usage: <prog> <IR file> <OutPut Seahorn> <Dir to output files>\n";
		return 1;
	}
// parse an IR file into an LLVM module
	llvm::SMDiagnostic Diag;
	unique_ptr<LLVMContext> C(new LLVMContext);
	unique_ptr<Module> M = parseIRFile(argv[1], Diag, *C);
// check if the module is alright
	bool broken_debug_info = false;
	if (llvm::verifyModule(*M, &llvm::errs(), &broken_debug_info)) {
		llvm::errs() << "error: module not valid\n";
		return 1;
	}
	if (broken_debug_info) {
		llvm::errs() << "caution: debug info is broken\n";
	}
	Function *F = M->getFunction("main");
	if (!F) {
		llvm::errs() << "error: could not find function 'main'\n";
		return 1;
	}
//	llvm::outs() << "iterate instructions of function: '" << F->getName()
//			<< "'\n";
//	llvm::outs() << "of file " << M->getSourceFileName() << "\n";

	map<string, string> foundVars;
	map<string, set<string>> blocksToScrLines;
	computeVarMappingAndSrcCodeMapping(foundVars, blocksToScrLines, F);

//	for (pair<string, string> e : foundVars) {
//		cout << e.first << " <-> " << e.second << "\n";
//	}

//Next, identify the location, where the invariants belong to:

//Next, read and parse the generated invariant

	set<string> invariants = collectInvats(argv);
	set<string> replacedInv;
//next, replace all occurences of "mod2" and "mod3"
	for (string invar : invariants) {
		if (invar.find("mod2") != string::npos) {
			invar = replaceAllOccurences(invar, "mod2", "%2 ");
		}
		if (invar.find("mod3") != string::npos) {
			invar = replaceAllOccurences(invar, "mod3", "%3 ");
		}
		replacedInv.insert(invar);
	}

//	for (string e : replacedInv) {
//		cout << e << "\n";
//	}

//Now, parse the invariants
	map<string, string> locToInv;
	for (string e : replacedInv) {

		//Now, parse the invariants:
		//Location --> Everything between 0 and the first colon include
		string invLoc = e.substr(0, e.find_first_of(':'));

		e = e.erase(0, e.find_first_of(':'));
		//1: find the invariants, each clause is put in "( ... )"
		if (e.find('(') != string::npos) {
			string conjunction = "";

			//Parse the expression by finding all outer-most  "(...)(...)",.
			int outMostOpeningBracketAt = -1;
			int countOpeningBrackets = 0;
			string expression;

			for (string::size_type i = 0; i < e.size(); i++) {
				char c = e[i];
				if (c == '(') {
					//Increase counter for opening brackets and mark outermost opening bracket if not set
					if (outMostOpeningBracketAt == -1) {
						outMostOpeningBracketAt = i;
					}
					countOpeningBrackets++;
				} else if (c == ')') {
					//Decrease counter for opening brackets
					countOpeningBrackets--;
					if (countOpeningBrackets == 0) {
						//Check if outermost closing bracket is found, than construct subexpression and check for inner '[' or ']'
						//the subexpression is: start from position of outermost opening bracket and has i - outMostOpeningBracket
						//many chars (since last not inculdet +1)
						expression = e.substr(outMostOpeningBracketAt,
								i - outMostOpeningBracketAt + 1);

						//Check, if "-" is present and replace it by -
						expression = replaceAllOccurences(expression, "-1*",
								"-");
						//check, if [] are present; if so replace the prefix notation by infix notation
						if (expression.find_first_of('[') != string::npos) {
							//LHS = expr without []
//							cout << " Expression is: " << expression << "\n";
							auto lhs = expression.substr(
									expression.find_first_of('[') + 1);
							lhs = lhs.substr(0, lhs.find_first_of(']'));// -2, since -1 for pos of ] and -1 to remove them
//							cout << lhs << "\n";

							//To avoid problems with whitespaces in the end, remove them
							lhs = trimEnd(lhs);

							auto lhsInInfix = converter::preToInfix(lhs);
							expression.replace(expression.find_first_of('['),
									expression.find_first_of(']')
											- expression.find_first_of('[') + 1,
									lhsInInfix);
						}

						conjunction = conjunction.append(expression);
						if (i < e.size() - 1) {
							conjunction += " & ";
						}
						outMostOpeningBracketAt = -1;

					}
				}
			}

			locToInv[invLoc] = conjunction.substr(0, conjunction.size());

		} else {
			//To remove the leading ":"
			locToInv[invLoc] = e.substr(1, e.length());
		}
	}
//prefix the variables with "main@"
	map<string, string> prefixedVars;
	for (auto const &e : foundVars) {
		//remove two leading and one following whitespace
		string temp = PREFIX + e.first.substr(2, e.first.size() - 3);
		prefixedVars[temp] = e.second;
	}

//NEXT, REPLACE THE LLVM VAR NAMES WITH THE C VAR NAMES

	map<string, string> updatedInvs;
	for (auto const &en : locToInv) {
		string replacedinv = en.second;
//		cout << "Replacing:   " << en.second << "\n";
		for (auto const &foundvar : prefixedVars) {

			replace(replacedinv, foundvar.first, foundvar.second);
//			cout << "replaced to :" << replacedinv <<" using "  <<foundvar.first << " ++ "<< foundvar.second<< " \n";
		}
		updatedInvs[en.first] = replacedinv;
	}

	cout << "\n\n";
	cout
			<< "Mapping of Source locations (including main@entry and main@exit) <-> invariant in C syntax \n";
	for (auto const &en : updatedInvs) {
		if (blocksToScrLines.count(en.first) > 0) {
			for (string srcCodeStr : blocksToScrLines[en.first]) {
				if (srcCodeStr != "") {
					cout << srcCodeStr << "<->" << en.second << "\n";
				} else {
					cout << en.first << "<->" << en.second << "\n";
				}
			}
		} else {
			cout << en.first << "<->" << en.second << "\n";
		}
	}

//Write the output to the file
	std::ofstream myfile;
	std::string fileName = argv[3];
	fileName += "invars_in_c.txt";
	myfile.open(fileName);
	myfile
			<< "Mapping of Source locations (including main@entry and main@exit) <-> invariant in C syntax \n";
	for (auto const &en : updatedInvs) {
		if (blocksToScrLines.count(en.first) > 0) {
			for (string srcCodeStr : blocksToScrLines[en.first]) {
				if (srcCodeStr != "") {
					myfile << srcCodeStr << DELIMITOR << en.second << "\n";
				} else {
					myfile << en.first << DELIMITOR << en.second << "\n";
				}
			}
		} else {
			myfile << en.first << DELIMITOR << en.second << "\n";
		}
	}

	myfile.close();

	llvm::llvm_shutdown();
	return 0;

}
