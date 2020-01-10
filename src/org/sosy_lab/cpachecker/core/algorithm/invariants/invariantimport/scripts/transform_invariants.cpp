#include <cxxabi.h>
#include <iostream>
#include <llvm/IR/CallSite.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DebugLoc.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
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
#include <boost/algorithm/string/predicate.hpp>
#include <typeinfo>
#include "Converter.h"
#include <set>

using namespace llvm;
using namespace std;

std::string PREFIX = "main@";
std::string DELIMITOR = "\n";

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

//Taken from https://stackoverflow.com/questions/1494399/how-do-i-search-find-and-replace-in-a-standard-string
void replace(std::string &str, const std::string &oldStr,
		const std::string &newStr) {
	std::string::size_type pos = 0u;
	while ((pos = str.find(oldStr, pos)) != std::string::npos) {
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

int main(int argc, char **argv) {
	if (argc != 4) {
		std::cout << "usage: <prog> <IR file> <OutPut Seahorn> <Dir to output files>\n";
		return 1;
	}
	// parse an IR file into an LLVM module
	llvm::SMDiagnostic Diag;
	std::unique_ptr<llvm::LLVMContext> C(new llvm::LLVMContext);
	std::unique_ptr<llvm::Module> M = llvm::parseIRFile(argv[1], Diag, *C);
	// check if the module is alright
	bool broken_debug_info = false;
	if (llvm::verifyModule(*M, &llvm::errs(), &broken_debug_info)) {
		llvm::errs() << "error: module not valid\n";
		return 1;
	}
	if (broken_debug_info) {
		llvm::errs() << "caution: debug info is broken\n";
	}
	auto F = M->getFunction("main");
	if (!F) {
		llvm::errs() << "error: could not find function 'main'\n";
		return 1;
	}
	llvm::outs() << "iterate instructions of function: '" << F->getName()
			<< "'\n";
	llvm::outs() << "of file " << M->getSourceFileName() << "\n";

	map<string, string> foundVars;
	map<string, string> blocksToScrLines;

	for (BasicBlock &BB : *F) {
		string srcLineOfBasicBlock = "";
		bool isLast = false;
		for (llvm::Instruction &I : BB) {

			if (auto branch = llvm::dyn_cast<llvm::BranchInst>(&I)) {
				isLast = true;
				for (unsigned i = 0; i < branch->getNumSuccessors(); i++) {
					if (branch->getSuccessor(i) == &BB) {
						srcLineOfBasicBlock =
								psr::llvmInstructionToOnlySrcCodeLine(&I);
					}
				}
			} else {
				isLast = false;
			}

			std::string sourceStr = psr::llvmInstructionToSrc(&I, false);
			if (boost::starts_with(sourceStr, "Var") || (&I)->getName() != "") {
				std::string llvmVarName = getLlvmName(&I);

				if (boost::starts_with(sourceStr, "Var")) {
					std::string cVarName = getNameForSourceVar(sourceStr);
					foundVars[llvmVarName] = cVarName;
				} else if (llvm::PHINode *phi = llvm::dyn_cast<llvm::PHINode>(
						&I)) {
					bool alreadyDef = false;
					for (auto &Operand : (&I)->operands()) {
						std::string llvmOpname = getLlvmName(Operand);
						std::string sourceStrOp = psr::llvmValueToSrc(Operand,
								true);
						if (sourceStrOp != "No source information available!") {
							string opVarName = getNameForSourceVar(sourceStrOp);
							//Check if the source var is used in a previous def:
							bool defUsed = false;
							for (auto const &e : foundVars)
								if (e.second.compare(opVarName) == 0) {
									defUsed = true;
								}
							if (!defUsed && !alreadyDef) {
								alreadyDef = true;
								foundVars[llvmVarName] = opVarName;
							} else if (!defUsed && alreadyDef) {
								//the Var is having two definitions, cannot decide (maybe with more complex logic ) --> Hence abort
								cout
										<< "An error occurred! There are more than one valid variable assignments for a variable.";
								return 1;
							}
						}
					}
				}

			}
		}
		//if the first node is a phi node, check if the block is a loop body.
		//THerefore, check if the last statement is a jump containing the block as one target
		if (isLast && srcLineOfBasicBlock != "") {
			blocksToScrLines[PREFIX + BB.getName().str()] = srcLineOfBasicBlock;
		} else {
			//If no loop structure, just use the first non phi nod of the block
			blocksToScrLines[PREFIX + BB.getName().str()] =
					psr::llvmInstructionToOnlySrcCodeLine(BB.getFirstNonPHI());
		}
	}

//Next, identify the location, where the invariants belong to:

//Next, read and parse the generated invariant

	std::ifstream infile(argv[2]);

	std::string line;
	bool isMainFunc = false;
	set<string> invariants;

	while (!infile.eof()) {
		//Currently only look at invariants for the main method
		if (boost::starts_with(line, "Function: main")) {
			isMainFunc = true;
		} else if (boost::starts_with(line, "Function:")) {
			isMainFunc = false;
		} else if (isMainFunc) {
			//Firstly, load the invariant for that location
			string currentInv = "";
			currentInv = currentInv.append(line);
			//remove lading whitespace and tabs
			line.erase(0, line.find_first_not_of(" \t"));
			//Check, if the next line contains  a new  invariant, denoted by a location staring with main and a ":" to denote the location
			while (std::getline(infile, line)) {
				if (!(boost::starts_with(line, "main")
						&& line.find(':') != string::npos)) {
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
	map<string, string> locToInv;

	for (string e : invariants) {

		//Now, parse the invariants:
		//Location --> Everythin between 0 and the first colon include
		string invLoc = e.substr(0, e.find_first_of(':'));
		e = e.erase(0, e.find_first_of(':'));
		//1: find the invariants, each clause is put in "( ... )"
		if (e.find('(') != string::npos) {
			string conjunction = "";
			while (e.find_first_of('(') != string::npos) {
				//check, if [] are present, than split the expression at () and []

				auto expr = e.substr(e.find_first_of('('),
						e.find_first_of(')'));
				e = e.erase(e.find_first_of('('), e.find_first_of(')'));
				if (expr.find_first_of('[') != string::npos) {
					//LHS = expr without []
					auto lhs = expr.substr(expr.find_first_of('[') + 1,
							expr.find_first_of(']') - 2); // -2, since -1 for pos of ] and -1 to remove them
					auto lhsInInfix = converter::preToInfix(lhs);

					expr.replace(expr.find_first_of('['),
							expr.find_first_of(']') - expr.find_first_of('[')
									+ 1, lhsInInfix);

				}
				conjunction = conjunction.append(expr);
				conjunction += "&&";
			}

			locToInv[invLoc] = conjunction.substr(0, conjunction.size() - 2);
		} else {
			locToInv[invLoc] = e;
		}
	}

	//prefix the variables with "main@"
	map<string, string> prefixedVars;
	for (auto const &e : foundVars) {
		//remove two leading and one following whitespace
		string temp = PREFIX + e.first.substr(2, e.first.size() - 3);
		prefixedVars[temp] = e.second;
	}
//	cout << "The mapping of llvm blocks to C surce code lines  is:\n";
//	for (auto const &e : blocksToScrLines) {
//		cout << e.first << "<-->" << e.second << "\n";
//	}

////	//NEXT, REPLACE THE LLVM VAR NAMES WITH THE C VAR NAMES

	map<string, string> updatedInvs;
	for (auto const &en : locToInv) {
		string replacedinv = en.second;
		for (auto const &foundvar : prefixedVars) {
			replace(replacedinv, foundvar.first, foundvar.second);
		}
		updatedInvs[en.first] = replacedinv;
	}

	cout << "\n\n";
	cout
			<< "Mapping of Source locations (including main@entry and main@exit) <-> invariant in C syntax \n";
	for (auto const &en : updatedInvs) {
		if (blocksToScrLines.count(en.first) > 0
				&& blocksToScrLines[en.first] != "") {
			cout << blocksToScrLines[en.first] << "<->" << en.second << "\n";
		} else {
			cout << en.first << "<->" << en.second << "\n";
		}
	}

	//Write the output to the file
	std::ofstream myfile;
	std::string fileName = argv[3];
	fileName +="/invars_in_c.txt";
	myfile.open(fileName);

	myfile
			<< "Mapping of Source locations (including main@entry and main@exit) <-(represented by a newline)-> invariant in C syntax \n";
	for (auto const &en : updatedInvs) {
		if (blocksToScrLines.count(en.first) > 0
				&& blocksToScrLines[en.first] != "") {
			myfile << blocksToScrLines[en.first] << DELIMITOR << en.second
					<< "\n";
		} else {
			myfile << en.first << DELIMITOR << en.second << "\n";
		}
	}

	myfile.close();

	llvm::llvm_shutdown();
	return 0;

}
