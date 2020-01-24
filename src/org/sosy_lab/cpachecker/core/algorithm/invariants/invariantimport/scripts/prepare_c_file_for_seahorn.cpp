#include <iostream>
#include <fstream>
#include <boost/algorithm/string/replace.hpp>

using namespace std;
int main(int argc, char **argv)
{
    if (argc != 3)
    {
        std::cout
            << "usage: <prog> <c file> < path to exchange dir> \n";
        return 1;
    }

    std::ifstream fin(argv[1]);

    std::ofstream myfile;
    std::string pathToFile = argv[2];
	pathToFile += "/program.c";
	myfile.open(pathToFile);

    //Add the needed include
 //   myfile << "#include \"seahorn/seahorn.h\"\n";

   // string toReplace1 = "extern void __VERIFIER_error() __attribute__ ((__noreturn__));";
   // string replacement1 = "extern void __VERIFIER_error() {\n";
  //  replacement1 += "printf(\"[sea] __VERIFIER_error was executd\");\n";
   // replacement1 += "exit(1);\n";
   // replacement1 += "}";

   // string toReplace2 = "__VERIFIER_assert";
//    string replacement2 = "sassert";
 //       string toNotReplace2 ="void __VERIFIER_assert(";


    string line;

    while (getline(fin, line))
    {
 //       if (line.find(toReplace1) != std::string::npos)
  //      {
 //           myfile << replacement1 << '\n';
  //      }
   //     else  if (line.find(toReplace2) != std::string::npos && line.find(toNotReplace2) == std::string::npos) 
 //       {
//               boost::replace_all(line, toReplace2, replacement2);
  //             myfile  << line << '\n';   
   //     } else
    //    {
            myfile << line << '\n';
     //   }
        
    }
    fin.close();

    myfile.close();
    return 0;
}
