#include <iostream>
#include <fstream>

using namespace std;
int main(int argc, char **argv)
{
	if (argc != 4)
	{
		std::cout
			<< "usage: <prog> <IR file>  < path to c file> <path to exchange dir> <debug output(0=false, 1 = true>\n";
		return 1;
	}

	bool debug = argv[4] ;
	std::ifstream fin(argv[1]);

	std::ofstream myfile;
	std::string pathToFile = argv[3];
	pathToFile += "program.ll";
	myfile.open(pathToFile);

	std::string line = "";
	std::string rep = "";
	rep += '"';
	rep += argv[2];
	rep += '"';
	rep += ')';
	while (std::getline(fin, line))
	{

		if (line.find("!DIFile(filename:") != std::string::npos)
		{
			//Firstly, remove the directory in front of  the program name!
			std::string filename = "filename: \"";
			//Get posiiotn from where to replace/remove
			int startOfFilename = line.find(filename) + filename.size();
			//Check, if a "/" is present in the subsring "!1 = !DIFile(filename: "/seahorn/loop.c","
			std::string tempStr= line.substr(0,line.find(", directory: "));
			if(tempStr.find("/") != std::string::npos){
				int lengthOfPathToReplace = 	tempStr.find_last_of("/") - tempStr.find_first_of("\"");
				line = line.replace(startOfFilename, lengthOfPathToReplace, "");
			}
			int numCharsToRepl = line.find_last_of(")") - (line.find("directory: ") + 10);
			line = line.replace(line.find("directory: ") + 11, numCharsToRepl, rep);
			//!1 = !DIFile(filename: "/seahorn/loop.c", directory: "/home/phasar/Documents")
			myfile << line <<"\n";
			cout << line << "\n";
		} else{
			myfile << line << "\n";
		}
	}
	cout << "File prepared \n";
	fin.close();

	myfile.close();
	return 0;
}
