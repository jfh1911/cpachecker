#!/usr/bin/python

import sys
import benchmark.runexecutor as runexecutor

def main(argv=None):
    if argv is None:
        argv = sys.argv

    if(len(argv) >= 5):
        args = argv[1]
        memlimit = int(argv[2])
        timelimit = int(argv[3])
        outputFileName = argv[4]

        rlimits={"memlimit":memlimit, "timelimit":timelimit}
        print args
        print rlimits
        print outputFileName
        
        (wallTime, cpuTime, returnvalue, output) = runexecutor.executeRun(args, rlimits, outputFileName);

        print wallTime
        print cpuTime
        print returnvalue
        print output

        result = args + "\n"
        result = result + "Walltime: " + str(wallTime) + "\n"
        result = result +  "CpuTime: " + str(wallTime) + "\n"
        result = result + "Returnvalue: " + str(returnvalue) + "\n"
        result = result + "\n"        
        result = result + "Output:\n" + output

        print result

        fobj = open(outputFileName, "w")
        fobj.write(result)
        fobj.close()

    else:
        print "Help todo"


if __name__ == "__main__":
    main()
