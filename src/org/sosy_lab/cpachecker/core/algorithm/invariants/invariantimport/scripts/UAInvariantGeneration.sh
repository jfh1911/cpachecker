# Usage:
# $1 = path to the file to generate invariant for
# $2 = path to the output directory to store generated invariants to
# $3 = path to the dir where the scripts are located

echo python lib/UAutomizer-linux/Ultimate.py --spec $3unreach-call.prp --architecture 32bit --witness-dir $2 --file $1  
cd lib/UAutomizer-linux/
pwd
python Ultimate.py --spec $3unreach-call.prp --architecture 32bit --witness-dir $2 --file $1  > /dev/null 2>&1

