# Usage:
# $1 = path to the file to generate invariant for
# $2 = path to the output directory to store generated invariants to
# $3 = path to the dir where the scripts are located

echo python3 Ultimate.py --spec $3unreach-call.prp --architecture 32bit --witness-dir $2   --full-output --file $1  > /dev/null 2>&1
cd lib/UAutomizer-linux/
python3 Ultimate.py --spec $3unreach-call.prp --architecture 32bit --witness-dir $2  --full-output --file $1  > /dev/null 2>&1

