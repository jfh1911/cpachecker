# Usage:
# $1 = path to the file to generate invariant for
# $2 = path to the output directory to store generated invariants to
# $3 = path to the dir where the scripts are located

echo python3 Ultimate.py --spec $3unreach-call.prp --architecture 32bit --witness-dir $2   --full-output --file $1  > $2log.txt
cd lib/UAutomizer-linux/
pwd
python3 Ultimate.py --spec $3unreach-call.prp --architecture 32bit --witness-dir $2  --full-output --file $1  > $2log.txt
cat $2log.txt
#> /dev/null 2>&1

