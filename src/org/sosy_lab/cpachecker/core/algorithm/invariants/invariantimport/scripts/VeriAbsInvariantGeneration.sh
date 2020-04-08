# Usage:
# $1 = path to the file to generate invariant for
# $2 = path to the output directory to store generated invariants to
# $3 = path to the dir where the scripts are located
# $4 = path to the veriabs script directory

echo $4veriabs "--property-file " $3unreach-call.prp $1
$4veriabs --property-file  $3unreach-call.prp $1 > /dev/null 2>&1

#Copy the invariant file to $2
echo cp witness.graphml $2
cp witness.graphml $2


