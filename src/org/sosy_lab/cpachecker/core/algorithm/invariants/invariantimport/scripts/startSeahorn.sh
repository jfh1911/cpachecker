# Usage: $1 = Path to the folder INSINDE the seahorn docker exchange folder used
# for storing and loading files. The path needs to work in the docker image
# run seahorn 
sea smt --solve --show-invars -g --oll=$1out.ll $1program.c >$1invariants.txt
cat $1invariants.txt

exit
