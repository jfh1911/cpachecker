# Usage:
# $1 = path to the file to generate invariant for
# $2 = path to the output directory to store generated invariants to

abs_path_to_seahorn_exchange_dir=~/Documents/seahorn/output/
name_of_Docker=inspiring_lalande

echo $1
echo $2

cd ~/Documents/seahorn

#preprcoess the c file given as argument
echo "Prepare file $1 for parsing"
./prepare_c_file_for_seahorn $1 ${abs_path_to_seahorn_exchange_dir}
echo "File is pepared for seahorn and stored at ${abs_path_to_seahorn_exchange_dir}"

# start the docker
 docker start $name_of_Docker
 
#docker execute the invariant generation
echo "Starting seahorn invariant generation"
docker exec  -w /seahorn/  $name_of_Docker sh startSeahorn.sh /seahorn/output/
echo "The invariant generation is finished" 
cat ${abs_path_to_seahorn_exchange_dir}invariants.txt
docker stop $name_of_Docker

#Copy the invariant file to $2
cp ${abs_path_to_seahorn_exchange_dir}invariants.txt $2
cp ${abs_path_to_seahorn_exchange_dir}out.ll $2
cp ${abs_path_to_seahorn_exchange_dir}program.c $2

# Transform the llvm ll file (modify the path to the source file
./transform_llvm_file $2/out.ll $2 $2

# Parse the invariants to c
 ./transform_invariants  $2program.ll $2invariants.txt $2

# Cleanup
rm ${abs_path_to_seahorn_exchange_dir}invariants.txt 
rm ${abs_path_to_seahorn_exchange_dir}out.ll 
rm ${abs_path_to_seahorn_exchange_dir}program.c 
