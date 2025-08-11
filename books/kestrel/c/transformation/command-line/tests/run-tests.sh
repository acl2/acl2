set -e # Stop on errors

rm -f splitgso.output/*.*
../transform-c.sh splitgso.json
rm -f simpadd0.output/*.*
../transform-c.sh simpadd0.json
rm -f split-fn.output/*.*
../transform-c.sh split-fn.json

# cd input-files
# gcc -O0 -c *.c
# ls *.o
# cd ..

cd splitgso.output
gcc -O0 -c *.c
echo "Results in splitgso.output:"
ls -l *.c
ls -l *.o
cd ..

cd simpadd0.output
gcc -O0 -c *.c
echo "Results in simpadd0.output:"
ls -l *.c
ls -l *.o
cd ..

cd split-fn.output
gcc -O0 -c *.c
echo "Results in split-fn.output:"
ls -l *.c
ls -l *.o
cd ..
