set -e # Stop on errors

rm -f split-gso.output/*.*
../transform-c.sh split-gso.json
rm -f simpadd0.output/*.*
../transform-c.sh simpadd0.json
rm -f split-fn.output/*.*
../transform-c.sh split-fn.json
../transform-c.sh split-fn2.json
../transform-c.sh split-fn3.json
rm -f wrap-fn.output/*.*
../transform-c.sh wrap-fn.json

# cd input-files
# gcc -O0 -c *.c
# ls *.o
# cd ..

cd split-gso.output
gcc -O0 -c *.c
echo "Results in split-gso.output:"
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

cd wrap-fn.output
gcc -O0 -c *.c
echo "Results in wrap-fn.output:"
ls -l *.c
ls -l *.o
cd ..
