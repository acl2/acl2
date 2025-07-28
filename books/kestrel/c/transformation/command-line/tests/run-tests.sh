set -e # Stop on errors

rm -f splitgso.output/*.*
../transform-c.sh splitgso.json
rm -f simpadd0.output/*.*
../transform-c.sh simpadd0.json

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
