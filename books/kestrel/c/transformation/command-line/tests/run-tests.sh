set -e # Stop on errors

OS=`uname -s`
echo "OS is $OS."

# Note that the first test takes longer because we have to save an image

rm -f split-gso.output/*.*
../transform-c.sh split-gso.json
rm -f split-gso-no-extensions.output/*.*
../transform-c.sh split-gso-no-extensions.json
rm -f simpadd0.output/*.*
../transform-c.sh simpadd0.json
rm -f split-fn.output/*.*
../transform-c.sh split-fn.json
../transform-c.sh split-fn2.json
../transform-c.sh split-fn3.json
rm -f wrap-fn.output/*.*
../transform-c.sh wrap-fn.json
rm -f add-section-attr.output/*.*
if [ ${OS} == "Darwin" ]; then
    ../transform-c.sh add-section-attr-mac.json
    ../transform-c.sh add-section-attr2-mac.json
else
    ../transform-c.sh add-section-attr.json
    ../transform-c.sh add-section-attr2.json
fi

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

cd split-gso-no-extensions.output
gcc -O0 -c *.c
echo "Results in split-gso-no-extensions.output:"
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

cd add-section-attr.output
gcc -O0 -c *.c
echo "Results in add-section-attr.output:"
ls -l *.c
ls -l *.o
cd ..
