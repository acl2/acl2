#!/bin/bash

if [ $# -eq 1 ] ; then \
    export outfile="\"$1\"" ;\
elif [ $# -eq 0 ] ; then \
    set outfile = "" ;\
else \
    echo "Usage: $0 [outfile]" ;\
    exit 1 ;\
fi

export tmpfile=/tmp/workxxx

rm -f $tmpfile

echo "(include-book " '"'"${ACL2_HOL_LISP}/book-essence"'")' > $tmpfile
echo "(axioms-essence $outfile)" >> $tmpfile
echo "(value :q) (quit)" >> $tmpfile

${ACL2} < $tmpfile
