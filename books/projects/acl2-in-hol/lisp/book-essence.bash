#!/bin/bash

if [ $# -eq 2 ] ; then \
    export outfile="\"$2\"" ;\
elif [ $# -eq 1 ] ; then \
    export outfile="" ;\
else \
    echo "Usage: $0 infile [outfile]" ;\
    exit 1 ;\
fi

export tmpfile=/tmp/workxxx
export infile="\"$1\""

rm -f $tmpfile

echo "(include-book " '"'"${ACL2_HOL_LISP}/book-essence"'")' > $tmpfile
echo "(book-essence $infile $outfile)" >> $tmpfile
echo "(value :q) (quit)" >> $tmpfile

${ACL2} < $tmpfile
