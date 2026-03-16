#!/bin/bash

if [ $# -eq 3 ] ; then \
    export outfile="\"$3\"" ;\
elif [ $# -eq 2 ] ; then \
    export outfile="" ;\
else \
    echo "Usage: $0 infile [outfile]" ;\
    exit 1 ;\
fi

# Suggestion from perplexity.ai:
export SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

export tmpfile=${SCRIPT_DIR}/workxxx-book-essence-${1}

export infile="\"$2\""

rm -f $tmpfile

echo "(include-book " '"'"${ACL2_HOL_LISP}/book-essence"'")' > $tmpfile
echo "(book-essence $infile $outfile)" >> $tmpfile
echo "(value :q) (quit)" >> $tmpfile

${ACL2} < $tmpfile
