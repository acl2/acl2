#!/bin/bash

export a2ml="${ACL2_HOL_LISP}/a2ml"

if [ $# -ne 2 && $# -ne 3 ] ; then \
	echo "Usage: $0 infile outfile [infile_dir]" ;\
	exit 1 ;\
fi

# Suggestion from perplexity.ai:
export SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

export infile="$1"
export outfile="$2"
export tmpfile=${SCRIPT_DIR}/workxxx-a2ml-"$(basename ${infile})"
if [ $# -eq 3 ] ; then \
    export infile_dir="$3" ;\
else \
    export infile_dir="" ;\
fi

rm -f $tmpfile
echo "(include-book " '"'"${a2ml}"'")' > $tmpfile
echo "(a2ml "'"'"$infile"'" "'"$outfile"'" "'"$infile_dir"'")' >> $tmpfile
echo "(value :q) (quit)" >> $tmpfile
${ACL2} < $tmpfile
