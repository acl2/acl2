#!/bin/sh

if [ $# -eq 2 ] ; then \
    partial="" ; \
    outfile=${2%.*}.out ; \
elif [ $# -eq 3 ] ; then \
    partial=" $3" ; \
    outfile=${2%.*}.out ; \
elif [ $# -eq 4 ] ; then \
    partial=" $3" ; \
    outfile=$4 ; \
else
    echo "Usage:  $0 takes two to four arguments, as follows." ; \
    echo "        # Third argument is t for partial proof, else omitted or nil ." ; \
    echo "        # Fourth argument is t for standard output, else an output file;" ; \
    echo "        # default for omitted out-file is lrat-file with .lrat replaced by .out ." ; \
    echo "        $0 cnf-file lrat-file" ; \
    echo "        $0 cnf-file lrat-file t" ; \
    echo "        $0 cnf-file lrat-file nil out-file" ; \
    echo "        $0 cnf-file lrat-file t   out-file" ; \
    echo "        $0 cnf-file lrat-file nil t" ; \
    echo "        $0 cnf-file lrat-file t   t" ; \
    exit 1 ; \
fi

invocation_dir=$(dirname "$0")

my_lrat_check=$invocation_dir/lrat-check

if [ ! -e $my_lrat_check ] ; then \
    echo "ERROR: file $invocation_dir/lrat-check does not exist."
    echo "See $invocation_dir/README."
    exit 1
fi

if [ ! -x $my_lrat_check ] ; then \
    echo "ERROR: file $invocation_dir/lrat-check exists but is not executable."
    exit 1
fi

if [ "$outfile" = t ] ; then \
    echo "(lrat-check \"$1\" \"$2\" $partial)" | $my_lrat_check ; \
else \
    echo "(lrat-check \"$1\" \"$2\" $partial)" | $my_lrat_check > "$outfile" ; \
fi

lrat_status=$?

if [ "$outfile" = t ] ; then \
    echo -n "" ; \
elif [ $lrat_status -eq 0 ] && [ "`grep '^s VERIFIED' $outfile`" != "" ] ; then \
    echo "s VERIFIED" ; \
    echo "  (see $outfile)" ; \
else \
    echo "s FAILED" ; \
    echo "  (see $outfile)" ; \
    exit 1
fi
