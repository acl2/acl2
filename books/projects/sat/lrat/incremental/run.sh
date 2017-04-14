#!/bin/sh

# To run this script, first save a suitable executable, for example:

# (include-book "run")
# :q
# (save-exec "lrat-check" "Executable including run.lisp")

export LRAT_PRINT_FORMULA=""
export cnf_outfile=""

if [ $# -eq 2 ] ; then \
    partial="" ; \
    outfile=${2%.*}.out ; \
elif [ $# -eq 3 ] ; then \
    partial=" $3" ; \
    outfile=${2%.*}.out ; \
elif [ $# -eq 4 ] ; then \
    partial=" $3" ; \
    outfile=$4 ; \
elif [ $# -eq 5 ] ; then \
    partial=" $3" ; \
    outfile=$4 ; \
    export LRAT_PRINT_FORMULA="$5"
    export cnf_outfile="$5"
else
    echo "Usage:  $0 takes two to five arguments, as follows." ; \
    echo "        # Third argument is t for partial proof, else omitted or nil ." ; \
    echo "        # Fourth argument is t for standard output, else an output file;" ; \
    echo "        # Fifth argument is t for standard output, else an output cnf file to diff with input;" ; \
    echo "        # default for omitted fourth argument is clrat-file with .clrat replaced by .out ." ; \
    echo "        $0 cnf-file clrat-file" ; \
    echo "        $0 cnf-file clrat-file nil [out-file [cnf-outfile]]" ; \
    echo "        $0 cnf-file clrat-file t   [out-file [cnf-outfile]]" ; \
    echo "        $0 cnf-file clrat-file nil [t [cnf-outfile]]" ; \
    echo "        $0 cnf-file clrat-file t   [t [cnf-outfile]]" ; \
    exit 1 ; \
fi

if [ "$cnf_outfile" != "" ] ; then \
    rm -f $cnf_outfile ; \
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
    /bin/echo -n "" ; \
elif [ $lrat_status -eq 0 ] && [ "`grep '^s VERIFIED' $outfile`" != "" ] ; then \
    echo "s VERIFIED" ; \
    echo "  (see $outfile)" ; \
else \
    echo "s FAILED" ; \
    echo "  (see $outfile)" ; \
    exit 1
fi

if [ "$cnf_outfile" != "" ] && [ "$cnf_outfile" != "t" ] && [ "$cnf_outfile" != "T" ] ; then \
    ./cnf_diff.sh "$1" "$cnf_outfile" ; \
    if [ $? -ne 0 ] ; then \
	exit 1 ; \
    fi \
fi
