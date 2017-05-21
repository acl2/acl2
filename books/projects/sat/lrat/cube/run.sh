#!/bin/sh

# To run this script, first save a suitable executable, for example:

# (include-book "run")
# :q
# (save-exec "cube-check" "Executable including run.lisp")

# Examples (refer to README for numbers and run.lisp for more on these tests):

# (1)
# ./run.sh ../tests/uuf-100-5.cnf ../tests/uuf-100-5-partial.clrat my-old2 nil my-new2

# (2)
# ./run.sh ../tests/uuf-30-1.cnf ../tests/uuf-30-1-cube.clrat my-old2 \
#          ../tests/uuf-30-1.cube my-new2

# (3)
# ./run.sh ../tests/uuf-30-1.cnf ../tests/uuf-30-1.clrat my-old2

# Feel free to change the following, which are currently set to their defaults.

export LRAT_CHUNK_SIZE=1000000
export LRAT_DEBUG=t
export LRAT_TIMEP=nil
export LRAT_EXITP=t

error=""
cube_infile=" nil"
produced_outfile=""

if [ $# -lt 3 ] ; then \
    error=true ; \
elif [ $# -gt 5 ] ; then \
    error=true ; \
elif [ $# -eq 5 ] ; then \
    if [ "$4" != "nil" ] ; then cube_infile=" \"$4\"" ; fi ; \
    produced_outfile=" \"$5\"" ; \
else \
    cnf_outfile=" \"$4\"" ; \
fi

if [ "$error" != "" ] ; then \
    echo "Usage:  $0 takes three to five arguments, as follows:" ; \
    echo "        $0 cnf_infile clrat_infile cnf_outfile cube_infile produced_outfile" ;\
    echo "        where cube_infile may be nil" ;\
    echo "        and both cube_infile and produced_outfile are optional." ;\
    exit 1 ; \
fi

cnf_infile=" \"$1\""
clrat_infile=" \"$2\""
cnf_outfile=" \"$3\""

if [ "$cnf_outfile" != "" ] ; then \
    rm -f $cnf_outfile ; \
fi
if [ "$produced_outfile" != "" ] ; then \
    rm -f $produced_outfile ; \
fi

invocation_dir=$(dirname "$0")

my_cube_check=$invocation_dir/cube-check

if [ ! -e $my_cube_check ] ; then \
    echo "ERROR: file $invocation_dir/cube-check does not exist."
    echo "See $invocation_dir/README."
    exit 1
fi

if [ ! -x $my_cube_check ] ; then \
    echo "ERROR: file $invocation_dir/cube-check exists but is not executable."
    exit 1
fi

echo "(lrat::cube-check$cnf_infile$clrat_infile$cnf_outfile$cube_infile$produced_outfile)" | $my_cube_check

exit $?
