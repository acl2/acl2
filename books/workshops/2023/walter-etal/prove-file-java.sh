#!/usr/bin/env bash

# Deal with the case where the script is symlinked somewhere
REAL_BASH_SOURCE="$(/usr/bin/env python3 -c "import os,sys; print(os.path.realpath(sys.argv[1]))" "${BASH_SOURCE[0]}")"
SCRIPT_DIR="$( cd "$( dirname "${REAL_BASH_SOURCE[0]}" )" && pwd )"

cd "$1"
# We redirect 4 -> 2 (stderr), 3 -> 1 (stdout), 1 (stdout) -> 4, and 2 -> dev/null
# This has the effect of discarding anything printed to stdout or stderr, and printing
# anything printed to fd 3. We pass 3 to prove-file to tell it that it should print
# information we should see to fd 3
($SCRIPT_DIR/prover-java 3 4 6>&5 3>&1 4>&2 1>&6 2>&6) 5>/dev/null
