#!/usr/bin/env bash

# This script will automatically regenerate the CFFI files that the
# Lisp-Z3 interface requires from the headers for Z3's C API. This
# allows one to use the interface with a version of Z3 that is too
# different from the one that the CFFI files provided with this package
# was built for.
#
# To use this script, you must provide the path to the z3.h header file.
# The location of this file depends on your OS and how you installed Z3,
# but here are a few options:
#
# - If you installed Z3 using Homebrew, the path to the file should be
#   the result of running `brew --prefix z3`, followed by `/include/z3.h`.
#
# - If you installed Z3 using a Linux package manager, or by building from
#   scratch, the file should be located at `/usr/include/z3.h` or
#   `/usr/local/include/z3.h`. If you are on Ubuntu or another Linux
#   distribution that distributes header files separately from libraries,
#   you may need to install the appropriate package (libz3-dev on Ubuntu)
#
# You must also have Python 3 installed, as well as the pyclibrary
# package. You can install this package with pip, e.g.:
# `pip install pyclibrary`
#
# Then, simply run this script, providing the path to the z3.h header
# file as an argument. e.g.:
# `./scripts/update-ffi.sh /usr/include/z3.h`
# The directory from which the script is run does not matter.

# Deal with the case where the script is symlinked somewhere
REAL_BASH_SOURCE="$(/usr/bin/env python3 -c "import os,sys; print(os.path.realpath(sys.argv[1]))" "${BASH_SOURCE[0]}")"
DIR="$( cd "$( dirname "${REAL_BASH_SOURCE[0]}" )" && pwd )"
REPO="$( cd "$( dirname "${REAL_BASH_SOURCE[0]}" )" && cd ../ && pwd )"

if [ $# -eq 0 ]; then
	echo "You must provide a path to the z3.h header file! Exiting..."
	exit 1
fi

set -e
echo "Generating z3-api.lisp..."
/usr/bin/env python3 "$DIR/gen-z3-api.py" $1 -o "$REPO/src/ffi/z3-api.lisp" -f
echo "Generating z3-grovel.lisp..."
/usr/bin/env python3 "$DIR/gen-z3-grovel.py" $1 -o "$REPO/src/ffi/z3-grovel.lisp" -f
echo "Generating z3-c-types.lisp..."
/usr/bin/env python3 "$DIR/gen-z3-c-types.py" $1 -o "$REPO/src/ffi/z3-c-types.lisp" -f
echo "Generating package.lisp..."
/usr/bin/env python3 "$DIR/gen-z3-package.py" $1 -o "$REPO/src/ffi/package.lisp" -f
