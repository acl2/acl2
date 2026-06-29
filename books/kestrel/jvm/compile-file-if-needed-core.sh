#! /bin/bash

# A script to compile .java files
#
# Copyright (C) 2008-2011 Eric Smith and Stanford University
# Copyright (C) 2013-2026 Kestrel Institute
# Copyright (C) 2016-2020 Kestrel Technology, LLC
#
# License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
#
# Author: Eric Smith (eric.smith@kestrel.edu)

################################################################################

# WARNING: This script assumes the class has the same name as the
# .java file (except for the extension)

set -e

SOURCEFILE=$1
CLASSFILE=$2

if [ -z "$KESTREL_ACL2_JAVAC" ]; then
    KESTREL_ACL2_JAVAC=javac
fi

if [[ ( -f "${CLASSFILE}" ) && ( "${CLASSFILE}" -nt "${SOURCEFILE}" ) ]] ; then
    echo "${CLASSFILE} is up-to-date."
#    : # no-op
else
    echo "Compiling ${SOURCEFILE} as ${CLASSFILE}."
    ${KESTREL_ACL2_JAVAC} -g -target 1.7 -source 1.7 "${SOURCEFILE}"
fi
