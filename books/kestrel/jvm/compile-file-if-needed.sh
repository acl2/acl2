# A script to compile .java files
#
# Copyright (C) 2008-2011 Eric Smith and Stanford University
# Copyright (C) 2013-2020 Kestrel Institute
# Copyright (C) 2016-2020 Kestrel Technology, LLC
#
# License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
#
# Author: Eric Smith (eric.smith@kestrel.edu)

################################################################################

#! /bin/bash
set -e # Exit on first error

# Compile a source file, placing the class file next to it
FILENAMENOEXT=$1 # path to the source file, with or without the .java extension
FILENAMENOEXT="${FILENAMENOEXT%.java}" # Strip .java extension if present

THISSCRIPTDIR="$( cd "$( dirname "$0" )" && pwd )" #Simpler commands can just give "." here, which seems bad.

CLASSFILE="${FILENAMENOEXT}.class"
SOURCEFILE="${FILENAMENOEXT}.java"

${THISSCRIPTDIR}/compile-file-if-needed-core.sh "${SOURCEFILE}" "${CLASSFILE}"
