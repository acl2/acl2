#!/bin/bash

# ACL2 Community Books build system
# Copyright (C) 2019 Centaur Technology
#
# Contact:
#   Centaur Technology Formal Verification Group
#   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
#   http://www.centtech.com/
#
# License: (An MIT/X11-style license)
#
#   Permission is hereby granted, free of charge, to any person obtaining a
#   copy of this software and associated documentation files (the "Software"),
#   to deal in the Software without restriction, including without limitation
#   the rights to use, copy, modify, merge, publish, distribute, sublicense,
#   and/or sell copies of the Software, and to permit persons to whom the
#   Software is furnished to do so, subject to the following conditions:
#
#   The above copyright notice and this permission notice shall be included in
#   all copies or substantial portions of the Software.
#
#   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
#   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
#   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
#   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
#   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
#   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
#   DEALINGS IN THE SOFTWARE.
#
# This script is based on an equivalent series of commands in
# GNUMakefile, adapted into a shell script by Sol Swords.

# ========================================================================

# This script checks for various features that some books require.
# This used to all be done in GNUMakefile itself, but we separated it
# in case other Makefiles want to use it as well.  To use it in a
# Makefile, first run it and then include the resulting
# Makefile-features, making sure that ACL2 and STARTJOB are in the
# environment -- e.g.:
# RUN_ACL2_FEATURES := $(shell cd $(BUILD_DIR); ACL2=$(ACL2) STARTJOB=$(STARTJOB) ./features.sh)
# -include $(BUILD_DIR)/Makefile-features

# We first run ACL2 on the cert_features.lsp script, which begins by
# setting up several variables (in Makefile syntax) in
# Makefile-features.  These primarily are features of ACL2 itself --
# ACL2_HAS_HONS, ACL2_HAS_PARALLEL, etc.  But we also set
# USE_QUICKLISP if it is not already set, because by default we set it
# to 1 except if the host Lisp is GCL.

# cert_features.lsp also sets up a few .certdep files that determine
# whether certain books need to be updated due to a change in
# e.g. acl2-exports.

# After that we look for several executables and features of the
# environment to determine whether we have the Glucose SAT solver, an
# IPASIR shared library, the z3 SMT solver, etc.  For each of these,
# we append more settings to the end of Makefile-features.

# For each variable that Makefile-features sets, it also adds that
# variable name to the EXPORTED_VARS list.  It then finally creates a
# variable called EXPORT_SHELL_ENV which is a series of
# space-delimited NAME=val pairs that can be used to work around the
# fact that while Gnu Make's "export" command affects the environment
# for shell commands within recipes, it doesn't affact the environment
# for $(shell ...) directives.

# Run from within build directory
echo "Determining ACL2 features (for ACL2 = $ACL2)" 1>&2
rm -f Makefile-features;
# Don't fail here if ACL2 isn't built! Still want to be able to do "make clean" etc.
ACL2_CUSTOMIZATION=NONE $STARTJOB -c "$ACL2 < cert_features.lsp &> Makefile-features.out" || echo "*** Failed to run ACL2! ***" 1>&2


echo "Determining whether Glucose is installed" 1>&2
if glucose --help 2> /dev/null;
then
    cat >> Makefile-features <<EOF
export OS_HAS_GLUCOSE ?= 1
EXPORTED_VARS += OS_HAS_GLUCOSE
EOF
fi


echo "Determining whether an ipasir shared library is installed" 1>&2
if [[ $IPASIR_SHARED_LIBRARY != '' ]];
then
    if [[ -e $IPASIR_SHARED_LIBRARY ]];
    then
	cat >> Makefile-features <<EOF
export OS_HAS_IPASIR ?= 1
EXPORTED_VARS += OS_HAS_IPASIR
EOF
    else
	echo "!!!WARNING: IPASIR_SHARED_LIBRARY was set to \"${IPASIR_SHARED_LIBRARY}\"," 1>&2
	echo "but this file doees not exist." 1>&2
    fi
fi

echo "Determining whether ABC is installed" 1>&2
if abc -h 2>&1 | fgrep 'UC Berkeley, ABC' 2>/dev/null;
then
    cat >> Makefile-features <<EOF
export OS_HAS_ABC ?= 1
EXPORTED_VARS += OS_HAS_ABC
EOF
fi

echo "Determining whether Z3 is installed, for use by SMTLink" 1>&2
if z3 --version 2>/dev/null;
then
    cat >> Makefile-features <<EOF
export OS_HAS_SMTLINK ?= 1
EXPORTED_VARS += OS_HAS_SMTLINK
EOF
fi

cat >> Makefile-features <<EOF
EXPORT_SHELL_ENV := \$(foreach v,\$(EXPORTED_VARS),\$(v)='\$(\$(v))')
EOF
