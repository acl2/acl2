#!/bin/sh

# VL Verilog Toolkit
# Copyright (C) 2008-2016 Centaur Technology
#
# Contact:
#   Centaur Technology Formal Verification Group
#   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
#   http:#www.centtech.com/
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
# Original author: Jared Davis <jared@centtech.com>

set -e
set -u

VL_KIT=../../bin/vl

if [ ! -e demo.sv ]
then
    echo "*** Error: demo.sv not found?"
    echo "*** Running from the wrong directory?"
    exit 1
fi

if [ ! -e "$VL_KIT" ]
then
    echo "*** Error: $VL_KIT not found; have you build the VL kit?"
    echo "*** You can try building it with:"
    echo "***"
    echo "***    $ cd ../../../..   # the acl2/books directory"
    echo "***    $ make vl -j N"
    echo "***"
    exit 1
fi

cat <<EOF

--- Creating .vlzip File ----------------------------------------

  The VL Server reads .vlzip files that are produced by the
  "vl zip" command.  We will now use this command to create
  a vlzip file in the ./ziproot directory.

-----------------------------------------------------------------

EOF

echo -n "Type OK when ready: "
read

mkdir -p ziproot
CMD="$VL_KIT zip demo.sv --name demo --output ./ziproot/demo.vlzip"

echo ""
echo "Submitting: $CMD"
$CMD

echo ""
echo "Resulting file:"
ls -lah ./ziproot/demo.vlzip

cat <<EOF

--- Ready to run the VL Server. ---------------------------------

  A VL server will now be started on port 34992.

  Once it is started, point your web browser to:
     http://localhost:34992/

  This terminal will become a Lisp shell where you can give
  commands to the server.  Normally this shell will not be
  very useful, but it can be handy when doing development of
  the VL server, i.e., you can redefine functions.

  Useful commands:
    (quit) -- to exit
    (lp) -- to go into ACL2

-----------------------------------------------------------------
EOF

echo -n "Type OK when ready: "
read

CMD="$VL_KIT server --port 34992 --root=./ziproot"
echo "Submitting: $CMD"

exec $CMD


