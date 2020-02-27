# cert.pl build system
# Copyright (C) 2008-2014 Centaur Technology
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
# Original author: Sol Swords <sswords@centtech.com>

package Certinfo;
use strict;
use warnings;

# info about a book:
use Class::Struct Certinfo => [ bookdeps => '@',        # books included by this one
				bookdeps_local => '@',  # flags corresp books from bookdeps as local
				portdeps => '@',        # books included in the portcullis
				portdeps_local => '@',  # flags corresp books from portdeps as local
				srcdeps => '@',         # source dependencies (.lisp, .acl2)
				otherdeps => '@',       # from depends_on forms
				image => '$',           # acl2, or from book.image/cert.image
				params => '%',          # cert_param entries
				include_dirs => '%',    # add-include-book-dir! forms
				local_include_dirs => '%', # all add-include-book-dir(!) forms
				defines => '%',         # exported ifdef-defines/undefines, strings mapped to "1"/""
				local_defines => '%',   # all ifdef-defines/undefines, strings mapped to "1"/""
				rec_visited => '%' ];   # already seen files for depends_rec

1;
