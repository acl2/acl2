; Copyright (C) 2018 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author (this file): Sol Swords <sswords@centtech.com>

(in-package "GL")

(include-book "xdoc/archive-matching-topics" :dir :system)
(local
 (progn
   (include-book "build/ifdef" :dir :system)
   (include-book "gl")
   (include-book "bfr-aig-bddify")
   (include-book "gl-ttags")
   (include-book "gobject-type-thms")
   (include-book "bfr-satlink")
   (include-book "bfr-fraig-satlink")
   (include-book "def-gl-rule")
   (include-book "defthm-using-gl")

   (include-book "centaur/glmc/glmc" :dir :system)
   (include-book "centaur/glmc/bfr-mcheck-abc" :dir :system)

   (include-book "centaur/misc/try-gl-concls" :dir :system)
   (acl2::ifdef "OS_HAS_GLUCOSE"
                (acl2::ifdef "OS_HAS_ABC"
                             (include-book "centaur/glmc/glmc-test" :dir :system)
                             (include-book "centaur/glmc/counter" :dir :system)
                             :endif)
                :endif)))


(xdoc::archive-matching-topics
 (let* ((from (cdr (assoc :from x))))
   (or (str::strprefixp "[books]/centaur/gl/" from)
       (str::strprefixp "[books]/centaur/glmc/" from)
       (str::strprefixp "[books]/centaur/misc/try-gl-concls" from))))
