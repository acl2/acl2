; Centaur Lexer Library
; Copyright (C) 2013 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "CLEX")
(include-book "std/util/defprojection" :dir :system)
(include-book "std/strings/eqv" :dir :system)

(defprojection charlist-fix (x)
  (str::char-fix x)
  :guard t
  :parents (str::char-fix))

(defthm character-listp-of-charlist-fix
  (character-listp (charlist-fix x))
  :hints(("Goal" :induct (len x))))

(defthm charlist-fix-when-character-listp
  (implies (character-listp x)
           (equal (charlist-fix x)
                  x))
  :hints(("Goal" :induct (len x))))

(defthm charlist-fix-under-charlisteqv
  (str::charlisteqv (charlist-fix x)
                    x)
  :hints(("Goal" :induct (len x))))
