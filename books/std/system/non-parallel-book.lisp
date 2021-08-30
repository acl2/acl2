; Copyright (C) 2008-2014 Centaur Technology
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

; The utility non-parallel-book was originally defined in
; centaur/vl/util/defs.lisp.  After consultation with Jared Davis and David
; Rager, Matt Kaufmann moved its definition to this file and also modified it a
; bit.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defsection non-parallel-book
  :parents (parallelism)
  :short "Mark a book as incompatible with ACL2(p) waterfall parallelism."
  :long "<p>Some features of ACL2 are incompatible with ACL2(p); see @(see
 unsupported-waterfall-parallelism-features).  For example, ACL2(p) does not
 support @(see clause-processor)s that modify the ACL2 @(see state).</p>

 <p>The form @('(non-parallel-book)') instructs ACL2 to ensure that @(see
 waterfall-parallelism) is turned off.  When you put that form into a book, it
 will be ignored when including the book unless keyword @(':check-expansion')
 is true.  (Suggestion: avoid that keyword unless you are sure you know what
 you are doing!)</p>"

  (defmacro non-parallel-book (&key check-expansion)
    `(make-event
      (if (f-get-global 'ACL2::parallel-execution-enabled state)
          (er-progn (set-waterfall-parallelism nil)
                    (value '(value-triple nil)))
        (value '(value-triple nil)))
      ,@(and check-expansion
             '(:check-expansion t)))))
