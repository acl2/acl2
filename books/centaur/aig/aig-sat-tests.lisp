; Centaur AIG Library
; Copyright (C) 2008-2013 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

; cert_param: (uses-glucose)

(in-package "ACL2")

(local (progn

(include-book "aig-sat")
(include-book "std/testing/assert-bang" :dir :system)

(defun my-glucose-config ()
  (declare (xargs :guard t))
  (satlink::make-config :cmdline "glucose -model"
                        :verbose t
                        :mintime 1/2
                        :remove-temps t))

(value-triple (tshell-ensure))

; These are some extremely basic tests.  The point isn't to thoroughly test the
; SAT solver.  It's just to make sure that everything seems to be basically
; holding together.

(defun test-aig-sat (input expect)
  (b* (((mv status ?alist)
        (aig-sat input :config (my-glucose-config))))
    (cw "Alist: ~x0" alist)
    (equal status expect)))

(assert! (test-aig-sat nil :unsat))
(assert! (test-aig-sat t :sat))

(assert! (test-aig-sat 'x :sat))
(assert! (test-aig-sat (aig-and 'x 'y) :sat))
(assert! (test-aig-sat (aig-ite 'x 'y 'z) :sat))

(assert! (test-aig-sat (aig-and
                        (aig-ite 'x 'y 'z)
                        (aig-ite 'x (aig-not 'y) (aig-not 'z)))
                       :unsat))


(assert! (test-aig-sat (aig-and-list
                        (list (aig-or 'x 'y)
                              'a
                              (aig-or (aig-not 'x) 'y)
                              (aig-and 'a 'b)
                              (aig-or 'x (aig-not 'y))
                              'c
                              (aig-not 'x)
                              (aig-not 'y)))
                       :unsat))


))
