; Standard Utilities Library
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

(in-package "STD")
(include-book "look-up")
(include-book "std/testing/assert" :dir :system)

(encapsulate
  ()
  (local
   (progn
     (assert! (not (var-is-stobj-p 'foo (w state))))
     (assert! (var-is-stobj-p 'state (w state)))
     (defstobj foo (field1 :initially 0))
     (assert! (var-is-stobj-p 'foo (w state))))))

(encapsulate
  ()
  (local
   (progn
     (assert! (equal (look-up-formals 'look-up-formals (w state))
                     '(fn world))))))

(encapsulate
  ()
  (local
   (progn
     (defun f1 (x) x)
     (defun f2 (x) (declare (xargs :guard (natp x))) x)
     (defun f3 (x) (declare (xargs :guard (and (integerp x)
                                               (<= 3 x)
                                               (<= x 13))))
            x)
     (assert! (equal (look-up-guard 'f1 (w state)) 't))
     (assert! (equal (look-up-guard 'f2 (w state)) '(natp x)))
     (assert! (equal (look-up-guard 'f3 (w state))
                     '(IF (INTEGERP X)
                          (IF (NOT (< X '3)) (NOT (< '13 X)) 'NIL)
                          'NIL))))))

(encapsulate
  ()
  (local
   (progn
     (defun f1 (x) x)
     (defun f2 (x) (mv x x))
     (defun f3 (x state) (declare (xargs :stobjs state)) (mv x state))
     (assert! (equal (look-up-return-vals 'f1 (w state)) '(nil)))
     (assert! (equal (look-up-return-vals 'f2 (w state)) '(nil nil)))
     (assert! (equal (look-up-return-vals 'f3 (w state)) '(nil state))))))

(encapsulate
  ()
  (local
   (progn
     (defun f1 (x) x)
     (defmacro f2 (x) x)
     (defmacro f3 (x y &key (c '5) (d '7)) (list x y c d))
     (assert! (equal (look-up-wrapper-args 'f1 (w state)) '(x)))
     (assert! (equal (look-up-wrapper-args 'f2 (w state)) '(x)))
     (assert! (equal (look-up-wrapper-args 'f3 (w state))
                     '(x y &key (c '5) (d '7)))))))

(encapsulate
  ()
  (local
   (progn
     (defun f (x) (declare (xargs :mode :program)) x)
     (defun g (x) x)
     (defun h (x) (declare (xargs :verify-guards t)) x)
     (assert! (logic-mode-p 'g (w state)))
     (assert! (logic-mode-p 'h (w state)))
     (assert! (not (logic-mode-p 'f (w state)))))))
