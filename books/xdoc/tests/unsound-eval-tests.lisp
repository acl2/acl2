; XDOC Documentation System for ACL2
; Copyright (C) 2009-2013 Centaur Technology
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

(in-package "ACL2")
(include-book "../unsound-eval")
(include-book "centaur/vl/util/print" :dir :system)
(include-book "std/util/defconsts" :dir :system)

(defmacro test-ok (sexpr expect)
  `(make-event
    (b* (((mv errmsg objects state) (unsound-eval ',sexpr))
         ((when (and (not errmsg)
                     (equal objects ',expect)))
          (value '(value-triple :success))))
      (er soft 'test-ok "Test failed for ~x0: expect ~x1 but got ~x2; msg is ~@3"
          ',sexpr ',expect objects (or errmsg "NIL")))))

(defmacro test-fail (sexpr)
  `(make-event
    (b* (((mv errmsg objects state) (unsound-eval ',sexpr))
         ((when errmsg)
          (value '(value-triple :success))))
      (er soft 'test-fail "Test failed for ~x0: expect FAIL but got ~x1."
          ',sexpr objects))))


(test-ok 3 (3))
(test-ok (list 3) ((3)))
(test-ok (mv 1 2 3) (1 2 3))
(test-ok (+ 1 2) (3))
(test-ok (append '(1 2 3) '(4 5 6)) ((1 2 3 4 5 6)))

(test-ok (princ$ "Hello" *standard-co* state) (state))
(test-ok (let ((state (princ$ "Hello" *standard-co* state)))
           (mv 1 state))
         (1 state))

(test-ok (let* ((state  (princ$ "Hello" *standard-co* state))
                (vl::ps (vl::vl-print "Hello")))
           (mv 1 state vl::ps))
         (1 state vl::ps))

(test-fail (f 1 2 3)) ;; not defined
(test-fail (er hard? 'foo "error"))
(test-fail (car 3))
(test-fail (mv state state))


(defun f (x)
  (er hard? 'f "X is ~x0." x))

(test-fail (f 3))

(defun infinite (x)
  (declare (xargs :mode :program))
  (if (zp x)
      nil
    (cons 1 (infinite x))))
(test-ok (infinite 0) (nil))
(test-fail
; Modified 1/2014 by Matt K.  In CMUCL the stack overflow from (infinite 3)
; aborted an ACL2 (without hons) certification attempt using the standard
; `make' process (via cert.pl), but I was unable to reproduce the problem at
; the terminal, and a search did not yield any CMUCL-specific code in the ACL2
; sources that might explain this oddity.  Perhaps some weird interaction with
; `make' is responsible for the aborted certification.  At any rate, it's easy
; enough to avoid the stack overflow in CMUCL or any other Lisp for which this
; turns out to be an issue.  In fact we've seen problems here with Allegro CL
; and CLISP, so we exclude those, too.
 (if (member-eq (@ host-lisp) '(:CMU :ALLEGRO :CLISP))
     (f 3)
   (infinite 3)))

;; Unfortunately with-local-stobj doesn't work directly, but at least it works
;; in a function call...
(test-fail (vl::with-local-ps (vl::vl-print "Hello")))

(defun g () (vl::with-local-ps (vl::vl-print "Hello")))
(test-ok (g) ("Hello"))

(defconst *foo* 3)
(test-ok *foo* (3))

;; Accessing stobjs works
(defconsts vl::ps
  (b* ((vl::ps (vl::vl-ps-full-reset))
       (vl::ps (vl::vl-print "foo")))
    vl::ps))

(test-ok (vl::vl-ps->string) ("foo"))

;; Updating stobjs even works, after a fashion...
(test-ok (let ((vl::ps (vl::vl-print "bar")))
           (mv (vl::vl-ps->string)
               vl::ps))
         ("foobar" vl::ps))
