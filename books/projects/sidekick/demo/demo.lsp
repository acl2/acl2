; ACL2 Sidekick
; Copyright (C) 2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "ACL2")

(verify (implies (and (natp x)
                      (consp y)
                      (integerp z)
                      (<= x y)
                      (< z (expt 2 k)))
                 (equal (append x y)
                        (revappend z (floor k n)))))

; Note: the acl2-customization.lsp file in this directory loads the sidekick
; book.  When you start ACL2 in this directory, you should see a message such
; as:
;
; ----------------------------------------------------------------
;
;           Sidekick started, see http://localhost:9000/
;
; ----------------------------------------------------------------
;
; To try out the Sidekick, point your web browser to that address.  Some things
; to try:
;
;   - Go to the Session page.  Run through these events interactively, and see
;     how it follows along with what you're doing.
;
;   - Interactively run ``:show append''.  It should bring up the lookup page
;     with documentation, properties, etc.
;
;   - Try something like (include-book "std/top" :dir :system) and then take
;     a look at the :lint command.  You can get there by clicking or by typing
;     :lint.
;
; More to come later.


; This is just to test out the session viewer color stuff

(defun app (x y)
  (if (atom x)
      y
    (cons (car x)
          (app (cdr x) y))))

(defun app2 (x y)
  (declare (xargs :guard t))
  (if (atom x)
      y
    (cons (car x)
          (app2 (cdr x) y))))

(defthm app-of-app
  (equal (app (app x y) z)
         (app x (app y z))))

; We'll add a disabled event to see the color change.

(defthmd app-when-atom
  (implies (atom x)
           (equal (app x y)
                  y)))

; And partially disabled/enabled events get a slightly lighter color:

(defun fib (x)
  (declare (xargs :verify-guards nil))
  (if (zp x)
      1
    (if (equal x 1)
        1
      (+ (fib (- x 1)) (fib (- x 2))))))

(make-event
 `(defthm fib-of-36
    (equal (fib 36) ,(fib 36))))

(defsection partially-disabled

  (defthmd disabled-lemma
    (implies (atom x)
             (equal (app x y) y)))

  (defthm enabled-lemma
    (implies (atom x)
             (equal (app x y) y))))

(defun <foo> (x)
  "Stupid test of encoding"
  x)

(defun f (x)
  (declare (xargs :mode :program :guard (natp x)))
  (+ 1 x))

(verify-termination f (declare (xargs :verify-guards nil)))

(verify-guards f)

(defsection mixed-program/logic

  (defun f-program (x)
    (declare (xargs :mode :program))
    x)

  (defun f-logic (x)
    (declare (xargs :mode :logic))
    x))

(defsection mixed-verified/unverified

  (defun f-unverified (x)
    (declare (xargs :verify-guards nil))
    x)

  (defun f-verified (x)
    (declare (xargs :verify-guards t))
    x))

(defsection two-program

  (defun f-program1 (x)
    (declare (xargs :mode :program))
    x)

  (defun f-program2 (x)
    (declare (xargs :mode :program))
    x))

(defsection two-unverified

  (defun f-unverified1 (x)
    (declare (xargs :verify-guards nil))
    x)

  (defun f-unverified2 (x)
    (declare (xargs :verify-guards nil))
    x))

(defsection two-verified

  (defun f-verified1 (x)
    (declare (xargs :verify-guards t))
    x)

  (defun f-verified2 (x)
    (declare (xargs :verify-guards t))
    x))


(defsection program-section
  (defun g-program (x)
    (declare (xargs :mode :program))
    x))

(defsection logic-section
  (defun g-logic (x)
    (declare (xargs :verify-guards nil))
    x))

(defsection verified-section
  (defun g-verified (x)
    (declare (xargs :verify-guards t))
    x))


(defthm app-of-app3
  (equal (app (app x y) z)
         (app x (app y z))))

(defthm app-of-app4
  (equal (app (app x y) z)
         (app x (app y z))))

(defthm app-of-app5
  (equal (app (app x y) z)
         (app x (app y z))))

(defthm app-of-app6
  (equal (app (app x y) z)
         (app x (app y z))))

(defthm app-of-app7
  (equal (app (app x y) z)
         (app x (app y z))))

(defthm app-of-app8
  (equal (app (app x y) z)
         (app x (app y z))))

(defthm app-of-app9
  (equal (app (app x y) z)
         (app x (app y z))))

(defthm app-of-app10
  (equal (app (app x y) z)
         (app x (app y z))))

(defun h0 (x) x)
(defun h1 (x)
  (declare (xargs :verify-guards t))
  x)

(define h2 (x) x)

(define h3 (x) x)

(define h4 (x) :mode :program x)


(defsection nesting-test
  (defun n1 (x) x)
  (defsection n23
    (defun n2 (x) x)
    (defun n3 (x) x))
  (encapsulate ()
    (defun n4 (x) x))
  (defsection n56
    (defsection n5
      (defun n5 (x) x))
    (defsection n6
      (defun n6 (x) x))))

(define h5 (x) x)
(define h6 (x) x)

