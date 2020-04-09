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
(include-book "std/util/bstar" :dir :system)

; This book is an awful hack to work around a problem with ACL2.
;
; ACL2 will not allow you to submit a theorem like this:
;
;    (defthm crock
;      (equal (consp x) (consp x)))
;
; That's reasonable, I guess, since such a rule would loop.
;
; Unfortunately, ACL2 is "smart" enough to simplify your rule, before even
; trying to prove that it holds, using certain kinds of type reasoning.  For
; instance, if you try to submit:
;
;    (defthm not-nil
;      (equal (not nil) t))
;
; ACL2 will use type reasoning to reduce (NOT NIL) to T, and then it will
; reject your rule on the grounds that you are rewriting T to itself.
;
; That's fine until you try to write a macro like DEFLIST/DEFALIST.  Here, the
; user gives us some predicate and also may tell us, e.g., that their predicate
; is true for NIL.  Now, for many reasons---to check whether they've told us
; the truth, and to fail quickly and in an obvious way if they haven't, and to
; make sure we're operating in a reliable theory---we try to submit a perfectly
; reasonable theorem:
;
;   (defthm predicate-of-nil
;      (equal (predicate nil) t))
;
; If PREDICATE is something interesting like INTEGER-LISTP, this theorem will
; go through fine and all is well.  But when the predicate is something simple
; like NOT or INTEGERP, ACL2 helpfully simplifies (PREDICATE NIL) to T and then
; bombs out.
;
; Here is a horrible way to work around this.

(defmacro maybe-defthm-as-rewrite
  ;; Submit a rewrite rule only if it's not going to run afoul of this check.
  (name    ; Name of the theorem you want to write, e.g., predicate-of-nil
   concl   ; Conclusion of your theorem, e.g., (equal (predicate 'nil) 't)
   &key hints)
  "Concl must be a HYP-FREE and already TRANSLATED term"
  `(make-event
    (b* ((name  ',name)
         (concl ',concl)
         (hints ',hints)
         ((unless (pseudo-termp concl))
          (er hard? 'maybe-defthm-as-rewrite
              "Expected concl to be a translated term, but got ~x0"
              concl)
          (value '(value-triple :error)))
         (thm   `(defthm ,name ,concl :hints ,hints))
         (ens   (acl2::ens state))
         (wrld  (acl2::w state))
         ;; Call ACL2's function that checks whether the rule is okay or not.
         ((mv msg ?eqv ?lhs ?rhs ?ttree)
          (acl2::interpret-term-as-rewrite-rule name nil

; Matt K. mod, 8/22/2016: Interpret-term-as-rewrite-rule now expects its term
; argument to have had remove-guard-holders applied.

                                                (acl2::remove-guard-holders
                                                 concl
                                                 wrld)
                                                ens wrld))
         ((when msg)
          ;; Not okay!  Don't submit the theorem.
          (value '(value-triple :invisible))))
      ;; Okay -- submit it!
      (value thm))))

(defun is-theorem-p (name world)
  (declare (xargs :mode :program))
  ;; Checks whether NAME is the name of a defined theorem.
  (acl2::fgetprop name 'acl2::theorem nil world))

(defmacro enable-if-theorem (name)
  ;; Enables NAME if it is a valid theorem, or does nothing otherwise.
  `(make-event
    (let ((name ',name))
      (if (is-theorem-p name (w state))
          (value `(in-theory (enable ,name)))
        (value `(value-triple :invisible))))))

(defmacro disable-if-theorem (name)
  ;; Disables NAME if it is a valid theorem, or does nothing otherwise.
  `(make-event
    (let ((name ',name))
      (if (is-theorem-p name (w state))
          (value `(in-theory (disable ,name)))
        (value `(value-triple :invisible))))))

(local
 (progn

   ;; Some basic tests

   (include-book "misc/assert" :dir :system)

   (maybe-defthm-as-rewrite foo (equal (car (cons x y)) x))
   (maybe-defthm-as-rewrite bar (equal (not 'nil) 't))
   (maybe-defthm-as-rewrite baz (equal (stringp 'nil) 'nil))

   (assert! (is-theorem-p 'foo (w state)))
   (assert! (not (is-theorem-p 'bar (w state))))
   (assert! (not (is-theorem-p 'baz (w state))))

   (assert! (let ((acl2::ens (acl2::ens state))) (active-runep '(:rewrite foo))))
   (assert! (let ((acl2::ens (acl2::ens state))) (not (active-runep '(:rewrite bar)))))

   (enable-if-theorem foo)

   (assert! (let ((acl2::ens (acl2::ens state)))
              (active-runep '(:rewrite foo))))

   (disable-if-theorem foo)

   (assert! (let ((acl2::ens (acl2::ens state)))
              (not (active-runep '(:rewrite foo)))))

   (enable-if-theorem foo)

   (assert! (let ((acl2::ens (acl2::ens state)))
              (active-runep '(:rewrite foo))))

   ))
