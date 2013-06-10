; CUTIL - Centaur Basic Utilities
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "CUTIL")
(include-book "tools/bstar" :dir :system)

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
          (acl2::interpret-term-as-rewrite-rule name nil concl ens wrld))
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
