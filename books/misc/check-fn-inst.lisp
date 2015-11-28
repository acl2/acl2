; Copyright (C) 2014, ForrestHunt, Inc.
; Written by Matt Kaufmann, August, 2014
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; Usage:
; (check-fn-inst (f1 g1) ... (fk gk))
; This succeeds exactly when the gi satisfy the constraints on fi.

(defun subst-to-trivial-formulas (subst wrld)

; Subst is a list of doublets of the form (f g), where f is a function symbol.
; We want a trivial formula that mentions every function symbol in the domain
; of subst; see :doc constraint.

  (declare (xargs :guard (and (symbol-alistp subst)
                              (plist-worldp wrld))))
  (cond ((endp subst) nil)
        (t (cons (let* ((fn (caar subst))
                        (formals (getprop fn 'formals t 'current-acl2-world
                                          wrld))
                        (ap (cons fn formals))
                        (term `(equal (hide ,ap) (hide ,ap))))
                   (cond ((eq formals t)
                          (er hard? 'subst-to-trivial-formulas
                              "The symbol ~x0 is not a function symbol in the ~
                               current ACL2 world."
                              fn))
                         (t term)))
                 (subst-to-trivial-formulas (cdr subst) wrld)))))

(defmacro check-fn-inst (&rest subst)
  `(make-event (er-progn
                (let ((form (cons 'and (subst-to-trivial-formulas ',subst (w state)))))

; From applying :trans1 to a suitable THM form, we get the following.  Exercise
; (might be straightforward but not sure): Avoid calling thm-fn by using a
; suitable make-event.

                  (thm-fn 't
                          state
                          (list
                           (list "Goal"
                                 :use
                                 (list
                                  (list* :functional-instance
                                         (list :theorem form)
                                         ',subst))))
                          'nil))
                (value '(value-triple nil)))))

; Examples

(local
(progn

(encapsulate
 ((f (x) t))
 (local (defun f (x) x))
 (defthm f-preserves-len
   (equal (len (f x))
          (len x))))

(defun g (x)
  (reverse x))

(defthm len-revappend
  (equal (len (revappend x y))
         (+ (len x) (len y))))

; Direct approach:
(encapsulate
 ()
 (local
  (defthm my-test
    t
    :hints (("Goal" :use ((:functional-instance
                           (:theorem (equal (f x) (f x)))
                           (f g)))))
    :rule-classes nil)))

; Via our macro:
(check-fn-inst (f g))

; Let's see what a failure looks like:

(defun h (x) (cdr x))

))

; Fails:
; (check-fn-inst (f h))
