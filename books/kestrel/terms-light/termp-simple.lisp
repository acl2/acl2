; An alternate definition of termp
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "free-vars-in-term")
(local (include-book "tools/flag" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "arglistp1"))

(local (in-theory (disable all-vars)))

;; Alternate definitions of termp and term-listp that are easier to reason about.
(mutual-recursion
 (defun termp-simple (x w)
   (declare (xargs :guard (plist-worldp-with-formals w)
                   :verify-guards nil ; done below
                   ))
   (cond
    ((atom x) (legal-variablep x))
    ((eq (car x) 'quote)
     (and (consp (cdr x)) (null (cddr x))))
    ((symbolp (car x))
     (let ((arity (arity (car x) w)))
       (and arity (term-listp-simple (cdr x) w)
            (eql (length (cdr x)) arity))))
    ((and (consp (car x))
          (true-listp (car x))
          (eq (car (car x)) 'lambda)
          (eql 3 (length (car x)))
          (arglistp (cadr (car x)))
          (termp-simple (caddr (car x)) w)
          ;; this is what changed (avoid set-difference-equal and call free-vars-in-term instead of all-vars):
          (subsetp-equal (free-vars-in-term (caddr (car x)))
                         (cadr (car x)))
          (term-listp-simple (cdr x) w)
          (eql (length (cadr (car x)))
               (length (cdr x))))
     t)
    (t nil)))
 (defun term-listp-simple (x w)
   (declare (xargs :guard (plist-worldp-with-formals w)))
   (cond ((atom x) (equal x nil))
         ((termp-simple (car x) w)
          (term-listp-simple (cdr x) w))
         (t nil))))

(local (make-flag termp-simple))

(local
 (defthm-flag-termp-simple
   (defthm termp-becomes-termp-simple
     (equal (termp x w)
            (termp-simple x w))
     :flag termp-simple)
   (defthm term-listp-becomes-term-listp-simple
     (equal (term-listp x w)
            (term-listp-simple x w))
     :flag term-listp-simple)
   :hints (("Goal" :expand (termp x w)
            :in-theory (enable termp)))))

(defthm term-listp-simple-forward-to-true-listp
  (implies (term-listp-simple terms w)
           (true-listp terms))
  :rule-classes :forward-chaining)

(local
 (defthm-flag-termp-simple
   (defthm pseudo-termp-when-termp-simple
     (implies (termp-simple x w)
              (pseudo-termp x))
     :flag termp-simple)
   (defthm pseudo-term-listp-when-term-listp-simple
     (implies (term-listp-simple x w)
              (pseudo-term-listp x))
     :flag term-listp-simple)
   :hints (("Goal" :expand (pseudo-termp x)
            :in-theory (enable pseudo-termp)))))

;; redundant and non-local
(defthm pseudo-termp-when-termp-simple
  (implies (termp-simple x w)
           (pseudo-termp x)))

;; redundant and non-local
(defthm pseudo-term-listp-when-term-listp-simple
  (implies (term-listp-simple x w)
           (pseudo-term-listp x)))

(verify-guards termp-simple
  :hints (("Goal" :in-theory (enable term-listp-becomes-term-listp-simple
                                     termp-becomes-termp-simple))))

;; redundant and non-local
(defthmd termp-becomes-termp-simple
  (equal (termp x w)
         (termp-simple x w)))

;; redundant and non-local
(defthmd term-listp-becomes-term-listp-simple
  (equal (term-listp x w)
         (term-listp-simple x w)))
