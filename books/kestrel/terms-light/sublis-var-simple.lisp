; Utilities that perform substitution
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/symbol-term-alistp" :dir :system)
(include-book "tools/flag" :dir :system)

;; See also the built-in function sublis-var.  It evaluates ground applications of certain functions:
;; (sublis-var (acons 'a ''3 nil) '(binary-+ a a)) = '6
;; It does not resolve IFs when the test is a constant:
;; (sublis-var (acons 'a ''3 nil) '(if (equal '3 a) x y)) = (IF 'T X Y)

;; See also Axe functions like sublis-var-and-eval-basic, which can evaluate
;; certain ground function applications and simplify IFs with constant tests.

;; Apply ALIST to replace free variables in FORM.  Free variables not bound in ALIST are left alone.
;; This function is simpler than sublis-var and, unlike sublis-var, doesn't evaluate functions applied to constant arguments.
;; TODO: Consider simplifying IFs whose tests are constants (i.e., don't build both branches of such an IF).
(mutual-recursion
 (defund sublis-var-simple (alist term)
   (declare (xargs :measure (acl2-count term)
                   :guard (and (symbol-alistp alist) ; usually a symbol-term-alistp
                               (pseudo-termp term))))
   (cond ((variablep term)
          (let ((res (assoc-eq term alist)))
            (if res (cdr res) term)))
         ((fquotep term) term)
         (t (cons ;try fcons-term
             ;; Since lambdas are closed, we don't have to do anything to the lambda body:
             (ffn-symb term)
             (sublis-var-simple-lst alist (fargs term))))))

 (defund sublis-var-simple-lst (alist terms)
   (declare (xargs :measure (acl2-count terms)
                   :guard (and (symbol-alistp alist)
                               (pseudo-term-listp terms))))
   (if (endp terms)
       nil
     (cons (sublis-var-simple alist (car terms))
           (sublis-var-simple-lst alist (cdr terms))))))

(make-flag sublis-var-simple)

(defthm-flag-sublis-var-simple
  (defthm sublis-var-simple-of-nil
    (implies (pseudo-termp term)
             (equal (sublis-var-simple nil term)
                    term))
    :flag sublis-var-simple)
  (defthm sublis-var-simple-lst-of-nil
    (implies (pseudo-term-listp terms)
             (equal (sublis-var-simple-lst nil terms)
                    terms))
    :flag sublis-var-simple-lst)
  :hints (("Goal" :in-theory (enable sublis-var-simple
                                     sublis-var-simple-lst))))

(defthm true-listp-of-sublis-var-simple-lst
  (true-listp (sublis-var-simple-lst alist terms)))

(defthm len-of-sublis-var-simple-lst
  (equal (len (sublis-var-simple-lst alist terms))
         (len terms))
  :hints (("Goal" :in-theory (enable sublis-var-simple-lst))))

(defthm-flag-sublis-var-simple
  (defthm pseudo-termp-of-sublis-var-simple
    (implies (and (pseudo-termp term)
                  (symbol-term-alistp alist))
             (pseudo-termp (sublis-var-simple alist term)))
    :flag sublis-var-simple)
  (defthm pseudo-term-listp-of-sublis-var-simple-lst
    (implies (and (pseudo-term-listp terms)
                  (symbol-term-alistp alist))
             (pseudo-term-listp (sublis-var-simple-lst alist terms)))
    :flag sublis-var-simple-lst)
  :hints (("Goal" :in-theory (enable sublis-var-simple
                                     sublis-var-simple-lst)
           :expand ((pseudo-termp (cons (car term) (sublis-var-simple-lst alist (cdr term))))))))

(defthm car-of-sublis-var-simple
  (equal (car (sublis-var-simple alist term))
         (if (variablep term)
             (if (assoc-eq term alist)
                 (cadr (assoc-eq term alist))
               nil)
           (car term)))
  :hints (("Goal" :in-theory (enable sublis-var-simple))))

(defthm consp-of-sublis-var-simple
  (implies (consp term)
           (consp (sublis-var-simple alist term)))
  :hints (("Goal" :expand ((sublis-var-simple alist term)))))

(defthm cdr-of-sublis-var-simple
  (equal (cdr (sublis-var-simple alist term))
         (if (variablep term)
             (if (assoc-eq term alist)
                 (cddr (assoc-eq term alist))
               nil)
           (if (equal 'quote (car term))
               (cdr term)
             (sublis-var-simple-lst alist (cdr term)))))
  :hints (("Goal" :in-theory (enable sublis-var-simple))))

(defthm car-of-sublis-var-simple-lst
  (implies (consp terms)
           (equal (car (sublis-var-simple-lst alist terms))
                  (sublis-var-simple alist (car terms))))
  :hints (("Goal" :expand (sublis-var-simple-lst alist terms)
           :in-theory (enable sublis-var-simple-lst))))

(defthm-flag-sublis-var-simple
  (defthm sublis-var-simple-of-nil
    (implies (pseudo-termp term)
             (equal (sublis-var-simple nil term)
                    term))
    :flag sublis-var-simple)
  (defthm sublis-var-simple-lst-of-nil
    (implies (pseudo-term-listp terms)
             (equal (sublis-var-simple-lst nil terms)
                    terms))
    :flag sublis-var-simple-lst))
