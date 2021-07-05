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
;; TODO change the formals of sublis-var-simple and sublis-var-simple-lst to be term and terms, not form and l?
(mutual-recursion
 (defund sublis-var-simple (alist form) ;todo: call this 'term'?
   (declare (xargs :measure (acl2-count form)
                   :guard (and (symbol-alistp alist) ; usually a symbol-term-alistp
                               (pseudo-termp form))))
   (cond ((variablep form)
          (let ((a (assoc-eq form alist)))
            (cond (a (cdr a)) (t form))))
         ((fquotep form) form)
         (t (cons ;try fcons-term
             (ffn-symb form)
             (sublis-var-simple-lst alist (fargs form))))))

 (defund sublis-var-simple-lst (alist l)
   (declare (xargs :measure (acl2-count l)
                   :guard (and (symbol-alistp alist)
                               (pseudo-term-listp l))))
   (if (endp l) ;(null l)
       nil
     (cons (sublis-var-simple alist (car l))
           (sublis-var-simple-lst alist (cdr l))))))

(make-flag sublis-var-simple)

(defthm-flag-sublis-var-simple
  (defthm sublis-var-simple-of-nil
    (implies (pseudo-termp form)
             (equal (sublis-var-simple nil form)
                    form))
    :flag sublis-var-simple)
  (defthm sublis-var-simple-lst-of-nil
    (implies (pseudo-term-listp l)
             (equal (sublis-var-simple-lst nil l)
                    l))
    :flag sublis-var-simple-lst)
  :hints (("Goal" :in-theory (enable sublis-var-simple
                                     sublis-var-simple-lst))))

(defthm true-listp-of-sublis-var-simple-lst
  (true-listp (sublis-var-simple-lst alist terms)))

(defthm len-of-sublis-var-simple-lst
  (equal (len (sublis-var-simple-lst alist l))
         (len l))
  :hints (("Goal" :in-theory (enable sublis-var-simple-lst))))

(defthm-flag-sublis-var-simple
  (defthm pseudo-termp-of-sublis-var-simple
    (implies (and (pseudo-termp form)
                  (symbol-term-alistp alist))
             (pseudo-termp (sublis-var-simple alist form)))
    :flag sublis-var-simple)
  (defthm pseudo-term-listp-of-sublis-var-simple-lst
    (implies (and (pseudo-term-listp l)
                  (symbol-term-alistp alist))
             (pseudo-term-listp (sublis-var-simple-lst alist l)))
    :flag sublis-var-simple-lst)
  :hints (("Goal" :in-theory (enable sublis-var-simple
                                     sublis-var-simple-lst)
           :expand ((pseudo-termp (cons (car form) (sublis-var-simple-lst alist (cdr form))))))))

(defthm car-of-sublis-var-simple
  (equal (car (sublis-var-simple alist form))
         (if (variablep form)
             (if (assoc-eq form alist)
                 (cadr (assoc-eq form alist))
               nil)
           (car form)))
  :hints (("Goal" :in-theory (enable sublis-var-simple))))

(defthm consp-of-sublis-var-simple
  (implies (consp term)
           (consp (sublis-var-simple alist term)))
  :hints (("Goal" :expand ((sublis-var-simple alist term)))))

(defthm cdr-of-sublis-var-simple
  (equal (cdr (sublis-var-simple alist form))
         (if (variablep form)
             (if (assoc-eq form alist)
                 (cddr (assoc-eq form alist))
               nil)
           (if (equal 'quote (car form))
               (cdr form)
             (sublis-var-simple-lst alist (cdr form)))))
  :hints (("Goal" :in-theory (enable sublis-var-simple))))

(defthm car-of-sublis-var-simple-lst
  (implies (consp l)
           (equal (car (sublis-var-simple-lst alist l))
                  (sublis-var-simple alist (car l))))
  :hints (("Goal" :expand (sublis-var-simple-lst alist l)
           :in-theory (enable sublis-var-simple-lst))))

(defthm-flag-sublis-var-simple
  (defthm sublis-var-simple-of-nil
    (implies (pseudo-termp form)
             (equal (sublis-var-simple nil form)
                    form))
    :flag sublis-var-simple)
  (defthm sublis-var-simple-lst-of-nil
    (implies (pseudo-term-listp l)
             (equal (sublis-var-simple-lst nil l)
                    l))
    :flag sublis-var-simple-lst))
