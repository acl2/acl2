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

(include-book "symbol-term-alistp")
(include-book "tools/flag" :dir :system)

;; See also the built-in function sublis-var.  It evaluates ground applications of certain functions:
;; (sublis-var (acons 'a ''3 nil) '(binary-+ a a)) = '6
;; It does not resolve IFs when the test is a constant:
;; (sublis-var (acons 'a ''3 nil) '(if (equal '3 a) x y)) = (IF 'T X Y)

;; See also Axe functions like my-sublis-var-and-eval-basic, which can evaluate
;; certain ground function applications and simplify IFs with constant tests.

;; Apply ALIST to replace free variables in FORM.  Free variables not bound in ALIST are left alone.
;; This function is simpler than sublis-var and, unlike sublis-var, doesn't evaluate functions applied to constant arguments.
;; TODO: Consider simplifying IFs whose tests are constants (i.e., don't build both branches of such an IF).
;; TODO: Rename sublis-var-simple?
;TODO change the formals of my-sublis-var and my-sublis-var-lst to be term and terms, not form and l?
(mutual-recursion
 (defund my-sublis-var (alist form) ;todo: call this 'term'?
   (declare (xargs :measure (acl2-count form)
                   :guard (and (symbol-alistp alist) ; usually a symbol-term-alistp
                               (pseudo-termp form))))
   (cond ((variablep form)
          (let ((a (assoc-eq form alist)))
            (cond (a (cdr a)) (t form))))
         ((fquotep form) form)
         (t (cons ;try fcons-term
             (ffn-symb form)
             (my-sublis-var-lst alist (fargs form))))))

 (defund my-sublis-var-lst (alist l)
   (declare (xargs :measure (acl2-count l)
                   :guard (and (symbol-alistp alist)
                               (pseudo-term-listp l))))
   (if (endp l) ;(null l)
       nil
     (cons (my-sublis-var alist (car l))
           (my-sublis-var-lst alist (cdr l))))))

(make-flag my-sublis-var)

(defthm-flag-my-sublis-var
  (defthm my-sublis-var-of-nil
    (implies (pseudo-termp form)
             (equal (my-sublis-var nil form)
                    form))
    :flag my-sublis-var)
  (defthm my-sublis-var-lst-of-nil
    (implies (pseudo-term-listp l)
             (equal (my-sublis-var-lst nil l)
                    l))
    :flag my-sublis-var-lst)
  :hints (("Goal" :in-theory (enable my-sublis-var
                                     my-sublis-var-lst))))

(defthm true-listp-of-my-sublis-var-lst
  (true-listp (my-sublis-var-lst alist terms)))

(defthm len-of-my-sublis-var-lst
  (equal (len (my-sublis-var-lst alist l))
         (len l))
  :hints (("Goal" :in-theory (enable my-sublis-var-lst))))

(defthm-flag-my-sublis-var
  (defthm pseudo-termp-of-my-sublis-var
    (implies (and (pseudo-termp form)
                  (symbol-term-alistp alist))
             (pseudo-termp (my-sublis-var alist form)))
    :flag my-sublis-var)
  (defthm pseudo-term-listp-of-my-sublis-var-lst
    (implies (and (pseudo-term-listp l)
                  (symbol-term-alistp alist))
             (pseudo-term-listp (my-sublis-var-lst alist l)))
    :flag my-sublis-var-lst)
  :hints (("Goal" :in-theory (enable my-sublis-var
                                     my-sublis-var-lst)
           :expand ((pseudo-termp (cons (car form) (my-sublis-var-lst alist (cdr form))))))))

(defthm car-of-my-sublis-var
  (equal (car (my-sublis-var alist form))
         (if (variablep form)
             (if (assoc-eq form alist)
                 (cadr (assoc-eq form alist))
               nil)
           (car form)))
  :hints (("Goal" :in-theory (enable my-sublis-var))))

(defthm consp-of-my-sublis-var
  (implies (consp term)
           (consp (my-sublis-var alist term)))
  :hints (("Goal" :expand ((my-sublis-var alist term)))))

(defthm cdr-of-my-sublis-var
  (equal (cdr (my-sublis-var alist form))
         (if (variablep form)
             (if (assoc-eq form alist)
                 (cddr (assoc-eq form alist))
               nil)
           (if (equal 'quote (car form))
               (cdr form)
             (my-sublis-var-lst alist (cdr form)))))
  :hints (("Goal" :in-theory (enable my-sublis-var))))

(defthm car-of-my-sublis-var-lst
  (implies (consp l)
           (equal (car (my-sublis-var-lst alist l))
                  (my-sublis-var alist (car l))))
  :hints (("Goal" :expand (my-sublis-var-lst alist l)
           :in-theory (enable my-sublis-var-lst))))

(defthm-flag-my-sublis-var
  (defthm my-sublis-var-of-nil
    (implies (pseudo-termp form)
             (equal (my-sublis-var nil form)
                    form))
    :flag my-sublis-var)
  (defthm my-sublis-var-lst-of-nil
    (implies (pseudo-term-listp l)
             (equal (my-sublis-var-lst nil l)
                    l))
    :flag my-sublis-var-lst))
