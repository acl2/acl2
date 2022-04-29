; Copyright (C) 2014, Regents of the University of Texas
; Written by David Rager (original date April, 2012)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Modified 8/2016 by Matt Kaufmann, so that termination and guards are also
; verified for remove-lambdas (and also remove-lambdas1 and
; remove-lambdas-lst).  That work is added here because it depends on
; properties of subcor-var that are local to this book.

(in-package "ACL2")

(include-book "sublis-var") ; for verification of cons-term

(local
 (include-book "pseudo-termp-lemmas"))

(verify-termination subcor-var1)

(verify-termination subcor-var
                    (declare (xargs :verify-guards nil)))

(local
 (defun subcor-var-flg (flg vars terms x)
   (cond
    (flg ; subcor-var-lst
     (cond ((endp x) nil)
           (t (cons (subcor-var-flg nil vars terms (car x))
                    (subcor-var-flg t vars terms (cdr x))))))
    (t ; subcor-var
     (cond ((variablep x)
            (subcor-var1 vars terms x))
           ((fquotep x) x)
           (t (cons-term (ffn-symb x)
                         (subcor-var-flg t vars terms (fargs x)))))))))

(local
 (defthmd subcor-var-flg-property
   (equal (subcor-var-flg flg vars term x)
          (if flg
              (subcor-var-lst vars term x)
            (subcor-var vars term x)))))

(local
 (defthm subcor-var-flg-preserves-len
   (implies flg
            (equal (len (subcor-var-flg flg vars terms x))
                   (len x)))))

(local
 (defthm pseudo-termp-subcor-var-flg
   (implies (and (symbol-listp vars)
                 (pseudo-term-listp terms)
                 (equal (len vars) (len terms))
                 (if flg
                     (pseudo-term-listp x)
                   (pseudo-termp x)))
            (if flg
                (pseudo-term-listp (subcor-var-flg flg vars terms x))
              (pseudo-termp (subcor-var-flg flg vars terms x))))
   :rule-classes nil))

(defthm pseudo-term-listp-subcor-var-lst
  (implies (and (symbol-listp vars)
                (pseudo-term-listp terms)
                (equal (len vars) (len terms))
                (pseudo-term-listp forms))
           (pseudo-term-listp (subcor-var-lst vars terms forms)))
  :hints (("Goal"
           :in-theory (enable subcor-var-flg-property)
           :use ((:instance pseudo-termp-subcor-var-flg
                            (flg t)
                            (x forms))))))

(defthm pseudo-term-listp-subcor-var
  (implies (and (symbol-listp vars)
                (pseudo-term-listp terms)
                (equal (len vars) (len terms))
                (pseudo-termp form))
           (pseudo-termp (subcor-var vars terms form)))
  :hints (("Goal"
           :in-theory (enable subcor-var-flg-property)
           :use ((:instance pseudo-termp-subcor-var-flg
                            (flg nil)
                            (x form))))))

(verify-guards subcor-var)

; The following events verify termination and guards for remove-lambdas (and
; also for remove-lambdas1 and remove-lambdas-lst).

(verify-termination remove-lambdas1) ; and remove-lambdas-lst
(verify-termination remove-lambdas)

(local (include-book "tools/flag" :dir :system))

(local (make-flag flag-remove-lambdas remove-lambdas1))

; Useful here: pseudo-term-listp-subcor-var-lst
; and pseudo-term-listp-subcor-var, proved above.

(local
 (defthm len-mv-nth-1-remove-lambdas-lst
   (equal (len (mv-nth 1 (remove-lambdas-lst x)))
          (len x))))

(local
 (defthm-flag-remove-lambdas
   (defthm pseudo-termp-mv-nth-1-remove-lambdas1
     (implies (pseudo-termp term)
              (pseudo-termp (mv-nth 1 (remove-lambdas1 term))))
     :flag remove-lambdas1)
   (defthm pseudo-term-listp-mv-nth-1-remove-lambdas-lst
     (implies (pseudo-term-listp termlist)
              (pseudo-term-listp (mv-nth 1 (remove-lambdas-lst termlist))))
     :flag remove-lambdas-lst)))

(local
 (defthm true-listp-mv-nth-1-remove-lambdas-lst
   (implies (force (true-listp lst))
            (true-listp (mv-nth 1 (remove-lambdas-lst lst))))
   :rule-classes :type-prescription))

(verify-guards remove-lambdas1) ; and remove-lambdas-lst
(verify-guards remove-lambdas)

