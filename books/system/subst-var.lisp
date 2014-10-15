; Copyright (C) 2014, Regents of the University of Texas
; Written by David Rager (original date April, 2012)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "sublis-var") ; for verification of cons-term

(local
 (include-book "pseudo-termp-lemmas"))

(verify-termination subst-var
                    (declare (xargs :verify-guards nil)))

(local
 (defun subst-var-flg (flg new old x)
   (cond (flg ; subst-var-lst
          (cond ((endp x) nil)
                (t (cons (subst-var-flg nil new old (car x))
                         (subst-var-flg t new old (cdr x))))))
         (t ; subst-var
          (cond ((variablep x)
                 (cond ((eq x old) new)
                       (t x)))
                ((fquotep x) x)
                (t (cons-term (ffn-symb x)
                              (subst-var-flg t new old (fargs x)))))))))
(local
 (defthmd subst-var-flg-property
   (equal (subst-var-flg flg new old x)
          (if flg
              (subst-var-lst new old x)
            (subst-var new old x)))))

(local
 (defthm subst-var-flg-preserves-len
   (implies flg
            (equal (len (subst-var-flg flg vars terms x))
                   (len x)))))

(local
 (defthm pseudo-termp-subst-var-flg
   (implies (and (pseudo-termp new)
                 (variablep old)
                 (if flg
                     (pseudo-term-listp x)
                   (pseudo-termp x)))
            (if flg
                (pseudo-term-listp (subst-var-flg flg new old x))
              (pseudo-termp (subst-var-flg flg new old x))))
   :rule-classes nil))

(defthm pseudo-term-listp-subst-var-lst
  (implies (and (pseudo-termp new)
                (variablep old)
                (pseudo-term-listp l))
           (pseudo-term-listp (subst-var-lst new old l)))
  :hints (("Goal"
           :in-theory (enable subst-var-flg-property)
           :use ((:instance pseudo-termp-subst-var-flg
                            (flg t)
                            (x l))))))

(defthm pseudo-termp-subst-var
  (implies (and (pseudo-termp new)
                (variablep old)
                (pseudo-termp form))
           (pseudo-termp (subst-var new old form)))
  :hints (("Goal"
           :in-theory (enable subst-var-flg-property)
           :use ((:instance pseudo-termp-subst-var-flg
                            (flg nil)
                            (x form))))))

(verify-guards subst-var)
