; Copyright (C) 2014, Regents of the University of Texas
; Written by David Rager (original date April, 2012)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; After verifying the guards of subst-var, it would be good to change the name
; of this book to subst-expr.lisp and finish verifying the guard of subst-expr.

(include-book "sublis-var") ; for verification of cons-term

(local
 (include-book "pseudo-termp-lemmas"))

(include-book "subst-var")

(verify-termination subst-expr1
                    (declare (xargs :verify-guards nil)))

(local
 (defun subst-expr1-flg (flg new old x)
   (cond
    (flg ; subst-expr1-lst
     (cond ((endp x) nil)
           (t (cons (subst-expr1-flg nil new old (car x))
                    (subst-expr1-flg t new old (cdr x))))))
    (t ; subst-expr1
     (cond ((equal x old) new)
           ((variablep x) x)
           ((fquotep x) x)
           (t (cons-term (ffn-symb x)
                      (subst-expr1-flg t new old (fargs x)))))))))

(local
 (defthmd subst-expr1-flg-property
   (equal (subst-expr1-flg flg new old x)
          (if flg
              (subst-expr1-lst new old x)
            (subst-expr1 new old x)))))

(local
 (defthm subst-expr1-flg-preserves-len
   (implies flg
            (equal (len (subst-expr1-flg flg vars terms x))
                   (len x)))))

(local
 (defthm pseudo-termp-subst-expr1-flg
   (implies (and (pseudo-termp new)
                 (pseudo-termp old)
                 (if flg
                     (pseudo-term-listp x)
                   (pseudo-termp x)))
            (if flg
                (pseudo-term-listp (subst-expr1-flg flg new old x))
              (pseudo-termp (subst-expr1-flg flg new old x))))
   :rule-classes nil))

(defthm pseudo-term-listp-subst-expr1-lst
  (implies (and (pseudo-termp new)
                (pseudo-termp old)
                (pseudo-term-listp args))
              (pseudo-term-listp (subst-expr1-lst new old args)))
  :hints (("Goal"
           :in-theory (enable subst-expr1-flg-property)
           :use ((:instance pseudo-termp-subst-expr1-flg
                            (flg t)
                            (x args))))))

(defthm pseudo-term-listp-subst-expr1
  (implies (and (pseudo-termp new)
                (pseudo-termp old)
                (pseudo-termp term))
              (pseudo-termp (subst-expr1 new old term)))
  :hints (("Goal"
           :in-theory (enable subst-expr1-flg-property)
           :use ((:instance pseudo-termp-subst-expr1-flg
                            (flg nil)
                            (x term))))))

(verify-guards subst-expr1)

(verify-termination subst-expr-error)

(verify-guards subst-expr-error)

(verify-termination subst-expr)
