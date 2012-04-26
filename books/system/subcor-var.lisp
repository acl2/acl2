(in-package "ACL2")

(include-book "sublis-var") ; for verification of cons-term

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
 (defthm subcor-var-flg-lambda-lemma
   (implies (and (pseudo-termp x)
                 (consp x)
                 (not (symbolp (car x))))
            (and (true-listp (car x))
                 (equal (length (car x)) 3)
                 (eq (car (car x)) 'lambda)
                 (symbol-listp (cadr (car x)))
                 (pseudo-termp (caddr (car x)))
                 (equal (length (cadr (car x)))
                        (length (cdr x)))))))
           
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

(local
 (defthm pseudo-termp-implies-pseudo-term-listp-cdr
   (implies (and (pseudo-termp x)
                 (consp x)
                 (not (equal (car x) 'quote)))
            (pseudo-term-listp (cdr x)))))

(local
 (defthm pseudo-term-listp-implies-true-listp
   (implies (pseudo-term-listp x)
            (true-listp x))))

(verify-guards subcor-var)
