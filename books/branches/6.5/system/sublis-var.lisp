; Copyright (C) 2014, Regents of the University of Texas
; Written by Matt Kaufmann (original date April, 2012)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(verify-termination quote-listp) ; and guards

(defthm character-listp-make-character-list
  (character-listp (make-character-list x)))

(verify-termination cons-term1) ; and guards

(verify-termination cons-term) ; and guards

(verify-termination cons-term1-mv2) ; and guards

(verify-termination sublis-var1
                    (declare (xargs :verify-guards nil)))

(local
 (defun sublis-var1-flg (flg alist x)
   (cond
    (flg ; sublis-var1-lst
     (cond ((endp x)
            (mv nil x))
           (t (mv-let (changedp1 term)
                      (sublis-var1-flg nil alist (car x))
                      (mv-let (changedp2 lst)
                              (sublis-var1-flg t alist (cdr x))
                              (cond ((or changedp1 changedp2)
                                     (mv t (cons term lst)))
                                    (t (mv nil x))))))))
    (t ; sublis-var1
     (cond ((variablep x)
            (let ((a (assoc-eq x alist)))
              (cond (a (mv (not (eq x (cdr a)))
                           (cdr a)))
                    (t (mv nil x)))))
           ((fquotep x)
            (mv nil x))
           (t (mv-let (changedp lst)
                      (sublis-var1-flg t alist (fargs x))
                      (let ((fn (ffn-symb x)))
                        (cond (changedp (mv t (cons-term fn lst)))
                              ((and (symbolp fn) ; optimization
                                    (quote-listp lst))
                               (cons-term1-mv2 fn lst x))
                              (t (mv nil x)))))))))))

(local
 (defthmd sublis-var1-flg-property
   (equal (sublis-var1-flg flg alist x)
          (if flg
              (sublis-var1-lst alist x)
            (sublis-var1 alist x)))))

(defthm pseudo-termp-cdr-assoc-equal
  (implies (pseudo-term-listp (strip-cdrs alist))
           (pseudo-termp (cdr (assoc-equal x alist)))))

(local
 (defthm sublis-var1-flg-preserves-len
   (implies flg
            (equal (len (mv-nth 1 (sublis-var1-flg flg alist x)))
                   (len x)))))

(local
 (defthm pseudo-termp-sublis-var1-flg
   (implies (and (symbol-alistp alist)
                 (pseudo-term-listp (strip-cdrs alist))
                 (if flg
                     (pseudo-term-listp x)
                   (pseudo-termp x)))
            (if flg
                (pseudo-term-listp (mv-nth 1 (sublis-var1-flg flg alist x)))
              (pseudo-termp (mv-nth 1 (sublis-var1-flg flg alist x)))))
   :rule-classes nil))

(defthm pseudo-termp-sublis-var1
  (implies (and (symbol-alistp alist)
                (pseudo-term-listp (strip-cdrs alist))
                (pseudo-termp x))
           (pseudo-termp (mv-nth 1 (sublis-var1 alist x))))
  :hints (("Goal"
           :in-theory (enable sublis-var1-flg-property)
           :use ((:instance pseudo-termp-sublis-var1-flg
                            (flg nil))))))

(defthm pseudo-termp-sublis-var1-lst
  (implies (and (symbol-alistp alist)
                (pseudo-term-listp (strip-cdrs alist))
                (pseudo-term-listp x))
           (pseudo-term-listp (mv-nth 1 (sublis-var1-lst alist x))))
  :hints (("Goal"
           :in-theory (enable sublis-var1-flg-property)
           :use ((:instance pseudo-termp-sublis-var1-flg
                            (flg t))))))

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

(verify-guards sublis-var1) ; and sublis-var1-lst

(verify-termination sublis-var) ; and guards

(verify-termination sublis-var-lst) ; and guards
