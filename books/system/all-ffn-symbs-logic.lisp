(in-package "ACL2")

(verify-termination all-ffn-symbs
  (declare (xargs :verify-guards nil))) ; and all-ffn-symbs-lst

(defun all-ffn-symbs-flg (flg x ans)
  (cond
   (flg (cond ((endp x) ans)
              (t (all-ffn-symbs-flg t (cdr x)
                                    (all-ffn-symbs-flg nil (car x) ans)))))
   ((variablep x) ans)
   ((fquotep x) ans)
   (t (all-ffn-symbs-flg
       t
       (fargs x)
       (cond ((flambda-applicationp x)
              (all-ffn-symbs-flg nil (lambda-body (ffn-symb x)) ans))
             (t (add-to-set-eq (ffn-symb x) ans)))))))

(defthm symbol-listp-all-ffn-symbs-flg
  (implies (and (symbol-listp ans)
                (if flg (pseudo-term-listp x) (pseudo-termp x)))
           (symbol-listp (all-ffn-symbs-flg flg x ans)))
  :rule-classes nil)

(defthm all-ffn-symbs-flg-is-all-ffn-symbs
  (equal (all-ffn-symbs-flg flg x ans)
         (if flg
             (all-ffn-symbs-lst x ans)
           (all-ffn-symbs x ans))))

(defthm symbol-listp-all-ffn-symbs
  (implies (and (symbol-listp ans)
                (pseudo-termp x))
           (symbol-listp (all-ffn-symbs x ans)))
  :hints (("Goal" :use ((:instance symbol-listp-all-ffn-symbs-flg
                                   (flg nil))))))

(defthm symbol-listp-all-ffn-symbs-lst
  (implies (and (symbol-listp ans)
                (pseudo-term-listp x))
           (symbol-listp (all-ffn-symbs-lst x ans)))
  :hints (("Goal" :use ((:instance symbol-listp-all-ffn-symbs-flg
                                   (flg t))))))

(verify-guards all-ffn-symbs
  :hints (("Goal" :use all-ffn-symbs-flg-is-all-ffn-symbs)))
