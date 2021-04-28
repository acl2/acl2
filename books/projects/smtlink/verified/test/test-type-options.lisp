(in-package "SMT")
(include-book "../type-options")

(defalist rational-integer-alist
  :key-type rationalp
  :val-type integerp
  :pred rational-integer-alistp
  :true-listp t)

(define rational-integer-cons-p ((x t))
  (and (consp x)
       (rationalp (car x))
       (integerp (cdr x))))

(easy-fix rational-integer-cons (cons 0 0))

(defoption maybe-integerp integerp :pred maybe-integerp)

(defoption maybe-rational-integer-consp rational-integer-cons-p
  :pred maybe-rational-integer-consp)

(deflist rational-list
  :elt-type rationalp
  :true-listp t)

(defthm integerp-implies-maybe-integerp
  (implies (integerp x) (maybe-integerp x)))

(defthm integerp-implies-rationalp
  (implies (integerp x) (rationalp x)))

(defthm rational-integer-cons-p-implies-maybe-rational-integer-consp
  (implies (rational-integer-cons-p x) (maybe-rational-integer-consp x)))

(defun supertype ()
  `((integerp . (,(make-smt-sub/supertype
                   :type 'rationalp
                   :formals '(x)
                   :thm 'integerp-implies-rationalp)
                 ,(make-smt-sub/supertype
                   :type 'maybe-integerp
                   :formals '(x)
                   :thm 'integerp-implies-maybe-integerp)))
    (rationalp . nil)
    (symbolp . nil)
    (booleanp . nil)
    (rational-integer-cons-p . (,(make-smt-sub/supertype
                                  :type 'maybe-rational-integer-consp
                                  :formals '(x)
                                  :thm
                                  'rational-integer-cons-p-implies-maybe-rational-integer-consp)))
    (rational-integer-alistp . nil)
    (maybe-integerp . nil)
    (maybe-rational-integer-consp . nil)
    (rational-list-p . nil)
    ))

(defthm maybe-integerp-can-be-integerp
  (implies (and (maybe-integerp x) x)
           (integerp x)))

(defthm maybe-rational-integer-consp-can-be-rational-integer-cons-p
  (implies (and (maybe-rational-integer-consp x) x)
           (rational-integer-cons-p x)))

(defun subtype ()
  `((rationalp . nil)
    (maybe-integerp . (,(make-smt-sub/supertype
                         :type 'integerp
                         :formals '(x)
                         :thm 'maybe-integerp-can-be-integerp)))
    (integerp . nil)
    (symbolp . nil)
    (booleanp . nil)
    (maybe-rational-integer-consp . (,(make-smt-sub/supertype
                                       :type 'rational-integer-cons-p
                                       :formals '(x)
                                       :thm
                                       'maybe-rational-integer-consp-can-be-rational-integer-cons-p)))
    (rational-integer-alistp . nil)
    (rational-integer-cons-p . nil)
    (rational-list-p . nil)
    ))

(defthm return-of-assoc-equal
  (implies (and (rationalp y)
                (rational-integer-alistp x))
           (maybe-rational-integer-consp (assoc-equal y x)))
  :hints (("Goal" :in-theory (enable maybe-rational-integer-consp
                                     rational-integer-cons-p))))

(defthm return-of-cdr-maybe
  (implies (maybe-rational-integer-consp x)
           (maybe-integerp (cdr x)))
  :hints (("Goal" :in-theory (enable maybe-rational-integer-consp
                                     rational-integer-cons-p))))

(defthm return-of-cdr
  (implies (rational-integer-cons-p x)
           (integerp (cdr x)))
  :hints (("Goal" :in-theory (enable rational-integer-cons-p))))

(defthm return-of-not
  (implies (booleanp x)
           (booleanp (not x))))

(defthm return-of-car-rlistp
  (implies (and (rational-list-p x) x)
           (rationalp (car x))))

(defthm return-of-cdr-rlistp
  (implies (rational-list-p x)
           (rational-list-p (cdr x))))

(defthm return-of-cons
  (implies (and (rationalp x)
                (rational-list-p y))
           (and (rational-list-p (cons x y))
                (cons x y))))

(defthm return-of-<
  (implies (and (rationalp x)
                (rationalp y))
           (booleanp (< x y))))

(defthm return-of-binary-+
  (implies (and (integerp x)
                (integerp y))
           (integerp (binary-+ x y))))

(defthm return-of-binary-*
  (implies (and (integerp x)
                (integerp y))
           (integerp (binary-* x y))))

(defthm return-of-binary-+-rationalp
  (implies (and (rationalp x)
                (rationalp y))
           (rationalp (binary-+ x y))))

(defthm return-of-unary--
  (implies (integerp x)
           (integerp (unary-- x))))

(defthm return-of-unary---rationalp
  (implies (rationalp x)
           (rationalp (unary-- x))))

(defthm return-of-rational-integer-alistp
  (booleanp (rational-integer-alistp x)))

(defthm return-of-rational-list-p
  (booleanp (rational-list-p x)))

(defthm return-of-rationalp
  (booleanp (rationalp x)))

(defthm return-of-integerp
  (booleanp (integerp x)))

(defthm return-of-acons
  (implies (and (rationalp x)
                (integerp y)
                (rational-integer-alistp z))
           (rational-integer-alistp (acons x y z))))

(defthm return-of-ifix
  (integerp (ifix x)))

(defthm return-of-rfix
  (rationalp (rfix x)))

(defthm return-of-equal
  (booleanp (equal x y)))

(defthm return-of-equal-integer
  (implies (and (integerp x) (integerp y))
           (booleanp (equal x y))))

(defun rational-list-car (x)
  (if (consp x) (car x) (rfix x)))

(defthm replace-of-car
  (implies (and (rational-list-p x) x)
           (equal (car x) (rational-list-car x))))

(defun rational-list-cons (x y)
  (cons x y))

(defthm replace-of-cons
  (equal (cons x y) (rational-list-cons x y)))

;; assoc-equal: rational-integer-alistp -> maybe-rational-integer-consp
;; cdr: maybe-rational-integer-consp -> maybe-integerp &
;;      rational-integer-consp -> integerp
;; <: integerp integerp -> booleanp
;; binary-+: integerp integerp -> integerp
;; unary--: integerp -> integerp
(defun functions ()
  `((acons . (,(make-return-spec
                :formals '(x y z)
                :thm 'return-of-acons)))
    (assoc-equal . (,(make-return-spec
                      :formals '(y x)
                      :thm 'return-of-assoc-equal)))
    (car . (,(make-return-spec
              :formals '(x)
              :thm 'return-of-car-rlistp)))
    (cdr . (,(make-return-spec
              :formals '(x)
              :thm 'return-of-cdr-maybe)
            ,(make-return-spec
              :formals '(x)
              :thm 'return-of-cdr)
            ,(make-return-spec
              :formals '(x)
              :thm 'return-of-cdr-rlistp)))
    (cons . (,(make-return-spec
               :formals '(x y)
               :thm 'return-of-cons)))
    (< . (,(make-return-spec
            :formals '(x y)
            :thm 'return-of-<)))
    (binary-+ . (,(make-return-spec
                   :formals '(x y)
                   :thm 'return-of-binary-+)
                 ,(make-return-spec
                   :formals '(x y)
                   :thm 'return-of-binary-+-rationalp)))
    (binary-* . (,(make-return-spec
                   :formals '(x y)
                   :thm 'return-of-binary-*)))
    (unary-- . (,(make-return-spec
                  :formals '(x)
                  :thm 'return-of-unary--)
                ,(make-return-spec
                  :formals '(x)
                  :thm 'return-of-unary---rationalp)))
    (not . (,(make-return-spec
              :formals '(x)
              :thm 'return-of-not)))
    (rational-integer-alistp . (,(make-return-spec
                                  :formals '(x)
                                  :thm
                                  'return-of-rational-integer-alistp)))
    (rational-list-p . (,(make-return-spec
                          :formals '(x)
                          :thm 'return-of-rational-list-p)))
    (rationalp . (,(make-return-spec
                    :formals '(x)
                    :thm 'return-of-rationalp)))
    (integerp . (,(make-return-spec
                   :formals '(x)
                   :thm 'return-of-integerp)))
    (ifix . (,(make-return-spec
               :formals '(x)
               :thm 'return-of-ifix)))
    (rfix . (,(make-return-spec
               :formals '(x)
               :thm 'return-of-rfix)))
    (equal . (,(make-return-spec
                :formals '(x y)
                :thm 'return-of-equal)
              ,(make-return-spec
                :formals '(x y)
                :thm 'return-of-equal-integer)))))

(defun options ()
  (b* ((supertype (supertype))
       (subtype (subtype))
       (functions (functions)))
    (make-type-options
     :supertype supertype
     :subtype subtype
     :functions functions)))
