(in-package "SMT")
(include-book "std/util/define" :dir :system)
(include-book "../hint-interface")

(define foo ((x integerp)
             (y rationalp))
  :returns (res rationalp)
  (b* ((x (ifix x))
       (y (rfix y)))
    (+ x y)))

(defthm return-of-integerp
  (booleanp (integerp x)))

(defthm return-of-rationalp
  (booleanp (rationalp x)))

(defthm return-of-ifix
  (integerp (ifix x)))

(defthm return-of-rfix
  (rationalp (rfix x)))

(defthm return-of-equal
  (booleanp (equal x y)))

(defthm return-of-not
  (booleanp (not x)))

(defthm return-of-equal-integer
  (implies (and (integerp x) (integerp y))
           (booleanp (equal x y))))

(defthm return-of-binary-+
  (implies (and (integerp x)
                (integerp y))
           (integerp (binary-+ x y))))

(defthm return-of-binary-+-rationalp
  (implies (and (rationalp x)
                (rationalp y))
           (rationalp (binary-+ x y))))

(defthm return-of-binary-*
  (implies (and (integerp x)
                (integerp y))
           (integerp (binary-* x y))))

(defthm return-of-binary-*-rationalp
  (implies (and (rationalp x)
                (rationalp y))
           (rationalp (binary-* x y))))

(defthm return-of-<
  (implies (and (rationalp x)
                (rationalp y))
           (booleanp (< x y))))

(defun smt-fun ()
  `(,(make-smt-function
      :name 'integerp
      :formals '(x)
      :returns '(return-of-integerp)
      :depth 0)
    ,(make-smt-function
      :name 'rationalp
      :formals '(x)
      :returns '(return-of-rationalp)
      :depth 0)
    ,(make-smt-function
      :name 'ifix
      :formals '(x)
      :returns '(return-of-ifix)
      :depth 0)
    ,(make-smt-function
      :name 'rfix
      :formals '(x)
      :returns '(return-of-rfix)
      :depth 0)
    ,(make-smt-function
      :name 'equal
      :formals '(x y)
      :returns '(return-of-equal return-of-equal-integer)
      :depth 0)
    ,(make-smt-function
      :name 'not
      :formals '(x)
      :returns '(return-of-not)
      :depth 0)
    ,(make-smt-function
      :name 'binary-+
      :formals '(x y)
      :returns '(return-of-binary-+ return-of-binary-+-rationalp)
      :depth 0)
    ,(make-smt-function
      :name 'binary-*
      :formals '(x y)
      :returns '(return-of-binary-* return-of-binary-*-rationalp)
      :depth 0)
    ,(make-smt-function
      :name '<
      :formals '(x y)
      :returns '(return-of-<)
      :depth 0)))

(defthm integerp-implies-rationalp
  (implies (integerp x) (rationalp x)))

(defun types-info ()
  `(,(make-smt-type :recognizer 'integerp
                    :supertypes `(,(make-smt-sub/supertype
                                    :type 'rationalp
                                    :formals '(x)
                                    :thm 'integerp-implies-rationalp)))
    ,(make-smt-type :recognizer 'rationalp)))

(defun my-hint ()
  (make-smtlink-hint
   :functions (smt-fun)
   :types (types-info)
   :wrld-fn-len 99))
