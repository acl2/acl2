;; Copyright (C) 2026, The University of British Columbia
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "../top")

(encapsulate ()
  (defrule return-of-int-sym-consp
    (booleanp (int-sym-consp x)))

  (defrule return-of-int-sym-alist-p
    (booleanp (int-sym-alist-p x)))

  (defrule return-of-cons-int-sym
    (implies (and (integerp x)
                  (symbolp y))
             (int-sym-consp
               (cons x y)))
    :enable (int-sym-consp))

  (defrule return-of-cons-int-sym-consp-int-sym-alist-p
    (implies (and (int-sym-consp x)
                  (int-sym-alist-p y))
             (int-sym-alist-p
               (cons x y)))
    :enable (int-sym-consp
              int-sym-alist-p))

  (defrule return-of-cons-int-sym-consp-nil
    (implies (and (int-sym-consp x)
                  (null y))
             (int-sym-alist-p
               (cons x y)))
    :enable (int-sym-consp
              int-sym-alist-p))

  (defrule return-of-assoc-equal-int-sym-alist-p
    (implies (and (integerp x)
                  (int-sym-alist-p y))
             (maybe-int-sym-consp
               (assoc-equal x y)))
    :enable (maybe-int-sym-consp
              int-sym-consp
              int-sym-alist-p))

  (defrule return-of-equal-maybe-int-sym-consp-int-sym-consp
    (implies (and (maybe-int-sym-consp x)
                  (int-sym-consp y))
             (booleanp (equal x y))))

  (defrule return-of-int-sym-array-select
    (implies (and (int-sym-array-p x)
                  (integerp y))
             (maybe-int-sym-consp (int-sym-array-select x y))))

  (defrule return-of-int-sym-array-store
    (implies (and (int-sym-array-p x)
                  (integerp y)
                  (int-sym-consp z))
             (int-sym-array-p (int-sym-array-store x y z))))

  (defrule return-of-int-sym-array-from-al
    (implies (int-sym-alist-p x)
             (int-sym-array-p (int-sym-array-from-al x))))

  (add-smtlink-hint
    :int-sym-arrays
    (make-smtlink-hint
      :acl2types (append
                   (list (make-smt-acl2type :recognizer 'maybe-int-sym-consp)
                         (make-smt-acl2type :recognizer 'int-sym-consp)
                         (make-smt-acl2type :recognizer 'int-sym-alist-p)
                         (make-smt-acl2type :recognizer 'int-sym-array-p))
                   (smt::make-acl2types))
      :datatypes (append
                   (list
                     (make-smt-datatype-basic
                       :recognizer (make-smt-function :name 'int-sym-consp
                                                      :kind :basic)
                       :equal (make-smt-function :name 'equal))
                     (make-smt-datatype-basic
                       :recognizer (make-smt-function :name 'maybe-int-sym-consp
                                                      :kind :basic)
                       :equal (make-smt-function :name 'equal))
                     (make-smt-datatype-basic
                       :recognizer (make-smt-function :name 'int-sym-alist-p
                                                      :kind :basic)
                       :equal (make-smt-function :name 'equal))
                     (make-smt-datatype-basic
                       :recognizer (make-smt-function :name 'int-sym-array-p
                                                      :kind :basic)
                       :equal (make-smt-function :name 'equal)))
                   (smt::make-datatypes))
      :functions (append
                   (list
                     (make-smt-function :name 'int-sym-consp
                                        :kind :basic
                                        :returns (list (make-thm-spec
                                                         :formals '(x)
                                                         :thm
                                                         'return-of-maybe-int-sym-consp)))
                     (make-smt-function :name 'int-sym-alist-p
                                        :kind :basic
                                        :returns (list (make-thm-spec
                                                         :formals '(x)
                                                         :thm
                                                         'return-of-int-sym-alist-p)))
                     (make-smt-function :name 'cons
                                        :kind :basic
                                        :returns (list (make-thm-spec
                                                         :formals '(x y)
                                                         :thm
                                                         'return-of-cons-int-sym)
                                                       (make-thm-spec
                                                         :formals '(x y)
                                                         :thm
                                                         'return-of-cons-int-sym-consp-int-sym-alist-p)
                                                       (make-thm-spec
                                                         :formals '(x y)
                                                         :thm
                                                         'return-of-cons-int-sym-consp-nil)
                                                       ))
                     (make-smt-function :name 'assoc-equal
                                        :kind :basic
                                        :returns (list (make-thm-spec
                                                         :formals '(x y)
                                                         :thm
                                                         'return-of-assoc-equal-int-sym-alist-p)))
                     (make-smt-function :name 'int-sym-array-select
                                        :kind :basic
                                        :returns (list (make-thm-spec
                                                         :formals '(x y)
                                                         :thm
                                                         'return-of-int-sym-array-select)))
                     (make-smt-function :name 'int-sym-array-store
                                        :kind :basic
                                        :returns (list (make-thm-spec
                                                         :formals '(x y z)
                                                         :thm
                                                         'return-of-int-sym-array-store)))
                     (make-smt-function :name 'int-sym-array-from-al
                                        :kind :basic
                                        :returns (list (make-thm-spec
                                                         :formals '(x)
                                                         :thm
                                                         'return-of-int-sym-array-from-al)))
                     (make-smt-function :name 'equal
                                        :kind :basic
                                        :returns (list (make-thm-spec
                                                         :formals '(x y)
                                                         :thm
                                                         'return-of-equal-maybe-int-sym-consp-int-sym-consp)
                                                       (make-thm-spec
                                                         :formals '(x y)
                                                         :thm 'return-of-equal-booleanp)
                                                       (make-thm-spec
                                                         :formals '(x y)
                                                         :thm 'return-of-equal-integerp)
                                                       (make-thm-spec
                                                         :formals '(x y)
                                                         :thm 'return-of-equal-rationalp)
                                                       (make-thm-spec
                                                         :formals '(x y)
                                                         :thm
                                                         'return-of-equal-symbolp))))
                   (make-basic-functions))
      :replaces (make-basic-replaces)
      :configurations (make-smt-config :smt-cnf (default-smt-cnf)))))
