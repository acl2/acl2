;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (12th Oct 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "hint-interface")
(include-book "basic-theorems")

(define make-acl2types ()
  :returns (type-lst smt-acl2type-list-p)
  (list (make-smt-acl2type :recognizer 'symbolp)
        (make-smt-acl2type :recognizer 'booleanp)
        (make-smt-acl2type
         :recognizer 'integerp
         :supertypes (list (make-smt-sub/supertype
                            :type 'rationalp
                            :thm (make-thm-spec
                                  :formals '(x)
                                  :thm 'integerp-is-rationalp))))
        (make-smt-acl2type :recognizer 'rationalp)))

(define make-datatypes ()
  :returns (type-lst smt-datatype-list-p)
  (list (make-smt-datatype-basic
         :recognizer (make-smt-function :name 'symbolp
                                        :kind :basic
                                        :translation-hint
                                        (make-trans-hint
                                         :translation "Symbol_z3.z3Sym"))
         :equal (make-smt-function :name 'equal)
         :property-hints '((COMMON-LISP::TYPE-OF-SYMBOLP-EQUAL . nil)
                           (COMMON-LISP::REFLEXIVITY-OF-SYMBOLP-EQUAL . nil)
                           (COMMON-LISP::SYMMETRICITY-OF-SYMBOLP-EQUAL . nil)
                           (COMMON-LISP::TRANSITIVITY-OF-SYMBOLP-EQUAL . nil)
                           (COMMON-LISP::TYPE-OF-SYMBOLP . nil)))
        (make-smt-datatype-basic
         :recognizer (make-smt-function :name 'booleanp
                                        :kind :basic
                                        :translation-hint
                                        (make-trans-hint
                                         :translation "_SMT_.BoolSort()"))
         :equal (make-smt-function :name 'equal)
         :property-hints '((ACL2::TYPE-OF-BOOLEANP-EQUAL . nil)
                           (ACL2::REFLEXIVITY-OF-BOOLEANP-EQUAL . nil)
                           (ACL2::SYMMETRICITY-OF-BOOLEANP-EQUAL . nil)
                           (ACL2::TRANSITIVITY-OF-BOOLEANP-EQUAL . nil)
                           (ACL2::TYPE-OF-BOOLEANP . nil)))
        (make-smt-datatype-basic
         :recognizer (make-smt-function :name 'integerp
                                        :kind :basic
                                        :translation-hint
                                        (make-trans-hint
                                         :translation "_SMT_.IntSort()"))
         :equal (make-smt-function :name 'equal)
         :property-hints '((COMMON-LISP::TYPE-OF-INTEGERP-EQUAL . nil)
                           (COMMON-LISP::REFLEXIVITY-OF-INTEGERP-EQUAL . nil)
                           (COMMON-LISP::SYMMETRICITY-OF-INTEGERP-EQUAL . nil)
                           (COMMON-LISP::TRANSITIVITY-OF-INTEGERP-EQUAL . nil)
                           (COMMON-LISP::TYPE-OF-INTEGERP . nil)))
        (make-smt-datatype-basic
         :recognizer (make-smt-function :name 'rationalp
                                        :kind :basic
                                        :translation-hint
                                        (make-trans-hint
                                         :translation "_SMT_.RealSort()"))
         :equal (make-smt-function :name 'equal)
         :property-hints '((COMMON-LISP::TYPE-OF-RATIONALP-EQUAL . nil)
                           (COMMON-LISP::REFLEXIVITY-OF-RATIONALP-EQUAL . nil)
                           (COMMON-LISP::SYMMETRICITY-OF-RATIONALP-EQUAL . nil)
                           (COMMON-LISP::TRANSITIVITY-OF-RATIONALP-EQUAL . nil)
                           (COMMON-LISP::TYPE-OF-RATIONALP . nil)))))

(define make-basic-functions ()
  :returns (fun-lst smt-function-list-p)
  (list (make-smt-function :name 'symbolp
                           :kind :basic
                           :returns (list (make-thm-spec
                                            :formals '(x)
                                            :thm 'return-of-symbolp))
                           :translation-hint
                           (make-trans-hint :translation "Symbol_z3.z3Sym"))
        (make-smt-function :name 'integerp
                           :kind :basic
                           :returns (list (make-thm-spec
                                            :formals '(x)
                                            :thm 'return-of-integerp))
                           :translation-hint
                           (make-trans-hint :translation "_SMT_.IntSort()"))
        (make-smt-function :name 'booleanp
                           :kind :basic
                           :returns (list (make-thm-spec
                                            :formals '(x)
                                            :thm 'return-of-booleanp))
                           :translation-hint
                           (make-trans-hint :translation "_SMT_.BoolSort()"))
        (make-smt-function :name 'rationalp
                           :kind :basic
                           :returns (list (make-thm-spec
                                            :formals '(x)
                                            :thm 'return-of-rationalp))
                           :translation-hint
                           (make-trans-hint :translation "_SMT_.RealSort()"))
        (make-smt-function :name 'symbol-fix
                           :kind :basic
                           :returns (list (make-thm-spec
                                            :formals '(x)
                                            :thm 'return-of-symbol-fix)))
        (make-smt-function :name 'bool-fix
                           :kind :basic
                           :returns (list (make-thm-spec
                                            :formals '(x)
                                            :thm 'return-of-bool-fix)))
        (make-smt-function :name 'ifix
                           :kind :basic
                           :returns (list (make-thm-spec
                                            :formals '(x)
                                            :thm 'return-of-ifix)))
        (make-smt-function :name 'rfix
                           :kind :basic
                           :returns (list (make-thm-spec
                                            :formals '(x)
                                            :thm 'return-of-rfix)))
        (make-smt-function :name 'not
                           :kind :basic
                           :returns (list (make-thm-spec
                                            :formals '(x)
                                            :thm 'return-of-not))
                           :translation-hint
                           (make-trans-hint :translation "_SMT_.notx"))
        (make-smt-function :name 'equal
                           :kind :basic
                           :returns (list (make-thm-spec
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
                                            :thm 'return-of-equal-symbolp))
                           :translation-hint
                           (make-trans-hint :translation "_SMT_.equal"))
        (make-smt-function :name '<
                           :kind :basic
                           :returns (list (make-thm-spec
                                            :formals '(x y)
                                            :thm 'return-of-<-integerp)
                                          (make-thm-spec
                                            :formals '(x y)
                                            :thm 'return-of-<-rationalp-integerp)
                                          (make-thm-spec
                                            :formals '(x y)
                                            :thm
                                            'return-of-<-integerp-rationalp)
                                          (make-thm-spec
                                            :formals '(x y)
                                            :thm 'return-of-<-rationalp))
                           :translation-hint
                           (make-trans-hint :translation "_SMT_.lt"))
        (make-smt-function :name 'unary--
                           :kind :basic
                           :returns (list (make-thm-spec
                                            :formals '(x)
                                            :thm 'return-of-unary---integerp)
                                          (make-thm-spec
                                            :formals '(x)
                                            :thm 'return-of-unary---rationalp))
                           :translation-hint
                           (make-trans-hint :translation "_SMT_.negate"))
        (make-smt-function :name 'unary-/
                           :kind :basic
                           :returns (list (make-thm-spec
                                            :formals '(x)
                                            :thm 'return-of-unary-/-integerp)
                                          (make-thm-spec
                                            :formals '(x)
                                            :thm
                                            'return-of-unary-/-rationalp))
                           :translation-hint
                           (make-trans-hint :translation "_SMT_.reciprocal"))
        (make-smt-function :name 'binary-+
                           :kind :basic
                           :returns (list (make-thm-spec
                                            :formals '(x y)
                                            :thm 'return-of-binary-+-integerp)
                                          (make-thm-spec
                                            :formals '(x y)
                                            :thm 'return-of-binary-+-rationalp-integerp)
                                          (make-thm-spec
                                            :formals '(x y)
                                            :thm
                                            'return-of-binary-+-integerp-rationalp)
                                          (make-thm-spec
                                            :formals '(x y)
                                            :thm 'return-of-binary-+-rationalp))
                           :translation-hint
                           (make-trans-hint :translation "_SMT_.plus"))
        (make-smt-function :name 'binary-*
                           :kind :basic
                           :returns (list (make-thm-spec
                                            :formals '(x y)
                                            :thm 'return-of-binary-*-integerp)
                                          (make-thm-spec
                                            :formals '(x y)
                                            :thm 'return-of-binary-*-rationalp-integerp)
                                          (make-thm-spec
                                            :formals '(x y)
                                            :thm
                                            'return-of-binary-*-integerp-rationalp)
                                          (make-thm-spec
                                            :formals '(x y)
                                            :thm
                                            'return-of-binary-*-rationalp))
                           :translation-hint
                           (make-trans-hint :translation "_SMT_.times"))
        (make-smt-function :name 'rational-+
                           :kind :basic
                           :returns (list (make-thm-spec
                                            :formals '(x y)
                                            :thm 'return-of-rational-+)))
        (make-smt-function :name 'rational--
                           :kind :basic
                           :returns (list (make-thm-spec
                                            :formals '(x)
                                            :thm 'return-of-rational--)))
        (make-smt-function :name 'rational-*
                           :kind :basic
                           :returns (list (make-thm-spec
                                            :formals '(x y)
                                            :thm 'return-of-rational-*)))
        (make-smt-function :name 'rational-/
                           :kind :basic
                           :returns (list (make-thm-spec
                                            :formals '(x)
                                            :thm 'return-of-rational-/)))
        (make-smt-function :name 'rational-<
                           :kind :basic
                           :returns (list (make-thm-spec
                                            :formals '(x y)
                                            :thm 'return-of-rational-<)))
        (make-smt-function :name 'integer-+
                           :kind :basic
                           :returns (list (make-thm-spec
                                            :formals '(x y)
                                            :thm 'return-of-integer-+)))
        (make-smt-function :name 'integer--
                           :kind :basic
                           :returns (list (make-thm-spec
                                            :formals '(x)
                                            :thm 'return-of-integer--)))
        (make-smt-function :name 'integer-*
                           :kind :basic
                           :returns (list (make-thm-spec
                                            :formals '(x y)
                                            :thm 'return-of-integer-*)))
        (make-smt-function :name 'integer-<
                           :kind :basic
                           :returns (list (make-thm-spec
                                            :formals '(x y)
                                            :thm 'return-of-integer-<)))
        (make-smt-function :name 'if
                           :kind :basic
                           :translation-hint
                           (make-trans-hint :translation "_SMT_.ifx"))
        (make-smt-function :name 'implies
                           :kind :basic
                           :translation-hint
                           (make-trans-hint :translation "_SMT_.implies"))))

(define make-basic-replaces ()
  :returns (replace-lst thm-spec-list-p)
  (list (make-thm-spec :thm 'replace-of-symbol-fix)
        (make-thm-spec :thm 'replace-of-bool-fix)
        (make-thm-spec :thm 'replace-of-ifix)
        (make-thm-spec :thm 'replace-of-rfix)))

(define make-basic-hints ()
  :returns (hint smtlink-hint-p)
  (make-smtlink-hint
   :acl2types (make-acl2types)
   :datatypes (make-datatypes)
   :functions (make-basic-functions)
   :replaces (make-basic-replaces)
   :configurations (make-smt-config :smt-cnf (default-smt-cnf))))
