; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "library-extensions")

(include-book "java-abstract-syntax")

(include-book "kestrel/std/system/primitivep" :dir :system)
(include-book "std/typed-alists/symbol-string-alistp" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ aij-notions
  :parents (atj-implementation)
  :short "AIJ notions used by ATJ."
  :long
  (xdoc::topstring
   (xdoc::p
    "ATJ is supported by " (xdoc::seetopic "aij" "AIJ") ".")
   (xdoc::p
    "Thus, ATJ uses some notions that are specific to AIJ."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *aij-package*
  :short "Name of the Java package of AIJ."
  "edu.kestrel.acl2.aij"
  ///
  (assert-event (atj-string-ascii-java-package-name-p *aij-package*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection aij-class-names
  :short "ACL2 named constants for the AIJ class names."
  (defconst *aij-class-char*           "Acl2Character")
  (defconst *aij-class-complex*        "Acl2ComplexRational")
  (defconst *aij-class-cons*           "Acl2ConsPair")
  (defconst *aij-class-def-fn*         "Acl2DefinedFunction")
  (defconst *aij-class-undef-pkg-exc*  "Acl2UndefinedPackageException")
  (defconst *aij-class-fn*             "Acl2Function")
  (defconst *aij-class-fn-app*         "Acl2FunctionCall")
  (defconst *aij-class-int*            "Acl2Integer")
  (defconst *aij-class-lambda*         "Acl2LambdaExpression")
  (defconst *aij-class-named-fn*       "Acl2NamedFunction")
  (defconst *aij-class-native-fn*      "Acl2NativeFunction")
  (defconst *aij-class-number*         "Acl2Number")
  (defconst *aij-class-pkg*            "Acl2Package")
  (defconst *aij-class-pkg-name*       "Acl2PackageName")
  (defconst *aij-class-qconst*         "Acl2QuotedConstant")
  (defconst *aij-class-ratio*          "Acl2Ratio")
  (defconst *aij-class-rational*       "Acl2Rational")
  (defconst *aij-class-string*         "Acl2String")
  (defconst *aij-class-symbol*         "Acl2Symbol")
  (defconst *aij-class-term*           "Acl2Term")
  (defconst *aij-class-value*          "Acl2Value")
  (defconst *aij-class-var*            "Acl2Variable"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *aij-class-names*
  :short "Names of the Java classes that form AIJ."
  (list *aij-class-char*
        *aij-class-complex*
        *aij-class-cons*
        *aij-class-def-fn*
        *aij-class-undef-pkg-exc*
        *aij-class-fn*
        *aij-class-fn-app*
        *aij-class-int*
        *aij-class-lambda*
        *aij-class-named-fn*
        *aij-class-native-fn*
        *aij-class-number*
        *aij-class-pkg*
        *aij-class-pkg-name*
        *aij-class-qconst*
        *aij-class-ratio*
        *aij-class-rational*
        *aij-class-string*
        *aij-class-symbol*
        *aij-class-term*
        *aij-class-value*
        *aij-class-var*)
  ///
  (assert-event (string-listp *aij-class-names*))
  (assert-event (no-duplicatesp-equal *aij-class-names*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection aij-class-types
  :short "ACL2 named constants for the AIJ class types."
  (defconst *aij-type-char*           (jtype-class *aij-class-char*))
  (defconst *aij-type-complex*        (jtype-class *aij-class-complex*))
  (defconst *aij-type-cons*           (jtype-class *aij-class-cons*))
  (defconst *aij-type-def-fn*         (jtype-class *aij-class-def-fn*))
  (defconst *aij-type-undef-pkg-exc*  (jtype-class *aij-class-undef-pkg-exc*))
  (defconst *aij-type-fn*             (jtype-class *aij-class-fn*))
  (defconst *aij-type-fn-app*         (jtype-class *aij-class-fn-app*))
  (defconst *aij-type-int*            (jtype-class *aij-class-int*))
  (defconst *aij-type-lambda*         (jtype-class *aij-class-lambda*))
  (defconst *aij-type-named-fn*       (jtype-class *aij-class-named-fn*))
  (defconst *aij-type-native-fn*      (jtype-class *aij-class-native-fn*))
  (defconst *aij-type-number*         (jtype-class *aij-class-number*))
  (defconst *aij-type-pkg*            (jtype-class *aij-class-pkg*))
  (defconst *aij-type-pkg-name*       (jtype-class *aij-class-pkg-name*))
  (defconst *aij-type-qconst*         (jtype-class *aij-class-qconst*))
  (defconst *aij-type-ratio*          (jtype-class *aij-class-ratio*))
  (defconst *aij-type-rational*       (jtype-class *aij-class-rational*))
  (defconst *aij-type-string*         (jtype-class *aij-class-string*))
  (defconst *aij-type-symbol*         (jtype-class *aij-class-symbol*))
  (defconst *aij-type-term*           (jtype-class *aij-class-term*))
  (defconst *aij-type-value*          (jtype-class *aij-class-value*))
  (defconst *aij-type-var*            (jtype-class *aij-class-var*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *aij-natives*
  :short "List of built-in ACL2 functions natively implemented in AIJ."
  :long
  (xdoc::topstring-p
   "Currently these are the ACL2 primitive functions
    plus @(tsee nonnegative-integer-quotient) and @(tsee string-append).")
  (append (strip-cars *primitive-formals-and-guards*)
          (list 'nonnegative-integer-quotient
                'string-append
                'len)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define aij-nativep ((fn symbolp))
  :returns (yes/no booleanp)
  :short "Recognize the ACL2 built-in functions natively implemented in AIJ."
  (and (member-eq fn *aij-natives*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *aij-symbol-constants*
  :short "AIJ's constants (i.e. static final fields)
          for certain ACL2 symbols."
  :long
  (xdoc::topstring-p
   "This is an alist from the ACL2 symbols
    to the names of the corresponding fields.")
  '((t . "T")
    (nil . "NIL")
    (list . "LIST")
    (if . "IF")
    (characterp . "CHARACTERP")
    (stringp . "STRINGP")
    (symbolp . "SYMBOLP")
    (integerp . "INTEGERP")
    (rationalp . "RATIONALP")
    (complex-rationalp . "COMPLEX_RATIONALP")
    (acl2-numberp . "ACL2_NUMBERP")
    (consp . "CONSP")
    (char-code . "CHAR_CODE")
    (code-char . "CODE_CHAR")
    (coerce . "COERCE")
    (intern-in-package-of-symbol . "INTERN_IN_PACKAGE_OF_SYMBOL")
    (symbol-package-name . "SYMBOL_PACKAGE_NAME")
    (symbol-name . "SYMBOL_NAME")
    (pkg-imports . "PKG_IMPORTS")
    (pkg-witness . "PKG_WITNESS")
    (unary-- . "UNARY_MINUS")
    (unary-/ . "UNARY_SLASH")
    (binary-+ . "BINARY_PLUS")
    (binary-* . "BINARY_STAR")
    (< . "LESS_THAN")
    (complex . "COMPLEX")
    (realpart . "REALPART")
    (imagpart . "IMAGPART")
    (numerator . "NUMERATOR")
    (denominator . "DENOMINATOR")
    (cons . "CONS")
    (car . "CAR")
    (cdr . "CDR")
    (equal . "EQUAL")
    (bad-atom<= . "BAD_ATOM_LESS_THAN_OR_EQUAL_TO")
    (or . "OR")
    (nonnegative-integer-quotient . "NONNEGATIVE_INTEGER_QUOTIENT")
    (string-append . "STRING_APPEND")
    (len . "LEN"))
  ///
  (assert-event (symbol-string-alistp *aij-symbol-constants*))
  (assert-event (no-duplicatesp-equal (strip-cdrs *aij-symbol-constants*))))
