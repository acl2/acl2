; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "library-extensions")

(include-book "abstract-syntax")

(include-book "kestrel/std/system/primitivep" :dir :system)
(include-book "kestrel/std/typed-alists/symbol-string-alistp" :dir :system)
(include-book "kestrel/utilities/xdoc/defxdoc-plus" :dir :system)
(include-book "std/util/defval" :dir :system)

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

(defval *aij-jpackage*
  :short "Name of the Java package of AIJ."
  "edu.kestrel.acl2.aij"
  ///
  (assert-event (atj-string-ascii-java-package-name-p *aij-jpackage*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection aij-class-names
  :short "ACL2 named constants for the AIJ class names."
  (defconst *aij-jclass-char*      "Acl2Character")
  (defconst *aij-jclass-complex*   "Acl2ComplexRational")
  (defconst *aij-jclass-cons*      "Acl2ConsPair")
  (defconst *aij-jclass-def-fn*    "Acl2DefinedFunction")
  (defconst *aij-jclass-eval-exc*  "Acl2EvaluationException")
  (defconst *aij-jclass-fn*        "Acl2Function")
  (defconst *aij-jclass-fn-app*    "Acl2FunctionApplication")
  (defconst *aij-jclass-int*       "Acl2Integer")
  (defconst *aij-jclass-lambda*    "Acl2LambdaExpression")
  (defconst *aij-jclass-named-fn*  "Acl2NamedFunction")
  (defconst *aij-jclass-native-fn* "Acl2NativeFunction")
  (defconst *aij-jclass-number*    "Acl2Number")
  (defconst *aij-jclass-pkg*       "Acl2Package")
  (defconst *aij-jclass-pkg-name*  "Acl2PackageName")
  (defconst *aij-jclass-qconst*    "Acl2QuotedConstant")
  (defconst *aij-jclass-ratio*     "Acl2Ratio")
  (defconst *aij-jclass-rational*  "Acl2Rational")
  (defconst *aij-jclass-string*    "Acl2String")
  (defconst *aij-jclass-symbol*    "Acl2Symbol")
  (defconst *aij-jclass-term*      "Acl2Term")
  (defconst *aij-jclass-value*     "Acl2Value")
  (defconst *aij-jclass-var*       "Acl2Variable"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *aij-class-names*
  :short "Names of the Java classes that form AIJ."
  (list *aij-jclass-char*
        *aij-jclass-complex*
        *aij-jclass-cons*
        *aij-jclass-def-fn*
        *aij-jclass-eval-exc*
        *aij-jclass-fn*
        *aij-jclass-fn-app*
        *aij-jclass-int*
        *aij-jclass-lambda*
        *aij-jclass-named-fn*
        *aij-jclass-native-fn*
        *aij-jclass-number*
        *aij-jclass-pkg*
        *aij-jclass-pkg-name*
        *aij-jclass-qconst*
        *aij-jclass-ratio*
        *aij-jclass-rational*
        *aij-jclass-string*
        *aij-jclass-symbol*
        *aij-jclass-term*
        *aij-jclass-value*
        *aij-jclass-var*)
  ///
  (assert-event (string-listp *aij-class-names*))
  (assert-event (no-duplicatesp-equal *aij-class-names*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection aij-class-types
  :short "ACL2 named constants for the AIJ class types."
  (defconst *aij-jtype-char*      (jtype-class *aij-jclass-char*))
  (defconst *aij-jtype-complex*   (jtype-class *aij-jclass-complex*))
  (defconst *aij-jtype-cons*      (jtype-class *aij-jclass-cons*))
  (defconst *aij-jtype-def-fn*    (jtype-class *aij-jclass-def-fn*))
  (defconst *aij-jtype-eval-exc*  (jtype-class *aij-jclass-eval-exc*))
  (defconst *aij-jtype-fn*        (jtype-class *aij-jclass-fn*))
  (defconst *aij-jtype-fn-app*    (jtype-class *aij-jclass-fn-app*))
  (defconst *aij-jtype-int*       (jtype-class *aij-jclass-int*))
  (defconst *aij-jtype-lambda*    (jtype-class *aij-jclass-lambda*))
  (defconst *aij-jtype-named-fn*  (jtype-class *aij-jclass-named-fn*))
  (defconst *aij-jtype-native-fn* (jtype-class *aij-jclass-native-fn*))
  (defconst *aij-jtype-number*    (jtype-class *aij-jclass-number*))
  (defconst *aij-jtype-pkg*       (jtype-class *aij-jclass-pkg*))
  (defconst *aij-jtype-pkg-name*  (jtype-class *aij-jclass-pkg-name*))
  (defconst *aij-jtype-qconst*    (jtype-class *aij-jclass-qconst*))
  (defconst *aij-jtype-ratio*     (jtype-class *aij-jclass-ratio*))
  (defconst *aij-jtype-rational*  (jtype-class *aij-jclass-rational*))
  (defconst *aij-jtype-string*    (jtype-class *aij-jclass-string*))
  (defconst *aij-jtype-symbol*    (jtype-class *aij-jclass-symbol*))
  (defconst *aij-jtype-term*      (jtype-class *aij-jclass-term*))
  (defconst *aij-jtype-value*     (jtype-class *aij-jclass-value*))
  (defconst *aij-jtype-var*       (jtype-class *aij-jclass-var*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define aij-nativep ((fn symbolp))
  :returns (yes/no booleanp)
  :short "ACL2 built-in functions natively implemented in AIJ."
  :long
  (xdoc::topstring-p
   "Currently these are exactly the ACL2 primitive functions.")
  (primitivep fn))

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
    (or . "OR"))
  ///
  (assert-event (symbol-string-alistp *aij-symbol-constants*))
  (assert-event (no-duplicatesp-equal (strip-cdrs *aij-symbol-constants*))))
