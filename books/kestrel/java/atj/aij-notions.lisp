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
(include-book "kestrel/utilities/xdoc/defxdoc-plus" :dir :system)
(include-book "std/util/defval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-aij-notions
  :parents (atj-implementation)
  :short "AIJ notions used by ATJ."
  :long
  (xdoc::topstring
   (xdoc::p
    "ATJ is supported by " (xdoc::seeurl "aij" "AIJ") ".")
   (xdoc::p
    "Thus, ATJ uses some notions that are specific to AIJ."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-aij-jpackage*
  :short "Name of the Java package of AIJ."
  "edu.kestrel.acl2.aij"
  ///
  (assert-event (atj-string-ascii-java-package-name-p *atj-aij-jpackage*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atj-aij-class-names
  :short "ACL2 named constants for the AIJ class names."
  (defconst *atj-jclass-char*      "Acl2Character")
  (defconst *atj-jclass-complex*   "Acl2ComplexRational")
  (defconst *atj-jclass-cons*      "Acl2ConsPair")
  (defconst *atj-jclass-def-fn*    "Acl2DefinedFunction")
  (defconst *atj-jclass-eval-exc*  "Acl2EvaluationException")
  (defconst *atj-jclass-fn*        "Acl2Function")
  (defconst *atj-jclass-fn-app*    "Acl2FunctionApplication")
  (defconst *atj-jclass-int*       "Acl2Integer")
  (defconst *atj-jclass-lambda*    "Acl2LambdaExpression")
  (defconst *atj-jclass-named-fn*  "Acl2NamedFunction")
  (defconst *atj-jclass-native-fn* "Acl2NativeFunction")
  (defconst *atj-jclass-number*    "Acl2Number")
  (defconst *atj-jclass-pkg*       "Acl2Package")
  (defconst *atj-jclass-pkg-name*  "Acl2PackageName")
  (defconst *atj-jclass-qconst*    "Acl2QuotedConstant")
  (defconst *atj-jclass-ratio*     "Acl2Ratio")
  (defconst *atj-jclass-rational*  "Acl2Rational")
  (defconst *atj-jclass-string*    "Acl2String")
  (defconst *atj-jclass-symbol*    "Acl2Symbol")
  (defconst *atj-jclass-term*      "Acl2Term")
  (defconst *atj-jclass-value*     "Acl2Value")
  (defconst *atj-jclass-var*       "Acl2Variable"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-aij-class-names*
  :short "Names of the Java classes that form AIJ."
  (list *atj-jclass-char*
        *atj-jclass-complex*
        *atj-jclass-cons*
        *atj-jclass-def-fn*
        *atj-jclass-eval-exc*
        *atj-jclass-fn*
        *atj-jclass-fn-app*
        *atj-jclass-int*
        *atj-jclass-lambda*
        *atj-jclass-named-fn*
        *atj-jclass-native-fn*
        *atj-jclass-number*
        *atj-jclass-pkg*
        *atj-jclass-pkg-name*
        *atj-jclass-qconst*
        *atj-jclass-ratio*
        *atj-jclass-rational*
        *atj-jclass-string*
        *atj-jclass-symbol*
        *atj-jclass-term*
        *atj-jclass-value*
        *atj-jclass-var*)
  ///
  (assert-event (string-listp *atj-aij-class-names*))
  (assert-event (no-duplicatesp-equal *atj-aij-class-names*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atj-aij-class-types
  :short "ACL2 named constants for the AIJ class types."
  (defconst *atj-jtype-char*      (jtype-class *atj-jclass-char*))
  (defconst *atj-jtype-complex*   (jtype-class *atj-jclass-complex*))
  (defconst *atj-jtype-cons*      (jtype-class *atj-jclass-cons*))
  (defconst *atj-jtype-def-fn*    (jtype-class *atj-jclass-def-fn*))
  (defconst *atj-jtype-eval-exc*  (jtype-class *atj-jclass-eval-exc*))
  (defconst *atj-jtype-fn*        (jtype-class *atj-jclass-fn*))
  (defconst *atj-jtype-fn-app*    (jtype-class *atj-jclass-fn-app*))
  (defconst *atj-jtype-int*       (jtype-class *atj-jclass-int*))
  (defconst *atj-jtype-lambda*    (jtype-class *atj-jclass-lambda*))
  (defconst *atj-jtype-named-fn*  (jtype-class *atj-jclass-named-fn*))
  (defconst *atj-jtype-native-fn* (jtype-class *atj-jclass-native-fn*))
  (defconst *atj-jtype-number*    (jtype-class *atj-jclass-number*))
  (defconst *atj-jtype-pkg*       (jtype-class *atj-jclass-pkg*))
  (defconst *atj-jtype-pkg-name*  (jtype-class *atj-jclass-pkg-name*))
  (defconst *atj-jtype-qconst*    (jtype-class *atj-jclass-qconst*))
  (defconst *atj-jtype-ratio*     (jtype-class *atj-jclass-ratio*))
  (defconst *atj-jtype-rational*  (jtype-class *atj-jclass-rational*))
  (defconst *atj-jtype-string*    (jtype-class *atj-jclass-string*))
  (defconst *atj-jtype-symbol*    (jtype-class *atj-jclass-symbol*))
  (defconst *atj-jtype-term*      (jtype-class *atj-jclass-term*))
  (defconst *atj-jtype-value*     (jtype-class *atj-jclass-value*))
  (defconst *atj-jtype-var*       (jtype-class *atj-jclass-var*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-aij-nativep ((fn symbolp))
  :returns (yes/no booleanp)
  :short "ACL2 built-in functions natively implemented in AIJ."
  :long
  (xdoc::topstring-p
   "Currently these are exactly the ACL2 primitive functions.")
  (primitivep fn))
