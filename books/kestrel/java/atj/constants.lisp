; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "abstract-syntax")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-constants
  :parents (atj-implementation)
  :short "Some ACL2 names constants used by ATJ."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atj-aij-class-consts
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

(defsection atj-aij-type-consts
  :short "ACL2 named constants for the AIJ (class) types."
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
