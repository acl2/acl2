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
(include-book "constants")

(include-book "kestrel/utilities/system/world-queries" :dir :system)
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

(define atj-aij-nativep ((fn symbolp))
  :returns (yes/no booleanp)
  :short "ACL2 built-in functions natively implemented in AIJ."
  :long
  (xdoc::topstring-p
   "Currently these are exactly the ACL2 primitive functions.")
  (primitivep fn))
