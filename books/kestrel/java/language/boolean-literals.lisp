; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "unicode")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ boolean-literals
  :parents (syntax)
  :short "Java boolean literals [JLS:3.10.3]."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *boolean-literals*
  :short "The Java boolean literals, as ACL2 strings."
  (list "true" "false")
  ///

  (assert-event (string-listp *boolean-literals*))

  (assert-event (no-duplicatesp-equal *boolean-literals*))

  (defruled ascii-listp-of-boolean-literals
    (implies (member-equal literal *boolean-literals*)
             (ascii-listp (string=>unicode literal)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-literal-p (x)
  :returns (yes/no booleanp)
  :short "Recognize the Java boolean literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "A Java boolean literal is a list of Java Unicode characters
     that consists of the (ASCII) codes of
     an element of @(tsee *boolean-literals*)."))
  (and (ascii-listp x)
       (member-equal (ascii=>string x)
                     *boolean-literals*)
       t)) ; turn result of MEMBER-EQUAL into boolean
