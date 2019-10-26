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

(defxdoc+ null-literal
  :parents (syntax)
  :short "Java null literal [JLS:3.10.7]."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *null-literal*
  :short "The Java null literal, as an ACL2 string."
  "null"
  ///

  (assert-event (stringp *null-literal*))

  (defruled ascii-listp-of-null-literal
    (ascii-listp (string=>unicode *null-literal*))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define null-literal-p (x)
  :returns (yes/no booleanp)
  :short "Recognize the Java null literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "The Java null literal is a list of Java Unicode characters
     that consists of the (ASCII) codes of @(tsee *null-literal*)."))
  (and (ascii-listp x)
       (equal (ascii=>string x)
              *null-literal*)))
