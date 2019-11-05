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

(include-book "kestrel/std/util/deffixer" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ binary-digits
  :parents (syntax)
  :short "Java binary digits [JLS:3.10.1]."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection binary-digit
  :short "Fixtype of Java binary digits [JLS:3.10.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A Java binary digit is one of the Java ASCII characters `0' and `1'.
     See the grammar rule @('binary-digit'),
     after which this type and these functions are named.")
   (xdoc::p
    "This is a type introduced by @(tsee fty::deffixtype)."))

  (define binary-digitp (x)
    :returns (yes/no booleanp)
    :parents (binary-digit)
    :short "Recognizer for @(tsee binary-digit)."
    (or (eql x (char-code #\0))
        (eql x (char-code #\1))))

  (std::deffixer binary-digit-fix
    :pred binary-digitp
    :body-fix (char-code #\0)
    :parents (binary-digit)
    :short "Fixer for @(tsee binary-digit).")

  (fty::deffixtype binary-digit
    :pred binary-digitp
    :fix binary-digit-fix
    :equiv binary-digit-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binary-digit-value ((x binary-digitp))
  :returns (val bitp :rule-classes (:rewrite :type-prescription))
  :short "Numeric value of a Java binary digit."
  (if (eql x (char-code #\0))
      0
    1))
