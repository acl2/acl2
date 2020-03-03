; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
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

(defsection bin-digit
  :short "Fixtype of Java binary digits [JLS:3.10.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A Java binary digit is one of the Java ASCII characters `0' and `1'.
     See the grammar rule @('binary-digit').")
   (xdoc::p
    "This is a type introduced by @(tsee fty::deffixtype)."))

  (define bin-digitp (x)
    :returns (yes/no booleanp)
    :parents (bin-digit)
    :short "Recognizer for @(tsee bin-digit)."
    (or (eql x (char-code #\0))
        (eql x (char-code #\1))))

  (std::deffixer bin-digit-fix
    :pred bin-digitp
    :body-fix (char-code #\0)
    :parents (bin-digit)
    :short "Fixer for @(tsee bin-digit).")

  (fty::deffixtype bin-digit
    :pred bin-digitp
    :fix bin-digit-fix
    :equiv bin-digit-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bin-digit-value ((x bin-digitp))
  :returns (val bitp :rule-classes (:rewrite :type-prescription))
  :short "Numeric value of a Java binary digit."
  (if (eql (bin-digit-fix x)
           (char-code #\0))
      0
    1)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist bin-digit-list
  :short "Fixtype of true lists of Java binary digits."
  :elt-type bin-digit
  :true-listp t
  :elementp-of-nil nil
  :pred bin-digit-listp)
