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

(defxdoc+ octal-digits
  :parents (syntax)
  :short "Java octal digits [JLS:3.10.1]."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection octal-digit
  :short "Fixtype of Java octal digits [JLS:3.10.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A Java octal digit is a Java ASCII character between `0' and `7'.
     See the grammar rule @('octal-digit'),
     after which this type and these functions are named.")
   (xdoc::p
    "This is a type introduced by @(tsee fty::deffixtype)."))

  (define octal-digitp (x)
    :returns (yes/no booleanp)
    :parents (octal-digit)
    :short "Recognizer for @(tsee octal-digit)."
    (and (integerp x)
         (<= (char-code #\0) x)
         (<= x (char-code #\7))))

  (std::deffixer octal-digit-fix
    :pred octal-digitp
    :body-fix (char-code #\0)
    :parents (octal-digit)
    :short "Fixer for @(tsee octal-digit).")

  (fty::deffixtype octal-digit
    :pred octal-digitp
    :fix octal-digit-fix
    :equiv octal-digit-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define octal-digit-value ((x octal-digitp))
  :returns (val natp
                :rule-classes (:rewrite :type-prescription)
                :hints (("Goal" :in-theory (enable octal-digitp
                                                   octal-digit-fix))))
  :short "Numeric value of a Java octal digit."
  (b* ((x (mbe :logic (octal-digit-fix x) :exec x)))
    (- x (char-code #\0)))
  :guard-hints (("Goal" :in-theory (enable octal-digitp)))
  ///

  (defret octal-digit-value-upper-bound
    (<= val 7)
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable octal-digit-fix octal-digitp)))))
