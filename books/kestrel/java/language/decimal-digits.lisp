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

(defxdoc+ decimal-digits
  :parents (syntax)
  :short "Java decimal digits [JLS:3.10.1]."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection digit
  :short "Fixtype of Java decimal digits [JLS:3.10.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A Java decimal digit is a Java ASCII character between `0' and `9'.
     See the grammar rule @('digit'),
     after which this type and these functions are named.")
   (xdoc::p
    "This is a type introduced by @(tsee fty::deffixtype)."))

  (define digitp (x)
    :returns (yes/no booleanp)
    :parents (digit)
    :short "Recognizer for @(tsee digit)."
    (and (integerp x)
         (<= (char-code #\0) x)
         (<= x (char-code #\9))))

  (std::deffixer digit-fix
    :pred digitp
    :body-fix (char-code #\0)
    :parents (digit)
    :short "Fixer for @(tsee digit).")

  (fty::deffixtype digit
    :pred digitp
    :fix digit-fix
    :equiv digit-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit-value ((x digitp))
  :returns (val natp
                :rule-classes (:rewrite :type-prescription)
                :hints (("Goal" :in-theory (enable digitp digit-fix))))
  :short "Numeric value of a Java decimal digit."
  (b* ((x (mbe :logic (digit-fix x) :exec x)))
    (- x (char-code #\0)))
  :guard-hints (("Goal" :in-theory (enable digitp)))
  ///

  (defret digit-value-upper-bound
    (<= val 9)
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable digit-fix digitp)))))
