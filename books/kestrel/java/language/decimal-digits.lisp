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

(defxdoc+ decimal-digits
  :parents (syntax)
  :short "Java decimal digits [JLS:3.10.1]."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dec-digit
  :short "Fixtype of Java decimal digits [JLS:3.10.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A Java decimal digit is a Java ASCII character between `0' and `9'.
     See the grammar rule @('digit').")
   (xdoc::p
    "This is a type introduced by @(tsee fty::deffixtype)."))

  (define dec-digitp (x)
    :returns (yes/no booleanp)
    :parents (dec-digit)
    :short "Recognizer for @(tsee dec-digit)."
    (and (integerp x)
         (<= (char-code #\0) x)
         (<= x (char-code #\9))))

  (std::deffixer dec-digit-fix
    :pred dec-digitp
    :body-fix (char-code #\0)
    :parents (dec-digit)
    :short "Fixer for @(tsee dec-digit).")

  (fty::deffixtype dec-digit
    :pred dec-digitp
    :fix dec-digit-fix
    :equiv dec-digit-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dec-digit-value ((x dec-digitp))
  :returns (val natp
                :rule-classes (:rewrite :type-prescription)
                :hints (("Goal" :in-theory (enable dec-digitp dec-digit-fix))))
  :short "Numeric value of a Java decimal digit."
  (b* ((x (mbe :logic (dec-digit-fix x) :exec x)))
    (- x (char-code #\0)))
  :guard-hints (("Goal" :in-theory (enable dec-digitp)))
  :hooks (:fix)
  ///

  (defret dec-digit-value-upper-bound
    (<= val 9)
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable dec-digit-fix dec-digitp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist dec-digit-list
  :short "Fixtype of true lists of Java decimal digits."
  :elt-type dec-digit
  :true-listp t
  :elementp-of-nil nil
  :pred dec-digit-listp)
