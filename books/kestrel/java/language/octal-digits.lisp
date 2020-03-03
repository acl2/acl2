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

(defxdoc+ octal-digits
  :parents (syntax)
  :short "Java octal digits [JLS:3.10.1]."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection oct-digit
  :short "Fixtype of Java octal digits [JLS:3.10.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A Java octal digit is a Java ASCII character between `0' and `7'.
     See the grammar rule @('octal-digit').")
   (xdoc::p
    "This is a type introduced by @(tsee fty::deffixtype)."))

  (define oct-digitp (x)
    :returns (yes/no booleanp)
    :parents (oct-digit)
    :short "Recognizer for @(tsee oct-digit)."
    (and (integerp x)
         (<= (char-code #\0) x)
         (<= x (char-code #\7))))

  (std::deffixer oct-digit-fix
    :pred oct-digitp
    :body-fix (char-code #\0)
    :parents (oct-digit)
    :short "Fixer for @(tsee oct-digit).")

  (fty::deffixtype oct-digit
    :pred oct-digitp
    :fix oct-digit-fix
    :equiv oct-digit-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define oct-digit-value ((x oct-digitp))
  :returns (val natp
                :rule-classes (:rewrite :type-prescription)
                :hints (("Goal" :in-theory (enable oct-digitp
                                                   oct-digit-fix))))
  :short "Numeric value of a Java octal digit."
  (b* ((x (mbe :logic (oct-digit-fix x) :exec x)))
    (- x (char-code #\0)))
  :guard-hints (("Goal" :in-theory (enable oct-digitp)))
  :hooks (:fix)
  ///

  (defret oct-digit-value-upper-bound
    (<= val 7)
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable oct-digit-fix oct-digitp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist oct-digit-list
  :short "Fixtype of true lists of Java octal digits."
  :elt-type oct-digit
  :true-listp t
  :elementp-of-nil nil
  :pred oct-digit-listp)
