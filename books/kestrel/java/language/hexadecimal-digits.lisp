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

(defxdoc+ hexadecimal-digits
  :parents (syntax)
  :short "Java hexadecimal digits [JLS:3.10.1]."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection hex-digit
  :short "Fixtype of Java hexadecimal digits [JLS:3.10.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A Java hexadecimal digit is a Java ASCII character that is
     either a decimal digit (i.e. between `0' and `9')
     or an (uppercase or lowercase) letter
     between `A' and `F' or between `a' and `f'.
     See the grammar rule @('hex-digit') (also in [JLS:3.3]).")
   (xdoc::p
    "This is a type introduced by @(tsee fty::deffixtype)."))

  (define hex-digitp (x)
    :returns (yes/no booleanp)
    :parents (hex-digit)
    :short "Recognizer for @(tsee hex-digit)."
    (and (integerp x)
         (or (and (<= (char-code #\0) x)
                  (<= x (char-code #\9)))
             (and (<= (char-code #\A) x)
                  (<= x (char-code #\F)))
             (and (<= (char-code #\a) x)
                  (<= x (char-code #\f))))))

  (std::deffixer hex-digit-fix
    :pred hex-digitp
    :body-fix (char-code #\0)
    :parents (hex-digit)
    :short "Fixer for @(tsee hex-digit).")

  (fty::deffixtype hex-digit
    :pred hex-digitp
    :fix hex-digit-fix
    :equiv hex-digit-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hex-digit-value ((x hex-digitp))
  :returns (val natp
                :rule-classes (:rewrite :type-prescription)
                :hints (("Goal" :in-theory (enable hex-digitp hex-digit-fix))))
  :short "Numeric value of a Java hexadecimal digit."
  (b* ((x (mbe :logic (hex-digit-fix x) :exec x)))
    (cond ((and (<= (char-code #\0) x)
                (<= x (char-code #\9))) (- x (char-code #\0)))
          ((and (<= (char-code #\A) x)
                (<= x (char-code #\F))) (+ 10 (- x (char-code #\A))))
          ((and (<= (char-code #\a) x)
                (<= x (char-code #\f))) (+ 10 (- x (char-code #\a))))
          (t (impossible))))
  :guard-hints (("Goal" :in-theory (enable hex-digitp)))
  :hooks (:fix)
  ///

  (defret hex-digit-value-upper-bound
    (<= val 15)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist hex-digit-list
  :short "Fixtype of true lists of Java hexadecimal digits."
  :elt-type hex-digit
  :true-listp t
  :elementp-of-nil nil
  :pred hex-digit-listp)
