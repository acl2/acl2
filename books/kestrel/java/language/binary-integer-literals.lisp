; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "optional-integer-type-suffix")
(include-book "binary-digits")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ binary-integer-literals
  :parents (integer-literals)
  :short "Java binary integer literals [JLS:3.10.1]."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum bindig/uscore
  :short "Fixtype of binary digits and underscores."
  :long
  (xdoc::topstring-p
   "A @('binary-numeral') in the grammar, excluding the prefix,
    consists of binary digits and underscores.")
  (:digit ((get bin-digit)))
  (:underscore ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist bindig/uscore-list
  :short "Fixtype of true lists of binary digits and underscores."
  :long
  (xdoc::topstring-p
   "A @('binary-numeral') in the grammar, excluding the prefix,
    is a sequence of binary digits and underscores,
    subject to certain restrictions
    formalized in @(tsee bindig/uscore-list-wfp).")
  :elt-type bindig/uscore
  :true-listp t
  :elementp-of-nil nil
  :pred bindig/uscore-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bindig/uscores-to-digits ((dus bindig/uscore-listp))
  :returns (ds bin-digit-listp)
  :short "Remove the underscores from
          a list of binary digits and underscores."
  :long
  (xdoc::topstring-p
   "Any underscores in a @('binary-numeral') in the grammar
    are just used for separation.
    This function returns the underlying sequence of binary digits,
    exluding also the prefix of the @('binary-numeral').")
  (b* (((when (endp dus)) nil)
       (du (car dus)))
    (bindig/uscore-case
     du
     :digit (cons du.get (bindig/uscores-to-digits (cdr dus)))
     :underscore (bindig/uscores-to-digits (cdr dus))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bindig/uscore-list-wfp ((dus bindig/uscore-listp))
  :returns (yes/no booleanp)
  :short "Check if a binary numeral (without prefix) is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @('binary-numeral') in the grammar, without the prefix,
     is a list of binary digits and underscores
     subject to the following constraints,
     derived from the grammar:")
   (xdoc::ul
    (xdoc::li
     "It must start with a digit, not an underscore.")
    (xdoc::li
     "It must end with a digit, not an underscore.
      (Note that first and last digit may be the same,
      if the binary numeral is just @('0b0') or @('0B0').)")))
  (and (consp dus)
       (bindig/uscore-case (car dus) :digit)
       (bindig/uscore-case (car (last dus)) :digit))
  :hooks (:fix)
  :prepwork
  ((defrulel hooks-fix-lemma
     (equal (last (bindig/uscore-list-fix x))
            (bindig/uscore-list-fix (last x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod bin-integer-literal
  :short "Fixtype of binary integer literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "A binary integer literal consist of
     (i) a lowercase or uppercase prefix,
     (ii) a sequence of binary digits and underscores
     satisfying the constraints in @(tsee bindig/uscore-list-wfp), and
     (iii) an optional integer type suffix,")
   (xdoc::p
    "The set of values of this fixtype should be isomorphic to
     the set of strings (or parse trees) defined by
     the Java grammar rule @('binary-integer-literal').
     This remains to be proved formally."))
  ((digits/uscores bindig/uscore-list
                   :reqfix (if (bindig/uscore-list-wfp digits/uscores)
                               digits/uscores
                             (list (bindig/uscore-digit (char-code #\0)))))
   (prefix-upcase-p bool)
   (suffix? optional-integer-type-suffix))
  :tag :bin-integer-lit
  :layout :list
  :require (bindig/uscore-list-wfp digits/uscores))
