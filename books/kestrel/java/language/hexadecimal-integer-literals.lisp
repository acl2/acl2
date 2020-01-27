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
(include-book "hexadecimal-digits")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ hexadecimal-integer-literals
  :parents (integer-literals)
  :short "Java hexadecimal integer literals [JLS:3.10.1]."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum hexdig/uscore
  :short "Fixtype of hexadecimal digits and underscores."
  :long
  (xdoc::topstring-p
   "A @('hex-numeral') in the grammar, excluding the prefix,
    consists of hexadecimal digits and underscores.")
  (:digit ((get hex-digit)))
  (:underscore ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist hexdig/uscore-list
  :short "Fixtype of true lists of hexadecimal digits and underscores."
  :long
  (xdoc::topstring-p
   "A @('hex-numeral') in the grammar, excluding the prefix,
    is a sequence of hexadecimal digits and underscores,
    subject to certain restrictions
    formalized in @(tsee hexdig/uscore-list-wfp).")
  :elt-type hexdig/uscore
  :true-listp t
  :elementp-of-nil nil
  :pred hexdig/uscore-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hexdig/uscores-to-digits ((dus hexdig/uscore-listp))
  :returns (ds hex-digit-listp)
  :short "Remove the underscores from
          a list of hexadecimal digits and underscores."
  :long
  (xdoc::topstring-p
   "Any underscores in a @('hex-numeral') in the grammar
    are just used for separation.
    This function returns the underlying sequence of hexadecimal digits,
    exluding also the prefix of the @('hex-numeral').")
  (b* (((when (endp dus)) nil)
       (du (car dus)))
    (hexdig/uscore-case
     du
     :digit (cons du.get (hexdig/uscores-to-digits (cdr dus)))
     :underscore (hexdig/uscores-to-digits (cdr dus))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hexdig/uscore-list-wfp ((dus hexdig/uscore-listp))
  :returns (yes/no booleanp)
  :short "Check if a hexadecimal numeral (without prefix) is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @('hex-numeral') in the grammar, without the prefix,
     is a list of hexadecimal digits and underscores
     subject to the following constraints,
     derived from the grammar:")
   (xdoc::ul
    (xdoc::li
     "It must start with a digit, not an underscore.")
    (xdoc::li
     "It must end with a digit, not an underscore.
      (Note that first and last digit may be the same,
      if the hexadecimal numeral is just @('0x0') or @('0X0').)")))
  (and (consp dus)
       (hexdig/uscore-case (car dus) :digit)
       (hexdig/uscore-case (car (last dus)) :digit))
  :hooks (:fix)
  :prepwork
  ((defrulel hooks-fix-lemma
     (equal (last (hexdig/uscore-list-fix x))
            (hexdig/uscore-list-fix (last x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod hex-integer-literal
  :short "Fixtype of hexadecimal integer literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "A hexadecimal integer literal consist of
     (i) a lowercase or uppercase prefix,
     (ii) a sequence of hexadecimal digits and underscores
     satisfying the constraints in @(tsee hexdig/uscore-list-wfp), and
     (iii) an optional integer type suffix,")
   (xdoc::p
    "The set of values of this fixtype should be isomorphic to
     the set of strings (or parse trees) defined by
     the Java grammar rule @('hex-integer-literal').
     This remains to be proved formally."))
  ((digits/uscores hexdig/uscore-list
                   :reqfix (if (hexdig/uscore-list-wfp digits/uscores)
                               digits/uscores
                             (list (hexdig/uscore-digit (char-code #\0)))))
   (prefix-upcase-p bool)
   (suffix optional-integer-type-suffix))
  :tag :hex-integer-lit
  :layout :list
  :require (hexdig/uscore-list-wfp digits/uscores))
