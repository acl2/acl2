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
(include-book "decimal-digits")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ decimal-integer-literals
  :parents (integer-literals)
  :short "Java decimal integer literals [JLS:3.10.1]."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum decdig/uscore
  :short "Fixtype of decimal digits and underscores."
  :long
  (xdoc::topstring-p
   "A @('decimal-numeral') in the grammar
    consists of decimal digits and underscores.")
  (:digit ((get dec-digit)))
  (:underscore ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist decdig/uscore-list
  :short "Fixtype of true lists of decimal digits and underscores."
  :long
  (xdoc::topstring-p
   "A @('decimal-numeral') in the grammar
    is a sequence of decimal digits and underscores,
    subject to certain restrictions
    formalized in @(tsee decdig/uscore-list-wfp).")
  :elt-type decdig/uscore
  :true-listp t
  :elementp-of-nil nil
  :pred decdig/uscore-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decdig/uscores-to-digits ((dus decdig/uscore-listp))
  :returns (ds dec-digit-listp)
  :short "Remove the underscores from a list of decimal digits and underscores."
  :long
  (xdoc::topstring-p
   "Any underscores in a @('decimal-numeral') in the grammar
    are just used for separation.
    This function returns the underlying sequence of decimal digits.")
  (b* (((when (endp dus)) nil)
       (du (car dus)))
    (decdig/uscore-case du
                        :digit (cons du.get
                                     (decdig/uscores-to-digits (cdr dus)))
                        :underscore (decdig/uscores-to-digits (cdr dus))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decdig/uscore-list-wfp ((dus decdig/uscore-listp))
  :returns (yes/no booleanp)
  :short "Check if a decimal numeral is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @('decimal-numeral') in the grammar
     is a list of decimal digits and underscores
     subject to the following constraints,
     derived from the grammar:")
   (xdoc::ul
    (xdoc::li
     "It must start with a digit, not an underscore.")
    (xdoc::li
     "It must end with a digit, not an underscore.
      (Note that first and last digit may be the same,
      if the decimal numeral is just @('0').)")
    (xdoc::li
     "If the starting digit is 0,
      then it must be the only digit
      (which implies that there cannot be any underscores.")))
  (and (consp dus)
       (decdig/uscore-case (car dus) :digit)
       (decdig/uscore-case (car (last dus)) :digit)
       (implies (equal (decdig/uscore-fix (car dus))
                       (decdig/uscore-digit (char-code #\0)))
                (= (len dus) 1)))
  :hooks (:fix)
  :prepwork
  ((defrulel hooks-fix-lemma
     (equal (last (decdig/uscore-list-fix x))
            (decdig/uscore-list-fix (last x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod dec-integer-literal
  :short "Fixtype of decimal integer literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "A decimal integer literal consists of
     (i) a sequence of decimal digits and underscores
     satisfying the constraints in @(tsee decdig/uscore-list-wfp), and
     (ii) an optional integer type suffix.")
   (xdoc::p
    "The set of values of this fixtype should be isomorphic to
     the set of strings (or parse trees) defined by
     the Java grammar rule @('decimal-integer-literal').
     This remains to be proved formally."))
  ((digits/uscores decdig/uscore-list
                   :reqfix (if (decdig/uscore-list-wfp digits/uscores)
                               digits/uscores
                             (list (decdig/uscore-digit (char-code #\0)))))
   (suffix? optional-integer-type-suffix))
  :tag :dec-integer-lit
  :layout :list
  :require (decdig/uscore-list-wfp digits/uscores))
