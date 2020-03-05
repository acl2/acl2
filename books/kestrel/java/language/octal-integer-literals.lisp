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
(include-book "octal-digits")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ octal-integer-literals
  :parents (integer-literals)
  :short "Java octal integer literals [JLS:3.10.1]."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum octdig/uscore
  :short "Fixtype of octal digits and underscores."
  :long
  (xdoc::topstring-p
   "An @('octal-numeral') in the grammar
    consists of octal digits and underscores.")
  (:digit ((get oct-digit)))
  (:underscore ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist octdig/uscore-list
  :short "Fixtype of true lists of octal digits and underscores."
  :long
  (xdoc::topstring-p
   "An @('octal-numeral') in the grammar
    is a sequence of octal digits and underscores,
    subject to certain restrictions
    formalized in @(tsee octdig/uscore-list-wfp).")
  :elt-type octdig/uscore
  :true-listp t
  :elementp-of-nil nil
  :pred octdig/uscore-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define octdig/uscores-to-digits ((dus octdig/uscore-listp))
  :returns (ds oct-digit-listp)
  :short "Remove the underscores from a list of octal digits and underscores."
  :long
  (xdoc::topstring-p
   "Any underscores in an @('octal-numeral') in the grammar
    are just used for separation.
    This function returns the underlying sequence of octal digits.")
  (b* (((when (endp dus)) nil)
       (du (car dus)))
    (octdig/uscore-case
     du
     :digit (cons du.get (octdig/uscores-to-digits (cdr dus)))
     :underscore (octdig/uscores-to-digits (cdr dus))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define octdig/uscore-list-wfp ((dus octdig/uscore-listp))
  :returns (yes/no booleanp)
  :short "Check if an octal numeral is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "An @('octal-numeral') in the grammar
     is a list of octal digits and underscores
     subject to the following constraints,
     derived from the grammar:")
   (xdoc::ul
    (xdoc::li
     "It must start with the digit 0, not an underscore or other digit.")
    (xdoc::li
     "It must end with a digit, not an underscore.")
    (xdoc::li
     "It must contain at least two digits
      (which implies that it cannot be confused
      with the decimal numeral @('0')).")))
  (and (consp dus)
       (equal (octdig/uscore-fix (car dus))
              (octdig/uscore-digit (char-code #\0)))
       (octdig/uscore-case (car (last dus)) :digit)
       (> (len (octdig/uscores-to-digits dus)) 1))
  :hooks (:fix)
  :prepwork
  ((defrulel hooks-fix-lemma
     (equal (last (octdig/uscore-list-fix x))
            (octdig/uscore-list-fix (last x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod oct-integer-literal
  :short "Fixtype of octal integer literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "An octal integer literal consists of
     (i) a sequence of octal digits and underscores
     satisfying the constraints in @(tsee octdig/uscore-list-wfp), and
     (ii) an optional integer type suffix.")
   (xdoc::p
    "The set of values of this fixtype should be isomorphic to
     the set of strings (or parse trees) defined by
     the Java grammar rule @('octal-integer-literal').
     This remains to be proved formally."))
  ((digits/uscores octdig/uscore-list
                   :reqfix (if (octdig/uscore-list-wfp digits/uscores)
                               digits/uscores
                             (list (octdig/uscore-digit (char-code #\0))
                                   (octdig/uscore-digit (char-code #\0)))))
   (prefix-upcase-p bool)
   (suffix? optional-integer-type-suffix))
  :tag :oct-integer-lit
  :layout :list
  :require (octdig/uscore-list-wfp digits/uscores))
