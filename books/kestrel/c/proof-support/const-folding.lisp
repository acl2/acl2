; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2026 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../representation/integer-operations")
(include-book "../atc/arrays")

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ const-folding
  :parents (proof-support)
  :short "Rules to fold constants."
  :long
  (xdoc::topstring
   (xdoc::p
    "In some proofs, it may be useful to simplify operations on constants,
     by which we mean C operations and C values.
     We start with a few example rules, which we plan to generalize."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection integer-const-folding
  :short "Constant folding rules for integer operations."
  :long
  (xdoc::topstring
   (xdoc::p
    "These work on C integer constants of the form
     @('(<type>-from-integer <c>)'), e.g. @('(sint-from-integer 4)')."))

  (defruled sub-sint-sint-okp-const-fold
    (implies (and (syntaxp (and (quotep c1)
                                (quotep c2)))
                  (sint-integerp c1)
                  (sint-integerp c2)
                  (sint-integerp (- c1 c2)))
             (sub-sint-sint-okp (sint-from-integer c1)
                                (sint-from-integer c2)))
    :enable sub-sint-sint-okp)

  (defruled sub-sint-sint-const-fold
    (implies (and (syntaxp (and (quotep c1)
                                (quotep c2)))
                  (sint-integerp c1)
                  (sint-integerp c2)
                  (sint-integerp (- c1 c2)))
             (equal (sub-sint-sint (sint-from-integer c1)
                                   (sint-from-integer c2))
                    (sint-from-integer (- c1 c2))))
    :enable sub-sint-sint)

  (defruled lt-sint-sint-const-fold
    (implies (and (syntaxp (and (quotep c1)
                                (quotep c2)))
                  (sint-integerp c1)
                  (sint-integerp c2))
             (equal (lt-sint-sint (sint-from-integer c1)
                                  (sint-from-integer c2))
                    (sint-from-integer (if (< c1 c2) 1 0))))
    :enable lt-sint-sint)

  (defruled boolean-from-sint-const-fold
    (implies (and (syntaxp (quotep c))
                  (sint-integerp c))
             (equal (boolean-from-sint (sint-from-integer c))
                    (if (equal c 0) nil t)))
    :enable boolean-from-sint)

  (defruled uchar-from-sint-const-fold
    (implies (and (syntaxp (quotep c))
                  (uchar-integerp c))
             (equal (uchar-from-sint (sint-from-integer c))
                    (uchar-from-integer c)))
    :enable (uchar-from-sint
             uchar-from-integer-mod
             uchar-integerp-alt-def
             sint-integerp-alt-def
             uchar-max-vs-sint-max
             ifix)))

;;;;;;;;;;;;;;;;;;;;

(defsection array-index-const-folding
  :short "Constant folding rules for operations on array indices."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are for constant integer indices,
     of the form @('(<type>-from-integer 2)'),
     e.g. @('(sint-from-integer 2)').
     The array is not constant."))

  (defruled uchar-array-index-okp-const-fold
    (implies (and (syntaxp (quotep c))
                  (sint-integerp c)
                  (<= 0 c)
                  (< c (uchar-array-length a)))
             (uchar-array-index-okp a (sint-from-integer c)))
    :enable (uchar-array-index-okp
             integer-from-cinteger
             cinteger-kind
             cinteger-sint->get
             integer-range-p
             (:e tau-system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *integer-const-folding*
  :short "List of constant folding rules for integer operations."
  '(sub-sint-sint-okp-const-fold
    sub-sint-sint-const-fold
    lt-sint-sint-const-fold
    boolean-from-sint-const-fold
    uchar-from-sint-const-fold))

(defval *array-index-const-folding*
  :short "List of constant folding rules for operations on array indices."
  '(uchar-array-index-okp-const-fold))

;;;;;;;;;;;;;;;;;;;;

(make-event
 `(def-ruleset integer-const-folding
    ',*integer-const-folding*))

(make-event
 `(def-ruleset array-index-const-folding
    ',*array-index-const-folding*))
