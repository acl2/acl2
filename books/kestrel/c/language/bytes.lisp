; C Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2020 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "kestrel/fty/defbyte" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bytes
  :parents (language)
  :short "Bytes."
  :long
  (xdoc::topstring
   (xdoc::p
    "A byte [C:3.6] consists of
     @('CHAR_BIT') bits [C:6.2.6.1/3, Footnote 50],
     which must be at least 8 [C:5.2.4.2.1].")
   (xdoc::p
    "Our C formalization is paramterized
     over the specific value of @('CHAR_BIT')."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-bit-constrp (char-bit)
  :returns (yes/no booleanp)
  :short "Constraints on the value of @('CHAR_BIT')."
  :long
  (xdoc::topstring
   (xdoc::p
    "It must be an integer that is at least 8."))
  (and (integerp char-bit)
       (>= char-bit 8))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection char-bit
  :short "Parameter for the specific value of @('CHAR_BIT')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This constrained nullary function is a parameter of our C formalization.
     It expresses the value of @('CHAR_BIT').")
   (xdoc::@def "char-bit"))

  (encapsulate

    (((char-bit) => *))

    (local (define char-bit () 8))

    (defrule char-bit-constrp-of-char-bit
      (char-bit-constrp (char-bit))))

  (defrule posp-of-char-bit
    (posp (char-bit))
    :rule-classes :type-prescription
    :use char-bit-constrp-of-char-bit
    :disable char-bit-constrp-of-char-bit
    :enable char-bit-constrp)

  (defrule char-bit-gteq-8
    (>= (char-bit) 8)
    :rule-classes :linear
    :use char-bit-constrp-of-char-bit
    :disable char-bit-constrp-of-char-bit
    :enable char-bit-constrp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defbyte byte
  :short "Fixtype of bytes."
  :size (char-bit)
  :pred bytep)
