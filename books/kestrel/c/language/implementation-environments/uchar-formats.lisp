; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "centaur/fty/top" :dir :system)

(include-book "../../portcullis")

(local (include-book "arithmetic-3/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ uchar-formats
  :parents (implementation-environments)
  :short "Formats of @('unsigned char') objects."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize the possible formats of @('unsigned char') objects,
     along with some operations on them."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod uchar-format
  :short "Fixtype of formats of @('unsigned char') objects."
  :long
  (xdoc::topstring
   (xdoc::p
    "Values of the @('unsigned char') type are represented
     using a pure binary notation [C17:6.2.6.1/3],
     i.e. where each bit counts for a successive power of 2.
     Footnote 50 says that a byte consists of @('CHAR_BIT') bits,
     and implies that an @('unsigned char') consists of one byte
     (as also implied by [C17:6.5.3.4/2] and [C17:6.5.3.4/4]).")
   (xdoc::p
    "Thus, the format of @('unsigned char') objects is determined
     by their number of bits, i.e. @('CHAR_BIT').
     This is required to be at least 8 [C17:5.2.4.2.1/1].")
   (xdoc::p
    "We use the name @('size') for the number of bits,
     i.e. the size (in bits) of @('unsigned char') objects."))
  ((size nat :reqfix (if (>= size 8) size 8)))
  :require (>= size 8)
  :pred uchar-formatp
  :prepwork ((local (in-theory (enable nfix))))
  ///

  (defret uchar-format->size-type-prescription
    (and (posp size)
         (> size 1))
    :fn uchar-format->size
    :rule-classes :type-prescription)

  (defret uchar-format->size-lower-bound
    (>= size 8)
    :fn uchar-format->size
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uchar-format->max ((format uchar-formatp))
  :returns (max posp :hints (("Goal" :in-theory (enable posp))))
  :short "The ACL2 integer value of @('UCHAR_MAX') [C17:5.2.4.2.1/1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This directly derives from @('CHAR_BIT'),
     as discussed in @(tsee uchar-format),
     and in footnote 50 of [C17:6.2.6.1//3],
     which says that @('unsigned char') values
     range from 0 to @($2^{\\mathtt{CHAR\\_BIT}}-1$).")
   (xdoc::p
    "This is at least 255, as required by [C17:5.2.4.2.1/1]."))
  (1- (expt 2 (uchar-format->size format)))
  :hooks (:fix)
  ///

  (defret uchar-format->-max-type-prescription
    (and (posp max)
         (> max 1))
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (enable posp))))

  (defrulel lemma
    (>= (expt 2 (uchar-format->size format)) 256)
    :rule-classes :linear
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
                    (x 2) (m 8) (n (uchar-format->size format)))
    :disable acl2::expt-is-weakly-increasing-for-base->-1)

  (defret uchar-format->max-lower-bound
    (>= max 255)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uchar-format-8 ()
  :returns (format uchar-formatp)
  :short "The @('unsigned char') format defined by 8 bits."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the simplest and most common format for @('unsigned char')."))
  (make-uchar-format :size 8)

  ///

  (defruled uchar-format->max-of-uchar-format-8
    (equal (uchar-format->max (uchar-format-8))
           255)))
