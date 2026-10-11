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

(include-book "../../portcullis")

(include-book "centaur/fty/top" :dir :system)

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

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
     using a pure binary notation [C17:6.2.6.1/3] [C23:6.2.6.1],
     i.e. where each bit counts for a successive power of 2.
     [C17:5.2.4.2.1/1] [C23:5.3.5.3.2] say that
     a byte consists of @('CHAR_BIT') bits.
     [C17:6.5.3.4/2] [C17:6.5.3.4/4] [C23:6.5.4.5] say that
     an @('unsigned char') consists of one byte.")
   (xdoc::p
    "Thus, the format of @('unsigned char') objects is determined
     by their number of bits, i.e. @('CHAR_BIT').
     This is required to be at least 8
     [C17:5.2.4.2.1/1] [C23:5.3.5.3.2].")
   (xdoc::p
    "We use the name @('size') for the number of bits,
     i.e. the size (in bits) of @('unsigned char') objects."))
  ((size nat :reqfix (if (>= size 8) size 8)))
  :require (>= size 8)
  :pred uchar-formatp
  :prepwork ((local (in-theory (enable (:e tau-system)))))
  ///

  (defret uchar-format->size-type-prescription
    (and (posp size)
         (> size 1))
    :fn uchar-format->size
    :rule-classes :type-prescription)

  (defret uchar-format->size-lower-bound
    (>= size 8)
    :fn uchar-format->size
    :rule-classes :linear)

  (defruled expt-of-one-less-than-uchar-format->size-lower-bound
    (>= (expt 2 (1- (uchar-format->size format))) 128)
    :rule-classes :linear
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
                    (x 2) (m 7) (n (1- (uchar-format->size format))))
    :disable acl2::expt-is-weakly-increasing-for-base->-1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uchar-format->max ((format uchar-formatp))
  :returns (max posp :hints (("Goal" :in-theory (enable posp))))
  :short "The ACL2 integer value of @('UCHAR_MAX')
          [C17:5.2.4.2.1/1] [C23:5.3.5.3.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This directly derives from @('CHAR_BIT'),
     as discussed in @(tsee uchar-format).")
   (xdoc::p
    "This is at least 255, as required by
     [C17:5.2.4.2.1/1] [C23:5.3.5.3.2]."))
  (1- (expt 2 (uchar-format->size format)))

  ///

  (defret uchar-format->max-type-prescription
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
