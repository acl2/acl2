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

(include-book "uchar-formats")
(include-book "schar-formats")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ char-formats
  :parents (implementation-environments)
  :short "Formats of (plain) @('char') objects."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize the possible formats of @('char') objects,
     along with some operations on them."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod char-format
  :short "Fixtype of formats of @('char') objects."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('char') type has the same representation as
     either @('unsigned char') or @('signed char')
     [C17:6.2.5/15].
     The choice is captured by a boolean."))
  ((signedp bool))
  :pred char-formatp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-format->max ((char-format char-formatp)
                          (uchar-format uchar-formatp)
                          (schar-format schar-formatp))
  :returns (max posp)
  :short "The ACL2 integer value of @('CHAR_MAX') [C17:5.2.4.2.1/1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in [C17:5.2.4.2.1/2],
     this is the same as either @('UCHAR_MAX') or @('SCHAR_MAX')."))
  (if (char-format->signedp char-format)
      (schar-format->max schar-format uchar-format)
    (uchar-format->max uchar-format))
  :hooks (:fix)
  ///

  (defret char-format->max-type-prescription
    (and (posp max)
         (> max 1))
    :rule-classes :type-prescription)

  (defret char-format->max-lower-bound
    (>= max 127)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-format->min ((char-format char-formatp)
                          (uchar-format uchar-formatp)
                          (schar-format schar-formatp))
  :returns (min integerp)
  :short "The ACL2 integer value of @('CHAR_MIN') [C17:5.2.4.2.1/1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in [C17:5.2.4.2.1/2],
     this is either 0 or the same as @('SCHAR_MIN')."))
  (if (char-format->signedp char-format)
      (schar-format->min schar-format uchar-format)
    0)
  :hooks (:fix)
  ///

  (defret char-format->min-type-prescription
    (and (integerp min)
         (<= min 0))
    :rule-classes :type-prescription)

  (defret char-format->min-upper-bound
    (<= min 0)
    :rule-classes
    ((:linear
      :trigger-terms
      ((char-format->min char-format uchar-format schar-format))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-format-8u ()
  :returns (format char-formatp)
  :short "The @('char') format defined by 8 bits and unsignedness."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the simplest format of @('char').
     It is not clear whether it is the most common or not."))
  (make-char-format :signedp nil)

  ///

  (defruled char-format->max-of-char-format-8u
    (equal (char-format->max (char-format-8u)
                             (uchar-format-8)
                             (schar-format-8tcnt))
           255))

  (defruled char-format->min-of-char-format-8u
    (equal (char-format->min (char-format-8u)
                             (uchar-format-8)
                             (schar-format-8tcnt))
           0)))
