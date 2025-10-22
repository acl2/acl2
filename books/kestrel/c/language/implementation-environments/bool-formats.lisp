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

(local (include-book "kestrel/utilities/nfix" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bool-formats
  :parents (implementation-environments)
  :short "Formats of @('_Bool') objects."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize the possible formats of @('_Bool') objects,
     along with some operations on them."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod bool-format
  :short "Fixtype of formats of @('_Bool') objects."
  :long
  (xdoc::topstring
   (xdoc::p
    "[C17:6.2.5/2] says that @('_Bool') is large enough to store 0 and 1.
     [C17:6.2.5/6] classifies @('_Bool') as an unsigned integer type;
     as such, [C17:6.2.6.2/1] implies that @('_Bool') object
     must consist of value bits and padding bits.
     Since only the values 0 and 1 are needed,
     it seems reasonable to infer that @('_Bool') objects
     have exactly one value bit;
     but since they must consist of an integral number of bytes [C17:6.2.6.1/2],
     the rest must be all padding bits.
     Although it does not seem reasonable to use more than one byte,
     nothing seems to prevent @('_Bool') object to take two or more bytes.")
   (xdoc::p
    "Thus, to capture the possible formats of @('_Bool') objects,
     we need the number of bytes (normally 1),
     and the index of the value bit,
     where the significance of the index is the same as
     in the lists of bit roles in @(tsee uinteger-format).
     We also include information (for now unconstrained)
     about possible trap representations [C17:6.2.6.1/5]."))
  ((byte-size pos)
   (value-index nat)
   (trap any))
  :pred bool-formatp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bool-format-wfp ((bool-format bool-formatp)
                         (uchar-format uchar-formatp))
  :returns (yes/no booleanp)
  :short "Check if a @('_Bool') format is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The index of the value bit must be within
     the range of indices of the bits that form the @('_Bool') object.
     This depends on the number of bits in a bit,
     which is defined by the @('unsigned char') format.
     So we need a separate predicate (this one) to express this condition,
     which could not be part of the @(tsee bool-format) fixtype."))
  (< (bool-format->value-index bool-format)
     (* (bool-format->byte-size bool-format)
        (uchar-format->size uchar-format)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bool-format-lsb ()
  :returns (format bool-formatp)
  :short "The @('_Bool') format defined by a single byte
          with its least significant bit as the value bit,
          and no trap representations."
  (make-bool-format :byte-size 1
                    :value-index 0
                    :trap nil)

  ///

  (defruled bool-format-wfp-of-bool-format-lsb
    (bool-format-wfp (bool-format-lsb) uchar-format)
    :enable (bool-format-wfp fix)))
