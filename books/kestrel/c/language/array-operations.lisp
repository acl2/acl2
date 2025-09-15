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

(include-book "values")
(include-book "flexible-array-member-removal")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ array-operations
  :parents (language)
  :short "Operations on C arrays."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-array->length ((array valuep))
  :guard (value-case array :array)
  :returns (length posp :hints (("Goal" :in-theory (enable posp))))
  :short "Length of an array."
  (len (value-array->elements array))
  :hooks (:fix)
  :prepwork ((local (include-book "std/lists/len" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-array-read ((index natp) (array valuep))
  :guard (value-case array :array)
  :returns (elem value-resultp
                 :hints (("Goal" :in-theory (enable value-array->length nfix))))
  :short "Read an element from an array."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the index is too large, it is an error."))
  (b* ((index (nfix index))
       ((unless (< index (value-array->length array)))
        (error (list :array-read-index index (value-fix array)))))
    (nth index (value-array->elements array)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-array-write ((index natp) (elem valuep) (array valuep))
  :guard (value-case array :array)
  :returns (new-array value-resultp)
  :short "Write an element to an array."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the index is too large, it is an error.")
   (xdoc::p
    "If the type of the new element does not match the array type,
     it is an error.")
   (xdoc::p
    "Prior to storing the value, we remove its flexible array member, if any.
     See @(tsee remove-flexible-array-member)."))
  (b* ((index (nfix index))
       ((unless (< index (value-array->length array)))
        (error (list :array-write-index index (value-fix array))))
       ((unless (equal (type-of-value elem)
                       (value-array->elemtype array)))
        (error (list :array-write-mistype
                     :required (value-array->elemtype array)
                     :supplied (type-of-value elem))))
       (new-elements (update-nth index
                                 (remove-flexible-array-member elem)
                                 (value-array->elements array))))
    (change-value-array array :elements new-elements))
  :guard-hints (("Goal" :in-theory (enable value-array->length)))
  :hooks (:fix)
  ///

  (defret value-kind-of-value-array-write
    (implies (not (errorp new-array))
             (equal (value-kind new-array)
                    :array)))

  (defruled not-errorp-of-value-array-read-when-not-write-error
    (implies (not (errorp (value-array-write index elem array)))
             (not (errorp (value-array-read index array))))
    :enable (value-array-read
             nfix
             value-array->length
             not-errorp-when-valuep)))
