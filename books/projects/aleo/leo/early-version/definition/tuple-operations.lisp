; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "values")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ tuple-operations
  :parents (dynamic-semantics)
  :short "Leo tuple operations."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are operations to manipulate tuples."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-tuple-make ((vals value-listp))
  :returns (result valuep)
  :short "Leo tuple construction operation."
  :long
  (xdoc::topstring
   (xdoc::p
    "A tuple in Leo is constructed from two or more values.
     However, here we also allow tuples of zero or one value.
     Tuples of zero values are constructed from the unit expression.
     There is no syntax in Leo to construct tuples of 1 value.
     The values may have any types.
     This operation never fails."))
  (value-tuple vals)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-tuple-read ((tupval valuep) (index natp))
  :returns (result value-resultp)
  :short "Leo tuple reading operation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This takes a value and a natural number index;
     the latter must be a numeral in the syntax.
     The value must be a tuple, otherwise it is an error.
     Furthermore, the index must be below the tuple length;
     tuples are zero-indexed."))
  (if (and (value-case tupval :tuple)
           (< (nfix index) (len (value-tuple->components tupval))))
      (nth (nfix index) (value-tuple->components tupval))
    (reserrf (list :op-tuple-read (value-fix tupval) (nfix index))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-tuple-write ((tupval valuep) (index natp) (newval valuep))
  :returns (result value-resultp)
  :short "Leo tuple writing operation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This formalizes the replacement of a tuple component with a new value.
     The new value must have the same type as the old one,
     otherwise we defensively return an error indication:
     this ensures that tuples maintain their types under writing,
     an invariant that we will eventually prove."))
  (b* ((err (reserrf (list :op-tuple-write
                       (value-fix tupval)
                       (nfix index)
                       (value-fix newval))))
       ((unless (value-case tupval :tuple)) err)
       (vals (value-tuple->components tupval))
       ((unless (< (nfix index) (len vals))) err)
       (oldval (nth (nfix index) vals))
       ((unless (equal (type-of-value newval)
                       (type-of-value oldval)))
        err))
    (value-tuple (update-nth (nfix index) newval vals)))
  :hooks (:fix))
