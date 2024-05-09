; Getting the defined functions from a term, etc.
;
; Copyright (C) 2022 Kestrel-2023 Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "filter-defined-fns")
(local (include-book "kestrel/terms-light/all-fnnames1" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

(defund defined-fns-in-term (term wrld)
  (declare (xargs :guard (and (pseudo-termp term)
                              (plist-worldp wrld))))
  (let ((fns (all-fnnames term)))
    (if (not (function-symbolsp fns wrld))
        (er hard? 'defined-fns-in-term "At least one of the functions is not in the world: ~x0." fns)
      (filter-defined-fns fns wrld))))

(defthm symbol-listp-of-defined-fns-in-term
  (implies (pseudo-termp term)
           (symbol-listp (defined-fns-in-term term wrld)))
  :hints (("Goal" :in-theory (enable defined-fns-in-term))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund defined-fns-in-terms (terms wrld acc)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (plist-worldp wrld)
                              (symbol-listp acc))))
  (if (endp terms)
      acc ; todo: think about the order here
    (defined-fns-in-terms (rest terms) wrld (union-eq (defined-fns-in-term (first terms) wrld)
                                                      acc))))

(defthm symbol-listp-of-defined-fns-in-terms
  (implies (and (pseudo-term-listp terms)
                (symbol-listp acc))
           (symbol-listp (defined-fns-in-terms terms wrld acc)))
  :hints (("Goal" :in-theory (enable defined-fns-in-terms))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund defined-fns-in-term-lists (term-lists wrld acc)
  (declare (xargs :guard (and (pseudo-term-list-listp term-lists)
                              (plist-worldp wrld)
                              (symbol-listp acc))))
  (if (endp term-lists)
      acc
    (defined-fns-in-term-lists (rest term-lists) wrld (defined-fns-in-terms (first term-lists) wrld acc))))

(defthm symbol-listp-of-defined-fns-in-term-lists
  (implies (and (pseudo-term-list-listp term-lists)
                (symbol-listp acc))
           (symbol-listp (defined-fns-in-term-lists term-lists wrld acc)))
  :hints (("Goal" :in-theory (enable defined-fns-in-term-lists))))
