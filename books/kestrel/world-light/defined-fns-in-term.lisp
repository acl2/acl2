; Getting the defined functions from a term
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "filter-defined-fns")
(local (include-book "kestrel/terms-light/all-fnnames1" :dir :system))

(defund defined-fns-in-term (term wrld)
  (declare (xargs :guard (and (pseudo-termp term)
                              (plist-worldp wrld))))
  (let ((fns (all-fnnames term)))
    (if (not (function-symbolsp fns wrld))
        (er hard? 'defined-fns-in-term "At least one of the functions is not in the world: ~x0." fns)
      (filter-defined-fns fns wrld))))
