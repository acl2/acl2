; Filter a list to keep the functions that are defined
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "fn-definedp")
(include-book "function-symbolsp")

;; Given a list of functions in WRLD, keep the defined ones.
(defund filter-defined-fns (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns)
                              (plist-worldp wrld)
                              (function-symbolsp fns wrld))))
  (if (endp fns)
      nil
    (let ((fn (first fns)))
      (if (fn-definedp fn wrld)
          (cons fn (filter-defined-fns (rest fns) wrld))
        (filter-defined-fns (rest fns) wrld)))))

(defthm symbol-listp-of-filter-defined-fns
  (implies (symbol-listp fns)
           (symbol-listp (filter-defined-fns fns wrld)))
  :hints (("Goal" :in-theory (enable filter-defined-fns))))
