; Filter a list to keep the functions that are in :logic mode
;
; Copyright (C) 2022-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "fn-logicp")
(include-book "function-symbolsp")
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

;; Given a list of functions in WRLD, keep the logic-mode ones.
(defund filter-logic-mode-fns (fns wrld acc)
  (declare (xargs :guard (and (symbol-listp fns)
                              (plist-worldp wrld)
                              (function-symbolsp fns wrld)
                              (symbol-listp acc))))
  (if (endp fns)
      (reverse acc)
    (let ((fn (first fns)))
      (filter-logic-mode-fns (rest fns)
                             wrld
                             (if (fn-logicp fn wrld)
                                 (cons fn acc)
                               acc)))))

(defthm symbol-listp-of-filter-logic-mode-fns
  (implies (and (symbol-listp fns)
                (symbol-listp acc))
           (symbol-listp (filter-logic-mode-fns fns wrld acc)))
  :hints (("Goal" :in-theory (enable filter-logic-mode-fns))))
