; Making a NOT with a hint to avoid consing
;
; Copyright (C) 2024-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Make a NOT from ARG, except return HINT (and avoid consing)
;; if HINT is that NOT.
;; Let's try leaving this enabled, since its :logic part is nice.
(defun make-not-with-hint (arg
                           hint ; (not <arg>)
                           )
  (declare (xargs :guard (and (true-listp hint)
                              (= 2 (len hint))
                              (eq 'not (car hint)))))
  (mbe :exec (if (equal arg (cadr hint))
                 hint ; reuse the hint, to avoid consing
               `(not ,arg))
       :logic `(not ,arg)))
