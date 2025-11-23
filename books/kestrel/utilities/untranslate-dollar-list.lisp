; Applying the :logic-mode untranslate function to each term in a list
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/system/untranslate-dollar" :dir :system)

;; Returns a list of (untranslated) terms.
(defund untranslate$-list (terms iff-flg state)
  (declare (xargs :guard (pseudo-term-listp terms)
                  :stobjs state))
  (if (endp terms)
      nil
    (cons (untranslate$ (first terms) iff-flg state)
          (untranslate$-list (rest terms) iff-flg state))))
