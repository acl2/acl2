; Replacing all instances of an item in a list
;
; Copyright (C) 2015-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Replace all instances of OLD with NEW in ITEMS.
(defun replace-item (old new items)
  (declare (xargs :guard (and (true-listp items))))
  (if (endp items)
      items
    (cons (if (equal (first items) old)
              new
            (first items))
          (replace-item old new (rest items)))))
