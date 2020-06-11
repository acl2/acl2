; A utility to apply a unary wrapper to all items in a list
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;; Turn each of the ITEMS into a unary call of FN on that item.
(defun wrap-all (fn items)
  (declare (xargs :guard (true-listp items)))
  (if (endp items)
      nil
    (cons `(,fn ,(first items))
          (wrap-all fn (rest items)))))
