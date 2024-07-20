; A variant of aset1 that checks its index
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "alen1")

(in-theory (disable (:executable-counterpart break$))) ;keeps it from breaking when it's evaluated during a proof, e.g., proofs about aset1-safe

;this makes sure the index is in bounds, which prevents memory from getting trashed if this is called on bad arguments
(defund aset1-safe (name l n val)
  (declare (xargs :guard (and (array1p name l)
                              (integerp n)
                              (>= n 0)
                              (< n (alen1 name l)))))
  (if (< n (alen1 name l))
      (aset1 name l n val)
    (progn$ ;(print-list l)
            (cw "Bad index, ~x0, for array ~x1 with len ~x2." n name (alen1 name l))
            (break$) ;(car 7) ;this causes a crash and is better than a hard-error since it puts us into the debugger.
            ;;aset1-safe is logically just aset1
            (aset1 name l n val))))

(defthm aset1-safe-becomes-aset1
  (implies t ;(< n (alen1 name l))
           (equal (aset1-safe name l n val)
                  (aset1 name l n val)))
  :hints (("Goal" :in-theory (enable aset1-safe))))
