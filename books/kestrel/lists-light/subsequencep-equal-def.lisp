; A definition of subsequencep-equal.
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defund subsequencep-equal (x y)
  (declare (xargs :guard (and (true-listp x)
                              (true-listp y))))
  (if (endp x)
      t
    (let ((tail (member-equal (first x) y)))
      (if (endp tail)
          nil
        (subsequencep-equal (rest x) (rest tail))))))
