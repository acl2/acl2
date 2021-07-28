; Removing the nth element of a list.
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Remove the Nth element of LIST.
;; TODO: Does such a function already exist?
(defund remove-nth (n list)
  (declare (xargs :guard (and (natp n)
                              (< n (len list)))))
  (if (zp n)
      (cdr list)
    (cons (car list) (remove-nth (+ -1 n) (cdr list)))))

(defthm len-of-remove-nth
  (implies (and (natp n)
                (< n (len list)))
           (equal (len (remove-nth n list))
                  (+ -1 (len list))))
  :hints (("Goal" :in-theory (enable remove-nth))))
