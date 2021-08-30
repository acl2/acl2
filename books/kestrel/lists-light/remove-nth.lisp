; Removing the nth element of a list.
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Remove the Nth element (0-based) of LIST.
;; TODO: Does such a function already exist?
(defund remove-nth (n list)
  (declare (xargs :guard (and (natp n)
                              (< n (len list)))))
  (if (endp list)
      nil ; or could return list here
    (if (zp n)
        (rest list) ; drop the 0th element
      (cons (first list) (remove-nth (+ -1 n) (rest list))))))

(defthm len-of-remove-nth
  (implies (and (natp n)
                (< n (len list)))
           (equal (len (remove-nth n list))
                  (+ -1 (len list))))
  :hints (("Goal" :in-theory (enable remove-nth))))

(defthm remove-nth-when->=
  (implies (<= (len list) (nfix n))
           (equal (remove-nth n list)
                  (true-list-fix list)))
  :hints (("Goal" :in-theory (enable remove-nth))))
