; Extracting every nth value of a list
;
; Copyright (C) 2022-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/ceiling" :dir :system))
(local (include-book "nthcdr"))
(local (include-book "revappend"))

(defund every-nth-exec-aux (n vals acc)
  (declare (xargs :guard (and (posp n)
                              (true-listp vals)
                              (true-listp acc))
                  :measure (len vals)
                  ))
  (if (not (mbt (posp n))) ; for termination
      nil
    (if (endp vals)
        (reverse acc)
      (every-nth-exec-aux n (nthcdr n vals) (cons (first vals) acc)))))

(defund every-nth-exec (n vals)
  (declare (xargs :guard (and (posp n)
                              (true-listp vals))))
  (every-nth-exec-aux n vals nil))

(defund every-nth (n vals)
  (declare (xargs :guard (and (posp n)
                              (true-listp vals))
                  :verify-guards nil ; done below
                  :measure (len vals)
                  ))
  (mbe :logic
       (if (not (mbt (posp n))) ; for termination
           nil
         (if (endp vals)
             nil
           (cons (first vals)
                 (every-nth n (nthcdr n vals)))))
       :exec (every-nth-exec n vals)))

(defthm every-nth-exec-aux-helper
  (implies (and (true-listp acc)
                (posp n))
           (equal (every-nth-exec-aux n vals acc)
                  (append (reverse acc)
                          (every-nth n vals))))
  :hints (("Goal" :in-theory (enable every-nth every-nth-exec-aux))))

(verify-guards every-nth :hints (("Goal" :in-theory (enable every-nth-exec every-nth))))

; (equal (every-nth 3 '(0 1 2 3 4 5 6 7 8 9 10)) '(0 3 6 9))

(defthm consp-of-every-nth
  (implies (posp n)
           (equal (consp (every-nth n vals))
                  (consp vals)))
  :hints (("Goal" :in-theory (enable every-nth))))

(defun ind (n vals n2)
   (declare (xargs :measure (len vals)))
   (if (not (posp n2))
       nil
     (if (endp vals)
         (list n vals n2)
       (ind (- n 1) (nthcdr n2 vals) n2))))

(defthm nth-of-every-nth
  (implies (and (posp n2)
                (natp n))
           (equal (nth n (every-nth n2 vals))
                  (nth (* n n2) vals)))
  :hints (("Goal" :in-theory (enable every-nth)
           :induct (ind n vals n2))))

(defthmd nth-when-remainder-known
  (implies (and (equal remainder (mod index modulus))
                (natp index)
                (posp modulus))
           (equal (nth index vals)
                  (nth (floor index modulus) (every-nth modulus (nthcdr remainder vals))))))

(defthm len-of-every-nth
  (implies (posp n)
           (equal (len (every-nth n vals))
                  (ceiling (len vals) n)))
  :hints (("Goal" :cases ((equal n 1))
           :in-theory (enable every-nth))))
