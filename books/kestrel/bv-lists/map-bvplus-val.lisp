; BV Lists Library: map-bvplus-val
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv/bvplus" :dir :system)
(include-book "unsigned-byte-listp")

;; One value is fixed, the other is a list
(defund map-bvplus-val (size val lst)
  (if (endp lst)
      nil
    (cons (bvplus size val (first lst))
          (map-bvplus-val size val (rest lst)))))

(defthm unsigned-byte-listp-of-map-bvplus-val
  (implies (natp size)
           (unsigned-byte-listp size (map-bvplus-val size val data)))
  :hints (("Goal" :in-theory (enable map-bvplus-val))))

(defthm len-of-map-bvplus-val
  (equal (len (map-bvplus-val high low data))
         (len data))
  :hints (("Goal" :in-theory (enable map-bvplus-val))))

(defthmd bvplus-of-nth
  (implies (and (natp n)
                (< n (len data)))
           (equal (bvplus size val (nth n data))
                  (nth n (map-bvplus-val size val data))))
  :hints (("Goal" :in-theory (enable map-bvplus-val (:I nth)))))
