; BV Lists Library: map-bvsx
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv/bvsx" :dir :system)
(include-book "unsigned-byte-listp")

(defund map-bvsx (high low lst)
  (if (endp lst)
      nil
    (cons (bvsx high low (first lst))
          (map-bvsx high low (rest lst)))))

(defthm unsigned-byte-listp-of-map-bvsx
  (implies (natp high)
           (unsigned-byte-listp high (map-bvsx high low data)))
  :hints (("Goal" :in-theory (enable map-bvsx))))

(defthm len-of-map-bvsx
  (equal (len (map-bvsx high low data))
         (len data))
  :hints (("Goal" :in-theory (enable map-bvsx))))

(defthmd bvsx-of-nth
  (implies (and (natp n)
                (< n (len data)))
           (equal (bvsx high low (nth n data))
                  (nth n (map-bvsx high low data))))
  :hints (("Goal" :in-theory (enable map-bvsx (:I nth)))))
