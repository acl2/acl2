; A function to recognize lists of lists of unsigned-bytes
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-unsigned-byte-p")
(include-book "kestrel/sequences/defforall" :dir :system)

;this is really a double forall - gen lemmas like all-unsigned-byte-p-of-car
(defforall all-all-unsigned-byte-p (n x) (all-unsigned-byte-p n x) :fixed (n))

(verify-guards all-all-unsigned-byte-p)

(defthm all-unsigned-byte-p-of-car-2
  (implies (and (all-all-unsigned-byte-p free x)
                (< 0 (len x)))
           (all-unsigned-byte-p free (car x)))
  :hints
  (("Goal" :in-theory (enable all-all-unsigned-byte-p))))

;should the forall do this?
(defthm booleanp-of-all-all-unsigned-byte-p
  (booleanp (all-all-unsigned-byte-p n x)))

;the forall should do this?
(defthm all-all-unsigned-byte-p-of-nil
  (all-all-unsigned-byte-p size nil)
  :hints (("Goal" :in-theory (enable all-all-unsigned-byte-p))))

(defthm all-unsigned-byte-p-when-all-all-unsigned-byte-p
  (implies (and (all-all-unsigned-byte-p free x)
                (< n (len x))
                (natp n))
           (all-unsigned-byte-p free (nth n x)))
  :hints (("Goal" :in-theory (e/d (ALL-ALL-UNSIGNED-BYTE-P nth) (;nth-of-cdr
                                                                   )))))
