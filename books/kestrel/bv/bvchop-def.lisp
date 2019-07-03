; BV Library: The definition of bvchop.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; these help prove natp-of-bvchop-type
(local (include-book "../arithmetic-light/expt"))
(local (include-book "../arithmetic-light/mod"))

;; Chop X down to its least significant SIZE bits.
;; TODO: Try make the :exec body more efficient.
(defund bvchop (size x)
  (declare (xargs :guard (and (natp size)
                              (integerp x))))
  (mbe :logic (mod (ifix x) (expt 2 (nfix size)))
       :exec (mod x (expt 2 size))))

(defthm natp-of-bvchop-type
  (natp (bvchop size x))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable bvchop))))

(in-theory (disable (:t bvchop))) ;natp-of-bvchop-type is better
