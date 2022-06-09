; Making an array of zeros
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/lists-light/repeat" :dir :system)
(include-book "bv-arrayp")
(local (include-book "all-unsigned-byte-p2"))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))

;todo: use in the JVM model
(defund array-of-zeros (width len)
  (declare (ignore width)
           (xargs :guard (natp len)))
  (repeat len 0))

(defthm len-of-array-of-zeros
  (equal (len (array-of-zeros width len))
         (nfix len))
  :hints (("Goal" :in-theory (enable array-of-zeros))))

(defthm BV-ARRAYP-of-array-of-zeros
  (implies (and (natp element-size)
                (natp len))
           (BV-ARRAYP ELEMENT-SIZE len (ARRAY-OF-ZEROS ELEMENT-SIZE len)))
  :hints (("Goal" :in-theory (enable BV-ARRAYP ARRAY-OF-ZEROS))))

(defthm array-of-zeros-iff
  (iff (array-of-zeros width len)
       (not (zp len)))
  :hints (("Goal" :in-theory (enable array-of-zeros))))

(defthm all-unsigned-byte-p-of-array-of-zeros
  (implies (natp width)
           (all-unsigned-byte-p width (array-of-zeros width len)))
  :hints (("Goal" :in-theory (enable array-of-zeros))))

(defthm nthcdr-of-array-of-zeros
  (implies (natp n)
           (equal (nthcdr n (array-of-zeros width len))
                  (array-of-zeros width (- len n))))
  :hints (("Goal" :in-theory (enable array-of-zeros))))
