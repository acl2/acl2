; Rules about map-packbv and map-unpackbv
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "map-packbv")
(include-book "map-unpackbv")
(include-book "packbv-and-unpackbv")
(local (include-book "kestrel/lists-light/take" :dir :system))

(defthm map-packbv-of-map-unpackbv
  (implies (and (natp itemcount)
                (posp itemsize))
           (equal (map-packbv itemcount itemsize (map-unpackbv itemcount itemsize bvs))
                  (bvchop-list (* itemcount itemsize) bvs)))
  :hints (("Goal" :in-theory (enable packbv map-packbv map-unpackbv))))

(defthm map-unpackbv-of-map-packbv
  (implies (and (all-all-unsigned-byte-p itemsize lists)
                (items-have-len itemcount lists)
                (true-list-listp lists)
                (natp itemcount)
                (posp itemsize))
           (equal (map-unpackbv itemcount itemsize (map-packbv itemcount itemsize lists))
                  lists))
  :hints (("Goal" :in-theory (enable packbv map-packbv map-unpackbv items-have-len))))
