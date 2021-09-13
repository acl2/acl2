; Rules mixing bvcat and bvplus
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvcat")
(include-book "bvplus")
(local (include-book "unsigned-byte-p"))

(defthmd plus-of-bvcat-fits-in-low-bits-core-helper
  (implies (and (<= 0 (+ k1 k2))
                (< (+ k1 k2) (expt 2 lowsize))
                (unsigned-byte-p lowsize k2) ;drop
                ;(natp lowsize)
                (integerp k1))
           (equal (+ k1 (bvcat highsize x lowsize k2))
                  (bvcat highsize x lowsize (+ k2 k1))))
  :hints (("Goal" :expand ((unsigned-byte-p lowsize (+ k1 k2)))
           :in-theory (enable bvcat logapp))))

(defthm bvcat-of-+-of-bvchop
  (implies (and (integerp k1) (integerp k2))
           (equal (BVCAT HIGHSIZE X LOWSIZE (+ K1 (BVCHOP LOWSIZE K2)))
                  (BVCAT HIGHSIZE X LOWSIZE (+ K1 K2)))))

(defthm plus-of-bvcat-fits-in-low-bits-core
  (implies (and (<= 0 (+ k1 (bvchop lowsize k2)))
                (< (+ k1 (bvchop lowsize k2)) (expt 2 lowsize))
                (natp lowsize)
                (integerp k2)
                (integerp k1))
           (equal (+ k1 (bvcat highsize x lowsize k2))
                  (bvcat highsize x lowsize (+ k2 k1))))
  :hints (("Goal" :use (:instance plus-of-bvcat-fits-in-low-bits-core-helper (k2 (bvchop lowsize k2))))))

(defthm plus-of-bvcat-fits-in-low-bits-core-negative-k1
  (implies (and (<= 0 (+ k1 (bvchop lowsize k2)))
                (<= k1 0)
                (natp lowsize)
                (integerp k1))
           (equal (+ k1 (bvcat highsize x lowsize k2))
                  (bvcat highsize x lowsize (+ k2 k1))))
  :hints (("Goal" :in-theory (disable plus-of-bvcat-fits-in-low-bits-core)
           :use (:instance plus-of-bvcat-fits-in-low-bits-core))))

(defthm bvplus-of-bvcat-fits-in-low-bits-core-negative-k1-helper
  (implies (and (<= 0 (+ k1 (bvchop lowsize k2)))
                (<= k1 0)
                (natp lowsize)
                (natp highsize)
                (<= (+ lowsize highsize) size)
                (integerp size)
                (integerp k1))
           (equal (bvplus size k1 (bvcat highsize x lowsize k2))
                  (bvcat highsize x lowsize (+ k2 k1))))
  :hints (("Goal" :in-theory (e/d (bvplus) (plus-of-bvcat-fits-in-low-bits-core-negative-k1
                                            BVCAT-OF-BVCHOP-LOW ;looped
                                            ))
           :use (:instance plus-of-bvcat-fits-in-low-bits-core-negative-k1))))
