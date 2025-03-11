; Mapping unpackbv over a list.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "unpackbv")
(include-book "kestrel/sequences/defmap" :dir :system)
(include-book "kestrel/typed-lists-light/items-have-len" :dir :system)
(include-book "kestrel/typed-lists-light/all-all-integerp" :dir :system)
(include-book "all-all-unsigned-byte-p")
(include-book "kestrel/typed-lists-light/all-true-listp" :dir :system)

;; todo: try the definition below instead of this defmap call
(defmap map-unpackbv (itemcount itemsize bv-lst) (unpackbv itemcount itemsize bv-lst) :fixed (itemcount itemsize)
  :declares ((xargs :guard (and (integer-listp bv-lst)
                                         (natp itemcount)
                                         (natp itemsize)))))

;; todo: put this in:
;; ;; Splits each of the BVS into a list of NUM items, each with SIZE bits.
;; ;; The result is a list of lists, one list for each of the original BVS.
;; ;; Unpacking is done in big-endian fashion, so the most significant chunk of
;; ;; each BV comes first in the corresponding list.
;; (defun map-unpackbv (num size bvs)
;;   (declare (xargs :guard (and (natp size)
;;                               (natp num)
;;                               (all-integerp bvs))))
;;   (if (atom bvs)
;;       nil
;;     (cons (unpackbv num size (first bvs))
;;           (map-unpackbv num size (rest bvs)))))

(defthm true-list-listp-of-map-unpackbv
  (true-list-listp (map-unpackbv num size bvs))
  :hints (("Goal" :in-theory (enable map-unpackbv))))

(defthm all-true-listp-of-map-unpackbv
  (implies (natp itemcount)
           (all-true-listp (map-unpackbv itemcount itemsize bv-lst)))
  :hints (("Goal" :in-theory (enable map-unpackbv))))

(defthm all-all-unsigned-byte-p-of-map-unpackbv
  (implies (natp size)
           (all-all-unsigned-byte-p size (map-unpackbv itemcount size bvs)))
  :hints (("Goal" :in-theory (enable map-unpackbv))))

(defthm all-all-integerp-of-map-unpackbv
  (all-all-integerp (map-unpackbv num size bvs))
  :hints (("Goal" :in-theory (enable map-unpackbv))))

(defthm items-have-len-of-map-unpackbv
  (implies (natp itemcount)
           (items-have-len itemcount (map-unpackbv itemcount itemsize bv-lst)))
  :hints (("Goal" :in-theory (enable map-unpackbv items-have-len))))

;; (defthm len-of-map-unpackbv
;;   (equal (len (map-unpackbv num size bvs))
;;          (len bvs)))

;; (defthm consp-of-map-unpackbv
;;   (equal (consp (map-unpackbv num size bvs))
;;          (consp bvs)))
