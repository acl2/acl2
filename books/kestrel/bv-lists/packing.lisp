; Mixed rules about packing and grouping
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Organize this better

(include-book "kestrel/lists-light/group" :dir :system)
(include-book "kestrel/lists-light/group2" :dir :system)
(include-book "kestrel/lists-light/ungroup" :dir :system)
(include-book "kestrel/lists-light/group-and-ungroup" :dir :system)
(include-book "kestrel/lists-light/rules2" :dir :system) ; for list-split
(include-book "kestrel/lists-light/group-rules" :dir :system) ;to introduce group2
(include-book "packbv")
(include-book "map-packbv")
(include-book "bytes-to-bits")
(include-book "kestrel/arithmetic-light/floor2" :dir :system) ;todo make local
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/divides" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divides" :dir :system))

;move
(defthm floor-of-*-same-arg2
  (implies (and (rationalp i)
                (rationalp j)
                (not (equal 0 j)))
           (equal (floor (* i j) j)
                  (floor i 1)))
  :hints (("Goal" :use (:instance floor-of-*-same)
           :in-theory (disable floor-of-*-same))))

;ffixme get rid of bytes-to-bits using this fact:
(defthm bytes-to-bits-rewrite
  (equal (bytes-to-bits x)
         (ungroup 8 (map-unpackbv 8 1 x)))
  :hints (("Goal" :expand ((:free (a b c) (unpackbv a b c)))
           :in-theory (enable bytes-to-bits byte-to-bits ungroup))))

(defthm all-all-unsigned-byte-p-of-group2
  (implies (all-unsigned-byte-p size x)
           (all-all-unsigned-byte-p size (group2 n x)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable all-all-unsigned-byte-p group2))))

(defthm all-all-unsigned-byte-p-of-group2-back
  (implies (and (equal 0 (mod (len x) n))
                (posp n)
                (all-all-unsigned-byte-p size (group2 n x)))
           (all-unsigned-byte-p size x))
  :hints (("subgoal *1/4" :use (:instance list-split (n n)))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (all-all-unsigned-byte-p group2)
                           (;LIST::EQUAL-APPEND-REDUCTION!
                            ;LIST::EQUAL-APPEND-REDUCTION!-ALT
                            APPEND-OF-TAKE-AND-NTHCDR-2
                            )))))

(defthm all-all-unsigned-byte-p-of-group2-rewrite
  (implies (and (equal 0 (mod (len x) n)) ;handle better
                (posp n))
           (equal (all-all-unsigned-byte-p size (group2 n x))
                  (all-unsigned-byte-p size x)))
  :hints (("Goal" :use (all-all-unsigned-byte-p-of-group2-back all-all-unsigned-byte-p-of-group2)
           :in-theory (disable all-all-unsigned-byte-p-of-group2-back all-all-unsigned-byte-p-of-group2))))

;where should this go?
;i guess defforall could do this...
;true for any mapped predicate..
(defthm all-all-unsigned-byte-p-of-group
  (implies (posp n)
           (equal (all-all-unsigned-byte-p size (group n x))
                  (all-unsigned-byte-p size x)))
  :hints (("subgoal *1/2" :use (:instance list-split))
          ("Goal" :in-theory (e/d (group) (APPEND-OF-TAKE-AND-NTHCDR-2)))))

(defmap map-ungroup (n x) (ungroup n x) :fixed (n))

;think about this
(defthm group2-of-ungroup-helper
  (implies (and (equal 0 (mod (len x) a))
                (equal c (* b a)) ;expensive?  restrict to constants?
                (natp a)
                (posp b))
           (equal (group2 c (ungroup b x))
                  (map-ungroup b (group2 a x))))
  :hints (("Goal" :in-theory (e/d (ungroup map-ungroup group2 posp) ())
           :do-not '(generalize eliminate-destructors))))

;restrict to constants?
(defthm group2-of-ungroup
  (implies (and (equal 0 (mod (len x) (/ c b)))
                (posp (/ c b))
                (posp b))
           (equal (group2 c (ungroup b x))
                  (map-ungroup b (group2 (/ c b) x))))
  :hints (("Goal" :use (:instance group2-of-ungroup-helper (a (/ c b)))
           :in-theory (disable group2-of-ungroup-helper))))

;(in-theory (disable mod-=-0))

;this may be bad if c is not b
(defthm group-of-ungroup
  (implies (and (equal 0 (mod (len x) (/ c b)))
                (posp (/ c b))
                (posp c)
                (posp b))
           (equal (group c (ungroup b x))
                  (map-ungroup b (group (/ c b) x))))
  :hints (("Goal" :in-theory (e/d (posp
                                   equal-of-0-and-mod)
                                  ())
;           :cases ((equal b 1))
           :do-not '(generalize eliminate-destructors))))

;; drop?
(defmap map-map-unpackbv (itemcount itemsize bv-lst) (map-unpackbv itemcount itemsize bv-lst) :fixed (itemcount itemsize))

;; ;; pushing group inside a map- adds one level of map-
;; ;yuck?
(defthm group-of-map-unpackbv
  (implies (posp n)
           (equal (group n (map-unpackbv count size bvs))
                  (map-map-unpackbv count size (group n bvs))))
  :hints (("Goal" :in-theory (enable group map-map-unpackbv))))


;; (defthm all-all-unsigned-byte-p-of-group2
;;   (implies (all-unsigned-byte-p '32 (take (* 16 (floor (len x) 16)) x))
;;            (all-all-unsigned-byte-p '32 (group2 '16 x)))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable all-all-unsigned-byte-p group2))))



;what's going on with having both group and group2?



;; (defthm unsigned-byte-p-of-bitlist-to-bv2
;;   (implies (<= (len x) n)
;;            (equal (unsigned-byte-p n (bitlist-to-bv2 x))
;;                   (natp n)))
;;  :hints (("Goal" :in-theory (enable bitlist-to-bv2))))

;; (defthm bitlist-to-bv2-rewrite
;;   (equal (bitlist-to-bv2 bitlist)
;;          (packbv (len bitlist) 1 bitlist)))

;; ;fffixme gen or automate?!
;; ;is there a simpler way to do this?
;; ;imagine stripping off one map from everything.  this theorem is the mapped version of that one?
(defthm map-packbv-of-map-ungroup-of-map-map-unpackbv
  (implies (and (items-have-len 4 4bv-list) ;drop?
                )
           (equal (map-packbv 32 1 (map-ungroup 8 (map-map-unpackbv 8 1 4bv-list)))
                  (map-packbv 4 8 4bv-list)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (map-packbv map-ungroup map-map-unpackbv
                                       CAR-BECOMES-NTH-OF-0
                                       packbv-opener
                                       CDR-OF-CDR-BECOMES-NTHCDR ;3-cdrs
                                       )
                           (;;LEN-OF-CDR-BETTER
                            CONSP-of-CDR
                            NTH-WHEN-N-IS-ZP
                            ;;;GETBIT-OF-BV-ARRAY-READ                   ;looped!
                            ;GETBIT-OF-BV-ARRAY-READ-HELPER            ;looped
                            ;BVCHOP-OF-NTH-BECOMES-BV-ARRAY-READ
                            ;NATP-WHEN-INTEGERP
                            ;NATP-MEANS-NON-NEG
                            )))))

;i hope this is all we need for the actual proofs (nothing about map-map-xxx??)
;The LHS unpacks bytes into bits and then packs the bits into words.
;The RHS goes straight from bytes to words.
;fixme gen!
;fixme is this the simplest rewrite rule that can be used for this?
(defthm map-packbv-of-group-of-ungroup-of-map-unpackbv
  (implies (and (all-unsigned-byte-p 8 bytes)
                (equal 0 (mod (len bytes) 4)))
           (equal (map-packbv 32 1 (group 32 (ungroup 8 (map-unpackbv 8 1 bytes))))
                  (map-packbv 4 8 (group 4 bytes)))))

(defthm all-all-integerp-of-group2
  (implies (all-integerp msg)
           (all-all-integerp (group2 n msg)))
  :hints (("Goal" :in-theory (enable group2))))

(defthm all-unsigned-byte-p-of-ungroup
  (implies (and (all-all-unsigned-byte-p n x)
                (items-have-len m x))
           (all-unsigned-byte-p n (ungroup m x)))
  :hints (("Goal" :in-theory (enable ungroup))))
