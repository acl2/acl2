(in-package "X")

(include-book "kestrel/axe/x86/unroller" :dir :system) ; todo: reduce, or file all these rules
(include-book "kestrel/bv-lists/map-bvplus-val" :dir :system)

(in-theory (disable bitops::unsigned-byte-p-induct bitops::unsigned-byte-p-ind)) ; yuck

(defthm *-of-4-and-slice-when-multiple
  (implies (and (equal 0 (mod index 4))
                (natp n))
           (equal (* 4 (slice n 2 index))
                  (bvchop (+ 1 n) index))))

(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))

;todo: gen
(defthm ceiling-of-lg-of-*-of-1/4
  (implies (and (equal 0 (mod x 4))
                (posp x))
           (equal (ceiling-of-lg (* 1/4 x))
                  (+ -2 (ceiling-of-lg x))))
  :hints (("Goal" :use (:instance acl2::ceiling-of-lg-of-*-of-expt-of-- (i 2))
                  :in-theory (disable acl2::ceiling-of-lg-of-*-of-expt-of--))))

(defthm integerp-of-*-of-1/4
  (equal (integerp (* 1/4 x))
         (equal 0 (mod x 4))))

(defthm *-of-4-and-logtail-of-2
  (implies (and (equal 0 (mod index 4))
                (natp index))
           (equal (* 4 (logtail 2 index))
                  index))
  :hints (("Goal" :in-theory (enable logtail))))

;todo: gen!
(defthm bv-array-read-chunk-little-when-multiple-4-8-helper
  (implies (and (equal 0 (bvchop 2 index)) ; index is a multiple of the chunk size
                (equal 0 (bvchop 2 len))
                (equal len (len array)) ; todo
                (< (+ -1 index 4) len)
                (natp index)
                )
           (equal (bv-array-read-chunk-little 4 8 len index array)
                  (bv-array-read 32
                                 (/ len 4)
                                 (slice (- (ceiling-of-lg len) 1)
                                        2
                                        index)
                                 (packbvs-little 4 8 array))))
  :hints (("Goal" :expand ( ;(slice 6 2 index)
                           (bvchop 2 (len array))
                           (bvchop 2 index)
;                           (bvlt (ceiling-of-lg len) (bvplus (ceiling-of-lg len) 3 index) len)
 ;                          (bvlt (ceiling-of-lg (len array)) (+ 3 index) (len array))
                           (slice (+ -1 (ceiling-of-lg (len array)))
                         2 index))
                  :do-not '(generalize eliminate-destructors)
                  :in-theory (e/d (bv-array-read
                                   packbv-little
                                   acl2::packbv-opener
                                   acl2::bvchop-of-sum-cases
                                   bvplus
                                   nfix
                                   ;bvlt
                                   )
                                  (acl2::bvcat-of-nth-arg4 ;loop
                                   acl2::bvcat-of-nth-arg2 ; loop!
                                   acl2::equal-of-constant-and-getbit-extend ; looped
                                   ;acl2::bvchop-top-bit-cases ; looped
                                   )))))

;gen
(defthm bv-array-read-chunk-little-when-multiple-4-8
  (implies (and (equal 0 (bvchop 2 index)) ; index is a multiple of the chunk size
                (equal 0 (bvchop 2 len)) ; len is a multiple of the chunk size
                (equal len (len array))
                (unsigned-byte-p (ceiling-of-lg len) index) ; we have another rule to trim it
                (bvlt (ceiling-of-lg len) index (bvplus (ceiling-of-lg len) -3 len))
                ;(unsigned-byte-p (ceiling-of-lg len) (+ 3 index))
                ;(bvlt (ceiling-of-lg len) (bvplus (ceiling-of-lg len) 3 index) len)
                (natp index)
                (<= 4 (len array)) ;drop or gen?
                )
           (equal (bv-array-read-chunk-little 4 8 len index array)
                  (bv-array-read 32
                                 (/ len 4)
                                 (slice (- (ceiling-of-lg len) 1)
                                        2
                                        index)
                                 (packbvs-little 4 8 array))))
  :hints (("Goal" :use bv-array-read-chunk-little-when-multiple-4-8-helper
                  :expand (bvplus (ceiling-of-lg (len array)) -3 (len array))
                  :in-theory (e/d (bvlt acl2::bvchop-of-sum-cases)
                                  (bv-array-read-chunk-little-when-multiple-4-8-helper)))))

(defthm acl2::bv-array-read-chunk-little-when-multiple-4-8-smt
  (implies (and (equal 0 (bvchop 2 index)) ; index is a multiple of the chunk size
                (equal 0 (bvchop 2 len)) ; len is a multiple of the chunk size
                (equal len (len array))
                (unsigned-byte-p (ceiling-of-lg len) index)
                (axe-smt (bvlt (ceiling-of-lg len) index (bvplus (ceiling-of-lg len) -3 len)))
                ;(unsigned-byte-p (ceiling-of-lg len) (+ 3 index))
                ;(bvlt (ceiling-of-lg len) (bvplus (ceiling-of-lg len) 3 index) len)
                (natp index)
                (<= 4 (len array))
                )
           (equal (bv-array-read-chunk-little 4 8 len index array)
                  (bv-array-read 32
                                 (/ len 4)
                                 (slice (- (ceiling-of-lg len) 1)
                                        2
                                        index)
                                 (packbvs-little 4 8 array))))
  :hints (("Goal" :use bv-array-read-chunk-little-when-multiple-4-8
                  :in-theory (disable bv-array-read-chunk-little-when-multiple-4-8))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; same as above, but now do it for 8 byte chunks:

;todo: gen
(defthm ceiling-of-lg-of-*-of-1/8
  (implies (and (equal 0 (mod x 8))
                (posp x))
           (equal (ceiling-of-lg (* 1/8 x))
                  (+ -3 (ceiling-of-lg x))))
  :hints (("Goal" :use (:instance acl2::ceiling-of-lg-of-*-of-expt-of-- (i 3))
                  :in-theory (disable acl2::ceiling-of-lg-of-*-of-expt-of--))))

(defthm integerp-of-*-of-1/8
  (equal (integerp (* 1/8 x))
         (equal 0 (mod x 8))))

(defthm *-of-8-and-logtail-of-3
  (implies (and (equal 0 (mod index 8))
                (natp index))
           (equal (* 8 (logtail 3 index))
                  index))
  :hints (("Goal" :in-theory (enable logtail))))

;todo: gen!
(defthm bv-array-read-chunk-little-when-multiple-8-8-helper ; todo: rename the other
  (implies (and (equal 0 (bvchop 3 index)) ; index is a multiple of the chunk size
                (equal 0 (bvchop 3 len)) ; len is a multiple of the chunk size
                (equal len (len array)) ; todo
                (< (+ -1 index 8) len)
                (natp index))
           (equal (bv-array-read-chunk-little 8 8 len index array)
                  (bv-array-read 64
                                 (/ len 8)
                                 (slice (- (ceiling-of-lg len) 1)
                                        3
                                        index)
                                 (packbvs-little 8 8 array))))
  :hints (("Goal" :expand ((bvchop 3 (len array))
                           (bvchop 3 index)
                           ;(bvlt (ceiling-of-lg len) (bvplus (ceiling-of-lg len) 3 index) len)
                           ;(bvlt (ceiling-of-lg (len array)) (+ 3 index) (len array))
                           (slice (+ -1 (ceiling-of-lg (len array))) 3 index))
                  :do-not '(generalize eliminate-destructors)
                  :in-theory (e/d (bv-array-read
                                   packbv-little
                                   acl2::packbv-opener
                                   acl2::bvchop-of-sum-cases
                                   bvplus
                                   nfix
                                   ;bvlt
                                   )
                                  (acl2::bvcat-of-nth-arg4 ;loop
                                   acl2::bvcat-of-nth-arg2 ; loop!
                                   acl2::equal-of-constant-and-getbit-extend ; looped
                                   ;acl2::bvchop-top-bit-cases ; looped
                                   )))))

;gen
(defthm bv-array-read-chunk-little-when-multiple-8-8
  (implies (and (equal 0 (bvchop 3 index)) ; index is a multiple of the chunk size
                (equal 0 (bvchop 3 len)) ; len is a multiple of the chunk size
                (equal len (len array))
                (unsigned-byte-p (ceiling-of-lg len) index) ; we have another rule to trim it
                (bvlt (ceiling-of-lg len) index (bvplus (ceiling-of-lg len) -7 len))
                (natp index)
                (<= 8 (len array)) ;drop or gen?
                )
           (equal (bv-array-read-chunk-little 8 8 len index array)
                  (bv-array-read 64
                                 (/ len 8)
                                 (slice (- (ceiling-of-lg len) 1)
                                        3
                                        index)
                                 (packbvs-little 8 8 array))))
  :hints (("Goal" :use bv-array-read-chunk-little-when-multiple-8-8-helper
                  :expand (bvplus (ceiling-of-lg (len array)) -7 (len array))
                  :in-theory (e/d (bvlt acl2::bvchop-of-sum-cases)
                                  (bv-array-read-chunk-little-when-multiple-8-8-helper
                                   bv-array-read-chunk-little-when-multiple-4-8-helper ; fires in this case too?
                                   acl2::bvcat-equal-rewrite-alt)))))

(in-theory (disable acl2::bv-array-read-chunk-little-unroll))

(defthm acl2::bv-array-read-chunk-little-when-multiple-8-8-smt
  (implies (and (equal 0 (bvchop 3 index)) ; index is a multiple of the chunk size
                (equal 0 (bvchop 3 len)) ; len is a multiple of the chunk size
                (equal len (len array))
                (unsigned-byte-p (ceiling-of-lg len) index)
                (axe-smt (bvlt (ceiling-of-lg len) index (bvplus (ceiling-of-lg len) -7 len)))
                (natp index)
                (<= 8 (len array))
                )
           (equal (bv-array-read-chunk-little 8 8 len index array)
                  (bv-array-read 64
                                 (/ len 8)
                                 (slice (- (ceiling-of-lg len) 1)
                                        3
                                        index)
                                 (packbvs-little 8 8 array))))
  :hints (("Goal" :use bv-array-read-chunk-little-when-multiple-8-8
                  :in-theory (disable bv-array-read-chunk-little-when-multiple-8-8))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; since the bvcat has low zeros, the low bits of k can't cause carry
;gen!  and don't require args to be trimmed?
(defthm acl2::slice-of-bvplus-of-bvcat-special
  (equal (slice 11 2 (bvplus 12 k (bvcat 10 val 2 0)))
         (bvplus 10 (slice 11 2 k) (bvchop 10 val)))
  :hints (("Goal" :in-theory (enable ;bvplus acl2::bvchop-of-sum-cases
                              acl2::slice-of-bvplus-cases))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: to be more general, support splitting when the bv-array-read is not the entire new rip term.
;; approach: create an identify function that causes things to be split (and ifs to be lifted)? and propagate it downward through a non-constant set-rip argument when there is something to split.
(defthm set-rip-of-bv-array-read-split-cases
  (implies (and (syntaxp (quotep data))
                (< len 20) ; todo: how many cases do we want to allow?
                ;; (unsigned-byte-p (ceiling-of-lg len) index)
                (bvle (ceiling-of-lg len) index (+ -1 len)) ; todo?
                (posp len)
                (natp index))
           (equal (set-rip (bv-array-read size len index data) x86)
                  ;; bv-array-read-cases here will then get unrolled:
                  (set-rip (bv-array-read-cases (bvchop (ceiling-of-lg len) (+ -1 len)) size len index data) x86)))
  :hints (("Goal" :in-theory (enable acl2::bv-array-read-becomes-bv-array-read-cases))))

(defthm set-rip-of-bv-array-read-split-cases-smt
  (implies (and (syntaxp (quotep data))
                (< len 20) ; todo: how many cases do we want to allow?
                ;; (unsigned-byte-p (ceiling-of-lg len) index)
                (axe-smt (bvle (ceiling-of-lg len) index (+ -1 len))) ; todo?
                (posp len)
                (natp index))
           (equal (set-rip (bv-array-read size len index data) x86)
                  ;; bv-array-read-cases here will then get unrolled:
                  (set-rip (bv-array-read-cases (bvchop (ceiling-of-lg len) (+ -1 len)) size len index data) x86)))
  :hints (("Goal" :in-theory (enable acl2::bv-array-read-becomes-bv-array-read-cases))))

(defthm set-rip-of-bvif-split
  (equal (set-rip (bvif size test tp ep) x86)
         (if test
             (set-rip (bvchop size tp) x86)
           (set-rip (bvchop size ep) x86))))
