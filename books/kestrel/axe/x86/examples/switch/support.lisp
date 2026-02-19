(in-package "X")

;; todo: file all these rules

(include-book "kestrel/axe/axe-syntax" :dir :system) ; for axe-smt
(include-book "kestrel/bv-lists/bv-array-read-chunk-little" :dir :system)
(include-book "kestrel/bv/bvplus" :dir :system)
(include-book "kestrel/bv/bvmod" :dir :system)
(include-book "kestrel/bv/bvdiv" :dir :system)
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/ceiling-of-lg" :dir :system))
(local (include-book "kestrel/bv/slice" :dir :system))
(local (include-book "kestrel/bv/arith" :dir :system)) ; for expt-hack
(local (include-book "kestrel/bv/rules10" :dir :system))
(local (include-book "kestrel/lists-light/group" :dir :system)) ; for acl2::*-of-/-same-alt
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/axe/rules3" :dir :system))
(local (include-book "kestrel/bv/trim-intro-rules" :dir :system))

;(in-theory (disable bitops::unsigned-byte-p-induct bitops::unsigned-byte-p-ind)) ; yuck

(local (in-theory (disable nth len)))

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
;; reading a chunk of 4 8-bit bytes
(defthm bv-array-read-chunk-little-when-multiple-4-8-helper
  (implies (and (equal 0 (bvchop 2 index)) ; index is a multiple of the chunk size
                (equal 0 (bvchop 2 len)) ; len is a multiple of the chunk size ; gen?
                (equal len (len array)) ; todo
                (< (+ -1 index 4) len) ; entire chunk is in bounds
                (natp index)
                )
           (equal (bv-array-read-chunk-little 4 8 len index array)
                  (bv-array-read 32
                                 (/ len 4)
                                 (slice (- (ceiling-of-lg len) 1)
                                        2
                                        index)
                                 (packbvs-little 4 8 array))))
  :hints (("Goal" :expand ((bvchop 2 (len array))
                           (bvchop 2 index)
;                           (bvlt (ceiling-of-lg len) (bvplus (ceiling-of-lg len) 3 index) len)
 ;                          (bvlt (ceiling-of-lg (len array)) (+ 3 index) (len array))
                           (slice (+ -1 (ceiling-of-lg (len array))) 2 index))
                  :do-not '(generalize eliminate-destructors)
                  :in-theory (e/d (bv-array-read
                                   packbv-little
                                   acl2::packbv-opener
                                   acl2::bvchop-of-sum-cases
                                   bvplus
                                   nfix
                                   ;bvlt
                                   bv-array-read-chunk-little
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

;; SMT version
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
                                   bv-array-read-chunk-little
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

;; (defthm packbv-little-of-1
;;   (equal (packbv-little 1 itemsize items)
;;          (bvchop itemsize (nth (+ -1 (len items)) items)))
;;   :hints (("Goal" :in-theory (enable packbv-little))))

;;    ;move
;; (local (include-book "kestrel/lists-light/len" :dir :system))
;; (defthm packbvs-little-of-1
;;   (implies (equal 1 (len items))
;;            (equal (packbvs-little 1 itemsize items)
;;                   (acl2::bvchop-list itemsize items)))
;;  :hints (("Goal" :in-theory (enable packbvs-little acl2::bvchop-list))))

(local
 (defthmd bv-array-read-chunk-little-when-multiple-helper
   (implies (and (equal 0 (mod index element-count)) ; index is a multiple of the chunk size
                 (equal 0 (mod len element-count)) ; len is a multiple of the chunk size ; gen?
                 (equal len (len array))           ; todo
                 (< (+ -1 index element-count) len) ; entire chunk is in bounds
                 (natp index)
                 (posp element-count)
                 (posp element-size))
            (equal (bv-array-read-chunk-little element-count element-size len index array)
                   (bv-array-read (* element-size element-count)
                                  (/ len element-count)
                                  (/ index element-count) ; slice
                                  (packbvs-little element-count element-size array))))
   :hints (("Goal" :expand (bv-array-read (* element-size element-count)
                                          (* (/ element-count) (len array))
                                          (* (/ element-count) index)
                                          (packbvs-little element-count element-size array))
                   :in-theory (e/d (bv-array-read
                                    acl2::bv-array-read-chunk-little-alt-def)
                                   (acl2::bvcat-equal-rewrite
                                    acl2::bvcat-equal-rewrite-alt
                                    acl2::bvcat-of-nth-arg4 ; todo
                                    acl2::bv-array-read-chunk-little-unroll))))))

;; This can introduce a call of bv-array-read, which the SMT solver knows about.
;; improve name?
;; the bvmod may cause trouble when element-count is not a power of 2
(defthmd acl2::bv-array-read-chunk-little-when-multiple
  (implies (and (syntaxp (and (quotep array) ; because we are going to pack the elements
                              (quotep len)
                              (quotep element-size)
                              (quotep element-count)))
                (equal 0 (bvmod (ceiling-of-lg len) index element-count)) ; index is a multiple of the chunk size, could go to bvchop if power-of-2
                (equal 0 (mod len element-count)) ; len is a multiple of the chunk size ; gets computed
                (equal len (len array)) ; gets computed  ; todo?
                (axe-smt (bvlt (ceiling-of-lg len) index (bvplus (ceiling-of-lg len) (- 1 element-count) len))) ; entire chunk is in bounds
                ;(natp index)
                (unsigned-byte-p (ceiling-of-lg len) index)
                (unsigned-byte-p (ceiling-of-lg len) element-count)
                (posp element-count)
                (posp element-size))
           (equal (bv-array-read-chunk-little element-count element-size len index array)
                  (bv-array-read (* element-size element-count) ; gets computed
                                 (/ len element-count) ; gets computed
                                 (bvdiv (ceiling-of-lg len) index element-count) ; could go got slice if power-of-2
                                 (packbvs-little element-count element-size array) ; gets computed!
                                 )))
  :hints (("Goal" :use (:instance bv-array-read-chunk-little-when-multiple-helper)
                  :cases ((equal (len array) element-count)
                          (< (len array) element-count))
                  :in-theory (enable bvmod bvdiv bvlt bvplus acl2::floor-when-mod-0))))

;;move
(defthm mod-of-+-of-mod-arg2+
  (implies (and (rationalp x1)
                (rationalp x2)
                (rationalp x3)
                (rationalp y)
                (< 0 y))
           (equal (mod (+ x1 (mod x2 y) x3) y)
                  (mod (+ x1 x2 x3) y)))
  :hints (("Goal" :use (:instance acl2::mod-of-+-of-mod-arg2
                                  (x1 (+ x1 x3)))
                  :in-theory (disable acl2::mod-of-+-of-mod-arg2))))

(defthm mod-of-+-of-mod-arg3
  (implies (and (rationalp x1)
                (rationalp x2)
                (rationalp x3)
                (rationalp y)
                (< 0 y))
           (equal (mod (+ x1 x3 (mod x2 y)) y)
                  (mod (+ x1 x3 x2) y)))
  :hints (("Goal" :use (:instance acl2::mod-of-+-of-mod-arg2
                                  (x1 (+ x1 x3)))
                  :in-theory (disable acl2::mod-of-+-of-mod-arg2))))

(defthm mod-of-+-subst-constant-arg2+
  (implies (and (syntaxp (not (quotep x))) ; prevent loops
                (equal k (mod x z))
                (syntaxp (quotep k))
                (rationalp x)
                (rationalp w)
                (rationalp y)
                (rationalp z)
                (< 0 z))
           (equal (mod (+ y x w) z)
                  (mod (+ y k w) z))))

(defthm bvmod-of-bvplus-when-multiple-arg1
  (implies (and (equal 0 (bvmod size x z))
                (equal 0 (mod (expt 2 size) (bvchop size z))) ; may often get computed ; or say that the bvplus doesn't overflow
                (integerp x)
                (integerp y)
                (integerp z)
                (bvlt size 0 z))
           (equal (bvmod size (bvplus size x y) z)
                  (bvmod size y z)))
  :hints (("Goal" :in-theory (enable bvmod bvplus acl2::bvchop-of-sum-cases bvlt))))

(defthm bvmod-of-bvplus-when-multiple-arg2
  (implies (and (equal 0 (bvmod size y z))
                (equal 0 (mod (expt 2 size) (bvchop size z))) ; may often get computed ; or say that the bvplus doesn't overflow
                (integerp x)
                (integerp y)
                (integerp z)
                (bvlt size 0 z))
           (equal (bvmod size (bvplus size x y) z)
                  (bvmod size x z)))
  :hints (("Goal" :in-theory (enable bvmod bvplus acl2::bvchop-of-sum-cases bvlt))))
