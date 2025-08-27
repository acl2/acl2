; Read and write operations for 32-bit RISC-V code reasoning
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R")

;; TODO: Consider adding 32 to the names of the functions in this file (or
;; making separate packages for 32-bit and 64-bit RISC-V proofs).  Note that
;; the functions defined in this file are analogous to the functions used by
;; Axe for x86 reasoning (except for the memory size).

(include-book "portcullis")
(include-book "kestrel/risc-v/specialized/states32" :dir :system)
(include-book "kestrel/memory/memory32" :dir :system)
(include-book "risc-v-rules")
(include-book "support") ; for write32-mem-ubyte32-lendian-alt-def
(include-book "kestrel/bv/bvcat-def" :dir :system)
(include-book "kestrel/bv-lists/bv-array-read" :dir :system)
(include-book "kestrel/bv-lists/bv-array-read-chunk-little" :dir :system)
;(local (include-book "kestrel/bv/logapp" :dir :system)) ; reduce
;(local (include-book "kestrel/lists-light/nth" :dir :system))
;(local (include-book "kestrel/lists-light/take" :dir :system))
;(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
;(local (include-book "kestrel/arithmetic-light/ash" :dir :system))
;(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/bv/logand" :dir :system))
(local (include-book "kestrel/bv/intro" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system))
;(local (include-book "kestrel/lists-light/update-nth" :dir :system))
(local (include-book "kestrel/bv/ash" :dir :system))
(local (include-book "kestrel/bv/bvplus" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/bv/rules3" :dir :system)) ; reduce?
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
;(local (include-book "kestrel/arithmetic-light/top" :dir :system))
(local (include-book "kestrel/arithmetic-light/lg" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
;(local (include-book "kestrel/arithmetic-light/times-and-divide" :dir :system))
;(local (include-book "kestrel/bv/top" :dir :system)) ; reduce

;; Disable bad rules that come in via fty via risc-v:
(in-theory (disable acl2::reverse-removal acl2::revappend-removal))

;move
(local
  (encapsulate ()
    (local (include-book "kestrel/arithmetic-light/times" :dir :system))
    (defthm unsigned-byte-p-of-+-of-*-of-expt
      (implies (and (unsigned-byte-p m x)
                    (unsigned-byte-p (- n m) y)
                    (posp n))
               (unsigned-byte-p n (+ x (* (expt 2 m) y))))
      :hints (("Goal" :in-theory (enable unsigned-byte-p acl2::expt-of-+))))))

(defthm unsigned-byte-p-of-+-of-*-of-power-of-2
  (implies (and (power-of-2p k)
                (unsigned-byte-p (lg k) x)
                (unsigned-byte-p (- n (lg k)) y)
                (posp n))
           (unsigned-byte-p n (+ x (* k y))))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-+-of-*-of-expt
                                  (m (lg k)))
           :in-theory (disable unsigned-byte-p-of-+-of-*-of-expt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Reads the byte at address ADDR.
(defund read-byte (addr stat)
  (declare (xargs :guard (and (unsigned-byte-p 32 addr)
                              (stat32ip stat))))
  (read32-mem-ubyte8 addr stat))

(defthm read-byte-when-not-integerp
  (implies (not (integerp addr))
           (equal (read-byte addr stat)
                  (read-byte 0 stat)))
  :hints (("Goal" :in-theory (enable read-byte read32-mem-ubyte8))))

; maybe drop the arg1 from the name
(defthm read-byte-of-bvchop-arg1
  (equal (read-byte (bvchop 32 addr) stat)
         (read-byte addr stat))
  :hints (("Goal" :in-theory (enable read-byte read32-mem-ubyte8))))

(defthm read-byte-of-constant-arg2
  (implies (and (syntaxp (quotep addr))
                (not (unsigned-byte-p 32 addr)))
           (equal (read-byte addr stat)
                  (read-byte (bvchop 32 addr) stat)))
  :hints (("Goal" :in-theory (enable read-byte
                                     read32-mem-ubyte8 ; todo
                                     ))))

;rename to have 8 in the name?
(defthmd unsigned-byte-p-of-read-byte-simple
  (unsigned-byte-p 8 (read-byte addr stat))
  :hints (("Goal" :in-theory (enable read-byte))))

(defthm unsigned-byte-p-of-read-byte
  (implies (<= 8 size)
           (equal (unsigned-byte-p size (read-byte addr stat))
                  (natp size)))
  :hints (("Goal" :use unsigned-byte-p-of-read-byte-simple
           :cases ((integerp size))
           :in-theory (disable  unsigned-byte-p-of-read-byte-simple))))

(defthm <=-of-read-byte-linear
  (<= (read-byte addr stat) 255)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable read-byte))))


(defthmd read-byte-of-+
  (implies (and (integerp x)
                (integerp y))
           (equal (read-byte (+ x y) stat)
                  (read-byte (bvplus 32 x y) stat)))
  :hints (("Goal" :in-theory (e/d (read-byte read32-mem-ubyte8 bvplus)
                                  (acl2::bvplus-of-+-arg3
                                   disjoint-regions32p-of-+-arg4
                                   in-region32p-of-+-arg3)))))

;rename
;todo: same as read-byte-equal-when-bvchops-equal?
(defthmd read-byte-when-bvchops-agree
  (implies (equal (bvchop 32 addr)
                  (bvchop 32 addr2))
           (equal (equal (read-byte addr stat)
                         (read-byte addr2 stat))
                  t))
  :hints (("Goal" :in-theory (enable read-byte
                                     read32-mem-ubyte8 ; todo
                                     ))))

;or do we want to introduce bvchop?
(defthm read-byte-of-+-of-bvchop-arg1
  (implies (and (integerp x)
                (integerp y))
           (equal (read-byte (+ x (bvchop 32 y)) stat)
                  (read-byte (+ x y) stat)))
  :hints (("Goal" :use ((:instance read-byte-of-bvchop-arg1 (addr (+ x (bvchop 32 y))))
                        (:instance read-byte-of-bvchop-arg1 (addr (+ x y))))
           :in-theory (disable read-byte-of-bvchop-arg1))))

;or do we want to introduce bvchop?
(defthm read-byte-of-+-of-bvchop-arg2
  (implies (and (integerp x)
                (integerp y))
           (equal (read-byte (+ (bvchop 32 y) x) stat)
                  (read-byte (+ y x) stat)))
  :hints (("Goal" :use ((:instance read-byte-of-bvchop-arg1 (addr (+ (bvchop 32 y) x)))
                        (:instance read-byte-of-bvchop-arg1 (addr (+ x y))))
           :in-theory (disable read-byte-of-bvchop-arg1))))

;or do we want to introduce bvchop?
(defthm read-byte-of-+-of-bvchop-arg2+
  (implies (and (integerp x)
                (integerp y))
           (equal (read-byte (+ x (bvchop 32 y) z) stat)
                  (read-byte (+ x y z) stat)))
  :hints (("Goal" :use ((:instance read-byte-of-bvchop-arg1 (addr (+ x (bvchop 32 y) z)))
                        (:instance read-byte-of-bvchop-arg1 (addr (+ x y z))))
           :in-theory (disable read-byte-of-bvchop-arg1))))

(defthm bvchop-of-+-of-bvimunus-arg3
  (implies  (and (integerp x)
                 (integerp y)
                 (integerp z))
            (equal (bvchop 32 (+ x y (bvuminus 32 z)))
                   (bvchop 32 (+ x y (- z)))))
  :hints (("Goal" :in-theory (enable bvuminus))))

;or do we want to introduce bvchop?
(defthm read-byte-of-+-of-bvuminus-arg3
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (read-byte (+ x y (bvuminus 32 z)) stat)
                  (read-byte (+ y x (- z)) stat)))
  :hints (("Goal" :use ((:instance read-byte-of-bvchop-arg1 (addr (+ x y (bvuminus 32 z))))
                        (:instance read-byte-of-bvchop-arg1 (addr (+ y x (- z)))))
           :in-theory (e/d (;bvuminus
                            )
                           (read-byte-of-bvchop-arg1)))))

(defthm read-byte-of-+-subst-constant-arg1
  (implies (and (equal (bvchop 32 x) freek)
                (syntaxp (and (quotep freek)
                              ;; avoid loops:
                              (not (quotep x))))
                (integerp x)
                (integerp y))
           (equal (read-byte (+ x y) stat)
                  (read-byte (+ freek y) stat)))
  :hints (("Goal" :in-theory (enable read-byte-of-+))))

(defthm read-byte-of-+-subst-constant-arg2
  (implies (and (equal (bvchop 32 y) freek)
                (syntaxp (and (quotep freek)
                              (not (quotep y))))
                (integerp x)
                (integerp y))
           (equal (read-byte (+ x y) stat)
                  (read-byte (+ x freek) stat)))
  :hints (("Goal" :in-theory (enable read-byte-of-+))))


(defthmd read32-mem-ubyte8-becomes-read-byte
  (equal (read32-mem-ubyte8 addr stat)
         (read-byte addr stat))
  :hints (("Goal" :in-theory (enable read32-mem-ubyte8 read-byte))))

(theory-invariant (incompatible (:rewrite read32-mem-ubyte8-redef) (:definition read-byte )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Read N bytes, starting at ADDR.  Unlike read, this returns a list.
;; TODO: Consider putting the N parameter first
(defund read-bytes (addr n stat)
  (declare (xargs :guard (and (unsigned-byte-p 32 addr)
                              (natp n)
                              (stat32ip stat))))
  (if (zp n)
      nil
    (cons (read-byte addr stat)
          (read-bytes (bvplus 32 1 addr) (+ -1 n) stat))))

(local
  ;rename
  (defun indf (n1 ad1 ad2 stat)
    (if (zp n1)
        (list n1 ad1 ad2 stat)
      (indf (+ -1 n1)
            (+ -1 ad1)
            (+ 1 ad2)
            stat))))

(defthm len-of-read-bytes
  (equal (len (read-bytes addr n stat))
         (nfix n))
  :hints (("Goal" :in-theory (enable read-bytes))))

(defthm bv-array-read-of-read-bytes-helper
  (implies (and (< ad1 len) ;(force (< ad1 len))
                (natp ad1)
                (natp len)
                (integerp ad2))
           (equal (bv-array-read 8 len ad1 (read-bytes ad2 len stat))
                  (read-byte (bvplus 32 ad1 ad2) stat)))
  :hints (("Goal" :induct (indf len ad1 ad2 stat) ; (read-bytes ad2 len stat)
           :expand (read-bytes ad2 len stat)
           ;(read-induct-two-sizes len ad1 ad2 stat)
           :in-theory (enable read-bytes read-byte-of-+
                              acl2::bvplus-of-+-arg2
                              acl2::bvplus-of-+-arg3))))

;;  ; todo: different from the version for x86
;; (defthm bv-array-read-of-read-bytes
;;   (implies (and (natp ad1)
;;                 (natp len)
;;                 (integerp ad2))
;;            (equal (bv-array-read 8 len ad1 (read-bytes ad2 len stat))
;;                   (if (< ad1 len)
;;                       (read-byte (bvplus 32 ad1 ad2) stat)
;;                     0)))
;;   :hints (("Goal" :use (:instance bv-array-read-of-read-bytes-helper)
;;            :in-theory (disable bv-array-read-of-read-bytes-helper))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Reads an N-byte chunk starting at ADDR (in little endian fashion).
;; Unlike read-bytes, this returns the value as a bit-vector.
(defund read (n addr stat)
  (declare (xargs :guard (and (natp n)
                              (unsigned-byte-p 32 addr)
                              (stat32ip stat))))
  (if (zp n)
      0
    (let ((addr (mbe :logic (ifix addr) :exec addr)) ; treats non-integer address as 0
          )
      (bvcat (* 8 (- n 1))
             (read (- n 1) (bvplus 32 1 addr) stat)
             8
             (read-byte addr stat)))))

;; includes the n=0 case
(defthm read-when-not-posp-cheap
  (implies (not (posp n))
           (equal (read n addr stat)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable read))))

(defthmd integerp-of-read (integerp (read n addr stat)))
(defthmd natp-of-read (natp (read n addr stat)))

(defthm read-when-not-integerp
  (implies (not (integerp addr))
           (equal (read n addr stat)
                  (read n 0 stat)))
  :hints (("Goal" :in-theory (enable read))))

(defthm unsigned-byte-p-of-read
  (implies (<= (* n 8) size)
           (equal (unsigned-byte-p size (read n addr stat))
                  (natp size)))
  :hints (("Goal" :in-theory (enable read))))

(defthm not-equal-of-constant-and-read
  (implies (and (syntaxp (quotep k))
                (not (unsigned-byte-p (* n 8) k))
                (natp n))
           (not (equal k (read n addr stat))))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-read (size (* n 8)))
           :in-theory (disable unsigned-byte-p-of-read))))

(defthmd not-equal-of-read-and-constant
  (implies (and (syntaxp (quotep k))
                (not (unsigned-byte-p (* n 8) k))
                (natp n))
           (not (equal (read n addr stat) k))))

(defthm <-of-read
  (implies (and (syntaxp (quotep k))
                (<= (expt 2 (* 8 n)) k)
                (natp n)
                (integerp k))
           (< (read n addr stat) k))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-read (size (* n 8)))
           :in-theory (disable unsigned-byte-p-of-read))))


(defthm read-of-constant-arg2
  (implies (and (syntaxp (quotep addr))
                (not (unsigned-byte-p 32 addr)))
           (equal (read n addr stat)
                  (read n (bvchop 32 addr) stat)))
  :hints (("Goal" :in-theory (enable read))))

(defthm ash-becomes-bvcat-when-byte-p
  (implies (and (unsigned-byte-p 8 x)
                (natp amt))
           (equal (ash x amt)
                  (bvcat (+ 8 amt) x amt 0)))
  :hints (("Goal" :use (:instance acl2::ash-becomes-bvcat (x x) (amt amt) (xsize 8))
           :in-theory (disable acl2::ash-becomes-bvcat))))

(defthmd +-of-bvcat-combine
  (implies (unsigned-byte-p low x)
           (equal (+ x (bvcat high highval low 0))
                  (bvcat high highval low x)))
  :hints (("Goal" :in-theory (enable bvcat logapp))))

(defthmd +-of-bvcat-combine-extra
  (implies (unsigned-byte-p low x)
           (equal (+ x (bvcat high highval low 0) rest)
                  (+ (bvcat high highval low x) rest)))
  :hints (("Goal" :in-theory (enable bvcat logapp))))

(local (include-book "kestrel/bv/ash" :dir :system))
(defthm read32-mem-ubyte32-lendian-redef
  (implies (integerp addr)
           (equal (read32-mem-ubyte32-lendian addr stat)
                  (bvcat2 8 (read-byte (bvplus 32 3 addr) stat)
                          8 (read-byte (bvplus 32 2 addr) stat)
                          8 (read-byte (bvplus 32 1 addr) stat)
                          8 (read-byte addr stat))))
  :hints (("Goal" :in-theory (e/d (read32-mem-ubyte32-lendian
                                   bvcat logapp
                                   ;ash
                                   unsigned-byte-p
                                   read32-mem-ubyte8-becomes-read-byte
                                    read-byte-of-+)
                                  (acl2::bvcat-equal-rewrite
                                   acl2::bvcat-equal-rewrite-alt
                                   acl2::logapp-equal-rewrite
                                   acl2::logapp-equal-rewrite-8
                                   acl2::logapp-equal-rewrite-16
                                   acl2::logapp-equal-rewrite-24)))))

(defthm read32-mem-ubyte32-lendian-becomes-read
  (implies (integerp addr)
           (equal (read32-mem-ubyte32-lendian addr stat)
                  (read 4 addr stat)))
  :hints (("Goal" :expand ((:free (n addr) (read n addr stat)))
           :in-theory (enable read))))

(defthmd read-of-+
  (implies (and (integerp x)
                (integerp y))
           (equal (read n (+ x y) stat)
                  (read n (bvplus 32 x y) stat)))
  :hints (("Goal" :in-theory (enable read read-byte-of-+
                                     acl2::bvplus-of-+-arg2
                                     acl2::bvplus-of-+-arg3))))

(defthmd read-becomes-read-byte
  (equal (read 1 addr stat)
         (read-byte addr stat))
  :hints (("Goal" :in-theory (enable read))))

(defthmd read-byte-becomes-read
  (equal (read-byte addr stat)
         (read 1 addr stat))
  :hints (("Goal" :in-theory (enable read))))



(local
  (defun bvchop-of-read-induct (numbits numbytes addr)
    (if (zp numbytes)
        (list numbits numbytes addr)
      (bvchop-of-read-induct (+ -8 numbits) (+ -1 numbytes) (+ 1 (ifix addr))))))

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))

(defthm bvchop-of-read
  (implies (and (equal 0 (mod numbits 8))
                (natp numbits)
                (natp numbytes))
           (equal (bvchop numbits (read numbytes addr stat))
                  (if (< numbits (* 8 numbytes))
                      (read (/ numbits 8) addr stat)
                    (read numbytes addr stat))))
  :hints (("Goal" :induct (bvchop-of-read-induct numbits numbytes addr)
           :expand (read numbytes addr stat)
           :in-theory (enable READ read-of-+))))

(local
  (defun read-high-low-induct (n addr stat high low)
    (if (zp n)
        (mv n addr stat high low)
      (read-high-low-induct (- n 1) (+ 1 addr) stat (+ -8 high) (+ -8 low)))))

;rename since used for a read proof as well
;add -alt to name?
(local
  (defun double-write-induct-two-addrs (n addr addr2 val stat)
    (if (zp n)
        (list n addr addr2 val stat)
      (double-write-induct-two-addrs (+ -1 n)
                                     (+ 1 addr)
                                     (+ 1 addr2)
                                     (logtail 8 val)
                                     stat))))

;rename
(local
  (defthmd read-when-bvchops-agree-helper
    (implies (and (equal (bvchop 32 addr)
                         (bvchop 32 addr2))
                  (integerp addr)
                  (integerp addr2))
             (equal (equal (read n addr stat)
                           (read n addr2 stat))
                    t))
    :hints (("Goal" :induct (double-write-induct-two-addrs N ADDR addr2 VAL STAT)
             :in-theory (enable read
                                acl2::bvchop-of-sum-cases
                                read-byte-when-bvchops-agree
                                ;bvplus
                                )))))

(defthmd read-when-bvchops-agree
  (implies (equal (bvchop 32 addr)
                  (bvchop 32 addr2))
           (equal (equal (read n addr stat)
                         (read n addr2 stat))
                  t))
  :hints (("Goal" :in-theory (enable ifix)
           :use (:instance read-when-bvchops-agree-helper
                           (addr (ifix addr))
                           (addr2 (ifix addr2))))))

(defthm read-of-bvchop-32
  (equal (read n (bvchop 32 addr) stat)
         (read n addr stat))
  :hints (("Goal" :in-theory (enable read-when-bvchops-agree))))

(local (include-book "kestrel/bv/arith" :dir :system))

;for whole bytes
;move up
(defthm slice-of-read
  (implies (and ;; (syntaxp (and (quotep low)
                ;;               (quotep high)))
                (equal 0 (mod low 8)) ; low bit of some byte
                ;;(equal 7 (mod high 8)) ; high bit of some byte
                (integerp (/ (+ high 1) 8))
                (< high (* 8 n))
;                (<= low high)
                (natp low)
                (natp high)
                (natp n)
                (integerp addr))
           (equal (slice high low (read n addr stat))
                  (read (/ (+ 1 high (- low)) 8) ; number if bytes to read
                        (+ (/ low 8) ; number of bytes we skip
                           addr)
                        stat)))
  :hints (("subgoal *1/2" :cases ((< high 7)))
          ("Goal" :induct (read-high-low-induct n addr stat high low)
           :do-not '(generalize eliminate-destructors)
           :expand ((read n addr stat)
                    (read (+ 1/8 (* 1/8 high)) addr stat))
           :in-theory (e/d (read acl2::integerp-squeeze read-of-+
                                 )
                           (acl2::<=-of-*-and-*-same-linear
                            acl2::<=-of-*-and-*-same-alt-linear
                            ;; these seemed to add stuff to the goal itself?!  why?
                            acl2::<-of-*-and-*-same-forward-1
                            acl2::<-of-*-and-*-same-forward-2
                            acl2::<-of-*-and-*-same-forward-3
                            acl2::<-of-*-and-*-same-forward-4)))))


(local (include-book "kestrel/arithmetic-light/limit-expt" :dir :system))

(defthmd bvplus-helper
  (implies (and (< x n2)
                (unsigned-byte-p 32 n2) ; gen?
                (unsigned-byte-p 32 x) ; if we keep this, simplify the rhs
                ;(integerp x)
                (natp n2))
           (equal (< (bvplus 32 1 x) n2)
                  (not (and ;(unsigned-byte-p 32 n2)
                         (equal (bvchop 32 x) (bvminus 32 n2 1))
                         (not (equal (bvchop 32 x) (+ -1 (expt 2 32))))))))
  :hints (("Goal" :in-theory (e/d (bvplus acl2::bvchop-of-sum-cases)
                                  (acl2::bvplus-of-+-arg3
                                   disjoint-regions32p-of-+-arg4
                                   in-region32p-of-+-arg3)))))

(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(defthm read-when-equal-of-read-bytes-and-subregion32p
  (implies (and (equal bytes (read-bytes ad2 n2 stat)) ; lots of free vars here ; note that refine-assumptions... puts the constant first
                (subregion32p n1 ad1 n2 ad2)
                ;; (syntaxp (quotep bytes)) ; maybe uncomment
                ;; (unsigned-byte-p 32 n1)
                (natp n1)
                (< n1 (expt 2 32)) ; allow equal?
                (unsigned-byte-p 32 n2) ; allow 2^32?
                (unsigned-byte-p 32 n1) ; todo
                (integerp ad1) ; todo
                (integerp ad2) ; todo
                (unsigned-byte-p 32 ad1) ; drop?
                (unsigned-byte-p 32 ad2) ; drop?
                )
           (equal (read n1 ad1 stat)
                  (bv-array-read-chunk-little n1 8 (len bytes) (bvminus 32 ad1 ad2) bytes)))
  :hints (("Goal"
           :do-not '(generalize eliminate-destructors)
;           :expand (read n1 ad1 stat)
           :expand ((read n1 ad1 stat)
                    (bv-array-read-chunk-little n1 8 n2 ad1 (read-bytes 0 n2 stat))
                    (bv-array-read-chunk-little n1 8 n2 (+ (bvchop 32 ad1) (bvuminus 32 ad2)) (read-bytes ad2 n2 stat))
                    (bv-array-read-chunk-little n1 8 n2 (bvchop 32 (+ ad1 (- ad2))) (read-bytes ad2 n2 stat)))
           :induct (read n1 ad1 stat)
           :in-theory (e/d ((:i read)
                            bvplus
                            ;bvuminus
                            bvuminus
                            ;acl2::bvchop-of-sum-cases
                            subregion32p
                            bvlt
                            in-region32p
                            read-becomes-read-byte
                            ifix
                            ;read-byte-of-+
                            ;read-of-+ ; loops with bvplus
                            acl2::expt-becomes-expt-limited
                            bvplus-helper
                            zp
                            unsigned-byte-p
                            )
                           (;distributivity
                            acl2::+-of-minus-constant-version ; fixme disable
                            (:e expt)
                            acl2::bvplus-of-+-arg3
                            disjoint-regions32p-of-+-arg4
                            in-region32p-of-+-arg3
                            ;bvchop-of-read ;looped, but we need it
                            ;acl2::bvcat-equal-rewrite acl2::bvcat-equal-rewrite-alt ; looped
                            ;; for speed:
                            ;acl2::usb-when-usb8
                            ;acl2::bvchop-identity
                            in-region32p-when-in-region32p-and-subregion32p
                            ;acl2::bound-lemma-for-adder
                            acl2::<-of-*-same-linear-special
                            acl2::bv-array-read-chunk-little-unroll ; looped
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;read-over-write-rules

(defthm read-byte-of-write32-xreg
  (equal (read-byte addr (write32-xreg reg val stat))
         (read-byte addr stat))
  :hints (("Goal" :in-theory (enable read-byte))))

(defthm read-of-write32-xreg
  (equal (read n addr (write32-xreg reg val stat))
         (read n addr stat))
  :hints (("Goal" :in-theory (enable read))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable ubyte8p)))

;; Writes the BYTE at address ADDR.
(defund write-byte (addr byte stat)
  (declare (xargs :guard (and (unsigned-byte-p 32 addr)
                              (unsigned-byte-p 8 byte)
                              (stat32ip stat))))
  (write32-mem-ubyte8 addr byte stat))

(defthm write-byte-when-not-integerp
  (implies (not (integerp addr))
           (equal (write-byte addr val stat)
                  (write-byte 0 val stat)))
  :hints (("Goal" :in-theory (enable write-byte write32-mem-ubyte8))))

(defthm write-byte-of-bvchop-32
  (equal (write-byte (bvchop 32 addr) val stat)
         (write-byte addr val stat))
  :hints (("Goal" :in-theory (e/d (write-byte) ()))))

(defthm stat32ip-of-write-byte
  (implies (stat32ip stat)
           (stat32ip (write-byte addr byte stat)))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthm error32p-of-write-byte
  (equal (error32p (write-byte addr byte stat))
         (error32p stat))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthmd write32-mem-ubyte8-becomes-write-byte
  (equal (write32-mem-ubyte8 addr byte stat)
         (write-byte addr byte stat))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthmd write-byte-of-+
  (implies (and (integerp x)
                (integerp y))
           (equal (write-byte (+ x y) val stat)
                  (write-byte (bvplus 32 x y) val stat)))
  :hints (("Goal" :in-theory (e/d (write-byte write32-mem-ubyte8 bvplus)
                                  (acl2::bvplus-of-+-arg3
                                   disjoint-regions32p-of-+-arg4
                                   in-region32p-of-+-arg3)))))

(theory-invariant (incompatible (:rewrite write-byte-of-+) (:definition bvplus)))

(defthm write-byte-of-bvchop-8
  (equal (write-byte addr (bvchop 8 val) stat)
         (write-byte addr val stat))
  :hints (("Goal" :in-theory (enable write-byte write32-mem-ubyte8))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Writes the N-byte chunk VAL starting at ADDR (in little endian fashion).
(defund write (n addr val stat)
  (declare (xargs :guard (and (natp n)
                              (unsigned-byte-p (* 8 n) val)
                              (unsigned-byte-p 32 addr)
                              (stat32ip stat))))
  (if (zp n)
      stat
    (let ((stat (write-byte addr (bvchop 8 val) stat)))
      (write (+ -1 n)
             (bvplus 32 1 addr)
             (logtail 8 val) ;(slice (+ -1 (* 8 n)) 8 val)
             stat))))

(defthm write-when-not-integerp
  (implies (not (integerp addr))
           (equal (write n addr val stat)
                  (write n 0 val stat)))
  :hints (("Goal" :in-theory (enable write))))

(local
  (defun write-sub8-induct (n addr val stat size)
    (if (zp n)
        (list n addr val stat size)
      (let ((stat (write-byte addr (bvchop 8 val) stat)))
        (write-sub8-induct (+ -1 n)
                           (bvplus 32 1 addr)
                           (logtail 8 val) ;(slice (+ -1 (* 8 n)) 8 val)
                           stat
                           (+ -8 size))))))

(defthm write-of-bvchop-arg3
  (implies (and (<= (* 8 n) size)
                (integerp size)
                (natp n))
           (equal (write n addr (bvchop size val) stat)
                  (write n addr val stat)))
  :hints (("Goal" :expand (write n addr (bvchop size val) stat)
           :induct (write-sub8-induct n addr val stat size)
           :in-theory (e/d (write acl2::logtail-of-bvchop) ()))))

(defthm write-of-logext-arg3
  (implies (and (<= (* 8 n) size)
                (integerp size)
                (natp n))
           (equal (write n addr (logext size val) stat)
                  (write n addr val stat)))
  :hints (("Goal" :use ((:instance write-of-bvchop-arg3)
                        (:instance write-of-bvchop-arg3 (val (logext size val)))))))

(defthm write-of-bvchop-32-arg2
  (equal (write n (bvchop 32 addr) val stat)
         (write n addr val stat))
  :hints (("Goal" :expand (write n (bvchop 32 addr) val stat)
           :in-theory (e/d (write) ()))))

(defthmd write-of-1-becomes-write-byte
  (equal (write 1 addr val stat)
         (write-byte addr val stat))
  :hints (("Goal" :expand (write 1 addr val stat)
           :in-theory (enable write))))

(defthm error32p-of-write
  (equal (error32p (write n addr byte stat))
         (error32p stat))
  :hints (("Goal" :in-theory (enable write))))

(defthm stat32ip-of-write
  (implies (stat32ip stat)
           (stat32ip (write n addr byte stat)))
  :hints (("Goal" :in-theory (enable write))))

(defthmd write32-mem-ubyte32-lendian-becomes-write
  (implies (and (integerp addr)
                ;(unsigned-byte-p 32 val)
                )
           (equal (write32-mem-ubyte32-lendian addr val stat)
                  (write 4 addr val stat)))
  :hints (("Goal" :expand ((:free (n addr val stat) (write n addr val stat)))
           :in-theory (enable write32-mem-ubyte32-lendian-alt-def
                              acl2::bvchop-of-logtail-becomes-slice
                              ;write32-mem-ubyte32-lendian
                              write
                              ubyte32-fix
                              acl2::ash-becomes-logtail
                              write32-mem-ubyte8-becomes-write-byte
                              ubyte32p
                              acl2::bvand-with-constant-mask-arg2
                              write-byte-of-+))))

(defthmd write-of-+
  (implies (and (integerp x)
                (integerp y))
           (equal (write n (+ x y) val stat)
                  (write n (bvplus 32 x y) val stat)))
  :hints (("Goal" :in-theory (enable write write-byte-of-+ acl2::bvplus-of-+-arg3))))

;; We use WRITE as the normal form
(defthmd write-byte-becomes-write
  (equal (write-byte addr val stat)
         (write 1 addr val stat))
  :hints (("Goal" :expand (write 1 addr val stat)
           :in-theory (enable write))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Could weaken to just require the bvchops to be equal
(defthm read-byte-of-write-byte-same
  (equal (read-byte addr (write-byte addr byte stat))
         (bvchop 8 byte))
  :hints (("Goal" :in-theory (enable read-byte write-byte))))

(defthm read-byte-of-write-byte-diff
  (implies (not (equal (bvchop 32 addr1)
                       (bvchop 32 addr2)))
           (equal (read-byte addr1 (write-byte addr2 byte stat))
                  (read-byte addr1 stat)))
  :hints (("Goal" :in-theory (enable read-byte write-byte))))

(defthm read-byte-subst-term-arg1
  (implies (and (equal (bvchop 32 ad) (bvchop 32 free))
                (syntaxp (smaller-termp free ad)))
           (equal (read-byte ad stat)
                  (read-byte free stat)))
  :hints (("Goal" :in-theory (enable read-byte read32-mem-ubyte8))))

;move up
(defthm write-byte-subst-term-arg1
  (implies (and (equal (bvchop 32 ad) (bvchop 32 free))
                (syntaxp (smaller-termp free ad))
                ;(integerp ad)
                ;(integerp free)
                )
           (equal (write-byte ad byte stat)
                  (write-byte free byte stat)))
  :hints (("Goal" :in-theory (enable write-byte write32-mem-ubyte8))))

(defthm write-byte-subst-const-arg1
  (implies (and (syntaxp (not (quotep ad)))
                (equal (bvchop 32 ad) free)
                (syntaxp (quotep free))
                ;(integerp ad)
                ;(integerp free)
                )
           (equal (write-byte ad byte stat)
                  (write-byte free byte stat)))
  :hints (("Goal" :in-theory (enable))))

;; Handles both cases (same address, different address).
;; Could add separate -same and -diff rules that would not cause case splits.
(defthm read-byte-of-write-byte
  (equal (read-byte addr1 (write-byte addr2 byte stat))
         (if (equal (bvchop 32 addr1)
                    (bvchop 32 addr2))
             (bvchop 8 byte)
           (read-byte addr1 stat)))
  :hints (("Goal" :in-theory (enable))))

(defthm read-byte-of-write-irrel-gen
  (implies (and (<= n (bvminus 32 addr1 addr2))
        ;        (integerp addr1)
         ;       (integerp addr2)
                )
           (equal (read-byte addr1 (write n addr2 val stat))
                  (read-byte addr1 stat)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct t
           :in-theory (e/d (read write bvplus
                                 acl2::bvchop-of-sum-cases
                                 acl2::bvuminus bvminus
                                 ;read-byte
                                 read32-mem-ubyte8-becomes-read-byte)
                           (acl2::bvminus-becomes-bvplus-of-bvuminus
                            acl2::bvcat-of-+-high
                            acl2::bvchop-identity
                            acl2::bvplus-of-+-arg3
                            disjoint-regions32p-of-+-arg4
                            in-region32p-of-+-arg3
                            write-of-bvchop-32-arg2 ; why?
                            )))))

(defthm read-byte-of-write-within
  (implies (and (< (bvminus 32 ad1 ad2) n)
                (<= n (expt 2 32))
                (integerp n)
;                (integerp ad1) ;needed?
                ;(integerp ad2)
                )
           (equal (read-byte ad1 (write n ad2 val stat))
                  (slice (+ 7 (* 8 (bvminus 32 ad1 ad2)))
                         (* 8 (bvminus 32 ad1 ad2))
                         val)))
  :hints (("Goal" :induct t
           :do-not '(preprocess)
           :in-theory (e/d (read
                            write posp
                            ;read-byte
                            ;write-byte
                            acl2::bvuminus
                            bvplus acl2::bvchop-of-sum-cases
                            read32-mem-ubyte8-becomes-read-byte ; todo: loop
                            acl2::expt-becomes-expt-limited
                            )
                           (acl2::bvplus-of-+-arg3
                            disjoint-regions32p-of-+-arg4
                            in-region32p-of-+-arg3
                            write32-mem-ubyte8-of-+-arg1 ; todo: loop
                            (:e expt)
                            )))))

(defthm read-byte-of-write-both
  (implies (and (<= n (expt 2 32))
                (integerp n)
                ;; (integerp ad1)
                ;; (integerp ad2)
                )
           (equal (read-byte ad1 (write n ad2 val stat))
                  (if (< (bvminus 32 ad1 ad2) n)
                      (slice (+ 7 (* 8 (bvminus 32 ad1 ad2)))
                             (* 8 (bvminus 32 ad1 ad2))
                             val)
                    (read-byte ad1 stat)))))

(DEFTHM READ-BYTE-OF-WRITE-BOTH-new
  (IMPLIES (AND ;(<= N (EXPT 2 32))
             (unsigned-byte-p 32 n)
             (INTEGERP N)
             ;; (INTEGERP AD1)
             ;; (INTEGERP AD2)
             )
           (EQUAL (READ-BYTE AD1 (WRITE N AD2 VAL STAT))
                  (IF (in-region32p ad1 n ad2)
                      (SLICE (+ 7 (* 8 (BVMINUS 32 AD1 AD2)))
                             (* 8 (BVMINUS 32 AD1 AD2))
                             VAL)
                    (READ-BYTE AD1 STAT))))
  :hints (("Goal" :in-theory (enable in-region32p bvlt))))

;build in to tool
(defthm subregion32p-of-+-of--1-same
  (implies (posp n)
           (subregion32p (+ -1 n) 1 n 0))
  :hints (("Goal" :in-theory (enable subregion32p in-region32p bvlt))))

(defthm read-of-write-when-disjoint-regions32p
  (implies (and (disjoint-regions32p n1 ad1 n2 ad2)
                (integerp ad1)
                (integerp ad2)
                (unsigned-byte-p 32 n1)
                (unsigned-byte-p 32 n2))
           (equal (read n1 ad1 (write n2 ad2 val stat))
                  (read n1 ad1 stat)))
  :hints (("Goal" :in-theory (enable read write zp))))

(local
  (defthm read-of-write-same-helper
    (implies (and (<= n 4294967296) ; 2^32
                  (integerp addr) ; drop?
                  (integerp n))
             (equal (read n addr (write n addr val stat))
                    (bvchop (* 8 n) val)))
    :hints (("Goal"
             :in-theory (e/d (read write acl2::bvchop-of-logtail-becomes-slice)
                             (;memi
                              (:e expt) ; memory exhaustion
                              ))))))

; same n and same address
(defthm read-of-write-same
  (implies (and (<= n 4294967296) ; 2^32
                ;; (integerp addr)
                (integerp n))
           (equal (read n addr (write n addr val stat))
                  (bvchop (* 8 n) val)))
  :hints (("Goal" :use (:instance read-of-write-same-helper (addr (ifix addr)))
           :in-theory (e/d (ifix) (read-of-write-same-helper
                                   (:e expt))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm read-of-write-when-disjoint-regions32p-gen
  (implies (and (disjoint-regions32p len1 start1 len2 start2) ; free vars
                (subregion32p n1 ad1 len1 start1)
                (subregion32p n2 ad2 len2 start2)
                (integerp ad1)
                (integerp ad2)
                (integerp start1)
                (integerp start2)
                (unsigned-byte-p 32 n1)
                (unsigned-byte-p 32 n2))
           (equal (read n1 ad1 (write n2 ad2 val stat))
                  (read n1 ad1 stat)))
  :hints (("Goal" :in-theory (enable read write))))

(defthm read-of-write-when-disjoint-regions32p-gen-alt
  (implies (and (disjoint-regions32p len2 start2 len1 start1) ; todo: rename vars
                (subregion32p n1 ad1 len1 start1)
                (subregion32p n2 ad2 len2 start2)
                (integerp ad1)
                (integerp ad2)
                (integerp start1)
                (integerp start2)
                (unsigned-byte-p 32 n1)
                (unsigned-byte-p 32 n2))
           (equal (read n1 ad1 (write n2 ad2 val stat))
                  (read n1 ad1 stat)))
  :hints (("Goal" :use (:instance read-of-write-when-disjoint-regions32p-gen)
;           :in-theory '(disjoint-regions32p-symmetric)
           )))

(defthm read-of-+-bvchop-arg2
  (implies (and (integerp k)
                (integerp ad))
           (equal (read n (+ k (bvchop 32 ad)) stat)
                  (read n (+ k ad) stat)))
  :hints (("Goal" :use ((:instance read-of-bvchop-32 (addr (+ k (bvchop 32 ad))))
                        (:instance read-of-bvchop-32 (addr (+ k ad))))
           :in-theory (disable read-of-bvchop-32
                               ;acl2::bvchop-sum-drop-bvchop-alt
                               ))))

(defthm read-of-+-subst-arg2
  (implies (and (equal (bvchop 32 ad) free)
                (syntaxp (smaller-termp free ad))
                (integerp k)
                (integerp ad))
           (equal (read n (+ k ad) stat)
                  (read n (+ k free) stat))))

(defthm read-of-write-byte-irrel
  (implies (and (<= 1 (bvminus 32 addr1 addr2))
                (<= n1 (bvminus 32 addr2 addr1))
                ;(natp n1)
                ;; (integerp addr2)
                ;; (integerp addr1)
                )
           (equal (read n1 addr1 (write-byte addr2 byte stat))
                  (read n1 addr1 stat)))
  :hints ( ;("subgoal *1/2" :cases ((equal n1 1)))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (read n1 addr1 stat)
           :in-theory (e/d (read bvplus acl2::bvchop-of-sum-cases  bvuminus bvminus read-when-bvchops-agree ifix)
                           (acl2::bvminus-becomes-bvplus-of-bvuminus ACL2::BVCAT-OF-+-HIGH)))))

(include-book "kestrel/bv/putbits" :dir :system)

;; todo: use in-regionp?
(defthm read-of-write-1-within
  (implies (and (bvlt 32 (bvminus 32 addr2 addr1) n)
                ;; (integerp addr1)
                ;; (integerp addr2)
                (unsigned-byte-p 32 n))
           (equal (read n addr1 (write 1 addr2 val stat))
                  (putbyte n (bvminus 32 addr2 addr1) val (read n addr1 stat))))
  :hints (("Goal" :induct (read n addr1 stat)
           :do-not '(generalize eliminate-destructors)
           :expand (read n addr1 (write-byte 0 val stat))
           :in-theory (e/d (read
                            write-of-1-becomes-write-byte
                            ;bvminus
                            bvplus
                            bvuminus
                            acl2::bvchop-of-sum-cases
                            bvlt
                            acl2::expt-becomes-expt-limited
                            read-when-bvchops-agree ifix)
                           ((:e expt)
                            ;;ACL2::BVCAT-EQUAL-REWRITE
                            ACL2::BVCAT-EQUAL-REWRITE-ALT)))))



(local (include-book "kestrel/lists-light/update-nth" :dir :system))
(defthm write-byte-of-write-byte-same
  (implies (integerp ad)
           (equal (write-byte ad byte1 (write-byte ad byte2 stat))
                  (write-byte ad byte1 stat)))
  :hints (("Goal" :in-theory (enable write-byte
                                     write32-mem-ubyte8 ; todo
                                     memory32ip
                                     ))))

(defthm write-byte-of-write-byte-diff
  (implies (and (syntaxp (smaller-termp ad2 ad1))
                (not (equal (bvchop 32 ad1)
                            (bvchop 32 ad2)))
                (integerp ad1)
                (integerp ad2))
           (equal (write-byte ad1 byte1 (write-byte ad2 byte2 stat))
                  (write-byte ad2 byte2 (write-byte ad1 byte1 stat))))
  :hints (("Goal" :in-theory (enable write-byte
                                     write32-mem-ubyte8 ; todo
                                     memory32ip
                                     ))))

(defthm write-byte-of-write-byte-gen
  (implies (and (syntaxp (smaller-termp ad2 ad1))
                (integerp ad1)
                (integerp ad2))
           (equal (write-byte ad1 byte1 (write-byte ad2 byte2 stat))
                  (if (equal (bvchop 32 ad1)
                             (bvchop 32 ad2))
                      (write-byte ad1 byte1 stat)
                    (write-byte ad2 byte2 (write-byte ad1 byte1 stat)))))
  :hints (("Goal" :use write-byte-of-write-byte-diff
           :in-theory (disable write-byte-of-write-byte-diff))))

(defthm write-of-+-bvchop-arg2
  (implies (and (integerp k)
                (integerp ad))
           (equal (write n (+ k (bvchop 32 ad)) val stat)
                  (write n (+ k ad) val stat)))
  :hints (("Goal" :use ((:instance write-of-bvchop-32-arg2 (addr (+ k (bvchop 32 ad))))
                        (:instance write-of-bvchop-32-arg2 (addr (+ k ad))))
           :in-theory (disable write-of-bvchop-32-arg2))))

(defthm write-of-+-subst-arg2
  (implies (and (equal (bvchop 32 ad) free)
                (syntaxp (smaller-termp free ad))
                (integerp k)
                (integerp ad))
           (equal (write n (+ k ad) val stat)
                  (write n (+ k free) val stat))))

(defthm write-of-4294967296
  (equal (write n 4294967296 val stat)
         (write n 0 val stat))
  :hints (("Goal" :use (:instance write-of-bvchop-32-arg2
                                  (addr 4294967296))
           :in-theory (disable write-of-bvchop-32-arg2))))

(defthm write-byte-subst-arg1
  (implies (and (equal (bvchop 32 ad) freek)
                (syntaxp (and (quotep freek)
                              (not (quotep ad))))
                (integerp ad)
                (integerp freek))
           (equal (write-byte ad byte stat)
                  (write-byte freek byte stat))))

(defthm write-of-write-byte-within
  (implies (and ;; ad2 is in the interval [ad1,ad1+n):
            (< (bvminus 32 ad2 ad1) n)
            ;; (integerp ad1)
            ;; (integerp ad2)
            (integerp n))
           (equal (write n ad1 val (write-byte ad2 byte stat))
                  (write n ad1 val stat)))
  :hints (("Goal" :induct t
           :in-theory (enable write
                              acl2::bvchop-of-sum-cases
                              bvminus
                              bvplus
                              ifix))))

(local (include-book "kestrel/arithmetic-light/limit-expt" :dir :system))
(local (acl2::limit-expt))

;; todo: gen the 1?
;rename -bv
; needs write-of-write-byte
(defthm read-1-of-write-within ; in x86, this is called read-1-of-write-within-new
  (implies (and (bvlt 32 (bvminus 32 addr1 addr2) n) ; todo: use in-regionp?
                (unsigned-byte-p 32 n) ; allow 2^32?
                )
           (equal (read 1 addr1 (write n addr2 val stat))
                  (slice (+ 7 (* 8 (bvminus 32 addr1 addr2)))
                         (* 8 (bvminus 32 addr1 addr2))
                         val)))
  :hints (("Goal" :induct (write n addr2 val stat)
           :in-theory (e/d (read write bvminus bvlt acl2::bvchop-of-sum-cases
                                 bvplus
                                 acl2::bvuminus-of-+
                                 bvuminus
                                 ifix
                                 in-region32p)
                           ((:e expt) ; todo
                            acl2::bvuminus-of-+ ; todo loop
                            )))))

(defthm write-normalize-constant-arg2
  (implies (and (syntaxp (quotep addr))
                (not (unsigned-byte-p 32 addr)))
           (equal (write n addr val stat)
                  (write n (bvchop 32 addr) val stat))))

(defthm write-normalize-constant-arg3
  (implies (and (syntaxp (and (quotep k)
                              (quotep n)))
                (not (unsigned-byte-p (* n 8) k))
                (natp n)
                )
           (equal (write n addr k stat)
                  (write n addr (bvchop (* n 8) k) stat))))

(defthm read-normalize-constant-arg2
  (implies (and (syntaxp (quotep addr))
                (not (unsigned-byte-p 32 addr)))
           (equal (read n addr stat)
                  (read n (bvchop 32 addr) stat))))
