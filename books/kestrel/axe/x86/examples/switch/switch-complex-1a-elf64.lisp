; A proof of a more complex x86 binary function with a switch statement
; Version 1a: Lifts from main entry point instead of process_command
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; STATUS: INCOMPLETE (fails to lift)

;; Testing whether symbolic execution keeps global_counter symbolic
;; when lifting from the main entry point instead of directly from process_command.

;; This example is based on switch-complex-1.c but uses argv[1][0] (first byte)
;; for global_counter and argv[1][1] (second byte) as the command argument.
;; It lifts starting from main() rather than process_command(). This tests whether
;; Axe's symbolic execution will treat both values as symbolic when the entire
;; call chain from main is lifted together.

;; switch-complex-1a.elf64 was produced on Linux by:
;;
;;   gcc -o switch-complex-1a.elf64 switch-complex-1a.c
;;
;; with GCC 15.2.0 (in "--platform linux/amd64 gcc:latest" Docker container).

;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

; (depends-on "switch-complex-1a.elf64")

(defthm *-of-4-and-slice-when-multiple
  (implies (and (equal 0 (mod index 4))
                (natp n))
           (equal (* 4 (slice n 2 index))
                  (bvchop (+ 1 n) index))))

(def-constant-opener acl2::packbv-little :disable t)
(def-constant-opener acl2::packbvs-little :disable t)

(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))

;todo: gen
(defthm ceiling-of-lg-of-*-of-1/4
  (implies (and (equal 0 (mod x 4))
                (posp x))
           (equal (ceiling-of-lg (* 1/4 x))
                  (+ -2 (ceiling-of-lg x))))
  :hints (("Goal" :use (:instance acl2::ceiling-of-lg-of-*-of-expt-of-- (i 2))
                  :in-theory (disable acl2::ceiling-of-lg-of-*-of-expt-of--))))

;todo: gen!
(defthm bv-array-read-chunk-little-when-multiple
  (implies (and (equal 0 (bvchop 2 index)) ; index is a multiple of the chunk size
                (equal 0 (bvchop 2 len))
                (equal len 4096) ; fixme
                (equal len (len array)) ; todo
            ;    (axe-smt (bvlt (ceiling-of-lg 4096) index 4096))
                (natp index)
                )
           (equal (bv-array-read-chunk-little 4 8 len index array)
                  (bv-array-read 32
                                 (/ len 4)
                                 (slice (- (ceiling-of-lg len) 1)
                                        2
                                        index)
                                 (acl2::packbvs-little 4 8 array))))
  :otf-flg t
  :hints (("Goal" :expand ( ;(slice 6 2 index)
                           (bvchop 2 index))
                  :in-theory (e/d (bv-array-read
                                   acl2::packbv-little
                                   acl2::packbv-opener
                                   acl2::bvchop-of-sum-cases
                                   bvplus
                                   nfix)
                                  (acl2::bvcat-of-nth-arg4 ;loop
                                   acl2::bvcat-of-nth-arg2 ; loop!
                                   acl2::equal-of-constant-and-getbit-extend ; looped
                                   ;acl2::bvchop-top-bit-cases ; looped
                                   )))))

;; since the bvcat has low zeros, the low bits of k can't cause carry
;gen!  and don't require args to be trimmed?
(defthm acl2::slice-of-bvplus-of-bvcat-special
  (equal (slice 11 2 (bvplus 12 k (bvcat 10 val 2 0)))
         (bvplus 10 (slice 11 2 k) (bvchop 10 val)))
  :hints (("Goal" :in-theory (enable ;bvplus acl2::bvchop-of-sum-cases
                              acl2::slice-of-bvplus-cases))))

;; Variant for 8-byte chunks (needed for the jump table with 336 bytes)
(defthm bv-array-read-chunk-little-when-multiple-8-336
  (implies (and (equal 0 (bvchop 3 index)) ; index is a multiple of 8
                (equal 0 (bvchop 3 len))   ; len is a multiple of 8
                (equal len 336)
                (equal len (len array))
                (natp index))
           (equal (bv-array-read-chunk-little 8 8 len index array)
                  (bv-array-read 64
                                 (/ len 8)
                                 (slice (- (ceiling-of-lg len) 1)
                                        3
                                        index)
                                 (acl2::packbvs-little 8 8 array))))
  :otf-flg t
  :hints (("Goal" :expand ((bvchop 3 index))
                  :in-theory (e/d (bv-array-read
                                   acl2::packbv-little
                                   acl2::packbv-opener
                                   acl2::bvchop-of-sum-cases
                                   bvplus
                                   nfix)
                                  (acl2::bvcat-of-nth-arg4
                                   acl2::bvcat-of-nth-arg2
                                   acl2::equal-of-constant-and-getbit-extend)))))

(defund map-bvsx (high low lst)
  (if (endp lst)
      nil
    (cons (bvsx high low (first lst))
          (map-bvsx high low (rest lst)))))

(defthm unsigned-byte-listp-of-map-bvsx
  (implies (natp high)
           (acl2::unsigned-byte-listp ; package!
            high (map-bvsx high low data)))
  :hints (("Goal" :in-theory (enable map-bvsx))))

(defthm len-of-map-bvsx
  (equal (len (map-bvsx high low data))
         (len data))
  :hints (("Goal" :in-theory (enable map-bvsx))))

(def-constant-opener map-bvsx)

(defthmd bvsx-of-nth
  (implies (and (natp n)
                (< n (len data)))
           (equal (bvsx high low (nth n data))
                  (nth n (map-bvsx high low data))))
  :hints (("Goal" :in-theory (enable map-bvsx (:I nth)))))

(defthm bvsx-of-bv-array-read-constant-array
  (implies (and (syntaxp (quotep data))
                (equal len (len data)))
           (equal (bvsx 64 32 (bv-array-read 32 len index data))
                  (bv-array-read 64 len index (map-bvsx 64 32 data))))
  :hints (("Goal" :in-theory (enable bv-array-read bvsx-of-nth))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund map-bvplus-val (size val lst)
  (if (endp lst)
      nil
    (cons (bvplus size val (first lst))
          (map-bvplus-val size val (rest lst)))))

(defthm unsigned-byte-listp-of-map-bvplus-val
  (implies (natp size)
           (acl2::unsigned-byte-listp
            size (map-bvplus-val size val data)))
  :hints (("Goal" :in-theory (enable map-bvplus-val))))

(defthm len-of-map-bvplus-val
  (equal (len (map-bvplus-val high low data))
         (len data))
  :hints (("Goal" :in-theory (enable map-bvplus-val))))

(def-constant-opener map-bvplus-val)

(defthmd bvplus-of-nth
  (implies (and (natp n)
                (< n (len data)))
           (equal (bvplus size val (nth n data))
                  (nth n (map-bvplus-val size val data))))
  :hints (("Goal" :in-theory (enable map-bvplus-val (:I nth)))))

(defthm bvplus-of-bv-array-read-constant-array
  (implies (and (syntaxp (and (quotep data)
                              (quotep val)
                              (quotep size)))
                (natp size)
                (or (power-of-2p len)
                    (bvlt (ceiling-of-lg len) index (len data)))
                (equal len (len data)))
           (equal (bvplus size val (bv-array-read size len index data))
                  (bv-array-read size len index (map-bvplus-val size val data))))
  :hints (("Goal" :in-theory (enable bv-array-read bvplus-of-nth bvlt))))

(defthm bvplus-of-bv-array-read-constant-array-smt
  (implies (and (syntaxp (and (quotep data)
                              (quotep val)
                              (quotep size)))
                (natp size)
                (axe-smt (or (power-of-2p len)
                             (bvlt (ceiling-of-lg len) index (len data))))
                (equal len (len data)))
           (equal (bvplus size val (bv-array-read size len index data))
                  (bv-array-read size len index (map-bvplus-val size val data))))
  :hints (("Goal" :in-theory (enable bv-array-read bvplus-of-nth bvlt))))

(defun bv-array-read-cases (i size len index data)
  (if (zp i)
      (bv-array-read size len 0 data)
    (if (equal i (bvchop (ceiling-of-lg len) index))
        (bv-array-read size len i data)
      (bv-array-read-cases (+ -1 i) size len index data))))

;(defopeners bv-array-read-cases) ; didn't work well (rules too specific?)
(defthm bv-array-read-cases-opener
  (implies (syntaxp (quotep i))
           (equal (bv-array-read-cases i size len index data)
                  (if (zp i)
                      (bv-array-read size len 0 data)
                    (if (equal i (bvchop (ceiling-of-lg len) index))
                        (bv-array-read size len i data)
                      (bv-array-read-cases (+ -1 i) size len index data))))))



(local
 (defthm helper
   (implies (and (not (equal 0 i))
                 (not (equal i (bvchop size index)))
                 (not (bvlt size i index))
                 (natp index)
                 (unsigned-byte-p size i)
                 )
            (not (bvlt size (bvplus size -1 i) index)))
   :hints (("Goal" :do-not-induct t :in-theory (enable bvlt bvplus)))))

(defthmd bv-array-read-becomes-bv-array-read-cases-helper
  (implies (and (bvle (ceiling-of-lg len) index i)
                (natp index)
                (unsigned-byte-p (ceiling-of-lg len) i)
                (natp i))
           (equal (bv-array-read size len index data)
                  (bv-array-read-cases i size len index data)))
  :hints (("Goal" :induct (bv-array-read-cases i size len index data)
                  :expand ((bv-array-read size len 0 data)
                           (bv-array-read size len index data))
                  :in-theory (enable acl2::bvlt-convert-arg2-to-bv
                                     acl2::trim-of-+-becomes-bvplus ; don't we want this enabled?
                                     ))))

(defthmd bv-array-read-becomes-bv-array-read-cases
  (implies (and (posp len)
                (natp index)
                (unsigned-byte-p (ceiling-of-lg len) index)
                (bvle (ceiling-of-lg len) index (+ -1 len)) ; todo?
                )
           (equal (bv-array-read size len index data)
                  (bv-array-read-cases (bvchop (ceiling-of-lg len) (+ -1 len))
                                       size len index data)))
  :hints (("Goal" :use (:instance bv-array-read-becomes-bv-array-read-cases-helper
                                  (i (+ -1 len))))))

;; todo: to be more general, support splitting when the bv-array-read is not the entire new rip term.
;; approach: create an identify function that causes things to be split (and ifs to be lifted)? and propagate it downward through a non-constant set-rip argument when there is something to split.
(defthm set-rip-of-bv-array-read-split-cases
  (implies (and (syntaxp (quotep data))
                (< len 12) ; increased from 10 to handle 10 cases plus default
                (posp len)
                (natp index)
                (unsigned-byte-p (ceiling-of-lg len) index)
                (bvle (ceiling-of-lg len) index (+ -1 len)) ; todo?
                )
           (equal (set-rip (bv-array-read size len index data) x86)
                  (set-rip (bv-array-read-cases (bvchop (ceiling-of-lg len) (+ -1 len)) size len index data) x86)))
  :hints (("Goal" :in-theory (enable bv-array-read-becomes-bv-array-read-cases))))

(defthm set-rip-of-bvif-split
  (equal (set-rip (bvif size test tp ep) x86)
         (if test
             (set-rip (bvchop size tp) x86)
           (set-rip (bvchop size ep) x86))))

;;; EM: this is similar to slice-of-sum-cases but for bvplus
(defthmd slice-of-bvplus-cases
  (implies (and (natp low)
                (natp high)
                (natp size)
                (< high size))
           (equal (slice high low (bvplus size x y))
                  (if (< high low)
                      0
                    (if (<= (expt 2 low)
                            (+ (bvchop low x)
                               (bvchop low y)))
                        ;;if carry
                        (bvchop (+ 1 high (- low))
                                (+ 1
                                   (slice high low x)
                                   (slice high low y)))
                      ;;no carry:
                      (bvchop (+ 1 high (- low))
                              (+ (slice high low x)
                                 (slice high low y)))))))
  :hints (("Goal" :in-theory (e/d (bvplus acl2::slice-of-sum-cases)
                                  ()))))

#|
; This doesn't work yet.

;; Lift from the main entry point:
(def-unrolled main
    :executable "switch-complex-1a.elf64"
    :target "main"
    :extra-rules '(read-of-write-when-disjoint-regions48p-gen-smt
                   unsigned-canonical-address-p-smt
                   read-when-equal-of-read-bytes-and-subregion48p-smt
                   acl2::bv-array-read-trim-index-axe
                   acl2::bv-array-read-convert-arg3-to-bv-axe
                   acl2::bv-array-read-shorten-when-in-first-half-smt
                   bv-array-read-chunk-little-when-multiple
                   bv-array-read-chunk-little-when-multiple-8-336
                   acl2::packbvs-little-constant-opener
                   acl2::packbv-little-constant-opener
                   acl2::slice-trim-axe-all
                   acl2::bvplus-trim-arg2-axe-all
                   acl2::bvplus-trim-arg3-axe-all
                   slice-of-bvplus-cases ; EM, defined above temporarily
                   acl2::slice-of-bvplus-of-bvcat-special
                   acl2::bv-array-read-trim-index-axe-all
                   acl2::bv-array-read-of-bvplus-of-constant-no-wrap-bv-smt
                   bvsx-of-bv-array-read-constant-array
                   map-bvsx-constant-opener
                   bvplus-of-bv-array-read-constant-array-smt
                   map-bvplus-val-constant-opener
                   set-rip-of-bv-array-read-split-cases
                   bv-array-read-cases-opener
                   set-rip-of-bvif-split
                   x86isa::x86-fetch-decode-execute-of-if)
    :remove-rules '(acl2::bv-array-read-chunk-little-unroll)
    :position-independent nil
; this doesn't seem to change nything:
;    :inputs-disjoint-from :all
    :inputs ((argc u64)
             (argv u64)
             (envp u64)
             (global-counter-addr u64)
             (global-counter-val u32))
    :output :rax
    :extra-assumptions '((canonical-address-p$inline argv)
                         (canonical-address-p$inline (bvplus 64 8 argv))
                         (canonical-address-p$inline (bvplus 64 15 argv))
                         (canonical-address-p$inline (read 8 (bvplus 48 8 argv) x86))
                         (canonical-address-p$inline (bvplus 64 1 (read 8 (bvplus 48 8 argv) x86)))
                         (canonical-address-p$inline global-counter-addr))
    :monitor '(;acl2::bv-array-read-shorten-when-in-first-half
               ;acl2::bv-array-read-of-bvplus-of-constant-no-wrap-bv-smt
               )
    :stack-slots 10)
|#

