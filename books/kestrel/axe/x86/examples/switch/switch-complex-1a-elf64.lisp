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
(include-book "support")

; (depends-on "switch-complex-1a.elf64")



;; Variant for 8-byte chunks (needed for the jump table with 336 bytes)
;; (defthm bv-array-read-chunk-little-when-multiple-8-336
;;   (implies (and (equal 0 (bvchop 3 index)) ; index is a multiple of 8
;;                 (equal 0 (bvchop 3 len))   ; len is a multiple of 8
;;                 (equal len 336)
;;                 (equal len (len array))
;;                 (natp index))
;;            (equal (bv-array-read-chunk-little 8 8 len index array)
;;                   (bv-array-read 64
;;                                  (/ len 8)
;;                                  (slice (- (ceiling-of-lg len) 1)
;;                                         3
;;                                         index)
;;                                  (acl2::packbvs-little 8 8 array))))
;;   :otf-flg t
;;   :hints (("Goal" :expand ((bvchop 3 index))
;;                   :in-theory (e/d (bv-array-read
;;                                    acl2::packbv-little
;;                                    acl2::packbv-opener
;;                                    acl2::bvchop-of-sum-cases
;;                                    bvplus
;;                                    nfix)
;;                                   (acl2::bvcat-of-nth-arg4
;;                                    acl2::bvcat-of-nth-arg2
;;                                    acl2::equal-of-constant-and-getbit-extend)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;





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
                   read-when-equal-of-read-bytes-and-subregion48p-smt
                   acl2::bv-array-read-shorten-when-in-first-half-smt
                   acl2::bv-array-read-chunk-little-when-multiple-8-8-smt
                   ;;bv-array-read-chunk-little-when-multiple-8-336
                   acl2::slice-trim-axe-all
                   acl2::bvplus-trim-arg2-axe-all
                   acl2::bvplus-trim-arg3-axe-all
                   slice-of-bvplus-cases ; EM, defined above temporarily
                   acl2::slice-of-bvplus-of-bvcat-special
                   acl2::bv-array-read-trim-index-axe-all
                   acl2::bv-array-read-of-bvplus-of-constant-no-wrap-bv-smt
                   acl2::bvsx-of-bv-array-read-constant-array
                   acl2::bvplus-of-bv-array-read-constant-array-smt
                   set-rip-of-bvif-split
                   x86isa::x86-fetch-decode-execute-of-if
                   )
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
