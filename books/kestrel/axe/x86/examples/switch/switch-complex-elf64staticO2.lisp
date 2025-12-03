; A proof of a more complex x86 binary function with a switch statement
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; STATUS: lifting fails.
;; Thehe SET-FAULT occurs at RIP 4200219 (0x40171b), which is a jmpq instruction.
;; The fault says :BAD-RETURN-ADDRESS with the target address read from the jump
;; table.
;; This can be contrasted with switch-complex-elf64.lisp, which successfully lifts
;; switch-complex.elf64, which is a dynamically linked ELF x86 executable
;; that seems to have the same jump table.

;; This example is like switch-complex.elf64
;; except that the switch-complex.c was compiled with the `-static -O2` switches.

;; switch-complex.elf64staticO2 was produced on Linux by:
;;
;;   gcc -static -O2 -o switch-complex.elf64staticO2 switch-complex.c
;;
;; with GCC 15.2.0 (in "--platform linux/amd64 gcc:latest" Docker container).
;; This version uses -O2 optimization level to test how the lifter handles
;; optimized code.  Note that the symbol table is not stripped.

;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "support")

; (depends-on "switch-complex.elf64staticO2")




;; ;; Variant for 8-byte chunks (needed for the jump table with 336 bytes)
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


(def-unrolled process-command
    :executable "switch-complex.elf64staticO2"
    :target "process_command"
    :extra-rules '(read-of-write-when-disjoint-regions48p-gen-smt
                   unsigned-canonical-address-p-smt
                   read-when-equal-of-read-bytes-and-subregion48p-smt
                   acl2::bv-array-read-shorten-when-in-first-half-smt
                   acl2::bv-array-read-chunk-little-when-multiple-8-8-smt
                   ;bv-array-read-chunk-little-when-multiple-8-336
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
                   x86isa::x86-fetch-decode-execute-of-if)
    :remove-rules '(acl2::bv-array-read-chunk-little-unroll)
    :position-independent nil
    :inputs ((cmd u32)
             (global-counter-addr u64)
             (global-counter-val u32))
    :output :rax
    :extra-assumptions '((canonical-address-p$inline global-counter-addr))
    :monitor '( ;acl2::bv-array-read-shorten-when-in-first-half
;acl2::bv-array-read-of-bvplus-of-constant-no-wrap-bv-smt
               )
    :stack-slots 10)


#|
;; Shows that the program correctly implements the switch statement.
;; For inputs 0-9, it returns global_counter * (cmd + 2)
;; and increments global_counter by (cmd + 1).
;; For all other inputs, it returns -1 and resets global_counter to 0.

(defthm process-command-correct-case-0
  (implies (equal global-counter-val 10) ; example initial value
           (equal (process-command 0 global-counter-addr global-counter-val)
                  (* 10 2))))

(defthm process-command-correct-case-1
  (implies (equal global-counter-val 10)
           (equal (process-command 1 global-counter-addr global-counter-val)
                  (* 10 3))))

(defthm process-command-correct-case-2
  (implies (equal global-counter-val 10)
           (equal (process-command 2 global-counter-addr global-counter-val)
                  (* 10 4))))

(defthm process-command-correct-case-3
  (implies (equal global-counter-val 10)
           (equal (process-command 3 global-counter-addr global-counter-val)
                  (* 10 5))))

(defthm process-command-correct-case-4
  (implies (equal global-counter-val 10)
           (equal (process-command 4 global-counter-addr global-counter-val)
                  (* 10 6))))

(defthm process-command-correct-case-5
  (implies (equal global-counter-val 10)
           (equal (process-command 5 global-counter-addr global-counter-val)
                  (* 10 7))))

(defthm process-command-correct-case-6
  (implies (equal global-counter-val 10)
           (equal (process-command 6 global-counter-addr global-counter-val)
                  (* 10 8))))

(defthm process-command-correct-case-7
  (implies (equal global-counter-val 10)
           (equal (process-command 7 global-counter-addr global-counter-val)
                  (* 10 9))))

(defthm process-command-correct-case-8
  (implies (equal global-counter-val 10)
           (equal (process-command 8 global-counter-addr global-counter-val)
                  (* 10 10))))

(defthm process-command-correct-case-9
  (implies (equal global-counter-val 10)
           (equal (process-command 9 global-counter-addr global-counter-val)
                  (* 10 11))))

(defthm process-command-correct-default
  (implies (bvlt 32 9 cmd) ; (not (member-equal cmd '(0 1 2 3 4 5 6 7 8 9)))
           (equal (process-command cmd global-counter-addr global-counter-val)
                  (bvuminus 32 1))))
|#
