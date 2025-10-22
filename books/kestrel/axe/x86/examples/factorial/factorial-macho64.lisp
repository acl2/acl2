; Lifts and verifies an x86 factorial, without unrolling loops
;
; Copyright (C) 2017-2021 Kestrel Technology, LLC
; Copyright (C) 2023-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; In this file, we apply Axe to lift an x86 version of factorial into logic,
;; without unrolling the loops.  Then we use APT to prove the resulting
;; function equivalent to the spec.

;; STATUS: COMPLETE

;; cert_param: (uses-stp)

(include-book "kestrel/x86/parsers/parse-executable" :dir :system)
(include-book "kestrel/axe/x86/loop-lifter" :dir :system)
(include-book "kestrel/utilities/deftest" :dir :system)
(include-book "kestrel/bv/rules3" :dir :system) ;for bvchop-of-+-becomes-bvplus
(include-book "kestrel/apt/wrap-output" :dir :system)
(include-book "kestrel/apt/simplify" :dir :system)
(include-book "kestrel/apt/drop-irrelevant-params" :dir :system)
(include-book "kestrel/apt/rename-params" :dir :system)
(include-book "kestrel/apt/tailrec" :dir :system)
(include-book "kestrel/apt/def" :dir :system)

; (depends-on "factorial.macho64")

(apt::set-default-input-old-to-new-enable t) ; for tailrec

(local (in-theory (enable acl2::bvchop-of-+-becomes-bvplus)))

;; TODO: Consider using a higher-level spec that doesn't use BV operations.
(defund factorial-spec (n)
  (declare (xargs :measure (bvchop 32 n)))
  (if (or (not (unsigned-byte-p 32 n)) ;for tailrec.  TODO: Drop this?
          (sbvle 32 n 0)) ;terminate if n <= 0
      1 ; factorial of 0 is 1
    ;; return n * (n-1)! :
    (bvmult 32 n (factorial-spec (bvminus 32 n 1)))))

;; Below, we simplify this (e.g., by projecting out just the state component we care about).
(lift-subroutine factorial
                 :target "_fact"
                 :executable "factorial.macho64"
                 :loops ((20 . ;offset to loop header
                             (20 24 30 33 37 40 43 46 49) ;loop pc offsets
                             ))
                 :measures ((20 (bvchop 32 var20)))
                 :stack-slots 3)

;; Test the lifted code:
(acl2::assert-equal (factorial 6 0) 720)

;; Now we have the function factorial, which represents an initial lifted
;; version of the code.  It is a bit messy, so we simplfy it using Kestrel's
;; APT toolkit.

;; Project out the output we care about (requires the simplify step below to
;; finish the job).
(def factorial-loop-1.2-pre
  (wrap-output factorial-loop-1 (lambda (x) (nth '3 x))
               :guard-hints nil
               :theorem-disabled nil
               :function-disabled nil))

;; Simplify to complete previous step:
(def factorial-loop-1.2
  (simplify factorial-loop-1.2-pre))

;; Drop all the extra params that do not support the output we care about:
(def factorial-loop-1.3
  (drop-irrelevant-params factorial-loop-1.2 (rax flag-af flag-cf flag-of flag-pf flag-sf flag-zf undef)))

;; Rename the params to match the spec:
(def factorial-loop-1.4
  (rename-params factorial-loop-1.3 ((var20 n) (var16 acc))))

;; needed for final theorem below
(defthm unsigned-byte-p-32-of-factorial-loop-1.4
  (implies (unsigned-byte-p 32 acc)
           (unsigned-byte-p 32 (factorial-loop-1.4 n acc))))

;; Now we have factorial-loop-1.4, which is pretty nice.  Next, we use APT to
;; transform the spec to make it more like the lifted code, so we can prove
;; them equivalent.

;; To make the spec match the lifted code, we have to make the it tail-recursive:
(def factorial-spec.2
  (apt::tailrec factorial-spec :domain (lambda (x) (unsigned-byte-p 32 x))))

;; Now we can directly prove equivalence of the (lifted, transformed) code and the
;; (transformed) spec:
(defthm connection-lemma
  (implies (and (unsigned-byte-p 32 n)
                (unsigned-byte-p 32 acc)
                (not (sbvlt 32 n 0)) ;; argument should not be negative
                )
           (equal (factorial-spec.2 n acc)
                  (factorial-loop-1.4 n acc)))
  :hints (("Goal" :induct t
           :in-theory (enable factorial-spec.2))))

;; Final correctness theorem linking the lifted code and the spec.
;; (The initial undef value in the code is unused.)
(defthm final
  (implies (and (unsigned-byte-p 32 n)
                (sbvle 32 0 n))
           (equal (factorial n undef)
                  (factorial-spec n))))
