; Rules about padding bit-vectors with zeros
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; These are not really used much, with our current STP translation approach.

(include-book "bv-syntax")
(include-book "bvmult")
(include-book "bvif")
(include-book "bvcat")
(include-book "bvxor")

;Depending on how we translate to SMT, We might prefer, for example:
;(bvxor 8 x (bvchop 8 (foo x)) (slice 7 0 y))
;to
;(bvxor 8 x (foo x) (slice 7 0 y))
;even though the bvchop can be dropped, because foo might be big (say, of size 32) and the latter would give a length mismatch in stp
;more like this?
;(in-theory (disable bvxor-of-bvchop-1 bvxor-of-bvchop-2))
;(in-theory (enable add-bvchop-to-bvxor-1 add-bvchop-to-bvxor-2)) ;BOZO what about trimming constants?
;(in-theory (disable bvchop-identity))
;bozo this is too bad
;(theory-invariant (incompatible (:rewrite add-bvchop-to-bvxor-1) (:rewrite bvchop-identity)))
;(theory-invariant (incompatible (:rewrite add-bvchop-to-bvxor-2) (:rewrite bvchop-identity)))

;(in-theory (enable bvxor-trim-arg1 bvxor-trim-arg2))

;not used
(defthmd bvmult-pad-arg1
  (implies (and (bind-free (bind-var-to-bv-term-size 'xsize x) (xsize))
                (< xsize size)
                (natp size)
                (natp xsize)
                (force (unsigned-byte-p xsize x))
                (integerp y)
                )
           (equal (bvmult size x y)
                  (bvmult size (bvcat (- size xsize) 0 xsize x) y)))
  :hints (("Goal" :in-theory (e/d (bvchop-identity)
                                  ( ;add-bvchop-to-bvxor-1
                                   ;add-bvchop-to-bvxor-2
                                   )))))

;not used
;bozo do one like this for every operator?
(defthmd bvmult-pad-arg2
  (implies (and (bind-free (bind-var-to-bv-term-size 'ysize y) (ysize))
                (< ysize size)
                (natp size)
                (natp ysize)
                (force (unsigned-byte-p ysize y))
                (integerp y)
                )
           (equal (BVMULT size x y)
                  (bvmult size x (bvcat (- size ysize) 0 ysize y))))
  :hints (("Goal" :in-theory (e/d (bvchop-identity)
                                  ( ;ADD-BVCHOP-TO-BVXOR-1
                                   ;ADD-BVCHOP-TO-BVXOR-2
                                   )))))

(theory-invariant (incompatible (:rewrite bvmult-pad-arg1) (:rewrite BVCAT-OF-0)))
(theory-invariant (incompatible (:rewrite bvmult-pad-arg2) (:rewrite BVCAT-OF-0)))


;after this fires, the associativity rule should fire too
;bozo make a high version
(defthmd bvcat-pad-low
  (implies (and (bind-free (bind-var-to-bv-term-size 'newsize lowval) (newsize))
                (unsigned-byte-p newsize lowval)
                (< newsize lowsize)
                (natp lowsize)
                (natp newsize)
                (integerp highval)
                (integerp lowval)
                )
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat highsize highval lowsize (bvcat (- lowsize newsize) 0 newsize lowval))))
  :hints (("Goal" :in-theory (enable bvchop-identity bvcat-of-bvchop-low))))

(defthmd bvcat-pad-high
  (implies (and (bind-free (bind-var-to-bv-term-size 'newsize highval) (newsize))
                (unsigned-byte-p newsize highval)
                (< newsize highsize)
                (natp highsize)
                (natp newsize)
                (integerp highval)
                (integerp lowval)
                )
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat highsize (bvcat (- highsize newsize) 0 newsize highval) lowsize lowval)))
  :hints (("Goal" :in-theory (enable bvchop-identity bvcat-of-bvchop-low))))

;not used
(defthmd bvif-pad-arg-1-with-zeros
  (implies (and (bind-free (bind-var-to-bv-term-size 'newsize x) (newsize))
                (< newsize size)
                (unsigned-byte-p newsize x)
                (integerp x)
                (integerp y)
                (natp newsize)
                (natp size))
           (equal (bvif size test x y)
                  (bvif size test (bvcat (- size newsize) 0 newsize x) y)))
  :hints (("Goal" :in-theory (enable bvchop-identity))))

;not used
(defthmd bvif-pad-arg-2-with-zeros
  (implies (and (bind-free (bind-var-to-bv-term-size 'newsize y) (newsize))
                (< newsize size)
                (unsigned-byte-p newsize y)
                (integerp x)
                (integerp y)
                (natp newsize)
                (natp size))
           (equal (BVIF size test x y)
                  (bvif size test x (bvcat (- size newsize) 0 newsize y))))
  :hints (("Goal" :in-theory (enable bvchop-identity))))

;not used?
(defthmd bvxor-pad-arg1
  (implies (and (bind-free (bind-var-to-bv-term-size 'newsize x) (newsize))
                (< newsize size)
                (natp size)
                (natp newsize)
                (force (unsigned-byte-p newsize x))
                (integerp y)
                )
           (equal (bvxor size x y)
                  (bvxor size (bvcat (- size newsize) 0 newsize x) y)))
  :hints (("Goal" :in-theory (e/d (bvchop-identity)
                                  ( ;add-bvchop-to-bvxor-1
                                   )))))

;not used?
(defthmd bvxor-pad-arg2
  (implies (and (bind-free (bind-var-to-bv-term-size 'newsize y) (newsize))
                (< newsize size)
                (natp size)
                (natp newsize)
                (force (unsigned-byte-p newsize y))
                (integerp x)
                )
           (equal (bvxor size x y)
                  (bvxor size x (bvcat (- size newsize) 0 newsize y))))
  :hints (("Goal" :in-theory (e/d (bvchop-identity)
                                  ( ;add-bvchop-to-bvxor-1
                                   )))))

;now we handle the adding of padding when we translate to stp
;; (deftheory add-padding '(bvcat-pad-low
;;                          bvcat-pad-high
;;                          bvmult-pad-arg1
;;                          bvmult-pad-arg2
;;                          bvxor-pad-arg1
;;                          bvxor-pad-arg2))
