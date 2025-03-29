; Axe rules about BV lists
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2021 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")


(include-book "known-booleans")
(include-book "axe-syntax")
(include-book "axe-syntax-functions-bv")
(include-book "kestrel/bv/unsigned-byte-p-forced" :dir :system)
(include-book "kestrel/bv/bvlt" :dir :system)
(include-book "kestrel/bv-lists/all-all-unsigned-byte-p" :dir :system)
(include-book "kestrel/bv-lists/bvchop-list" :dir :system)
(include-book "kestrel/bv-lists/bvxor-list" :dir :system)
(include-book "kestrel/bv-lists/unsigned-byte-listp" :dir :system)
(include-book "kestrel/bv-lists/byte-listp" :dir :system)
(include-book "kestrel/typed-lists-light/items-have-len" :dir :system)
(include-book "kestrel/typed-lists-light/all-true-listp" :dir :system)
;(include-book "kestrel/lists-light/prefixp" :dir :system) ;drop?
(include-book "kestrel/utilities/defopeners" :dir :system)
(include-book "kestrel/lists-light/all-same" :dir :system)
(include-book "kestrel/lists-light/repeat" :dir :system)
;(include-book "kestrel/lists-light/nth" :dir :system)
(local (include-book "list-rules")) ; for nth-equal-car-hack

(add-known-boolean unsigned-byte-listp)
(add-known-boolean all-unsigned-byte-p)
(add-known-boolean all-integerp)
(add-known-boolean byte-listp)

(add-known-boolean items-have-len)
(add-known-boolean all-true-listp)
(add-known-boolean all-all-unsigned-byte-p)

;TODO: I forgot the extra parens around the claim, and it treated AND as one claim and so on...
;use def-constant-opener?
(defopeners bvxor-list :hyps ((and (syntaxp (quotep x)) (syntaxp (quotep y)))))

(defthmd nth-of-bv-when-all-same
  (implies (and (syntaxp (quotep lst))
                (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (all-same lst)
                (< (len lst) (expt 2 xsize))
                (unsigned-byte-p-forced xsize x))
           (equal (nth x lst)
                  (if (bvlt xsize x (len lst))
                      (car lst)
                    nil)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p-forced  nth-when-all-same)
                                  (all-same
                                   ;;CAR-BECOMES-NTH-OF-0 ;looped
                                   )))))

(defthmd nth-of-plus-of-bv-and-minus
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (natp y)
                (unsigned-byte-p-forced xsize x))
           (equal (nth (+ x (- y)) lst)
                  (if (<= y x)
                      (nth (bvplus xsize x (- y)) lst)
                    (nth 0 lst))))
  :hints (("Goal" :in-theory (e/d (bvplus bvminus bvuminus unsigned-byte-p-forced unsigned-byte-p nth)
                                  (;NTH-OF-CDR
                                   )))))

(defthmd nth-of-plus-of-bv-and-minus-alt
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (natp y)
                (unsigned-byte-p-forced xsize x))
           (equal (nth (+ (- y) x) lst)
                  (if (<= y x)
                      (nth (bvplus xsize x (- y)) lst)
                    (nth 0 lst))))
  :hints (("Goal" :use (:instance nth-of-plus-of-bv-and-minus)
           :in-theory (disable nth-of-plus-of-bv-and-minus))))

(defthmd repeat-of-plus-of-bv-and-minus
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (natp y)
                (unsigned-byte-p-forced xsize x))
           (equal (repeat (+ x (- y)) v)
                  (if (<= y x)
                      (repeat (bvplus xsize x (- y)) v)
                    (repeat 0 v))))
  :hints (("Goal" :in-theory (enable bvplus bvminus bvuminus unsigned-byte-p-forced unsigned-byte-p))))

(defthmd repeat-of-plus-of-bv-and-minus-alt
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (natp y)
                (unsigned-byte-p-forced xsize x))
           (equal (repeat (+ (- y) x) v)
                  (if (<= y x)
                      (repeat (bvplus xsize x (- y)) v)
                    (repeat 0 v))))
  :hints (("Goal" :use (:instance repeat-of-plus-of-bv-and-minus)
           :in-theory (disable repeat-of-plus-of-bv-and-minus))))

(defthmd firstn-of-+-of-minus
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y))
           (equal (firstn (+ x (- y)) z)
                  (if (< x y)
                      nil
                    (firstn (bvplus (max xsize ysize) x (bvuminus (max xsize ysize) y)) z))))
  :hints (("Goal" :in-theory (e/d (bvplus bvuminus bvminus unsigned-byte-p-forced <-of-if-arg1
                                          ;bvchop-identity-when-<=
                                          bvchop-identity-when-<=
                                          )
                                  (;UNSIGNED-BYTE-P-OF-+-OF-MINUS
                                   ;FIRSTN-BECOMES-TAKE-GEN
                                   )))))

(defthmd firstn-of-+-of-minus-2
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y))
           (equal (firstn (+ x (- y)) z)
                  (if (< x y)
                      nil
                    (firstn (bvplus (max xsize ysize) x (bvuminus (max xsize ysize) y)) z))))
  :hints (("Goal" :use (:instance firstn-of-+-of-minus)
           :in-theory (disable firstn-of-+-of-minus))))

;; Permuted variant
(defthmd equal-of-bvchop-list-and-nil
  (equal (equal (bvchop-list n x) nil)
         (not (consp x)))
  :hints (("Goal" :in-theory (enable bvchop-list))))
