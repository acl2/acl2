; Mixed Axe rules
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; These rules use the axe-syntax functions.

;; This file was called dagrulesmore.lisp.

(include-book "rules1")
(include-book "kestrel/bv/rules6" :dir :system)
(include-book "rules3") ;drop? ;for BVPLUS-OF-BVUMINUS-TIGHTEN-GEN-no-split
(include-book "axe-syntax-functions")
(include-book "axe-syntax-functions-bv")
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/library-wrappers/arithmetic-inequalities" :dir :system)) ;drop?
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system)) ; for EXPT-BOUND-LINEAR-2

(defthmd bvplus-commutative-2-sizes-differ2-dag
  (implies (and (axe-syntaxp (should-commute-args-dag 'bvplus x y dag-array)) ;gen?
                (equal (+ 1 smallsize) bigsize) ;relax somehow?
                (natp smallsize)
                (unsigned-byte-p smallsize y) ;move to conc? by adding bvchops - or maybe adding bvchop would cause loops?
;                (unsigned-byte-p smallsize z)
                (natp bigsize))
           (equal (bvplus bigsize x (bvplus smallsize y z))
                  (if (bvlt bigsize (bvplus bigsize y (bvchop smallsize z)) (expt 2 smallsize)) ;no overflow..
                      ;each of these have y before x:
                      (bvplus bigsize y (bvplus bigsize x (bvchop smallsize z)))
                    (bvplus bigsize (expt 2 smallsize) (bvplus bigsize y (bvplus bigsize x (bvchop smallsize z)))))))
  :hints (("Goal" ;:use (:instance bvplus-commutative-2-core (size bigsize))
           :in-theory (e/d (bvlt
                            bvplus
                            getbit-when-val-is-not-an-integer
                            bvuminus bvminus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (getbit-of-plus
;                            <-of-bvchop-arg1
                            <-becomes-bvlt-free
                            <-becomes-bvlt-free-alt
                            ;<-when-unsigned-byte-p
                            ;<-when-unsigned-byte-p-alt
                            <-becomes-bvlt
                            ;minus-becomes-bv
                            ;plus-becomes-bvplus-arg1-free
                            ;bvuminus-of-+
                            bvplus-of-plus-arg3
                            ;plus-1-and-bvchop-becomes-bvplus ;fixme
                            bvminus-becomes-bvplus-of-bvuminus
                            <-becomes-bvlt
                            <-becomes-bvlt-alt
                            <-of-bvplus-becomes-bvlt-arg1
                            <-of-bvplus-becomes-bvlt-arg2
                            ;anti-bvplus
                            ;getbit-of-+
                            ;plus-becomes-bvplus
                            bvlt-of-plus-arg1
                            bvlt-of-plus-arg2
                            ;slice-of-+
                            ;getbit-of-+ ;looped
                            )))))

;shouldn't this just go to bvuminus?
(defthmd bvchop-of-minus-trim
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (natp size))
           (equal (bvchop size (unary-- x))
                  (bvchop size (unary-- (trim size x)))))
  :hints (("Goal" :in-theory (enable trim))))

;; ;may be a bad idea inside a bvplus, since it can cause the sizes to differ
;; (defthmd bvuminus-when-smaller-bind-free-dag
;;   (implies (and (axe-bind-free (bind-bv-size-axe x 'free dag-array) '(free))
;;                 (< free size)
;;                 (natp size)
;;                 (unsigned-byte-p-forced free x)
;;                 )
;;            (equal (bvuminus size x)
;;                   (if (equal 0 x)
;;                       0
;;                       (bvplus size (- (expt 2 size) (expt 2 free))
;;                               (bvuminus free x)))))
;;   :hints (("Goal" :use (:instance bvuminus-when-smaller)
;;            :in-theory (disable bvuminus-when-smaller))))

(defthmd plus-becomes-bvplus-arg1-free-dag
  (implies (and (unsigned-byte-p xsize x)
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (force (unsigned-byte-p-forced ysize y))
                (posp xsize))
           (equal (+ x y)
                  (bvplus (+ 1 (max xsize ysize)) x y)))
  :hints (("Goal" :use (:instance plus-becomes-bvplus)
           :in-theory (e/d (unsigned-byte-p-forced) (plus-becomes-bvplus)))))

(defthmd plus-becomes-bvplus-arg2-free-dag
  (implies (and (unsigned-byte-p xsize x)
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p-forced ysize y)
                (posp xsize))
           (equal (+ y x)
                  (bvplus (+ 1 (max xsize ysize)) x y)))
  :hints (("Goal" :use (:instance plus-becomes-bvplus-arg2-free)
           :in-theory (disable plus-becomes-bvplus-arg2-free))))


;deprecated?
(defthmd <-becomes-bvlt-dag
  (implies (and (axe-bind-free (bind-bv-size-axe x 'free dag-array) '(free))
                (syntaxp (quotep k))
                (unsigned-byte-p-forced free x)
                (unsigned-byte-p free k))
           (equal (< k x)
                  (bvlt free k x)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced)
           :use (:instance <-becomes-bvlt))))


;gen the 1
(defthmd +-becomes-bvplus-when-bv-dag
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p-forced xsize x)
                (natp xsize))
           (equal (+ 1 x)
                  (bvplus (+ 1 xsize) 1 x)))
  :hints (("Goal" :in-theory (e/d (bvplus
                                   UNSIGNED-BYTE-P-FORCED)
                                  (anti-bvplus
                                   ;GETBIT-OF-+
                                   BVLT-OF-PLUS-ARG1
                                   BVLT-OF-PLUS-ARG2
                                   PLUS-BECOMES-BVPLUS
                                   <-OF-CONSTANT-WHEN-UNSIGNED-BYTE-P-SIZE-PARAM
                                   )))))

(DEFTHMd BVPLUS-OF-BVUMINUS-TIGHTEN-GEN-NO-SPLIT-dag
  (IMPLIES (AND (syntaxp (QUOTEP SIZE))
                (syntaxp (QUOTEP K))
                (syntaxp (QUOTEP N))
                (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (< XSIZE N)
                (NOT (EQUAL 0 X))
                (<= N SIZE)
                (NATP N)
                (UNSIGNED-BYTE-P-FORCED XSIZE X))
           (EQUAL (BVPLUS SIZE K (BVUMINUS N X))
                  (BVPLUS SIZE
                          (BVPLUS SIZE (- (EXPT 2 N) (EXPT 2 XSIZE))
                                  K)
                          (BVUMINUS XSIZE X))))
  :hints (("Goal" :use (:instance BVPLUS-OF-BVUMINUS-TIGHTEN-GEN-NO-SPLIT)
           :in-theory (disable BVPLUS-OF-BVUMINUS-TIGHTEN-GEN-NO-SPLIT))))

(defthmd bvlt-tighten-bind-and-bind-dag
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (< (max xsize ysize) size)
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y)
                (natp size)
                (posp xsize))
           (equal (bvlt size x y)
                  (bvlt (max xsize ysize) x y)))
  :hints (("Goal" :use (:instance bvlt-tighten-non-dag)
           :in-theory (disable bvlt-tighten-non-dag))))

(defthmd <-becomes-bvlt-dag-gen
  (implies (and (axe-bind-free (bind-bv-size-axe x 'free dag-array) '(free))
                ;;(syntaxp (quotep k))
               (unsigned-byte-p free k)
               (unsigned-byte-p-forced free x))
          (equal (< k x)
                 (bvlt free k x)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced)
           :use (:instance <-becomes-bvlt))))

(defthmd <-becomes-bvlt-dag-alt-gen
  (implies (and (axe-bind-free (bind-bv-size-axe x 'free dag-array) '(free))
                ;;(syntaxp (quotep k))
               (unsigned-byte-p free k)
               (unsigned-byte-p-forced free x))
          (equal (< x k)
                 (bvlt free x k)))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p-forced) (<-becomes-bvlt-free-alt <-becomes-bvlt-free))
           :use (:instance <-becomes-bvlt))))

(defthmd bvlt-of-constant-when-usb-dag
  (implies (and (syntaxp (quotep k))
                (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (<= (expt 2 xsize) (bvchop size k))
                (<= xsize size)
                (natp xsize) ;drop?
                (integerp size)
                (unsigned-byte-p-forced xsize x))
           (not (bvlt size k x)))
  :hints (("Goal" :use (:instance bvlt-of-constant-when-usb)
           :in-theory (disable bvlt-of-constant-when-usb))))


;gross?!
;crap x just gets put in for free before we can relieve the unsigned-byte-p-forced hyp..
(defthmd unsigned-byte-p-when-equal-bv-dag
  (implies (and (equal x free)
                (axe-bind-free (bind-bv-size-axe free 'freesize dag-array) '(freesize))
                (<= freesize size)
                (natp size)
                (unsigned-byte-p-forced freesize free))
           (equal (unsigned-byte-p size x)
                  t))
  :hints (("Goal" :in-theory (enable UNSIGNED-BYTE-P-FORCED))))


(defthmd plus-becomes-bvplus-dag
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y)
                (posp xsize))
           (equal (+ x y)
                  (bvplus (+ 1 (max xsize ysize)) x y)))
  :hints (("Goal" :use (:instance plus-becomes-bvplus)
           :in-theory (disable plus-becomes-bvplus))))


(defthmd equal-when-bv-sizes-differ-1-dag
  (implies (and (unsigned-byte-p free x)
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (< free ysize)
                )
           (equal (equal x y)
                  (and (unsigned-byte-p free y) ;use unsigned-byte-p-forced in a hyp???
                       (equal x (bvchop free y))))))

(defthmd unsigned-byte-p-of-bvplus-when-both-smaller
  (implies (and (axe-bind-free (bind-bv-size-axe x 'x-size dag-array) '(x-size))
                (axe-bind-free (bind-bv-size-axe y 'y-size dag-array) '(y-size))
                (< x-size 31)
                (< y-size 31)
                (natp x-size)
                (natp y-size)
                (unsigned-byte-p-forced x-size x)
                (unsigned-byte-p-forced y-size y))
           (equal (unsigned-byte-p '31 (bvplus '32 x y))
                  t))
  :hints (("Goal" :in-theory (e/d (bvlt bvplus unsigned-byte-p-forced)
                                  (anti-bvplus)))))

(defthmd plus-of-minus-one-and-bv-dag
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (posp xsize)
                (unsigned-byte-p-forced xsize x))
           (equal (+ -1 x)
                  (if (equal 0 x)
                      -1
                    (bvplus xsize -1 x))))
  :hints (("Goal" :in-theory (enable bvplus unsigned-byte-p-forced))))


;fixme put this back? Mon Jul 19 21:04:00 2010
;; (defthm bv-array-write-trim-index
;;   (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
;;                 (< 2 xsize)
;;                 (unsigned-byte-p-forced xsize x)
;;                 (natp xsize))
;;            (equal (bv-array-write '8 '4 x val data)
;;                   (if (bvle xsize 4 x)
;;                       (bvchop-list 8 (take 4 data))
;;                     (bv-array-write '8 '4 (bvchop 2 x) val data))))
;;   :hints (("Goal" :in-theory (e/d (unsigned-byte-p-forced bv-array-write update-nth2 bvlt)
;;                                   (update-nth-becomes-update-nth2-extend-gen)))))


(defthmd bvdiv-tighten-dag
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (< (max xsize ysize) size)
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y)
                (natp size)
                (posp xsize))
           (equal (bvdiv size x y)
                  (bvdiv (max xsize ysize) x y)))
  :hints (("Goal" :use (:instance bvdiv-tighten)
           :in-theory (disable bvdiv-tighten))))


;fffixme
;improve other rules like this!
(defthmd <-becomes-bvlt-dag-gen-better
  (implies (and (axe-bind-free (bind-bv-size-axe x 'free dag-array) '(free)) ;ffffixme here and elsewhere abstain if x is a quotep?!! ;why?
                (syntaxp (not (quotep x)))
                (natp free)
                (integerp k)
                (unsigned-byte-p-forced free x))
           (equal (< k x)
                  ;;redid conc
                  (boolor (< k 0)
                          (booland (unsigned-byte-p free k)
                                   (bvlt free k x)))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced unsigned-byte-p)
           :use (:instance <-becomes-bvlt-dag-gen))))

;can loop when x=0?
;this one lacks the not quote hyp but requires x not to be 0
(defthmd <-becomes-bvlt-dag-gen-better2
  (implies (and (axe-bind-free (bind-bv-size-axe x 'free dag-array) '(free)) ;ffffixme here and elsewhere abstain if x is a quotep?!! ;why? can loop if k is a difference?
                (syntaxp (not (quotep x)))
                (not (equal x 0))
                (natp free)
                (integerp k)
                (unsigned-byte-p-forced free x))
           (equal (< k x)
;;redid conc to use bool ops
                  (boolor (< k 0)
                          (booland (unsigned-byte-p free k) ;fixme this can loop when k is a difference? because of UNSIGNED-BYTE-P-OF-+-OF-MINUS
                                   (bvlt free k x)))))
  :hints (("Goal" :use (:instance <-becomes-bvlt-dag-gen-better)
           :in-theory (disable <-becomes-bvlt-dag-gen-better))))

(defthmd bvlt-tighten-arg2
  (implies (and (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (syntaxp (not (quotep y)))
                (< ysize size)
                (natp size)
                (natp ysize)
                (unsigned-byte-p-forced ysize y))
           (equal (bvlt size y x)
                  ;redid conc:
                  (boolor (not (unsigned-byte-p ysize (bvchop size x)))
                          (bvlt ysize y x))))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p-forced bvlt
                                                          ;unsigned-byte-p
                                                          )
                                  (bvlt-tighten-non-dag
                                   UNSIGNED-BYTE-P-OF-BVCHOP-BIGGER2)))))


(defthmd bvlt-tighten-arg1
  (implies (and (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (syntaxp (not (quotep y))) ;needed?
                (< ysize size)
                (natp size)
                (natp ysize)
                (unsigned-byte-p-forced ysize y))
           (equal (bvlt size x y)
                  ;;redid conc:
                  (booland (unsigned-byte-p ysize (bvchop size x))
                           (bvlt ysize x y))))
  :hints (("Goal"
           :use (bvchop-tighten
                 (:instance <-of-bvchop-and-bvchop-same (s2 ysize) (s1 size) (x y)))
           :in-theory (e/d (unsigned-byte-p-forced bvlt
                                                   booland
                                                   ;bvchop
                                                   ;unsigned-byte-p
                                                   )
                           (<-of-bvchop-and-bvchop-same
                            BVCHOP-WHEN-<-TIGHTEN
                            bvlt-tighten-non-dag
                            UNSIGNED-BYTE-P-OF-BVCHOP-BIGGER2)))))

(defthmd bvmult-tighten-dag-power-of-2
  (implies (and (syntaxp (quotep x))
                (natp x)
                (power-of-2p x)
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (< (+ (lg x) ysize) size)
                (natp size)
                (natp ysize)
                (unsigned-byte-p-forced ysize y))
           (equal (bvmult size x y)
                  (bvmult (+ (lg x) ysize) x y)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced bvmult power-of-2p posp lg))))

(defthmd plus-of-minus-becomes-bv-dag
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p xsize y) ;this has been expensive
                (not (bvlt xsize x y))
                (natp xsize)
                (unsigned-byte-p-forced xsize x))
           (equal (+ x (- y))
                  (bvplus xsize x (bvuminus xsize y))))
  :hints (("Goal" :use ((:instance minus-becomes-bv (free xsize)))
           :in-theory (e/d (unsigned-byte-p-forced) ( minus-becomes-bv)))))

(defthmd plus-of-minus-becomes-bv-dag-alt
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p xsize y)
                (not (bvlt xsize x y))
                (natp xsize)
                (unsigned-byte-p-forced xsize x))
           (equal (+ (- y) x)
                  (bvplus xsize x (bvuminus xsize y))))
  :hints (("Goal" :use (:instance plus-of-minus-becomes-bv-dag)
           :in-theory (disable plus-of-minus-becomes-bv-dag))))


;; ;gen the 32
;; (defthm floor-of-when-usb-bind-free-dag-32
;;   (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
;;                 (unsigned-byte-p-forced xsize x))
;;            (equal (floor x 32)
;;                   (slice (+ -1 xsize) 5 x)))
;;   :hints (("Goal" :in-theory (e/d (UNSIGNED-BYTE-P-FORCED natp slice logtail unsigned-byte-p floor-bounded-by-/)
;;                                   (anti-slice)))))

;kind of gross?
;more like this?
(defthmd <-of-+-of-minus-and-bv
  (implies (and (axe-bind-free (bind-bv-size-axe k 'ksize dag-array) '(ksize))
                (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (natp y)
                (natp xsize) ;drop?
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ksize k))
           (equal (< (+ x (- y)) k)
                  (if (< x y)
                      t
                    (< (bvplus xsize x (bvuminus xsize y)) k))))
  :hints (("Goal" :use (:instance plus-of-minus-becomes-bv-dag)
           :in-theory (e/d (unsigned-byte-p-forced usb-hack-100 bvlt bvplus bvuminus bvminus)
                           (plus-of-minus-becomes-bv-dag BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))

(defthmd equal-of-+-of-minus-and-bv
  (implies (and (axe-bind-free (bind-bv-size-axe k 'ksize dag-array) '(ksize))
                (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (natp y)
                (natp xsize) ;drop?
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ksize k))
           (equal (equal k (+ x (- y)))
                  (if (< x y)
                      nil
                    (equal k (bvplus xsize x (bvuminus xsize y))))))
  :hints (("Goal" :use (:instance plus-of-minus-becomes-bv-dag)
           :in-theory (e/d (unsigned-byte-p-forced usb-hack-100 bvlt bvplus bvuminus bvminus)
                           (plus-of-minus-becomes-bv-dag BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))

(defthmd +-of-minus-bind-free
  (implies (and (syntaxp (quotep k))
                (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p xsize k)
                (bvle xsize k x)
                (natp xsize)
                (unsigned-byte-p-forced xsize x))
           (equal (binary-+ (- k) x)
                  (bvplus xsize (- k) x)))
  :hints (("Goal" :in-theory (enable bvplus bvlt ;unsigned-byte-p
                                     unsigned-byte-p-forced
                                     ))))

(defthmd +-of-minus-bind-free-constant-version
  (implies (and (syntaxp (quotep k))
                (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p xsize (- k))
                (bvle xsize (- k) x)
                (natp xsize)
                (unsigned-byte-p-forced xsize x))
           (equal (binary-+ k x)
                  (bvplus xsize k x)))
  :hints (("Goal" :use (:instance +-of-minus-bind-free (k (- k)))
           :in-theory (disable +-of-minus-bind-free))))

(defthmd <-of-constant-and-+-of-minus
  (implies (and (syntaxp (quotep k))
                (natp k)
                (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (natp y)
                (unsigned-byte-p xsize k) ;drop?
                (unsigned-byte-p-forced xsize x))
           (equal (< k (+ x (- y)))
                  (if (<= y x)
                      (bvlt xsize k (bvplus xsize x (bvuminus xsize y)))
                    nil)))
  :hints (("Goal"
           :cases ((unsigned-byte-p xsize y))
           :in-theory (e/d (bvplus bvlt bvuminus bvchop-of-sum-cases bvminus UNSIGNED-BYTE-P-FORCED
                                   UNSIGNED-BYTE-P-when-UNSIGNED-BYTE-P-free-better)
                           (bvminus-becomes-bvplus-of-bvuminus)))))

(defthmd equal-of-floor-of-expt-and-bv-constant-version-dag
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (power-of-2p k)
                (natp (lg k))
                (posp xsize)
                (unsigned-byte-p-forced xsize x)
                (integerp y))
           (equal (equal (floor y k) x)
                  (if (< y 0)
                      nil
                    (if (<= (expt 2 (+ xsize (lg k))) y)
                        nil
                      (equal (slice (+ -1 xsize (lg k)) (lg k) y) x)))))
  :hints (("Goal" :use (:instance equal-of-floor-of-expt-and-bv (n (lg k)))
           :in-theory (enable unsigned-byte-p-forced))))

;gen!
(defthmd <-of-diff-of-bv-and-constant
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (<= (expt 2 xsize) k)
                (natp y)
                (unsigned-byte-p-forced xsize x))
           (< (+ x (- y)) k))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthmd nth-of-plus-of-bv-and-minus
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (natp y)
                (unsigned-byte-p-forced xsize x))
           (equal (nth (+ x (- y)) lst)
                  (if (<= y x)
                      (nth (bvplus xsize x (- y)) lst)
                    (nth 0 lst))))
  :hints (("Goal" :in-theory (e/d (bvplus bvminus bvuminus unsigned-byte-p-forced nth) (;NTH-OF-CDR
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
  :hints (("Goal" :in-theory (enable bvplus bvminus bvuminus unsigned-byte-p-forced))))

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

(defthmd <-of-constant-and-+-of-bv-and-minus
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (<= 0 k) ;could this be expensive?
                (natp y)
                (unsigned-byte-p-forced xsize x))
           (equal (< k (+ x (- y)))
                  (if (<= y x)
                      (< k (bvplus xsize x (- y)))
                    nil)))
  :hints (("Goal" :cases ((unsigned-byte-p xsize y))
           :in-theory (enable natp
                              unsigned-byte-p-forced bvplus bvchop-of-sum-cases ;yuck
                              UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-FREE-BETTER))))

(defthmd <-of-constant-and-+-of-minus-and-bv
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (<= 0 k) ;could this be expensive?
                (natp y)
                (unsigned-byte-p-forced xsize x))
           (equal (< k (+ (- y) x))
                  (if (<= y x)
                      (< k (bvplus xsize x (- y)))
                    nil)))
  :hints (("Goal" :use (:instance <-of-constant-and-+-of-bv-and-minus)
           :in-theory (disable <-of-constant-and-+-of-bv-and-minus))))

(defthmd +-of-minus-1-and-bv2-alt-bind-free
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p-forced xsize x))
           (equal (+ -1 (+ x y))
                  (if (equal x 0) (+ -1 y) (+ y (bvplus xsize -1 x)))))
  :hints (("Goal" :use (:instance +-of-minus-1-and-bv2 (free xsize))
           :in-theory (e/d (unsigned-byte-p-forced natp ;yuck
                                                   ) ( +-of-minus-1-and-bv2)))))



;put this in place
(defthmd <-becomes-bvlt-dag-alt-gen-better
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (syntaxp (not (quotep x))) ;why?
                (integerp y) ;drop?
                (unsigned-byte-p-forced xsize x))
           (equal (< x y)
                  (if (< y 0) ;was <= but i prefer not to split on whether y=0
                      nil
                    (if (unsigned-byte-p xsize y)
                        (bvlt xsize x y)
                      t))))
  :hints (("Goal" :use (:instance <-becomes-bvlt-dag-alt-gen (k y) ( free xsize))
           :in-theory (e/d (unsigned-byte-p-when-unsigned-byte-p-free-better unsigned-byte-p-forced)
                           (<-becomes-bvlt-dag-alt-gen)))))

;fixme think about when x=0
(defthmd <-becomes-bvlt-dag-alt-gen-better2
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
;;;                (syntaxp (not (quotep x))) ;why?
                (integerp y) ;drop?
                (unsigned-byte-p-forced xsize x))
           (equal (< x y)
                  (if (< y 0) ;was <= but i prefer not to split on whether y=0
                      nil
                    (if (unsigned-byte-p xsize y)
                        (bvlt xsize x y)
                      t))))
  :hints (("Goal" :use (:instance <-becomes-bvlt-dag-alt-gen-better)
           :in-theory (disable <-becomes-bvlt-dag-alt-gen-better))))

(defthmd <-of-+-of-minus-becomes-bvlt
  (implies (and (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p ysize k) ;add (syntaxp (quotep k))?
                (natp x)
                (unsigned-byte-p-forced ysize y)
                )
           (equal (< (+ (- x) y) k)
                  (if (< y x)
                      t
                    (bvlt ysize (bvplus ysize (bvuminus ysize x) y) k))))
  :hints (("Goal"
           :cases ((unsigned-byte-p ysize x))
           :in-theory (enable bvlt bvplus bvuminus bvminus bvchop-of-sum-cases unsigned-byte-p-forced
                              UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-FREE-BETTER))))

(defthmd <-of-constant-and-+-of-bv-and-minus-and-bv
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe z 'zsize dag-array) '(zsize))
                (<= 0 k)
                (natp y)
                (natp xsize)
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced zsize z))
           (equal (< k (+ x (- y) z))
                  (if (<= y (+ x z))
                      (< k (bvplus (+ 1 (max xsize zsize)) (bvplus (+ 1 (max xsize zsize)) x z) (- y)))
                    nil)))
  :hints (("Goal" :use (:instance <-of-constant-and-+-of-minus-and-bv (x (+ x z)) (xsize (+ 1 (max xsize zsize))))
           :in-theory (e/d (unsigned-byte-p-forced BVPLUS-OF-PLUS-ARG2)
                           (<-of-constant-and-+-of-minus-and-bv
                            SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE)))))

(defthmd equal-of-constant-and-+-of-minus-and-bv
  (implies (and (syntaxp (quotep k))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (posp k)
                (natp ysize)
                (natp x)
                (unsigned-byte-p-forced ysize y)
                )
           (equal (equal k (+ (- x) y))
                  (if (< x y)
                      (equal k (bvminus ysize y x))
                    nil)))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p-forced bvminus bvuminus bvplus bvchop-of-sum-cases)
                                  (<-OF-BVCHOP-HACK ;why?
                                   )))))

(defthmd unsigned-byte-p-of-smaller
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (< size xsize)
                (natp xsize)
                (natp size)
                (unsigned-byte-p-forced xsize x))
           (equal (unsigned-byte-p size x)
                  (equal 0 (slice (+ -1 xsize) size x))))
  :hints (("Goal"
           :cases (equal size xsize)
           :use (:instance split-bv (y x) (n xsize) (m size))
           :in-theory (e/d (unsigned-byte-p-forced) (BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE bvcat-of-bvchop-low)))))


;gen
;fixme what if this loops?
(defthmd bvplus-of-bvplus-of-constant-and-short-expand
  (implies (and (syntaxp (quotep k))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (< ysize 32)
                (natp ysize)
                (integerp k)
                (< (bvchop 32 k) (- (expt 2 30) (expt 2 ysize))) ;should get computed (shows that there is no oveflow)
                (unsigned-byte-p-forced ysize y)
                )
           (equal (bvplus '32 x (bvplus '30 k y))
                  (bvplus '32 x (bvplus '32 k y))))
  :hints (("Goal" :use (:instance  bvplus-of-bvplus-of-constant-and-short-expand-helper (k (bvchop 32 k)))))
; :hints (("Goal" :in-theory (enable bvlt bvplus bvchop-of-sum-cases UNSIGNED-BYTE-P-FORCED)))
  )

(defthmd *-becomes-bvmult-2
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p ysize y)
                (unsigned-byte-p-forced xsize x)
                )
           (equal (* x y) (bvmult (+ ysize xsize) x y)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced)
           :use (:instance *-becomes-bvmult-non-dag (n xsize) (m ysize)))))

(defthmd *-becomes-bvmult-3
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p ysize y)
                (unsigned-byte-p-forced xsize x)
                )
           (equal (* y x) (bvmult (+ ysize xsize) x y)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced)
           :use (:instance *-becomes-bvmult-non-dag (n xsize) (m ysize)))))


;fixme use signed comparisons more when values can go negative?!
(defthmd unsigned-byte-p-of-+-of-minus2
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (<= (+ 1 n) xsize)
                (<= (+ 1 n) ysize)
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y)
                (natp n))
           (equal (unsigned-byte-p n (+ (- x) y))
                  (and (sbvle (+ 1 (max xsize ysize)) 0 (+ (- x) y))
                       (sbvlt (+ 1 (max xsize ysize)) (+ (- x) y) (expt 2 n)))))
  :hints (("Goal"
;           :cases ((equal 1 (GETBIT 29 X)))
           :in-theory (enable bvlt sbvlt bvplus bvuminus bvminus bvchop-of-sum-cases unsigned-byte-p-forced getbit-of-plus))))

;move
(defthm <-of-if-arg1-safe
  (implies (syntaxp (quotep k))
           (equal (< (if test x y) k)
                  (if test (< x k) (< y k)))))

;move
(defthmd bvchop-identity-when-<=
  (implies (and (unsigned-byte-p size x)
                (unsigned-byte-p size y)
                (<= y x))
           (equal (bvchop size (+ x (- y)))
                  (+ x (- y))))
;  :hints (("Goal" :use (:instance bvchop-identity (i (+ x (- y))))))
  :hints (("Goal" :in-theory (disable expt
                                      UNSIGNED-BYTE-P-OF-+-OF-MINUS-BETTER-HELPER ;yuck
                                      )))
  )

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
                                          bvchop-identity-when-<=)
                                  (UNSIGNED-BYTE-P-OF-+-OF-MINUS
                                   FIRSTN-BECOMES-TAKE-GEN)))))

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

(defthmd unsigned-byte-p-of-+-of-minus-better
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (<= n (max xsize ysize))
                (natp n)
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y))
           (equal (unsigned-byte-p n (+ x (- y)))
                  (if (bvlt (+ 1 (max xsize ysize)) x y)
                      nil ;because (+ x (- y)) is negative
                    (bvlt (+ 1 (max xsize ysize)) (bvminus (+ 1 (max xsize ysize)) x y) (expt 2 n)))))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-+-of-minus-better-helper (size (max xsize ysize)))
           :in-theory (enable unsigned-byte-p-forced))))

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
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p-forced nth-when-all-same) (all-same
                                                                                   ;CAR-BECOMES-NTH-OF-0 ;looped
                                                                                   )))))
;gen!
(defthmd equal-of-constant-and-bvchop-when-bvlt
  (implies (and (axe-rewrite-objective 't)
                (bvlt 6 x free)
                (bvlt 6 free 32)
                (unsigned-byte-p 6 free)
;(natp free)
                )
           (equal (equal k (bvchop 6 x))
                  (equal k (bvchop 5 x))))
  :hints (("Goal"
           :use (:instance split-bv (y (bvchop 6 x)) (n 6) (m 5))
           :in-theory (e/d (bvlt ;UNSIGNED-BYTE-P
                            )
                           (bvcat-of-bvchop-low bvcat-of-getbit-and-x-adjacent
                                                 bvcat-equal-rewrite-alt
                                                 bvcat-equal-rewrite
                                                 REWRITE-<-WHEN-SIZES-DONT-MATCH2
                                                 GETBIT-WHEN-BVLT-OF-SMALL)))))

(defthmd bvlt-of-constant-arg2-weaken
  (implies (and (syntaxp (quotep k))
                (axe-rewrite-objective 't)
                (not (equal k (bvchop size x))) ;can this loop?
                (unsigned-byte-p size k)
                (natp size)
                (< 0 k))
           (equal (bvlt size k x)
                  (bvlt size (+ -1 k) x)))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthmd bvlt-of-constant-arg2-strengthen
  (implies (and (syntaxp (quotep k))
                (axe-rewrite-objective 'nil)
                (not (equal free (bvchop size x))) ;can this loop?
                (syntaxp (quotep free))
                (equal free (+ 1 k)) ;gets computed
                (unsigned-byte-p size k)
                (< k (+ -1 (expt 2 size)))
                (natp size))
           (equal (bvlt size k x)
                  (bvlt size (+ 1 k) x)))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthmd bvlt-of-constant-arg3-strengthen
  (implies (and (syntaxp (quotep k))
                (< 0 k)
                (axe-rewrite-objective 'nil)
                (not (equal free (bvchop size x))) ;can this loop?
                (syntaxp (quotep free))
                (equal free (+ -1 k))
                (unsigned-byte-p size k)
                (natp size)
                )
           (equal (bvlt size x k)
                  (bvlt size x (+ -1 k))))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthmd bvlt-of-constant-arg3-weaken
  (implies (and (syntaxp (quotep k))
                (axe-rewrite-objective 't)
                (not (equal k (bvchop size x))) ;can this loop?
                (unsigned-byte-p size k)
                (< k (+ -1 (expt 2 size)))
                (natp size))
           (equal (bvlt size x k)
                  (bvlt size x (+ 1 k))))
  :hints (("Goal" :in-theory (enable bvlt))))

;gen
(defthm bvlt-must-be-axe
  (implies (and (axe-rewrite-objective 't)
                (bvlt 6 free x)
                (equal free (+ -1 k))
                (< 0 k)
                (unsigned-byte-p 6 k)
                )
           (equal (bvlt 6 k x)
                  (not (equal k (bvchop 6 x)))))
  :hints (("Goal" :in-theory (e/d (bvlt bvchop-of-sum-cases bvminus) (<-OF-+-OF-MINUS-AND-CONSTANT)))))

;; (defthmd equal-of-bvchop-extend-when-bvlt
;;   (implies (and (axe-rewrite-objective 'nil)
;;                 (syntaxp (quotep k))
;;                 (bvlt size2 x free) ;x is bounded such that its top bit must be 0 (fixme make a version for 1...)
;;                 (syntaxp (quotep free))
;;                 (equal size2 (+ 1 size));fixme gen
;;                 (bvle size2 free (expt 2 size))
;;                 ;(natp size)
;;                 (unsigned-byte-p size k) ;move
;;                 )
;;            (equal (equal k (bvchop size x))
;;                   (equal k;(bvcat 1 free size k)
;;                          (bvchop (+ 1 size) x))))
;;   :hints (("Goal" :use (:instance equal-of-bvchop-extend (free 0)))))

(defthmd equal-of-bvchop-extend-when-bvlt
  (implies (and (axe-rewrite-objective 'nil)
                (syntaxp (quotep k))
                (bvlt size2 x free) ;x is bounded such that its top bit must be 0 (fixme make a version for 1...)
                (syntaxp (quotep free))
                (< size size2)
                (bvle size2 free (expt 2 size))
                (natp size))
           (equal (equal k (bvchop size x))
                  (equal k (bvchop size2 x))))
  :hints (("Goal" :use (:instance equal-of-bvchop-extend-when-bvlt-helper))))

;; (defthmd equal-of-bvchop-extend-when-not-bvlt
;;   (implies (and (axe-rewrite-objective 'nil)
;;                 (syntaxp (quotep k))
;;                 (not (bvlt size2 free x)) ;x is bounded such that its top bit must be 0 (fixme make a version for 1...)
;;                 (syntaxp (quotep free))
;;                 (equal size2 (+ 1 size)) ;fixme gen
;;                 (bvle size2 (+ 1 free) (expt 2 size))
;;                 (unsigned-byte-p size2 free)
;;                 (< free (+ -1 (expt 2 (+ 1 size)))) ;no overflow
;;                 (unsigned-byte-p size k) ;move
;;                 )
;;            (equal (equal k (bvchop size x))
;;                   (equal k ;(bvcat 1 free size k)
;;                          (bvchop (+ 1 size) x))))
;;   :hints (("Goal" :in-theory (enable bvlt)
;;            :use (:instance equal-of-bvchop-extend-when-bvlt (free (+ 1 free))))))

(defthmd equal-of-bvchop-extend-when-not-bvlt
   (implies (and (axe-rewrite-objective 'nil)
                 (syntaxp (quotep k))
                 (not (bvlt size2 free x)) ;x is bounded such that its top bits must be 0 (fixme make a version for 1... and maybe other values?)
                 (syntaxp (quotep free))
                 (< size size2)
                 (bvlt size2 free (expt 2 size))
                 (natp size)
                 (natp size2)
                 )
            (equal (equal k (bvchop size x))
                   (equal k (bvchop size2 x))))
   :hints (("Goal" :use (:instance equal-of-bvchop-extend-when-not-bvlt-helper)
            :in-theory (disable equal-of-bvchop-extend-when-not-bvlt-helper))))
