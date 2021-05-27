; A function to divide a list into fixed-sized chunks
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;stuff about the function group, which chops a list into segments
;; TODO: harvest good lemmas from this book

(include-book "kestrel/utilities/myif" :dir :system) ;drop?
(include-book "firstn-def")
(include-book "subrange-def")
(include-book "kestrel/typed-lists-light/items-have-len" :dir :system)
(include-book "kestrel/typed-lists-light/all-true-listp" :dir :system)
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor2" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/arithmetic-light/ceiling" :dir :system))
(local (include-book "kestrel/arithmetic-light/integerp" :dir :system))
(local (include-book "nth"))
(local (include-book "len"))
(local (include-book "cdr"))
(local (include-book "cons"))
(local (include-book "append"))
(local (include-book "subrange"))
(local (include-book "take"))
(local (include-book "nthcdr"))
(local (include-book "firstn"))
(local (include-book "true-list-fix"))
(local (include-book "kestrel/library-wrappers/ihs-quotient-remainder-lemmas" :dir :system)) ;drop, for FLOOR-BOUNDed-by-/
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divides" :dir :system))

;; todo: consider putting back the stuff that uses list::equiv

;(local (in-theory (disable LIST::FIRSTN-1-REWRITE-STRONG)))

;(in-theory (disable list::equal-append-reduction!-alt list::equal-append-reduction!))
(local (in-theory (disable equal-of-append)))

;todo: move some of these rules:

(defthmd integerp-of-small-helper
  (implies (and (< x n)
                (posp x)
                (posp n))
           (not (integerp (* (/ n) x))))
  :hints (("Goal" :in-theory (enable)
           :cases ((< (* (/ n) x) 0)
                   (<= 1 (* (/ n) x))))))

;make an alt rule
;simplify the rhs more?
(defthm integerp-of-small-helper-2
  (implies (and (< x n)
                (natp x)
                (posp n))
           (equal (integerp (* (/ n) x))
                  (equal 0 (* (/ n) x))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil)))
  :hints (("Goal" :in-theory (enable integerp-squeeze)
           :cases ((< (* (/ n) x) 0)
                   (<= 1 (* (/ n) x))))))

;limit?
(defthm integerp-of-small
  (implies (and (< x n)
                (natp x)
                (posp n))
           (equal (integerp (* (/ n) x))
                  (equal x 0)))
  :hints (("Goal" :use (:instance integerp-of-small-helper)
           :in-theory (disable integerp-of-small-helper))))

(defthm <-of-/-same
  (implies (and (< 0 x)
                (< 1 n) ;allow =?
                (rationalp n)
                (rationalp x))
           (not (< x (/ x n))))
  :hints (("Goal" :in-theory (enable ;<-unary-/-positive-right
                              ))))

(defthm <-of-floor-same
  (implies (and (natp x)
                (< 0 x)
                (<= 1 n)
                (rationalp n))
           (equal (< (floor x n) x)
                  (not (equal 1 n))))
  :hints (("Goal"
           :use (<-of-/-same
                 (:instance FLOOR-BOUNDed-by-/ (y n)))
           :in-theory (e/d (posp)
                           (<-of-/-same
                            ;<-*-/-LEFT-COMMUTED
                            FLOOR-BOUNDed-by-/
                            my-FLOOR-UPPER-BOUND)))))

(defthm +-of-minus-and-*-same
  (implies (and (syntaxp (quotep k))
                (rationalp n))
           (equal (+ (- n) (* k n))
                  (* (+ -1 k) n))))

;can loop with the definition of subrange?
;move
(defthm cdr-of-firstn
  (implies (and (<= n (len x))
                (natp n))
           (equal (cdr (firstn n x))
                  (subrange 1 (+ -1 n) x)))
  :hints (("Goal" :in-theory (e/d (subrange)
                                  (;anti-subrange
                                   )))))

;can loop with defn subrange?
;move
(defthmd firstn-of-cdr-becomes-subrange
  (implies (and (<= (+ 1 n) (len x))
                (natp n))
           (equal (firstn n (cdr x))
                  (subrange 1 (+ n) x)))
  :hints (("Goal" :in-theory (e/d (subrange)
                                  (;anti-subrange
                                   )))))

;;  :hints (("Goal" :in-theory (enable take firstn))))

;move
(defthm *-of-/-same-alt
  (implies (and (rationalp n)
                (rationalp x)
                (not (equal 0 n)))
           (equal (* (/ n) n x)
                  x)))

(defthmd floor-bound-hack-1
  (implies (and (posp j)
                (natp i))
           (implies (<= 2 (FLOOR i j))
                    (<= (* 2 j) i)))
  :hints (("Goal"
           :use ((:instance my-FLOOR-UPPER-BOUND)
                 ;(:instance <-*-/-LEFT (x i) (a 2) (y j))
                 )
           :in-theory (disable my-FLOOR-UPPER-BOUND
                               my-FLOOR-UPPER-BOUND
                               ))))

;gen the 1 !
(defthmd floor-bound-hack-2
  (IMPLIES (AND (EQUAL (FLOOR I J) 1)
                (POSP J)
                (NATP I))
           (< I (* 2 J)))
  :hints (("Goal"
           :use ( ;(:instance FLOOR-UPPER-BOUND-better (x i) (y j))
                 (:instance my-FLOOR-lower-BOUND))
           :in-theory (disable my-FLOOR-UPPER-BOUND
                               my-FLOOR-UPPER-BOUND
                               ))))


(defthm floor-bound-hack-3
  (implies (and (posp j)
                (natp i))
           (equal (<= 2 (FLOOR i j))
                  (<= (* 2 j) i)))
  :hints (("Goal" :in-theory (enable floor-bound-hack-2 floor-bound-hack-1))))

(defthm floor-bound-hack-4
  (implies (and (posp j)
                (natp i))
           (equal (< 1 (FLOOR i j))
                  (<= (* 2 j) i)))
  :hints (("Goal" :use (:instance floor-bound-hack-3)
           :in-theory (disable floor-bound-hack-3))))

(local (in-theory (enable floor-must-be-1)))


;;(EQUAL (FIRSTN N X) (LIST (NTH 0 X)))

(defthm posp-of-one-less
  (implies (posp n)
           (equal (posp (+ -1 n))
                  (not (equal 1 n))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))



(defthm <-of-+-cancel-first-and-first
  (equal (< (+ x y) (+ x z))
         (< y z)))


;; (defthm cdr-of-firstn
;;   (implies (and (natp n)
;;                 (< n (len lst)) ;move to conc?
;;                 )
;;            (equal (cdr (firstn n lst))
;;                   (subrange 1 (+ -1 n) lst)))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (e/d (subrange) (take-of-nthcdr-becomes-subrange
;;                                        cdr-of-take-becomes-subrange
;;                                        cdr-of-take-becomes-subrange-better)))))

(defthm firstn-of-subrange-gen
  (implies (and (<= i (+ 1 (- end start)))
                (natp start)
                (natp end)
                (natp i))
           (equal (firstn i (subrange start end lst))
                  (subrange start (+ start i -1) lst))))

;; (LIST::EQUIV Y (CDR Y))

(defthm <-of-times-of-floor-and-same
  (implies (and (rationalp i)
                (rationalp j)
                (< 0 j))
           (equal (< (* j (floor i j)) i)
                  (not (integerp (/ i j)))))
  :hints (("Goal" :use (:instance my-floor-upper-bound (x i) (y j))
           :in-theory (disable my-floor-upper-bound))))

(defthm <-of-times-of-floor-and-same-hack
  (implies (and (integerp i)
                (integerp j)
                (< 0 j))
           (equal (< i (+ 1 (* j (FLOOR i j))))
                  (integerp (/ i j))))
  :hints (("Goal" :use (:instance <-of-times-of-floor-and-same)
           :in-theory (disable <-of-times-of-floor-and-same))))

;use polarity?
(defthm <-+-floor-lemma
  (implies (and (integerp i)
                (integerp j)
                (< 0 j))
           (equal (< (+ 1 (* j (FLOOR i j))) i)
                  (not (or (integerp (/ i j))
                           (equal i (+ 1 (* j (FLOOR i j))))))))
  :hints (("Goal" :use (:instance my-floor-upper-bound)
           :in-theory (disable my-floor-upper-bound
;                               floor-bound-lemma3
                               ))))

(defthm firstn-of-nthcdr-lemma
  (implies (and (natp n)
                (<= n (len x)))
           (equal (firstn (+ (- n) (len x)) (nthcdr n x))
                  (nthcdr n (true-list-fix x)))))

;(in-theory (enable LIST::NTH-APPEND))

;move
;also make a firstn-of-cdr-better?
(defthm cdr-of-firstn-better
  (equal (cdr (firstn n x))
         (subrange 1 (+ -1 (min (nfix n) (len x))) x))
  :hints (("Goal" :expand ((SUBRANGE 1 (+ -1 N) X)
                           (subrange 1 (+ -1 (min (nfix n) (len x))) x))
           :in-theory (enable))))

;only makes sense when (len x) is a multiple of n?
(defund group (n x)
  (declare (xargs :measure (+ 1 (len x))
                  :guard (and (true-listp x) ;would be nice for firstn's guard to not require true-listp
                              (posp n))))
  (if (or (not (mbt (posp n)))
          (atom x))
      nil
    (cons (firstn n x)
          (group n (nthcdr n x)))))

(defthm consp-of-group
  (implies (posp n)
           (equal (consp (group n list))
                  (consp list)))
  :hints (("Goal" :in-theory (enable group))))

;drop?
(defthm endp-of-group
  (implies (posp n)
           (equal (endp (group n list))
                  (endp list)))
  :hints (("Goal" :in-theory (enable endp))))

(defthm cdr-of-group
  (implies (posp n)
           (equal (cdr (group n list))
                  (group n (nthcdr n list))))
  :hints (("Goal" :in-theory (enable group))))

(defthm car-of-group
  (implies (posp n)
           (equal (car (group n list))
                  (firstn n list)))
  :hints (("Goal" :in-theory (enable group))))

(defthm len-of-group
  (implies (posp n)
           (equal (len (group n list))
                  (ceiling (len list) n)))
  :hints (("Goal" :in-theory (enable group
                                     CEILING-IN-TERMS-OF-FLOOR))))

(defthm group-of-cons
  (implies (posp n)
           (equal (group n (cons a x))
                  (cons (cons a (firstn (+ -1 n) x))
                        (group n (nthcdr (+ -1 n) x)))))
  :hints (("Goal" ;:induct (group n x)
           :do-not '(generalize eliminate-destructors)
           :expand ((GROUP N (CONS A X))
                    (group n x))
           :in-theory (e/d (group)
                           (firstn-becomes-take
;                            list::firstn-does-nothing
                            firstn-becomes-take-gen
                            floor-bounded-by-/
                            ;small-int-hack
;                            list::nthcdr-when-<=
                            )))))

;remove n?
(defun firstn-of-group-induct (x n m)
  (if (zp m)
      (list x n m)
    (firstn-of-group-induct (nthcdr n x) n (+ -1 m))))

(local (in-theory (disable NTHCDR-OF-TRUE-LIST-FIX)))


;move
(defthm firstn-of-nthcdr
  (implies (and (natp n1)
                (natp n2))
           (equal (firstn n1 (nthcdr n2 x))
                  (nthcdr n2 (firstn (+ n1 n2) x))))
  :hints (("Goal" :in-theory (e/d (firstn
                                   TRUE-LIST-FIX-OF-NTHCDR
                                   NTHCDR-WHEN-<-OF-LEN) ()))))

(defthm firstn-of-group
  (implies (and (posp n)
                (natp m))
           (equal (firstn m (group n x))
                  (group n (firstn (* m n) x))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((GROUP N (FIRSTN (* M N) X)))
           :induct (firstn-of-group-induct x n m)
           :in-theory (e/d (group ;firstn
                            )
                           (NTHCDR-OF-CDR-COMBINE NTHCDR-OF-CDR-COMBINE-STRONG
                                                  FIRSTN-BECOMES-TAKE
                                                  firstn-becomes-take-gen)))))

(defthm take-of-group
  (implies (and (posp n)
                (natp m)
                (<= m (ceiling (len x) n)))
           (equal (take m (group n x))
                  (group n (firstn (* m n) x))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((GROUP N (take (* M N) X)))
           :induct (firstn-of-group-induct x n m)
           :in-theory (e/d (group ;firstn
                            )
                           (NTHCDR-OF-CDR-COMBINE
                            NTHCDR-OF-CDR-COMBINE-STRONG
                            FIRSTN-BECOMES-TAKE
                            firstn-becomes-take-gen)))))

(defthm nthcdr-of-group
  (implies (and (posp n)
                (natp m))
           (equal (nthcdr m (group n x))
                  (group n (nthcdr (* m n) x))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;          :expand ((GROUP N (FIRSTN (* M N) (NTHCDR N X))))
           :induct (firstn-of-group-induct x n m)
           :in-theory (e/d (group nthcdr)
                           (NTHCDR-OF-CDR-COMBINE NTHCDR-OF-CDR-COMBINE-STRONG)))))

;use subrange?
(defthm nth-of-group
  (implies (and (natp m)
                (posp n))
           (equal (nth m (group n x))
                  (firstn n (nthcdr (* m n) x))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;          :expand ((GROUP N (FIRSTN (* M N) (NTHCDR N X))))
           :expand ((GROUP N X))
           :induct (firstn-of-group-induct x n m)
           :in-theory (e/d (group nthcdr ;LIST::NTH-OF-CONS
                                  )
                           (NTHCDR-OF-CDR-COMBINE NTHCDR-OF-CDR-COMBINE-STRONG)))))

(defthm group-when-not-consp
  (implies (not (consp x))
           (equal (group n x)
                  nil))
  :hints (("Goal" :in-theory (enable group))))

(defthm group-of-true-list-fix
  (equal (group n (true-list-fix x))
         (group n x))
  :hints (("Goal" :in-theory (enable group
                                     TRUE-LIST-FIX-OF-NTHCDR))))

;; ;move
;; (defthm subrange-of-cdr
;;   (implies (natp end)
;;            (equal (subrange start end (cdr x))
;;                   (subrange (+ (nfix start) 1) (+ end 1) x)))
;;   :hints
;;   (("Goal" :in-theory
;;     (e/d (subrange take-of-nthcdr TAKE)
;;          (anti-subrange
;;           nthcdr-of-take)))))

;; ;move
;; (local
;;  (defthm equiv-of-take-and-self
;;   (implies (natp n)
;;            (equal (list::equiv y (take n y))
;;                   (equal n (len y))))
;;   :hints (("Goal" :in-theory (enable take)))))

;; (local
;;  (defthm equiv-of-firstn-and-self
;;   (implies (natp n)
;;            (equal (list::equiv y (firstn n y))
;;                   (>= n (len y))))))

;; ;; (LIST::EQUIV (NTHCDR N L) L)

;; (defun group-induct (l le n)
;;   (if (or (zp n)
;;           (endp l))
;;       (list l le n)
;;     (group-induct (nthcdr n l) (nthcdr n le) n)))

;; (local
;;  (defthm list::equiv-implies-equal-group
;;   (implies (list::equiv l l-equiv)
;;            (equal (group n l)
;;                   (group n l-equiv)))
;;   :rule-classes (:congruence)
;;   :hints (("Goal"
;;            :induct (group-induct l l-equiv n)
;;            :in-theory (enable group)))))

;; ;move
;; ;why do I need this?
;; (defthm perm-equal-list-of-nth-0
;;   (equal (PERM X (LIST (NTH 0 X)))
;;          (equal 1 (len x))))

;move
(defthm car-of-firstn
  (implies (posp n)
           (equal (car (firstn n x))
                  (car x))))

(defthm true-list-fix-when-not-consp-cheap
  (implies (not (consp x))
           (equal (true-list-fix x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;; or go from (NTHCDR (LEN X) X) to finalcdr
(defthm append-of-nthcdr-of-len-same
  (equal (APPEND (NTHCDR (LEN X) X) Y)
         y)
  :hints (("Goal" :in-theory (enable equal-of-append))))

(DEFTHMd FIRSTN-WHEN-Zp
  (IMPLIES (ZP N)
           (EQUAL (FIRSTN N X)
                  NIL))
  :HINTS (("Goal" :IN-THEORY (ENABLE FIRSTN))))

;only do this if there are whole chunks to cut off..
(defthmd group-of-append-1
  (implies (posp n)
           (equal (group n (append x y))
                  (append (group n (firstn (* n (floor (len x) n)) x))
                          (group n (append (nthcdr (* n (floor (len x) n))
                                                   x)
                                           y)))))
  :hints (("Goal" :in-theory (e/d (equal-of-append
                                   FIRSTN-WHEN-Zp)
                                  (FIRSTN-BECOMES-TAKE-GEN
                                   FIRSTN-BECOMES-TAKE)))))

(defthmd group-of-append-2
  (implies (and (posp n)
                (< (len x) n))
           (equal (group n (append x y))
                  (if (and (atom x) (atom y))
                      nil
                    (cons (append x (firstn (- n (len x)) y))
                          (group n (nthcdr (- n (len x)) y)))))))

;simple case for when x and y both have a length that's a multiple of n?
(defthm group-of-append
  (implies (posp n)
           (equal (group n (append x y))
                  (append (group n (firstn (* n (floor (len x) n))
                                           x))
                          (if (and (equal 0 (mod (len x) n))
                                   (atom y))
                              nil
                            (cons (append (nthcdr (* n (floor (len x) n)) ;use lastn of (mod (len x) n)?
                                                  x)
                                          (firstn (- n (mod (len x) n))
                                                  y))
                                  (group n (nthcdr (- n (mod (len x) n))
                                                   y)))))))
  :hints (("Goal"
           :use ((:instance group-of-append-1)
                 (:instance group-of-append-2 (x (NTHCDR (* N (FLOOR (LEN X) N)) X))))
           :in-theory (e/d (group-of-append-2 mod)
                           ()))))

(defthmd group-of-append-new
  (implies (posp n)
           (equal (group n (append x y))
                  (if (equal 0 (mod (len x) n))
                      ;;x contains only complete groups:
                      (append (group n x)
                              (group n y))
                    ;;x ends with a partial group:
                    (append (group n (firstn (* n (floor (len x) n))
                                             x))
                            (cons (append (nthcdr (* n (floor (len x) n)) ;use lastn of (mod (len x) n)?
                                                  x)
                                          (firstn (- n (mod (len x) n))
                                                  y))
                                  (group n (nthcdr (- n (mod (len x) n))
                                                   y)))))))
  :hints (("Goal" :in-theory (e/d (group-of-append) (;MOD-OF-EXPT-OF-2-CONSTANT-VERSION ;+-BECOMES-BVPLUS-HACK
                                                                          MOD-TYPE
                                                                          MOD-bounded-by-modulus
                                                                          floor-bounded-by-/
                                                                          ;LIST::EQUAL-APPEND-REDUCTION!
                                                                          ;natp-when-integerp
                                                                          FIRSTN-BECOMES-TAKE-GEN)))))

(defthm group-of-append-new2
  (implies (posp n)
           (equal (group n (append x y))
                  (append (group n (firstn (* n (floor (len x) n)) ;process whole groups in x
                                           x))
                          (if (equal 0 (mod (len x) n))
                              ;;x contains only whole groups:
                              (group n y)
                            ;;x ends with a partial group:
                            (cons (append (nthcdr (* n (floor (len x) n)) ;use lastn of (mod (len x) n)?
                                                  x)
                                          (firstn (- n (mod (len x) n))
                                                  y))
                                  (group n (nthcdr (- n (mod (len x) n))
                                                   y)))))))
  :hints (("Goal" :in-theory (e/d (group-of-append) (;MOD-OF-EXPT-OF-2-CONSTANT-VERSION ;+-BECOMES-BVPLUS-HACK
                                                                          MOD-TYPE
                                                                          MOD-bounded-by-modulus
                                                                          floor-bounded-by-/
                                                                          ;LIST::EQUAL-APPEND-REDUCTION!
                                                                          ;natp-when-integerp
                                                                          FIRSTN-BECOMES-TAKE-GEN)))))

(defthm group-of-myif-arg2
  (equal (group z (myif test x y))
         (myif test (group z x)
               (group z y)))
  ;why so slow without the minimal-theory?
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(myif)))))

(defthm iff-of-group
  (implies (posp n)
           (iff (group n x)
                (not (atom x))))
  :hints (("Goal" :in-theory (enable group))))

(defthm equal-of-nil-and-group
  (implies (posp n)
           (equal (equal nil (group n x))
                  (atom x))))

(defthm items-have-len-of-group
  (implies (posp n)
           (equal (items-have-len n (group n x))
                  (equal 0 (mod (len x) n))))
  :hints (("Goal" :in-theory (enable GROUP items-have-len))))

(defthm true-listp-of-group
  (true-listp (group n x)))

(defthm all-true-listp-of-group
  (all-true-listp (group n x))
  :hints (("Goal" :in-theory (enable group))))
