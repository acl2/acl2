; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "RTL")

(include-book "../lib2/top")

(include-book "bits-new")

(local (include-book "../../arithmetic/top"))
;;;
;;;

(local
 (encapsulate ()
              (local (include-book "bits-new-proofs"))

             (defthm bits_alt-is-bits
               (equal (bits_alt x i j)
                      (bits x i j)))


             (defthm bitn_alt-is-bitn
               (equal (bitn_alt x n)
                      (bitn x n)))


             (defthm binary-cat_alt-is-binary-cat
               (equal (binary-cat_alt x m y n)
                      (binary-cat x m y n)))

             ))


;;;;;;;;;


(local
 (defund bvequal (v1 v2 n)
  (equal (sumbits v1 n)
         (sumbits v2 n))))


(local
 (defthm bvequal-then-equal
  (implies (and (bvequal x y n)
                (bvecp x n)
                (bvecp y n)
                (natp n))
           (equal x y))
  :hints (("Goal" :use ((:instance sumbits-thm
                                   (x x))
                        (:instance sumbits-thm
                                   (x y)))
           :in-theory (enable bvequal)))
  :rule-classes nil))

(local
 (encapsulate ()
              (local (include-book "log-new"))


              (defthmd bitn-lognot-g
                (implies (and (integerp x)
                              (integerp n)
                              (>= n 0))
                         (not (equal (bitn (lognot x) n)
                                     (bitn x n))))
                :hints (("Goal" :cases ((equal n 0)))
                        ("Subgoal 2" :use ((:instance bitn_alt-lognot)))
                        ("Subgoal 1" :in-theory (e/d (lognot bitn-def mod)
                                                     ()))))
              ))




(local
 (defthmd bitn-lnot-lognot-bvequal-lemma
   (implies (and (integerp x)
                 (natp n)
                 (> n 0)
                 (natp n)
                 (natp i)
                 (<= i (+ -1 n)))
            (equal (bitn (lnot x n) i)
                   (bitn (bits (lognot x) (+ -1 n) 0) i)))
   :hints (("Goal" :in-theory (e/d (bitn-lnot) ())
            :use ((:instance bitn-lognot-g
                             (n i))
                  (:instance bitn-0-1
                             (x x)
                             (n i)))))))


(local
 (defthm lnot-lognot-bvequal
   (implies (and (integerp x)
                 (natp n)
                 (> n 0)
                 (natp n)
                 (natp i)
                 (<= i n))
            (bvequal (lnot x n)
                     (bits (lognot x) (+ -1 n) 0)
                     i))
   :hints (("Goal" :in-theory (e/d (bvequal bitn-lnot-lognot-bvequal-lemma) (bitn-bits))))))



(defthm lnot-lognot
  (implies (and (natp n)
                (> n 0)
                (integerp x))
           (equal (lnot x n)
                  (bits (lognot x) (+ -1 n) 0)))
  :hints (("Goal" :use ((:instance bvequal-then-equal
                                   (x (lnot x n))
                                   (y (bits (lognot x) (+ -1 n) 0))
                                   (n n)))
           :in-theory (e/d (lnot-lognot-bvequal) ()))))








(local
 (encapsulate ()
              (local (include-book "log-new-proofs"))

              (defthmd bitn_alt-logand
                (implies (and (integerp x)
                              (integerp y)
                              (integerp n))
                         (equal (bitn_alt (logand x y) n)
                                (logand (bitn_alt x n) (bitn_alt y n)))))
              ))



(local
 (defthmd bitn-land-logand-bvequal-lemma
   (implies (and (integerp x)
                 (integerp y)
                 (natp n)
                 (> n 0)
                 (natp i)
                 (<= i (+ -1 n)))
            (equal (bitn (land x y n) i)
                   (bitn (bits (logand x y) (+ -1 n)  0) i)))
   :hints (("Goal" :in-theory (e/d (bitn-land) ())
            :use ((:instance bitn_alt-logand
                             (n i))
                  (:instance bitn-0-1
                             (x x)
                             (n i))
                  (:instance bitn-0-1
                             (x y)
                             (n i)))))))




(local
 (defthmd land-logand-bvequal
   (implies (and (integerp x)
                 (integerp y)
                 (natp n)
                 (> n 0)
                 (natp i)
                 (<= i n))
            (bvequal (land x y n)
                     (bits (logand x y) (+ -1 n)  0)
                     i))
   :hints (("Goal" :in-theory (e/d (bvequal bitn-land-logand-bvequal-lemma)
                                   ())))))




(defthmd land-logand
  (implies (and (natp n)
                (> n 0)
                (integerp x)
                (integerp y))
           (equal (land x y n)
                  (bits (logand x y) (+ -1 n) 0)))
  :hints (("Goal" :use ((:instance bvequal-then-equal
                                   (x (land x y n))
                                   (y (bits (logand x y) (+ -1 n) 0))
                                   (n n)))
           :in-theory (e/d (land-logand-bvequal) ()))))




;;;;;



(local
 (encapsulate ()
              (local (include-book "log-new-proofs"))

              (defthmd bitn_alt-logxor
                (implies (and (case-split (integerp x))
                              (case-split (integerp y))
                              (case-split (integerp n)))
                         (equal (bitn_alt (logxor x y) n)
                                (logxor (bitn_alt x n) (bitn_alt y n)))))
              ))



(local
 (defthmd bitn-lxor-logxor-bvequal-lemma
   (implies (and (integerp x)
                 (integerp y)
                 (natp n)
                 (> n 0)
                 (natp i)
                 (<= i (+ -1 n)))
            (equal (bitn (lxor x y n) i)
                   (bitn (bits (logxor x y) (+ -1 n)  0) i)))
   :hints (("Goal" :in-theory (e/d (bitn-lxor) ())
            :use ((:instance bitn_alt-logxor
                             (n i))
                  (:instance bitn-0-1
                             (x x)
                             (n i))
                  (:instance bitn-0-1
                             (x y)
                             (n i)))))))




(local
 (defthmd lxor-logxor-bvequal
   (implies (and (integerp x)
                 (integerp y)
                 (natp n)
                 (> n 0)
                 (natp i)
                 (<= i n))
            (bvequal (lxor x y n)
                     (bits (logxor x y) (+ -1 n)  0)
                     i))
   :hints (("Goal" :in-theory (e/d (bvequal bitn-lxor-logxor-bvequal-lemma)
                                   ())))))


(defthmd lxor-logxor
  (implies (and (natp n)
                (> n 0)
                (integerp x)
                (integerp y))
           (equal (lxor x y n)
                  (bits (logxor x y) (+ -1 n) 0)))
  :hints (("Goal" :use ((:instance bvequal-then-equal
                                   (x (lxor x y n))
                                   (y (bits (logxor x y) (+ -1 n) 0))
                                   (n n)))
           :in-theory (e/d (lxor-logxor-bvequal) ()))))


;;;;;;



(local
 (encapsulate ()
              (local (include-book "log-new-proofs"))

              (defthmd bitn_alt-logior
                (implies (and (integerp x)
                              (integerp y)
                              (integerp n))
                         (equal (bitn_alt (logior x y) n)
                                (logior (bitn_alt x n) (bitn_alt y n)))))
              ))



(local
 (defthmd bitn-lior-logior-bvequal-lemma
   (implies (and (integerp x)
                 (integerp y)
                 (natp n)
                 (> n 0)
                 (natp i)
                 (<= i (+ -1 n)))
            (equal (bitn (lior x y n) i)
                   (bitn (bits (logior x y) (+ -1 n)  0) i)))
   :hints (("Goal" :in-theory (e/d (bitn-lior) ())
            :use ((:instance bitn_alt-logior
                             (n i))
                  (:instance bitn-0-1
                             (x x)
                             (n i))
                  (:instance bitn-0-1
                             (x y)
                             (n i)))))))




(local
 (defthmd lior-logior-bvequal
   (implies (and (integerp x)
                 (integerp y)
                 (natp n)
                 (> n 0)
                 (natp i)
                 (<= i n))
            (bvequal (lior x y n)
                     (bits (logior x y) (+ -1 n)  0)
                     i))
   :hints (("Goal" :in-theory (e/d (bvequal bitn-lior-logior-bvequal-lemma)
                                   ())))))


(defthmd lior-logior
  (implies (and (natp n)
                (> n 0)
                (integerp x)
                (integerp y))
           (equal (lior x y n)
                  (bits (logior x y) (+ -1 n) 0)))
  :hints (("Goal" :use ((:instance bvequal-then-equal
                                   (x (lior x y n))
                                   (y (bits (logior x y) (+ -1 n) 0))
                                   (n n)))
           :in-theory (e/d (lior-logior-bvequal) ()))))



;;;;;
;;;;;



(local
 (defthmd bitn-logand-logand-bvequal-lemma
   (implies (and (integerp x)
                 (integerp y)
                 (natp n)
                 (natp i)
                 (<= i n))
            (equal (bitn (logand (bits x n 0)
                                 y) i)
                   (bitn (logand x y) i)))
   :hints (("Goal" :in-theory (e/d (bitn-bits) ())
            :use ((:instance bitn_alt-logand
                             (x (bits x n 0))
                             (y y)
                             (n i))
                  (:instance bitn_alt-logand
                             (x x)
                             (y y)
                             (n i)))))))




(local
 (defthmd logand-logand-bvequal
   (implies (and (integerp x)
                 (integerp y)
                 (natp n)
                 (natp i)
                 (<= i (+ 1 n)))
            (bvequal (logand (bits x n 0) y)
                     (logand x y)
                     i))
   :hints (("Goal" :in-theory (e/d (bvequal
                                    bitn-logand-logand-bvequal-lemma)
                                   ())))))



(local
 (encapsulate ()
   (local (include-book "log-new"))

   (defthm logand-bvecp-g
     (implies (and (natp n)
                   (bvecp x n)
                   (integerp y))
              (bvecp (logand x y) n))
     :hints (("Goal" :use ((:instance logand-bnd))
              :in-theory (e/d (bvecp) ()))))

   (defthm logand-bvecp-g2
     (implies (and (natp n)
                   (bvecp y n)
                   (integerp x))
              (bvecp (logand x y) n))
     :hints (("Goal" :use ((:instance logand-bvecp-g
                                      (x y)
                                      (y x))))))))



(defthmd logand-bits-reduce
  (implies (and (syntaxp (or (and (consp y)
                                  (not (equal (car y) 'bits)))
                             (symbolp y)))
                (bvecp y (+ 1 n))
                (natp n)
                (integerp x))
           (equal (logand (bits x n 0)
                          y)
                  (logand x y)))
  :hints (("Goal" :use ((:instance bvequal-then-equal
                                   (x (logand (bits x n 0)
                                              y))
                                   (y (logand x y))
                                   (n (+ 1 n))))
           :in-theory (e/d (logand-logand-bvequal) ()))))





(defthmd logand-bitn-reduce
  (implies (and (syntaxp (or (and (consp y)
                                  (not (equal (car y) 'bitn)))
                             (symbolp y)))
                (bvecp y 1)
                (integerp x))
           (equal (logand (bitn x 0)
                          y)
                  (logand x y)))
  :hints (("Goal" :use ((:instance logand-bits-reduce
                                   (n 0)))
           :in-theory (e/d (bitn) (bits-n-n-rewrite)))))


