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

(in-package "ACL2")

(include-book "land0")
(include-book "lior0")
(include-book "lxor0")
(local (include-book "../../arithmetic/top"))
(local (include-book "logand"))
(local (include-book "logior"))
(local (include-book "logxor"))
(local (include-book "merge"))
(local (include-book "bvecp"))
(local (include-book "bits"))

(defthmd lior0-land0-1
  (equal (lior0 x (land0 y z n) n)
         (land0 (lior0 x y n) (lior0 x z n) n))
  :hints (("Goal" :use ((:instance logior-logand
				   (x (bits x (1- n) 0))
				   (y (bits y (1- n) 0))
				   (z (bits z (1- n) 0))))
           :in-theory (enable lior0 land0))))

(defthmd lior0-land0-2
  (equal (lior0 (land0 y z n) x n)
         (land0 (lior0 x y n) (lior0 x z n) n))
  :hints (("Goal" :use ((:instance logior-logand
				   (x (bits x (1- n) 0))
				   (y (bits y (1- n) 0))
				   (z (bits z (1- n) 0))))
           :in-theory (enable lior0 land0))))

(defthmd land0-lior0-1
  (equal (land0 x (lior0 y z n) n)
         (lior0 (land0 x y n) (land0 x z n) n))
  :hints (("Goal" :use ((:instance logand-logior
				   (x (bits x (1- n) 0))
				   (y (bits y (1- n) 0))
				   (z (bits z (1- n) 0))))
           :in-theory (enable lior0 land0))))

(defthmd land0-lior0-2
  (equal (land0 (lior0 y z n) x n)
         (lior0 (land0 x y n) (land0 x z n) n))
  :hints (("Goal" :use ((:instance logand-logior
				   (x (bits x (1- n) 0))
				   (y (bits y (1- n) 0))
				   (z (bits z (1- n) 0))))
           :in-theory (enable lior0 land0))))

(defthmd lior0-land0-lxor0
  (equal (lior0 (land0 x y n) (lior0 (land0 x z n) (land0 y z n) n) n)
         (lior0 (land0 x y n) (land0 (lxor0 x y n) z n) n))
  :hints (("Goal" :use ((:instance log3
				   (x (bits x (1- n) 0))
				   (y (bits y (1- n) 0))
				   (z (bits z (1- n) 0))))
           :in-theory (enable lior0 land0 lxor0))))

(defthmd lxor0-rewrite
  (equal (lxor0 x y n)
         (lior0 (land0 x (lnot y n) n)
               (land0 y (lnot x n) n)
               n))
  :hints (("Goal" :use ((:instance logxor-rewrite-2
				   (x (bits x (1- n) 0))
				   (y (bits y (1- n) 0))))
           :in-theory (enable lior0 land0 lxor0))))

(defthmd lnot-lxor0
  (equal (lnot (lxor0 x y n) n)
         (lxor0 (lnot x n) y n))
  :hints (("Goal" :use ((:instance lnot-logxor
				   (x (bits x (1- n) 0))
				   (y (bits y (1- n) 0))))
           :in-theory (enable lxor0))))

;move
(defthm bits-of-1-plus-double
  (implies (and (integerp x)
                (<= 0 i)
                )
           (equal (bits (+ 1 (* 2 x)) i 1)
                  (bits x (1- i) 0)))
  :hints (("goal" :in-theory (enable bits expt-split mod-prod mod-sum-cases)
           ))
  )

;move
;useful for inductions involvling lnot?
(defthm lnot-shift-plus-1
  (implies (and (case-split (integerp x))
                (case-split (< 0 n))
                (case-split (integerp n))
                )
           (equal (lnot (+ 1 (* 2 x)) n)
                  (* 2 (lnot x (1- n)))))
  :hints (("Goal" :use (:instance bits-plus-bits (x (+ 1 (* 2 X))) (n  (1- N)) (m 0) (p 1))
           :in-theory (enable lnot expt-split))))

;move?
;do we want this sort of theorem about lognot and logand too?
; Matt K.:  The original proof fails using v2-8-alpha-12-30-03.  I don't know
; why, but I do notice that the induction heuristics are getting in the way,
; because the problem goal (the one with the hint below) goes through in the
; proof-builder.  So we use the proof-builder proof.

#|
(local
 (defthm lnot-lior0-aux
  (implies (and (integerp x) ;gen?
                (integerp y) ;gen?
                )
           (equal (lnot (lior0 x y n) n)
                  (land0 (lnot x n) (lnot y n) n)))
  :hints (("subgoal *1/2" :use (lior0-def
                                (:instance land0-def (x  (LNOT X N)) (y (LNOT Y N)))
                                (:instance mod012 (m x))
                                (:instance mod012 (m y))
                                (:instance lnot-fl-original (k 1))
                                (:instance lnot-fl-original (x y) (k 1))
                                )
           )
          ("Goal" :in-theory (enable lnot-shift-2)
           :do-not '(generalize)
           :induct ( op-dist-induct x y n)))))
|#

(local
 (DEFTHM LNOT-LIOR0-AUX
   (IMPLIES (AND (INTEGERP X) (INTEGERP Y))
            (EQUAL (LNOT (LIOR0 X Y N) N)
                   (LAND0 (LNOT X N) (LNOT Y N) N)))
   :INSTRUCTIONS
   ((:IN-THEORY (ENABLE LNOT-SHIFT-2))
    (:INDUCT (OP-DIST-INDUCT X Y N))
    :PROVE
    (:PROVE :HINTS
            (("Goal" :USE
              (LIOR0-DEF (:INSTANCE LAND0-DEF (X (LNOT X N))
                                   (Y (LNOT Y N)))
                        (:INSTANCE MOD012 (M X))
                        (:INSTANCE MOD012 (M Y))
                        (:INSTANCE LNOT-FL-ORIGINAL (K 1))
                        (:INSTANCE LNOT-FL-ORIGINAL (X Y) (K 1))))))
    :PROVE)))

(defthm lnot-lior0
  (equal (lnot (lior0 x y n) n)
         (land0 (lnot x n) (lnot y n) n))
  :hints (("goal" :in-theory (disable lnot-lior0-aux)
           :use (:instance lnot-lior0-aux (x (fl x)) (y (fl y)))))
  )

; See comment above about v2-8-alpha-12-30-03.  A similar situation applies
; just below.
#|
(local
 (defthm lnot-land0-aux
   (implies (and (integerp x) ;gen?
                 (integerp y) ;gen?
                 )
            (equal (lnot (land0 x y n) n)
                   (lior0 (lnot x n) (lnot y n) n)))
   :hints (("subgoal *1/2" :use (land0-def
                                 (:instance lior0-def (x  (LNOT X N)) (y (LNOT Y N)))
                                 (:instance mod012 (m x))
                                 (:instance mod012 (m y))
                                 (:instance lnot-fl-original (k 1))
                                 (:instance lnot-fl-original (x y) (k 1))
                                 )
            )
           ("Goal" :in-theory (enable lnot-shift)
            :do-not '(generalize)
            :induct ( op-dist-induct x y n)))))
|#

(DEFTHM LNOT-LAND0-AUX
        (IMPLIES (AND (INTEGERP X) (INTEGERP Y))
                 (EQUAL (LNOT (LAND0 X Y N) N)
                        (LIOR0 (LNOT X N) (LNOT Y N) N)))
        :INSTRUCTIONS
        ((:IN-THEORY (ENABLE LNOT-SHIFT-2))
         (:INDUCT (OP-DIST-INDUCT X Y N))
         :PROVE
         (:PROVE :HINTS
                 (("Goal" :USE
                          (LAND0-DEF (:INSTANCE LIOR0-DEF (X (LNOT X N))
                                               (Y (LNOT Y N)))
                                    (:INSTANCE MOD012 (M X))
                                    (:INSTANCE MOD012 (M Y))
                                    (:INSTANCE LNOT-FL-ORIGINAL (K 1))
                                    (:INSTANCE LNOT-FL-ORIGINAL (X Y) (K 1))))))
         :PROVE))

(defthm lnot-land0
  (equal (lnot (land0 x y n) n)
         (lior0 (lnot x n) (lnot y n) n))
  :hints (("Goal" :in-theory (disable LNOT-LAND0-aux)
           :use (:instance lnot-land0-aux (x (fl x)) (y (fl y)))))
  )
