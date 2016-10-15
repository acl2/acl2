(in-package "ACL2")

(include-book "land")
(include-book "lior")
(include-book "lxor")
(local (include-book "../arithmetic/top"))
(local (include-book "logand"))
(local (include-book "logior"))
(local (include-book "logxor"))
(local (include-book "merge"))
(local (include-book "bvecp"))
(local (include-book "bits"))

(defthmd lior-land-1
  (equal (lior x (land y z n) n)
         (land (lior x y n) (lior x z n) n))
  :hints (("Goal" :use ((:instance logior-logand
				   (x (bits x (1- n) 0))
				   (y (bits y (1- n) 0))
				   (z (bits z (1- n) 0))))
           :in-theory (enable lior land))))

(defthmd lior-land-2
  (equal (lior (land y z n) x n)
         (land (lior x y n) (lior x z n) n))
  :hints (("Goal" :use ((:instance logior-logand
				   (x (bits x (1- n) 0))
				   (y (bits y (1- n) 0))
				   (z (bits z (1- n) 0))))
           :in-theory (enable lior land))))

(defthmd land-lior-1
  (equal (land x (lior y z n) n)
         (lior (land x y n) (land x z n) n))
  :hints (("Goal" :use ((:instance logand-logior
				   (x (bits x (1- n) 0))
				   (y (bits y (1- n) 0))
				   (z (bits z (1- n) 0))))
           :in-theory (enable lior land))))

(defthmd land-lior-2
  (equal (land (lior y z n) x n)
         (lior (land x y n) (land x z n) n))
  :hints (("Goal" :use ((:instance logand-logior
				   (x (bits x (1- n) 0))
				   (y (bits y (1- n) 0))
				   (z (bits z (1- n) 0))))
           :in-theory (enable lior land))))

(defthmd lior-land-lxor
  (equal (lior (land x y n) (lior (land x z n) (land y z n) n) n)
         (lior (land x y n) (land (lxor x y n) z n) n))
  :hints (("Goal" :use ((:instance log3
				   (x (bits x (1- n) 0))
				   (y (bits y (1- n) 0))
				   (z (bits z (1- n) 0))))
           :in-theory (enable lior land lxor))))

(defthmd lxor-rewrite
  (equal (lxor x y n)
         (lior (land x (lnot y n) n)
               (land y (lnot x n) n)
               n))
  :hints (("Goal" :use ((:instance logxor-rewrite-2
				   (x (bits x (1- n) 0))
				   (y (bits y (1- n) 0))))
           :in-theory (enable lior land lxor))))

(defthmd lnot-lxor
  (equal (lnot (lxor x y n) n)
         (lxor (lnot x n) y n))
  :hints (("Goal" :use ((:instance lnot-logxor
				   (x (bits x (1- n) 0))
				   (y (bits y (1- n) 0))))
           :in-theory (enable lxor))))

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
 (defthm lnot-lior-aux
  (implies (and (integerp x) ;gen?
                (integerp y) ;gen?
                )
           (equal (lnot (lior x y n) n)
                  (land (lnot x n) (lnot y n) n)))
  :hints (("subgoal *1/2" :use (lior-def
                                (:instance land-def (x  (LNOT X N)) (y (LNOT Y N)))
                                (:instance mod012 (x x))
                                (:instance mod012 (x y))
                                (:instance lnot-fl (k 1))
                                (:instance lnot-fl (x y) (k 1))
                                )
           )
          ("Goal" :in-theory (enable lnot-shift)
           :do-not '(generalize)
           :induct ( op-dist-induct x y n)))))
|#

(local
 (DEFTHM LNOT-LIOR-AUX
   (IMPLIES (AND (INTEGERP X) (INTEGERP Y))
            (EQUAL (LNOT (LIOR X Y N) N)
                   (LAND (LNOT X N) (LNOT Y N) N)))
   :INSTRUCTIONS
   ((:IN-THEORY (ENABLE LNOT-SHIFT))
    (:INDUCT (OP-DIST-INDUCT X Y N))
    :PROVE
    (:PROVE :HINTS
            (("Goal" :USE
              (LIOR-DEF (:INSTANCE LAND-DEF (X (LNOT X N))
                                   (Y (LNOT Y N)))
                        (:INSTANCE MOD012 (X X))
                        (:INSTANCE MOD012 (X Y))
                        (:INSTANCE LNOT-FL (K 1))
                        (:INSTANCE LNOT-FL (X Y) (K 1))))))
    :PROVE)))

(defthm lnot-lior
  (equal (lnot (lior x y n) n)
         (land (lnot x n) (lnot y n) n))
  :hints (("goal" :in-theory (disable lnot-lior-aux)
           :use (:instance lnot-lior-aux (x (fl x)) (y (fl y)))))
  )

; See comment above about v2-8-alpha-12-30-03.  A similar situation applies
; just below.
#|
(local
 (defthm lnot-land-aux
   (implies (and (integerp x) ;gen?
                 (integerp y) ;gen?
                 )
            (equal (lnot (land x y n) n)
                   (lior (lnot x n) (lnot y n) n)))
   :hints (("subgoal *1/2" :use (land-def
                                 (:instance lior-def (x  (LNOT X N)) (y (LNOT Y N)))
                                 (:instance mod012 (x x))
                                 (:instance mod012 (x y))
                                 (:instance lnot-fl (k 1))
                                 (:instance lnot-fl (x y) (k 1))
                                 )
            )
           ("Goal" :in-theory (enable lnot-shift)
            :do-not '(generalize)
            :induct ( op-dist-induct x y n)))))
|#

(DEFTHM LNOT-LAND-AUX
        (IMPLIES (AND (INTEGERP X) (INTEGERP Y))
                 (EQUAL (LNOT (LAND X Y N) N)
                        (LIOR (LNOT X N) (LNOT Y N) N)))
        :INSTRUCTIONS
        ((:IN-THEORY (ENABLE LNOT-SHIFT))
         (:INDUCT (OP-DIST-INDUCT X Y N))
         :PROVE
         (:PROVE :HINTS
                 (("Goal" :USE
                          (LAND-DEF (:INSTANCE LIOR-DEF (X (LNOT X N))
                                               (Y (LNOT Y N)))
                                    (:INSTANCE MOD012 (X X))
                                    (:INSTANCE MOD012 (X Y))
                                    (:INSTANCE LNOT-FL (K 1))
                                    (:INSTANCE LNOT-FL (X Y) (K 1))))))
         :PROVE))

(defthm lnot-land
  (equal (lnot (land x y n) n)
         (lior (lnot x n) (lnot y n) n))
  :hints (("Goal" :in-theory (disable LNOT-LAND-aux)
           :use (:instance lnot-land-aux (x (fl x)) (y (fl y)))))
  )

