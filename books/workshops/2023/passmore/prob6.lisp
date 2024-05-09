;;
;; Theorem (over ℝ):
;;
;; (IMPLIES (AND (<= 0 a)
;;               (<= 0 b)
;;               (<= 0 c)
;;               (<= (* c (EXPT (+ (* 2 a) b) 3)) (* 27 x)))
;;          (<= (* c a a b) x)).
;;
;; Proof found by Imandra in 1.753819 secs.
;; Questions? Contact Grant Passmore (grant@imandra.ai).
;;

(in-package "ACL2")

(encapsulate ()

;; Preamble

 (SET-IGNORE-OK T)
 (SET-IRRELEVANT-FORMALS-OK T)

 (LOCAL (DEFMACRO NEQ (X Y)
          `(OR (< ,X ,Y) (> ,X ,Y))))

 (LOCAL (DEFUN SQUARE (X)
          (* X X)))

 (LOCAL (DEFTHM SQUARE-PSD
          (IMPLIES (RATIONALP X)
                   (>= (SQUARE X) 0))
          :RULE-CLASSES (:LINEAR)))

 (LOCAL (DEFTHM SQUARE-TYPE
          (IMPLIES (RATIONALP X)
                   (RATIONALP (SQUARE X)))
          :RULE-CLASSES (:TYPE-PRESCRIPTION)))

 (LOCAL (IN-THEORY (DISABLE SQUARE)))
 
 (LOCAL (include-book "arithmetic-5/top" :dir :system))

;; Normalized problem polynomials
 
 (LOCAL (DEFUND PROB-0 (A B C X)
          (- 0 (- 0 A))))
 
 (LOCAL (DEFUND PROB-1 (A B C X)
          (- 0 (- 0 B))))
 
 (LOCAL (DEFUND PROB-2 (A B C X)
          (- 0 (- 0 C))))
 
 (LOCAL (DEFUND PROB-3 (A B C X)
          (- 0 (- (* C (EXPT (+ (* 2 A) B) 3)) (* 27 X)))))
 
 (LOCAL (DEFUND PROB-4 (A B C X)
          (- (* C (* A (* A B))) X)))

;; Normalized goal expressed using problem polynomials
 
 (LOCAL (DEFUN GOAL (A B C X)
          (IMPLIES (AND (RATIONALP A)
                        (RATIONALP B)
                        (RATIONALP C) (RATIONALP X))
                   (NOT (AND (>= (PROB-0 A B C X) 0)
                             (>= (PROB-1 A B C X) 0)
                             (>= (PROB-2 A B C X) 0)
                             (>= (PROB-3 A B C X) 0)
                             (> (PROB-4 A B C X) 0))))))

;; Ideal cofactors

;; Cone cofactors
 
 (LOCAL (DEFUND CONE-CF-0 (A B C X)
          (* (- (* C (* A (* A B))) X) (* 1/26 (SQUARE 1)))))
 
 (LOCAL (DEFTHM CONE-CF-0-TYPE
          (IMPLIES (AND (RATIONALP A)
                        (RATIONALP B)
                        (RATIONALP C) (RATIONALP X))
                   (RATIONALP (CONE-CF-0 A B C X)))
          :hints
          (("Goal" :in-theory (enable CONE-CF-0)))))
 
 (LOCAL (DEFTHM CONE-CF-0-PSD
          (IMPLIES (AND (NOT (GOAL A B C X))
                        (RATIONALP A)
                        (RATIONALP B)
                        (RATIONALP C) (RATIONALP X))
                   (>= (CONE-CF-0 A B C X) 0))
          :hints
          (("Goal" :in-theory
                   (enable CONE-CF-0
                           PROB-0
                           PROB-1 PROB-2 PROB-3 PROB-4)))
          :rule-classes (:linear )))
 
 (LOCAL (DEFUND CONE-CF-1 (A B C X)
          (* (- 0 (- (* C (EXPT (+ (* 2 A) B) 3)) (* 27 X)))
             (* 1/26 (SQUARE 1)))))
 
 (LOCAL (DEFTHM CONE-CF-1-TYPE
          (IMPLIES (AND (RATIONALP A)
                        (RATIONALP B)
                        (RATIONALP C) (RATIONALP X))
                   (RATIONALP (CONE-CF-1 A B C X)))
          :hints
          (("Goal" :in-theory (enable CONE-CF-1)))))
 
 (LOCAL (DEFTHM CONE-CF-1-PSD
          (IMPLIES (AND (NOT (GOAL A B C X))
                        (RATIONALP A)
                        (RATIONALP B)
                        (RATIONALP C) (RATIONALP X))
                   (>= (CONE-CF-1 A B C X) 0))
          :hints
          (("Goal" :in-theory
                   (enable CONE-CF-1
                           PROB-0
                           PROB-1 PROB-2 PROB-3 PROB-4)))
          :rule-classes (:linear )))
 
 (LOCAL (DEFUND CONE-CF-2 (A B C X)
          (* (* (- 0 (- 0 B)) (- 0 (- 0 C)))
             (* 1/26 (SQUARE (+ (* -1 A) B))))))
 
 (LOCAL (DEFTHM CONE-CF-2-TYPE
          (IMPLIES (AND (RATIONALP A)
                        (RATIONALP B)
                        (RATIONALP C) (RATIONALP X))
                   (RATIONALP (CONE-CF-2 A B C X)))
          :hints
          (("Goal" :in-theory (enable CONE-CF-2)))))
 
 (LOCAL (DEFTHM CONE-CF-2-PSD
          (IMPLIES (AND (NOT (GOAL A B C X))
                        (RATIONALP A)
                        (RATIONALP B)
                        (RATIONALP C) (RATIONALP X))
                   (>= (CONE-CF-2 A B C X) 0))
          :hints
          (("Goal" :in-theory
                   (enable CONE-CF-2
                           PROB-0
                           PROB-1 PROB-2 PROB-3 PROB-4)))
          :rule-classes (:linear )))
 
 (LOCAL (DEFUND CONE-CF-3 (A B C X)
          (* (* (- 0 (- 0 A)) (- 0 (- 0 C)))
             (* 4/13 (SQUARE (+ (* -1 A) B))))))
 
 (LOCAL (DEFTHM CONE-CF-3-TYPE
          (IMPLIES (AND (RATIONALP A)
                        (RATIONALP B)
                        (RATIONALP C) (RATIONALP X))
                   (RATIONALP (CONE-CF-3 A B C X)))
          :hints
          (("Goal" :in-theory (enable CONE-CF-3)))))
 
 (LOCAL (DEFTHM CONE-CF-3-PSD
          (IMPLIES (AND (NOT (GOAL A B C X))
                        (RATIONALP A)
                        (RATIONALP B)
                        (RATIONALP C) (RATIONALP X))
                   (>= (CONE-CF-3 A B C X) 0))
          :hints
          (("Goal" :in-theory
                   (enable CONE-CF-3
                           PROB-0
                           PROB-1 PROB-2 PROB-3 PROB-4)))
          :rule-classes (:linear )))

;; Monoid cofactors
 
 (LOCAL (DEFUND MONOID-CF-0 (A B C X)
          (- (* C (* A (* A B))) X)))

;; Positivstellensatz certificate
 
 (LOCAL (DEFUN CERT (A B C X)
          (+ (MONOID-CF-0 A B C X)
             (CONE-CF-0 A B C X)
             (CONE-CF-1 A B C X)
             (CONE-CF-2 A B C X) (CONE-CF-3 A B C X) 0)))

;; Contradictory results on the sign of the certificate
 
 (LOCAL (DEFTHMD CERT-KEY
          (IMPLIES (AND (RATIONALP A)
                        (RATIONALP B)
                        (RATIONALP C) (RATIONALP X))
                   (= (CERT A B C X) 0))
          :hints
          (("Goal" :in-theory
                   (enable SQUARE
                           CERT
                           PROB-0
                           PROB-1
                           PROB-2
                           PROB-3
                           PROB-4
                           CONE-CF-0
                           CONE-CF-1
                           CONE-CF-2 CONE-CF-3 MONOID-CF-0)))))
 
 (LOCAL (DEFTHM CERT-CONTRA-M-0
          (IMPLIES (AND (NOT (GOAL A B C X))
                        (RATIONALP A)
                        (RATIONALP B)
                        (RATIONALP C) (RATIONALP X))
                   (> (MONOID-CF-0 A B C X) 0))
          :hints
          (("Goal" :in-theory
                   (enable SQUARE
                           CERT
                           PROB-0
                           PROB-1
                           PROB-2
                           PROB-3
                           PROB-4
                           CONE-CF-0
                           CONE-CF-1
                           CONE-CF-2 CONE-CF-3 MONOID-CF-0)))
          :rule-classes (:linear )))
 
 (LOCAL (DEFTHM CERT-CONTRA-C-0
          (IMPLIES (AND (NOT (GOAL A B C X))
                        (RATIONALP A)
                        (RATIONALP B)
                        (RATIONALP C) (RATIONALP X))
                   (>= (CONE-CF-0 A B C X) 0))
          :rule-classes (:linear )))
 
 (LOCAL (DEFTHM CERT-CONTRA-C-1
          (IMPLIES (AND (NOT (GOAL A B C X))
                        (RATIONALP A)
                        (RATIONALP B)
                        (RATIONALP C) (RATIONALP X))
                   (>= (CONE-CF-1 A B C X) 0))
          :rule-classes (:linear )))
 
 (LOCAL (DEFTHM CERT-CONTRA-C-2
          (IMPLIES (AND (NOT (GOAL A B C X))
                        (RATIONALP A)
                        (RATIONALP B)
                        (RATIONALP C) (RATIONALP X))
                   (>= (CONE-CF-2 A B C X) 0))
          :rule-classes (:linear )))
 
 (LOCAL (DEFTHM CERT-CONTRA-C-3
          (IMPLIES (AND (NOT (GOAL A B C X))
                        (RATIONALP A)
                        (RATIONALP B)
                        (RATIONALP C) (RATIONALP X))
                   (>= (CONE-CF-3 A B C X) 0))
          :rule-classes (:linear )))
 
 (LOCAL (DEFTHM CERT-CONTRA
          (IMPLIES (AND (NOT (GOAL A B C X))
                        (RATIONALP A)
                        (RATIONALP B)
                        (RATIONALP C) (RATIONALP X))
                   (NEQ (CERT A B C X) 0))
          :rule-classes nil))

;; Main lemma
 
 (LOCAL (DEFTHM MAIN
          (IMPLIES (AND (RATIONALP A)
                        (RATIONALP B)
                        (RATIONALP C) (RATIONALP X))
                   (GOAL A B C X))
          :hints
          (("Goal" :in-theory
                   (disable GOAL)
                   :use (CERT-KEY CERT-CONTRA)))
          :rule-classes nil))

;; Final theorem
 
 (DEFTHM FINAL
   (IMPLIES (AND (RATIONALP A)
                 (RATIONALP B)
                 (RATIONALP C)
                 (RATIONALP X)
                 (<= 0 A)
                 (<= 0 B)
                 (<= 0 C)
                 (<= (* C (EXPT (+ (* 2 A) B) 3)) (* 27 X)))
            (<= (* C A A B) X))
   :hints
   (("Goal" :in-theory
            (enable GOAL PROB-0 PROB-1 PROB-2 PROB-3 PROB-4)
            :use (MAIN )))
   :rule-classes nil)
)
