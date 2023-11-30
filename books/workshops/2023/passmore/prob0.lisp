;;
;; Theorem (over ℝ):
;;
;; (IMPLIES (= (+ (* A X X) (* B X) C) 0)
;;          (>= (- (* B B) (* 4 A C)) 0)).
;;
;; Proof found by Imandra in 0.179818 secs.
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
          (+ (* A (* X X)) (+ (* B X) C))))
 
 (LOCAL (DEFUND PROB-1 (A B C X)
          (- 0 (- (* B B) (* 4 (* A C))))))

;; Normalized goal expressed using problem polynomials
 
 (LOCAL (DEFUN GOAL (A B C X)
          (IMPLIES (AND (RATIONALP A)
                        (RATIONALP B)
                        (RATIONALP C) (RATIONALP X))
                   (NOT (AND (= (PROB-0 A B C X) 0)
                             (> (PROB-1 A B C X) 0))))))

;; Ideal cofactors
 
 (LOCAL (DEFUND IDEAL-CF-0 (A B C X)
          (* -4 A)))
 
 (LOCAL (DEFTHM IDEAL-CF-0-TYPE
          (IMPLIES (AND (RATIONALP A)
                        (RATIONALP B)
                        (RATIONALP C) (RATIONALP X))
                   (RATIONALP (IDEAL-CF-0 A B C X)))
          :hints
          (("Goal" :in-theory (enable IDEAL-CF-0)))))

;; Cone cofactors
 
 (LOCAL (DEFUND CONE-CF-0 (A B C X)
          (SQUARE (+ (* 2 (* A X)) B))))
 
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
                   (enable CONE-CF-0 PROB-0 PROB-1)))
          :rule-classes (:linear )))

;; Monoid cofactors
 
 (LOCAL (DEFUND MONOID-CF-0 (A B C X)
          (- 0 (- (* B B) (* 4 (* A C))))))

;; Positivstellensatz certificate
 
 (LOCAL (DEFUN CERT (A B C X)
          (+ (MONOID-CF-0 A B C X)
             (CONE-CF-0 A B C X)
             (* (IDEAL-CF-0 A B C X) (PROB-0 A B C X)))))

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
                           IDEAL-CF-0 CONE-CF-0 MONOID-CF-0)))))
 
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
                           IDEAL-CF-0 CONE-CF-0 MONOID-CF-0)))
          :rule-classes (:linear )))
 
 (LOCAL (DEFTHM CERT-CONTRA-C-0
          (IMPLIES (AND (NOT (GOAL A B C X))
                        (RATIONALP A)
                        (RATIONALP B)
                        (RATIONALP C) (RATIONALP X))
                   (>= (CONE-CF-0 A B C X) 0))
          :rule-classes (:linear )))
 
 (LOCAL (DEFTHM CERT-CONTRA-I-0
          (IMPLIES (AND (NOT (GOAL A B C X))
                        (RATIONALP A)
                        (RATIONALP B)
                        (RATIONALP C) (RATIONALP X))
                   (= (* (IDEAL-CF-0 A B C X)
                         (PROB-0 A B C X))
                      0))
          :hints
          (("Goal" :in-theory
                   (enable SQUARE
                           CERT
                           PROB-0
                           PROB-1
                           IDEAL-CF-0 CONE-CF-0 MONOID-CF-0)))
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
                 (RATIONALP X) (= (+ (* A X X) (* B X) C) 0))
            (>= (- (* B B) (* 4 A C)) 0))
   :hints
   (("Goal" :in-theory
            (enable GOAL PROB-0 PROB-1) :use (MAIN )))
   :rule-classes nil)
)
