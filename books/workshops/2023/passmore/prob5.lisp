;;
;; Theorem (over ℝ):
;;
;; (IMPLIES (AND (<= 0 x) (<= 0 y))
;;          (<= (* x y (expt (+ x y) 2))
;;              (expt (+ (* x x) (* y y)) 2))).
;;
;; Proof found by Imandra in 0.993155 secs.
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
 
 (LOCAL (DEFUND PROB-0 (X Y)
          (- 0 (- 0 X))))
 
 (LOCAL (DEFUND PROB-1 (X Y)
          (- 0 (- 0 Y))))
 
 (LOCAL (DEFUND PROB-2 (X Y)
          (- (* X (* Y (EXPT (+ X Y) 2)))
             (EXPT (+ (* X X) (* Y Y)) 2))))

;; Normalized goal expressed using problem polynomials
 
 (LOCAL (DEFUN GOAL (X Y)
          (IMPLIES (AND (RATIONALP X) (RATIONALP Y))
                   (NOT (AND (>= (PROB-0 X Y) 0)
                             (>= (PROB-1 X Y) 0)
                             (> (PROB-2 X Y) 0))))))

;; Ideal cofactors

;; Cone cofactors
 
 (LOCAL (DEFUND CONE-CF-0 (X Y)
          (+ (SQUARE (+ (EXPT X 2)
                        (+ (* -1/2 (* X Y))
                           (* -1/2 (EXPT Y 2)))))
             (* 3/4 (SQUARE (+ (* X Y) (* -1 (EXPT Y 2))))))))
 
 (LOCAL (DEFTHM CONE-CF-0-TYPE
          (IMPLIES (AND (RATIONALP X) (RATIONALP Y))
                   (RATIONALP (CONE-CF-0 X Y)))
          :hints
          (("Goal" :in-theory (enable CONE-CF-0)))))
 
 (LOCAL (DEFTHM CONE-CF-0-PSD
          (IMPLIES (AND (NOT (GOAL X Y))
                        (RATIONALP X) (RATIONALP Y))
                   (>= (CONE-CF-0 X Y) 0))
          :hints
          (("Goal" :in-theory
                   (enable CONE-CF-0 PROB-0 PROB-1 PROB-2)))
          :rule-classes (:linear )))

;; Monoid cofactors
 
 (LOCAL (DEFUND MONOID-CF-0 (X Y)
          (- (* X (* Y (EXPT (+ X Y) 2)))
             (EXPT (+ (* X X) (* Y Y)) 2))))

;; Positivstellensatz certificate
 
 (LOCAL (DEFUN CERT (X Y)
          (+ (MONOID-CF-0 X Y) (CONE-CF-0 X Y) 0)))

;; Contradictory results on the sign of the certificate
 
 (LOCAL (DEFTHMD CERT-KEY
          (IMPLIES (AND (RATIONALP X) (RATIONALP Y))
                   (= (CERT X Y) 0))
          :hints
          (("Goal" :in-theory
                   (enable SQUARE
                           CERT
                           PROB-0
                           PROB-1
                           PROB-2 CONE-CF-0 MONOID-CF-0)))))
 
 (LOCAL (DEFTHM CERT-CONTRA-M-0
          (IMPLIES (AND (NOT (GOAL X Y))
                        (RATIONALP X) (RATIONALP Y))
                   (> (MONOID-CF-0 X Y) 0))
          :hints
          (("Goal" :in-theory
                   (enable SQUARE
                           CERT
                           PROB-0
                           PROB-1
                           PROB-2 CONE-CF-0 MONOID-CF-0)))
          :rule-classes (:linear )))
 
 (LOCAL (DEFTHM CERT-CONTRA-C-0
          (IMPLIES (AND (NOT (GOAL X Y))
                        (RATIONALP X) (RATIONALP Y))
                   (>= (CONE-CF-0 X Y) 0))
          :rule-classes (:linear )))
 
 (LOCAL (DEFTHM CERT-CONTRA
          (IMPLIES (AND (NOT (GOAL X Y))
                        (RATIONALP X) (RATIONALP Y))
                   (NEQ (CERT X Y) 0))
          :rule-classes nil))

;; Main lemma
 
 (LOCAL (DEFTHM MAIN
          (IMPLIES (AND (RATIONALP X) (RATIONALP Y))
                   (GOAL X Y))
          :hints
          (("Goal" :in-theory
                   (disable GOAL)
                   :use (CERT-KEY CERT-CONTRA)))
          :rule-classes nil))

;; Final theorem
 
 (DEFTHM FINAL
   (IMPLIES (AND (RATIONALP X)
                 (RATIONALP Y) (<= 0 X) (<= 0 Y))
            (<= (* X Y (EXPT (+ X Y) 2))
                (EXPT (+ (* X X) (* Y Y)) 2)))
   :hints
   (("Goal" :in-theory
            (enable GOAL PROB-0 PROB-1 PROB-2) :use (MAIN )))
   :rule-classes nil)
)
