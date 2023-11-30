;;
;; Theorem (over ℝ):
;;
;; (>= (+ (EXPT x 4) (EXPT y 4) (EXPT z 4) 1 (- 0 (* 4 x y z)))
;;     0).
;;
;; Proof found by Imandra in 0.224749 secs.
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
 
 (LOCAL (DEFUND PROB-0 (X Y Z)
          (- 0
             (+ (EXPT X 4)
                (+ (EXPT Y 4)
                   (+ (EXPT Z 4)
                      (+ 1 (- 0 (* 4 (* X (* Y Z)))))))))))

;; Normalized goal expressed using problem polynomials
 
 (LOCAL (DEFUN GOAL (X Y Z)
          (IMPLIES (AND (RATIONALP X)
                        (RATIONALP Y) (RATIONALP Z))
                   (NOT (AND (> (PROB-0 X Y Z) 0))))))

;; Ideal cofactors

;; Cone cofactors
 
 (LOCAL (DEFUND CONE-CF-0 (X Y Z)
          (+ (SQUARE (+ (* -1/3 (EXPT X 2))
                        (+ (* -1/3 (EXPT Y 2))
                           (+ (* -1/3 (EXPT Z 2)) 1))))
             (+ (* 2/3 (SQUARE (+ (* -1 (* Y Z)) X)))
                (+ (* 8/9
                      (SQUARE (+ (EXPT X 2)
                                 (+ (* -1/2 (EXPT Y 2))
                                    (* -1/2 (EXPT Z 2))))))
                   (+ (* 2/3 (SQUARE (+ (* -1 (* X Y)) Z)))
                      (+ (* 2/3
                            (SQUARE (+ (* X Z) (* -1 Y))))
                         (* 2/3
                            (SQUARE (+ (* -1 (EXPT Y 2))
                                       (EXPT Z 2)))))))))))
 
 (LOCAL (DEFTHM CONE-CF-0-TYPE
          (IMPLIES (AND (RATIONALP X)
                        (RATIONALP Y) (RATIONALP Z))
                   (RATIONALP (CONE-CF-0 X Y Z)))
          :hints
          (("Goal" :in-theory (enable CONE-CF-0)))))
 
 (LOCAL (DEFTHM CONE-CF-0-PSD
          (IMPLIES (AND (NOT (GOAL X Y Z))
                        (RATIONALP X)
                        (RATIONALP Y) (RATIONALP Z))
                   (>= (CONE-CF-0 X Y Z) 0))
          :hints
          (("Goal" :in-theory (enable CONE-CF-0 PROB-0)))
          :rule-classes (:linear )))

;; Monoid cofactors
 
 (LOCAL (DEFUND MONOID-CF-0 (X Y Z)
          (- 0
             (+ (EXPT X 4)
                (+ (EXPT Y 4)
                   (+ (EXPT Z 4)
                      (+ 1 (- 0 (* 4 (* X (* Y Z)))))))))))

;; Positivstellensatz certificate
 
 (LOCAL (DEFUN CERT (X Y Z)
          (+ (MONOID-CF-0 X Y Z) (CONE-CF-0 X Y Z) 0)))

;; Contradictory results on the sign of the certificate
 
 (LOCAL (DEFTHMD CERT-KEY
          (IMPLIES (AND (RATIONALP X)
                        (RATIONALP Y) (RATIONALP Z))
                   (= (CERT X Y Z) 0))
          :hints
          (("Goal" :in-theory
                   (enable SQUARE
                           CERT PROB-0 CONE-CF-0 MONOID-CF-0)))))
 
 (LOCAL (DEFTHM CERT-CONTRA-M-0
          (IMPLIES (AND (NOT (GOAL X Y Z))
                        (RATIONALP X)
                        (RATIONALP Y) (RATIONALP Z))
                   (> (MONOID-CF-0 X Y Z) 0))
          :hints
          (("Goal" :in-theory
                   (enable SQUARE
                           CERT PROB-0 CONE-CF-0 MONOID-CF-0)))
          :rule-classes (:linear )))
 
 (LOCAL (DEFTHM CERT-CONTRA-C-0
          (IMPLIES (AND (NOT (GOAL X Y Z))
                        (RATIONALP X)
                        (RATIONALP Y) (RATIONALP Z))
                   (>= (CONE-CF-0 X Y Z) 0))
          :rule-classes (:linear )))
 
 (LOCAL (DEFTHM CERT-CONTRA
          (IMPLIES (AND (NOT (GOAL X Y Z))
                        (RATIONALP X)
                        (RATIONALP Y) (RATIONALP Z))
                   (NEQ (CERT X Y Z) 0))
          :rule-classes nil))

;; Main lemma
 
 (LOCAL (DEFTHM MAIN
          (IMPLIES (AND (RATIONALP X)
                        (RATIONALP Y) (RATIONALP Z))
                   (GOAL X Y Z))
          :hints
          (("Goal" :in-theory
                   (disable GOAL)
                   :use (CERT-KEY CERT-CONTRA)))
          :rule-classes nil))

;; Final theorem
 
 (DEFTHM FINAL
   (IMPLIES (AND (RATIONALP X) (RATIONALP Y) (RATIONALP Z))
            (>= (+ (EXPT X 4)
                   (EXPT Y 4) (EXPT Z 4) 1 (- 0 (* 4 X Y Z)))
                0))
   :hints
   (("Goal" :in-theory (enable GOAL PROB-0) :use (MAIN )))
   :rule-classes nil)
)
