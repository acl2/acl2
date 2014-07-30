
(include-book "wp-gen")

(ld "examples/sum.lisp") ; assigns sum program to global sum
;; Calculates the sum of integers from 1 to A_0101-1 (generated from an 8-bit
;; adding routine for the 6502).
(run-wp (@ sum) :count-var count :prefix wp-SUM)
;; Defuns WP-SUM-L_280, WP-SUM-L_282, WP-SUM-L_283, WP-SUM-L_286, 
;; WP-SUM-L_289 and WP-SUM-L_291.


(ld "examples/sum-simple.lisp") ; assigns sum-simple
;; A simpler version of sum-program.lisp
(run-wp (@ sum-simple) :count-var count :prefix wp-sum-simple)
;; Defuns WP-SUM-SIMPLE-L_INIT, WP-SUM-SIMPLE-L_280, 
;; WP-SUM-SIMPLE-L_282, WP-SUM-SIMPLE-L_283, WP-SUM-SIMPLE-L_286,
;; WP-SUM-SIMPLE-L_287 and WP-SUM-SIMPLE-L_291.


(ld "examples/sum-simpler.lisp") ; assigns sum-simpler
;; An even simpler version of sum-program.lisp
(run-wp (@ sum-simpler) :count-var count :prefix wp-sum-simpler)
;; Defuns WP-SUM-SIMPLER-L_INIT, WP-SUM-SIMPLER-L_280, 
;; WP-SUM-SIMPLER-L_282, WP-SUM-SIMPLER-L_283, 
;; WP-SUM-SIMPLER-L_286, WP-SUM-SIMPLER-L_287 and 
;; WP-SUM-SIMPLER-L_291.


(ld "examples/new-program.lisp") ; assigns new-prog
;; A program that does some basic assignments and then a branch to two possible
;; end states based on the value of a variable. The mutrec form detects that
;; the weakest precondition predicates are not mutually recursive.
(run-wp (@ new-prog) :prefix wp-NEW1 :mutrec t) ;; mutrec=t by default
;; Defuns WP-NEW1-L_1, WP-NEW1-L_2, WP-NEW1-L_3, WP-NEW1-L_BAD and
;; WP-NEW1-L_END.

(defthm wp-new1 (implies (= u 1641602559) (wp-new1-l_1 u v w)))

(run-wp (@ new-prog) :prefix wp-NEW1-nomutrec :mutrec nil :count-var count)
;; Defuns WP-NEW1-NOMUTREC-L_END, WP-NEW1-NOMUTREC-L_BAD, 
;; WP-NEW1-NOMUTREC-L_3, WP-NEW1-NOMUTREC-L_2 and WP-NEW1-NOMUTREC-L_1.

;; (defthm wp-new1-b (implies (= u 1641602559) (wp-new1-nomutrec-l_1 u v w c)))
;; Cannot prove this theorem because ACL2 tries to induct and can't find an
;; induction scheme.

(ld "examples/new-program2.lisp") ; assigns new-prog2
(run-wp (@ new-prog2) :count-var count :prefix wp-NEW2)
;; Defuns WP-NEW2-L_1, WP-NEW2-L_2, WP-NEW2-L_25, WP-NEW2-L_3, WP-NEW2-L_BAD
;; and WP-NEW2-L_END.


(ld "examples/false-prog.lisp") ; assigns false-prog
(run-wp (@ false-prog) :prefix wp-F)
;; Defuns WP-F-L_INIT, WP-F-L_280, WP-F-L_282, WP-F-L_283, WP-F-L_286,
;; WP-F-L_287 and WP-F-L_291.

(ld "examples/sum-simple-wrong.lisp") ; assigns sum-simple-wrong
(run-wp (@ sum-simple-wrong) :count-var count :prefix wp-sum-wrong)
;; Defuns WP-SUM-WRONG-L_INIT, WP-SUM-WRONG-L_280, WP-SUM-WRONG-L_282,
;; WP-SUM-WRONG-L_283, WP-SUM-WRONG-L_286, WP-SUM-WRONG-L_287 and 
;; WP-SUM-WRONG-L_291.


;; It would be nice to be able to prove general theorems about functions that
;; are (almost) always nil!!