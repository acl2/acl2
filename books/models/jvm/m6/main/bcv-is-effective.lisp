; Verified code execute correctly on M6 produce the "same result" of safe
; execution.

(in-package "DJVM")

(include-book "m6-simple")
(include-book "djvm-simple")


;; (include-book "bcv-simple")

;----------------------------------------------------------------------

(include-book "djvm-is-safe")
(include-book "../DJVM/consistent-state-bcv-on-track")

;----------------------------------------------------------------------

(encapsulate () 
  (local (include-book "on-track-with-bcv-implies-next-inst-in-range"))
  (defthm consistent-state-strong-implies-wff-inst-next-inst
    (IMPLIES (and (CONSISTENT-STATE-STRONG djvm-S)
                  (consistent-state-bcv-on-track djvm-s))
             (WFF-INST (NEXT-INST djvm-S)))))


;;; note. the above has big skip-proofs in 
;;;
;;; on-track-with-bcv-implies-next-inst-in-range.lisp !!! 
;;;
;;; The idea is clear. If a recorded signaturate state exists at certain PC
;;; then we know that an instruction at that PC address exists. 
;;;

(encapsulate () 
 (local (include-book "step-preserve-state-equiv-if-on-track-with-bcv"))
 ;; the above book has lots of skip proofs in it. 
 ;;
 ;; It just illustrates how the leaf lemma theorems are to be used. 
 ;;
 (defthm step-preserve-state-equiv
   (implies (and (consistent-state-strong djvm-s)
                 (consistent-state-bcv-on-track djvm-s)
                 (state-equiv m6::m6-s djvm::djvm-s)
                 (bcv::verifyAll (external-class-table djvm-s)
                                 (external-class-table djvm-s))
                 (equal (next-inst djvm::djvm-s) inst))
   (state-equiv (m6::m6-step inst m6::m6-s)
                (djvm::djvm-step inst djvm::djvm-s)))))
;;
;; we proved other leaf level theorems for the following 
;;

(encapsulate () 
 (local (include-book "on-track-with-bcv-remain-on-track"))
 (defthm step-preserve-path
   (implies (and (consistent-state-strong djvm-s)
                 (consistent-state-bcv-on-track djvm-s)
                 (equal (next-inst djvm-s) inst))
            (consistent-state-bcv-on-track 
             (djvm::djvm-step inst djvm-s)))))


;
;----------------------------------------------------------------------
;----------------------------------------------------------------------


(skip-proofs 
 (defthm djvm-step-change-no-external-class-table
   (equal (external-class-table (djvm-step any s))
          (external-class-table s))))


(skip-proofs 
 (defthm state-equiv-implies-next-inst-equal
   (implies (state-equiv m6::m6-s djvm::djvm-s)
            (equal (next-inst m6::m6-s)
                   (next-inst djvm::djvm-s)))))


;----------------------------------------------------------------------

(defthm verified-program-executes-safely
  (implies (and (consistent-state-strong djvm-s)
                (consistent-state-bcv-on-track djvm-s)
                (state-equiv m6::m6-s djvm::djvm-s)
                (bcv::verifyAll (external-class-table djvm-s)
                                (external-class-table djvm-s)))
           (state-equiv (m6::m6-simple-run n m6::m6-s)
                        (djvm::djvm-simple-run n djvm::djvm-s)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable m6::m6-step
                               djvm::djvm-step
                               state-equiv
                               wff-inst
                               bcv::verifyAll
                               next-inst
                               consistent-state-strong
                               consistent-state-bcv-on-track
                               external-class-table))))

                                      

                
                
