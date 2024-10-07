(in-package "DJVM")
(include-book "../main/djvm-simple")
(include-book "../main/m6-simple")
(include-book "../DJVM/consistent-state-bcv-on-track")
(include-book "../BCV/typechecker-simple")

;----------------------------------------------------------------------

;; this proof depends on the leaf lemma that 
;; execution is monotonic!! 
;;

;; (encapsulate () 
;;      (local (include-book "base-bcv-step-monotonic"))
;;      (defthm AALOAD-monotonicity
;;        (implies (and (bcv::sig-frame-more-general gframe sframe env1)
;;                      (bcv::consistent-sig-stack (bcv::frameStack sframe) icl)
;;                      (bcv::consistent-sig-stack (bcv::frameStack gframe) icl)
;;                      (not (equal (bcv::nth1OperandStackIs 2 gframe) 'NULL))
;;                      (not (equal (bcv::nth1OperandStackIs 2 sframe) 'NULL))
;;                      (bcv::check-AALOAD inst env1 gframe) 
;;                      (bcv::check-AALOAD inst env1 sframe) 
;;                      (bcv::good-icl icl)
;;                      (bcv::good-scl (bcv::classtableEnvironment env1))
;;                      (bcv::icl-scl-compatible icl (bcv::classtableEnvironment env1)))
;;                 (bcv::sig-frame-more-general 
;;                  (bcv::normal-frame (bcv::execute-AALOAD inst env gframe))
;;                  (bcv::normal-frame (bcv::execute-AALOAD inst env sframe)) env1))))

;;;;;;; 

;;
;; (encapsulate () 
;;        (local   (include-book "base-next-state-more-specific"))
;;        (defthm next-state-no-more-general-aaload
;;          (mylet* ((oframe (frame-sig (current-frame s)
;;                                      (instance-class-table s)
;;                                      (heap s)
;;                                      (heap-init-map (aux s))))
;;                   (ns   (djvm::execute-aaload inst s))
;;                   (nframe (frame-sig (current-frame ns)
;;                                      (instance-class-table ns)
;;                                      (heap ns)
;;                                      (heap-init-map (aux ns)))))
;;                  (implies (and (consistent-state s)
;;                                (bcv::check-aaload inst (env-sig s) oframe)
;;                                (djvm::check-aaload inst s)
;;                                (not (check-null (topStack (popStack s))))
;;                                (check-array (RREF (topStack (popStack s))) 
;;                                             (value-of (topStack s)) s))
;;                           (bcv::sig-frame-more-general 
;;                            (car (bcv::execute-aaload inst 
;;                                                      (env-sig s)
;;                                                      oframe))
;;                            nframe
;;                            (env-sig s))))
;;          :hints (("Goal" :in-theory (disable 
;;                                      ;;djvm::check-aaload
;;                                      ;;bcv::check-aaload
;;                                      djvm::execute-aaload
;;                                      bcv::execute-aaload
;;                                      bcv::isAssignable
;;                                      check-null
;;                                      frame-push-value-sig)
;;                   :cases ((NULLp (TAG-REF (ELEMENT-AT-ARRAY (VALUE-OF (TOPSTACK S))
;;                                                             (RREF (TOPSTACK (POPSTACK S)))
;;                                                             S))))))))

;;;
;;;
;;; we als need theorems that says that execute-AALOAD does not change 
;;; other frames, nor other threads!!! 
;;;

;----------------------------------------------------------------------

;; if there is an exception we will know that 
;; the entrance to the exception handler is OK, because 
;; bcv-simple-method checked that. 


;----------------------------------------------------------------------

;;
;; (skip-proofs 
;; (defthm step-remains-on-track-AALOAD
;;   (implies (and (consistent-state-strong djvm::djvm-s)
;;                 (consistent-state-bcv-on-track djvm::djvm-s)
;;                 (equal (next-inst djvm::djvm-s) inst)
;;                 (equal (bcv::op-code inst) 'AALOAD))
;;            (consistent-state-bcv-on-track
;;             (execute-AALOAD inst djvm::djvm-s)))
;;   :hints (("Goal" :cases ((nullp (topStack (popstack djvm::djvm-s)))))))

;----------------------------------------------------------------------

(skip-proofs 
 (defthm step-preserve-path
   (implies (and (consistent-state-strong djvm-s)
                 (consistent-state-bcv-on-track djvm-s)
                 (equal (next-inst djvm-s) inst))
            (consistent-state-bcv-on-track 
             (djvm::djvm-step inst djvm-s)))))

