(in-package "ACL2")
(include-book "bcv-model")
(include-book "bcv-simple-model")
(include-book "generic")



(defthm member-extract-code-implied-by-member-merged-code-and-inst
  (implies (and (merged-code-safe merged-code sig-frame) 
                (member inst merged-code)
                (inst? inst))
           (member inst (extract-code merged-code))))


(local 
 (defthm g-pc-collect-witness-pc
   (implies (bound? pc (collect-witness-merged-code-safe merged-code
                                                         sig-frame))
            (equal (g 'pc (cdr (assoc-equal pc 
                                            (collect-witness-merged-code-safe
                                             merged-code sig-frame))))
                   pc))))



(defthm member-inst-extract-code-implies-bound-pc
  (implies (and (merged-code-safe merged-code sig-frame)
                (member inst (extract-code merged-code)))
           (ASSOC-EQUAL (G 'PC INST)
                        (COLLECT-WITNESS-MERGED-CODE-SAFE MERGED-CODE SIG-FRAME))))


;----------------------------------------------------------------------

(defthm merged-code-safe-implies-current-inst-is-bound
   (implies (AND (MERGED-CODE-SAFE MERGED-CODE SIG-FRAME)
                 (MEMBER INST MERGED-CODE)
                 (INST? INST))
            (equal (g 'pc (cdr (assoc-equal (g 'pc inst)
                                            (collect-witness-merged-code-safe
                                             merged-code sig-frame))))
                   (g 'pc inst))))


;; (defthm merged-code-safe-implies-PUSH-is-NOT-THE-LAST-INST
;;   (implies (AND (EQUAL (CAR (G 'INST INST)) 'PUSH)
;;                 (MERGED-CODE-SAFE MERGED-CODE SIG-FRAME)
;;                 (MEMBER INST MERGED-CODE)
;;                 (INST? INST))
;;            (assoc-equal 
;;             (+ 1 (g 'pc inst))
;;             (collect-witness-merged-code-safe 
;;              merged-code sig-frame)))
;;   :hints (("Goal" :do-not '(generalize))))


(defthm car-bcv-simple-execute-step-is-bcv-execute-step
  (implies (member (car (g 'inst inst)) '(PUSH POP IFEQ INVOKE))
           (equal (car (bcv-simple-execute-step (g 'inst inst) sig-frame))
                  (bcv-execute-step inst sig-frame))))


;----------------------------------------------------------------------
  
;; ;;;;
;; ;;;;   Shall we prove the following by induction directly? no.
;; ;;;;   
;; ;;;;   We will first prove when the first instruction is an instruction
;; ;;;;  

;; (defthm merge-code-safe-implies-sig-frame-compatible-lemma
;;   (implies (and ;;; (case-split (member (bcv-op-code inst) '(PUSH POP IFEQ INVOKE))))))
;;                 ;;; (not (member (bcv-op-code inst) '(HALT RETURN)))
;;                 (case-split (member (bcv-op-code inst) '(PUSH)))
;;                 (merged-code-safe merged-code sig-frame)
;;                 (wff-code1 (extract-code merged-code) (g 'pc (car merged-code)))
;;                 (member inst merged-code)
;;                 (inst? inst)
;;                 (equal pc (g 'pc inst)))
;;            (sig-frame-compatible
;;             (bcv-execute-step inst 
;;                               (cdr (assoc-equal pc
;;                                                 (collect-witness-merged-code-safe merged-code sig-frame))))
;;             (cdr (assoc-equal (+ 1 pc)
;;                               (collect-witness-merged-code-safe 
;;                                merged-code sig-frame)))))
;;   :hints (("Goal" :in-theory (disable inst? stack-map?
;;                                       sig-frame-compatible
;;                                       bcv-simple-execute-step
;;                                       bcv-execute-step
;;                                       bcv-check-step-pre)
;;            :do-not '(generalize fertilize))))

(defthm not-equal-g-not-equal
  (implies (not (equal (g 'pc X) (g 'pc Y)))
           (not (equal X Y)))
  :rule-classes nil)



(defthm s-never-AFTERGOTO
  (not (equal (s 'pc (+ 1 x) Any2) 'AFTERGOTO))
  :hints (("Goal" :use ((:instance not-equal-g-not-equal
                                   (X (s 'pc (+ 1 x) any2))
                                   (Y 'AFTERGOTO))))))
                               

(defthm bcv-execute-step-is-not-aftergoto
  (implies (not (member (car (g 'inst inst)) '(HALT RETURN)))
           (not (equal (bcv-execute-step inst sig-frame)
                       'AFTERGOTO))))

;----------------------------------------------------------------------

(defthm not-merge-code-safe-aftr-goto
  (implies (inst? (car merged-code)) 
           (not (merged-code-safe merged-code 'aftergoto))))


(defthm inst-stack-map-more-general
  (implies (and (merged-code-safe merged-code sig-frame)
                (inst? (car merged-code))
                (not (member (bcv-op-code (car merged-code)) '(HALT RETURN)))
                (stack-map? (cadr merged-code)))
           (sig-frame-compatible
            (bcv-execute-step (car merged-code) sig-frame)
            (cadr merged-code)))
  :hints (("Goal" :in-theory (e/d () (bcv-execute-step
                                      inst? stack-map?
                                      sig-frame-compatible))
           :do-not '(generalize)
           :do-not-induct t)))


(defun stack-map-prefix (merge-code)
  (if (endp merge-code) nil
    (if (inst? (car merge-code)) nil
      (cons (car merge-code)
            (stack-map-prefix (cdr merge-code))))))


(defthm merge-code-safe-implies-first-assignable-to-any-in-the-prefix
  (implies (and (merged-code-safe merge-code sig-frame)
                (stack-map? (car merge-code))
                (member any-stack-map (stack-map-prefix merge-code)))
           (sig-frame-compatible 
                     (car merge-code) 
                     any-stack-map)))


(defthm merge-code-safe-equal-assoc-equal-is-last
  (implies (and (merged-code-safe merge-code sig-frame)
                (stack-map? (car merge-code)))
           (equal (cdr (assoc-equal (g 'pc (car merge-code))
                                    (collect-witness-merged-code-safe
                                     merge-code sig-frame)))
                  (car (last (stack-map-prefix merge-code)))))
  :hints (("Goal" :in-theory (e/d () (stack-map? inst?)))))
                       
                
(defthm member-last-stack-map-prefix
  (implies (consp l)
           (member (car (last l)) l)))



(defthm merge-code-safe-equal-assoc-equal-is-last-general
  (implies (and (merged-code-safe merge-code sig-frame)
                (stack-map? (car merge-code))
                (equal pc (g 'pc (car merge-code))))
           (equal (cdr (assoc-equal pc
                                    (collect-witness-merged-code-safe
                                     merge-code sig-frame)))
                  (car (last (stack-map-prefix merge-code)))))
  :hints (("Goal" :in-theory (e/d () (stack-map? inst?)))))



(encapsulate ()
 (local (include-book "bcv-find-correct-witness-bcv-check-pre"))             
 (defthm wff-code1-uniqueness
   (IMPLIES
    (AND (WFF-CODE1 (EXTRACT-CODE MERGED-CODE4) any)
         (MERGED-CODE-SAFE MERGED-CODE4 MERGED-CODE3))
    (wff-code1 (extract-code merged-code4)
               (g 'pc (car merged-code4))))
   :rule-classes :forward-chaining))

(encapsulate () 
 (local (include-book "bcv-find-correct-witness-bcv-check-pre"))
 (defthm merged-code-safe-implies-extract-code-pc-is-same-strong
   (implies (merged-code-safe merged-code sig-frame)
            (equal (g 'pc (car (extract-code merged-code)))
                   (g 'pc (car merged-code))))))


(defthm two-adjacent-instructions-pc-adjacent-2
  (implies (and (merged-code-safe merged-code sig-frame)
                (wff-code1 (extract-code merged-code)
                           (g 'pc (car merged-code)))
                (inst? (car merged-code))
                (stack-map? (cadr merged-code)))
           (equal (+ 1 (g 'pc (car merged-code)))
                  (g 'pc (cadr merged-code))))
  :hints (("Goal" :in-theory (e/d () (inst? stack-map?))
           :do-not '(generalize fertilize))))

(local 
 (defthm merged-code-safe-implies-pc-equal
   (implies (and (merged-code-safe merged-code sig-frame)
                 (inst? (car merged-code)))
            (equal (g 'pc sig-frame)
                   (g 'pc (car merged-code))))))


(defthm two-adjacent-instructions-pc-adjacent-2-specific
  (implies (and (merged-code-safe merged-code sig-frame)
                (wff-code1 (extract-code merged-code)
                           (g 'pc (car merged-code)))
                (inst? (car merged-code))
                (stack-map? (cadr merged-code)))
           (equal (+ 1 (g 'pc sig-frame))
                  (g 'pc (cadr merged-code))))
  :hints (("Goal" :in-theory (e/d () (inst? wff-code1
                                      merged-code-safe
                                      stack-map?)))))


(local (in-theory (disable merged-code-safe-implies-pc-equal)))




(local 
 (defthm sig-frame-compatible-transitive
   (implies (and (sig-frame-compatible frame1 frame2)
                 (sig-frame-compatible frame2 frame3))
            (sig-frame-compatible frame1 frame3))))


(defthm wff-code-implies-not-equal
  (implies  (and  (merged-code-safe merged-code sig-frame)
                  (WFF-CODE1 (EXTRACT-CODE MERGED-CODE)
                             (+ 1 pc))
                  (stack-map? (car merged-code)))
            (not (equal (g 'pc (car merged-code)) pc))))

(local 
 (defthm sig-frame-compatible-reflexive
   (SIG-FRAME-COMPATIBLE stack-map stack-map)))



(defthm member-last-stack-map-prefix
  (implies (consp l)
           (member (car (last l)) l)))


(defthm consp-stack-map-prefix
  (implies (stack-map? (car merged-code))
           (consp (stack-map-prefix merged-code))))


(defthm inst-stack-map-more-general-specific
  (implies (and (merged-code-safe merged-code sig-frame)
                (inst? (car merged-code))
                (not (member (bcv-op-code (car merged-code)) '(HALT RETURN)))
                (stack-map? (cadr merged-code)))
           (sig-frame-compatible
            (bcv-execute-step (car merged-code) sig-frame)
            (car (last (stack-map-prefix (cdr merged-code))))))
  :hints (("Goal" :in-theory (e/d () (bcv-execute-step
                                      bcv-check-step-pre
                                      inst? stack-map?
                                      sig-frame-compatible))
           :use ((:instance 
                  sig-frame-compatible-transitive
                  (frame1 (bcv-execute-step (car merged-code) sig-frame))
                  (frame2 (cadr merged-code))
                  (frame3 (car (last (stack-map-prefix (cdr merged-code)))))))
           :restrict
           ((merge-code-safe-implies-first-assignable-to-any-in-the-prefix
             ((sig-frame (bcv-execute-step (car merged-code) sig-frame)))))
           :do-not '(generalize)
           :do-not-induct t)))


(defthm execute-inst-compatible-with-stack-1
  (implies (and (merged-code-safe merged-code sig-frame)
                (inst? (car merged-code))
                (wff-code1 (extract-code merged-code) 
                           (g 'pc sig-frame))
                (not (member (bcv-op-code (car merged-code)) '(HALT RETURN)))
                (stack-map? (cadr merged-code))
                (equal pc (+ 1 (g 'pc (car merged-code)))))
           (sig-frame-compatible
            (bcv-execute-step (car merged-code) sig-frame)
            (cdr (assoc-equal pc (collect-witness-merged-code-safe merged-code sig-frame)))))
   :hints (("Goal" :in-theory (e/d () (bcv-execute-step
                                       bcv-check-step-pre
                                       inst? stack-map?
                                       ;;wff-code1
                                       ;;extract-code
                                       sig-frame-compatible))
            :restrict ((two-adjacent-instructions-pc-adjacent-2-specific 
                        ((merged-code merged-code))))
            :do-not '(generalize)
            :do-not-induct t)))


(defthm two-adjacent-instructions-pc-adjacent
  (implies (and (merged-code-safe merged-code sig-frame)
                (inst? (car merged-code))
                (inst? (cadr merged-code)))
           (equal (+ 1 (g 'pc (car merged-code)))
                  (g 'pc (cadr merged-code)))))

(defthm bcv-execute-step-produces-a-specific-state
  (implies (and (merged-code-safe merged-code sig-frame)
                (inst? (car merged-code))
                (inst? (cadr merged-code))
                (not (member (bcv-op-code (car merged-code)) '(HALT RETURN)))
                (equal pc (g 'pc (cadr merged-code))))
           (equal (cdr (assoc-equal pc
                                    (collect-witness-merged-code-safe
                                     merged-code sig-frame)))
                  (bcv-execute-step (car merged-code) sig-frame)))
  :hints (("Goal" :in-theory (e/d ()(bcv-execute-step
                                     bcv-check-step-pre
                                     two-adjacent-instructions-pc-adjacent
                                     sig-frame-compatible
                                     inst? stack-map?))
           :do-not '(generalize fertilize)
           :use ((:instance two-adjacent-instructions-pc-adjacent))
           :do-not-induct t)))


(defthm execute-inst-compatible-with-stack-2
  (implies (and (merged-code-safe merged-code sig-frame)
                (inst? (car merged-code))
                (wff-code1 (extract-code merged-code) 
                           (g 'pc sig-frame))
                (not (member (bcv-op-code (car merged-code)) '(HALT RETURN)))
                (inst? (cadr merged-code))
                (equal pc (+ 1 (g 'pc (car merged-code)))))
           (sig-frame-compatible
            (bcv-execute-step (car merged-code) sig-frame)
            (cdr (assoc-equal pc (collect-witness-merged-code-safe merged-code sig-frame)))))
   :hints (("Goal" :in-theory (e/d () (bcv-execute-step
                                       bcv-check-step-pre
                                       inst? stack-map?
                                       sig-frame-compatible))
            :do-not '(generalize)
            :do-not-induct t)))


;----------------------------------------------------------------------

(defthm execute-inst-compatible-with-stack
  (implies (and (merged-code-safe merged-code sig-frame)
                (inst? (car merged-code))
                (wff-code1 (extract-code merged-code) 
                           (g 'pc sig-frame))
                (not (member (bcv-op-code (car merged-code)) '(HALT RETURN)))
                (equal pc (+ 1 (g 'pc (car merged-code)))))
           (sig-frame-compatible
            (bcv-execute-step (car merged-code) sig-frame)
            (cdr (assoc-equal pc (collect-witness-merged-code-safe merged-code sig-frame)))))
   :hints (("Goal" :in-theory (e/d () (bcv-execute-step
                                       bcv-check-step-pre
                                       inst? stack-map?
                                       execute-inst-compatible-with-stack-1
                                       sig-frame-compatible))
            :cases ((inst? (cadr merged-code))
                    (stack-map? (cadr merged-code)))
            :do-not '(generalize)
            :do-not-induct t)
           ("Subgoal 1.1" :use ((:instance execute-inst-compatible-with-stack-1
                                           (pc (+ 1 (g 'pc (car merged-code)))))))))


;----------------------------------------------------------------------

(defthm |Subgoal *1/9.3|
  (IMPLIES
   (AND (CONSP MERGED-CODE2)
        (NOT (EQUAL SIG-FRAME 'AFTERGOTO))
        (NOT (MEMBER MERGED-CODE1 MERGED-CODE2))
        (NOT (EQUAL (CAR (G 'INST MERGED-CODE1))
                    'HALT))
        (NOT (EQUAL (CAR (G 'INST MERGED-CODE1))
                    'RETURN))
        (WFF-CODE1 (EXTRACT-CODE MERGED-CODE2)
                   (+ 1 (G 'PC MERGED-CODE1)))
        (INST? MERGED-CODE1)
        (EQUAL (G 'PC SIG-FRAME)
               (G 'PC MERGED-CODE1))
        (BCV-CHECK-STEP-PRE MERGED-CODE1 SIG-FRAME)
        (MERGED-CODE-SAFE MERGED-CODE2
                          (BCV-EXECUTE-STEP MERGED-CODE1 SIG-FRAME))
        (NOT (EQUAL (+ 1 (G 'PC MERGED-CODE1))
                    (G 'PC MERGED-CODE1))))
   (SIG-FRAME-COMPATIBLE
    (BCV-EXECUTE-STEP MERGED-CODE1 SIG-FRAME)
    (CDR (ASSOC-EQUAL (+ 1 (G 'PC MERGED-CODE1))
                      (COLLECT-WITNESS-MERGED-CODE-SAFE
                       MERGED-CODE2
                       (BCV-EXECUTE-STEP MERGED-CODE1 SIG-FRAME))))))
    :hints (("Goal" :in-theory (disable inst? stack-map?
                                      sig-frame-compatible
                                      execute-inst-compatible-with-stack
                                      bcv-simple-execute-step
                                      bcv-execute-step
                                      bcv-check-step-pre)
             :use ((:instance execute-inst-compatible-with-stack
                              (pc (+ 1 (g 'pc (car merged-code))))))
           :do-not '(generalize fertilize))))


(defthm collect-witness-merged-code-safe-normalize
  (implies (and (merged-code-safe merged-code sig-frame)
                (inst? (car merged-code))
                (< (g 'pc (car merged-code)) pc))
           (equal 
            (CDR
             (ASSOC-EQUAL PC
                          (COLLECT-WITNESS-MERGED-CODE-SAFE MERGED-CODE SIG-FRAME)))
            (cdr (ASSOC-EQUAL PC
                              (COLLECT-WITNESS-MERGED-CODE-SAFE (CDR MERGED-CODE)
                                                                (BCV-EXECUTE-STEP (CAR MERGED-CODE)
                                                                                  SIG-FRAME))))))
  :hints (("Goal" :in-theory (disable bcv-execute-step bcv-check-step-pre
                                      sig-frame-compatible
                                      inst?)
           :do-not '(generalize))))

;; (defthm collect-witness-merged-member-remainer
;;   (implies (and (wff-code1 (extract-code merged-code) 
;;                            (g 'pc (car merged-code)))
;;                 (inst? (car merged-code))
;;                 (member inst (cdr merged-code))
;;                 (inst? inst))
;;            (< (g 'pc (car merged-code)) 
;;               (g 'pc inst)))
;;   :hints (("Goal" :do-not '(generalize))))


(defthm member-inst-merged-code-implies-not-equal
  (implies (and (member inst code)
                (wff-code1 code pc))
           (<= pc (g 'pc inst)))
  :hints (("Goal" :in-theory (e/d () (inst? stack-map?))
           :do-not '(generalize))))





(defthm member-inst-merged-code-implies-not-equal-specific
  (implies (and (member inst merged-code)
                (merged-code-safe merged-code sig-frame)
                (inst? inst)
                (wff-code1 (extract-code merged-code) (+ 1 pc)))
           (< pc (g 'pc inst)))
  :hints (("Goal" :in-theory (e/d () (inst? stack-map?))
           :use ((:instance member-inst-merged-code-implies-not-equal
                            (code (extract-code merged-code))
                            (pc (+ 1 pc))))
           :do-not '(generalize)
           :do-not-induct t)))



(defthm member-inst-merged-code-implies-not-equal-futher
  (implies (and (member inst merged-code)
                (merged-code-safe merged-code sig-frame)
                (inst? inst)
                (wff-code1 (extract-code merged-code) (+ 1 pc)))
           (not (equal (+ 1 (g 'pc inst)) pc)))
  :hints (("Goal" :in-theory (e/d () (inst? stack-map?))
           :use ((:instance member-inst-merged-code-implies-not-equal
                            (code (extract-code merged-code))
                            (pc (+ 1 pc))))
           :do-not '(generalize)
           :do-not-induct t)))


(defthm member-inst-merged-code-implies-not-equal-futher-2
  (implies (and (member inst merged-code)
                (merged-code-safe merged-code sig-frame)
                (inst? inst)
                (wff-code1 (extract-code merged-code) (+ 1 pc)))
           (not (equal (g 'pc inst) pc)))
  :hints (("Goal" :in-theory (e/d () (inst? stack-map?))
           :use ((:instance member-inst-merged-code-implies-not-equal
                            (code (extract-code merged-code))
                            (pc (+ 1 pc))))
           :do-not '(generalize)
           :do-not-induct t)))



(defthm |Subgoal *1/9.12.1''|
  (IMPLIES
   (AND
    (CONSP MERGED-CODE2)
    (NOT (EQUAL SIG-FRAME 'AFTERGOTO))
    (SIG-FRAME-COMPATIBLE
     (BCV-EXECUTE-STEP
      MERGED-CODE1
      (CDR (ASSOC-EQUAL (G 'PC MERGED-CODE1)
                        (COLLECT-WITNESS-MERGED-CODE-SAFE
                         MERGED-CODE2
                         (BCV-EXECUTE-STEP MERGED-CODE1 SIG-FRAME)))))
     (CDR (ASSOC-EQUAL (+ 1 (G 'PC MERGED-CODE1))
                       (COLLECT-WITNESS-MERGED-CODE-SAFE
                        MERGED-CODE2
                        (BCV-EXECUTE-STEP MERGED-CODE1 SIG-FRAME)))))
    (NOT (EQUAL (CAR (G 'INST MERGED-CODE1))
                'HALT))
    (NOT (EQUAL (CAR (G 'INST MERGED-CODE1))
                'RETURN))
    (WFF-CODE1 (EXTRACT-CODE MERGED-CODE2)
               (+ 1 (G 'PC MERGED-CODE1)))
    (INST? MERGED-CODE1)
    (EQUAL (G 'PC SIG-FRAME)
           (G 'PC MERGED-CODE1))
    (BCV-CHECK-STEP-PRE MERGED-CODE1 SIG-FRAME)
    (MERGED-CODE-SAFE MERGED-CODE2
                      (BCV-EXECUTE-STEP MERGED-CODE1 SIG-FRAME))
    (NOT (EQUAL (+ 1 (G 'PC MERGED-CODE1))
                (G 'PC MERGED-CODE1))))
   (SIG-FRAME-COMPATIBLE
    (BCV-EXECUTE-STEP MERGED-CODE1 SIG-FRAME)
    (CDR (ASSOC-EQUAL (+ 1 (G 'PC MERGED-CODE1))
                      (COLLECT-WITNESS-MERGED-CODE-SAFE
                       MERGED-CODE2
                       (BCV-EXECUTE-STEP MERGED-CODE1 SIG-FRAME))))))
    :hints (("Goal" :in-theory (disable inst? stack-map?
                                      sig-frame-compatible
                                      execute-inst-compatible-with-stack
                                      bcv-simple-execute-step
                                      bcv-execute-step
                                      bcv-check-step-pre)
             :use ((:instance execute-inst-compatible-with-stack
                              (pc (+ 1 (g 'pc (car merged-code))))))
           :do-not '(generalize fertilize))))

;;;
;;; not sure what the above says!! 
;;; Don't understand why the above need induction!!! 
;;; anyway!! 
;;;


(defthm merge-code-safe-implies-sig-frame-compatible-lemma-lemma
  (IMPLIES
   (AND (not (member (bcv-op-code inst) '(HALT RETURN)))
        (WFF-CODE1 (extract-code MERGED-CODE) (G 'PC (car MERGED-CODE)))
        (inst? inst)
        (MERGED-CODE-SAFE MERGED-CODE sig-frame)
        (member inst merged-code)
        (equal pc (g 'pc inst)))
   (SIG-FRAME-COMPATIBLE
    (BCV-EXECUTE-STEP 
     inst 
     (cdr (assoc-equal pc (collect-witness-merged-code-safe merged-code sig-frame))))
    (CDR (ASSOC-EQUAL (+ 1 pc)
                      (COLLECT-WITNESS-MERGED-CODE-SAFE
                       merged-code sig-frame)))))
  :hints (("Goal" :in-theory (disable inst? stack-map?
                                      sig-frame-compatible
                                      bcv-simple-execute-step
                                      bcv-execute-step
                                      bcv-check-step-pre)
           :do-not '(generalize fertilize))))




;----------------------------------------------------------------------

(defthm merge-code-safe-implies-sig-frame-compatible-lemma
  (implies (and (case-split (member (bcv-op-code inst) '(PUSH POP IFEQ INVOKE)))
                (merged-code-safe merged-code sig-frame)
                (wff-code1 (extract-code merged-code)
                           (g 'pc (car merged-code)))
                (member inst merged-code)
                (inst? inst)
                (equal pc (g 'pc inst)))
           (sig-frame-compatible
            (car (bcv-simple-execute-step (g 'inst inst)
                                          (cdr (assoc-equal pc
                                                            (collect-witness-merged-code-safe merged-code sig-frame)))))
            (cdr (assoc-equal (+ 1 pc) 
                              (collect-witness-merged-code-safe 
                               merged-code sig-frame)))))
  :hints (("Goal" :in-theory (disable inst?
                                      sig-frame-compatible
                                      bcv-simple-execute-step
                                      bcv-execute-step
                                      bcv-check-step-pre)
           :do-not-induct t)))



;----------------------------------------------------------------------

(defthm member-extract-code-member-merged-code-f
  (implies (member inst (extract-code merged-code))
           (member inst merged-code))
  :rule-classes :forward-chaining)

(defthm member-extract-code-inst-f
  (implies (member inst (extract-code merged-code))
           (inst? inst))
  :rule-classes :forward-chaining)


(defthm merge-code-safe-implies-sig-frame-compatible
  (implies (and (case-split (member (bcv-op-code inst) '(PUSH POP IFEQ INVOKE)))
                (merged-code-safe merged-code sig-frame)
                (equal (g 'pc sig-frame) 0)
                (wff-code (extract-code merged-code))
                (member inst (extract-code merged-code))
                (equal pc (g 'pc inst)))
           (sig-frame-compatible
            (car (bcv-simple-execute-step (g 'inst inst)
                                          (cdr (assoc-equal pc
                                                            (collect-witness-merged-code-safe merged-code sig-frame)))))
            (cdr (assoc-equal (+ 1 pc) 
                              (collect-witness-merged-code-safe 
                               merged-code sig-frame)))))
  :hints (("Goal" :in-theory (disable inst? bcv-simple-execute-step
                                      bcv-execute-step
                                      sig-frame-compatible
                                      inst? member bcv-op-code
                                      bcv-check-step-pre)
           :use ((:instance merge-code-safe-implies-sig-frame-compatible-lemma))
           :do-not-induct t)))


