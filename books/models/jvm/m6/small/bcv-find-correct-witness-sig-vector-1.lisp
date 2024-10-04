(in-package "ACL2")
(include-book "bcv-model")
(include-book "bcv-simple-model")
(include-book "generic")



;; (local (include-book "bcv-find-correct-witness-bcv-check-pre"))



(encapsulate () 
  (local       
   (defthm get-is-stack-map-sig-frame-pop-n
     (equal (g 'is-stack-map (sig-frame-pop-n n sig-frame))
            (g 'is-stack-map sig-frame))))
  (local 
   (defthm get-is-inst-sig-frame-pop-n
     (equal (g 'is-inst (sig-frame-pop-n n sig-frame))
            (g 'is-inst sig-frame))))

   (local 
    (defthm get-pc-sig-frame-pop-n
      (equal (g 'pc (sig-frame-pop-n n sig-frame))
             (g 'pc sig-frame))))

   (defthm bcv-execute-step-produce-stack-map-or-aftergoto
     (implies (and (stack-map? stack-map)
                   (bcv-check-step-pre inst stack-map)
                   (not (stack-map? (bcv-execute-step inst stack-map))))
              (equal (bcv-execute-step inst stack-map) 'aftergoto))))

;----------------------------------------------------------------------

;; Subgoal *1/9.12'4'
;; (IMPLIES
;;  (AND
;;    (CONSP MERGED-CODE2)
;;    (NOT (EQUAL INIT-FRAME 'AFTERGOTO))
;;    (NOT (STACK-MAP? MERGED-CODE1))
;;    (INST? MERGED-CODE1)
;;    (EQUAL (G 'PC INIT-FRAME)
;;           (G 'PC MERGED-CODE1))
;;    (BCV-CHECK-STEP-PRE MERGED-CODE1 INIT-FRAME)
;;    (SIG-FRAME-COMPATIBLE
;;         STACK-MAP
;;         (CDR (ASSOC-EQUAL (G 'PC INIT-FRAME)
;;                           (COLLECT-WITNESS-MERGED-CODE-SAFE
;;                                MERGED-CODE2
;;                                (BCV-EXECUTE-STEP MERGED-CODE1 INIT-FRAME)))))
;;    (MERGED-CODE-SAFE MERGED-CODE2
;;                      (BCV-EXECUTE-STEP MERGED-CODE1 INIT-FRAME))
;;    (WFF-CODE1 (EXTRACT-CODE MERGED-CODE2)
;;               (+ 1 (G 'PC INIT-FRAME)))
;;    (MEMBER STACK-MAP MERGED-CODE2)
;;    (STACK-MAP? INIT-FRAME)
;;    (STACK-MAP? STACK-MAP)
;;    (EQUAL (G 'PC STACK-MAP)
;;           (G 'PC INIT-FRAME)))
;;  (SIG-FRAME-COMPATIBLE STACK-MAP INIT-FRAME)).

;; we want to prove that sig-frame-compatible

;;    (SIG-FRAME-COMPATIBLE
;;         STACK-MAP
;;         (CDR (ASSOC-EQUAL (G 'PC INIT-FRAME)
;;                           (COLLECT-WITNESS-MERGED-CODE-SAFE
;;                                MERGED-CODE2
;;                                (BCV-EXECUTE-STEP MERGED-CODE1
;;                                INIT-FRAME)))))
;;
;; is impossible when 
;;
;;    (WFF-CODE1 (EXTRACT-CODE MERGED-CODE2)
;;               (+ 1 (G 'PC INIT-FRAME)))


(defthm stack-map-implies-not-sig-frame-compatible
    (implies (stack-map? x)
             (not (sig-frame-compatible x nil))))


(encapsulate () 
 (local (include-book "bcv-if-pc-small-then-not-bound-in-witness"))
 (defthm merged-code-is-safe-implies-not-bound-smaller
   (implies (and (merged-code-safe merged-code init-frame)
                 (WFF-CODE1 (EXTRACT-CODE MERGED-CODE)
                            (g 'pc (car merged-code)))
                 (< pc1 (g 'pc (car merged-code))))
            (not (assoc-equal pc1 (collect-witness-merged-code-safe 
                                   merged-code init-frame))))))


(encapsulate () 
 (local (include-book "bcv-if-verified-then-pc-ordered"))
 (local (defthm merged-code-safe-implies-pc-less-than
          (implies (and (WFF-CODE1 (EXTRACT-CODE MERGED-CODE)
                                   (+ 1 pc))
                        (consp (extract-code merged-code))
                        (merged-code-safe merged-code sig-frame))
                   (< pc 
                      (g 'pc (car merged-code))))
          :rule-classes :linear))

 (defthm merged-code-safe-implies-pc-less-than-rewrite
   (implies (and (WFF-CODE1 (EXTRACT-CODE MERGED-CODE)
                            (+ 1 pc))
                 (consp (extract-code merged-code))
                 (merged-code-safe merged-code sig-frame))
            (< pc 
               (g 'pc (car merged-code))))))




;----------------------------------------------------------------------

(encapsulate ()
 (local (include-book "bcv-find-correct-witness-bcv-check-pre"))             
 (defthm wff-code1-uniqueness
   (IMPLIES
    (AND (WFF-CODE1 (EXTRACT-CODE MERGED-CODE4) any)
         (MERGED-CODE-SAFE MERGED-CODE4 MERGED-CODE3))
    (wff-code1 (extract-code merged-code4)
               (g 'pc (car merged-code4))))
   :rule-classes :forward-chaining))


(defthm sig-frame-compatible-reflexive
  (SIG-FRAME-COMPATIBLE STACK-MAP STACK-MAP))


(defthm sig-frame-compatible-pc-equal-f
  (implies (SIG-FRAME-COMPATIBLE init-frame stack-map)
           (equal (g 'pc init-frame) 
                  (g 'pc stack-map)))
  :rule-classes :forward-chaining)

(defthm sig-frame-compatible-transitive
  (implies (and (sig-frame-compatible frame1 frame2)
                (SIG-FRAME-COMPATIBLE frame2 frame3))
           (sig-frame-compatible frame1 frame3)))





(defthm merged-code-safe-implies-merged-code-pc-is-pc
  (implies (and (merged-code-safe merged-code init-frame)
                (stack-map? init-frame))
           (equal (g 'pc (car merged-code))
                  (g 'pc init-frame)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable sig-frame-compatible inst? stack-map?
                               bcv-check-step-pre
                               bcv-execute-step))))



(defthm collect-witness-merged-code-safe-not-consp-if-not-extract-code
  (implies (not (consp (extract-code merged-code)))
           (not (consp (collect-witness-merged-code-safe merged-code init-frame)))))



(defthm first-stack-map-frame-is-compatible-with-the-last-frame-for-a-same-pc
  (IMPLIES (and (merged-code-safe merged-code stack-map)
                (stack-map? stack-map)
                (equal (g 'pc stack-map) pc))
           (SIG-FRAME-COMPATIBLE
            stack-map
            (CDR (ASSOC-EQUAL
                  pc 
                  (COLLECT-WITNESS-MERGED-CODE-SAFE MERGED-CODE stack-map)))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable sig-frame-compatible inst? stack-map?
                               bcv-check-step-pre
                               bcv-execute-step))))


;; (i-am-here) ;; Mon Nov 14 16:34:29 2005

(defthm |Subgoal *1/9.12'4'|
  (IMPLIES
   (AND
    (CONSP MERGED-CODE2)
    (NOT (EQUAL INIT-FRAME 'AFTERGOTO))
    (INST? MERGED-CODE1)
    (BCV-CHECK-STEP-PRE MERGED-CODE1 INIT-FRAME)
    (SIG-FRAME-COMPATIBLE
     STACK-MAP
     (CDR (ASSOC-EQUAL (G 'PC INIT-FRAME)
                       (COLLECT-WITNESS-MERGED-CODE-SAFE
                        MERGED-CODE2
                        (BCV-EXECUTE-STEP MERGED-CODE1 INIT-FRAME)))))
    (EQUAL (G 'PC INIT-FRAME)
           (G 'PC MERGED-CODE1))
    (MERGED-CODE-SAFE MERGED-CODE2
                      (BCV-EXECUTE-STEP MERGED-CODE1 INIT-FRAME))
    (WFF-CODE1 (EXTRACT-CODE MERGED-CODE2)
               (+ 1 (G 'PC INIT-FRAME)))
    (MEMBER STACK-MAP MERGED-CODE2)
    (STACK-MAP? INIT-FRAME)
    (STACK-MAP? STACK-MAP)
    (EQUAL (G 'PC STACK-MAP)
           (G 'PC INIT-FRAME)))
   (SIG-FRAME-COMPATIBLE STACK-MAP INIT-FRAME))
 :hints (("Goal" :do-not '(generalize fertilize)
          :in-theory (disable sig-frame-compatible inst? stack-map?
                              ;; assoc-equal
                              wff-code1
                              bcv-check-step-pre
                              extract-code
                              bcv-execute-step)
          :cases ((consp (extract-code merged-code2)))
          :do-not-induct t)))




(defthm verified-implies-partial-sig-vector-compatible-with-full-vector-lemma
   (implies (and (merged-code-safe merged-code init-frame)
                 (consp (cdr merged-code))
                 (wff-code1 (extract-code merged-code)
                            (g 'pc (car merged-code)))
                 (member stack-map merged-code)
                 (or (stack-map? init-frame)
                     (equal init-frame 'aftergoto))
                 (stack-map? stack-map)
                 (equal (g 'pc stack-map) pc))
            (sig-frame-compatible 
             stack-map
             (cdr (assoc-equal pc (collect-witness-merged-code-safe 
                                   merged-code init-frame)))))
   :hints (("Goal" :do-not '(generalize fertilize)
            :in-theory (disable sig-frame-compatible inst? stack-map?
                                ;; wff-code1
                                ;; assoc-equal
                                bcv-check-step-pre
                                ;;extract-code
                                bcv-execute-step))))
