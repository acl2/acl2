(in-package "ACL2")
(include-book "bcv-model")
(include-book "bcv-simple-model")
(include-book "generic")
;----------------------------------------------------------------------




;; This is not as straightforward as we would like to think:

;;; Because 
;;;;;  It is not obvious (to us and computer) 
;;;;;
;;;;;        if one has an instruction that instruction is a member of merged code
;;;;;        then, there is we did a bcv-check-step-pre on it at some point
;;;;;        during execution. 
;;;;;        
;;;;;  It is not obvious that the stack map recorded into 
;;;;;  collect-witness-merged-code-safe will not be "masked" by a later stack
;;;;;  map declared for the same pc!
;;;;;


;; (defthm merge-code-safe-implies-bcv-check-step-pre-lemma
;;   (implies (and (merged-code-safe merged-code sig-frame)
;;                 (member inst merged-code)
;;                 (wff-code1 (extract-code merged-code)
;;                            (g 'pc (car merged-code)))
;;                 (inst? inst)
;;                 (equal pc (g 'pc inst))
;;                 (bound?  pc (collect-witness-merged-code-safe 
;;                              merged-code sig-frame)))
;;            (bcv-check-step-pre inst 
;;                                (cdr (assoc-equal pc 
;;                                                  (collect-witness-merged-code-safe 
;;                                                   merged-code sig-frame)))))
;;   :hints (("Goal" :in-theory (e/d (merged-code-safe
;;                                    collect-witness-merged-code-safe)
;;                                   (bcv-check-step-pre inst?
;;                                                       sig-frame-compatible
;;                                                       stack-map?
;;                                                       bcv-execute-step))
;;            :do-not '(generalize fertilize)
;;            :induct (merged-code-safe merged-code sig-frame))))

(local 
 (encapsulate () 
   (local 
    (defthm wff-code1-implies-not-member-lemma
      (implies (and (wff-code1 code pc)
                    (< (g 'pc inst) pc))
               (not (member inst code)))))


   (defthm wff-code1-implies-not-member-lemma-specific
     (implies (and (wff-code1 (extract-code merged-code) (+ 1 (g 'pc inst)))
                   (inst? inst))
              (not (member inst (extract-code merged-code))))
     :hints (("Goal" :use ((:instance wff-code1-implies-not-member-lemma
                                      (code (extract-code merged-code))
                                      (pc (+ 1 (g 'pc inst)))))
              :in-theory (disable wff-code1-implies-not-member-lemma))))))

(local 
 (defthm inst-not-member-code-not-member-mergedcode-instance
   (implies (and (not (member inst (extract-code merged-code)))
                 (equal (car (last merged-code)) 'END_OF_CODE)
                 (inst? inst))
            (not (member inst merged-code)))))

(local 
 (defthm merged-code-safe-implies-end-with-end-of-code
   (implies (merged-code-safe mergedcode init-frame)
            (equal (car (last mergedcode))
                   'END_OF_CODE))
   :hints (("Goal" :in-theory (enable merged-code-safe)))))


(local 
 (defthm |Subgoal *1/9.7|
   (IMPLIES
    (AND (MERGED-CODE-SAFE MERGED-CODE sig-frame)
         (inst? inst)
         (WFF-CODE1 (EXTRACT-CODE MERGED-CODE)
                    (+ 1 (G 'PC INST))))
    (not (MEMBER INST MERGED-CODE)))
   :hints (("Goal" :do-not-induct t))))


(defthm merged-code-safe-implies-extract-code-pc-is-same
  (implies (and (merged-code-safe merged-code sig-frame)
                (stack-map? (car merged-code)))
           (equal (g 'pc (car (extract-code merged-code)))
                  (g 'pc (car merged-code)))))


(defthm merged-code-safe-implies-extract-code-pc-is-same-strong
  (implies (merged-code-safe merged-code sig-frame)
           (equal (g 'pc (car (extract-code merged-code)))
                  (g 'pc (car merged-code)))))



;; (local 
;;  (defthm wff-code1-implies-car-pc
;;    (implies (and (wff-code1 code pc)
;;                  (consp code))
;;             (equal (g 'pc (car code)) pc))))


(local 
 (defthm wff-code1-uniqueness
   (IMPLIES
    (AND (WFF-CODE1 (EXTRACT-CODE MERGED-CODE4) any)
         (MERGED-CODE-SAFE MERGED-CODE4 MERGED-CODE3))
    (wff-code1 (extract-code merged-code4)
               (g 'pc (car merged-code4))))
   :rule-classes :forward-chaining))

;----------------------------------------------------------------------
;
; EXport 
         

(defthm merge-code-safe-implies-bcv-check-step-pre-lemma
  (implies (and (merged-code-safe merged-code sig-frame)
                (member inst merged-code)
                (wff-code1 (extract-code merged-code)
                           (g 'pc (car merged-code)))
                (inst? inst)
                (equal pc (g 'pc inst)))
           (bcv-check-step-pre inst 
                               (cdr (assoc-equal pc 
                                                 (collect-witness-merged-code-safe 
                                                  merged-code sig-frame)))))
  :hints (("Goal" :in-theory (e/d (merged-code-safe
                                   collect-witness-merged-code-safe)
                                  (bcv-check-step-pre inst?
                                                      sig-frame-compatible
                                                      stack-map?
                                                      bcv-execute-step))
           :do-not '(generalize fertilize)
           :induct (merged-code-safe merged-code sig-frame))))


;----------------------------------------------------------------------

(defthm member-extract-code-member-merged-code
  (implies (member inst (extract-code merged-code))
           (member inst merged-code))
  :rule-classes :forward-chaining)


(defthm member-extract-code-implies-inst
  (implies (member inst (extract-code merged-code))
           (inst? inst))
  :rule-classes :forward-chaining)

;----------------------------------------------------------------------

(defthm merge-code-safe-implies-bcv-check-step-pre
  (implies (and (merged-code-safe merged-code sig-frame)
                (equal (g 'pc sig-frame) 0)
                (wff-code (extract-code merged-code))
                (member inst (extract-code merged-code))
                (equal pc (g 'pc inst)))
           (bcv-check-step-pre inst 
                               (cdr (assoc-equal pc 
                                                 (collect-witness-merged-code-safe 
                                                  merged-code sig-frame)))))
  :hints (("Goal" :in-theory (disable inst? bcv-check-step-pre)
           :do-not-induct t)))

;----------------------------------------------------------------------

(defthm wff-code1-uniqueness
  (IMPLIES
   (AND (WFF-CODE1 (EXTRACT-CODE MERGED-CODE4) any)
        (MERGED-CODE-SAFE MERGED-CODE4 MERGED-CODE3))
    (wff-code1 (extract-code merged-code4)
               (g 'pc (car merged-code4))))
  :rule-classes :forward-chaining)