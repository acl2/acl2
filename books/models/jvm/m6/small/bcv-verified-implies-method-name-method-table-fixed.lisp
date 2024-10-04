(in-package "ACL2")
(include-book "bcv-model")
(include-book "generic")

(defthm bcv-execute-step-change-no-method-name
  (implies (and (bcv-check-step-pre inst sig-frame)
                (case-split (not (member (bcv-op-code inst)
                                         '(HALT RETURN)))))
           (equal (G 'METHOD-NAME
                     (BCV-EXECUTE-STEP inst
                                       SIG-FRAME))
                  (g 'method-name sig-frame))))



(defthm bcv-execute-step-change-no-method-table
  (implies (and (bcv-check-step-pre inst sig-frame)
                (case-split (not (member (bcv-op-code inst)
                                         '(HALT RETURN)))))
           (equal (G 'METHOD-table
                     (BCV-EXECUTE-STEP inst
                                       SIG-FRAME))
                  (g 'method-table sig-frame))))


;;;
;;; the following fact is not straightforward as people would have thought. 
;;; because we don't know what's the stack-map that exist in the merged-code!
;;; 
;;; After a HALT, we will depend o nthe new stack-map to continue the checking
;;;
;;; we better be able to say that methot-name and method-table registered does
;;; not change!!! 
;;; 
;;; Fri Nov 11 09:55:03 2005


;; (defthm verified-implies-method-name-no-change
;;   (implies (and (merged-code-safe merged-code sig-frame)
;;                 (stack-map? sig-frame)
;;                 (bound? pc (collect-witness-merged-code-safe merged-code sig-frame)))
;;            (equal (G 'METHOD-NAME
;;                      (CDR (ASSOC-EQUAL pc
;;                                        (COLLECT-WITNESS-MERGED-CODE-SAFE
;;                                         MERGED-CODE SIG-FRAME))))
;;                   (g 'method-name sig-frame)))
;;   :hints (("Goal" :in-theory (e/d () (bcv-execute-step
;;                                       sig-frame-compatible)))))

;;; We need to characterize it. Introducing the concept to

(defthm bcv-execute-step-produce-AFTERGOTO
  (implies (and (bcv-check-step-pre inst sig-frame)
                (case-split (member (bcv-op-code inst) '(RETURN HALT))))
           (equal (bcv-execute-step inst sig-frame) 'AFTERGOTO)))


(local 
 (defthm equal-stac-frame-pop-n-still-equal
  (equal (g 'is-stack-map (sig-frame-pop-n n sframe))
         (g 'is-stack-map sframe))))


(local 
 (defthm equal-is-inst-pop-n-still-equal
  (equal (g 'is-inst (sig-frame-pop-n n sframe))
         (g 'is-inst sframe))))



(defthm bcv-execute-step-produce-STACK-MAPS
  (implies (and (bcv-check-step-pre inst sig-frame)
                (stack-map? sig-frame)
                (case-split (not (member (bcv-op-code inst) '(RETURN HALT)))))
           (stack-map? (bcv-execute-step inst sig-frame))))
  

(encapsulate ()
   (local (include-book "bcv-find-correct-witness-bcv-check-pre"))
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
                                                     merged-code sig-frame)))))))





(DEFTHM verified-implies-method-name-no-change-lemma
  (implies (and (merged-code-safe merged-code sig-frame)
                (wff-maps-consistent (extract-maps merged-code) init-frame)
                (stack-map? init-frame)
                (or (equal sig-frame 'aftergoto)
                    (and (stack-map? sig-frame)
                         (equal (g 'method-name sig-frame) 
                                (g 'method-name init-frame))
                         (equal (g 'method-table sig-frame)
                                (g 'method-table init-frame))))
                (bound? pc (collect-witness-merged-code-safe merged-code sig-frame)))
           (equal (G 'METHOD-NAME
                     (CDR (ASSOC-EQUAL pc
                                       (COLLECT-WITNESS-MERGED-CODE-SAFE
                                        MERGED-CODE SIG-FRAME))))
                  (g 'method-name init-frame)))
  :hints (("Goal" :in-theory (e/d () (bcv-execute-step
                                      bcv-check-step-pre
                                      bcv-execute-step
                                      stack-map? inst?
                                      sig-frame-compatible))
           :do-not '(generalize fertilize))))







(DEFTHM verified-implies-method-name-no-change
  (implies (and (merged-code-safe merged-code init-frame)
                (wff-maps-consistent (extract-maps merged-code) init-frame)
                (stack-map? init-frame)
                (bound? pc (collect-witness-merged-code-safe merged-code init-frame)))
           (equal (G 'METHOD-NAME
                     (CDR (ASSOC-EQUAL pc
                                       (COLLECT-WITNESS-MERGED-CODE-SAFE
                                        MERGED-CODE init-FRAME))))
                  (g 'method-name init-frame)))
  :hints (("Goal" :in-theory (e/d () (bcv-execute-step
                                      bcv-check-step-pre
                                      bcv-execute-step
                                      stack-map? inst?
                                      sig-frame-compatible))
           :do-not '(generalize fertilize))))




(defthm verified-implies-method-table-no-change-lemma
   (implies (and (merged-code-safe merged-code sig-frame)
                 (wff-maps-consistent (extract-maps merged-code) init-frame)
                 (stack-map? init-frame)
                 (or (equal sig-frame 'aftergoto)
                     (and (stack-map? sig-frame)
                          (equal (g 'method-name sig-frame) 
                                 (g 'method-name init-frame))
                          (equal (g 'method-table sig-frame)
                                 (g 'method-table init-frame))))
                 (bound? pc (collect-witness-merged-code-safe merged-code sig-frame)))
           (equal (G 'method-table
                     (CDR (ASSOC-EQUAL pc
                                       (COLLECT-WITNESS-MERGED-CODE-SAFE
                                        MERGED-CODE SIG-FRAME))))
                  (g 'method-table init-frame)))
  :hints (("Goal" :in-theory (e/d () (bcv-execute-step
                                      bcv-check-step-pre
                                      bcv-execute-step
                                      stack-map? inst?
                                      sig-frame-compatible))
           :do-not '(generalize fertilize))))




(defthm verified-implies-method-table-no-change
   (implies (and (merged-code-safe merged-code init-frame)
                 (wff-maps-consistent (extract-maps merged-code) init-frame)
                 (stack-map? init-frame)
                 (bound? pc (collect-witness-merged-code-safe merged-code init-frame)))
           (equal (G 'method-table
                     (CDR (ASSOC-EQUAL pc
                                       (COLLECT-WITNESS-MERGED-CODE-SAFE
                                        MERGED-CODE INIT-FRAME))))
                  (g 'method-table init-frame)))
  :hints (("Goal" :in-theory (e/d () (bcv-execute-step
                                      bcv-check-step-pre
                                      bcv-execute-step
                                      stack-map? inst?
                                      sig-frame-compatible))
           :do-not '(generalize fertilize))))
