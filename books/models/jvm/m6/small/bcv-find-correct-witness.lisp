(in-package "ACL2")
(include-book "bcv-model")
(include-book "bcv-simple-model")
(include-book "generic")



(encapsulate ()
  (local (include-book "bcv-find-correct-witness-bcv-check-pre"))
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
             :cases ((consp (cdr merged-code)))
             :do-not-induct t))))

;;; bcv-simple-execute-step is almost the same as 
;;; bcv-execute-step, except for IFEQ. RETURN. HALT (Tue Nov  8 14:21:27 2005) 
;;;
;;; bcv-simple-execute-step produce two next states for IFEQ
;;; produce none for RETURN and HALT !! 
;;;
;;;
;; (i-am-here) ;; Fri Nov 11 10:58:03 2005
;; (encapsulate () 
;;  (local (include-book "bcv-check-pre-implies-bcv-simple-check-pre-if-all-method-verified"))
;;  (defthm bcv-check-step-pre-implies-bcv-simple-check-step
;;   (implies (and (bcv-check-step-pre inst sig-frame)
;;                 (bcv-verified-method-table (g 'method-table sig-frame)))
;;            (bcv-simple-check-step-pre (g 'inst inst) sig-frame))))

;; not true. 
;; 
;; because bcv-simple-check-step-pre refers to sig-vector component of a
;; method! 
;; 
;; We somehow need to say if the sig-vector component is equal to ...
;; 
;; (sig-frame-compatible 
;;         (sig-method-init-frame method method-table)
;;         (binding 0 (g 'sig-vector method)))
;;
;; Basically we need this above fact
;;        

(encapsulate () 
 (local (include-book "bcv-check-pre-implies-bcv-simple-check-pre-if-all-method-verified"))
 (defthm bcv-check-step-pre-implies-bcv-simple-check-step
  (implies (and (bcv-check-step-pre inst sig-frame)
                (bcv-verified-method-table (g 'method-table sig-frame)))
           (bcv-simple-check-step-pre (g 'inst inst) sig-frame))))




(encapsulate ()
  (local (include-book "bcv-find-correct-witness-all-next-state"))
  (defthm merged-code-safe-implies-all-next-state-safe
    (implies (and (merged-code-safe merged-code sig-frame)
                  (equal (extract-maps merged-code)
                         (update-maps-with-method-table 
                          (g 'stackmaps 
                             (cdr (assoc-equal (g 'method-name sig-frame)
                                               (g 'method-table sig-frame))))
                          (g 'method-name sig-frame)
                          (g 'method-table sig-frame)))
                  (equal (g 'pc sig-frame) 0)
                  (stack-map? sig-frame)
                  (wff-code (extract-code merged-code))
                  (wff-maps (extract-maps merged-code))
                  (member inst (extract-code merged-code))
                  (inst? inst)
                  (equal pre (binding (g 'pc inst) (collect-witness-merged-code-safe 
                                          merged-code sig-frame))))
             (all-next-state-safe 
              (bcv-simple-execute-step (g 'inst inst) pre)
              (collect-witness-merged-code-safe merged-code sig-frame)))))



(encapsulate ()
  (local (include-book "bcv-find-correct-witness-all-next-state"))
  (defthm member-inst-extract-code-implies-bound-pc
    (implies (and (merged-code-safe merged-code sig-frame)
                  (member inst (extract-code merged-code)))
             (ASSOC-EQUAL (G 'PC INST)
                          (COLLECT-WITNESS-MERGED-CODE-SAFE MERGED-CODE SIG-FRAME)))))



(encapsulate ()
  (local (include-book "bcv-find-correct-witness-all-next-state"))
  (defthm verified-implies-method-table-no-change
    (implies (and (merged-code-safe merged-code init-frame)
                  (wff-maps-consistent (extract-maps merged-code) init-frame)
                  (stack-map? init-frame)
                  (bound? pc (collect-witness-merged-code-safe merged-code init-frame)))
             (equal (G 'method-table
                       (CDR (ASSOC-EQUAL pc
                                         (COLLECT-WITNESS-MERGED-CODE-SAFE
                                          MERGED-CODE INIT-FRAME))))
                    (g 'method-table init-frame)))))


(defthm merge-code-safe-implies-bcv-simple-check-pre-on-witness-lemma
  (implies (and (merged-code-safe merged-code sig-frame)
                (bcv-verified-method-table (g 'method-table sig-frame))
                (wff-maps-consistent (extract-maps merged-code) sig-frame)
                (equal (extract-maps merged-code)
                       (update-maps-with-method-table 
                        (g 'stackmaps 
                           (cdr (assoc-equal (g 'method-name sig-frame)
                                             (g 'method-table sig-frame))))
                        (g 'method-name sig-frame)
                        (g 'method-table sig-frame)))
                (stack-map? sig-frame)
                (wff-maps (extract-maps merged-code))
                (equal (g 'pc sig-frame) 0)
                (equal (g 'pc inst) pc)
                (inst? inst)
                (wff-code (extract-code merged-code))
                (member inst (extract-code merged-code)))
           (bcv-simple-inst pc
                            (g 'inst inst)
                            (collect-witness-merged-code-safe
                             merged-code sig-frame)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable bcv-check-step-pre
                               bcv-verified-method-table
                               bcv-simple-check-step-pre
                               bcv-simple-execute-step))))




(defthm update-maps-with-method-table-produces-consistent-maps
  (wff-maps-consistent
   (update-maps-with-method-table maps 
                                  (g 'method-name sig-frame)
                                  (g 'method-table sig-frame))
   sig-frame))


(defthm merge-code-safe-implies-bcv-simple-check-pre-on-witness
  (implies (and (merged-code-safe merged-code sig-frame)
                (bcv-verified-method-table (g 'method-table sig-frame))
                (equal (extract-maps merged-code)
                       (update-maps-with-method-table 
                        (g 'stackmaps 
                           (cdr (assoc-equal (g 'method-name sig-frame)
                                             (g 'method-table sig-frame))))
                        (g 'method-name sig-frame)
                        (g 'method-table sig-frame)))
                (stack-map? sig-frame)
                (wff-maps (extract-maps merged-code))
                (equal (g 'pc sig-frame) 0)
                (equal (g 'pc inst) pc)
                (inst? inst)
                (wff-code (extract-code merged-code))
                (member inst (extract-code merged-code)))
           (bcv-simple-inst pc
                            (g 'inst inst)
                            (collect-witness-merged-code-safe
                             merged-code sig-frame)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable bcv-check-step-pre
                               bcv-verified-method-table
                               bcv-simple-check-step-pre
                               bcv-simple-execute-step)
           :cases ((wff-maps-consistent (extract-maps merged-code) sig-frame)))))
