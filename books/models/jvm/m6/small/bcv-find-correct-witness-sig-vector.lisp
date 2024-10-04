(in-package "ACL2")
(include-book "bcv-model")
(include-book "bcv-simple-model")
(include-book "generic")

;; (local (include-book "bcv-find-correct-witness-bcv-check-pre"))

(encapsulate () 
   (local (include-book "bcv-find-correct-witness-sig-vector-1"))
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
                                   merged-code init-frame)))))))

;----------------------------------------------------------------------

(local (include-book "bcv-make-inst"))


(local 
 (defthm wff-code-implies-mergedStackMapAndCode
   (implies (and (consp code)
                 (merged-code-safe (mergeStackMapAndCode maps code method method-table)
                                   init-frame))
            (consp (cdr (mergeStackMapAndCode maps code method-name method-table))))
   :hints (("Goal" :do-not '(generalize)
            :in-theory (disable bcv-check-step-pre
                                bcv-execute-step
                                make-inst
                                makestackmap)))))


(local 
 (defthm extract-code-mergeStackMapAndCode-specific
   (implies (and (equal (car (last (mergeStackMapAndCode maps code method-name
                                                         method-table)))
                        'END_OF_CODE)
                 (wff-code code))
            (equal (extract-code (mergeStackMapAndCode maps code method-name method-table))
                   code))
   :hints (("Goal" 
            :in-theory (e/d (wff-code) (extract-code mergeStackMapAndCode))
            :use ((:instance extract-code-mergeStackMapAndCode
                             (pc 0)))))))


(local 
 (defthm merged-code-safe-implies-end-with-end-of-code
   (implies (merged-code-safe mergedcode init-frame)
            (equal (car (last mergedcode))
                   'END_OF_CODE))
   :hints (("Goal" :in-theory (enable merged-code-safe)))))


(local 
 (defthm if-bound-then-g-pc-pc
   (implies (bound? pc (extract-partial-sig-vector maps))
            (equal (g 'pc (cdr (assoc-equal pc (extract-partial-sig-vector
                                                maps))))
                   pc))))


(encapsulate ()
 (local (include-book "bcv-find-correct-witness-bcv-check-pre"))             
 (defthm wff-code1-uniqueness
   (IMPLIES
    (AND (WFF-CODE1 (EXTRACT-CODE MERGED-CODE4) any)
         (MERGED-CODE-SAFE MERGED-CODE4 MERGED-CODE3))
    (wff-code1 (extract-code merged-code4)
               (g 'pc (car merged-code4))))
   :rule-classes :forward-chaining))


;; (defthm car-merged-code-stack-is-car-code
;;   (implies (merged-code-safe (mergeStackMapAndCode 
;;                               maps stack-map method-name
;;                               method-table) init-frame)
;;            (equal (g 'pc (car (mergeStackMapAndCode maps code method-name
;;                                                     method-table)))
;;                   (g 'pc (car code))))
;;   :hints (("Goal" :do-not '(generalize)
;;            :in-theory (disable bcv-check-step-pre
;;                                bcv-execute-step
;;                                make-inst
;;                                makestackmap))))



;----------------------------------------------------------------------

(defthm wff-code-implies
  (implies (wff-code code)
           (wff-code1 code (g 'pc (car code)))))
           
;----------------------------------------------------------------------


(defthm bound-implies-member
  (implies (bound? pc (extract-partial-sig-vector maps))
           (member (cdr (assoc-equal pc (extract-partial-sig-vector maps)))
                   maps)))
                   
                   
(defthm bound?-bound?-update-maps
  (implies (bound? x (extract-partial-sig-vector maps))
           (bound? x (extract-partial-sig-vector (update-maps-with-method-table
                                                  maps method-name method-table)))))
           

(defthm member-extract-map
  (implies (member x (extract-maps merged-code))
           (member x merged-code)))

(in-theory (disable member-extract-map))



(defthm make-inst-never-end-of-code
    (not (equal (make-inst inst) 'END_OF_CODE))
    :hints (("Goal" :in-theory (disable make-inst-inst
                                        not-inst-end-of-code)
             :use ((:instance make-inst-inst)
                   (:instance not-inst-end-of-code)))))


(encapsulate () 
 (local (include-book "bcv-find-correct-witness-sig-vector-1"))
 (defthm merged-code-safe-implies-merged-code-pc-is-pc
   (implies (and (merged-code-safe merged-code init-frame)
                 (stack-map? init-frame))
            (equal (g 'pc (car merged-code))
                   (g 'pc init-frame)))
   :hints (("Goal" :do-not '(generalize)
            :in-theory (disable sig-frame-compatible inst? stack-map?
                                bcv-check-step-pre
                                bcv-execute-step)))))




;; (defthm merged-code-safe-implies-merged-code-pc-is-pc
;;   (implies (and (merged-code-safe merged-code init-frame)
;;                 (stack-map? init-frame))
;;            (equal (g 'pc (car merged-code))
;;                   (g 'pc init-frame)))
;;   :hints (("Goal" :do-not '(generalize)
;;            :in-theory (disable sig-frame-compatible inst? stack-map?
;;                                bcv-check-step-pre
;;                                bcv-execute-step))))

         

(defthm stack-map-make-stack-map
  (IMPLIES (STACK-MAP? MAPS1)
           (STACK-MAP? (MAKESTACKMAP MAPS1 method-name METHOD-TABLE)))
  :hints (("Goal" :in-theory (enable stack-map?))))

(defthm stack-map-set-method-table
  (IMPLIES (STACK-MAP? MAPS1)
           (STACK-MAP? (s 'max-stack max-stack 
                          (s 'method-name method-name 
                             (s 'method-table method-table maps1)))))
  :hints (("Goal" :in-theory (enable stack-map?))))




(defthm |s-same-g-lemma-2|
  (IMPLIES (AND (EQUAL (G 'IS-INST map) nil)
                (equal (G 'IS-STACK-MAP map) t))
           (EQUAL (S 'IS-STACK-MAP
                     T (S 'IS-INST NIL map))
                  map))
  :hints (("Goal" :in-theory (disable s-same-g)
           :use ((:instance S-SAME-G
                            (a 'is-stack-map) 
                            (R (s 'is-inst nil map)))
                 (:instance S-SAME-G
                            (a 'is-inst)
                            (R map))))))


(local 
 (defthm stack-map-set-equal
   (IMPLIES (STACK-MAP? MAPS1)
            (EQUAL (MAKESTACKMAP MAPS1 method-name METHOD-TABLE)
                   (S 'METHOD-TABLE METHOD-TABLE 
                      (s 'method-name method-name 
                         (s 'max-stack (g 'max-stack 
                                          (cdr (assoc-equal method-name method-table)))
                            MAPS1)))))
   :hints (("Goal" :in-theory (enable stack-map?)))))



(defthm extract-code-wff-code1-same
  (implies (wff-code1 code pc)
           (equal (extract-code (append code '(END_OF_CODE)))
                  code)))


(defthm extract-code-wff-code1-same-2
  (implies (wff-code1 code pc)
           (equal (extract-maps (append code '(END_OF_CODE)))
                  nil)))


(defthm extract-maps-merged-code-safe-is-maps
  (implies (and (wff-maps maps)
                (wff-code1 code any)
                (equal (car (last (mergeStackMapAndCode maps code method-name
                                                        method-table)))
                       'END_OF_CODE))
           (equal (extract-maps (mergeStackMapAndCode maps code method-name method-table))
                  (update-maps-with-method-table maps method-name method-table)))
  :hints (("Goal" :in-theory (e/d ()
                                  (make-inst inst? stack-map?
                                   makeStackmap))
           :do-not '(generalize))))



(defthm extract-maps-merged-code-safe-is-maps-specific
  (implies (and (wff-maps maps)
                (wff-code code)
                (equal (car (last (mergeStackMapAndCode maps code method-name
                                                        method-table)))
                       'END_OF_CODE))
           (equal (extract-maps (mergeStackMapAndCode maps code method-name method-table))
                  (update-maps-with-method-table maps method-name method-table)))
  :hints (("Goal" :in-theory (e/d (wff-code)
                                  (make-inst)))))


(defthm member-binding-in-partial-sig-vector
   (implies (and (bound? pc (extract-partial-sig-vector maps))
                 (equal (car (last (mergeStackMapAndCode maps code method-name
                                                         method-table)))
                        'END_OF_CODE)
                 (wff-maps maps)
                 (wff-code code))
            (MEMBER
             (CDR (ASSOC-EQUAL PC
                               (EXTRACT-PARTIAL-SIG-VECTOR
                                (UPDATE-MAPS-WITH-METHOD-TABLE MAPS method-name
                                                               method-table))))
             (MERGESTACKMAPANDCODE MAPS CODE method-name method-table)))
   :hints (("Goal" :in-theory (disable wff-code wff-maps
                                       extract-partial-sig-vector
                                       update-maps-with-method-table
                                       mergestackmapandcode)
            :use ((:instance member-extract-map
                             (x (CDR (ASSOC-EQUAL PC
                                                  (EXTRACT-PARTIAL-SIG-VECTOR
                                                   (UPDATE-MAPS-WITH-METHOD-TABLE MAPS method-name method-table)))))
                             (merged-code  (MERGESTACKMAPANDCODE MAPS CODE
                                                                 method-name 
                                                                 method-table)))))))


;----------------------------------------------------------------------

(defthm member-update-maps-stack-map
  (implies (and (wff-maps maps)
                (member x (update-maps-with-method-table maps method-name method-table)))
           (stack-map? x)))


(defthm stack-map-specific
  (implies (and (bound? pc (extract-partial-sig-vector maps))
                (wff-maps maps))
           (stack-map? (cdr (assoc-equal pc
                         (extract-partial-sig-vector
                          (update-maps-with-method-table maps method-name
                                                         method-table)))))))

;----------------------------------------------------------------------


(defthm  verified-implies-partial-sig-vector-compatible-with-full-vector
   (implies (and (merged-code-safe (mergeStackMapAndCode maps code
                                                         method-name
                                                         method-table)
                                   init-frame)
                 (wff-code code)
                 (wff-maps maps)
                 (stack-map? init-frame)
                 (equal (g 'pc init-frame) 0)
                 (equal (g 'method-table init-frame) method-table)
                 (bound? pc (extract-partial-sig-vector maps)))
            (sig-frame-compatible 
             (cdr (assoc-equal pc (extract-partial-sig-vector 
                                   (update-maps-with-method-table maps
                                                                  method-name method-table))))
             (cdr (assoc-equal pc (collect-witness-merged-code-safe 
                                   (mergeStackMapAndCode maps code method-name method-table)
                                   init-frame)))))
   :hints (("Goal"
            :in-theory (disable sig-frame-compatible
                                mergeStackMapAndCode
                                member
                                stack-map?
                                update-maps-with-method-table
                                collect-witness-merged-code-safe
                                merged-code-safe)
            :do-not-induct t)))

;----------------------------------------------------------------------
