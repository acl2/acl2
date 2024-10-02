(in-package "ACL2")
(include-book "bcv-model")
(include-book "bcv-simple-model")

;;(i-am-here) ;; Thu Nov  3 19:39:19 2005



(local (in-theory (disable bcv-simple-inst collect-witness-merged-code-safe
                           inst? stack-map? make-inst
                           merged-code-safe)))



(defthm extract-code-wff-code1-same
  (implies (wff-code1 code pc)
           (equal (extract-code (append code '(END_OF_CODE)))
                  code)))

(defthm |s-same-g-lemma|
  (IMPLIES (AND (EQUAL (G 'IS-INST INST) T)
                (NOT (G 'IS-STACK-MAP INST)))
           (EQUAL (S 'IS-INST
                     T (S 'IS-STACK-MAP NIL INST))
                  INST))
  :hints (("Goal" :in-theory (disable s-same-g)
           :use ((:instance S-SAME-G
                            (a 'is-inst) 
                            (R (s 'is-stack-map nil inst)))
                 (:instance S-SAME-G
                            (a 'is-stack-map)
                            (R inst))))))


(defthm inst-implies-make-inst-same
  (implies (inst? inst)
           (equal (make-inst inst) inst))
  :hints (("Goal" :in-theory (enable inst? make-inst))))

;; (i-am-here) ;; Fri Nov 11 10:49:03 2005

(defthm extract-code-mergeStackMapAndCode
  (implies (and (equal (car (last (mergeStackMapAndCode maps code method-name method-table)))
                       'END_OF_CODE)
                (wff-code1 code pc))
           (equal (extract-code (mergeStackMapAndCode maps code method-name method-table))
                  code))
  :hints (("Goal" :in-theory (enable inst?))))

(defthm not-inst-end-of-code
  (not (inst? 'END_OF_CODE)))

(defthm get-is-inst-make-inst
  (g 'is-inst (make-inst inst))
  :hints (("Goal" :in-theory (enable make-inst))))

(defthm make-inst-inst
  (implies (inst? inst)
           (inst? (make-inst inst)))
  :hints (("Goal" :in-theory (enable make-inst inst?))))


(defthm g-end-of-code
  (not (g 'is-inst 'END_OF_CODE)))

(defthm make-inst-never-end-of-code
  (not (equal (make-inst inst) 'END_OF_CODE))
  :hints (("Goal" :in-theory (disable make-inst
                                      get-is-inst-make-inst
                                      g-end-of-code)
           :use ((:instance get-is-inst-make-inst)
                 (:instance g-end-of-code)))))

(defthm extract-code-mergeStackMapAndCode-specific
  (implies (and (equal (car (last (mergeStackMapAndCode maps code method-name method-table)))
                       'END_OF_CODE)
                (wff-code code))
           (equal (extract-code (mergeStackMapAndCode maps code method-name  method-table))
                  code))
  :hints (("Goal" 
           :in-theory (e/d (wff-code) (extract-code mergeStackMapAndCode))
           :use ((:instance extract-code-mergeStackMapAndCode
                            (pc 0))))))

;----------------------------------------------------------------------

;; (i-am-here) ;; Thu Nov  3 21:03:06 2005




;; ;; Fri Nov  4 10:51:41 2005
;; (skip-proofs 
;;  (defthm merge-code-safe-implies-bcv-check-step-pre
;;   (implies (and (merged-code-safe merged-code sig-frame)
;;                 (member inst merged-code)
;;                 (inst? inst)
;;                 (equal (nth pc (extract-code merged-code)) inst))
;;            (bcv-check-step-pre inst 
;;                                (cdr (assoc-equal pc 
;;                                                  (collect-witness-merged-code-safe 
;;                                                   merged-code sig-frame)))))
;;   :hints (("Goal" :in-theory (e/d (merged-code-safe
;;                                    collect-witness-merged-code-safe)
;;                                   (bcv-check-step-pre
;;                                    bcv-execute-step))))))


;; (skip-proofs 
;;  (defthm bcv-check-step-pre-implies-bcv-simple-check-step
;;   (implies (bcv-check-step-pre inst 
;;                                (cdr (assoc-equal pc 
;;                                                  (collect-witness-merged-code-safe 
;;                                                   merged-code sig-frame))))
;;            (bcv-simple-check-step-pre inst
;;                                       (cdr (assoc-equal pc 
;;                                                         (collect-witness-merged-code-safe 
;;                                                          merged-code sig-frame)))))))
;;

;;(i-am-here) ;; Sat Nov  5 19:43:23 2005
;;(i-am-here) ;; Thu Nov 10 20:42:38 2005

(encapsulate () 
  (local (include-book "bcv-find-correct-witness"))           
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
                             merged-code sig-frame)))))


;;; modified form!!! 


;; ;; (encapsulate () 
;; ;;   (local (include-book "bcv-find-correct-witness"))           
;; ;;   (defthm merge-code-safe-implies-bcv-simple-check-pre-on-witness
;; ;;     (implies (and (merged-code-safe merged-code sig-frame)
;; ;;                   (bcv-verified-method-table (g 'method-table sig-frame))
;; ;;                   (member inst merged-code)
;; ;;                   (inst? inst)
;; ;;                   (equal (nth pc (extract-code merged-code)) inst))
;; ;;              (bcv-simple-inst pc
;; ;;                               inst
;; ;;                               (collect-witness-merged-code-safe
;; ;;                                merged-code sig-frame)))))
;;;;;
;;;;; originally. 
;;;;;
;;; this is not true !!! 
;;; because bcv-simple-inst will assert that 
;;; the bcv-simple-check-INVOKE method-table, opstack, method-name are 
;;; compatible with recorded signature of the method being invoked!!
;;; we know it will be true!! 
;;;
;;; Because we verified each method, and we will know that each method 
;;; 's first frame will have this property!! 
;;; 


(local (in-theory (disable bcv-verified-method-table)))



;----------------------------------------------------------------------

;; (i-am-here) ;; Mon Nov  7 22:35:31 2005

(defthm member-code-merge-merged-code-lemma
  (implies (and (equal (car (last (mergeStackMapAndCode maps code method-name method-table)))
                       'END_OF_CODE)
                (inst? inst)
                (member inst code))
           (member inst (mergeStackMapAndCode maps code method-name method-table)))
  :hints (("Goal" :do-not '(generalize))))
                      

(defthm merged-code-safe-implies-end-with-end-of-code
  (implies (merged-code-safe mergedcode init-frame)
           (equal (car (last mergedcode))
                  'END_OF_CODE))
  :hints (("Goal" :in-theory (enable merged-code-safe))))

(defun is-suffix-code (code1 code)
  (if (equal code code1)
      t
    (if (endp code) nil
      (is-suffix-code code1 (cdr code)))))

(defthm is-suffix-code-cdr-suffix
  (implies (and (is-suffix-code code1 code)
                (consp code1))
           (is-suffix-code (cdr code1) code)))


(defthm not-inst-end-of-code
  (not (inst? 'END_OF_CODE)))


(defthm mem-suffix-mem-all
  (implies (and (member inst code1)
                (is-suffix-code code1 code))
           (member inst code)))



(defthm mem-suffix-mem-all-specific
  (implies (and (is-suffix-code code1 code)
                (consp code1))
           (member (car code1) code)))



(local (in-theory (disable wff-code)))


(defun suffix-code-offset (code1 code)
  (if (equal code code1) 0
    (if (endp code) 0
      (+ 1 (suffix-code-offset code1 (cdr code))))))


(defthm member-wff-code-implies-inst-lemma
  (implies (and (member inst code)
                (wff-code1 code pc))
           (inst? inst))
  :hints (("Goal" :in-theory (enable wff-code1 inst?))))



(defthm member-wff-code-implies-inst
  (implies (and (member inst code)
                (wff-code code))
           (inst? inst))
  :hints (("Goal" :in-theory (enable wff-code))))



(defthm member-wff-code-implies-inst-specific
  (implies (and (is-suffix-code code1 code)
                (consp code1)
                (wff-code code))
           (inst? (car code1)))
  :hints (("Goal" :use ((:instance member-wff-code-implies-inst
                                   (inst (car code1)))))))


(defthm nth-suffix-offset-is-car
  (implies (and (is-suffix-code code1 code)
                (consp code1))
           (equal (nth (suffix-code-offset code1 code) code)
                  (car code1))))


(defthm never-suffix-code-lemma
  (implies (not (is-suffix-code y x))
           (NOT (IS-SUFFIX-CODE (cons any y) x))))



(defthm is-suffix-code-size
  (implies (< (acl2-count y)
              (acl2-count x))
           (not (is-suffix-code x y))))

(defthm never-suffix-code
  (not (is-suffix-code (cons y x) x)))


(defthm suffix-code-offset-is
  (implies (and (is-suffix-code code1 code)
                (consp code1))
           (equal (+ 1 (suffix-code-offset code1 code))
                  (suffix-code-offset (cdr code1) code))))


;; (i-am-here) ;; Sat Nov  5 19:51:44 2005
;; 

;; (i-am-here) ;; Sat Nov  5 20:00:20 2005


(defthm stack-map-make-stack-map
  (IMPLIES (STACK-MAP? MAPS1)
           (STACK-MAP? (MAKESTACKMAP MAPS1 method-name METHOD-TABLE)))
  :hints (("Goal" :in-theory (enable stack-map?))))

(defthm stack-map-set-method-table-x
  (IMPLIES (STACK-MAP? MAPS1)
           (STACK-MAP? (s 'max-stack any3 
                          (s 'method-name any2 (s 'method-table any maps1)))))
  :hints (("Goal" :in-theory (enable stack-map?))))


;; (i-am-here) ;; Sun Nov  6 00:54:35 2005


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


(defthm stack-map-set-equal
  (IMPLIES (STACK-MAP? MAPS1)
           (EQUAL (MAKESTACKMAP MAPS1 method-name METHOD-TABLE)
                  (s 'max-stack 
                     (g 'max-stack 
                        (cdr (assoc-equal method-name method-table)))
                     (s 'method-name method-name (S 'METHOD-TABLE METHOD-TABLE MAPS1)))))
  :hints (("Goal" :in-theory (enable stack-map?))))

(encapsulate () 
 (local (include-book "bcv-find-correct-witness-sig-vector"))
 (defthm extract-maps-merged-code-safe-is-maps
   (implies (and (wff-maps maps)
                 (wff-code1 code any)
                 (equal (car (last (mergeStackMapAndCode maps code method-name
                                                         method-table)))
                        'END_OF_CODE))
            (equal (extract-maps (mergeStackMapAndCode maps code method-name method-table))
                   (update-maps-with-method-table maps method-name method-table)))))
 


(defthm extract-maps-merged-code-safe-is-maps-specific
  (implies (and (wff-maps maps)
                (wff-code code)
                (equal (car (last (mergeStackMapAndCode maps code
                                                        method-name
                                                        method-table)))
                       'END_OF_CODE))
           (equal (extract-maps (mergeStackMapAndCode maps code method-name method-table))
                  (update-maps-with-method-table maps method-name method-table)))
  :hints (("Goal" :in-theory (e/d (wff-code)
                                  (make-inst makeStackmap)))))


(defthm wff-code1-pc-suffix-offset-is
  (implies (and (wff-code1 code pc)
                (consp code1)
                (integerp pc)
                (is-suffix-code code1 code))
           (equal (+ pc (suffix-code-offset code1 code))
                  (g 'pc (car code1)))))



(defthm wff-code-pc-suffix-offset-is
  (implies (and (wff-code code)
                (consp code1)
                (is-suffix-code code1 code))
           (equal (suffix-code-offset code1 code)
                  (g 'pc (car code1))))
  :hints (("Goal" :in-theory (e/d (wff-code)
                                  (suffix-code-offset 
                                   is-suffix-code))
           :use ((:instance wff-code1-pc-suffix-offset-is
                            (pc 0))))))
                   

(defthm wff-code-suffix-implies-pc-ordered
  (implies (and (wff-code1 code pc)
                (is-suffix-code code1 code)
                (consp (cdr code1)))
           (equal (+ 1 (g 'pc (car code1)))
                  (g 'pc (cadr code1))))
  :hints (("Goal" :do-not '(generalize))))


(defthm wff-code-suffix-implies-pc-ordered-suffix
  (implies (and (wff-code code)
                (is-suffix-code code1 code)
                (case-split (consp (cdr code1))))
            (equal (+ 1 (g 'pc (car code1)))
                   (g 'pc (cadr code1))))
  :hints (("Goal" :in-theory (enable wff-code)
           :use ((:instance wff-code1-pc-suffix-offset-is
                            (pc 0))))))

(defun strip-pc (code)
  (if (endp code) code
    (cons (g 'inst (car code))
          (strip-pc (cdr code)))))
      

(defthm member-suffix-member-total
  (implies (and (is-suffix-code code1 code)
                (member x code1))
           (member x code)))

;; (i-am-here) ;; Tue Nov  8 13:01:48 2005                
;; >L            (DEFUN BCV-SIMPLE-METHOD1 (PC CODE SIG-VECTOR)
;;                      (DECLARE (XARGS :MEASURE (LEN CODE)))
;;                      (IF (ENDP CODE)
;;                          T
;;                          (LET* ((INST (CAR CODE)))
;;                                (AND (BCV-SIMPLE-INST PC INST SIG-VECTOR)
;;                                     (BCV-SIMPLE-METHOD1 (+ 1 PC)
;;                                                         (CDR CODE)
;;                                                         SIG-VECTOR)))))

(defun bcv-simple-method1-induct (pc code1 maps code method-table method-name init-frame)
  (declare (xargs :measure (len code1)))
  (if (endp code1) 
      (list pc code1 maps code method-table method-name init-frame)
    (and (bcv-simple-inst pc (g 'inst (car code1)) 
                          (collect-witness-merged-code-safe
                           (mergeStackMapAndCode maps code method-name method-table)
                           init-frame))
         (bcv-simple-method1-induct (+ 1 pc) (cdr code1) 
                                    maps code method-table method-name init-frame))))


;; (i-am-here) ;; Thu Nov 10 20:43:27 2005
(defthm wff-maps-update-maps-with-method-table-wff-maps
  (implies (WFF-MAPS maps)
           (wff-maps (UPDATE-MAPS-WITH-METHOD-TABLE maps method-name method-table))))


;; (defthm |Subgoal *1/3'4'|
;;   (IMPLIES
;;    (AND
;;     (NOT (BCV-SIMPLE-INST
;;           (G 'PC CODE2)
;;           (G 'INST CODE2)
;;           (COLLECT-WITNESS-MERGED-CODE-SAFE
;;            (MERGESTACKMAPANDCODE
;;             (G 'STACKMAPS
;;                (CDR (ASSOC-EQUAL (G 'METHOD-NAME INIT-FRAME)
;;                                  (G 'METHOD-TABLE INIT-FRAME))))
;;             CODE (G 'METHOD-TABLE INIT-FRAME))
;;            INIT-FRAME)))
;;     (MERGED-CODE-SAFE
;;      (MERGESTACKMAPANDCODE (G 'STACKMAPS
;;                               (CDR (ASSOC-EQUAL (G 'METHOD-NAME INIT-FRAME)
;;                                                 (G 'METHOD-TABLE INIT-FRAME))))
;;                            CODE (G 'METHOD-TABLE INIT-FRAME))
;;      INIT-FRAME)
;;     (stack-map? init-frame)
;;     (EQUAL (G 'PC INIT-FRAME) 0)
;;     (BCV-VERIFIED-METHOD-TABLE (G 'METHOD-TABLE INIT-FRAME))
;;     (IS-SUFFIX-CODE (CONS CODE2 CODE3) CODE)
;;     (WFF-MAPS (G 'STACKMAPS
;;                  (CDR (ASSOC-EQUAL (G 'METHOD-NAME INIT-FRAME)
;;                                    (G 'METHOD-TABLE INIT-FRAME))))))
;;    (NOT (WFF-CODE CODE))))


;; (defthm member-wff-code
;;   (implies (and (member x code)
;;                 (wff-code code))
;;            (inst? inst))
;;   :hints (("Goal" :in-theory (endp wff-code))))
           
(defthm is-suffix-code-implies-inst-lemma
  (implies (and (is-suffix-code (cons x code2) code)
                (wff-code1 code pc))
           (inst? x))
  :hints (("Goal" :in-theory (enable wff-code))))


(defthm is-suffix-code-implies-inst
  (implies (and (is-suffix-code (cons x code2) code)
                (wff-code code))
           (inst? x))
  :hints (("Goal" :in-theory (enable wff-code))))
           

(defthm merge-code-safe-implies-bcv-simple-method1-lemma
  (implies (and (merged-code-safe (mergeStackMapAndCode maps code method-name method-table)
                                  init-frame)
                (equal (g 'pc init-frame) 0)
                (equal (g 'method-table init-frame) method-table)
                (equal (g 'method-name init-frame) method-name)
                (equal (G 'STACKMAPS
                          (CDR (ASSOC-EQUAL (G 'METHOD-NAME INIT-FRAME)
                                            (G 'METHOD-TABLE INIT-FRAME))))
                       maps)
                (bcv-verified-method-table (g 'method-table init-frame))
                (is-suffix-code code1 code)
                (stack-map? init-frame)
                (wff-maps maps)
                (wff-code code)
                (equal (suffix-code-offset code1 code) pc))
           (bcv-simple-method1 pc (strip-pc code1)
                               (collect-witness-merged-code-safe
                                (mergeStackMapAndCode maps code method-name method-table)
                                init-frame)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable bcv-simple-inst)
           :induct (bcv-simple-method1-induct 
                    pc code1 maps code method-table method-name init-frame))))



(defthm init-frame-compatible
  (implies (and (merged-code-safe merged-code sig-frame)
                (stack-map? sig-frame)
                (consp (cdr merged-code))
                (equal (g 'pc (car merged-code)) pc))
           (sig-frame-compatible 
            sig-frame
            (cdr (assoc-equal pc (collect-witness-merged-code-safe
                                  merged-code sig-frame)))))
  :hints (("Goal" :in-theory (e/d (merged-code-safe
                                   collect-witness-merged-code-safe)
                                  (bcv-check-step-pre
                                   bcv-execute-step)))))
                                  



  
(defthm wff-code-implies-first-pc-is-zero
  (implies (wff-code code)
           (equal (g 'pc (car code)) 0))
  :hints (("Goal" :in-theory (enable wff-code))))

(defthm sig-frame-compatible-indepent-of-set-sig-vector
  (implies (sig-frame-compatible frame1 frame2)
           (sig-frame-compatible (s 'sig-vector any frame1)
                                 frame2)))

(defthm wff-code-merged-code-consp
  (implies (and (equal (car (last (mergeStackMapAndCode maps code method-name method-table)))
                       'END_OF_CODE)
                (wff-code code))
           (consp (cdr (mergeStackMapAndCode maps code method-name method-table))))
  :hints (("Goal" :in-theory (enable wff-code))))


(defthm merged-code-car-pc-same-as-code
  (implies (equal (car (last (mergeStackMapAndCode maps code method-name method-table)))
                  'END_OF_CODE)
           (equal (g 'pc (car (mergeStackMapAndCode maps code method-name method-table)))
                  (g 'pc (car code))))
  :hints (("Goal" :in-theory (enable make-inst))))



(defthm merged-code-car-pc-same-as-code-specific
  (implies (merged-code-safe (mergeStackMapAndCode maps code method-name method-table)
                             (SIG-METHOD-INIT-FRAME METHOD METHOD-TABLE))
           (equal (g 'pc (car (mergeStackMapAndCode maps code method-name method-table)))
                  (g 'pc (car code)))))

           


(defthm sig-frame-init-frame-s-sig-vector
  (equal 
   (SIG-METHOD-INIT-FRAME (S 'SIG-VECTOR any method)
                          METHOD-TABLE)
   (sig-method-init-frame method method-table)))


(defthm sig-frame-init-frame-s-code
  (equal 
   (SIG-METHOD-INIT-FRAME (S 'code any method)
                          METHOD-TABLE)
   (sig-method-init-frame method method-table)))

;; (i-am-here) ;; Fri Nov  4 14:18:25 2005

(defthm g-method-table-from-init-frame
  (equal (g 'method-table (SIG-METHOD-INIT-FRAME METHOD METHOD-TABLE))
         method-table)
  :hints (("Goal" :in-theory (enable sig-method-init-frame))))


(defthm g-pc-from-init-frame
  (equal (g 'pc (sig-method-init-frame method method-table)) 0))


(defthm g-method-name-from-init-frame
  (equal (g 'method-name (sig-method-init-frame method method-table))
         (g 'method-name method)))

;; (i-am-here) ;; Tue Nov  8 14:10:39 2005

(defthm parsecode-strip-pc-lemma
  (equal (strip-pc (parsecode1 any code)) code)
  :hints (("Goal" :in-theory (enable make-inst))))

(defthm parsecode-strip-pc
  (equal (strip-pc (parsecode code)) code))

(in-theory (disable parsecode))

;; (i-am-here) ;; Tue Nov  8 13:49:07 2005


(defthm merge-code-safe-implies-bcv-simple-method1-lemma-specific
  (implies (and (merged-code-safe (mergeStackMapAndCode maps parsed-code
                                                        method-name method-table)
                                  init-frame)
                (equal (g 'pc init-frame) 0)
                (equal (g 'method-table init-frame) method-table)
                (equal (g 'method-name init-frame) method-name)
                (equal (G 'STACKMAPS
                          (CDR (ASSOC-EQUAL (G 'METHOD-NAME INIT-FRAME)
                                            (G 'METHOD-TABLE INIT-FRAME))))
                       maps)
                (bcv-verified-method-table (g 'method-table init-frame))
                (stack-map? init-frame)
                (wff-maps maps)
                (wff-code parsed-code)
                (equal code (strip-pc parsed-code)))
           (bcv-simple-method1 0 code
                               (collect-witness-merged-code-safe
                                (mergeStackMapAndCode maps parsed-code
                                                      method-name method-table)
                                init-frame)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable bcv-simple-inst bcv-simple-method1))))

(defthm sig-method-init-frame-is-stack-map
  (stack-map? (sig-method-init-frame method method-table))
  :hints (("Goal" :in-theory (enable stack-map? sig-method-init-frame))))


;; (defthm bcv-suceed-implies-bcv-simple-succeed
;;   (implies (and (bcv-method method method-table)
;;                 (equal method (binding (g 'method-name method)
;;                                        method-table))
;;                 (bcv-verified-method-table method-table))
;;            (bcv-simple-method
;;             (s 'sig-vector
;;                (collect-witness-bcv-method
;;                 method method-table)
;;                method)
;;             method-table))
;;   :hints (("Goal" :in-theory (disable sig-method-init-frame
;;                                       sig-frame-compatible))))

;; note: this above is not true
;;
;; Because bcv-simple-check-invoke will assert about other method's first
;; frame! We will need to set sig-vector to the witness in every method that
;; may potentially be invoked. 

;; 
;; We shall define a function to say two method-table are related! 
;;
;; The best would be write a function that given method-table produce 
;; a new method-table. So we don't have to discuss about existence pair that
;; satisfies the relation

;; it is always easy to first define the relation then write an algorithm that
;; generate a pair that satisfies it.
;; 
;; Can I generate such a thing. 



;; (encapsulate () 
;;  (local (include-book "bcv-check-pre-implies-bcv-simple-check-pre-if-all-method-verified"))
;;  (defthm bcv-check-step-pre-implies-bcv-simple-check-step
;;   (implies (and (bcv-check-step-pre inst sig-frame)
;;                 (bcv-verified-method-table (g 'method-table sig-frame)))
;;            (bcv-simple-check-step-pre (g 'inst inst) sig-frame))))
;;; 
;;; this is not provable for INVOKE!! 
;;;  


(defthm bcv-succeed-implies-bcv-simple-succeed
  (implies (and (bcv-method method method-table)
                (equal method (binding (g 'method-name method)
                                       method-table))
                (bcv-verified-method-table method-table))
           (bcv-simple-method
            (s 'sig-vector
               (collect-witness-bcv-method
                method method-table)
               method)
            method-table))
  :hints (("Goal" :in-theory (disable sig-method-init-frame
                                      sig-frame-compatible))))

                     


;; (defthm bcv-suceed-implies-bcv-simple-succeed
;;   (implies (bcv-method method method-table)
;;            (bcv-simple-method
;;             (s 'sig-vector
;;                (collect-witness-bcv-method
;;                 method method-table)
;;                method)
;;             method-table))
;;   :hints (("Goal" :in-theory (disable sig-method-init-frame
;;                                       sig-frame-compatible))))
                     
