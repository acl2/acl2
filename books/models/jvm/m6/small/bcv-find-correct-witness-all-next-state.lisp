(in-package "ACL2")
(include-book "bcv-model")
(include-book "bcv-simple-model")
(include-book "generic")



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



(defthm all-next-state-safe-reduction-when-PUSH-POP-INVOKE
  (implies (case-split (member (bcv-op-code inst) '(PUSH POP INVOKE)))
           (equal (all-next-state-safe
                   (bcv-simple-execute-step (g 'inst inst) pre)
                   sig-vector)
                  (sig-frame-compatible
                   (car (bcv-simple-execute-step (g 'inst inst) pre))
                   (cdr (assoc-equal (+ 1 (g 'pc pre))
                                     sig-vector)))))
  :hints (("Goal" :in-theory (disable sig-frame-compatible))))



(defthm all-next-state-safe-reduction-when-RETURN-HALT
  (implies (case-split (member (bcv-op-code inst) '(RETURN HALT)))
           (all-next-state-safe
            (bcv-simple-execute-step (g 'inst inst) pre)
            sig-vector)))


;----------------------------------------------------------------------

;;
;; This following is useless we want to express the theorem in terms of
;; merged-code instead of ...
;; 

;; (encapsulate () 
;;   (local (include-book "bcv-find-correct-witness-sig-vector"))
;;   (defthm  verified-implies-partial-sig-vector-compatible-with-full-vector
;;     (implies (and (merged-code-safe (mergeStackMapAndCode maps code
;;                                                           method-table)
;;                                     init-frame)
;;                   (wff-code code)
;;                   (wff-maps maps)
;;                   (stack-map? init-frame)
;;                  (equal (g 'pc init-frame) 0)
;;                  (equal (g 'method-table init-frame) method-table)
;;                  (bound? pc (extract-partial-sig-vector maps)))
;;             (sig-frame-compatible 
;;              (cdr (assoc-equal pc (extract-partial-sig-vector 
;;                                    (update-maps-with-method-table maps method-table))))
;;              (cdr (assoc-equal pc (collect-witness-merged-code-safe 
;;                                    (mergeStackMapAndCode maps code method-table)
;;                                    init-frame)))))))



;; (defthm targeIsSafe-on-partial-sig-vector
;;   (implies (targetIsSafe pc frame partial-sig-vector)
;;            (sig-frame-compatible
;;             frame 
;;             (cdr (assoc-equal pc partial-sig-vector)))))


;; (defthm targeIsSafe-implies-bounded?
;;   (implies (targetIsSafe pc frame partial-sig-vector)
;;            (assoc-equal pc partial-sig-vector)))

                                  
                              
;; (defthm targetIsSafe-implies-bound-f
;;   (implies (targetIsSafe pc frame vector)
;;            (assoc-equal pc vector))
;;   :rule-classes :forward-chaining)


;; (defthm targetIsSafe-implies-bound-specific-f
;;   (implies (targetIsSafe pc frame (extract-partial-sig-vector 
;;                                    (update-maps-with-method-table maps method-table)))
;;            (assoc-equal pc (extract-partial-sig-vector maps)))
;;   :rule-classes :forward-chaining)
     

;; (defthm verified-and-target-is-safe-implies-sig-frame-compatible
;;   (implies (and (merged-code-safe (mergeStackMapAndCode maps code method-table)
;;                                   init-frame)
;;                 (wff-code code)
;;                 (wff-maps maps)
;;                 (stack-map? init-frame)
;;                 (equal (g 'pc init-frame) 0)
;;                 (equal (g 'method-table init-frame) method-table)
;;                 (targetIsSafe pc frame (extract-partial-sig-vector 
;;                                         (update-maps-with-method-table maps
;;                                                                        method-table))))
;;            (sig-frame-compatible 
;;             frame
;;             (cdr (assoc-equal pc (collect-witness-merged-code-safe 
;;                                   (mergeStackMapAndCode maps code method-table)
;;                                   init-frame)))))
;;   :hints (("Goal" :in-theory (disable sig-frame-compatible targetIsSafe)
;;            :use ((:instance sig-frame-compatible-transitive
;;                             (frame1 frame)
;;                             (frame2 (cdr (assoc-equal pc
;;                                                       (extract-partial-sig-vector 
;;                                                        (update-maps-with-method-table maps
;;                                                                                       method-table)))))
;;                             (frame3 (cdr (assoc-equal pc 
;;                                                       (collect-witness-merged-code-safe
;;                                                        (mergeStackMapAndCode
;;                                                         maps code method-table)
;;                                                        init-frame))))))
;;            :do-not-induct t)))


;; ;; note this is not good enough. We want something expressed in terms of
;; ;; merged-code 

(defthm sig-frame-compatible-transitive
   (implies (and (sig-frame-compatible frame1 frame2)
                 (sig-frame-compatible frame2 frame3))
            (sig-frame-compatible frame1 frame3)))


(local (in-theory (disable sig-frame-compatible-transitive)))

;
;  All this above is for reasoning about targetIsSafe! 
;  where we demand that a signature state exists at the branch target!! 
;  we assert this signature state is more specific than the one we see 
;  at the 
;
;----------------------------------------------------------------------

;; the following should be easier!!
;; (i-am-here) ;; Mon Nov  7 17:35:35 2005

;; (i-am-here) ;; Mon Nov  7 19:37:09 2005

;; (i-am-here) ;; Mon Nov  7 21:00:25 2005

;; (i-am-here) ;; Mon Nov  7 21:08:31 2005



(encapsulate () 
  (local (include-book "bcv-simple-execute-produce-compatible-next-states"))
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
                                 merged-code sig-frame)))))))


;;; Mon Nov  7 19:13:56 2005
;;; note this is not true if inst is HALT or RETURN!!! 
;;; Mon Nov  7 19:13:59 2005



(defthm g-pc-collect-witness-pc
  (implies (bound? pc (collect-witness-merged-code-safe merged-code
                                                        sig-frame))
           (equal (g 'pc (cdr (assoc-equal pc 
                                           (collect-witness-merged-code-safe
                                            merged-code sig-frame))))
                  pc)))

;;;
;;; basic facts about collect-witness-merged-code-safe!! 
;;; Mon Nov  7 19:58:17 2005
;;;

(defthm all-next-state-safe-bcv-simple-execute-step-if-car-cadr
  (implies (and (equal pc (g 'pc pre))
                (equal (op-code inst) 'IFEQ)
                (equal pre (cdr (assoc-equal pc sig-vector))))
           (equal (all-next-state-safe (bcv-simple-execute-step inst pre) sig-vector)
                  (and (sig-frame-compatible
                        (car (bcv-simple-execute-step inst 
                                                      (cdr (assoc-equal pc sig-vector))))
                        (cdr (assoc-equal (+ 1 pc) sig-vector)))
                       (sig-frame-compatible
                        (cadr (bcv-simple-execute-step inst (cdr (assoc-equal
                                                                  pc sig-vector))))
                        (cdr (assoc-equal (cadr inst) sig-vector))))))
  :hints (("Goal" :in-theory (disable sig-frame-compatible))))
                                          

;----------------------------------------------------------------------





;; (encapsulate ()
;;  (local (include-book "bcv-partial-signature-vector-full-signature-vector"))
;;  (defthm verified-extract-partial-sig-compatible-with-full-sig
;;    (implies (merged-code-safe merged-code init-frame)
;;             (partial-sig-vector-compatible
;;              (extract-partial-sig-vector 
;;               (extract-maps merged-code))
;;              (collect-witness-merged-code-safe merged-code init-frame)))
;;    :hints (("Goal" :in-theory (disable sig-frame-compatible)))))

;;; original form! 

;; (i-am-here) ;; Thu Nov 10 22:23:17 2005

(encapsulate () 
 (local (include-book "bcv-partial-signature-vector-full-signature-vector"))
 (defthm verified-extract-partial-sig-compatible-with-full-sig
  (implies (and (merged-code-safe merged-code init-frame)
                (stack-map? init-frame)
                (wff-code1 (extract-code merged-code)
                           (g 'pc (car merged-code))))
           (partial-sig-vector-compatible 
            (extract-partial-sig-vector (extract-maps merged-code))
            (collect-witness-merged-code-safe merged-code init-frame)))))


(defthm bound-partial-sig-vector-implies-sig-frame-compatible-lemma
   (implies (and (bound? pc l)
                 (partial-sig-vector-compatible1 l partial-sig-vector full))
            (sig-frame-compatible
             (cdr (assoc-equal pc partial-sig-vector))
             (cdr (assoc-equal pc full))))
   :hints (("Goal" :in-theory (disable sig-frame-compatible))))



(defthm bound-partial-sig-vector-implies-sig-frame-compatible
   (implies (and (bound? pc partial-sig-vector)
                 (partial-sig-vector-compatible partial-sig-vector full))
            (sig-frame-compatible
             (cdr (assoc-equal pc partial-sig-vector))
             (cdr (assoc-equal pc full))))
   :hints (("Goal" :in-theory (disable sig-frame-compatible
                                       partial-sig-vector-compatible1)
            :restrict
            ((bound-partial-sig-vector-implies-sig-frame-compatible-lemma
              ((l partial-sig-vector)))))))


;; (defthm  verified-and-target-is-safe-implies-sig-frame-compatible-general
;;   (implies (and (merged-code-safe merged-code init-frame)
;;                 (targetIsSafe pc frame (extract-partial-sig-vector
;;                                         (extract-maps merged-code))))
;;            (sig-frame-compatible 
;;             frame
;;             (cdr (assoc-equal pc (collect-witness-merged-code-safe merged-code
;;                                                                    init-frame)))))
;;   :hints (("Goal" :in-theory (disable sig-frame-compatible targetIsSafe)
;;            :use ((:instance sig-frame-compatible-transitive
;;                             (frame1 frame)
;;                             (frame2 (cdr (assoc-equal pc
;;                                                       (extract-partial-sig-vector 
;;                                                        (extract-maps merged-code)))))
;;                             (frame3 (cdr (assoc-equal pc 
;;                                                       (collect-witness-merged-code-safe
;;                                                        merged-code
;;                                                        init-frame))))))
;;            :do-not-induct t)))


;; >L            (DEFUN SIG-FRAME-COMPATIBLE (SFRAME GFRAME)
;;                      (AND (EQUAL (G 'PC SFRAME) (G 'PC GFRAME))
;;                           (EQUAL (G 'MAX-STACK SFRAME)
;;                                  (G 'MAX-STACK GFRAME))
;;                           (EQUAL (G 'METHOD-NAME SFRAME)
;;                                  (G 'METHOD-NAME GFRAME))
;;                           (EQUAL (G 'METHOD-TABLE SFRAME)
;;                                  (G 'METHOD-TABLE GFRAME))
;;                           (SIG-OPSTACK-COMPATIBLE SFRAME GFRAME)
;;                           (SIG-LOCAL-COMPATIBLE (G 'LOCALS SFRAME)
;;                                                 (G 'LOCALS GFRAME))))


;; 1 ACL2 >:pe bcv-check-ifeq
;;    d      1  (INCLUDE-BOOK "bcv-model")
;;              \
;;              [Included books, outermost to innermost:
;;               "/home/hbl/currentwork/src/small/bcv-model.lisp"
;;              ]
;;              \
;; >L            (DEFUN
;;                  BCV-CHECK-IFEQ (INST SIG-FRAME)
;;                  (AND (<= 1 (G 'OP-STACK SIG-FRAME))
;;                       (TARGETISSAFE
;;                            (ARG INST)
;;                            (SIG-FRAME-POP-VALUE SIG-FRAME)
;;                            (EXTRACT-PARTIAL-SIG-VECTOR
;;                                 (G 'STACKMAPS
;;                                    (BINDING (G 'METHOD-NAME SIG-FRAME)
;;                                             (G 'METHOD-TABLE SIG-FRAME)))))))
;;;;
;;;; identified one error with bcv-check-ifeq.
;;;; we need to advance the pc!!! 
;;;;


;; ;; (defun bcv-check-IFEQ (inst sig-frame)
;; ;;   (and (<= 1 (g 'op-stack sig-frame))
;; ;;        (targetIsSafe 
;; ;;         (arg inst)
;; ;;         (s 'pc (arg inst)
;; ;;            (sig-frame-pop-value sig-frame))
;; ;;         (extract-partial-sig-vector 
;; ;;          (g 'stackmaps
;; ;;             (binding (g 'method-name sig-frame)
;; ;;                      (g 'method-table sig-frame)))))))
;; ;;   ;; (extract-sig-vector (g 'stackmaps sig-frame)))

;;;;
;;;; This adds a lot ofcomplexity because targetIsSafe is stated with respect to 
;;;; 
;;;; partial sig vector!!
;;;; 

(defthm bcv-check-step-pre-IFEQ-implies-target-is-safe-bcv-extract-sig-vector
  (implies (and (bcv-check-step-pre inst sig-frame)
                (equal (bcv-op-code inst) 'IFEQ))
           (targetIsSafe
            (cadr (g 'inst inst))
            (cadr (bcv-simple-execute-step (g 'inst inst) sig-frame))
            (extract-partial-sig-vector 
             (update-maps-with-method-table 
              (g 'stackmaps 
                 (cdr (assoc-equal (g 'method-name sig-frame)
                                   (g 'method-table sig-frame))))
              (g 'method-name sig-frame)
              (g 'method-table sig-frame))))))
                                                


(defthm bcv-check-step-pre-IFEQ-implies-target-is-safe-bcv-extract-sig-vector-specific
  (implies (and (bcv-check-step-pre inst sig-frame)
                (equal (bcv-op-code inst) 'IFEQ)
                (equal (extract-maps merged-code)
                       (update-maps-with-method-table 
                        (g 'stackmaps 
                           (cdr (assoc-equal (g 'method-name sig-frame)
                                             (g 'method-table sig-frame))))
                        (g 'method-name sig-frame)
                        (g 'method-table sig-frame))))
           (targetIsSafe
            (cadr (g 'inst inst))
            (cadr (bcv-simple-execute-step (g 'inst inst) sig-frame))
            (extract-partial-sig-vector 
             (extract-maps merged-code)))))


;; (i-am-here) ;; Thu Nov 10 22:35:54 2005


(encapsulate () 
 (local (include-book "bcv-verified-implies-method-name-method-table-fixed"))
 (defthm verified-implies-method-table-no-change
   (implies (and (merged-code-safe merged-code init-frame)
                 (wff-maps-consistent (extract-maps merged-code) init-frame)
                 (stack-map? init-frame)
                 (bound? pc (collect-witness-merged-code-safe merged-code init-frame)))
           (equal (G 'method-table
                     (CDR (ASSOC-EQUAL pc
                                       (COLLECT-WITNESS-MERGED-CODE-SAFE
                                        MERGED-CODE INIT-FRAME))))
                  (g 'method-table init-frame))))

 (DEFTHM verified-implies-method-name-no-change
   (implies (and (merged-code-safe merged-code init-frame)
                (wff-maps-consistent (extract-maps merged-code) init-frame)
                (stack-map? init-frame)
                (bound? pc (collect-witness-merged-code-safe merged-code init-frame)))
           (equal (G 'METHOD-NAME
                     (CDR (ASSOC-EQUAL pc
                                       (COLLECT-WITNESS-MERGED-CODE-SAFE
                                        MERGED-CODE init-FRAME))))
                  (g 'method-name init-frame)))))

;;;
;;; Fri Nov 11 10:24:23 2005, after adding wff-maps-consistent the above is
;;; provable!! 
;;;

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
                                                   merged-code sig-frame)))))))



(defthm not-member-implies-not-merge-code-safe
  (implies (and (member inst (extract-code merged-code))
                (not (member (bcv-op-code inst) '(RETURN HALT PUSH POP INVOKE IFEQ))))
           (not (MERGED-CODE-SAFE MERGED-CODE SIG-FRAME))))


(defthm member-inst-extract-code-implies-bound-pc
  (implies (and (merged-code-safe merged-code sig-frame)
                (member inst (extract-code merged-code)))
           (ASSOC-EQUAL (G 'PC INST)
                        (COLLECT-WITNESS-MERGED-CODE-SAFE MERGED-CODE SIG-FRAME))))


;; (ASSOC-EQUAL (CAR (CDR (G 'INST INST)))
;;              (EXTRACT-PARTIAL-SIG-VECTOR (EXTRACT-MAPS MERGED-CODE))).

;; (defthm targeIsSafe-implies-bound
;;   (implies (targetIsSafe pc frame sig-vector)
;;            (assoc-equal pc sig-vector)))


;; (defthm targeIsSafe-implies-bound-specific
;;   (implies (targetIsSafe pc frame (EXTRACT-PARTIAL-SIG-VECTOR 
;;                                    (update-maps-with-method-table maps method-table)))
;;            (assoc-equal pc (extract-partial-sig-vector maps))))


(defthm assoc-equal-extract-partial-sig-vector
  (implies (assoc-equal pc (extract-partial-sig-vector
                            (update-maps-with-method-table maps method-name method-table)))
           (assoc-equal pc (extract-partial-sig-vector maps)))
  :rule-classes :forward-chaining)


(defthm bcv-check-step-pre-IFEQ-implies-lemma
  (implies (and (equal (op-code (g 'inst inst)) 'IFEQ)
                (bcv-check-step-pre inst sig-frame)
                (equal (extract-maps merged-code)
                       (update-maps-with-method-table 
                        (g 'stackmaps 
                           (cdr (assoc-equal (g 'method-name sig-frame)
                                             (g 'method-table sig-frame))))
                        (g 'method-name sig-frame)
                        (g 'method-table sig-frame))))
           (assoc-equal (cadr (g 'inst inst))
                        (extract-partial-sig-vector 
                         (extract-maps merged-code))))
  :hints (("Goal" :in-theory (e/d (bcv-check-step-pre)
                                  (stack-map? inst?))
           :do-not-induct t)))
                         


;; (defthm bcv-check-step-pre-IFEQ-implies-lemma
;;   (implies (and (equal (op-code (g 'inst inst)) 'IFEQ)
;;                 (bcv-check-step-pre inst sig-frame)
;;                 (equal (extract-maps merged-code)
;;                        (update-maps-with-method-table 
;;                         (g 'stackmaps 
;;                            (cdr (assoc-equal (g 'method-name sig-frame)
;;                                              (g 'method-table sig-frame))))
;;                         (g 'method-table sig-frame))))
;;            (assoc-equal (cadr (g 'inst inst))
;;                         (extract-partial-sig-vector 
;;                          (extract-maps merged-code))))
;;   :hints (("Goal" :in-theory (e/d (bcv-check-step-pre)
;;                                   (stack-map? inst?))
;;            :do-not-induct t)))
                         

(defthm update-maps-with-method-table-produces-consistent-maps
  (wff-maps-consistent
   (update-maps-with-method-table maps 
                                  (g 'method-name sig-frame)
                                  (g 'method-table sig-frame))
   sig-frame))



(defthm merge-code-safe-implies-bcv-check-step-pre-specific-lemma
   (implies (and (merged-code-safe merged-code sig-frame)
                 (equal (g 'pc sig-frame) 0)
                 (stack-map? sig-frame)
                 (wff-code (extract-code merged-code))
                 (wff-maps-consistent (extract-maps merged-code) sig-frame)
                 (equal (extract-maps merged-code)
                        (update-maps-with-method-table 
                         (g 'stackmaps 
                            (cdr (assoc-equal (g 'method-name sig-frame)
                                              (g 'method-table sig-frame))))
                         (g 'method-name sig-frame)
                         (g 'method-table sig-frame)))
                 (member inst (extract-code merged-code))
                 (equal pc (g 'pc inst))
                 (equal (op-code (g 'inst inst)) 'IFEQ))
            (SIG-FRAME-COMPATIBLE
             (S
              'PC
              (CADR (G 'INST INST))
              (SIG-FRAME-POP-VALUE
               (CDR (ASSOC-EQUAL
                     (G 'PC INST)
                     (COLLECT-WITNESS-MERGED-CODE-SAFE MERGED-CODE SIG-FRAME)))))
             (CDR (ASSOC-EQUAL (CADR (G 'INST INST))
                               (extract-partial-sig-vector (extract-maps merged-code))))))
   :hints (("Goal" :in-theory (disable merged-code-safe wff-code
                                       MERGE-CODE-SAFE-IMPLIES-BCV-CHECK-STEP-PRE
                                       sig-frame-compatible
                                       inst? stack-map?
                                       sig-frame-pop-value
                                       wff-code extract-partial-sig-vector)
            :use ((:instance merge-code-safe-implies-bcv-check-step-pre))
            :do-not-induct t)))
                                       

(defthm merge-code-safe-implies-bcv-check-step-pre-specific
   (implies (and (merged-code-safe merged-code sig-frame)
                 (equal (g 'pc sig-frame) 0)
                 (stack-map? sig-frame)
                 (wff-code (extract-code merged-code))
                 (equal (extract-maps merged-code)
                        (update-maps-with-method-table 
                         (g 'stackmaps 
                            (cdr (assoc-equal (g 'method-name sig-frame)
                                              (g 'method-table sig-frame))))
                         (g 'method-name sig-frame)
                         (g 'method-table sig-frame)))
                 (member inst (extract-code merged-code))
                 (equal pc (g 'pc inst))
                 (equal (op-code (g 'inst inst)) 'IFEQ))
            (SIG-FRAME-COMPATIBLE
             (S
              'PC
              (CADR (G 'INST INST))
              (SIG-FRAME-POP-VALUE
               (CDR (ASSOC-EQUAL
                     (G 'PC INST)
                     (COLLECT-WITNESS-MERGED-CODE-SAFE MERGED-CODE SIG-FRAME)))))
             (CDR (ASSOC-EQUAL (CADR (G 'INST INST))
                               (extract-partial-sig-vector (extract-maps
                                                            merged-code))))))
   :hints (("Goal" :in-theory (disable merged-code-safe wff-code
                                       MERGE-CODE-SAFE-IMPLIES-BCV-CHECK-STEP-PRE
                                       sig-frame-compatible
                                       inst? stack-map?
                                       sig-frame-pop-value
                                       wff-code extract-partial-sig-vector)
            :cases ((wff-maps-consistent (extract-maps merged-code) sig-frame)))))



(encapsulate () 
 (local (include-book "bcv-find-correct-witness-sig-vector-1"))
 (defthm merged-code-safe-implies-merged-code-pc-is-pc
   (implies (and (merged-code-safe merged-code init-frame)
                 (stack-map? init-frame))
            (equal (g 'pc (car merged-code))
                   (g 'pc init-frame)))))


(defthm |IFEQ-other-branch-ok-lemma|
  (IMPLIES
   (AND (EQUAL (CAR (g 'inst INST)) 'IFEQ)
        (MERGED-CODE-SAFE MERGED-CODE SIG-FRAME)
        (wff-maps-consistent (extract-maps merged-code) sig-frame)
        (EQUAL (EXTRACT-MAPS MERGED-CODE)
               (UPDATE-MAPS-WITH-METHOD-TABLE
                (G 'STACKMAPS
                   (CDR (ASSOC-EQUAL (G 'METHOD-NAME SIG-FRAME)
                                     (G 'METHOD-TABLE SIG-FRAME))))
                (g 'method-name sig-frame)
                (G 'METHOD-TABLE SIG-FRAME)))
        (EQUAL (G 'PC SIG-FRAME) 0)
        (stack-map? sig-frame)
        (wff-maps (extract-maps merged-code))
        (CONSP (EXTRACT-CODE MERGED-CODE))
        (WFF-CODE1 (EXTRACT-CODE MERGED-CODE) 0)
        (WFF-MAPS (EXTRACT-MAPS MERGED-CODE))
        (MEMBER INST (EXTRACT-CODE MERGED-CODE))
        (INST? INST))
   (SIG-FRAME-COMPATIBLE
    (CADR
     (BCV-SIMPLE-EXECUTE-STEP
      (g 'inst INST)
      (CDR (ASSOC-EQUAL
            (G 'PC INST)
            (COLLECT-WITNESS-MERGED-CODE-SAFE MERGED-CODE SIG-FRAME)))))
    (CDR
     (ASSOC-EQUAL (CADR (g 'inst INST))
                  (COLLECT-WITNESS-MERGED-CODE-SAFE MERGED-CODE SIG-FRAME)))))
  :hints (("Goal" :in-theory (e/d (bcv-simple-execute-step)
                                  (inst? extract-code 
                                         targetIsSafe
                                         partial-sig-vector-compatible
                                         bcv-check-step-pre-IFEQ-implies-lemma
                                         sig-frame-compatible-transitive
                                         sig-frame-pop-value
                                         sig-frame-compatible))
           :use ((:instance sig-frame-compatible-transitive
                            (frame1 
                             (S
                              'PC
                              (CADR (G 'INST INST))
                              (SIG-FRAME-POP-VALUE
                               (CDR (ASSOC-EQUAL
                                     (G 'PC INST)
                                     (COLLECT-WITNESS-MERGED-CODE-SAFE
                                      MERGED-CODE SIG-FRAME))))))
                            (frame2 
                             (CDR (ASSOC-EQUAL (CADR (G 'INST INST))
                                               (extract-partial-sig-vector
                                                (extract-maps merged-code)))))
                            (frame3 
                             (CDR
                              (ASSOC-EQUAL (CADR (g 'inst INST))
                                           (COLLECT-WITNESS-MERGED-CODE-SAFE
                                            MERGED-CODE SIG-FRAME)))))
                 (:instance bcv-check-step-pre-IFEQ-implies-lemma
                            (sig-frame 
                             (cdr (assoc-equal (g 'pc inst)
                                               (collect-witness-merged-code-safe 
                                                merged-code sig-frame))))))
           :do-not '(generalize fertilize)
           :do-not-induct t)))


(defthm |IFEQ-other-branch-ok|
  (IMPLIES
   (AND (EQUAL (CAR (g 'inst INST)) 'IFEQ)
        (MERGED-CODE-SAFE MERGED-CODE SIG-FRAME)
        (EQUAL (EXTRACT-MAPS MERGED-CODE)
               (UPDATE-MAPS-WITH-METHOD-TABLE
                (G 'STACKMAPS
                   (CDR (ASSOC-EQUAL (G 'METHOD-NAME SIG-FRAME)
                                     (G 'METHOD-TABLE SIG-FRAME))))
                (g 'method-name sig-frame)
                (G 'METHOD-TABLE SIG-FRAME)))
        (EQUAL (G 'PC SIG-FRAME) 0)
        (stack-map? sig-frame)
        (wff-maps (extract-maps merged-code))
        (CONSP (EXTRACT-CODE MERGED-CODE))
        (WFF-CODE1 (EXTRACT-CODE MERGED-CODE) 0)
        (WFF-MAPS (EXTRACT-MAPS MERGED-CODE))
        (MEMBER INST (EXTRACT-CODE MERGED-CODE))
        (INST? INST))
   (SIG-FRAME-COMPATIBLE
    (CADR
     (BCV-SIMPLE-EXECUTE-STEP
      (g 'inst INST)
      (CDR (ASSOC-EQUAL
            (G 'PC INST)
            (COLLECT-WITNESS-MERGED-CODE-SAFE MERGED-CODE SIG-FRAME)))))
    (CDR
     (ASSOC-EQUAL (CADR (g 'inst INST))
                  (COLLECT-WITNESS-MERGED-CODE-SAFE MERGED-CODE SIG-FRAME)))))
  :hints (("Goal" :cases ((wff-maps-consistent (extract-maps merged-code)
                                               sig-frame))
           :in-theory (e/d ()
                           (inst? extract-code 
                                  bcv-simple-execute-step
                                  targetIsSafe
                                  partial-sig-vector-compatible
                                  bcv-check-step-pre-IFEQ-implies-lemma
                                  sig-frame-compatible-transitive
                                  sig-frame-pop-value
                                  sig-frame-compatible)))))




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
            (collect-witness-merged-code-safe merged-code sig-frame)))
  :hints (("Goal" :cases (
                          (member (bcv-op-code inst) '(RETURN HALT))
                          (member (bcv-op-code inst) '(PUSH POP INVOKE))
                          (equal (bcv-op-code inst) 'IFEQ))
           :in-theory (disable sig-frame-compatible 
                               bcv-check-step-pre
                               inst? stack-map?
                               bcv-execute-step
                               bcv-simple-execute-step)
           :do-not '(generalize fertilize)
           :do-not-induct t)))

