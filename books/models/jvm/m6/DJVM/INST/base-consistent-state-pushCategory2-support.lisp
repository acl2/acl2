(in-package "DJVM")

(include-book "base")
(include-book "base-consistent-state")

(include-book "base-consistent-state-step-definition")

(local (include-book "base-consistent-state-step-properties"))

(defthm pushStack-reduce
  (and (equal (env (pushStack v s)) (env s))
       (equal (heap (pushStack v s)) (heap s))
       (equal (class-table (pushStack v s)) (class-table s))
       (equal (instance-class-table (pushStack v s))
              (instance-class-table s))
       (equal (array-class-table (pushStack v s))
              (array-class-table s))
       (equal (error-flag (pushStack v s))
              (error-flag s))
       (equal (no-fatal-error? (pushStack v s))
              (no-fatal-error? s))
       (equal (current-thread (pushStack v s))
              (current-thread s))
       (equal (pc (pushStack v s))
              (pc s))
       (equal (aux (pushStack v s))
              (aux s))
       (equal (class-loaded? any (pushStack v s))
              (class-loaded? any s)))
  :hints (("Goal" :in-theory (enable class-loaded? 
                                     pushStack no-fatal-error?))))


(defthm pushStack-reduce-more
 (equal (JVM::ARRAY-CLASS-CORRECTLY-LOADED? anylist (pushStack v s))
        (jvm::array-class-correctly-loaded? anylist s)))
 

(defthm pushStack-reduce-more-2
  (equal (jvm::array-class-table-inv-helper anylist (pushStack v s))
         (jvm::array-class-table-inv-helper anylist s))
  :hints (("Goal" :in-theory (enable jvm::array-class-table-inv-helper))))


(defthm pushStack-reduce-more-3
  (implies (wff-state s)
           (equal (jvm::loader-inv (pushStack v s))
                  (jvm::loader-inv s)))
  :hints (("Goal" :in-theory (enable jvm::loader-inv))))
  



(defthm wff-state-implies-equal-pushStack-build-instance-data-guard
  (implies (wff-state s)
           (equal (build-a-java-visible-instance-data-guard anylist (pushStack v s))
                  (build-a-java-visible-instance-data-guard anylist s)))
  :hints (("Goal" :in-theory (enable build-a-java-visible-instance-data-guard))))



(defthm wff-state-implies-equal-pushStack-build-instance-guard
  (implies (wff-state s)
           (equal (build-a-java-visible-instance-guard any (pushStack v s))
                  (build-a-java-visible-instance-guard any s)))
  :hints (("Goal" :in-theory (enable build-a-java-visible-instance-guard))))



;; (skip-proofs 
;;  (defthm consistent-state-thread-by-id-pushStack
;;    (implies (consistent-state s)
;;             (equal (thread-by-id x 
;;                                  (thread-table (pushStack v s)))
;;                    (if (equal x (current-thread s))
;;                        (push-stack-of-thread 
;;                         v (thread-by-id (current-thread s)
;;                                         (thread-table s)))
;;                      (thread-by-id x (thread-table s)))))))


;; (skip-proofs 
;;  (defthm consistent-state-thread-by-id-pushStack-2
;;    (implies (consistent-state s)
;;             (equal (thread-by-id x 
;;                                  (thread-table (pushStack v (pushStack '(topx . topx) s))))
;;                    (if (equal x (current-thread s))
;;                        (push-stack-of-thread 
;;                         v (push-stack-of-thread 'topx
;;                                                 (thread-by-id (current-thread s)
;;                                                               (thread-table s))))
;;                      (thread-by-id x (thread-table s)))))))


;;;

;; >V d          (DEFUN MAKE-THREAD
;;                      (ID PC JVM::CALL-STACK JVM::S
;;                          JVM::M-REF JVM::MDEPTH THREAD-REF)
;;                      (LIST 'JVM::THREAD
;;                            ID (CONS 'JVM::SAVED-PC PC)
;;                            (CONS 'JVM::CALL-STACK JVM::CALL-STACK)
;;                            (CONS 'JVM::STATUS JVM::S)
;;                            (CONS 'MONITOR JVM::M-REF)
;;                            (CONS 'JVM::MDEPTH JVM::MDEPTH)
;;                            (CONS 'JVM::THREAD-OBJ THREAD-REF)))


(local (in-theory (disable push-stack-of-thread)))


(defthm push-stack-of-thread-not-null
  (push-stack-of-thread v thread))



;; (defthm wff-thread-table-pushStack-v-still-wff-thread-table
;;   (implies (and (wff-thread-table (thread-table s))
;;                 (thread-by-id (current-thread s) (thread-table s)))
;;            (wff-thread-table (thread-table (pushStack v s))))
;;   :hints (("Goal" :in-theory (enable pushstack))))



(defthm collect-thread-id-thread-table-pushStack
  (implies (wff-thread-table (thread-table s))
           (equal (COLLECT-THREAD-ID (THREAD-TABLE (PUSHSTACK V s)))
                  (collect-thread-id (thread-table s))))
  :hints (("Goal" :in-theory (enable pushstack))))


;; (defthm thread-table-pushStack-is
;;   (equal (thread-table (pushStack v s))
;;          (replace-thread-table-entry (thread-by-id (current-thread s)
;;                                                    (thread-table s))
;;                                      (push-stack-of-thread 
;;                                          v (thread-by-id (current-thread s)
;;                                                          (thread-table s)))
;;                                      (thread-table s)))
;;   :hints (("Goal" :in-theory (e/d (pushStack) ())))) 

  

(defun all-consistent-thread-entry (tids tt cl hp)
  (if (endp tids) t
    (and (consistent-thread-entry 
          (thread-by-id (car tids) tt)
          cl  hp)
         (all-consistent-thread-entry (cdr tids) tt cl hp))))
  

(defthm wff-thread-implies-reduce-thread-by-id
  (implies (wff-thread tt1)
           (equal (THREAD-BY-ID (THREAD-ID TT1)
                                (CONS TT1 TT2))
                  tt1))
  :hints (("Goal" :in-theory (enable thread-by-id))))



(defthm wff-thread-implies-reduce-thread-by-id-2
  (implies (and (wff-thread tt1)
                (not (equal (thread-id tt1) id)))
           (equal (THREAD-BY-ID id
                                (CONS TT1 TT2))
                  (thread-by-id id tt2)))
  :hints (("Goal" :in-theory (enable thread-by-id))))


(defthm all-consistent-thread-entry-reduce
  (implies (and (wff-thread-table tt)
                (wff-thread tt1)
                (not (mem (thread-id tt1)  l)))
           (equal (ALL-CONSISTENT-THREAD-ENTRY l
                                               (cons tt1 TT) CL HP)
                  (ALL-CONSISTENT-THREAD-ENTRY l
                                               TT CL HP)))
  :hints (("Goal" :in-theory (e/d () (consistent-thread-entry))
           :do-not '(generalize))))


(defthm consistent-thread-table-entries-reduce-to-all-consistent-thread-entry
  (implies (and (wff-thread-table tt)
                (nodup-set (collect-thread-id tt)))
           (equal (consistent-thread-entries tt cl hp)
                  (all-consistent-thread-entry (collect-thread-id tt) tt cl hp)))
  :hints (("Goal" :in-theory (e/d () (consistent-thread-entry))
           :do-not '(generalize))))


(defthm thread-table-pushStack-is
  (equal (thread-table (pushStack v s))
         (replace-thread-table-entry (thread-by-id (current-thread s)
                                                   (thread-table s))
                                     (push-stack-of-thread 
                                         v (thread-by-id (current-thread s)
                                                         (thread-table s)))
                                     (thread-table s)))
  :hints (("Goal" :in-theory (e/d (pushStack) ()))))


(defthm not-mem-replace-thread-table-entry-produces-no-change
  (implies (not (mem old tt))
           (equal (replace-thread-table-entry old new tt) 
                  tt)))

(defthm thread-id-no-match-replace-thread-table-entry-produces-no-change
  (implies (and (not (equal (thread-id new) id))
                (not (equal (thread-id old) id)))
           (equal (thread-by-id id (replace-thread-table-entry old new tt))
                  (thread-by-id id tt))))

(defthm thread-by-id-cons
  (implies (not (equal (thread-id new) id))
           (equal (thread-by-id id (cons new tt))
                  (thread-by-id id tt)))
  :hints (("Goal" :in-theory (enable thread-by-id))))


(defthm old-appear-late-replace-thread-table-entry-produces-no-change
  (implies (and (not (equal (thread-by-id id tt) old))
                (not (equal (thread-id new) id)))
           (equal (thread-by-id id (replace-thread-table-entry old new tt))
                  (thread-by-id id tt)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (enable thread-by-id))))



(defthm thread-by-id-from-replace-thread-table-entry
  (implies (equal (thread-id new) 
                  (thread-id old))
           (equal (thread-by-id id (replace-thread-table-entry old new tt))
                  (if (and (mem old tt)
                           (equal (thread-by-id id tt) old)
                           (equal (thread-id new) id))
                      new
                    (thread-by-id id tt))))
  :hints (("Goal" :cases ((mem old tt))
           :do-not '(generalize)
           :in-theory (enable thread-by-id))))
             
                  

(defthm consistent-thread-entry-remain-consistent-thread-entry-if-replacement-is-consistent
  (implies (and (consistent-thread-entry (thread-by-id id tt) cl hp)
                (equal (thread-id new) (thread-id old))
                (consistent-thread-entry new cl hp))
           (consistent-thread-entry 
            (THREAD-BY-ID id (REPLACE-THREAD-TABLE-ENTRY OLD NEW TT))
            CL HP))
  :hints (("Goal" :in-theory (disable consistent-thread-entry)
           :do-not '(generalize))))

;;;
;;; the above theorem maybe useful. However it does not tell what change and
;;; what do not change. It only tells that consistency is preseved!!
;;;



(defthm all-consistent-thread-entry-if-current-thread-consistent
  (implies (and (all-consistent-thread-entry l tt cl hp) 
                (equal (thread-id new) (thread-id old))
                (consistent-thread-entry new cl hp))
           (all-consistent-thread-entry 
            l 
            (replace-thread-table-entry old new tt)
            cl hp))
  :hints (("Goal" :in-theory (e/d () (consistent-thread-entry)))))

;;; We still need to replace two replace-thread-table-entry!! with one!! 

;; (skip-proofs 
;;  (defthm consistent-state-implies-consistent-thread-entry
;;    (implies (consistent-state s)
;;             (consistent-thread-entry (thread-by-id (current-thread s)
;;                                                    (thread-table s))
;;                                      (instance-class-table s)
;;                                      (heap s)))
;;    :rule-classes :forward-chaining))





(defthm consistent-thread-entry-implies-wff-REFp-thread-REF
  (implies (consistent-thread-entry thread cl hp)
           (wff-REFp (TAG-REF (THREAD-REF thread)))))


(defthm consistent-thread-entry-implies-valid-REFp-thread-REF
  (implies (consistent-thread-entry thread cl hp)
           (VALID-REFP (TAG-REF (THREAD-REF thread)) hp)))



;; >V d          (DEFUN WFF-CALL-FRAME (FRAME)
;;                      (AND (TRUE-LISTP FRAME)
;;                           (EQUAL (LEN FRAME) 7)
;;                           (EQUAL (CAR FRAME) 'FRAME)
;;                           (CONSP (NTH 1 FRAME))
;;                           (CONSP (NTH 2 FRAME))
;;                           (TRUE-LISTP (NTH 2 FRAME))
;;                           (CONSP (NTH 3 FRAME))
;;                           (TRUE-LISTP (NTH 3 FRAME))
;;                           (WFF-METHOD-PTR (NTH 4 FRAME))
;;                           (CONSP (NTH 5 FRAME))
;;                           (CONSP (NTH 6 FRAME))))



;; (defthm wff-call-frame-make-frame
;;   (implies (and (wff-call-frame frame)
;;                 (true-listp anyopstack)
;;            (WFF-CALL-FRAME (MAKE-FRAME anypc
;;                                        anyopstack
;;                                        anylocals 
;;                                        (METHOD-PTR (CURRENT-FRAME S))
;;                                  (SYNC-OBJ-REF (CURRENT-FRAME S))
;;                                  (RESUME-PC (CURRENT-FRAME S))))).


;; (i-am-here) ;; Tue Jul 26 13:24:53 2005
;; make sure the pushCategory2 pushes a (topx . topx) pair
;; so that base-untag-state.lisp is easier. 
;;

;; (i-am-here) ;; Tue Jul 26 13:39:21 2005

(defthm wff-call-frame-make-frame
  (implies (wff-call-frame frame)
           (WFF-CALL-FRAME (MAKE-FRAME (RETURN-PC frame)
                              (LIST* V '(TOPX . TOPX)
                                     (OPERAND-STACK frame))
                              (LOCALS frame)
                              (METHOD-PTR frame)
                              (SYNC-OBJ-REF frame)
                              (RESUME-PC frame)
                              (frame-aux frame))))
  :hints (("Goal" :in-theory (enable wff-call-frame
                                     make-frame
                                     resume-pc
                                     return-pc
                                     operand-stack
                                     method-ptr
                                     locals
                                     frame-aux
                                     sync-obj-ref))))



(defthm wff-call-frame-make-frame-specific
  (implies (and (wff-call-frame frame)
                (equal (return-pc frame) return-pc))
           (WFF-CALL-FRAME (MAKE-FRAME return-pc
                              (LIST* V '(topx . topx)
                                     (OPERAND-STACK frame))
                              (LOCALS frame)
                              (METHOD-PTR frame)
                              (SYNC-OBJ-REF frame)
                              (RESUME-PC frame)
                              (frame-aux frame))))                              
  :hints (("Goal" :in-theory (enable wff-call-frame
                                     make-frame
                                     resume-pc
                                     return-pc
                                     operand-stack
                                     method-ptr
                                     locals
                                     frame-aux
                                     sync-obj-ref))))




(defthm not-category1
  (implies (equal (type-size (tag-of v)) 2)
           (not (category1 v)))
  :hints (("Goal" :in-theory (enable category1))))

(in-theory (disable frame-aux))

;;(i-am-here) ;; Sun Jul 31 19:33:16 2005

(defthm consistent-call-stack-linkage-if-originally-consitent
  (implies (and (<= (+ 2
                       (LEN (OPERAND-STACK (CURRENT-FRAME S))))
                    (METHOD-MAXSTACK (CURRENT-METHOD S)))
                (consistent-call-stack-linkage (THREAD-CALL-STACK 
                                                (THREAD-BY-ID (CURRENT-THREAD S)
                                                              (THREAD-TABLE S)))
                                               (instance-class-table s))
                (consp (THREAD-CALL-STACK (THREAD-BY-ID (CURRENT-THREAD S)
                                                        (THREAD-TABLE S)))))
           (CONSISTENT-CALL-STACK-LINKAGE
            (CONS (MAKE-FRAME (RETURN-PC (CURRENT-FRAME S))
                              (LIST* V '(topx . topx)
                                     (OPERAND-STACK (CURRENT-FRAME S)))
                              (LOCALS (CURRENT-FRAME S))
                              (METHOD-PTR (CURRENT-FRAME S))
                              (SYNC-OBJ-REF (CURRENT-FRAME S))
                              (RESUME-PC (CURRENT-FRAME S))
                              (frame-aux (current-frame s)))
                  (CDR (THREAD-CALL-STACK (THREAD-BY-ID (CURRENT-THREAD S)
                                                        (THREAD-TABLE S)))))
            (INSTANCE-CLASS-TABLE S)))
  :hints (("Goal" :in-theory (e/d (WFF-INVOCATION-FRAME)
                                  (RETURN-PC (RETURN-PC)
                                             consistent-frame)))))


(defthm consistent-frame-implies-sync-obj-bound
  (implies (and  (consistent-frame frame cl hp)
                 (NOT (EQUAL (SYNC-OBJ-REF frame)
                             -1)))
           (BOUND? (SYNC-OBJ-REF frame)
                   hp)))


(defthm consistent-thread-entry-implies-thread-mref
  (implies (and  (consistent-thread-entry thread cl hp)
                 (NOT (EQUAL (thread-mref thread)
                             -1)))
           (BOUND? (thread-mref thread)
                   hp)))




(defthm consistent-frame-max-local-implies-local-size-in-range
  (implies (and (consistent-frame-max-local frame cl)
                (not (mem '*abstract* (method-accessflags (deref-method (method-ptr frame) cl))))
                (not (mem '*native* (method-accessflags (deref-method (method-ptr frame) cl)))))
           (<= (LEN (LOCALS frame))
               (METHOD-MAXLOCALS 
                (deref-method (method-ptr frame) cl)))))



(defthm consistent-frame-max-local-implies-local-size-in-range-specific
  (implies (and (consistent-frame-max-local (current-frame s) (instance-class-table s))
                (not (mem '*abstract* (method-accessflags (current-method s))))
                (not (mem '*native* (method-accessflags (current-method s)))))
           (<= (LEN (LOCALS (current-frame s)))
               (METHOD-MAXLOCALS (current-method s)))))
                

(defthm consistent-state-implies-consistent-frame-max-local
  (implies (consistent-frame (current-frame s) (instance-class-table s) 
                             (heap s))
           (consistent-frame-max-local (current-frame s) (instance-class-table s))))


(defthm push-push-is-consistent-thread-entry
  (implies (and (CONSISTENT-VALUE-X V (INSTANCE-CLASS-TABLE S)
                                    (HEAP S))
                (equal (type-size (TAG-OF V))  2)
                (<= (+ 2
                       (LEN (OPERAND-STACK (CURRENT-FRAME S))))
                    (METHOD-MAXSTACK (CURRENT-METHOD S)))
                (consistent-state s))
           (consistent-thread-entry 
            (PUSH-STACK-OF-THREAD
             V
             (PUSH-STACK-OF-THREAD '(topx . topx)
                                   (THREAD-BY-ID (CURRENT-THREAD S)
                                                 (THREAD-TABLE S))))
            (instance-class-table s)
            (heap s)))
  :hints (("Goal" :in-theory (e/d (consistent-thread-entry
                                   frame-set-operand-stack
                                   thread-set-call-stack
                                   push-stack-of-thread)
                                  (thread-ref
                                   thread-mref
                                   consistent-call-stack-linkage
                                   valid-refp
                                   )))))





(defthm mem-replace-replace-thread-table-entry
  (implies (mem newv0 tt)
           (mem newv1 (replace-thread-table-entry 
                       newv0 newv1 tt))))


(defthm replace-thread-table-replace-thread-table
  (implies (and (mem newv0 tt)
                (not (mem newv1 tt)))
           (equal (replace-thread-table-entry
                   newv1 
                   newv2 
                   (replace-thread-table-entry 
                    newv0 newv1 tt))
                  (replace-thread-table-entry
                   newv0
                   newv2 tt)))
  :hints (("Goal" :do-not '(generalize))))


(defthm not-mem-collect-id-not-mem
  (implies (not (mem (thread-id thread) (collect-thread-id tt)))
           (not (mem thread tt))))



(defthm nodup-collect-thread-id-implies-not-mem
  (implies (and (mem newv0 tt)
                (not (equal newv1 newv0))
                (equal (thread-id newv1) (thread-id newv0))
                (nodup-set (collect-thread-id tt)))
           (not (mem newv1 tt)))
  :hints (("Goal" :do-not '(generalize))))


(defthm top-thread-call-stack-push-stack-of-thread
  (equal (top (thread-call-stack (push-stack-of-thread v thread)))
         (frame-set-operand-stack 
          (push v (operand-stack (top
                                  (thread-call-stack
                                   thread))))
          (top (thread-call-stack thread))))
  :hints (("Goal" :in-theory (enable frame-set-operand-stack
                                     push-stack-of-thread
                                     make-thread
                                     thread-set-call-stack
                                     thread-call-stack))))


(defthm not-equal-opstack-not-frame-equal
  (implies (not (equal (operand-stack frame2) 
                       (operand-stack frame1)))
           (not (equal frame2 frame1)))
  :rule-classes nil)

(defthm not-equal-frame-set-operand-stack
  (not (equal (frame-set-operand-stack 
               (push v (operand-stack frame)) frame)
              frame))
  :hints (("Goal" :in-theory (enable 
                              frame-set-operand-stack)
           :use ((:instance not-equal-opstack-not-frame-equal
                            (frame2 (frame-set-operand-stack 
                                     (push v (operand-stack frame))
                                     frame))
                            (frame1 frame))))))

  

(defthm not-equal-top-frame-not-thread-equal
  (implies (not (equal (top (thread-call-stack thread2))
                       (top (thread-call-stack thread1))))
           (not (equal thread2 thread1)))
  :rule-classes nil)

(defthm push-stack-of-thread-not-equal-old
  (not (equal (push-stack-of-thread v thread)
              thread))
  :hints (("Goal" :in-theory (disable top push)
           :use ((:instance not-equal-top-frame-not-thread-equal
                            (thread2 (push-stack-of-thread v thread))
                            (thread1 thread))
                 (:instance top-thread-call-stack-push-stack-of-thread)))))



(defthm nodup-collect-thread-id-specific
   (implies (and (mem newv0 tt)
                 (nodup-set (collect-thread-id tt)))
            (not (mem (push-stack-of-thread v newv0) tt)))
   :hints (("Goal" :do-not '(generalize)
            :use ((:instance nodup-collect-thread-id-implies-not-mem
                             (newv1 (push-stack-of-thread v newv0)))))))


(defthm push-stack-of-thread-reduce
   (equal (thread-id (push-stack-of-thread v thread))
          (thread-id thread)))





(defthm replace-thread-table-entry-same-same
  (implies (equal new1 new0)
           (equal (replace-thread-table-entry new1 new2 
                                              (replace-thread-table-entry new0 new1 tt))
                  (replace-thread-table-entry new0 new2 tt))))
    



;; (defthm consistent-thread-table-entries-reduce-to-all-consistent-thread-entry
;;   (implies (and (wff-thread-table tt)
;;                 (nodup-set (collect-thread-id tt)))
;;            (equal (consistent-thread-entries tt cl hp)
;;                   (all-consistent-thread-entry (collect-thread-id tt) tt cl hp)))
;;   :hints (("Goal" :in-theory (e/d () (consistent-thread-entry))
;;            :do-not '(generalize))))




(defthm consistent-state-implies-all-consistent-thread-entry
  (implies (consistent-state s)
           (ALL-CONSISTENT-THREAD-ENTRY (COLLECT-THREAD-ID (THREAD-TABLE S))
                                        (THREAD-TABLE S)
                                        (INSTANCE-CLASS-TABLE S)
                                        (HEAP S)))
  :hints (("Goal" :in-theory (e/d (consistent-state)
                                  (consistent-thread-table-entries-reduce-to-all-consistent-thread-entry))
           :use ((:instance
                  consistent-thread-table-entries-reduce-to-all-consistent-thread-entry
                  (tt (thread-table s))
                  (hp (heap s))
                  (cl (instance-class-table s)))))))




(defthm wff-thread-table-bound-then-mem
  (implies (and (wff-thread-table tt)
                (thread-by-id id tt))
           (mem (thread-by-id id tt) tt))
  :hints (("Goal" :in-theory (enable thread-by-id))))

(defthm consistent-state-implies-mem-current-thread
  (implies (consistent-state s)
           (MEM (THREAD-BY-ID (CURRENT-THREAD S) (THREAD-TABLE S)) (THREAD-TABLE S))))


;; (i-am-here) ;; Thu Jun 16 21:40:29 2005

;; (i-am-here) ;; Mon Jun 20 17:40:49 2005

;; (i-am-here) ;; Thu Jul 21 13:22:20 2005

(local 
 (defthm consistent-state-implies-consistent-heap-init-state
   (implies (CONSISTENT-STATE S)
            (CONSISTENT-HEAP-INIT-STATE (HEAP S)
                                        (INSTANCE-CLASS-TABLE S)
                                        (HEAP-INIT-MAP (AUX S))))
   :hints (("Goal" :in-theory (enable consistent-state)))))

;; (i-am-here) ;; Tue Jul 26 13:23:33 2005


(local 
 (DEFTHM
   CONSISTENT-STATE-PUSHSTACK-CONSISTENT-STATE-PUSHSTACK-2-lemma
   (IMPLIES (AND (CONSISTENT-VALUE-X V (INSTANCE-CLASS-TABLE S)
                                     (HEAP S))
                 (CATEGORY2 V)
                 (<= (+ 2
                        (LEN (OPERAND-STACK (CURRENT-FRAME S))))
                     (MAX-STACK S))
                 (CONSISTENT-STATE S))
            (CONSISTENT-STATE-STEP (PUSHSTACK V (pushStack '(topx . topx) S))))
   :hints (("Goal" :in-theory (e/d (class-exists?)
                                   (consistent-thread-entry consistent-jvp
                                                            fields))))))


(defthm consistent-state-step-implies-consistent-state
  (implies (consistent-state-step s)
           (consistent-state s))
  :hints (("Goal" :in-theory (e/d (consistent-state)
                                  (consistent-thread-table-entries-reduce-to-all-consistent-thread-entry))))
  :rule-classes nil)



(defthm consistent-state-step-push-push-consistent-state-push-push
  (implies (consistent-state-step (PUSHSTACK V (pushStack '(topx . topx) S)))
           (consistent-state (pushStack v (pushStack '(topx . topx) s))))
  :hints (("Goal" :in-theory (disable consistent-state-step)
           :use ((:instance
                  consistent-state-step-implies-consistent-state
                  (s (pushStack v (pushStack '(topx . topx) s))))))))



(DEFTHM
  CONSISTENT-STATE-PUSHSTACK-CONSISTENT-STATE-PUSHSTACK-2
  (IMPLIES (AND (CONSISTENT-VALUE-X V (INSTANCE-CLASS-TABLE S)
                                    (HEAP S))
                (CATEGORY2 V)
                (<= (+ 2
                       (LEN (OPERAND-STACK (CURRENT-FRAME S))))
                    (MAX-STACK S))
                (CONSISTENT-STATE S))
           (CONSISTENT-STATE (PUSHSTACK V (pushStack '(topx . topx) S)))))





