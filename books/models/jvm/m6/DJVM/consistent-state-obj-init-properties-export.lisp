(in-package "DJVM")
(include-book "consistent-state-obj-init")
(include-book "consistent-state-properties2") 
(include-book "INST/base-locals")
(include-book "djvm-heap")
(include-book "INST/base-bind-free")

(local (include-book "consistent-state-obj-init-properties"))

;;; popStack

(defthm consistent-state-obj-init-preserved-by-popStack 
  (implies (and (consistent-state-obj-init s)
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s) (thread-table s)))))
           (consistent-state-obj-init (popStack s)))
  :hints (("Goal" :in-theory (e/d (popStack popstack-of-thread)
                                  (consistent-state)))))


;;; pushStack 1 


(defthm consistent-state-obj-init-preserved-by-pushStack-1
  (implies (and (consistent-state-obj-init s)
                (wff-tagged-value v)
                (case-split (not (equal (tag-of v) 'REF)))
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s) (thread-table s)))))                
           (consistent-state-obj-init (pushStack v s)))
  :hints (("Goal" :in-theory (e/d (pushStack push-stack-of-thread)
                                  (consistent-state)))))

;;; pushStack 2 

(defthm consistent-state-obj-init-preserved-by-pushStack-2
  (implies (and (consistent-state-obj-init s)
                (wff-tagged-value v)
                (case-split (equal (tag-of v) 'REF))
                (case-split (NULLp v))
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s)))))
           (consistent-state-obj-init (pushStack v s)))
  :hints (("Goal" :in-theory (e/d (pushStack push-stack-of-thread)
                                  (consistent-state)))))

;;; pushStack 3 

(defthm consistent-state-obj-init-preserved-by-pushStack-3
  (implies (and (consistent-state-obj-init s)
                (wff-tagged-value v)
                (case-split (equal (tag-of v) 'REF))
                (case-split (not (NULLp v)))
                (case-split (initialized-ref (value-of v)
                                             (heap-init-map (aux s))))
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s)))))
           (consistent-state-obj-init (pushStack v s)))
  :hints (("Goal" :in-theory (e/d (pushStack push-stack-of-thread)
                                  (consistent-state)))))

;;; pushStack 4 
          

(defthm consistent-state-obj-init-preserved-by-pushStack-4
  (implies (and (consistent-state-obj-init s)
                (wff-tagged-value v)
                (case-split (equal (method-ptr-methodname
                                    (method-ptr (current-frame s)))
                                   "<init>"))
                (or (equal (value-of v)
                           (acl2::g 'this (frame-aux (current-frame s))))
                    (mem (value-of v)
                         (collect-values (frame-obj-init-map (current-frame s)))))
                (case-split (equal (tag-of v) 'REF))
                (case-split (not (NULLp v)))
                (case-split (not (initialized-ref (value-of v)
                                                  (heap-init-map (aux s)))))
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s)))))
           (consistent-state-obj-init (pushStack v s)))
  :hints (("Goal" :in-theory (e/d (pushStack push-stack-of-thread)
                                  (consistent-state))
           :expand (current-frame s)
           :do-not '(fertilize))))


;;; pushStack 5 

(defthm consistent-state-obj-init-preserved-by-pushStack-5
  (implies (and (consistent-state-obj-init s)
                (wff-tagged-value v)
                (case-split (not (equal (method-ptr-methodname
                                         (method-ptr (current-frame s)))
                                        "<init>")))
                (mem (value-of v)
                     (collect-values (frame-obj-init-map (current-frame s))))
                (case-split (equal (tag-of v) 'REF))
                (case-split (not (NULLp v)))
                (case-split (not (initialized-ref (value-of v)
                                                  (heap-init-map (aux s)))))
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s)))))
           (consistent-state-obj-init (pushStack v s)))
  :hints (("Goal" :in-theory (e/d (pushStack push-stack-of-thread)
                                  (consistent-state))
           :do-not '(fertilize))))


;;; set local 1 


(defthm consistent-state-obj-init-preserved-by-state-set-local-at-1
  (implies (and (consistent-state-obj-init s)
                (wff-tagged-value v)
                (integerp i)
                (<= 0 i)
                (< i (len (locals (current-frame s))))
                (case-split (not (equal (tag-of v) 'REF)))
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s)))))                
           (consistent-state-obj-init (state-set-local-at i v s)))
  :hints (("Goal" :in-theory (e/d (state-set-local-at 
                                   set-local-at-of-thread) (consistent-state))
           :do-not-induct t)))



(defthm consistent-state-obj-init-preserved-by-state-set-local-at-2
  (implies (and (consistent-state-obj-init s)
                (wff-tagged-value v)
                (integerp i)
                (<= 0 i)
                (< i (len (locals (current-frame s))))
                (case-split (equal (tag-of v) 'REF))
                (case-split (NULLp v))
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s)))))                
           (consistent-state-obj-init (state-set-local-at i v s)))
  :hints (("Goal" :in-theory (e/d (set-local-at-of-thread
                                   state-set-local-at)
                                  (consistent-state))
           :do-not-induct t)))




(defthm consistent-state-obj-init-preserved-by-state-set-local-at-3
  (implies (and (consistent-state-obj-init s)
                (wff-tagged-value v)
                (integerp i)
                (<= 0 i)
                (< i (len (locals (current-frame s))))
                (case-split (equal (tag-of v) 'REF))
                (case-split (not (NULLp v)))
                (case-split (initialized-ref (value-of v) (heap-init-map (aux
                                                                          s))))
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s)))))                
           (consistent-state-obj-init (state-set-local-at i v s)))
  :hints (("Goal" :in-theory (e/d (state-set-local-at
                                   set-local-at-of-thread) 
                                  (consistent-state))
           :do-not-induct t)))





(defthm consistent-state-obj-init-preserved-by-state-set-local-at-4
  (implies (and (consistent-state-obj-init s)
                (wff-tagged-value v)
                (integerp i)
                (<= 0 i)
                (< i (len (locals (current-frame s))))
                (case-split (equal (method-ptr-methodname
                                    (method-ptr (current-frame s)))
                                   "<init>"))
                (or (equal (value-of v)
                           (acl2::g 'this (frame-aux (current-frame s))))
                    (mem (value-of v)
                         (collect-values (frame-obj-init-map (current-frame s)))))
                (case-split (equal (tag-of v) 'REF))
                (case-split (not (NULLp v)))
                (case-split (not (initialized-ref (value-of v) (heap-init-map (aux s)))))
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s)))))                
           (consistent-state-obj-init (state-set-local-at i v s)))
  :hints (("Goal" :in-theory (e/d (state-set-local-at 
                                   set-local-at-of-thread) (consistent-state))
           :do-not-induct t)))





(defthm consistent-state-obj-init-preserved-by-state-set-local-at-5
  (implies (and (consistent-state-obj-init s)
                (wff-tagged-value v)
                (integerp i)
                (<= 0 i)
                (< i (len (locals (current-frame s))))
                (case-split (not (equal (method-ptr-methodname
                                         (method-ptr (current-frame s)))
                                        "<init>")))
                (mem (value-of v)
                     (collect-values (frame-obj-init-map (current-frame s))))
                (case-split (equal (tag-of v) 'REF))
                (case-split (not (NULLp v)))
                (case-split (not (initialized-ref (value-of v) (heap-init-map (aux s)))))
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s)))))
           (consistent-state-obj-init (state-set-local-at i v s)))
  :hints (("Goal" :in-theory (e/d (state-set-local-at
                                   set-local-at-of-thread) (consistent-state))
           :do-not-induct t)))

;----------------------------------------------------------------------


(defthm consistent-state-obj-init-preserved-by-state-set-pc
  (equal (consistent-state-obj-init (state-set-pc any s))
         (consistent-state-obj-init s)))


;----------------------------------------------------------------------


(defthm consistent-state-obj-init-state-set-local-at-general-specific
  (implies (and (consistent-state-obj-init (state-set-local-at i (topStack s1) s1))
                (wff-thread (thread-by-id (current-thread s1) (thread-table s1)))
                (equal (frame-obj-init-map (current-frame s2))
                       (frame-obj-init-map (current-frame s1)))
                (equal (acl2::g 'this (frame-aux (current-frame s2)))
                       (acl2::g 'this (frame-aux (current-frame s1))))
                (equal (method-ptr (current-frame s2))
                       (method-ptr (current-frame s1)))
                (equal (heap-init-map (aux s2))
                       (heap-init-map (aux s1)))
                (equal (len (locals (current-frame s2)))
                       (len (locals (current-frame s1))))
                (wff-tagged-value (topStack s1))
                (thread-by-id (current-thread s2) (thread-table s2))
                (consp (thread-call-stack 
                        (thread-by-id (current-thread s2) (thread-table s2))))
                (integerp i)
                (<= 0 i)
                (< i (len (locals (current-frame s1))))
                (consistent-state-obj-init s2))
            (consistent-state-obj-init (state-set-local-at i (topStack s1) s2)))
  :hints (("Goal" :do-not '(generalize fertilize)
           :use ((:instance
                  consistent-state-obj-init-state-set-local-at-general-lemma
                  (v (topStack s1)))))))



(defthm consistent-state-obj-init-invalidate-category2
  (implies (and (consistent-state-obj-init s)
                (<= -1 i)
                (< i (len (locals (current-frame s))))
                (integerp i)
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s)))))                
           (consistent-state-obj-init (invalidate-category2-value i s)))
  :hints (("Goal" :in-theory (enable invalidate-category2-value))))




(defthm consistent-state-obj-init-state-set-local-at
  (implies (and (consistent-state-obj-init s)
                (<= 0 i)
                (< i (len (locals (current-frame s))))
                (integerp i)
                (topStack-guard-strong s)
                (wff-tagged-value (topStack s))
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s)))))
           (consistent-state-obj-init (state-set-local-at i (topStack s) s)))
  :hints (("Goal" :in-theory (disable state-set-local-at))))


(defthm consistent-state-obj-init-pushStack
   (implies (and (consistent-state-obj-init s)
                 (<= 0 i)
                 (< i (len (locals (current-frame s))))
                 (integerp i)
                 (thread-by-id (current-thread s) (thread-table s))
                 (consp (thread-call-stack (thread-by-id (current-thread s)
                                                         (thread-table s)))))
            (consistent-state-obj-init (pushStack (local-at i s) s))))



(defthm not-consp-deref2-init-implies-initialized-ref
  (implies (not (consp (deref2-init (tag-REF v) hp-init)))
           (initialized-ref v hp-init))
  :hints (("Goal" :in-theory (enable initialized-ref))))



(defthm not-consp-deref2-init-implies-initialized-ref
  (implies (not (consp (deref2-init (tag-REF v) hp-init)))
           (initialized-ref v hp-init))
  :hints (("Goal" :in-theory (enable initialized-ref))))
  


(defthm consistent-state-obj-init-preserved-by-state-set-heap
  (equal (consistent-state-obj-init (state-set-heap any s))
         (consistent-state-obj-init s)))



(defthm consistent-state-obj-init-preserved-by-resolveClassReference
  (equal (consistent-state-obj-init (resolveClassReference any s))
         (consistent-state-obj-init s))
  :hints (("Goal" :in-theory (disable resolveClassReference))))


(defthm consistent-state-obj-init-preserved-by-getArrayClass
  (equal (consistent-state-obj-init (getArrayClass any s))
         (consistent-state-obj-init s))
  :hints (("Goal" :in-theory (disable getArrayClass))))




(defthm consistent-state-obj-init-preserved-by-make-state
  (implies (equal (heap-init-map (aux s)) (heap-init-map aux))
           (equal (consistent-state-obj-init (make-state pc cid 
                                                         hp 
                                                         (thread-table s)
                                                         cl 
                                                         env
                                                         ef
                                                         aux))
                  (consistent-state-obj-init s)))
  :hints (("Goal" :in-theory (enable consistent-state-obj-init)))) 

(defthm getArrayClass-reduce
  (and (equal (PC (GETARRAYCLASS any s))
              (pc s))
       (equal (current-thread (getarrayclass any s))
              (current-thread s))
       (equal (thread-table (getarrayclass any s))
              (thread-table s))
       (equal (current-frame (getarrayclass any s))
              (current-frame s))
       (equal (heap-init-map (aux (getarrayclass any s)))
              (heap-init-map (aux s))))
  :hints (("Goal" :in-theory (enable getarrayclass))))


(defthm resolveClassReference-reduce
  (and (equal (PC (resolveClassReference any s))
              (pc s))
       (equal (current-thread (resolveClassReference any s))
              (current-thread s))
       (equal (thread-table (resolveClassReference any s))
              (thread-table s))
       (equal (heap-init-map (aux (resolveClassReference any s)))
              (heap-init-map (aux s)))
       (equal (current-frame (resolveClassReference any s))
              (current-frame s)))
  :hints (("Goal" :in-theory (enable resolveClassReference))))

;----------------------------------------------------------------------


(defthm consistent-state-obj-init-update-trace
  (equal    (consistent-state-obj-init (update-trace any s))
            (consistent-state-obj-init s))
   :hints (("Goal" :in-theory (disable update-trace))))



;----------------------------------------------------------------------

(in-theory (disable consistent-state-obj-init state-set-local-at pushStack popStack))

;----------------------------------------------------------------------
