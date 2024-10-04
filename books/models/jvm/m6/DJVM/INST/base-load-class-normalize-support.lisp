(in-package "DJVM")
(include-book "../../DJVM/consistent-state")
(include-book "../../DJVM/consistent-state-properties")


(defthm getArrayClass-does-not-affect-current-thread
  (and (equal (current-thread (getArrayClass any s)) 
              (current-thread s))
       (equal (thread-table (getArrayClass any s))
              (thread-table s)))
  :hints (("Goal" :in-theory (enable getArrayClass))))


(defthm resolveClassReference-does-not-affect-current-thread
  (and (equal (current-thread (resolveClassReference any s))
              (current-thread s))
       (equal (thread-table (resolveClassReference  any s))
              (thread-table s))))


(defthm current-frame-getArrayClass
  (equal (current-frame (getArrayClass any s))
         (current-frame s))
  :hints (("Goal" :in-theory (e/d (current-frame)
                                  (getArrayClass)))))

(defthm current-frame-resolveClassReference
  (equal (current-frame (resolveClassReference any s))
         (current-frame s))
  :hints (("Goal" :in-theory (e/d (current-frame)
                                  (resolveClassReference)))))


(local 
 (encapsulate () 
   (local (include-book "base-loader-preserve-consistent-state"))
   (acl2::set-enforce-redundancy t)
   (defthm deref-method-no-change-add-new-class
     (implies (and (not (isClassTerm (class-by-name (classname class-rep) cl)))
                   (deref-method method-ptr cl))
              (equal (deref-method method-ptr (cons class-rep cl))
                     (deref-method method-ptr cl)))
     :hints (("Goal" :in-theory (enable deref-method))))))


(local 
 (defthm deref-method-no-change-load-class2
   (implies (and (not (class-loaded? name s))
                 (deref-method method-ptr (instance-class-table s)))
            (equal (deref-method method-ptr (instance-class-table (load_class2 name s)))
                   (deref-method method-ptr (instance-class-table s))))
   :hints (("Goal" :in-theory (e/d (load_class2 add-instance-class-entry class-loaded?)
                                   (make-runtime-class-rep isClassTerm))))))


(local 
 (encapsulate () 
   (local (include-book "base-loader-preserve-consistent-state"))
   (defthm not-loaded-notloaded-after-load-class-x-specific
     (implies (not (class-loaded? any s))
              (NOT (CLASS-LOADED? ANY
                                  (LOAD_CLASS_X ANY (LOAD_CLASS_X ANY S SEEN '2)
                                             SEEN '1)))))))
          

(local 
 (defthm deref-method-no-change-load-class-x
   (implies (deref-method method-ptr (instance-class-table s))
            (equal (deref-method method-ptr (instance-class-table  (load_class_x n-o-ns s seen mode)))
                   (deref-method method-ptr (instance-class-table s))))
   :hints (("Goal" :in-theory (e/d ()
                                   (make-runtime-class-rep isClassTerm))
            :do-not '(generalize)))))
                                        


(local 
 (defthm deref-method-no-change-load_class
   (implies (deref-method method-ptr (instance-class-table s))
            (equal (deref-method method-ptr (instance-class-table  
                                             (load_class n s)))
                   (deref-method method-ptr (instance-class-table s))))
   :hints (("Goal" :in-theory (e/d ()
                                   (make-runtime-class-rep isClassTerm))
            :do-not '(generalize)))))


(local 
 (defthm deref-method-no-change-load_array_class2
   (implies (deref-method method-ptr (instance-class-table s))
            (equal (deref-method method-ptr (instance-class-table  
                                             (load_array_class2 any s)))
                   (deref-method method-ptr (instance-class-table s))))
   :hints (("Goal" :in-theory (e/d (load_array_class2)
                                   (make-runtime-class-rep isClassTerm))
            :do-not '(generalize)))))



(local 
 (defthm deref-method-no-change-load_array_class
   (implies (deref-method method-ptr (instance-class-table s))
            (equal (deref-method method-ptr (instance-class-table  
                                             (load_array_class any s)))
                   (deref-method method-ptr (instance-class-table s))))
   :hints (("Goal" :in-theory (e/d (load_array_class)
                                   (make-runtime-class-rep 
                                    load_array_class2 load_class
                                    isClassTerm))
            :do-not '(generalize)))))


(local 
 (defthm current-method-getArrayClass
   (implies (current-method s)
            (equal (current-method (getArrayClass any s))
                   (current-method s)))
   :hints (("Goal" :in-theory (e/d (current-frame getArrayClass)
                                   (load_array_class))))))


(local          
 (defthm current-method-resolveClassReference
   (implies (current-method s)
            (equal (current-method (resolveClassReference any s))
                   (current-method s)))
   :hints (("Goal" :in-theory (e/d (current-method resolveClassReference)
                                   (load_array_class))))))

(local 
 (skip-proofs 
  (defthm consistent-state-implies-current-method
    (implies (consistent-state s)
             (current-method s)) ;; valid-method-ptr
    :hints (("Goal" :in-theory (enable consistent-state))))))


(local          
 (defthm current-method-resolveClassReference-general
   (implies (and (current-method s)
                 (equal (method-ptr (current-frame s)) method-ptr))
            (equal (deref-method method-ptr (instance-class-table (resolveClassReference any s)))
                   (deref-method method-ptr (instance-class-table s))))
   :hints (("Goal" :in-theory (e/d (current-method) (CURRENT-METHOD-RESOLVECLASSREFERENCE))
            :use current-method-resolveClassReference))))



(local 
 (defthm current-method-getArrayClass-general
   (implies (and (current-method s)
                 (equal (method-ptr (current-frame s)) method-ptr))
            (equal (deref-method method-ptr (instance-class-table (getArrayClass any s)))
                   (deref-method method-ptr (instance-class-table s))))
   :hints (("Goal" :in-theory (e/d (current-method)
                                   (current-method-getArrayClass))
            :use current-method-getArrayClass))))



(local 
 (defthm consistent-state-implies-wff-state-b
   (implies (consistent-state s)
            (wff-state s))))

(local
 (encapsulate ()
  (local (include-book "base-loader-preserve-consistent-state"))
  (defthm getArrayClass-preserve-consistency
    (implies (consistent-state s)
             (consistent-state (getArrayClass any s))))))




(local 
 (defthm consistent-state-implies-wff-class-table-b
   (implies (consistent-state s)
            (wff-class-table (class-table s)))))


(local 
 (defthm consistent-state-implies-wff-instance-class-table-b
   (implies (consistent-state s)
            (wff-instance-class-table (instance-class-table s)))))



(local
 (encapsulate ()
  (local (include-book "base-loader-preserve-consistent-state"))
  (defthm resolveClassReference-preserve-consistency
    (implies (consistent-state s)
             (consistent-state (resolveClassReference any s))))))






(defthm topStack-guard-strong-not-affected-by-class-loading
  (and (implies (consistent-state s) 
                ;; Wed Apr  7 11:29:37 2004 added 
                (equal (topStack-guard-strong (getArrayClass any s))
                       (topStack-guard-strong s)))
       (implies (consistent-state s)
                (equal (topStack-guard-strong (resolveClassReference any s))
                       (topStack-guard-strong s))))
  :hints (("Goal" :in-theory (e/d (topStack-guard-strong)
                                  (getArrayClass resolveClassReference
                                                 method-ptr)))))




(defthm wff-call-stack-consistent-state
  (implies (wff-heap (heap s))
           (alistp (heap s))))

(defthm wff-heap-wff-state
  (implies (consistent-state s)
           (wff-heap (heap s)))
  :hints (("Goal" :in-theory (enable consistent-state))))


(defthm consistent-state-wff-state-b
  (implies (consistent-state s)
           (wff-state s)))

(defthm acl2-numberp-pc
  (implies (consistent-state s)
           (integerp (pc s))))
  

(defthm topStack-guard-strong-implies-topStack-guard
  (implies (topStack-guard-strong s)
           (topStack-guard s))
  :hints (("Goal" :in-theory (enable topStack-guard-strong 
                                     topStack-guard)))
  :rule-classes :forward-chaining)


(defthm current-frame-getArrayClass
  (equal (current-frame (getArrayClass any s))
         (current-frame s))
  :hints (("Goal" :in-theory (e/d (current-frame)
                                  (getArrayClass)))))

(defthm current-frame-resolveClassReference
  (equal (current-frame (resolveClassReference any s))
         (current-frame s))
  :hints (("Goal" :in-theory (e/d (current-frame)
                                  (resolveClassReference)))))



(defthm wff-class-table-load_array
  (implies (wff-class-table (class-table s))
           (wff-class-table (class-table (getArrayClass any s))))
  :hints (("Goal" :in-theory (enable getArrayClass wff-class-table))))


(defthm wff-class-table-resolveClassReference
  (implies (wff-class-table (class-table s))
           (wff-class-table (class-table (resolveClassReference any s))))
  :hints (("Goal" :in-theory (enable resolveClassReference load_class))))


;----------------------------------------------------------------------

; some rules to go up to prove stronger result -- consistent-state to get
; result of well-formed-ness 
;    


;; (defthm thread-by-id-popStack-normalize
;;   (equal (THREAD-BY-ID
;;           (CURRENT-THREAD S)
;;           (THREAD-TABLE
;;            (POPSTACK
;;         (GETARRAYCLASS (NORMALIZE-TYPE-REP (ARG INST))
;;                        (RESOLVECLASSREFERENCE (NORMALIZE-TYPE-REP (ARG INST))


(defthm thread-by-id-popStack-is-popStack-of-thread
  (implies (and (consistent-state s)
                (equal (current-thread s) id))
           (equal (thread-by-id id
                                (thread-table (popstack s)))
                  (popstack-of-thread (thread-by-id (current-thread s)
                                                    (thread-table s))))))

;; this is likely to be wrong!! 

(defthm thread-call-stack-pop-stack-of-thread-is
  (equal (thread-call-stack (popSTACK-OF-THREAD thread))
         (push (frame-set-operand-stack (pop (operand-stack (top
                                                             (thread-call-stack thread))))
                                        (top (thread-call-stack thread)))
               (pop (thread-call-stack thread))))
  :hints (("Goal" :in-theory (e/d (popstack-of-thread) ()))))


(defthm build-an-array-instance-does-not-affect-s
  (equal (mv-nth 1 (build-an-array-instance base-type  bound s))
         s))


(defthm wff-call-frame-current-frame
  (implies (consistent-state s)
           (wff-call-frame (current-frame s))))
;;
;; more suitable in the base-consistent-state.lisp  


;----------------------------------------------------------------------

;; (i-am-here) ;; Sat May 28 00:01:33 2005

(defthm deref-method-getArrayClass-general
  (implies (and (consistent-state s)
                (equal (method-ptr (current-frame s)) method-ptr))
           (equal (deref-method method-ptr (instance-class-table (getArrayClass any s)))
                  (deref-method method-ptr (instance-class-table s))))
  :hints (("Goal" :in-theory (disable getArrayClass))))


(defthm deref-method-resolveClassReference-general
  (implies (and (consistent-state s)
                (equal (method-ptr (current-frame s)) method-ptr))
           (equal (deref-method method-ptr (instance-class-table (resolveClassReference any s)))
                  (deref-method method-ptr (instance-class-table s))))
    :hints (("Goal" :in-theory (disable resolveClassReference))))

