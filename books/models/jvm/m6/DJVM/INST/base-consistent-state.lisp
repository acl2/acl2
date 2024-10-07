(in-package "DJVM")
(include-book "../../DJVM/consistent-state")
(include-book "../../DJVM/consistent-state-properties")
(include-book "../../DJVM/INST/base-array")
(include-book "../../BCV/bcv-functions")


(in-theory (disable consistent-object))

(local 
 (defthm consistent-heap1-bound?-heap-consistent-object
  (implies (and (consistent-heap1 hp1 hp cl id)
                (bound? ref hp1))
           (consistent-object (binding ref hp1) hp cl))
  :hints (("Goal" :in-theory (e/d (binding bound?) (consistent-object))))))


(local 
 (defthm consistent-heap1-bound?-heap-consistent-object-specific
  (implies (and (consistent-heap1 hp1 hp cl 0)
                (bound? ref hp1))
           (consistent-object (binding ref hp1) hp cl))))



(local 
 (defthm consistent-state-implies-consistent-heap1
   (implies (consistent-state s)
            (consistent-heap1 (heap s) (heap s) (instance-class-table s) 0))
   :hints (("Goal" :in-theory (e/d (consistent-state consistent-heap))))))


(local 
 (defthm consistent-value-x-tag-REF-check-NULL-implies-bound?
   (implies (and (not (check-NULL tagged-ref))
                 (consistent-value-x tagged-ref cl hp)
                 (equal (tag-of tagged-ref) 'REF))
            (bound? (rREF tagged-ref) hp))
   :hints (("Goal" :in-theory (e/d (rREF consistent-value) ())))))


(defthm consistent-state-not-null-wff-REFp-implies-consistent-object
  (implies (and (not (check-NULL tagged-ref))
                (consistent-state s)
                (consistent-value-x tagged-ref (instance-class-table s) 
                                    (heap s))
                (equal (tag-of tagged-ref) 'REF))
           (consistent-object (deref2 tagged-ref (heap s))
                              (heap s)
                              (instance-class-table s)))
  :hints (("Goal" :in-theory (e/d (deref2) (binding-rREF-normalize
                                            consistent-value-x)))))



(defthm consistent-state-not-null-wff-REFp-implies-consistent-object-f
  (implies (and (consistent-value-x tagged-ref (instance-class-table s) 
                                    (heap s))
                (not (check-NULL tagged-ref))
                (consistent-state s)
                (equal (tag-of tagged-ref) 'REF))
           (consistent-object (deref2 tagged-ref (heap s))
                              (heap s)
                              (instance-class-table s)))
  :hints (("Goal" :in-theory (e/d (deref2) (binding-rREF-normalize
                                            consistent-value-x))))
  :rule-classes :forward-chaining)



(defthm REFp-consistent-state-not-null
  (implies (and (REFp v (heap s))
                (consistent-state s)
                (equal (instance-class-table s) cl)
                (not (nullp v)))
           (consistent-object (deref2 v (heap s)) (heap s) cl))
  :hints (("Goal" :in-theory (e/d (REFp consistent-heap deref2) (binding-rref-normalize)))))

(defthm consistent-object-wff-object-strong
  (implies (consistent-object obj hp cl)
           (wff-obj-strong obj))
  :hints (("Goal" :in-theory (enable consistent-object)))
  :rule-classes :forward-chaining)


(defthm wff-obj-strong-wff-obj-f
  (implies (wff-obj-strong obj)
           (wff-obj obj))
  :rule-classes :forward-chaining)

(defthm safe-topStack-normalize
  (equal (safe-topStack s)
         (topStack s))
  :hints (("Goal" :in-theory (enable safe-topStack current-frame))))

(defthm safe-popStack-normalize
  (equal (safe-popStack s)
         (popStack s))
  :hints (("Goal" :in-theory (enable safe-popStack 
                                     popstack-of-thread
                                     frame-set-operand-stack current-frame))))

(defthm consistent-state-topStack-guard-strong-implies-consistent-value-x
  (implies (and (topstack-guard-strong s)
                (consistent-state s))
           (consistent-value-x (topStack s) (instance-class-table s) (heap s)))
  :hints (("Goal" :in-theory (e/d (safe-topstack) (consistent-value-x))
           :use CONSISTENT-STATE-TOPSTACK-CONSISTENT-VALUE-X))
  :rule-classes :forward-chaining)


(defthm consistent-state-topStack-guard-strong-implies-consistent-value-x-b
  (implies (and (topstack-guard-strong s)
                (consistent-state s))
           (consistent-value-x (topStack s) (instance-class-table s) (heap s)))
  :hints (("Goal" :in-theory (e/d (safe-topstack) (consistent-value-x)))))




;;
;; Mon Apr 18 22:05:52 2005. The idea is now how to make acl2 to derive these. 
;;
;; when the value is not on the top!!
;;

(in-theory (disable topStack popStack consistent-value-x))


(defthm consistent-state-popStack
  (implies (and (topstack-guard-strong s)
                (consistent-state s))
           (consistent-state (popStack s)))
  :hints (("Goal" :use consistent-state-popStack-consistent-state)))
           

(defthm consistent-state-topStack-guard-strong-implies-consistent-value-x-2
  (implies (and (topstack-guard-strong (popStack s))
                (topstack-guard-strong s)
                (consistent-state s))
           (consistent-value-x (topStack (popStack s)) 
                               (instance-class-table s)
                               (heap s)))
  :hints (("Goal" :use
           ((:instance consistent-state-topStack-guard-strong-implies-consistent-value-x
                       (s (popStack s))))))
  :rule-classes :forward-chaining)
  

(defthm consistent-state-topStack-guard-strong-implies-consistent-value-x-2-b
  (implies (and (topstack-guard-strong (popStack s))
                (topstack-guard-strong s)
                (consistent-state s))
           (consistent-value-x (topStack (popStack s)) 
                               (instance-class-table s)
                               (heap s))))


(in-theory (enable safe-secondstack secondstack-guard-strong))

(in-theory (disable tag-of))

(defthm wff-REFp-implies-tag-of-being-REF
  (implies (wff-REFp v)
           (equal (tag-of v) 'REF))
  :hints (("Goal" :in-theory (enable wff-REFp tag-of))))

(defthm wff-obj-consistent-object-back
  (implies (consistent-object (deref2 x (heap s)) (heap s) (instance-class-table s))
           (WFF-OBJ (deref2 x (heap s)))))


(defthm wff-obj-strong-consistent-object-back
  (implies (consistent-object (deref2 x (heap s)) (heap s) (instance-class-table s))
           (WFF-OBJ-strong (deref2 x (heap s)))))



(defthm wff-common-info-wff-obj-strong-b
  (implies (wff-obj-strong obj)
           (wff-common-info (common-info obj))))
  

(defthm safe-pushStack-normalize
  (equal (safe-pushStack v s)
         (pushStack v s))
  :hints (("Goal" :in-theory (enable safe-pushStack push-stack-of-thread))))


(local (defthm method-ptr-frame-set-opstack
   (equal (method-ptr (frame-set-operand-stack opstack frame))
          (method-ptr frame))
   :hints (("Goal" :in-theory (enable frame-set-operand-stack)))))

;;(i-am-here)

(local 
 (defthm method-ptr-does-not-change-after-pop
   (implies (topstack-guard-strong s)
           (equal (method-ptr (current-frame (safe-popStack s)))
                  (method-ptr (current-frame s))))
           :hints (("Goal" :in-theory (e/d (safe-popStack 
                                            topstack-guard-strong
                                            current-frame)
                                           (safe-popStack-normalize
                                            topframe-normalization))))))

(defthm method-ptr-does-not-change-after-pop-popStack
  (implies (topstack-guard-strong s)
           (equal (method-ptr (current-frame (popStack s)))
                  (method-ptr (current-frame s))))
  :hints (("Goal" :use method-ptr-does-not-change-after-pop)))


(in-theory (disable pushStack tag-REF))
(in-theory (disable max-stack CODE-MAX-STACK
                    method-maxstack))


(defthm method-ptr-reduce
  (implies (topstack-guard-strong s)
           (equal (method-ptr (CAR (THREAD-CALL-STACK (THREAD-BY-ID (CURRENT-THREAD S)
                                                                    (THREAD-TABLE (POPSTACK
                                                                                   S))))))
                  (method-ptr (current-frame s))))
  :hints (("Goal" :use method-ptr-does-not-change-after-pop-popStack
           :in-theory (e/d (current-frame) (method-ptr-does-not-change-after-pop-popStack)))))

(defthm max-stack-no-change
  (implies (topstack-guard-strong s)
           (equal (max-stack (popStack s))
                  (max-stack s)))
  :hints (("Goal" :in-theory (e/d (max-stack) ()))))


(local (defthm operand-stack-frame-set-opstack
         (equal (operand-stack (frame-set-operand-stack opstack frame))
                opstack)
         :hints (("Goal" :in-theory (enable make-frame frame-set-operand-stack operand-stack)))))

(local 
 (defthm popStack-popOpStack
      (implies   (TOPSTACK-GUARD-STRONG S)
                  (equal (operand-stack (current-frame (safe-popStack s)))
                         (cdr (operand-stack (current-frame s)))))
   :hints (("Goal" :in-theory (e/d (safe-popStack 
                                    current-frame
                                    topstack-guard-strong)
                                   (topframe-normalization
                                    safe-popStack-normalize))))))


(local (defthm topstack-guard-strong-implies-consp-opstack
         (implies (topstack-guard-strong s)
                  (consp (operand-stack (current-frame s))))
         :hints (("Goal" :in-theory (enable topstack-guard-strong)))))

(local 
 (defthm popStack-decrease-stack-size
   (implies (TOPSTACK-GUARD-STRONG S)
            (equal (len (operand-stack (current-frame (safe-popStack s))))
                   (- (len (operand-stack (current-frame s))) 1)))
   :hints (("Goal" :in-theory (disable safe-popStack-normalize)))))

(defthm popStack-decrease-stack-size-popStack
  (implies (TOPSTACK-GUARD-STRONG S)
           (equal (len (operand-stack (current-frame (popStack s))))
                    (- (len (operand-stack (current-frame s))) 1)))
  :hints (("Goal" :use popStack-decrease-stack-size)))


(defthm consistent-state-pushStack-consistent-state-pushStack
   (implies (and (consistent-value-x v (instance-class-table s) (heap s))
                 (Category1 v)
                 (<= (+ 1 (len (operand-stack (current-frame s))))
                     (max-stack s))
                 (consistent-state s))
            (consistent-state (pushStack v s)))
   :hints (("Goal" :use consistent-state-pushStack-consistent-state)))



(defthm wff-state-consistent-state-specific-back
  (implies (consistent-state (pushStack v s))
           (wff-state (pushStack v s))))

;;;
;;; the strategy is to go upward and derive everything from consistent-state! 
;;; 


(in-theory (disable tag))


(in-theory (disable state-set-pc))

(defthm state-set-pc-consistent-state
  (implies (and (consistent-state s)
                (integerp pc))
           (consistent-state (state-set-pc pc s))))

;; (i-am-here) ;; Fri Jul 22 16:52:17 2005

(defthm consistent-value-x-and-tag-INT-implies-INT32p
  (implies (and (equal (djvm-translate-int-type (tag-of v)) 'INT)
                (consistent-value-x v cl hp))
           (INT32p (value-of v)))
  :hints (("Goal" :in-theory (enable consistent-value INT32p consistent-value-x)))
  :rule-classes :forward-chaining)


(defthm consistent-value-x-and-tag-INT-implies-INT32p-b
  (implies (and (equal (djvm-translate-int-type (tag-of (topStack s))) 'INT)
                (consistent-value-x (topStack s) (instance-class-table s) (heap s)))
           (INT32p (value-of (topStack s))))
  :hints (("Goal" :in-theory (enable consistent-value INT32p consistent-value-x))))


(defthm consistent-value-x-and-tag-REF-implies-wff-refp
  (implies (and (equal (tag-of tagged-value) 'REF)
                (consistent-value-x tagged-value cl hp))
           (wff-refp tagged-value))
  :hints (("Goal" :in-theory (enable consistent-value consistent-value-x)))
  :rule-classes :forward-chaining)


(defthm consistent-value-x-and-tag-REF-implies-wff-refp-b
  (implies (and (equal (tag-of (topStack s)) 'REF)
                (consistent-value-x (topStack s) (instance-class-table s) (heap s)))
           (wff-refp (topStack s)))
  :hints (("Goal" :in-theory (enable consistent-value consistent-value-x))))


(defthm consistent-state-thread-by-id-replace-thread-entry
  (implies (and (consistent-state s)
                (equal (thread-id thread) (current-thread s)))
           (equal (thread-by-id (current-thread s)
                                (replace-thread-table-entry 
                                 (thread-by-id (current-thread s)
                                               (thread-table s))
                                 thread
                                 (thread-table s)))
                  thread)))

(defthm thread-id-thread-set-call-stack
  (equal (thread-id (thread-set-call-stack cs thread))
         (thread-id thread)))


(defthm thread-id-thread-by-id 
  (implies (consistent-state s)
           (equal (thread-id (thread-by-id (current-thread s)
                                           (thread-table s)))
                  (current-thread s))))

(defthm method-ptr-no-change
  (implies (consistent-state s)
           (equal (method-ptr (current-frame (popStack s)))
                  (method-ptr (current-frame s))))
  :hints (("Goal" :in-theory (e/d (current-frame popStack
                                                 aux frame-set-operand-stack
                                                 popStack-of-thread
                                                 replace-thread-table-entry
                                                 state-set-thread-table
                                                 thread-by-id
                                                 thread-table 
                                                 current-thread)
                                  (topFrame-normalization 
                                   thread-table
                                   method-ptr 
                                   current-thread)))))

(defthm env-popStack-not-change
  (equal (env (popStack s))
         (env s))
  :hints (("Goal" :in-theory (e/d (current-frame popStack
                                                 aux frame-set-operand-stack
                                                 replace-thread-table-entry
                                                 state-set-thread-table
                                                 thread-by-id
                                                 thread-table 
                                                 current-thread)
                                  (topFrame-normalization)))))


;----------------------------------------------------------------------



(defthm car-thread-call-normalization
  (implies (equal (current-thread s) id)
           (equal 
            (CAR (THREAD-CALL-STACK (THREAD-BY-ID id 
                                                  (THREAD-TABLE s))))
            (current-frame s)))
  :hints (("Goal" :in-theory (e/d (current-frame)
                                  (topframe-normalization)))))

;----------------------------------------------------------------------


(defthm env-sig-popStack
  (implies (consistent-state s)
           (equal (env-sig (popstack s))
                  (env-sig s)))
  :hints (("Goal" :in-theory (enable env-sig))))


;----------------------------------------------------------------------



(defthm consistent-state-implies-op-stack-primitive-shared-guard
  (implies (and (consistent-state s)
                (NOT (MEM '*NATIVE*
                          (METHOD-ACCESSFLAGS (CURRENT-METHOD S)))))
           (op-stack-primitive-shared-guard s)))


;----------------------------------------------------------------------


(defthm canPopCategory1-implies-consistent-state
  (implies (and (canPopCategory1 (operand-stack (current-frame s)))
                (NOT (MEM '*NATIVE*
                          (METHOD-ACCESSFLAGS (CURRENT-METHOD S))))
                (consistent-state s))
           (consistent-state (popStack s)))
  :hints (("Goal" :in-theory (e/d (topstack-guard-strong) 
                                  (canPopCategory1 op-stack-primitive-shared-guard))
           :use consistent-state-popStack)))

;----------------------------------------------------------------------


(defthm current-frame-popStack                           
  (implies (consistent-state s)                      
           (equal (frame-pop-opstack (current-frame s))  
                  (current-frame (popStack s))))         
  :hints (("Goal" :in-theory (enable popStack current-frame
                                     frame-pop-opstack
                                     frame-set-operand-stack
                                     popstack-of-thread))))

;----------------------------------------------------------------------

(local 
 (defthm consistent-heap2-bound?-array-type-implies-consistent-array-object
   (implies (and (consistent-heap2 hp1 hp cl acl id)
                 (bound? v hp1)
                 (isArrayType (obj-type (binding v hp1))))
            (consistent-array-object (binding v hp1) hp cl acl))
   :hints (("Goal" :in-theory (e/d (bound? binding) 
                                   (consistent-array-object isArrayType))
            :do-not '(generalize)))))


(local (defthm REFp-consistent-heap-implies-consistent-array-object-if-array-type
  (implies (and (REFp v hp1)
                (not (nullp v))
                (isArrayType (obj-type (deref2 v hp1)))
                (consistent-heap2 hp1 hp cl acl id))
           (consistent-array-object (deref2 v hp1) hp cl acl))
  :hints (("Goal" :in-theory (e/d (deref2 REFp)
                                  (consistent-array-object 
                                   isArrayType
                                   binding-rref-normalize))))))


(local (defthm consistent-state-consistent-heap2
         (implies (consistent-state s)
                  (consistent-heap2 (heap s) (heap s) 
                                    (instance-class-table s)
                                    (array-class-table s) 0))
         :hints (("Goal" :in-theory (enable consistent-state)))))
         

(defthm REFp-consistent-state-implies-consistent-array-object-if-array-type
  (implies (and (REFp (topStack s) (heap s))
                (not (nullp (topStack s)))
                (isArrayType (obj-type (deref2 (topStack s) (heap s))))
                (equal (heap s) hp)
                (equal (instance-class-table s) cl)
                (equal (array-class-table s) acl)
                (consistent-state s))
           (consistent-array-object (deref2 (topStack s) hp) hp cl acl))
  :hints (("Goal" :restrict
           ((REFp-consistent-heap-implies-consistent-array-object-if-array-type
            ((id 0)))))))


(defthm REFp-consistent-state-implies-consistent-array-object-if-array-type-2
  (implies (and (REFp v (heap s))
                (not (nullp v))
                (isArrayType (obj-type (deref2 v (heap s))))
                (equal (instance-class-table s) cl)
                (equal (array-class-table s) acl)
                (consistent-state s))
           (consistent-array-object (deref2 v  (heap s)) (heap s) cl acl))
  :hints (("Goal" :restrict
           ((REFp-consistent-heap-implies-consistent-array-object-if-array-type
            ((id 0)))))))


;----------------------------------------------------------------------

(local (defthm consistent-array-object-implies-array-type-s
  (implies (consistent-array-object obj hp cl acl)
           (array-type-s (obj-type obj) cl))
  :hints (("Goal" :in-theory (enable consistent-array-object)))))


(defthm consistent-array-object-implies-array-type-s-specific
  (implies (and (consistent-array-object (deref2 (topStack s) (heap s))
                                         (heap s)
                                         (instance-class-table s)
                                         (array-class-table s))
                (equal (heap s) hp)
                (equal (instance-class-table s) cl))
           (array-type-s (obj-type (deref2 (topStack s) hp))
                         cl)))




(defthm consistent-array-object-implies-array-type-s-specific-2
  (implies (and (consistent-array-object (deref2 v (heap s))
                                         (heap s)
                                         (instance-class-table s)
                                         (array-class-table s))
                (equal (instance-class-table s) cl))
           (array-type-s (obj-type (deref2 v (heap s)))
                         cl)))


;----------------------------------------------------------------------


;;(i-am-here)

(defthm current-frame-not-changed-by-state-set-pc
  (equal (current-frame (state-set-pc any s))
         (current-frame s))
  :hints (("Goal" :in-theory (enable state-set-pc))))

(defthm aux-pushStack
  (equal (aux (pushStack v s))
         (aux s))
  :hints (("Goal" :in-theory (enable pushStack))))

(defthm method-ptr-current-frame
  (implies (consistent-state s)
           (equal (method-ptr (current-frame (pushStack v s)))
                  (method-ptr (current-frame s))))
  :hints (("Goal" :in-theory (e/d (pushStack current-frame
                                             push-stack-of-thread)
                                  (car-thread-call-normalization 
                                   topframe-normalization)))))

;; (i-am-here)

(defthm no-pending-exception
  (equal  (PENDING-EXCEPTION
           (pushstack v s))
          (pending-exception s))
  :hints (("Goal" :in-theory (enable pending-exception))))


;;; these are generally useful. 

;----------------------------------------------------------------------
;
; Some properties about values that come out of a consistent array-object
;

;; (i-am-here) ;; Sat Apr 30 17:27:13 2005

;----------------------------------------------------------------------


;; (defthm consistent-state-topStack-tag-REF-then-REFp
;;   (implies (and (equal (tag-of (topStack s)) 'REF)
;;                 (consistent-state s)
;;                 (equal (heap s) 
;;            (REFp (topStack s) 

;; (i-am-here) ;; Tue May  3 20:57:40 2005
;; i-am-here!!

;;; We want this one! 

(defthm consistent-value-tag-REF-implies-REFp-specific
  (implies (and (consistent-value-x v (instance-class-table s) (heap s))
                (equal (tag-of v) 'REF))
           (REFp v (heap s)))
  :hints (("Goal" :in-theory (enable consistent-value-x consistent-value REFp))))


;----------------------------------------------------------------------

; really just to only used when NULLp is disabled

(defthm not-NULLp-tag-REF-not-equal-minus-1
  (implies (not (NULLp (tag-REF v)))
           (not (equal v -1))))


(defthm value-of-tag-REF 
  (equal (value-of (tag-REF v)) v)
  :hints (("Goal" :in-theory (enable value-of tag-REF))))

;----------------------------------------------------------------------



(defthm not-NULLp-tag-REF-not-equal-minus-1-f
  (implies (not (NULLp (tag-REF v)))
           (not (equal v -1)))
  :rule-classes :forward-chaining)



(defthm tag-of-tag-REF
  (equal (tag-of (tag-REF v)) 'REF)
  :hints (("Goal" :in-theory (enable tag-REF tag-of))))

;
; We have value-of, rREF
;

;----------------------------------------------------------------------


(defthm consistent-state-implies-consistent-heap-array-init3
  (implies (consistent-state s)
           (consistent-heap-array-init-state3 (heap s) (heap-init-map (aux
                                                                       s))))
  :hints (("Goal" :in-theory (enable consistent-state
                                     consistent-heap-array-init-state))))

;----------------------------------------------------------------------

(defthm check-null-not-equal-value-of-minus-1
  (implies (not (check-null v))
           (not (equal (value-of v) -1))))

(defthm check-null-not-equal-value-of-minus-1-f
  (implies (not (check-null v))
           (not (equal (value-of v) -1)))
  :rule-classes :forward-chaining)

;----------------------------------------------------------------------


(defthm isArrayType-implies-consistent-array-object
  (implies (and (consistent-state s)
                (not (NULLp v))
                (REFp v (heap s))
                (isArrayType (obj-type (deref2 v (heap s)))))
           (consistent-array-object (deref2 v (heap s))
                                    (heap s) (instance-class-table s)
                                    (array-class-table s)))
  :hints (("Goal" :in-theory (e/d (consistent-state consistent-heap consistent-heap)
                                  (consistent-array-object nullp)))))



(local 
 (defthm consistent-state-ipmlies-consistent-heap2
   (implies (consistent-state s)
            (consistent-heap2 (heap s) (heap s)
                              (instance-class-table s)
                              (array-class-table s) 0))))

;;(i-am-here) ;; Thu Jun 16 19:31:13 2005

(local 
 (defthm consistent-heap2-implies-isArrayType-is-consistent-array-object
   (implies (and (consistent-heap2 hp1 hp cl acl id)
                 (isArrayType (obj-type (binding v hp1))))
            (consistent-array-object (binding v hp1) hp cl acl))
   :hints (("Goal" :in-theory (e/d (binding)
                                   (consistent-array-object))))))

(defthm isArrayType-implies-consistent-array-object-strong
  (implies (and (consistent-state s)
                (isArrayType (obj-type (deref2 v (heap s)))))
           (consistent-array-object (deref2 v (heap s))
                                    (heap s) (instance-class-table s)
                                    (array-class-table s)))
  :hints (("Goal" :in-theory (e/d (deref2  rREF
                                   consistent-heap consistent-heap)
                                  (consistent-array-object
                                   obj-type
                                   isArrayType
                                   binding-rref-normalize
                                   consistent-heap2-implies-isArrayType-is-consistent-array-object
                                   consistent-state
                                   binding
                                   nullp))
           :use ((:instance
                  consistent-heap2-implies-isArrayType-is-consistent-array-object
                  (hp1 (heap s)) 
                  (hp (heap s))
                  (v (cdr v))
                  (cl (instance-class-table s))
                  (acl (array-class-table s))
                  (id 0))))))



;; (defthm isArrayType-implies-consistent-array-object-strong
;;   (implies (and (consistent-state s)
;;                 (isArrayType (obj-type (deref2 v (heap s)))))
;;            (consistent-array-object (deref2 v (heap s))
;;                                     (heap s) (instance-class-table s)
;;                                     (array-class-table s)))
;;   :hints (("Goal" :in-theory (e/d (consistent-state consistent-heap consistent-heap)
;;                                   (consistent-array-object nullp)))))


;----------------------------------------------------------------------

(defthm consistent-state-consistent-heap-init-state3
  (implies (consistent-state s)
           (consistent-heap-array-init-state3 (heap s) (heap-init-map (aux s))))
  :hints (("Goal" :in-theory (enable consistent-heap-array-init-state3
                                     consistent-state))))

;----------------------------------------------------------------------

(defthm consistent-value-tag-REF
   (implies (and (not (primitive-type? (array-component-type type)))
                 (consistent-value (tag x (array-component-type type))
                                   (array-component-type type) cl hp))
            (consistent-value (tag-REF x) (array-component-type type) cl hp))
   :hints (("Goal" :in-theory (enable tag tag-REF))))

;----------------------------------------------------------------------


;; (DEFTHM PUSHSTACK-WFFSTATE
;;   (IMPLIES (WFF-STATE S)
;;            (WFF-STATE (SAFE-PUSHSTACK V S)))
;;   :HINTS
;;   (("Goal" :IN-THEORY (DISABLE CONSISTENT-STATE))))
;;
;; from consistent-state-properties.lisp!! 
;;

;; (i-am-here) ;; Wed May 11 00:31:02 2005

(DEFTHM PUSHSTACK-WFFSTATE-base
  (IMPLIES (WFF-STATE S)
           (WFF-STATE (PUSHSTACK V S)))
  :hints (("Goal" :in-theory (enable pushstack))))


;; Sat May  7 15:13:18 2005 should be easy to fix!! 

(DEFTHM POPSTACK-WFFSTATE-base
  (IMPLIES (WFF-STATE S)
           (WFF-STATE (POPSTACK S)))
  :hints (("Goal" :in-theory (enable popStack))))




(DEFTHM update-trace-WFFSTATE-base
  (IMPLIES (WFF-STATE S)
           (WFF-STATE (update-trace th  S)))
  :hints (("Goal" :in-theory (enable update-trace))))




(DEFTHM state-set-heap-WFFSTATE-base
  (IMPLIES (WFF-STATE S)
           (WFF-STATE (state-set-heap hp  S)))
  :hints (("Goal" :in-theory (enable state-set-heap))))


(in-theory (disable pushstack-wffstate popstack-wffstate))

;----------------------------------------------------------------------

(defthm consistent-state-state-set-pc-pc
  (implies (and (consistent-state s)
                (integerp pc))
            (consistent-state (state-set-pc pc s))))


;----------------------------------------------------------------------

(defthm consistent-value-x-NULL-REF
  (CONSISTENT-VALUE-X '(REF . -1) cl hp)
  :hints (("Goal" :in-theory (enable consistent-value-x consistent-value))))


;----------------------------------------------------------------------

(defthm len-opstack-sig-is-len-stack
  (implies (consistent-opstack stack cl hp)
           (equal (len (opstack-sig stack cl hp hp-init method-ptr))
                  (len stack))))


(in-theory (disable heap-init-map))

;----------------------------------------------------------------------


(defthm consistent-state-implies-consistent-heap-array-init
  (implies (consistent-state s)
           (consistent-heap-array-init-state (heap s)
                                             (instance-class-table s)
                                             (array-class-table s)
                                             (heap-init-map (aux s))))
  :hints (("Goal" :in-theory (e/d (consistent-state) 
                                  (consistent-heap-array-init-state))))
  :rule-classes :forward-chaining)


(defthm consistent-heap-array-init-implies-alistp
  (implies (consistent-state s)
           (alistp (heap-init-map (aux s))))
  :hints (("Goal" :in-theory (e/d (consistent-state) ())))
  :rule-classes :forward-chaining)

;----------------------------------------------------------------------


(defthm not-value-of-v-implies-not-nullp
  (implies (not (equal (value-of v) -1))
           (not (NULLp v)))
  :hints (("Goal" :in-theory (enable value-of NULLp rREF))))


(defthm REFp-not-value-minus-1-implies-consistent-object
  (implies (and (REFp v (heap s))
                (not (equal (value-of v) -1))
                (consistent-state s))
           (consistent-object (deref2 v (heap s))
                              (heap s)
                              (instance-class-table s))))
                                      
;----------------------------------------------------------------------


(defthm consistent-heap-array-init-implies-wff-heap-init-state
  (implies (consistent-state s)
           (wff-heap-init-map (heap-init-map (aux s))))
  :hints (("Goal" :in-theory (e/d (consistent-state) ())))
  :rule-classes :forward-chaining)



(defthm consistent-heap-array-init-implies-wff-heap-init-state-strong
  (implies (consistent-state s)
           (wff-heap-init-map-strong (heap-init-map (aux s))))
  :hints (("Goal" :in-theory (e/d (consistent-state) ())))
  :rule-classes :forward-chaining)

;----------------------------------------------------------------------



;----------------------------------------------------------------------


;; (defthm topStack-guard-strong-implies-wff-tagged-value
;;   (implies (topStack-guard-strong s)
;;            (wff-tagged-value (safe-topStack s)))
;;   :hints (("Goal" :in-theory (enable topStack-guard-strong canPopCategory1
;;                                      category1 safe-topStack))))



(defthm check-array-implies-wff-internal-array
  (implies (CHECK-ARRAY-guard  (RREF v) hp)
           (WFF-INTERNAL-ARRAY (DEREF2 v hp)))
  :hints (("Goal" :in-theory (enable check-array-guard))))

(defthm wff-internal-array-implies-array-bound-integerp
  (implies (wff-internal-array array)
           (integerp (array-bound array)))
  :hints (("Goal" :in-theory (enable wff-internal-array array-bound))))

(defthm check-array-implies-within-bound-1
  (implies (check-array (rREF v) index s)
           (<= 0 index))
  :hints (("Goal" :in-theory (enable check-array)))
  :rule-classes :forward-chaining)


(defthm check-array-implies-within-bound-2
  (implies (check-array (rREF v) index s)
           (< index (array-bound (deref2 v (heap s)))))
  :hints (("Goal" :in-theory (enable check-array)))
  :rule-classes :linear)



;; (defthm topStack-guard-strong-implies-wff-tagged-value
;;   (implies (topStack-guard-strong s)
;;            (wff-tagged-value (safe-topStack s)))
;;   :hints (("Goal" :in-theory (enable topStack-guard-strong canPopCategory1
;;                                      category1 safe-topStack))))


;----------------------------------------------------------------------



(defthm consistent-state-implies-build-a-java-visible-instance-guard
  (implies (consistent-state s)
           (build-a-java-visible-instance-guard "java.lang.Object" s))
  :hints (("Goal" :in-theory (enable consistent-state
                                     build-a-java-visible-instance-guard))))


(defthm consistent-state-implies-build-a-java-visible-instance-guard-java-lang-Class
  (implies (consistent-state s)
           (build-a-java-visible-instance-guard "java.lang.Class" s))
  :hints (("Goal" :in-theory (enable consistent-state
                                     build-a-java-visible-instance-guard))))



(defthm consistent-state-implies-build-a-java-visible-instance-guard-java-lang-String
  (implies (consistent-state s)
           (build-a-java-visible-instance-guard "java.lang.String" s))
  :hints (("Goal" :in-theory (enable consistent-state
                                     build-a-java-visible-instance-guard))))


;----------------------------------------------------------------------


(defthm REF-qual-minus-1-value-equal-minus-1
  (iff (equal (rREF v) -1)
       (equal (value-of v) -1))
  :hints (("Goal" :in-theory (enable rREF value-of))))

;----------------------------------------------------------------------

(in-theory (disable consistent-state array-bound array-data))


;----------------------------------------------------------------------

(defthm consistent-state-consistent-value-x
  (implies (and (consistent-state s)
                (topStack-guard-strong s)
                (equal (instance-class-table s) cl)
                (equal (heap s) hp))
           (consistent-value-x (topStack s) cl hp)))
                
  

(defthm wff-REFp-implies-tag-of-equal-REF
  (implies (wff-REFp v)
           (equal (tag-of v) 'REF)))


(defthm bound?-rREFp
  (implies (and (REFp v hp)
                (not (equal (value-of v) -1)))
           (bound? (rREF v) hp)))



(defthm wff-tagged-value-implied-by-consistent-value-x
  (implies (consistent-value-x (topStack s) (instance-class-table s) (heap s))
           (WFF-TAGGED-VALUE (TOPSTACK s))))


(defthm pc-set-element-at-array
  (equal (pc (set-element-at-array index value array-ref s))
         (pc s)))


; (i-am-here)

(defthm pc-set-element-at
  (equal (pc (mv-nth 1 (set-element-at index value array s)))
         (pc s)))


(defthm consistent-state-state-set-pc
  (implies (and (consistent-state s)
                (integerp pc))
           (consistent-state (state-set-pc pc s)))
  :hints (("Goal" :in-theory (enable consistent-state))))


(defthm integerp-inst-size
  (integerp (inst-size inst)))



(defthm wff-state-implies-integer-pc
  (implies (wff-state s)
           (integerp (pc s)))
  :hints (("Goal" :in-theory (enable pc wff-state)))
  :rule-classes :forward-chaining)



;; (defthm consistent-state-implies-integer-pc
;;   (implies (consistent-state s)
;;            (integerp (pc s)))
;;   :hints (("Goal" :in-theory (enable wff-state consistent-state)))
;;   :rule-classes :forward-chaining)
                 


;----------------------------------------------------------------------

(local 
 (encapsulate ()
  (local (include-book "base-skip-proofs"))
  (defthm isAssignableTo-isAssignableTo-if-class-table-same
     (implies (equal (instance-class-table s2) 
                     (instance-class-table s1))
              (iff (car (isAssignableTo typ1 typ2 s2))
                   (car (isAssignableTo typ1 typ2 s1))))
     :hints (("Goal" :in-theory (enable isAssignableTo))))))

(local 
 (defthm popStack-change-no-cl
   (equal (instance-class-table (popStack s))
          (instance-class-table s))))

;;; consider move this into base??  Wed May 11 00:39:15 2005

(defthm isAssignableTo-isAssignableTo-popStack
  (iff (car (isAssignableTo typ1 typ2 (popstack s)))
       (car (isAssignableTo typ1 typ2 s)))
  :hints (("Goal" :use ((:instance
                         isAssignableTo-isAssignableTo-if-class-table-same
                         (s2 (popstack s))
                         (s1 s))))))

       
;----------------------------------------------------------------------

  

(defthm wff-REFp-implies-tag-of-equal-REF
  (implies (wff-REFp v)
           (equal (tag-of v) 'REF)))


(defthm bound?-rREFp
  (implies (and (REFp v hp)
                (not (equal (value-of v) -1)))
           (bound? (rREF v) hp)))



;----------------------------------------------------------------------

(defthm bcv-isAssignable-fact-null
  (BCV::ISASSIGNABLE 'NULL 'NULL ENV))

;; (defthm locals-not-change-pushStack
;;   (implies (consistent-state s)
;;            (equal (LOCALS (CURRENT-FRAME (PUSHSTACK V S)))
;;                   (locals (current-frame s)))))


;----------------------------------------------------------------------

(local 
 (defthm consistent-frame-integerp-max-local
   (implies (and (consistent-frame frame cl hp)
                 (not (mem '*native* 
                           (method-accessflags 
                            (deref-method (method-ptr frame) cl)))))
            (integerp (method-maxlocals (deref-method 
                                         (method-ptr frame) cl))))))

(in-theory (disable method-maxlocals))

(defthm consistent-state-integerp-max-local
  (implies (and (consistent-state s)
                (not (mem '*native* 
                          (method-accessflags 
                           (current-method s)))))
           (integerp (method-maxlocals (current-method s))))
  :hints (("Goal" :in-theory (e/d (current-method) (method-maxlocals 
                                                    current-method-normalization)))))


(defthm consistent-state-integerp-max-local-f
  (implies (and (consistent-state s)
                (not (mem '*native* 
                          (method-accessflags 
                           (current-method s)))))
           (integerp (method-maxlocals (current-method s))))
  :hints (("Goal" :in-theory (e/d (current-method) (method-maxlocals 
                                                    current-method-normalization))))
  :rule-classes :forward-chaining)

;----------------------------------------------------------------------


;; (i-am-here) ;;; Wed May 18 13:01:48 2005

(local 
 (defthm nth-index-cons
   (implies (and (integerp index)
                 (>= index 1))
            (equal (nth index (cons x l))
                   (nth (+ -1 index) l)))))


(local (defthm two-minus-is-minus-two
         (equal (+ -1 -1 index)
                (+ -2 index))))

(local (defthm nth-minus-2-cddr-n
         (implies (and (integerp index)
                       (>= index 2))
                  (equal (nth index (cons any1 (cons any2 locals)))
                         (nth (+ -2 index) locals)))))
                                    

(include-book "base-locals")

;; (i-am-here) ;; Sat May 21 18:53:19 2005 
;; need to be fixed 

;;(skip-proofs 
(local (defthm consistent-locals-consistent-value-x-if-at-valid-index
         (implies (and (consistent-locals locals cl hp)
                       (integerp index)
                       (valid-local-index index locals))
                  (consistent-value-x (nth index locals) cl hp))
         :hints (("Goal" :in-theory (e/d () (consistent-value-x category2Loc
                                                                category1loc))
                  :do-not '(generalize)))))

;;; We need to modify the consistent-locals to assert types exists!
  

(defthm local-at-is-consistent-value-x
   (implies (and (consistent-state s)
                 (valid-local-index i (locals (current-frame s)))
                (integerp i)
                (<= 0 i)
                (< i (len (locals (current-frame s)))))
           (consistent-value-x (local-at i s)
                               (instance-class-table s)
                               (heap s)))
  :hints (("Goal" :in-theory (e/d (local-at) 
                                  (consistent-value-x locals consistent-locals)))))



(defthm REFp-implies-category1
  (implies (REFp v hp)
           (category1 v))
  :hints (("Goal" :in-theory (enable tag-of WFF-REFp REFp valid-REFp category1)))
  :rule-classes :forward-chaining)


;; (defthm REFp-implies-category1-b
;;   (implies (REFp v hp)
;;            (category1 v))
;;   :hints (("Goal" :in-theory (enable tag-of WFF-REFp REFp valid-REFp category1))))


;----------------------------------------------------------------------


(defthm int32p-implies-rationalp
  (implies (INT32p (value-of v))
           (rationalp (value-of v)))
  :hints (("Goal" :in-theory (enable INT32p))))

;----------------------------------------------------------------------



(defthm topstack-guard-strong-implies-consp-opstack
  (implies (topstack-guard-strong s)
           (consp (operand-stack (current-frame s))))
  :hints (("Goal" :in-theory (enable topstack-guard-strong))))

;; it appears that we want export this. 
;; necessary for execute-ANEWARRY guard verification. 


(defthm consistent-state-popstack-consistent-state-normalized
  (implies (and (topstack-guard-strong s)
                (consistent-state s))
           (consistent-state (popstack s))))


;;;
;;; originally we only have consistent-state-safe-popStack... 
;----------------------------------------------------------------------



(defthm consistent-state-popstack-consistent-state-normalized
  (implies (and (topstack-guard-strong s)
                (consistent-state s))
           (consistent-state (popstack s))))





;----------------------------------------------------------------------



(defthm consistent-state-pc-integerp
  (implies (consistent-state s)
           (integerp (pc s))))




(defthm consistent-state-acl2-numberp
  (implies (consistent-state s)
           (acl2-numberp (pc s))))



;----------------------------------------------------------------------



(defthm wff-call-frame-current-frame
  (implies (consistent-state s)
           (wff-call-frame (current-frame s))))


;;; need to for guard verification of ANEWARRAY!! 


;----------------------------------------------------------------------

(defthm consistent-state-wff-state
  (implies (consistent-state s)
           (wff-state s)))

;;; these are not very good rules!! 
;;; We may want more specific rules
;;; so that ACL2 does not do unecessary backchaining!! 
;;; But so far let it be. 
;;; Note it can slow down proofs and distract the proof. 
;;;
;;;
;;; Let me see if this affect a lot proofs.  we will move it into
;;; guard-verification.lisp!!

;; (i-am-here) ;; 

(defthm topstack-guard-strong-topStack-guard
  (implies (topstack-guard-strong s)
           (topstack-guard s))
  :hints (("Goal" :in-theory (enable topstack-guard-strong))))



(defthm consistent-state-wff-heap
  (implies (consistent-state s)
           (wff-heap (heap s))))



(defthm consistent-state-wff-thread-table
  (implies (consistent-state s)
           (wff-thread-table (thread-table s))))


(defthm acl2-numberp-pc
  (implies (consistent-state s)
           (integerp (pc s))))


(defthm inst-size-integerp
  (integerp (inst-size anyinst)))


;----------------------------------------------------------------------



(encapsulate () 
  (local 
   (defthm REFp-not-NULLp-consistent-object
     (implies (and (consistent-state s)
                   (REFp v (heap s))
                   (not (NULLp v))
                   (equal (instance-class-table s) cl))
              (consistent-object (deref2 v (heap s))
                                 (heap s)
                                 cl))))
                              

   (local (defthm REFp-check-NULL-not-NULLp
            (implies (and (REFp v hp)
                          (not (check-NULL v)))
                     (not (NULLp v)))))

 (defthm REFp-not-NULLp-consistent-object-alternative
   (implies (and (consistent-state s)
                 (REFp v (heap s))
                 (not (check-NULL v))
                 (equal (instance-class-table s) cl))
            (consistent-object (deref2 v (heap s))
                               (heap s)
                               cl))))


;----------------------------------------------------------------------


(defthm can-load-array-class-in-consistent-state
  (implies (CONSISTENT-STATE S)
           (JVM::LOAD_ARRAY_CLASS_GUARD S))
  :hints (("Goal" :in-theory (enable consistent-state
                                     jvm::load_array_class_guard))))


(defthm can-load-class-in-consistent-state
  (implies (CONSISTENT-STATE S)
           (JVM::LOAD_CLASS-GUARD S))
  :hints (("Goal" :in-theory (enable consistent-state
                                     jvm::load_class-guard))))

                              

;----------------------------------------------------------------------
(local 
 (defthm bound?-bind-any-hp
   (bound? any (bind any obj hp))
   :hints (("Goal" :in-theory (enable bound? bind)))))


(defthm consistent-value-x-fact
  (consistent-value-x (tag-ref (len hp)) cl (bind (len hp) any
                                                  hp))
  :hints (("Goal" :in-theory (enable 
                              tag-ref consistent-value-x 
                              wff-REFp tag-of
                              rREF value-of 
                              wff-tagged-value))))



(defthm category1-tag-ref-len
  (category1 (tag-ref (len any)))
  :hints (("Goal" :in-theory (enable tag-ref category1 tag-of 
                                     wff-tagged-value value-of))))


(in-theory (enable max-stack))

;----------------------------------------------------------------------


(defthm consistent-state-implies-method-max-stack-integerp
  (implies (and (consistent-state s)
                (not (mem '*native* (method-accessflags (current-method s)))))
           (integerp (METHOD-MAXSTACK (CURRENT-METHOD S))))
  :hints (("Goal" :in-theory (e/d (method-maxstack) 
                                  (consistent-state 
                                   code-max-stack
                                   consistent-code))))
     :rule-classes :forward-chaining)

;----------------------------------------------------------------------

;; (i-am-here) ;;; Sat Jun 18 00:55:05 2005


(local 
 (defthm
   class-hierachy-consistent1-class-n-implies-not-java-lang-Object-super-bounded
   (implies 
    (and (class-hierachy-consistent1-class-n name cl)
         (not (equal name "java.lang.Object")))
    (isClassTerm (class-by-name (super (class-by-name name cl))
                                       cl)))
   :hints (("Goal" :in-theory (e/d (class-exists? class-loaded?) (isClassTerm))))))

(local 
 (defthm
   class-hierachy-consistent1-aux-implies-bounded-class-hierachy-consistent1-class-n
   (implies (and (class-hierachy-consistent1-aux cl1 cl)
                 (isClassTerm (class-by-name name cl1)))
            (class-hierachy-consistent1-class-n name cl))))

(local 
 (defthm consistent-state-implies-class-hierachy-consistent1-aux
   (implies (consistent-state s)
            (class-hierachy-consistent1-aux (instance-class-table s)
                                            (instance-class-table s)))
   :hints (("Goal" :in-theory (enable consistent-state consistent-class-hierachy)))))



(defthm consistent-state-implies-not-equal-java-lang-Object-super-bounded
  (implies (and (consistent-state s)
                (not (equal name "java.lang.Object"))
                (isClassTerm (class-by-name name (instance-class-table s))))
           (isClassTerm (class-by-name (super (class-by-name name
                                                             (instance-class-table s)))
                                       (instance-class-table s))))
  :hints (("Goal" :in-theory (e/d (consistent-class-hierachy)
                                  (class-hierachy-consistent1-class-n
                                   consistent-state
                                   isClassTerm))
           :use ((:instance
                  class-hierachy-consistent1-aux-implies-bounded-class-hierachy-consistent1-class-n
                  (cl1 (instance-class-table s))
                  (cl (instance-class-table s)))))))


;----------------------------------------------------------------------

(defthm not-type-size2
    (implies (REFp v hp)
             (not (equal (type-size (tag-of v)) 2)))
    :rule-classes :forward-chaining)


;----------------------------------------------------------------------

(skip-proofs 
 (defthm consistent-state-implies-local-size-ok
   (implies (consistent-state s)
            (<=  (len (locals (current-frame s)))
                 (max-local s)))
   :rule-classes :linear))


(skip-proofs 
 (defthm consistent-state-nth-local-wff-tagged-value
   (implies (and (consistent-state s)
                 (<= 0 i)
                 (< i (len (locals (current-frame s)))))
            (wff-tagged-value (nth i (locals (current-frame s)))))))

;; this is proved somewhere!! 

;----------------------------------------------------------------------

(local 
 (defthm equal-minus-one-minus-one-plus-negative-two
   (equal (+ -1 -1 i)
          (+ -2 i))))

(local 
 (defthm nth-i-specific
   (implies (and (< 0 i)
                 (integerp i))
            (equal (nth (- i 1) (cdr locals))
                   (nth i locals)))))


(local 
 (defthm nth-i-specific-2
   (implies (and (< 1 i)
                 (integerp i))
            (equal (nth (- i 2) (cddr locals))
                   (nth i locals)))
   :hints (("Goal" 
            :in-theory (disable nth-i-specific)
            :use ((:instance nth-i-specific
                             (i (- i 1))
                             (locals (cdr locals)))
                  (:instance nth-i-specific))
            :do-not-induct t))))



(defthm valid-local-index-implies-not-topx
  (implies (and (valid-local-index i locals)
                (integerp i)
                (<= 0 i)
                (< i (len locals)))
           (not (equal (tag-of (nth i locals)) 'topx)))
  :hints (("Goal" :do-not '(generalize)
           :induct (valid-local-index i locals))
          ("Subgoal *1/6.5" :cases ((< 1 i)))
          ("Subgoal *1/6.1" :cases ((< 1 i)))))

