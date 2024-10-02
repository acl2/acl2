(in-package "DJVM")
(include-book "../DJVM/consistent-state")
(include-book "../DJVM/djvm-frame-manipulation-primitives")

(acl2::set-match-free-default :all)

(defthm consistent-thread-entry-implies-consistent-opstack
  (implies (consistent-thread-entry th cl hp)
           (consistent-opstack 
            (operand-stack (top (thread-call-stack th))) cl hp))
  :rule-classes :forward-chaining)


(defthm consistent-opstack-consistent-value-x
  (implies (and (consistent-opstack opstack cl hp)
                (canPopCategory1 opstack))
           (consistent-value-x (top opstack) cl hp))
  :rule-classes :forward-chaining)



(defthm topStack-guard-implies-canPopCategory
  (implies (topStack-guard-strong s)
           (canPopCategory1 
            (operand-stack 
             (top (thread-call-stack 
                   (thread-by-id (current-thread s)
                                 (thread-table s)))))))
  :rule-classes :forward-chaining)

;; Doesn't hurt 
;;
(defthm consistent-state-implies-consistent-thread-entry-b
  (implies (consistent-thread-entry th cl hp)
           (consistent-opstack 
            (operand-stack (top (thread-call-stack th))) cl hp)))


(defthm consistent-opstack-consistent-value-x-b
  (implies (and (consistent-opstack opstack cl hp)
                (canPopCategory1 opstack))
           (consistent-value-x (top opstack) cl hp)))
                                      

(defthm topStack-guard-implies-canPopCategory-b
  (implies (topStack-guard-strong s)
           (canPopCategory1 
            (operand-stack 
             (top (thread-call-stack 
                   (thread-by-id (current-thread s)
                                 (thread-table s))))))))


(defthm consistent-state-topstack-consistent-value-x
  (implies (and (topStack-guard-strong s)
                (consistent-state s))
           (consistent-value-x (safe-topStack s) 
                               (instance-class-table s)
                               (heap s)))
  :hints (("Goal" :in-theory (disable consistent-value-x 
                                      consistent-state
                                      topStack-guard-strong
                                      canPopCategory1
                                      operand-stack
                                      thread-call-stack
                                      top
                                      current-thread
                                      instance-class-table
                                      heap
                                      thread-table)))
  :rule-classes :forward-chaining)




(defthm consistent-value-x-implies-wff-tagged-value
  (implies (consistent-value-x v cl hp)
           (wff-tagged-value v))
  :rule-classes :forward-chaining)


(defthm pc-pushStack-unchanged
  (equal (pc (pushStack v s))
         (pc s)))

;;; may have proved it in ADD1-program-correct proof! 
;;; Fri Jan 16 01:34:38 2004. does not matter if .... 


(defthm pc-safe-pushStack-unchanged
  (equal (pc (safe-pushStack v s))
         (pc s)))


(defthm pc-popStack-unchanged
  (equal (pc (popStack s))
         (pc s)))

(defthm pc-safe-popStack-unchanged
  (equal (pc (safe-popStack s))
         (pc s)))

(in-theory (enable wff-state pc))

;; (defthm wff-state-implies-pc-numberp
;;   (implies (wff-state s)
;;            (integerp (pc s)))
;;   :rule-classes :forward-chaining)


;; Mon May 17 16:43:16 2004

;;(i-am-here)

(defthm current-thread-pushStack-unchange
  (equal (current-thread (pushStack v s))
         (current-thread s)))

(defthm current-thread-popStack-unchange
  (equal (current-thread (popStack s))
         (current-thread s)))

;; Mon May 17 16:54:46 2004. If proof breaks. These above is to blame. 
;; Mon May 17 16:55:04 2004


(defthm consistent-state-implies-thread-id-thread-by-id
  (implies (consistent-state s)
           (equal (thread-id (thread-by-id (current-thread s)
                                           (thread-table s)))
                  (current-thread s))))


(defthm thread-by-id-replace-entry
  (implies (and (equal (thread-id new-thread) (thread-id old-thread))
                (wff-thread old-thread)
                (wff-thread new-thread)
                (equal (thread-by-id (thread-id old-thread) ths)
                       old-thread)
                (wff-thread-table ths))
           (equal (thread-by-id x 
                    (replace-thread-table-entry old-thread new-thread ths))
                 (if (equal (thread-id old-thread) x)
                     new-thread
                   (thread-by-id x ths))))
  :hints (("Goal" :do-not '(generalize))))




(defthm consistent-thread-entries-consistent-thread-entries
  (implies (and (consistent-thread-entry new-thread cl hp)
                (consistent-thread-entries ths cl hp))
           (consistent-thread-entries (replace-thread-table-entry 
                                        old new-thread ths)
                                      cl hp))
  :hints (("Goal" :in-theory (disable consistent-thread-entry))))



;; (i-am-here) 
;; Sun Aug  8 16:01:24 2004
;; failed after the update to the consistent-state.

;;
;; need some properties about changing thread-table does not affect class-table
;;
;; The following three are added/ 

(defthm  build-a-java-visible-instance-data-guard-independent-of-thread-table
  (implies (wff-state s)
           (equal (build-a-java-visible-instance-data-guard
                   any (state-set-thread-table anytt s))
                  (build-a-java-visible-instance-data-guard any s)))
  :hints (("Goal" :in-theory (enable build-a-java-visible-instance-data-guard
                                     state-set-thread-table))))

(defthm wff-state-state-set-thread-table
  (implies (wff-state s)
           (wff-state (state-set-thread-table anytt s)))
  :hints (("Goal" :in-theory (enable state-set-thread-table))))


(defthm build-a-java-visible-instance-guard-independent-of-thread-table
  (implies (wff-state s)
           (equal (build-a-java-visible-instance-guard
                   any (state-set-thread-table anytt s))
                  (build-a-java-visible-instance-guard any s)))
  :hints (("Goal" :in-theory (e/d (build-a-java-visible-instance-guard)
                                  (wff-state)))))


(defthm class-table-equal-implies-equal-correctly-loaded
  (equal (jvm::array-class-correctly-loaded? l (state-set-thread-table anytt s1))
         (jvm::array-class-correctly-loaded? l s1))
  :hints (("Goal" :in-theory (enable array-class-table class-loaded? 
                                     array-base-type
                                     instance-class-table)
           :do-not '(generalize))))


;; loops easily.
;; Sun Aug  8 16:39:14 2004
;;

;; (defthm class-table-equal-implies-equal
;;    (implies (and (equal (class-table s2) (class-table s1)))
;;             (equal (jvm::array-class-table-inv-helper l s2)
;;                    (jvm::array-class-table-inv-helper l s1)))
;;    :rule-classes nil)


(defthm class-table-equal-implies-equal
  (equal (jvm::array-class-table-inv-helper l (state-set-thread-table anytt s1))
         (jvm::array-class-table-inv-helper l s1)))

(defthm class-loaded-implies-equal
  (equal (class-loaded? any (state-set-thread-table anytt s1))
         (class-loaded? any s1))
  :hints (("Goal" :in-theory (enable instance-class-table 
                                     class-loaded?))))


(defthm loader-inv-independent-of-state-set-thread-table
  (implies (wff-state s1)
           (equal (jvm::loader-inv (state-set-thread-table anytt s1))
                  (jvm::loader-inv s1)))
  :hints (("Goal" :in-theory (enable instance-class-table jvm::loader-inv))))



;; (i-am-here) ;; Thu Feb 10 14:07:45 2005 ;; added the assertion that
;; unique thread-ids of the thread table!! 

(defthm thread-id-no-change-replace-thread-entry
  (implies (equal (thread-id y) (thread-id x))
           (equal (collect-thread-id (replace-thread-table-entry x y tt))
                  (collect-thread-id tt))))


(defthm consistent-state-set-thread-table-consistent-state
  (implies (and (consistent-state s)
                (wff-thread old-thread)
                (wff-thread new-thread)
                (equal (thread-by-id (thread-id old-thread) (thread-table s))
                       old-thread)
                (equal (thread-id new-thread) (thread-id old-thread))
                (consistent-thread-entry new-thread (instance-class-table s) (heap s)))
           (consistent-state 
              (state-set-thread-table 
                (replace-thread-table-entry old-thread new-thread (thread-table s))
                s)))
  :hints (("Goal" :in-theory (disable consistent-thread-entry wff-state thread-id thread-by-id))))


(in-theory (enable thread-set-call-stack thread-call-stack))

;; (i-am-here)

(in-theory (disable consistent-adjacent-frame)) ;; Sun Mar 20 06:29:17 2005
;; new addition 

(in-theory (disable resume-pc))

(defthm consistent-thread-entry-set-call-stack
  (implies (and (consistent-call-stack cs cl hp)
                (consistent-call-stack-linkage cs cl)
                (consistent-thread-entry th cl hp)
                (consp cs))
           (consistent-thread-entry (thread-set-call-stack cs th) cl hp)))

(defthm push-consistent-frame-implies-consistent-call-stack
  (implies (and (consistent-frame frame cl hp)
                (consistent-call-stack call-stack cl hp))
           (consistent-call-stack (push frame call-stack) cl hp)))

;;; Mon Mar 21 10:41:35 2005. 
;;; 


(defthm consistent-adjacent-frame-if-return-pc-method-ptr-equal
  (implies (and (consistent-adjacent-frame caller callee cl)
                (equal (return-pc modified-callee)
                       (return-pc callee))
                (equal (method-ptr modified-callee)
                       (method-ptr callee)))
           (consistent-adjacent-frame caller modified-callee cl))
  :hints (("Goal" :in-theory (enable consistent-adjacent-frame))))



(defthm consistent-linkage-linkage-lemma
  (implies (and (consistent-call-stack-linkage call-stack cl)
                (equal (return-pc frame)
                       (return-pc (top call-stack)))
                (equal (method-ptr frame)
                       (method-ptr (top call-stack)))
                (wff-invocation-frame frame cl))
           (consistent-call-stack-linkage (push frame (pop call-stack)) cl)))


(defthm wff-invocation-frame-frame-set-opstack
  (implies (and (wff-invocation-frame frame cl)
                (<= (LEN OPSTACK)
                    (method-maxstack (deref-method (method-ptr frame) cl)))
                (true-listp opstack))
           (wff-invocation-frame (frame-set-operand-stack opstack frame) cl))
  :hints (("Goal" :in-theory (e/d (wff-call-frame operand-stack) ())
           :do-not-induct t)))

(defthm return-pc-frame-set-operand-stack
  (equal (return-pc (frame-set-operand-stack opstack frame))
         (return-pc frame)))


(defthm return-pc-frame-set-locals
  (equal (return-pc (frame-set-locals locals frame))
         (return-pc frame)))



(defthm method-ptr-frame-set-locals
  (equal (method-ptr (frame-set-locals locals frame))
         (method-ptr frame)))


(defthm method-ptr-frame-set-operand-stack
  (equal (method-ptr (frame-set-operand-stack opstack frame))
         (method-ptr frame)))



(in-theory (enable frame-set-operand-stack))


(local (in-theory (enable wff-call-frame make-frame wff-call-stack operand-stack locals sync-obj-ref return-pc method-ptr)))
;; (local (in-theory (disable frame-set-operand-stack)))
;(i-am-here)

;; (defthm wff-call-frame-make-frame
;;   (implies (valid-sync-obj
;;    (wff-call-frame (make-frame 
;;                     RETURN-PC 
;;                     OPERANT-STACK LOCALS
;;                     METHOD-PTR 
;;                     SYNC-OBJ-REF 
;;                     RESUME-PC)))
;; 
;; ;; (i-am-here)                   

(defthm consistent-opstack-truelistp
  (implies (consistent-opstack opstack cl hp)
           (true-listp opstack))
  :rule-classes :forward-chaining)

(defthm set-opstack-consistent-frame-consistent-frame
  (implies (and (consistent-opstack opstack cl hp)
                (<= (len opstack) (method-maxstack (deref-method (method-ptr frame) cl)))
                (consistent-frame frame cl hp))
           (consistent-frame (frame-set-operand-stack opstack frame) cl hp))
  :hints (("Goal" :do-not-induct t)))

;; Mon May 17 14:20:20 2004. Add extra assertion about OPSTACK size 

(defthm len-pop-opstack-is
  (implies (canPopCategory1 opstack)
           (equal (len (pop opstack))
                  (- (len opstack) 1))))





;; (defthm len-pop-opstack-less-than
;;   (<= (len (pop opstack)) (len opstack)))


(defthm consistent-opstack-pop-consistent-opstack
  (implies (and (canPopCategory1 opstack)
                (consistent-opstack opstack cl hp))
           (consistent-opstack (pop opstack) cl hp)))

(defthm consistent-opstack-push-consistent-opstack
  (implies (and (consistent-value-x v cl hp)
                (consistent-opstack opstack cl hp)
                (Category1 v))
           (consistent-opstack (push v opstack) cl hp)))


(defthm consistent-opstack-push-consistent-opstack
  (implies (and (consistent-value-x v cl hp)
                (consistent-opstack opstack cl hp)
                (Category1 v))
           (consistent-opstack (push v opstack) cl hp)))


(defthm consistent-opstack-pop2-consistent-opstack
  (implies (and (canPopCategory2 opstack)
                (consistent-opstack opstack cl hp))
           (consistent-opstack (pop (pop opstack)) cl hp)))

(defthm consistent-call-stack-consistent-call-stack
  (implies (consistent-call-stack cs cl hp)
           (consistent-call-stack (cdr cs) cl hp)))

(defthm consisntent-frame-implied-by-consistent-call-stack
  (implies (and (consistent-call-stack cs cl hp)
                (consp cs))
           (consistent-frame (top cs) cl hp)))

(defthm consisntent-call-stack-implied-by-consistent-call-stack
  (implies (consistent-call-stack cs cl hp)
           (consistent-call-stack (pop cs) cl hp)))


; (i-am-here) ;;  Sun Oct 17 16:46:27 2004

;; quite some problems. 

(defthm consistent-frame-implies-len-opstack-less-max-stack
  (implies (and (consistent-frame frame cl hp)
                ;;; Sun Oct 17 16:48:08 2004
                (not (mem '*native* (method-accessflags 
                                     (deref-method (method-ptr frame) cl)))))
           (<= (len (operand-stack frame))
               (METHOD-MAXSTACK (DEREF-METHOD (METHOD-PTR FRAME) CL))))
  :rule-classes :linear)


;; (defthm consistent-frame-implies-len-opstack-less-max-stack
;;   (implies (consistent-frame frame cl hp)
;;            (<= (len (operand-stack frame))
;;                (METHOD-MAXSTACK (DEREF-METHOD (METHOD-PTR FRAME) CL))))
;;   :rule-classes :linear)


(defthm consistent-frame-implies-len-opstack-less-max-stack-rewrite
  (implies (and (consistent-frame frame cl hp)
                (not (mem '*native* (method-accessflags 
                                     (deref-method (method-ptr frame) cl)))))
           (<= (len (operand-stack frame))
               (METHOD-MAXSTACK (DEREF-METHOD (METHOD-PTR FRAME) CL)))))


;; free variable problem!! 

(defthm consistent-frame-implies-len-opstack-less-max-stack-forward
  (implies (and (consistent-frame frame cl hp)
                (not (mem '*native* (method-accessflags 
                                     (deref-method (method-ptr frame) cl)))))
           (<= (len (operand-stack frame))
               (METHOD-MAXSTACK (DEREF-METHOD (METHOD-PTR FRAME) CL))))
  :rule-classes :forward-chaining)



(defthm consistent-thread-entry-consistent-frame
  (implies (consistent-thread-entry th cl hp)
           (consistent-frame (top (thread-call-stack th))
                             cl hp))
  :hints (("Goal" :in-theory (e/d () (consistent-frame)))))


;; (defthm consistent-
;;   (implies (consistent-thread-entry th cl hp)
;;            (consistent-frame (top (thread-call-stack th))
;;                              cl hp))
;;   :hints (("Goal" :in-theory (e/d () (consistent-frame)))))

(defthm consistent-state-consistent-thread-entry
  (implies (consistent-state s)
           (consistent-thread-entry (thread-by-id (current-thread s)
                                                  (thread-table s))
                                    (instance-class-table s)
                                    (heap s)))
  :hints (("Goal" :in-theory (e/d (current-frame) (consistent-thread-entry)))))

(local (in-theory (disable top thread-call-stack operand-stack)))


(defthm consistent-state-consistent-frame
  (implies (consistent-state s)
           (consistent-frame (current-frame s)
                             (instance-class-table s)
                             (heap s)))
  :hints (("Goal" :in-theory (e/d (current-frame) (consistent-frame
                                                   consistent-state)))))

(defthm consistent-state-consistent-frame-forward
  (implies (consistent-state s)
           (consistent-frame (current-frame s)
                             (instance-class-table s)
                             (heap s)))
  :hints (("Goal" :in-theory (e/d (current-frame) (consistent-frame
                                                   consistent-state))))
  :rule-classes :forward-chaining)


(local
 (defthm current-frame-normalize
   (equal (TOP (THREAD-CALL-STACK (THREAD-BY-ID (CURRENT-THREAD S)
                                                (THREAD-TABLE S))))
          (current-frame s))))



(defthm consistent-state-implies-len-opstack-less-max-stack-rewrite
  (implies (and (consistent-state s)
                (not (mem '*native* (method-accessflags 
                                     (deref-method (method-ptr (current-frame
                                                                s))
                                                   (instance-class-table s))))))
           (<= (len (operand-stack (current-frame s)))
               (max-stack s)))
  :hints (("Goal" :in-theory (e/d () (current-frame method-ptr method-maxstack 
                                                    consistent-state)))))


;; (skip-proofs 
;;  (defthm consistent-state-implies-len-opstack-less-max-stack
;;    (implies (consistent-state s)
;;             (<= (len (operand-stack (current-frame s)))
;;                 (max-stack s)))))

(defthm consistent-state-implies-len-opstack-less-max-stack-linear
  (implies (and (consistent-state s)
                (not (mem '*native* 
                          (method-accessflags 
                           (deref-method (method-ptr (current-frame s))
                                         (instance-class-table s))))))
           (<= (len (operand-stack (current-frame s)))
               (max-stack s)))
  :hints (("Goal" :in-theory (disable current-frame max-stack operand-stack consistent-state)))
  :rule-classes :linear)

(local (in-theory (disable current-frame-normalize)))

(defthm consistent-state-implies-len-opstack-less-max-stack-specific
   (implies (and (consistent-state s)
                (not (mem '*native* 
                          (method-accessflags 
                           (deref-method (method-ptr (current-frame s))
                                         (instance-class-table s))))))
            (<= (len (operand-stack (top (thread-call-stack (thread-by-id
                                                             (current-thread s)
                                                             (thread-table s))))))

                (METHOD-MAXSTACK
                 (DEREF-METHOD
                  (METHOD-PTR (TOP (THREAD-CALL-STACK (THREAD-BY-ID (CURRENT-THREAD S)
                                                                    (THREAD-TABLE S)))))
                  (INSTANCE-CLASS-TABLE S)))))
   :hints (("Goal" :use
            consistent-state-implies-len-opstack-less-max-stack-rewrite
            :in-theory (disable consistent-state)))
   :rule-classes :linear)

;;;
;;; ??  Sun Oct 17 12:01:08 2004. 
;;; 

;;; (i-am-here)

(in-theory (disable wff-call-frame wff-method-decl 
                    method-accessflags consistent-adjacent-frame
                    wff-method-ptr))

(skip-proofs 
 (defthm consistent-state-implies-consistent-call-linkage
   (implies (consistent-state s)
            (consistent-call-stack-linkage 
             (thread-call-stack (thread-by-id (current-thread s) 
                                              (thread-table s)))
             (instance-class-table s)))))

(skip-proofs 
 (defthm consistent-state-implies-wff-invocation-frame
   (implies (consistent-state s)
            (WFF-INVOCATION-FRAME
             (TOP (THREAD-CALL-STACK (THREAD-BY-ID (CURRENT-THREAD S)
                                                   (THREAD-TABLE S))))
             (INSTANCE-CLASS-TABLE S)))))

(in-theory (disable wff-invocation-frame))

(defthm true-listp-pop
  (implies (true-listp list)
           (TRUE-LISTP (pop list))))

(defthm true-listp-push
  (implies (true-listp list)
           (TRUE-LISTP (push v list))))


(defthm consistent-state-popStack-consistent-state
   (implies (and (topStack-guard-strong s)
                 (consistent-state s))
            (consistent-state (safe-popStack s)))
   :hints (("Goal" :in-theory (disable
                                       state-set-thread-table
                                       consistent-state
                                       consistent-opstack-consistent-value-x-b
                                       consistent-thread-entry
                                       wff-thread
                                       wff-state
                                       thread-call-stack
                                       instance-class-table
                                       heap
                                       top
                                       pop
                                       current-frame
                                       method-ptr
                                       method-maxstack
                                       operand-stack
                                       canPopCategory1
                                       frame-set-operand-stack
                                       thread-set-call-stack
                                       current-thread
                                       thread-table
                                       push
                                       consistent-frame))))



(defthm len-push-v-is
  (equal (len (push v l))
         (+ (len l) 1)))

;(i-am-here)

;; (defthm len-add-minus
;;   (implies (and (< (len l) x)
;;                 (integerp x))
;;            (<= (len (push v l)) x)))

;; (len (operand-stack (top (thread-call-stack
;;                                                     (thread-by-id
;;                                                      (current-thread s) 
;;                                                      (thread-table s)))))))


(defthm consistent-state-pushStack-consistent-state
   (implies (and (consistent-value-x v (instance-class-table s) (heap s))
                 (Category1 v)
                 (<= (+ 1 (len (operand-stack (current-frame s))))
                     (max-stack s))
                 (consistent-state s))
            (consistent-state (safe-pushStack v s)))
   :hints (("Goal" 
            :use consistent-state-implies-len-opstack-less-max-stack-specific
            :in-theory (disable state-set-thread-table
                                       consistent-state
                                       consistent-opstack-consistent-value-x-b
                                       consistent-thread-entry
                                       wff-thread
                                       wff-state
                                       thread-call-stack
                                       instance-class-table
                                       heap
                                       top
                                       pop
                                       method-maxstack
                                       ;; current-frame
                                       method-ptr
                                       operand-stack
                                       canPopCategory1
                                       frame-set-operand-stack
                                       thread-set-call-stack
                                       current-thread
                                       thread-table
                                       push
                                       consistent-frame))))




(defthm array-object-consistent1-and-nth 
  (implies (and (array-obj-consistent1 data-array component-type hp cl)
                (<= 0 index)
                (< index (len data-array)))
           (consistent-value (tag (nth index data-array)
                                  component-type)
                             component-type cl hp))
  :hints (("Goal" :in-theory (disable consistent-value tag)
           :do-not '(generalize))))

(defthm consistent-array-obj-implies-array
  (implies (consistent-array-object array-obj hp cl acl)
           (array-obj-consistent1 (array-data array-obj) (array-component-type
                                                          (obj-type array-obj))
                                  hp cl))
  :rule-classes :forward-chaining)

;; (acl2::set-match-free-error nil)

(defthm consistent-value-element-at-consistent-array
  (implies (and (consistent-array-object array hp cl acl)
                (<= 0 index)
                (<  index (array-bound array)))
           (consistent-value 
                (tag (element-at index array) (array-component-type (obj-type array)))
                (array-component-type (obj-type array))
                cl hp))
  :hints (("Goal" :in-theory (disable consistent-value tag
                                      array-bound array-data
                                      primitive-type? obj-type
                                      array-component-type))))


(defthm consistent-value-implies-consistent-value-x
  (implies (consistent-value v type cl hp)
           (consistent-value-x v cl hp))
  :rule-classes :forward-chaining)


(defthm consistent-value-implies-consistent-value-x-b
  (implies (consistent-value v type cl hp)
           (consistent-value-x v cl hp)))


(in-theory (enable state-set-thread-table make-state))

;; (defthm wff-state-state-set-thread-table
;;   (implies (wff-state s)
;;            (wff-state (state-set-thread-table tt s))))

(in-theory (disable  state-set-thread-table wff-state))

;; (defthm wff-state-state-set-thread-table
;;   (implies (wff-state s)
;;            (wff-state (state-set-thread-table any s)))
;;   :hints (("Goal" :in-theory (enable wff-state state-set-thread-table))))

(defthm pushStack-wffstate
  (implies (wff-state s)
           (wff-state (safe-pushStack v s)))
  :hints (("Goal" :in-theory (disable consistent-state))))

(defthm popStack-wffstate
  (implies (wff-state s)
           (wff-state (safe-popStack s)))
  :hints (("Goal" :in-theory (disable consistent-state))))

(in-theory (enable state-set-thread-table wff-state))


;; (defthm pushStack-wffstate-f
;;   (implies (wff-state s)
;;            (wff-state (safe-pushStack v s)))
;;   :rule-classes :forward-chaining)


;; (defthm popStack-wffstate-f
;;   (implies (wff-state s)
;;            (wff-state (safe-popStack s)))
;;   :rule-classes :forward-chaining)


(defthm consistent-state-implies-wff-state
  (implies (consistent-state s)
           (wff-state s))
  :rule-classes :forward-chaining)

(defthm consistent-state-implies-wff-heap
  (implies (consistent-state s)
           (wff-heap (heap s)))
  :rule-classes :forward-chaining)


(defthm consistent-value-x-and-tag-REF-implies-valid-refp
  (implies (and (not (equal (value-of tagged-value) -1))
                (consistent-value-x tagged-value cl hp)
                (equal (tag-of tagged-value) 'REF))
           (Valid-REFp tagged-value hp))
  :rule-classes :forward-chaining)

;; Be careful about selection of trigger term.

;; the problem here is that binding for cl and hp if we want to use forward
;; chaining. We need to start from (consistent-state s) to get the fact that
;; certain slot are Valid-REFp

(defthm Valid-REFp-Deref2-in-wff-heap-strong-wff-object
  (implies (and (Valid-REFp ref hp)
                (wff-heap-strong hp))
           (wff-obj-strong (deref2 ref hp)))
  :rule-classes :forward-chaining)

;; Forward chaining rule rules!!

;; give stronger guidance


;; (defthm thread-set-call-stack-consistent-thread-entry
;;   (implies (and (consistent-call-stack cs cl hp)
;;                 (consistent-call-stack-linkage cs cl)
;;                 (consp cs)
;;                 (consistent-thread-entry th cl hp))
;;            (consistent-thread-entry (thread-set-call-stack cs th) cl hp))
;;   :hints (("Goal" :in-theory (enable thread-set-call-stack thread-call-stack 
;;                                      wff-thread))))

;;; this seems to be proved before. as: consistent-thread-entry-set-call-stack

(defthm consistent-call-stack-push-new-frame
  (implies (and (consistent-frame frame cl hp)
                (consistent-call-stack cs cl hp))
           (consistent-call-stack (cons frame cs) cl hp)))


(in-theory (disable make-state))

(defthm popStack-heap-unchanged
  (equal (heap (popStack s))
         (heap s)))


(defthm pushStack-heap-unchanged
  (equal (heap (pushStack v s))
         (heap s)))



(defthm safe-popStack-heap-unchanged
  (equal (heap (safe-popStack s))
         (heap s))
  :hints (("Goal" :in-theory (disable consistent-state))))

(defthm safe-pushStack-heap-unchanged
  (equal (heap (safe-pushStack v s))
         (heap s))
  :hints (("Goal" :in-theory (disable consistent-state))))


(in-theory (enable instance-class-table))

(defthm popStack-instance-class-table-unchanged
  (equal (instance-class-table (popStack s))
         (instance-class-table s)))

(defthm pushStack-instance-class-table-unchanged
  (equal (instance-class-table (pushStack v s))
         (instance-class-table s)))


(defthm instance-class-table-no-change-safe-pushCategory2
  (equal (INSTANCE-CLASS-TABLE
          (SAFE-PUSHCATEGORY2 v s))
         (instance-class-table s))
  :hints (("Goal" :in-theory (e/d (safe-pushcategory2)
                                  (pushStack instance-class-table)))))


(defthm safe-popStack-instance-class-table-unchanged
  (equal (instance-class-table (safe-popStack s))
         (instance-class-table s))
  :hints (("Goal" :in-theory (disable consistent-state))))



(defthm safe-pushStack-instance-class-table-unchanged
  (equal (instance-class-table (safe-pushStack v s))
         (instance-class-table s))
  :hints (("Goal" :in-theory (disable consistent-state))))



(in-theory (disable instance-class-table))



(defthm consistent-state-secondStack-consistent-value-x
  (implies (and (secondStack-guard-strong s)
                (consistent-state s))
           (consistent-value-x (safe-secondStack s) 
                               (instance-class-table s)
                               (heap s)))
  :hints (("Goal" :in-theory (disable consistent-value-x safe-popStack safe-topStack consistent-state)
           :use ((:instance consistent-state-topstack-consistent-value-x
                            (s (safe-popStack s))))))
  :rule-classes :forward-chaining)


(defthm consistent-state-implies-wff-heap-strong
  (implies (consistent-state s)
           (wff-heap-strong (heap s)))
  :hints (("Goal" :in-theory (enable consistent-state)))
  :rule-classes :forward-chaining)




;; question, what's the problem with Forward chaining

(defthm consistent-state-implies-wff-class-table
  (implies (consistent-state s)
           (wff-class-table (class-table s)))
  :hints (("Goal" :in-theory (enable consistent-state)))
  :rule-classes :forward-chaining)


(defthm consistent-state-implies-wff-instance-class-table
  (implies (consistent-state s)
           (wff-instance-class-table (instance-class-table s)))
  :hints (("Goal" :in-theory (enable consistent-state)))
  :rule-classes :forward-chaining)


;; (in-theory (disable deref2 consistent-state heap tag-of value-of))


;; >V d          (DEFUN MAKE-STATE
;;                      (JVM::IP JVM::CUR JVM::JAVAHEAP
;;                               THREAD-TABLE JVM::INTERNAL-CLASS-TABLE
;;                               ENV ERROR-FLAG AUX)
;;                      (LIST 'STATE
;;                            JVM::IP
;;                            JVM::CUR (CONS 'HEAP JVM::JAVAHEAP)
;;                            (CONS 'THREAD-TABLE THREAD-TABLE)
;;                            JVM::INTERNAL-CLASS-TABLE
;;                            ENV ERROR-FLAG AUX))

;; (defthm wff-state-state-set-pc
;;   (implies (integerp pc)
;;            (wff-state (make-state pc cid hp tt cl env ef aux)))
;;   :hints (("Goal" :in-theory (e/d (make-state wff-state)))))

;;; moved to jvm-object-manipulation-primitives.lisp Wed Mar 31 13:08:45 2004

;(i-am-here)
(defthm state-set-pc-loader-inv
  (implies (and (wff-state s)
                (integerp pc))
           (equal (jvm::loader-inv (state-set-pc pc s))
                  (jvm::loader-inv s)))
  :hints (("Goal" :in-theory (enable jvm::loader-inv))))


;; (defthm state-set-pc-loader-inv-alternative
;;   (implies (and (wff-state s)
;;                 (integerp pc))
;;            (equal (jvm::loader-inv (state-set-pc pc s))
;;                   (jvm::loader-inv s)))
;;   :hints (("Goal" :in-theory (enable jvm::loader-inv))))


(defthm state-set-pc-wff-state
  (implies (and (wff-state s)
                (integerp pc))
           (wff-state (state-set-pc pc s))))

(defthm state-set-pc-class-loaded?
  (equal (class-loaded? any (state-set-pc pc s))
         (class-loaded? any s))
  :hints (("Goal" :in-theory (enable class-loaded? instance-class-table))))

;(i-am-here)

(defthm state-set-pc-load_class-guard
  (implies (and (wff-state s)
                (integerp pc))
           (equal (jvm::load_class-guard (state-set-pc pc s))
                  (jvm::load_class-guard s)))
  :hints (("Goal" :in-theory (disable state-set-pc))))

(defthm array-class-table-equal-after-state-set-pc
  (equal (array-class-table (state-set-pc pc s))
         (array-class-table s)))

(defthm state-set-pc-build-a-java-instance-data-guard
  (implies (and (wff-state s)
                (integerp pc))
           (equal (build-a-java-visible-instance-data-guard any (state-set-pc pc s))
                  (build-a-java-visible-instance-data-guard any s))))



(defthm state-set-pc-build-a-java-instance-guard
  (implies (and (wff-state s)
                (integerp pc))
           (equal (build-a-java-visible-instance-guard any (state-set-pc pc s))
                  (build-a-java-visible-instance-guard any s)))
  :hints (("Goal" :in-theory (e/d (build-a-java-visible-instance-guard)
                                  (state-set-pc)))))
                                  


(defthm state-set-pc-array-class-correctly-loaded?
  (implies (and (wff-state s)
                (integerp pc))
           (equal (jvm::array-class-correctly-loaded? l (state-set-pc pc s))
                  (jvm::array-class-correctly-loaded? l s)))
  :hints (("Goal" :in-theory (e/d (array-base-type)
                                  (state-set-pc)))))
  


(defthm state-set-pc-array-class-table-inv-helper
  (implies (and (wff-state s)
                (integerp pc))
           (equal (jvm::array-class-table-inv-helper l (state-set-pc pc s))
                  (jvm::array-class-table-inv-helper l s)))
  :hints (("Goal" :in-theory (disable state-set-pc))))


(defthm state-set-pc-load_array_class_guard
  (implies (and (wff-state s)
                (integerp pc))
           (equal (jvm::load_array_class_guard (state-set-pc pc s))
                  (jvm::load_array_class_guard s)))
  :hints (("Goal" :in-theory (disable state-set-pc))))



;; (defthm state-set-pc-build-instance-guard
;;   (implies (and (wff-state s)
;;                 (integerp pc))
;;            (equal (jvm::loader-inv (state-set-pc pc s))
;;                   (jvm::loader-inv s)))
;;   :hints (("Goal" :in-theory (enable jvm::loader-inv))))

  

(local (in-theory (disable state-set-pc wff-state instance-class-table 
                           class-table
                           array-class-table)))


(defthm state-set-pc-consistent-state
  (implies (and (consistent-state s)
                (integerp pc))
           (consistent-state (state-set-pc pc s)))
  :hints (("Goal" :in-theory (e/d (consistent-state)
                                  (CONSISTENT-THREAD-TABLE
                                   jvm::load_array_class_guard
                                   consistent-class-table
                                   jvm::load_class-guard
                                   consistent-heap
                                   )))))

;;state-set-pc 
                                     ;;jvm::loader-inv))))
                                     ;array-class-table instance-class-table
                                     ;heap))))



(defthm consistent-state-implies-pc-numberp
  (implies  (consistent-state s)
            (integerp (pc s)))
  :rule-classes :forward-chaining)

;; (defthm consistent-value-implies-consistent-value-x-b-instance
;;   (let ((v (tag (ELEMENT-AT (VALUE-OF (TOPSTACK S))
;;                             (deref2 (SECONDSTACK S) (heap s)))
;;                  (array-component-type (obj-type (deref2 (secondstack s) (heap s))))))
;;         (type (array-component-type (obj-type (deref2 (secondStack s) (heap s)))))
;;         (cl (instance-class-table s))
;;         (hp (heap s)))
;;     (implies (consistent-value v type cl hp)
;;              (consistent-value-x v cl hp))))
;;
;; moved to djvm-bytecode.lisp
;;


(defthm tag-ref-tag
    (implies (not (primitive-type? type))
           (equal (tag-ref v)
                  (tag v type)))
    :hints (("Goal" :in-theory (enable tag-ref tag))))


;; (defthm consistent-value-implies-consistent-value-x-b-instance-real
;;   (let ((v1 (tag (ELEMENT-AT (VALUE-OF (TOPSTACK S))
;;                             (deref2 (SECONDSTACK S) (heap s)))
;;                  (array-component-type (obj-type (deref2 (secondstack s) (heap
;;                                                                           s))))))
;;         (v2 (tag-ref (ELEMENT-AT (VALUE-OF (TOPSTACK S))
;;                             (deref2 (SECONDSTACK S) (heap s)))))
;;         (type (array-component-type (obj-type (deref2 (secondStack s) (heap s)))))
;;         (cl (instance-class-table s))
;;         (hp (heap s)))
;;     (implies (and (consistent-value v1 type cl hp)
;;                   (not (primitive-type? type)))
;;              (consistent-value-x v2 cl hp))))

;; (in-theory (disable consistent-value-implies-consistent-value-x-b-instance
;;                     tag-ref-tag))




(defthm tag-ref-category1
  (implies (wff-tagged-value (tag-ref v))
           (category1 (tag-ref v)))
  :hints (("Goal" :in-theory (enable category1 tag-ref tag-of 
                                     wff-tagged-value))))


(defthm consistent-value-x-implies-wff-tagged-value-b
  (implies (consistent-value-x v cl hp)
           (wff-tagged-value v)))


(defthm wff-internal-array-implies-array-type
  (implies (wff-internal-array array)
           (isArrayType (obj-type array)))
  :hints (("Goal" :in-theory (enable wff-internal-array
                                     obj-type)))
  :rule-classes :forward-chaining)

;;(i-am-here) ;; Tue Jul 12 20:16:11 2005

(in-theory (disable consistent-array-object))

(defthm consistent-heap2-isArrayType-consistent-array-object
  (implies (and (mem xobj hp1)
                (isArrayType (obj-type (cdr xobj)))
                (consistent-heap2 hp1 hp cl acl id))
           (consistent-array-object (cdr xobj)
                                    hp cl acl)))



(defthm assoc-mem
  (implies (assoc-equal x l)
           (mem (assoc-equal x l) l)))



(defthm array-type-s-implies-isArrayType
  (implies (array-type-s type cl)
           (isArrayType type))
  :rule-classes :forward-chaining)


(in-theory (disable isArrayType))



(in-theory (disable consistent-state safe-popStack topStack-guard-strong pc
                    wff-obj wff-obj-strong safe-pushStack safe-topStack wff-state)) ;; wff-internal-array))


;---------------------------------------------------------------------

(defthm consistent-heap1-deref2-f
  (implies (and (consistent-heap1 hp1 hp cl id)
                (deref2 v hp1))
           (consistent-object (deref2 v hp1) hp cl))
  :hints (("Goal" :in-theory (disable consistent-object)))
  :rule-classes :forward-chaining)


(defthm consistent-heap1-deref2
  (implies (and (consistent-heap1 hp1 hp cl id)
                (deref2 v hp1))
           (consistent-object (deref2 v hp1) hp cl))
  :hints (("Goal" :in-theory (disable consistent-object))))


(defthm consistent-heap-deref2-f
  (implies (and (consistent-heap hp cl acl)
                (deref2 v hp))
           (consistent-object (deref2 v hp) hp cl))
  :hints (("Goal" :in-theory (disable consistent-object deref2)))
  :rule-classes :forward-chaining)


(defthm consistent-heap-deref2
  (implies (and (consistent-heap hp cl acl)
                (deref2 v hp))
           (consistent-object (deref2 v hp) hp cl))
  :hints (("Goal" :in-theory (disable consistent-object deref2))))

;---------------------------------------------------------------------

(defthm consistent-thread-entry-implies-consp-call-stack
  (implies (consistent-thread-entry thread cl hp)
           (consp (thread-call-stack thread)))
  :rule-classes :forward-chaining)

;; (acl2::set-match-free-error nil)

(defthm consistent-thread-entry-implies-consp-call-stack-b
  (implies (consistent-thread-entry thread cl hp)
           (consp (thread-call-stack thread))))


(defthm consistent-thread-entry-implies-consp-call-stack-b-specific
  (implies (consistent-thread-entry (thread-by-id id (thread-table s))
                                    (instance-class-table s) (heap s))
           (consp (thread-call-stack (thread-by-id id (thread-table s))))))



(defthm consistent-call-stack-implies-car-consistent-call-frame
  (implies (and (consistent-call-stack cs cl hp)
                (consp cs))
           (consistent-frame (car cs) cl hp))
  :rule-classes :forward-chaining)


(defthm consistent-call-stack-implies-car-consistent-call-frame-b
  (implies (and (consistent-call-stack cs cl hp)
                (consp cs))
           (consistent-frame (car cs) cl hp)))


;----------------------------------------------------------------------

(in-theory (disable thread-table thread-set-call-stack current-thread
                    frame-set-operand-stack thread-table thread-id
                    operand-stack thread-call-stack wff-thread))


(in-theory (enable thread-by-id))

(defthm replace-thread-table-entry-thread-by-id-1
  (implies (and (equal (thread-id new-thread) id2)
                (thread-by-id id2 thread-table)
                (wff-thread-table thread-table)
                (not (equal id1 id2)))
           (equal (thread-by-id id1 (replace-thread-table-entry
                                     (thread-by-id id2 thread-table)
                                     new-thread
                                     thread-table))
                  (thread-by-id id1 thread-table))))

(defthm replace-thread-table-entry-thread-by-id-2
       (implies (and (equal (thread-id new-thread) id2)
                     (thread-by-id id2 thread-table)
                     (wff-thread-table thread-table)                     
                     (equal id1 id2))
                (equal (thread-by-id id1 (replace-thread-table-entry
                                          (thread-by-id id2 thread-table)
                                          new-thread
                                          thread-table))
                       new-thread)))


(defthm consistent-state-implies-thread-by-id-exists
  (implies (consistent-state s)
           (thread-by-id (current-thread s) (thread-table s)))
  :hints (("Goal" :in-theory (enable consistent-state)))
  :rule-classes :forward-chaining)


(defthm thread-call-stack-thread-set-call-stack
  (equal (thread-call-stack (thread-set-call-stack cs thread))
         cs)
  :hints (("Goal" :in-theory (enable thread-call-stack thread-set-call-stack))))





(defthm topFrame-normalization 
  ;; should be named to current-frame
  (equal (top (thread-call-stack (thread-by-id 
                                  (current-thread s)
                                  (thread-table s))))
         (current-frame s)))

           
(defthm consistent-state-implies-consistent-frame
   (implies (consistent-state s)
            (consistent-frame (current-frame s)
                              (instance-class-table s)
                              (heap s)))
   :hints (("Goal" :in-theory (e/d (consistent-state consistent-thread-entry current-frame)
                                   (consistent-frame topFrame-normalization))
            :expand ((current-frame s))))
   :rule-classes :forward-chaining)


(in-theory (disable thread-by-id))

;; (in-theory (enable thread-table thread-set-call-stack current-thread
;;                     frame-set-operand-stack thread-table thread-id
;;                     operand-stack thread-call-stack wff-thread))



(defthm consistent-state-implies-consistent-class-decls
  (implies (consistent-state s)
           (consistent-class-decls (instance-class-table s)
                                   (instance-class-table s)
                                   (heap s)))
  :hints (("Goal" :in-theory (e/d (consistent-state consistent-class-table)
                                  (consistent-class-decls))))
  :rule-classes :forward-chaining)



;;----------------------------------------------------------------------
;;
;; (defthm consistent-state-implies-consistent-frame
;;    (implies (consistent-state s)
;;             (consistent-frame (top-frame s)
;;                               (instance-class-table s)
;;                               (heap s)))
;;    :hints (("Goal" :in-theory (e/d (consistent-state consistent-thread-entry top-frame)
;;                                    (consistent-frame topframe-normalization))
;;             :expand ((top-frame s))))
;;    :rule-classes :forward-chaining)
;;
;; this should be easy too.
;;

;; ;;; moved to consistent-state-properties.lisp Mon Feb 23 22:23:17 2004


;; (defthm consistent-frame-implies-consistent-opstack
;;    (implies (consistent-frame frame cl hp)
;;             (consistent-opstack (operand-stack frame) cl hp))
;;    :rule-classes :forward-chaining)


;; (defthm consistent-opstack-implies-canPop-implies-consistent-value
;;   (implies (and (consistent-opstack opstack cl hp)
;;                 (canPopCategory1 opstack))
;;            (consistent-value-x (car opstack) cl hp))
;;   :rule-classes :forward-chaining)


;----------------------------------------------------------------------


(defthm consistent-frame-implies-wff-call-frame-f
  (implies (consistent-frame frame cl hp)
           (wff-call-frame frame))
  :rule-classes :forward-chaining)


(defthm consistent-state-consistent-frame-f
  (implies (consistent-state s)
           (consistent-frame (current-frame s)
                             (instance-class-table s)
                             (heap s)))
  :rule-classes :forward-chaining)


;; (defthm consistent-state-consistent-thread-entry
;;   (implies (consistent-state s)
;;            (consistent-thread-entry 
;;             (thread-by-id (current-thread s)
;;                           (thread-table s))
;;             (instance-class-table s)
;;             (heap s)))
;;   :rule-classes :forward-chaining)


;; (defthm consistent-thread-entry-implies-consistent-call-stack
;;   (implies (consistent-thread-entry thread cl hp)
;;            (consistent-call-stack (thread-call-stack thread) cl hp))
;;   :rule-classes :forward-chaining)
;;;
;;; proved in djvm-frame-manipulation-primitives.lisp
;;;

(defthm consp-len-no-less-than-0
  (implies (consp l)
           (<= 1 (len l)))
  :rule-classes :linear)


(defthm consistent-thread-entry-implies-wff-call-stack
  (implies (consistent-thread-entry th cl hp)
           (wff-call-stack (thread-call-stack th)))
  :rule-classes :forward-chaining)

;(i-am-here)

(local
 (defthm consistent-method-decl-search-method
   (implies (and (searchMethod method-ptr methods)
                 (consistent-method-decls methods))
            (consistent-method-decl (searchMethod method-ptr methods)))))

(local 
 (defthm consistent-class-decl-consistent-class-decls
   (implies (and (class-by-name name cls)
                 (consistent-class-decls cls cl hp))
            (consistent-class-decl (class-by-name name cls) cl hp))
   :hints (("Goal" :in-theory (disable consistent-class-decl)))))


(local 
 (defthm consistent-class-decl-consistent-class-decls-f
   (implies (and (class-by-name name cls)
                 (consistent-class-decls cls cl hp))
            (consistent-class-decl (class-by-name name cls) cl hp))
   :hints (("Goal" :in-theory (disable consistent-class-decl)))
   :rule-classes :forward-chaining))



(local
 (defthm consistent-method-decls-if-consistent-class-decl
   (implies (consistent-class-decl class cl hp)
            (consistent-method-decls (methods class)))))


(local
 (defthm consistent-method-decls-if-consistent-class-decl-f
   (implies (consistent-class-decl class cl hp)
            (consistent-method-decls (methods class)))
   :rule-classes :forward-chaining))


(defthm valid-method-ptr-consistent-class-decls-consistent-method
  (implies (and (valid-method-ptr method-ptr cl)
                (consistent-class-decls cl anyCl hp))
           (consistent-method-decl (deref-method method-ptr cl)))
  :hints (("Goal" :in-theory (e/d (deref-method) 
                                  (consistent-method-decl 
                                   consistent-class-decl
                                   methods))))
  :rule-classes :forward-chaining)


;; (skip-proofs
;;  (defthm valid-method-ptr-consistent-class-decls-consistent-method
;;    (implies (and (valid-method-ptr method-ptr cl)
;;                  (consistent-class-decls cl anyCl hp))
;;             (consistent-method-decl (deref-method method-ptr cl))))
;;  :rule-classes :forward-chaining)

                                  
;; Mon Mar 29 23:46:34 2004 TODO.

(defthm valid-method-ptr-implied-by-consistent-frame
  (implies (consistent-frame frame cl hp)
           (valid-method-ptr (method-ptr frame) cl))
  :rule-classes :forward-chaining)


;; (defthm consistent-state-implies-consistent-method-decl
;;   (implies (consistent-state s)
;;            (consistent-method-decl 
;;             (deref-method (method-ptr (current-frame s)) (instance-class-table s))))
;;   :hints (("Goal" :in-theory (e/d () (consistent-method-decl method-ptr
;;                                      consistent-frame valid-method-ptr)))))



; (i-am-here)
;
;; Sun Oct 17 12:33:02 2004

;(i-am-here)

(defthm consp-implies-len
  (implies (consp x)
           (<= 1 (len x)))
  :rule-classes :linear)

;; (defthm consistent-thread-entry-implies-call-stack-len
;;   (implies (consistent-thread-entry th cl hp)
;;            (<= 1 (LEN (THREAD-CALL-STACK th)))))

(defthm consistent-state-current-frame-guard
  (implies (consistent-state s)
           (current-frame-guard s))
  :hints (("Goal" :in-theory (e/d () ())))
  :rule-classes :forward-chaining)



;; (skip-proofs 
;;  (defthm consistent-state-current-frame-guard
;;    (implies (consistent-state s)
;;             (current-frame-guard s))
;;    :rule-classes :forward-chaining))


(defthm wff-call-frame-implies-wff-method-ptr
  (implies (wff-call-frame frame)
           (wff-method-ptr (method-ptr frame)))
  :hints (("Goal" :in-theory (enable wff-call-frame method-ptr)))
  :rule-classes :forward-chaining)

;;; Mon Apr 18 15:45:53 2005
;;; Why we want this current-method definiton here? 
;;; We can only define it after consistent-state is defined! 
;;;

(defun current-method (s)
  (declare (xargs :guard (consistent-state s)))
  (deref-method (method-ptr (current-frame s)) (instance-class-table s)))

(defthm consistent-state-implies-consistent-method-decl
  (implies (consistent-state s)
           (consistent-method-decl 
            (current-method s)))
  :hints (("Goal" :in-theory (e/d (current-method) (consistent-method-decl method-ptr
                                     consistent-frame valid-method-ptr))))
  :rule-classes :forward-chaining)

(defthm current-method-normalization
  (equal (deref-method (method-ptr (current-frame s))
                       (instance-class-table s))
         (current-method s))
  :hints (("Goal" :in-theory (enable current-method))))


(defthm consistent-method-decl-implies-wff-method-decl
  (implies (consistent-method-decl method)
           (wff-method-decl method))
  :rule-classes :forward-chaining)
  
(defthm wff-method-decl-implies-method-accessflags
  (implies (wff-method-decl method)
           (true-listp (method-accessflags method)))
  :hints (("Goal" :in-theory (enable wff-method-decl method-accessflags)))
  :rule-classes :forward-chaining)

(defthm consistent-method-decl-implies-consistent-code-if-not-native-abstract
  (implies (and (consistent-method-decl method)
                (not (mem '*abstract* (method-accessflags method)))
                (not (mem '*native* (method-accessflags method))))
           (consistent-code (method-code method)))
  :hints (("Goal" :in-theory (disable consistent-code method-accessflags)))
  :rule-classes :forward-chaining)

(defthm consistent-code-wff-code
  (implies (consistent-code code)
           (wff-code code))
  :rule-classes :forward-chaining)

(defthm consistent-code-integerp-max-stack
  (implies (consistent-code code)
           (integerp (code-max-Stack code)))
  :rule-classes :forward-chaining)

(defthm consistent-code-integerp-max-local
   (implies (consistent-code code)
            (integerp (code-max-local code)))
   :rule-classes :forward-chaining)

;----------------------------------------------------------------------

(defthm consistent-frame-implies-consistent-opstack
   (implies (consistent-frame frame cl hp)
            (consistent-opstack (operand-stack frame) cl hp))
   :rule-classes :forward-chaining)

(defthm consistent-frame-implies-consistent-locals
   (implies (consistent-frame frame cl hp)
            (consistent-locals (locals frame) cl hp))
   :rule-classes :forward-chaining)

;(i-am-here)  ;; Mon Oct 18 07:25:57 2004

(defthm consistent-opstack-implies-canPop-implies-consistent-value
  (implies (and (consistent-opstack opstack cl hp)
                (canPopCategory1 opstack))
           (consistent-value-x (car opstack) cl hp))
  :hints (("Goal" :in-theory (e/d (top) (consistent-value-x))))
  :rule-classes :forward-chaining)


;----------------------------------------------------------------------


(defthm consistent-state-implies-consistent-heap-init-state-forward
   (implies (consistent-state s)
            (consistent-heap-array-init-state
                              (heap s) (instance-class-table s)
                              (array-class-table s)
                              (heap-init-map (aux s))))
   :hints (("Goal" :in-theory (disable consistent-state CONSISTENT-HEAP-ARRAY-INIT-STATE)
            :expand ((consistent-state s))))
   :rule-classes :forward-chaining)



(defthm consistent-state-implies-consistent-heap-init-state-backward
   (implies (consistent-state s)
            (consistent-heap-array-init-state
                              (heap s) (instance-class-table s)
                              (array-class-table s)
                              (heap-init-map (aux s)))))


;----------------------------------------------------------------------

;; (acl2::i-am-here)

;(i-am-here) ; Sun Oct 17 14:41:19 2004

(local (in-theory (disable method-ptr wff-call-stack wff-method-decl
                           wff-method-ptr wff-code method-ptr
                           method-accessflags
                           wff-call-frame method-code method-maxstack)))

;; Sun Oct 17 14:51:34 2004
;; Note: this is caught by the guard verification

(defthm consistent-method-decl-implies-consistent-code
  (implies (and (consistent-method-decl method)
                (not (mem '*abstract* (method-accessflags method)))
                (not (mem '*native* (method-accessflags method))))
           (consistent-code (method-code method)))
  :hints (("Goal" :in-theory (enable method-code))))

;; (defthm consistent-method-decl-implies-consistent-code
;;   (implies (consistent-method-decl method)
;;            (consistent-code (method-code method)))
;;   :hints (("Goal" :in-theory (enable method-code)))
;;   :rule-classes :forward-chaining)
;;
;; This is not true. using consistent-state definition of today.  I need to
;; assert that the current method is not an abstract or *native*
;; 
;;

(defthm consistent-code-wff-code-b
  (implies (consistent-code code)
           (wff-code code))
  :hints (("Goal" :in-theory (enable consistent-code))))


(defthm consistent-code-integerp-max-stack-b
  (implies (consistent-code code)
           (integerp (code-max-stack code)))
  :hints (("Goal" :in-theory (enable consistent-code))))


(defthm consistent-frame-implies-not-mem-abstract
  (implies (consistent-frame frame cl hp)
           (not (mem '*abstract* 
                     (method-accessflags 
                      (deref-method (method-ptr frame) cl))))))

(defthm consistent-frame-implies-not-mem-abstract-f
  (implies (consistent-frame frame cl hp)
           (not (mem '*abstract* 
                     (method-accessflags 
                      (deref-method (method-ptr frame) cl)))))
  :rule-classes :forward-chaining)



;; (defthm consistent-state-consistent-frame-f
;;   (implies (consistent-state s)
;;            (consistent-frame (current-frame s)
;;                              (instance-class-table s)
;;                              (heap s)))
;;   :rule-classes :forward-chaining)
;;; this should use 


(defthm consistent-state-implies-not-mem-native
  (implies (consistent-state s)
           (not (mem '*abstract* (method-accessflags (current-method s)))))
  :hints (("Goal" :in-theory (disable consistent-state consistent-frame)
           :use ((:instance consistent-frame-implies-not-mem-abstract-f
                            (frame (current-frame s))
                            (cl (instance-class-table s))
                            (hp (heap s)))))))


(defthm consistent-state-implies-max-stack-guard-true
  (implies (and (consistent-state s)
                (not (mem '*native* (method-accessflags 
                                     (current-method s)))))
           (max-stack-guard s))
  :hints (("Goal" :in-theory (e/d () (consistent-state 
                                      consistent-code))))
  :rule-classes :forward-chaining)

;; (skip-proofs 
;;  (defthm consistent-state-implies-max-stack-guard-true
;;    (implies (consistent-state s)
;;             (max-stack-guard s))
;;    :rule-classes :forward-chaining))



(defthm consistent-state-implies-max-stack-integerp
  (implies (and (consistent-state s)
                (not (mem '*native* (method-accessflags (current-method s)))))
           (integerp (max-stack s)))
  :hints (("Goal" :in-theory (e/d (method-maxstack) 
                                  (consistent-state 
                                   code-max-stack
                                   consistent-code))))
   :rule-classes :forward-chaining)

;;; these above is not true. Sun May 16 20:48:11 2004 we need to fix the
;;; consistent-state to assert stronger well-formed-ness on the class-table. 
;;;
;;; TO DO!! Sun May 16 20:48:41 2004
;;;
;;; Mon May 17 11:43:36 2004. The above should be true now.  

(verify-guards safe-pushStack
               :hints (("Goal" :in-theory (disable max-stack-guard
                                                   consistent-state))))

;; ======================================================================
;; 
;; Fri Oct 29 16:55:46 2004


;;; Tue Jun  7 13:28:04 2005
;;(i-am-here)

;;(i-am-here)


  ;;; Tue Jun  7 14:42:28 2005 Hack to get safe-pushCategory2 guard verified!! 
(local 
 (encapsulate ()
    (defthm current-frame-pushStack-is
      (implies (consistent-state s)
               (equal (current-frame (pushStack v s))
                      (frame-set-operand-stack (push v (operand-stack (current-frame s)))
                                               (current-frame s))))
      :hints (("Goal" :in-theory (e/d (current-frame pushStack top
                                                     push-Stack-of-thread
                                                     frame-set-operand-stack)
                                      (topframe-normalization)))))
              


    (defthm wff-call-frame-frame-set-operand-stack-x
      (implies (wff-call-frame frame)
               (wff-call-frame (frame-set-operand-stack (push v (operand-stack
                                                                 frame)) 
                                                        frame)))
      :hints (("Goal" :in-theory (enable wff-call-frame frame-set-operand-stack
                                         operand-stack locals method-ptr
                                         make-frame return-pc wff-method-ptr))))



    (defthm top-push-is
      (equal (top (push frame cs)) frame)
      :hints (("Goal" :in-theory (enable top))))

    (in-theory (disable push top))

    (defthm thread-table-pushStack-is
      (equal (thread-table (pushStack v s))
             (replace-thread-table-entry (thread-by-id (current-thread s)
                                                       (thread-table s))
                                         (push-stack-of-thread 
                                             v (thread-by-id (current-thread s)
                                                             (thread-table s)))
                                         (thread-table s)))
      :hints (("Goal" :in-theory (e/d (pushStack) ())))) 
                                         

    (defthm thread-call-stack-push-stack-of-thread-is
      (equal (THREAD-CALL-STACK  (PUSH-STACK-OF-THREAD v thread))
             (push (frame-set-operand-stack (push v (operand-stack (top
                                                                    (thread-call-stack thread))))
                                            (top (thread-call-stack thread)))
                   (pop (thread-call-stack thread))))
      :hints (("Goal" :in-theory (e/d (push-stack-of-thread) ()))))


    (defthm wff-call-stack-push-frame
      (wff-call-stack (push frame cs))
      :hints (("Goal" :in-theory (enable wff-call-stack push))))))



(verify-guards safe-pushCategory2
               :hints (("Goal" :in-theory (disable consistent-state method-ptr
                                                   method-code))))

;;Tue Jun  7 13:28:06 2005


;----------------------------------------------------------------------



(defthm consistent-state-good-scl
  (IMPLIES (CONSISTENT-STATE S)
           (bcv::good-scl (bcv::scl-jvm2bcv (env-class-table (env s)))))
  :hints (("Goal" :in-theory (e/d (consistent-state) (bcv::good-scl))))
  :rule-classes :forward-chaining)

(defthm consistent-scl-implies-not-super-java-lang-Object-bounded
  (implies (bcv::good-scl scl)
           (NOT
             (BCV::ISCLASSTERM
              (BCV::CLASS-BY-NAME
               (BCV::CLASSSUPERCLASSNAME
                (BCV::CLASS-BY-NAME "java.lang.Object" scl))
               scl))))
  :rule-classes :forward-chaining)

(defthm consistent-scl-implies-not-nil-bounded
  (implies (bcv::good-scl scl)
           (NOT
            (BCV::ISCLASSTERM
             (BCV::CLASS-BY-NAME  nil  scl))))
  :rule-classes :forward-chaining)

;;----------------------------------------------------------------------
;;
;; Thu Jul 21 22:33:17 2005

(skip-proofs 
 (defthm consistent-state-implies-not-bound-hp-init-fact-1
   (implies (consistent-state s)
            (not (bound? nil (heap-init-map (aux s)))))))


(skip-proofs 
 (defthm consistent-state-implies-not-bound-hp-init-fact-2
   (implies (consistent-state s)
            (not (bound? -1 (heap-init-map (aux s)))))))


;; need some efforts. 
;;
;;----------------------------------------------------------------------

