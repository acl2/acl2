(in-package "DJVM")

(include-book "../../DJVM/consistent-state")
(include-book "../../DJVM/consistent-state-properties")

(local 
 (defthm thread-by-id-cons-x
   (EQUAL (THREAD-BY-ID (THREAD-ID NEW-THREAD)
                        (CONS NEW-THREAD TT2))
          NEW-THREAD)
   :hints (("Goal" :in-theory (enable thread-by-id)))))

(local 
 (defthm replace-thread-table-entry-not-mem-equal
   (implies (not (mem oldthread tt))
            (equal (thread-by-id any (replace-thread-table-entry oldthread
                                                                 newthread tt))
                   (thread-by-id any tt)))
   :hints (("Goal" :do-not '(generalize)
            :in-theory (enable thread-by-id)))))


(local 
 (defthm thread-by-id-replace-thread-table-entry-any-any
   (implies (equal (thread-id new-thread) id)
            (equal (thread-by-id id 
                                 (replace-thread-table-entry 
                                  (thread-by-id id tt)
                                  new-thread
                                  tt))
                   (if (mem  (thread-by-id id tt) tt)
                       new-thread
                     (thread-by-id id tt))))
   :hints (("Goal" :do-not '(generalize)
            :in-theory (enable thread-by-id)))))


(local 
 (defthm thread-id-make-thread
   (equal (thread-id (make-thread ID PC CALL-STACK S
                         M-REF MDEPTH THREAD-REF))
          id)
   :hints (("Goal" :in-theory (enable thread-id)))))

(local 
 (defthm mem-thread-thread-id
   (implies (and (mem (thread-by-id id tt) tt)
                 (thread-by-id id tt))
            (equal (thread-id (thread-by-id id tt)) id))
   :hints (("Goal" :in-theory (enable thread-by-id thread-id)
            :do-not '(generalize)))))

(local 
 (defthm not-thread-by-id-replace-thread-entry
   (implies (and (not (thread-by-id id tt))
                 (mem nil tt)
                 new-thread
                 (equal  (thread-id new-thread) id))
            (equal (thread-by-id id
                                 (replace-thread-table-entry 
                                  nil
                                  new-thread tt))
                   new-thread))
   :hints (("Goal" :in-theory (enable thread-by-id)))))


(local
 (defthm not-id-nil-then-thread-by-id-nil
   (implies (and (not (equal id nil))
                 (not (thread-by-id id tt)))
            (not (THREAD-BY-ID id 
                               (REPLACE-THREAD-TABLE-ENTRY
                                NIL
                                (MAKE-THREAD NIL NIL
                                             (LIST (FRAME-SET-OPERAND-STACK (LIST V) NIL))
                                             NIL NIL NIL NIL)
                                tt))))
   :hints (("Goal" :in-theory (e/d (thread-by-id) (make-thread))))))





(local 
 (defthm locals-frame-set-operand-stack
   (equal (LOCALS (FRAME-SET-OPERAND-STACK any frame))
          (locals frame))
   :hints (("Goal" :in-theory (enable frame-set-operand-stack locals)))))










(defthm locals-no-change-pushStack
  (equal (locals (current-frame (pushstack v s)))
         (locals (current-frame s)))
  :hints (("Goal" :in-theory (e/d (current-frame
                                   thread-set-call-stack
                                   push-stack-of-thread)
                                  (topframe-normalization
                                   make-thread
                                   locals))
           :cases ((mem (thread-by-id (current-thread s)
                                      (thread-table s))
                        (thread-table s))))
          ("Subgoal 1" :cases ((thread-by-id (current-thread s)
                                             (thread-table s))))
          ("Subgoal 1.2" :cases ((equal (current-thread s) nil)))))



(local
 (defthm not-id-nil-then-thread-by-id-nil-general
   (implies (and (not (equal id nil))
                 (equal (thread-id new-thread) nil)
                 (not (thread-by-id id tt)))
            (not (THREAD-BY-ID id 
                               (REPLACE-THREAD-TABLE-ENTRY
                                NIL
                                new-thread
                                tt))))
   :hints (("Goal" :in-theory (e/d (thread-by-id) (make-thread))))))


(defthm locals-no-change-popStack
  (equal (locals (current-frame (popStack s)))
         (locals (current-frame s)))
  :hints (("Goal" :in-theory (e/d (current-frame
                                   thread-set-call-stack
                                   popstack-of-thread)
                                  (topframe-normalization
                                   make-thread
                                   locals))
           :cases ((mem (thread-by-id (current-thread s)
                                      (thread-table s))
                        (thread-table s))))
          ("Subgoal 1" :cases ((thread-by-id (current-thread s)
                                             (thread-table s))))
          ("Subgoal 1.2" :cases ((equal (current-thread s) nil)))))




(defthm method-ptr-no-change-pushStack 
  (equal (method-ptr (current-frame (pushStack v s)))
         (method-ptr (current-frame s)))
  :hints (("Goal" :in-theory (e/d (current-frame
                                   thread-set-call-stack
                                   push-stack-of-thread)
                                  (topframe-normalization
                                   make-thread
                                   method-ptr))
           :cases ((mem (thread-by-id (current-thread s)
                                      (thread-table s))
                        (thread-table s))))
          ("Subgoal 1" :cases ((thread-by-id (current-thread s)
                                             (thread-table s))))
          ("Subgoal 1.2" :cases ((equal (current-thread s) nil)))))


(defthm method-ptr-no-change-popStack
  (equal (method-ptr (current-frame (popStack s)))
         (method-ptr (current-frame s)))
  :hints (("Goal" :in-theory (e/d (current-frame
                                   thread-set-call-stack
                                   popstack-of-thread)
                                  (topframe-normalization
                                   make-thread
                                   method-ptr))
           :cases ((mem (thread-by-id (current-thread s)
                                      (thread-table s))
                        (thread-table s))))
          ("Subgoal 1" :cases ((thread-by-id (current-thread s)
                                             (thread-table s))))
          ("Subgoal 1.2" :cases ((equal (current-thread s) nil)))))


;;; no hypothesis!! 
;;; this should be fine. 

;;;
;;; Expect more of these maybe we will move these into
;;; base-consistent-state.lisp itself! 
;;;


;;; These should be provable. It is obvious when s is a consistent-state 
;;; It is less so when s is some arbitrary state. 
;;; 


(defthm consistent-object-implies-object-type-not-primitive-type
  (implies (consistent-object obj (heap s) (instance-class-table s))
           (not (primitive-type? (obj-type obj)))))

(local 
 (defthm operand-stack-frame-set-opstack
   (equal (operand-stack (frame-set-operand-stack stk frame))
          stk)
   :hints (("Goal" :in-theory (enable frame-set-operand-stack operand-stack)))))


(local 
 (defthm consistent-thread-entries-implies-thread-by-id
   (implies (and (thread-by-id id tt)
                 (consistent-thread-entries tt cl hp))
            (mem  (thread-by-id id tt) tt))
   :hints (("Goal" :in-theory (enable thread-by-id)))))
                  

(local 
 (defthm consistent-state-implies-thread-exists
   (IMPLIES (CONSISTENT-STATE S)
            (MEM (THREAD-BY-ID (CURRENT-THREAD S)
                               (THREAD-TABLE S))
                 (THREAD-TABLE S)))
   :hints (("Goal" :in-theory (enable consistent-state)))))



(defthm operand-stack-current-frame-pushStack
  (implies (consistent-state s)
           (equal (operand-stack (current-frame (pushStack v s)))
                  (push v (operand-stack (current-frame s)))))
  :hints (("Goal" :in-theory (e/d (pushStack current-frame
                                             push-stack-of-thread)
                                  (topframe-normalization)))))


;; (skip-proofs 
;;  (defthm operand-stack-current-frame-popStack
;;    (equal (operand-stack (current-frame (popStack s)))
;;           (pop (operand-stack (current-frame s))))
;;    :rule-classes nil))

;;; ;;; this we don't want! We want to keep opstack-sig not to keep (popStack
;;; s) form untouched!! 
;;;
;;; Sun Jul 31 17:08:16 2005. At least this is the current strategy!! 

;;(i-am-here) ;; Sun Jul 31 17:09:06 2005

(defthm operand-stack-current-frame-popStack
  (implies (consistent-state s)
           (equal (operand-stack (current-frame (popStack s)))
                  (pop (operand-stack (current-frame s)))))
  :hints (("Goal" :in-theory (e/d (current-frame
                                   thread-set-call-stack
                                   popstack-of-thread)
                                  (topframe-normalization
                                   make-thread
                                   method-ptr))
           :cases ((mem (thread-by-id (current-thread s)
                                      (thread-table s))
                        (thread-table s))))
          ("Subgoal 1" :cases ((thread-by-id (current-thread s)
                                             (thread-table s))))
          ("Subgoal 1.2" :cases ((equal (current-thread s) nil))))
    :rule-classes nil)



(include-book "../../DJVM/consistent-state-to-sig-state")


(local 
 (defthm consistent-object-implies-obj-type
   (implies (consistent-object obj hp cl)
            (equal (bcv::sizeof (fix-sig (obj-type obj))) 1))
   :hints (("Goal" :in-theory (enable bcv::sizeof)))))

(local 
 (defthm consistent-state-implies-consistent-object
   (implies (and (consistent-state s)
                 (deref2 v (heap s)))
            (consistent-object (deref2 v (heap s)) (heap s)
                               (instance-class-table s)))
   :hints (("Goal" :in-theory (e/d (consistent-state)
                                   (consistent-object
                                    deref2))))))



(local 
 (defthm consistent-object-implies-obj-type-specific
   (implies (consistent-object (deref2 v (heap s)) (heap s)
                               (instance-class-table s))
            (equal (bcv::sizeof (fix-sig (obj-type (deref2 v (heap s))))) 1))
   :hints (("Goal" :in-theory (e/d () (bcv::sizeof deref2 obj-type consistent-object))))))



(defthm fix-sig-size-1
  (implies (consistent-state s)
           (equal (bcv::sizeof (fix-sig (obj-type (deref2 v (heap s))))) 1))
  :hints (("Goal" :in-theory (e/d () (deref2 obj-type consistent-object))
           :cases ((deref2 v (heap s))))))

;; (i-am-here) ;; Tue May 17 15:04:10 2005

(local 
 (defthm consistent-heap1-not-bound?
   (implies (and (consistent-heap1 hp1 hp cl id)
                 (< idx id))
            (not (binding idx hp1)))))


(defthm consistent-state-null-not-bounded?
  (implies (and (consistent-state s)
                (nullp v))
           (not (deref2 v (heap s))))
  :hints (("Goal" :in-theory (e/d (consistent-state consistent-heap deref2)
                                  (binding)))))

;;; openning up consistent-state always takes time to get a proof through. 
;;;

;----------------------------------------------------------------------
;; (i-am-here) ;; Sun Jul 31 13:52:41 2005

(defthm frame-aux-frame-set-operand-stack
  (equal (frame-aux (frame-set-operand-stack any frame))
         (frame-aux frame))
  :hints (("Goal" :in-theory (enable frame-aux
                                     frame-set-operand-stack))))


(defthm frame-aux-flags-pushStack-no-change
  (equal (frame-aux (current-frame (pushStack v s)))
         (frame-aux (current-frame s)))
  :hints (("Goal" :in-theory (e/d (current-frame
                                   thread-set-call-stack
                                   push-stack-of-thread)
                                  (topframe-normalization
                                   make-thread
                                   frame-aux
                                   method-ptr))
           :cases ((mem (thread-by-id (current-thread s)
                                      (thread-table s))
                        (thread-table s))))
          ("Subgoal 1" :cases ((thread-by-id (current-thread s)
                                             (thread-table s))))
          ("Subgoal 1.2" :cases ((equal (current-thread s) nil)))))




(defthm  frame-aux-flags-popStack-no-change
  (equal (frame-aux (current-frame (popStack s)))
         (frame-aux (current-frame s)))
  :hints (("Goal" :in-theory (e/d (current-frame
                                   thread-set-call-stack
                                   popstack-of-thread)
                                  (topframe-normalization
                                   make-thread
                                   frame-aux
                                   method-ptr))
           :cases ((mem (thread-by-id (current-thread s)
                                      (thread-table s))
                        (thread-table s))))
          ("Subgoal 1" :cases ((thread-by-id (current-thread s)
                                             (thread-table s))))
          ("Subgoal 1.2" :cases ((equal (current-thread s) nil)))))



(in-theory (disable frame-aux))




(defthm gen-frame-flags-pushStack-no-change
  (equal (gen-frame-flags  (current-frame (pushStack v s)) hp-init)
         (gen-frame-flags (current-frame s) hp-init))
  :hints (("Goal" :in-theory (e/d (gen-frame-flags)
                                  (pushStack current-frame)))))



(defthm gen-frame-flags-popStack-no-change
  (equal (gen-frame-flags  (current-frame (popStack s)) hp-init)
         (gen-frame-flags (current-frame s) hp-init))
  :hints (("Goal" :in-theory (e/d (gen-frame-flags)
                                  (popStack current-frame)))))


(in-theory (disable gen-frame-flags))