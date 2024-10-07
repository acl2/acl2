(in-package "DJVM")
(include-book "../M6-DJVM-shared/jvm-frame-manipulation-primitives")

(acl2::set-verify-guards-eagerness 2)

;;; Define stronger guard for pushStack, popStack that are used in defining
;;; bytecode semantics. 

(include-book "../DJVM/consistent-state")  
;; DJVM specific. In fact is about the same as current-thread

(defthm wff-call-frame-implies-wff-method-ptr-method-ptr
  (implies (wff-call-frame frame)
           (wff-method-ptr (method-ptr frame)))
  :hints (("Goal" :in-theory (enable method-ptr  wff-call-frame))))

(local (in-theory (disable wff-method-ptr method-ptr)))

(defun op-stack-primitive-shared-guard (s)
  (mylet* ((cid (current-thread s))
           (tt  (thread-table s))
           (thread (thread-by-id cid tt))
           (callstack (thread-call-stack thread))
           (topframe  (top callstack))
           (method-ptr (method-ptr (current-frame s)))
           (cl         (instance-class-table s))
           (method     (deref-method method-ptr cl)))
          (and (wff-state s)
               (wff-thread-table tt)
               (thread-exists? cid tt)
               (wff-thread thread)
               ;;
               ;; we don't need wff-call-stack we do need a wff-top-frame, we don't
               ;; care whether return pc are right or not. Just the syntax is right
               ;; to allow us to access certain fields and assert properties on certain
               ;; pieces that are concerned with validity of the operation.
               ;;
               (wff-call-stack callstack)
               (wff-call-frame topframe)
               (wff-class-table (class-table s))
               (wff-instance-class-table (instance-class-table s))
               (wff-method-decl method)
               (not (mem '*native* 
                         (method-accessflags method))))))
                    

;; Lets consider jvm-frame-manipulation-primitives.lisp's topStack being
;; INTERNAL operations of JVM, which does not check whether topStack is called
;; on a category1 top.

(defun topStack-guard-strong (s)
  (mylet*
   ((opstack 
         (operand-stack 
          (top (thread-call-stack (thread-by-id (current-thread s)
                                                (thread-table s)))))))
  (and (op-stack-primitive-shared-guard s)
       (canPopCategory1 opstack))))




;;; This is a different popStack. We want stronger check!!
;;; 
;;; Previously we use internal popStack
;;;; 
;;;; Defensive machine could check stronger guard than non defensive machine
;;;; could!!
;;;;

;;; should I change the definition. some proof might fail. but they should be
;;; easy to fix.

;;; let keep the current definition...

;;;
;;; safe-popStack is used in defining djvm bytecode semantics.  
;;;
;;; We have the folllowing property, if consistent-state, if guard does not
;;; fail, executing instruction perserves the consistent-state. 
;;; 

(defthm wff-thread-table-thread-by-id-thread-id
  (implies (and (wff-thread-table ths)
                (thread-by-id x ths))
           (equal (thread-id (thread-by-id x ths))
                  x)))


(defthm wff-thread-table-thread-by-id-thread-id-2
  (implies (and (wff-thread-table ths)
                (thread-by-id x ths))
           (equal (nth 1 (thread-by-id x ths))
                  x))
  :hints (("Goal" :in-theory (enable wff-thread thread-id wff-thread-table))))

(in-theory (enable wff-thread thread-id))

(defun safe-popStack (s)
  (declare (xargs :guard  (topStack-guard-strong s)))
  (mylet* ((curthread-id (current-thread s))
           (old-thread-table (thread-table s))
           (old-thread   (thread-by-id curthread-id old-thread-table))
           (old-call-stack (thread-call-stack old-thread))
           (old-frame      (top old-call-stack))
           (old-op-stack   (operand-stack old-frame))
           (new-op-stack   (pop old-op-stack))
           (new-frame    (frame-set-operand-stack new-op-stack old-frame))
           (new-call-stack (push new-frame (pop old-call-stack)))
           (new-thread     (thread-set-call-stack  new-call-stack old-thread))
           (new-thread-table (replace-thread-table-entry old-thread 
                                                         new-thread
                                                         old-thread-table)))
          (state-set-thread-table new-thread-table s)))

;;; enable many things. guard verification should be easy. 
;; Fri Jan 16 00:16:44 2004

(defun secondStack-guard-strong (s)
  (and (topStack-guard-strong s)
       (topStack-guard-strong (safe-popStack s))))


(defun thirdStack-guard-strong (s)
  (and (secondStack-guard-strong s)
       (topStack-guard-strong (safe-popStack (safe-popStack s)))))



;;
;; could disable more functions and prove more accessors 
;;
(defun safe-topStack (s) 
  (declare (xargs :guard (topStack-guard-strong s)))
  ;; we could not be able to guard verify that topStack's guard can be verified
  ;; unless we have a extensive ... check-inst  
  (top (operand-stack 
        (top (thread-call-stack (thread-by-id (current-thread s)
                                              (thread-table s)))))))





(defun safe-secondStack (s)
  (declare (xargs :guard (secondStack-guard-strong s)
                  :guard-hints (("Goal" :in-theory (disable topStack-guard)))))
  
  (safe-topStack (safe-popStack s)))


(defun safe-thirdStack (s)
  (declare (xargs :guard (thirdStack-guard-strong s)
                  :guard-hints (("Goal" :in-theory (disable topStack-guard)))))
  
  (safe-topStack (safe-popStack (safe-popStack s))))


;----------------------------------------------------------------------

;; push is always allowed. 
;; pushStack now has a stronger guard!! 
;; Maybe we do not need that. 
;; Any operations now needs such a stronge guard. 
;; 
;; have to think again about whether we need to just use pushStack as ...
;; 

;; notice this is a very strong guard, if a state is not consistent,
;; safe-pushStack will signal a guard violation. 


(defthm consistent-state-implies-wff-thread-table
  (implies (consistent-state s)
           (wff-thread-table (thread-table s)))
  :rule-classes :forward-chaining)

;; do I want to disable consistent-state


(defthm consistent-state-implies-wff-thread-table-b
  (implies (consistent-state s)
           (wff-thread-table (thread-table s))))

;; do I want to disable thread-table, here? 


(defthm consistent-state-implies-wff-thread-exists
  (implies (consistent-state s)
           (thread-exists? (current-thread s)
                          (thread-table s)))
  :rule-classes :forward-chaining)

(defthm consistent-state-implies-wff-thread-exists-b
  (implies (consistent-state s)
           (thread-exists? (current-thread s)
                          (thread-table s))))



(defthm thread-exists-wff-thread-table-wff-thread
  (implies (and (thread-exists? id ths)
                (wff-thread-table ths))
           (wff-thread (thread-by-id id ths)))
  :rule-classes :forward-chaining)


(defthm thread-exists-wff-thread-table-wff-thread-b
  (implies (and (thread-exists? id ths)
                (wff-thread-table ths))
           (wff-thread (thread-by-id id ths))))


(defthm thread-exists-consistent-thread-table-consistent-thread
  (implies (and (thread-exists? id ths)
                (consistent-thread-entries ths cl hp))
           (consistent-thread-entry (thread-by-id id ths) cl hp))
  :rule-classes :forward-chaining)


(defthm thread-exists-consistent-thread-table-consistent-thread-b
  (implies (and (thread-exists? id ths)
                (consistent-thread-entries ths cl hp))
           (consistent-thread-entry (thread-by-id id ths) cl hp)))


(defthm consistent-thread-entry-implies-consistent-call-stack
  (implies (consistent-thread-entry th cl hp)
           (consistent-call-stack (thread-call-stack th) cl hp))
  :rule-classes :forward-chaining)


(defthm consistent-thread-entry-implies-consistent-call-stack-b
  (implies (consistent-thread-entry th cl hp)
           (consistent-call-stack (thread-call-stack th) cl hp)))


(defthm consistent-call-stack-implies-wff-call-frame-top-frame
  (implies (and (consistent-call-stack cstack cl hp)
                (consp cstack))
           (wff-call-frame (car cstack)))
  :rule-classes :forward-chaining)

;; (acl2::set-match-free-error nil)

(defthm consistent-call-stack-implies-wff-call-frame-top-frame-b
  (implies (and (consistent-call-stack cstack cl hp)
                (consp cstack))
           (wff-call-frame (car cstack))))

;; this is not a good backchain rule, although it is quite general
;; strong for people to use. 

(defthm consistent-thread-entry-implies-wff-call-frame
  (implies (consistent-thread-entry th cl hp)
           (wff-call-frame (top (thread-call-stack th))))
  :rule-classes :forward-chaining)


(defthm consistent-thread-entry-implies-wff-call-frame-b
  (implies (consistent-thread-entry th cl hp)
           (wff-call-frame (top (thread-call-stack th)))))


;;
;; this it could get from 
;;   consistent-call-stack-implies-wff-call-frame-top-frame-b
;;   consistent-thread-entry-implies-consistent-call-stack-b
;;  and definition of consistent-thread-entry 
;;
;; Not it could not. Because of the free variable.  10/06/03  
;;

(defthm consistent-state-implies-consistent-thread-entry
  (implies (consistent-state s)
           (consistent-thread-entry (thread-by-id (current-thread s)
                                                  (thread-table s))
                                    (instance-class-table s)
                                    (heap s)))
  :rule-classes :forward-chaining)


(defthm consistent-thread-entry-consp-call-stack
  (implies (consistent-thread-entry th cl hp)
           (consp (thread-call-stack th)))
  :rule-classes :forward-chaining)

;; need to prove some theorems about updating subcomponent in a disiplined way
;; will preserve the consistent-state or well-formed ness

(defthm wff-thread-set-wff-call-stack-remains-wff
  (implies (and (wff-thread tt)
                (consp cs))
           (wff-thread (thread-set-call-stack cs tt)))
  :hints (("Goal" :in-theory (enable wff-thread))))


(defthm thread-set-call-stack-not-change-thread-id 
  (equal (thread-id (thread-set-call-stack cs th))
         (thread-id th))
  :hints (("Goal" :in-theory (enable thread-set-call-stack))))


;; (include-book "../DJVM/consistent-state-properties")  

(acl2::set-verify-guards-eagerness 0)

(defun safe-pushStack (value s)
 (declare (xargs :guard (and (consistent-state s)
                             (not (mem '*native*
                                       (method-accessflags
                                        (deref-method (method-ptr
                                                       (current-frame s))
                                                      (instance-class-table s)))))
                             (<= (+ 1 (len (operand-stack (current-frame s))))
                                 (max-stack s)))))
  (mylet* ((curthread-id (current-thread s))
           (old-thread-table (thread-table s))
           (old-thread   (thread-by-id curthread-id old-thread-table))
           (old-call-stack (thread-call-stack old-thread))
           (old-frame      (top old-call-stack))
           (old-op-stack   (operand-stack old-frame))
           (new-op-stack   (push value old-op-stack))
           (new-frame    (frame-set-operand-stack new-op-stack old-frame))
           (new-call-stack (push new-frame (pop old-call-stack)))
           (new-thread     (thread-set-call-stack  new-call-stack old-thread))
           (new-thread-table (replace-thread-table-entry old-thread 
                                                         new-thread
                                                         old-thread-table)))
          (state-set-thread-table new-thread-table s)))


(defun safe-pushCategory2 (value s)
  (declare (xargs :guard (and (consistent-state s)
                              (not (mem '*native* (method-accessflags 
                                                   (deref-method (method-ptr
                                                                  (current-frame s))
                                                                 (instance-class-table s)))))
                              (<= (+ 2 (len (operand-stack (current-frame s))))
                                  (max-stack s)))))
  (pushStack value (pushStack '(topx . topx) s))) 
;;
;; Tue Jul 26 12:06:21 2005
;; fixed to make the life of base-untag-state.lisp easier!! 
;;












