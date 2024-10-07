(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-thread")

(acl2::set-verify-guards-eagerness 2)
;; we chosed to not do guard verification for class loader, let me try to do
;; the guard verification here. 

;---- short cut to retrieve information in the current state.

;; the guard on this function is fairly complicated!!  Wed Dec 24 18:38:05 2003
;; We also most end up writing wff-state-strong (recursively) every level being
;; synatx correct!

;; We should first define all data structures then define syntax WFF
;; then define operations that cut through levels by asserting WFF at the
;; input. 
;;
;; Wed Dec 24 18:40:44 2003
;; 
;; the problem is that the concept of maybe too varied. 
;; We may just relying on consistent-state. 

(defun wff-call-stack (call-stack)
  (>= (len call-stack) 1)) ;; call-stack has at least one frame 


(defun current-frame-guard (s)
  (and (wff-state s)
       (wff-thread-table (thread-table s))
       (wff-thread (thread-by-id (current-thread s) (thread-table s)))
       (wff-call-stack (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s))))))

(defun current-frame (s)
  (declare (xargs :guard (current-frame-guard s)))
  (let* ((tid         (current-thread s))
         (curthread   (thread-by-id tid (thread-table s)))
         (call-stack  (thread-call-stack curthread))
         (top-frame   (top call-stack)))
    top-frame))

;; same as top-frame in bcv-check-djvm-check.lisp Tue Mar  9 16:39:24 2004

(defun current-method-ptr (s)
  (declare (xargs :guard (and (current-frame-guard s)
                              (wff-call-frame (current-frame s)))))
  (method-ptr (current-frame s)))

(defun localx (s)
  (declare (xargs :guard (and (current-frame-guard s)
                              (wff-call-frame (current-frame s)))))
  (locals (current-frame s)))


(defun current-class (s)
  (declare (xargs :guard (and (current-frame-guard s)
                              (wff-call-frame (current-frame s))
                              (wff-method-ptr (current-method-ptr s))
                              (wff-state s)
                              (wff-class-table (class-table s))
                              (wff-instance-class-table (instance-class-table s)))))
  (let ((classname (method-ptr-classname (current-method-ptr s))))
    (class-by-name classname (instance-class-table s))))


;;--- short cut to push value, get values from the current frame
;; 
;; Java visible stack operation.
;;
;; return state. 
;; may be simplified using modify macro 

(defun alert (msg s)
  (prog2$ (acl2::cw msg)
          s))

(defun push-stack-of-thread (value old-thread)
  (declare (xargs :guard (and (wff-thread old-thread)
                              (wff-call-stack (thread-call-stack old-thread))
                              (wff-call-frame (top (thread-call-stack old-thread))))))
  (let* ((old-call-stack (thread-call-stack old-thread))
         (old-frame      (top old-call-stack))
         (old-op-stack   (operand-stack old-frame))
         (new-op-stack   (push value old-op-stack))
         (new-frame    (frame-set-operand-stack new-op-stack old-frame))
         (new-call-stack (push new-frame (pop old-call-stack)))
         (new-thread     (thread-set-call-stack  new-call-stack old-thread)))
    new-thread))


;; need a prove here to relieve that guard 
;; of state-set-thread-table 

(defthm push-stack-of-thread-wff-wff
  (implies (wff-thread old-thread)
           (wff-thread (push-stack-of-thread value old-thread))))
  


(defthm replace-thread-table-entry-wff-wff
  (implies (and (wff-thread new-thread)
                (wff-thread-table tt))
           (wff-thread-table (replace-thread-table-entry
                               old-thread new-thread tt))))

(defthm wff-state-set-thread-table-wff-wff
  (implies (and (wff-state s)
                (wff-thread-table tt))
           (wff-state (state-set-thread-table tt s)))
  :hints (("Goal" :in-theory (enable wff-state state-set-thread-table
                                     make-state pc))))


(defthm thread-by-id-is-id
   (implies (wff-thread (thread-by-id id tt))
            (equal (thread-id (thread-by-id id tt))
                   id)))


(defthm thread-id-unchanged-by-push-value
   (equal (thread-id (push-stack-of-thread value old-thread))
          (thread-id old-thread))
   :hints (("Goal" :in-theory (enable push-stack-of-thread))))

(in-theory (disable push-stack-of-thread wff-thread thread-id
                    wff-call-stack wff-call-frame
                    state-set-thread-table wff-state wff-thread-table))


;; replace-thread-table-entry has a strong guard!!

(defun pushStack (value s)
  (declare (xargs :guard (and (current-frame-guard s)
                              (wff-call-frame (current-frame s)))))
  (mylet* ((curthread-id (current-thread s))
           (old-thread-table (thread-table s))
           (old-thread   (thread-by-id curthread-id old-thread-table))
           (new-thread   (push-stack-of-thread value  old-thread))
           (new-thread-table (replace-thread-table-entry old-thread 
                                                         new-thread
                                                         old-thread-table)))
          (state-set-thread-table new-thread-table s)))

(in-theory (disable operand-stack thread-call-stack))
(in-theory (enable wff-call-stack))

(defun popStack-of-thread (old-thread)
  (declare (xargs :guard (and (wff-thread old-thread)
                              (wff-call-stack (thread-call-stack old-thread))
                              (wff-call-frame (top (thread-call-stack
                                                    old-thread)))
                              (consp (operand-stack (top (thread-call-stack old-thread)))))))
  (let* ((old-call-stack (thread-call-stack old-thread))
         (old-frame      (top old-call-stack))
         (old-op-stack   (operand-stack old-frame))
         (new-op-stack   (pop old-op-stack))
         (new-frame    (frame-set-operand-stack new-op-stack old-frame))
         (new-call-stack (push new-frame (pop old-call-stack)))
         (new-thread     (thread-set-call-stack  new-call-stack old-thread)))
    new-thread))

(defthm pop-stack-of-thread-wff-wff
  (implies (wff-thread old-thread)
           (wff-thread (popStack-of-thread old-thread)))
  :hints (("Goal" :in-theory (enable wff-thread))))


(defthm thread-id-unchanged-by-pop-value
   (equal (thread-id (popStack-of-thread old-thread))
          (thread-id old-thread))
   :hints (("Goal" :in-theory (enable popstack-of-thread thread-id))))

(in-theory (disable popStack-of-thread))



(defun popStack (s)
  (declare (xargs :guard (and (current-frame-guard s)
                              (wff-call-frame (current-frame s))
                              (consp (operand-stack (current-frame s))))))
  (mylet* ((curthread-id (current-thread s))
           (old-thread-table (thread-table s))
           (old-thread   (thread-by-id curthread-id old-thread-table))
           (new-thread   (popStack-of-thread old-thread))
           (new-thread-table (replace-thread-table-entry old-thread 
                                                         new-thread
                                                         old-thread-table)))
          (state-set-thread-table new-thread-table s)))


(defun set-local-at-of-thread (index value old-thread)
  (declare (xargs :guard (and (wff-thread old-thread)
                              (wff-call-stack (thread-call-stack old-thread))
                              (wff-call-frame (top (thread-call-stack
                                                    old-thread)))
                              (integerp index)
                              (<= 0 index)
                              (true-listp (locals (top (thread-call-stack
                                                        old-thread))))
                              (< index (len (locals (top (thread-call-stack old-thread))))))))
  (mylet* ((old-call-stack (thread-call-stack old-thread))
           (old-top-frame  (top old-call-stack))
           (old-locals     (locals old-top-frame))
           (new-locals     (update-nth index value old-locals))
           (new-top-frame  (frame-set-locals new-locals old-top-frame))
           (new-call-stack (push new-top-frame (pop old-call-stack)))
           (new-thread     (thread-set-call-stack new-call-stack old-thread)))
          new-thread))

;;;
;;; the problem!!! this operation is shared by DJVM and JVM!! 
;;; 
;;; in DJVM, we need to trash the "double" value, if the second half of that
;;; size 2 value is over writtend with value!! 
;;;
;;; We need to do that in DJVM!! 


(defthm set-local-at-of-threadwff-wff
  (implies (wff-thread old-thread)
           (wff-thread (set-local-at-of-thread i v old-thread)))
  :hints (("Goal" :in-theory (enable set-local-at-of-thread wff-thread))))

(defthm thread-id-unchanged-by-set-local-at
   (equal (thread-id (set-local-at-of-thread i v old-thread))
          (thread-id old-thread))
   :hints (("Goal" :in-theory (enable set-local-at-of-thread thread-id))))

(in-theory (disable set-local-at-of-thread))


(defun state-set-local-at (index value s)
  (declare (xargs :guard (and (current-frame-guard s)
                              (wff-call-frame (current-frame s))
                              (integerp index)
                              (<= 0 index)
                              (true-listp (locals (current-frame s)))
                              (< index (len (locals (current-frame s)))))))
  (mylet* ((old-thread-table (thread-table s))
           (old-thread (thread-by-id (current-thread s) old-thread-table))
           (new-thread (set-local-at-of-thread index value old-thread))
           (new-thread-table (replace-thread-table-entry old-thread new-thread
                                                         old-thread-table)))
    (state-set-thread-table new-thread-table s)))


;; Commented out Suppose to be M6 and DJVM specific!!
;;

(defun topStack-guard (s)
   (and (current-frame-guard s)
        (wff-call-frame (current-frame s))
        (consp (operand-stack (current-frame s)))))

(defun topStack (s)
   (declare (xargs :guard (topStack-guard s)))
   (top (operand-stack (current-frame s))))


;; internal topStack used in 
;;
;; Sun Dec 28 22:41:38 2003: Different use of topStack!!

(defun secondStack (s)
  (declare (xargs :guard (and (topStack-guard s)
                              (topStack-guard (popStack s)))))
  (topStack (popStack s)))




; (defun thirdStack (s);   (declare (xargs :guard (and (topStack-guard s)
;                               (topStack-guard (popStack s))
;                               (topStack-guard (popStack (popStack s))))))
;   (topStack (popStack (popStack s))))


; (defun fourthStack (s)
;   (declare (xargs :guard (and (topStack-guard s)
;                               (topStack-guard (popStack s))
;                               (topStack-guard (popStack (popStack s)))
;                               (topStack-guard (popStack (popStack (popStack s)))))))
;   (topStack (popStack (popStack (popStack s)))))


; ;; (defun fifthStack (s)
; ;;   (topStack (popStack (popStack (popStack (popStack s))))))

; ;; there the guard does not contain semantic information.... guard are just
; ;; requirement of LISP!! Otherwise we would require that popStack could only be
; ;; called on Operand stack with top element being a size one object!!
; ;; thus guard verification would say more. ...
; ;; 
; ;; Realization: those operation should be defined as M6 operations and DJVM
; ;; operations seperatedly!! but how about our class loader? They do not use
; ;; those primitives? They do not change opstack!!

; (defun popStackN (n s)
;   (if (zp n)
;       s
;     (popStackN (- n 1) (popStack s))))


; (defun pushLong (v s)
;   (pushStack 'topx (pushStack v s)))


; (defun popLong (s)
;   (popStack (popStack s)))

; (defun topLong  (s)    
;   (topStack (popStack s)))
;

;;;; Mon Dec 29 15:53:17 2003 this JVM specific!!

; ;-- primitives for executing the method.



; ;; FRAME operation

;;;; Mon Dec 29 15:56:01 2003 reuse the following!! 
;;;; Tue Jan 13 17:40:16 2004 Not the current priority. We only want to write a
;;;; consistent-state, whose's guard is t!!

;;;; 
;;;; deal with this later!!
;;;; 


;;; (i-am-here) 

;;;
;;; Tue Mar 15 20:14:29 2005. Now dealing with guard verification
;;; of ARETURN. We need to guard verify these. 
;;;
;;; At least write down appropriate guard on this. 
;;;
;;; We will also need to update consistent-state to assert this! 
;;; 
;;; We also need to deal with special cases when a native method is invoked.

;;; (acl2::set-verify-guards-eagerness 0)


;;;
;;; now the question of how strong the guards should be!! 
;;; Should it characterize the only the conditions it could be invoked? 
;;; 

;;; We could make pushFrame0 to check everything so that its guard will be T
;;;
;;; However: it will affect the execution speed! 
;;; 


(defun pushFrame0-guard (s)
   (and (wff-state s)
        (wff-thread-table (thread-table s))
        (wff-thread (thread-by-id (current-thread s) 
                                  (thread-table s)))))

;;; some theorem will needed

(defthm wff-thread-thread-set-call-stack-push
  (implies (wff-thread thread)
           (wff-thread (thread-set-call-stack 
                        (push frame (thread-call-stack thread))
                        thread)))
  :hints (("Goal" :in-theory (enable wff-thread thread-set-call-stack))))

(defthm wff-thread-thread-set-call-stack-pop
  (implies (wff-thread thread)
           (wff-thread (thread-set-call-stack 
                        (pop (thread-call-stack thread))
                        thread)))
  :hints (("Goal" :in-theory (enable wff-thread thread-set-call-stack))))

(defthm thread-id-thread-set-call-stack
  (equal (thread-id (thread-set-call-stack cs thread))
         (thread-id thread))
  :hints (("Goal" :in-theory (enable thread-id))))
                                              
(local (in-theory (disable thread-set-call-stack push pop)))



(defun pushFrame0 (new-frame s)
  (declare (xargs :guard (pushFrame0-guard s)))
  (mylet* ((curthread-id     (current-thread s))
           (old-thread-table (thread-table s))
           (old-thread (thread-by-id curthread-id old-thread-table))
           (old-call-stack (thread-call-stack old-thread))
           (new-call-stack (push new-frame old-call-stack))
           (new-pc         0) ;; set new pc
           (new-thread    (thread-set-call-stack new-call-stack old-thread))
           (new-thread-table (replace-thread-table-entry old-thread 
                                                         new-thread 
                                                         old-thread-table)))
          (state-set-pc new-pc (state-set-thread-table new-thread-table s))))

;;; The question here is whether we assert that pushFrame's method-ptr is a
;;; valid-method-ptr. whether to asssert that initial-locals matches with
;;; method-ptr
;;; 
;;; We have several other usage of pushFrame (in implementing native call) it
;;; is likely that these usage pattern will fail an over simplified "guard"
;;;
;;; We have a two conflict goals here: Caputre safety condition for using such
;;; operations. 
;;;
;;; Tue Mar 15 21:39:15 2005. Go with the barely necessary assertions. 
;;; 

(defun pushFrame (method-ptr initial-locals s)
  (declare (xargs :guard (pushFrame0-guard s)))
  (let* ((new-operand-stack (make-init-operand-stack))
         (return-pc    (pc s))
         (new-frame    (make-frame return-pc new-operand-stack initial-locals
                                   method-ptr -1 -1 nil))) ;; Sat Jul 30 23:56:01 2005
    (pushFrame0 new-frame s)))

;;;
;;; note the DJVM will take care of setting up the aux environment!! 
;;;


(defun popFrame (s)
  (declare (xargs :guard (and (current-frame-guard s)
                              (wff-call-frame (current-frame s)))))
  (let* ((curthread-id  (current-thread s))
         (old-thread-table (thread-table s))
         (old-thread     (thread-by-id curthread-id old-thread-table))
         (old-call-stack (thread-call-stack old-thread))
         (new-pc         (return-pc (top old-call-stack)))
         (new-call-stack (pop old-call-stack))
         (new-thread     (thread-set-call-stack new-call-stack old-thread))
         (new-thread-table (replace-thread-table-entry old-thread 
                                                       new-thread 
                                                       old-thread-table)))
    (state-set-pc new-pc (state-set-thread-table new-thread-table s))))



 ;; do nothing if invoked on illegal input. maybe I should add some
 ;; output to indicate guard violation.
 ;;;; Mon Dec 29 15:57:57 2003. above comment outdated!! We will use guard
 ;;;; verification to ensure not such thing happen!!




; (defun build-initial-local1 (rev-arg-types operand-stack)
;   (if (endp rev-arg-types)
;       nil
;     (if (equal (type-size (car rev-arg-types)) 2)
;         (cons 'topx (cons (top (pop operand-stack))  
;            ;; assuming in locals, a Long value is stored in the first slot.
;                          (build-initial-local1 (cdr rev-arg-types) (pop (pop
;                                                                          operand-stack)))))
;       (cons (top operand-stack) (build-initial-local1 (cdr rev-arg-types) (pop operand-stack))))))
      

; (defun build-initial-local (arg-types operand-stack)  (reverse (build-initial-local1 (reverse arg-types) operand-stack)))

;; (defun make-method-ptr (classname methodname args-type return-type)
;;    (list 'method-ptr classname methodname args-type return-type))
;;
;;; defined in jvm-thread.lisp. Tue Mar 15 21:41:51 2005

;; (defun wff-method-ptr (method-ptr)
;;    (and (true-listp method-ptr)
;;         (equal (len method-ptr) 5)
;;  ;;     (consp (nth 3 method-ptr)) this is not necessary. in conflict with
;;  ;; functions with no parameter. FIXED 10/28/03
;;         (true-listp (nth 3 method-ptr))))
       
;;; defined in jvm-thread.lisp. Tue Mar 15 21:42:18 2005


; (defun method-ptr-classname   (method-ptr) 
;   (declare (xargs :guard (wff-method-ptr method-ptr)))
;   (nth 1 method-ptr))

; (defun method-ptr-methodname  (method-ptr)  
;   (declare (xargs :guard (wff-method-ptr method-ptr)))
;   (nth 2 method-ptr))

; (defun method-ptr-args-type   (method-ptr) 
;   (declare (xargs :guard (wff-method-ptr method-ptr)))
;   (nth 3 method-ptr))

; (defun method-ptr-returntype  (method-ptr)  
;   (declare (xargs :guard (wff-method-ptr method-ptr)))
;   (nth 4 method-ptr))


; ; primitives for how to get a method-ptr to store in the call frame
; (defun method-rep-to-method-ptr (method-rep)
;   (make-method-ptr (method-classname method-rep)
;                    (method-methodname method-rep)
;                    (method-args       method-rep)
;                    (method-returntype method-rep)))



; (defun pushFrameWithPop (obj-ref method-rep s)
;   (let* ((method-ptr (method-rep-to-method-ptr method-rep))
;          (locals     (build-initial-local (method-args method-rep)
;                                           (operand-stack (current-frame s))))
;          (accessflags (method-accessflags method-rep)))
;     (if (mem '*static* accessflags) ;; no this pointer
;         (pushFrame method-ptr locals (popStackN (len locals) s))
;       (pushFrame method-ptr (cons obj-ref locals) (popStackN (+ (len locals) 1) s)))))


;--- 

;;;
;;; Mon Apr 18 16:01:21 2005
;;;
;;; Shall I add something here so that it may disrupt the proof of other
;;; things? 
;;;
;;; How likely it will happen? 

;;; From DJVM/INST/base.lisp
;;;

;; (defthm operand-stack-frame-set-opstack
;;   (equal (operand-stack (frame-set-operand-stack opstack frame))
;;          opstack)
;;   :hints (("Goal" :in-theory (enable frame-set-operand-stack operand-stack))))








