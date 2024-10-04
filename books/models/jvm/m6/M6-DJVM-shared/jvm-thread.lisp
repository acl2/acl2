(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-type-value")
(include-book "../M6-DJVM-shared/jvm-state")
(include-book "../M6-DJVM-shared/jvm-obj")
(include-book "../M6-DJVM-shared/jvm-internal-primitives")

;; 08/27/03 The only difference between defensive machine and non-defensive
;; machine is that we want OP stack and Locals has tagged value.
;;
;; We will define a function to untag the top frame of the current thread to
;; relate the BCV results. How do we deal with scheduling issue??
;; 
;; No scheduling? or finite scheduling?
;;
;; How to relate to BCV result with a multi-threaded JVM


(acl2::set-verify-guards-eagerness 2)

(defun make-thread-table (threads) 
  (cons 'thread-table threads))

;(defun threads (thread-table)
;  (cdr thread-table))

;; threads are a list of (id . thread) pair


(defun make-thread (id pc call-stack s m-ref mdepth thread-ref)
  (list 'thread id 
     (cons 'saved-pc pc)
     (cons 'call-stack call-stack)
     (cons 'status s)         ;; 
     (cons 'monitor  m-ref)
     (cons 'mdepth   mdepth)
     (cons 'thread-obj thread-ref)))

;; status is a list of 
;; flags 
;; thread_just_born thread_active thread_suspended thread_dead
;; thread_monitor_wait thread_convar_wait 


(defun wff-thread (thread) 
  (and (true-listp thread)
       (equal (len thread) 8)
       (equal (car thread) 'thread)
       (consp (nth 2 thread))
       (consp (nth 3 thread))
       (consp (nth 4 thread))
       (consp (nth 5 thread))
       (consp (nth 6 thread))
       (consp (nth 7 thread))))

(defun thread-id (thread)
  (declare (xargs :guard (wff-thread thread)))
  (nth 1 thread))
  

(defun thread-saved-pc    (thread) 
  (declare (xargs :guard (wff-thread thread)))
  (cdr (nth 2 thread)))

(defun thread-call-stack  (thread) 
  (declare (xargs :guard (wff-thread thread)))
  (cdr (nth 3 thread)))

(defun thread-state       (thread) 
  (declare (xargs :guard (wff-thread thread)))
  (cdr (nth 4 thread))) ;; thread-state is a list

(defun thread-mref       (thread)
  (declare (xargs :guard (wff-thread thread)))
  (cdr (nth 5 thread)))

(defun thread-mdepth     (thread) 
  (declare (xargs :guard (wff-thread thread)))
  (cdr (nth 6 thread)))

(defun thread-ref         (thread) 
  (declare (xargs :guard (wff-thread thread)))
  (cdr (nth 7 thread)))


;; (defun make-thread (id pc call-stack s m-ref mdepth thread-ref)
;;   (list 'thread id 
;;      (cons 'saved-pc pc)
;;      (cons 'call-stack call-stack)
;;      (cons 'status s)         ;; 
;;      (cons 'monitor  m-ref) ;; the monitor its currently holding or just holded.
;;      (cons 'mdepth   mdepth)
;;      (cons 'thread-obj thread-ref)))

;; ;; 
;; ;; Status is a set of combinations flags 
;; ;; 
;; ;;   thread_just_born 
;; ;;   thread_active 
;; ;;   thread_suspended 
;; ;;   thread_dead
;; ;;   thread_monitor_wait 
;; ;;   thread_convar_wait
;; ;;

;; (defun thread-id          (thread)   (nth 1 thread))
;; (defun thread-saved-pc    (thread)   (cdr (nth 2 thread)))
;; (defun thread-call-stack  (thread)   (cdr (nth 3 thread)))
;; (defun thread-state       (thread)   (cdr (nth 4 thread)))  ;; thread-state is a list
;; (defun thread-mref        (thread)    (cdr (nth 5 thread))) ;; the monitor being hold
;; (defun thread-mdepth      (thread)    (cdr (nth 6 thread)))
;; (defun thread-ref         (thread)   (cdr (nth 7 thread)))  ;; thread-obj

(defthm thread-accessor-is
  (let ((thread (make-thread id pc cs s m-ref mdepth thread-ref)))
  (and (equal (thread-id thread) id)
       (equal (thread-saved-pc thread) pc)
       (equal (thread-call-stack thread) cs)
       (equal (thread-state thread) s)
       (equal (thread-mref thread) m-ref)
       (equal (thread-mdepth thread) mdepth)
       (equal (thread-ref thread) thread-ref))))



(defun thread-set-id  (id thread)
  (declare (xargs :guard (wff-thread thread)))
  (make-thread id
               (thread-saved-pc thread)
               (thread-call-stack thread)
               (thread-state      thread)
               (thread-mref       thread)
               (thread-mdepth     thread)
               (thread-ref        thread)))


(defun thread-set-saved-pc  (pc thread)
  (declare (xargs :guard (wff-thread thread)))
  (make-thread (thread-id       thread)
               pc
               (thread-call-stack thread)
               (thread-state      thread)
               (thread-mref       thread)
               (thread-mdepth     thread)
               (thread-ref        thread)))

(defun thread-set-call-stack  (cs thread)
  (declare (xargs :guard (wff-thread thread)))
  (make-thread (thread-id       thread)
               (thread-saved-pc thread)
               cs
               (thread-state      thread)
               (thread-mref       thread)
               (thread-mdepth     thread)
               (thread-ref        thread)))

(defun thread-set-state  (st  thread)
  (declare (xargs :guard (wff-thread thread)))
  (make-thread (thread-id       thread)
               (thread-saved-pc thread)
               (thread-call-stack thread)
               st
               (thread-mref       thread)
               (thread-mdepth     thread)
               (thread-ref        thread)))

(defun thread-set-mref (mref thread)
  (declare (xargs :guard (wff-thread thread)))
  (make-thread (thread-id       thread)
               (thread-saved-pc thread)
               (thread-call-stack thread)
               (thread-state      thread)
               mref
               (thread-mdepth     thread)
               (thread-ref        thread)))


(defun thread-set-mdepth  (mdepth thread)
  (declare (xargs :guard (wff-thread thread)))
  (make-thread (thread-id       thread)
               (thread-saved-pc thread)
               (thread-call-stack thread)
               (thread-state      thread)
               (thread-mref       thread)
               mdepth
               (thread-ref        thread)))

(defun thread-set-ref  (ref thread)
  (declare (xargs :guard (wff-thread thread)))
  (make-thread (thread-id       thread)
               (thread-saved-pc thread)
               (thread-call-stack thread)
               (thread-state      thread)
               (thread-mref       thread)
               (thread-mdepth     thread)
               ref))

;----------------------------------------------------------------------

(defun make-method-ptr (classname methodname args-type return-type)
   (list 'method-ptr classname methodname args-type return-type))

(defun wff-method-ptr (method-ptr)
  (and (true-listp method-ptr)
       (equal (len method-ptr) 5)
;;     (consp (nth 3 method-ptr)) this is not necessary. in conflict with
;; functions with no parameter. FIXED 10/28/03
       (true-listp (nth 3 method-ptr))))
       


(defun method-ptr-classname   (method-ptr) 
  (declare (xargs :guard (wff-method-ptr method-ptr)))
  (nth 1 method-ptr))

(defun method-ptr-methodname  (method-ptr)  
  (declare (xargs :guard (wff-method-ptr method-ptr)))
  (nth 2 method-ptr))

(defun method-ptr-args-type   (method-ptr) 
  (declare (xargs :guard (wff-method-ptr method-ptr)))
  (nth 3 method-ptr))

(defun method-ptr-returntype  (method-ptr)  
  (declare (xargs :guard (wff-method-ptr method-ptr)))
  (nth 4 method-ptr))

;----------------------------------------------------------------------

(defun make-frame (return-pc operant-stack locals method-ptr sync-obj-ref
                             resume-pc aux)
  (list 'frame 
        (cons 'return_pc return-pc)
        (cons 'operand-stack operant-stack)
        (cons 'locals locals)
        method-ptr
        (cons 'sync-obj-ref sync-obj-ref)
        (cons 'resume-pc resume-pc)
        (cons 'aux aux)))


(defun wff-call-frame (frame)
  (and (true-listp frame)
       (equal (len frame) 8)
       (equal (car frame) 'frame)
       (consp (nth 1 frame))
       (consp (nth 2 frame))
       (true-listp (nth 2 frame))
       (consp (nth 3 frame))
       (true-listp (nth 3 frame))
       (wff-method-ptr (nth 4 frame))
       (consp (nth 5 frame))
       (consp (nth 6 frame))
       (consp (nth 7 frame))))

(defun return-pc     (frame)    
  (declare (xargs :guard (wff-call-frame frame)))
  (cdr (nth 1 frame)))

(defun operand-stack (frame)  
  (declare (xargs :guard (wff-call-frame frame)))
  (cdr (nth 2 frame)))

(defun locals        (frame)   
  (declare (xargs :guard (wff-call-frame frame)))
  (cdr (nth 3 frame)))

(defun method-ptr    (frame)  
  (declare (xargs :guard (wff-call-frame frame)))
  (nth 4 frame))

(defun sync-obj-ref  (frame) 
  (declare (xargs :guard (wff-call-frame frame)))
  (cdr (nth 5 frame)))

(defun resume-pc  (frame) 
  (declare (xargs :guard (wff-call-frame frame)))
  (cdr (nth 6 frame)))


(defun frame-aux  (frame) 
  (declare (xargs :guard (wff-call-frame frame)))
  (cdr (nth 7 frame)))

;----------------------------------------------------------------------

(defun frame-set-return-pc     (pc frame)    
  (declare (xargs :guard (wff-call-frame frame)))
      (make-frame pc 
                  (operand-stack frame)
                  (locals        frame)
                  (method-ptr    frame)
                  (sync-obj-ref  frame)
                  (resume-pc     frame)
                  (frame-aux     frame)))



(defun frame-set-operand-stack  (op-stack frame) 
  (declare (xargs :guard (wff-call-frame frame)))   
      (make-frame (return-pc frame)
                  op-stack
                  (locals        frame)
                  (method-ptr    frame)
                  (sync-obj-ref  frame)
                  (resume-pc     frame)
                  (frame-aux     frame)))


(defun frame-set-locals     (locals frame)    
  (declare (xargs :guard (wff-call-frame frame)))
      (make-frame (return-pc frame)
                  (operand-stack frame)
                  locals
                  (method-ptr    frame)
                  (sync-obj-ref  frame)
                  (resume-pc     frame)
                  (frame-aux     frame)))


(defun frame-set-method-ptr  (ptr frame)    
  (declare (xargs :guard (wff-call-frame frame)))
      (make-frame (return-pc frame)
                  (operand-stack frame)
                  (locals        frame)
                  ptr
                  (sync-obj-ref  frame)
                  (resume-pc     frame)
                  (frame-aux     frame)))


(defun frame-set-sync-obj-ref  (ref frame)    
  (declare (xargs :guard (wff-call-frame frame)))
      (make-frame (return-pc frame)
                  (operand-stack frame)
                  (locals        frame)
                  (method-ptr    frame)
                  ref
                  (resume-pc     frame)
                  (frame-aux     frame)))


;;; Sat Mar 19 13:04:15 2005. 
;;;
;;; In order to talk about safety condition for executing RETURN instruction,
;;; we need to add a new field to the call frame to character the condition. 
;;; 
;;; (Or we could collect a trace and talk about safety condition on the trace?
;;;

(defun frame-set-resume-pc  (resume-pc frame)    
  (declare (xargs :guard (wff-call-frame frame)))
      (make-frame (return-pc frame)
                  (operand-stack frame)
                  (locals        frame)
                  (method-ptr    frame)
                  (sync-obj-ref  frame)
                  resume-pc
                  (frame-aux     frame)))


(defun frame-set-aux  (aux frame)    
  (declare (xargs :guard (wff-call-frame frame)))
      (make-frame (return-pc frame)
                  (operand-stack frame)
                  (locals        frame)
                  (method-ptr    frame)
                  (sync-obj-ref  frame)
                  (resume-pc     frame)
                  aux))

;;; (i-am-here) ;; Sat Mar 19 13:04:12 2005

;; It is possible for us to represent method-ptr as an pointer 
;; but since we don't care efficiency, we leave it as a symbolic reference
;; how to use the method-ptr to find the code to execute will be defined.
;; 
;; In KVM, after symbolic reference is resolved for once, it is replaced with a
;; pointer to the heap obj that represent the method.
;; 

;; there are several uses of the method-ptr. 
;;
;;   1. Used in the instructions such as new, putstatic, invokevirtual to refer
;;      to a method, to be resolved, may cause the loading of new classes
;;
;;   2. Used in the call frame to indicate the current method being executed, 
;;      assumed to be resolved, will not cause loading of new classes
;;

;;
;; operand-stack are a list of values, as in jvm-type-value
;; locals are a list of values, 
;;    note: storing long and double locals will
;;   occupy two slots.
;;

;; THREAD-STATE ... several state ... defined by KVM thread.h

;; enum { 
;;    THREAD_JUST_BORN = 1,     /* Not "start"ed yet */
;;    THREAD_ACTIVE = 2,        /* Currently running, or on Run queue */
;;    THREAD_SUSPENDED = 4,     /* Waiting for monitor or alarm */
;;    THREAD_DEAD = 8,          /* Thread has quit */
;;    THREAD_MONITOR_WAIT = 16,
;;    THREAD_CONVAR_WAIT = 32,
;;    THREAD_DBG_SUSPENDED = 64
;; } state;

;; we may only use some of them. 

;; THREAD-REF is the reference to the java-visible representation of the
;; Thread.  A number into the <JavaHeap>


;; The following functions are for manipulating the thread-table and threads.



; ** from jvm-thread.lisp **
 (defun wff-thread-table (thread-table)
  (if (not (consp thread-table)) t
    (and (wff-thread (car thread-table))
         (wff-thread-table (cdr thread-table)))))


(defun thread-by-id (id thread-table)
  (declare (xargs :guard (wff-thread-table thread-table)))
  (if (not (consp thread-table))
      nil
    (if (equal (thread-id (car thread-table)) id)
        (car thread-table)
      (thread-by-id id (cdr thread-table)))))

;; it is easy to go from thread-id to thread-ref, it is hard to go from
;; thread-ref to thread-id, since in the thread-obj itself, there is no field
;; to record which VM thread is associated with it.

;; we could add a field in specific info field of a thread-obj.
;; currently we chose to search the thread-table for the right thread with thread-ref.

;; in real jvm, thread id is THE reference itself.

(defun thread-id-by-ref (thread-ref threads)
  (declare (xargs :guard (wff-thread-table threads)))
  (if (not (consp threads))
      -1
    (if (equal (thread-ref (car threads)) thread-ref)
        (thread-id (car threads))
      (thread-id-by-ref thread-ref (cdr threads)))))


(defun replace-thread-table-entry (old-thread new-thread old-thread-table)
  (declare (xargs :guard (and (wff-thread old-thread)
                              (wff-thread new-thread)
                              (wff-thread-table old-thread-table)
                              (equal (thread-by-id (thread-id old-thread)
                                                   old-thread-table)
                                     old-thread)
                              (equal (thread-id old-thread) 
                                     (thread-id new-thread)))))
  (if (not (consp old-thread-table))
      old-thread-table
    (if (equal (car old-thread-table) old-thread)
        (cons new-thread (cdr old-thread-table))
      (cons (car old-thread-table) 
            (replace-thread-table-entry old-thread new-thread (cdr old-thread-table))))))

;********************
(defun add-thread-entry (new-thread tt)
  (cons new-thread tt))

(defun make-init-operand-stack () 
  nil)

(defun new-thread-id (tt)
  (len tt))

;************************
(defun add-no-dup (flag fl)
  (if (mem flag fl)
      fl
    (cons flag fl)))

(defun set-thread-state-flag (flag thread)
  (declare (xargs :guard (wff-thread thread)))
  (let* ((state (thread-state thread))
         (new-state (add-no-dup flag state)))
    (thread-set-state new-state thread)))

(defun remove-all (flag fl)
  (if (not (consp fl))
      nil
    (if (equal (car fl) flag)
        (remove-all flag (cdr fl))
      (cons (car fl) (remove-all flag (cdr fl))))))

(defun remove-thread-state-flag (flag thread)
  (declare (xargs :guard (wff-thread thread)))
  (let* ((state (thread-state thread))
         (new-state (remove-all flag state)))
    (thread-set-state new-state thread)))
    

;**********************
(defun set-thread-state-by-id (tid status s)
  (declare (xargs :guard (and (wff-state s)
                              (wff-thread-table s))))
  (let* ((old-thread-table (thread-table s))
         (old-thread (thread-by-id tid old-thread-table))
         (new-thread (thread-set-state (list status) old-thread))
         (new-thread-table (replace-thread-table-entry old-thread new-thread
                                                       old-thread-table)))
    (state-set-thread-table new-thread-table s)))



;**********************
(defun buildThread (thread-ref s)
  (declare (xargs :guard (wff-state s)))
  (let* ((tt  (thread-table s))
         (nid (new-thread-id tt))
         (new-thread (make-thread nid
                                  0   ;; saved pc ;; first to be executed instruction
                                  nil
                                  '(thread_just_born)
                                  -1  ;; indicate waiting no monitor 
                                  0   ;; monitor depth 0
                                  thread-ref))
         (new-tt (add-thread-entry new-thread tt)))
    (mv nid (state-set-thread-table new-tt s))))


;************************
(defun getVMthread (thread-ref s)
  (declare (xargs :guard (and (wff-state s)
                              (wff-thread-table (thread-table s)))))
  (let ((tid (thread-id-by-ref thread-ref (thread-table s))))
    (if (equal tid -1) 
        (buildThread thread-ref s)
      (mv tid s))))



(defun thread-exists? (x tt)
  (declare (xargs :guard (wff-thread-table tt)))
  (thread-by-id x tt))

(defun current-thread-exists? (s)
  (declare (xargs :guard (and (wff-state s)
                              (wff-thread-table (thread-table s)))))
   (thread-exists? (current-thread s) (thread-table s)))



;----------------------------------------------------------------------

;; (in-theory (enable make-frame return-pc operand-stack locals method-ptr
;;                   sync-obj-ref wff-call-frame))


(defthm frame-accessor
  (let ((s1 (make-frame rpc os lc mp sf mpc aux)))
    (and (equal (return-pc s1) rpc)
         (equal (operand-stack s1) os)
         (equal (locals s1)     lc)
         (equal (method-ptr s1) mp)
         (equal (resume-pc s1) mpc)
         (equal (sync-obj-ref s1) sf)
         (equal (frame-aux s1) aux))))


;; (defthm wff-call-frame-make-frame
;;   (wff-call-frame (make-frame rpc os lc mp sf)))

;----------------------------------------------------------------------
(acl2::set-verify-guards-eagerness 2)

(defun collect-thread-id (tt)
  (declare (xargs :guard (wff-thread-table tt)))
  (if (not (consp tt))
      nil
    (cons (thread-id (car tt))
          (collect-thread-id (cdr tt)))))

;; (i-am-here)
(defun unique-id-thread-table (tt)
  (declare (xargs :guard (wff-thread-table tt)))
  (nodup-set (collect-thread-id tt)))

;----------------------------------------------------------------------

; Wed Jan  7 23:25:42 2004 new addition
;; (in-theory (disable make-thread thread-id thread-saved-pc thread-call-stack
;;                     thread-mdepth thread-mref thread-ref thread-state))
;; 
;; This break jvm-frame-manipulation-primitives.lisp

;----------------------------------------------------------------------

; Thu Jan  8 15:55:30 2004
;
; Move some properties of replace-thread-table-entry here??
; or into a separate file? 
;


(acl2::set-verify-guards-eagerness 2)

(defun method-stackMap (Method)
  (declare (xargs :guard (and (wff-method-decl method)
                              (wff-code (method-code method)))))
  (code-stackmaps (method-code method)))

(defun method-maxStack (Method)
  (declare (xargs :guard (and (wff-method-decl method)
                              (wff-code (method-code method)))))
   (code-max-Stack (method-code method)))

(defun method-maxLocals (Method)
  (declare (xargs :guard (and (wff-method-decl method)
                              (wff-code (method-code method)))))
   (code-max-local (method-code method)))

(defun method-handlers (Method)
  (declare (xargs :guard (and (wff-method-decl method)
                              (wff-code (method-code method)))))
   (code-handlers (method-code method)))

(acl2::set-verify-guards-eagerness 0)

;; Mon Oct 25 16:39:49 2004

;----------------------------------------------------------------------

;; (defun isThreadAlive (thread)
;;   (declare (xargs :guard (wff-thread thread)))
;;   (or (mem 'thread_suspended (thread-state thread))
;;       (mem 'thread_active    (thread-state thread))))

;; (defun areAliveThreads1 (threads)
;;   (declare (xargs :guard (wff-thread-table threads)))
;;   (if (not (consp threads))
;;       nil
;;     (or (isThreadAlive (car threads))
;;         (areAliveThreads1 (cdr threads)))))

;; ;; it is possible to have suspended thread, but no active thread.

;; (defun areAliveThreads (s)
;;   (declare (xargs :guard (and (wff-state s)
;;                               (wff-thread-table (thread-table s)))))
;;   (let ((tt (thread-table s)))
;;     (areAliveThreads1 tt)))


;; ;; tmp implementation: reschedule 
;; (defun reschedule (s) 
;;   (declare (xargs :guard t))
;;   s)

;; ;; tmp implementation: terminate 
;; (defun terminate (s) 
;;   (declare (xargs :guard t))
;;   s)

;; First leave these in both m6-bytecode.lisp and djvm-bytecode.lisp!! 

;----------------------------------------------------------------------
