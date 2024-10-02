(in-package "M6")
(include-book "../M6-DJVM-shared/jvm-semantic-primitives-2")
(include-book "../M6/m6-state")
(include-book "../M6/m6-thread")
(include-book "../M6/m6-object-type-hierachy")
(include-book "../M6/m6-frame-manipulation-primitives")
(include-book "../M6/m6-linker")
(include-book "../M6/m6-thread-primitives")
(include-book "../M6/m6-monitor-failure-as-fatalError")
(include-book "../M6/m6-object-manipulation-primitives")
(include-book "../M6/m6-static-initializer")


;;
;; set the return pc to KILL_THREAD
;; so when a corresponding return is executed, system know to kill thread. 
;; when there is no active thread, program terminates.
;;

;; for those call back functions, we may not want to use same operation to get
;; access the state. topStack etc. has guards that works only on valid
;; opstacks. 

;;
;; We want to share a major portion of code between Defensive JVM and Regular
;; JVM, we need call back function behave the same. we need Native method
;; behave properly if they manipulate the operand stack.
;;

;; Do I want to get into this?? 
;; (defun topStackAsRef (

;;
;; Mon Dec 29 00:32:23 2003

;;(acl2::set-verify-guards-eagerness 0)

(defun initInitialThreadBehavior (s) 
  (let* ((array-ref (topStack s))
         (classname (secondStack s))
         (main-method-ptr (make-method-ptr classname "main" 
                                           '((array "java.lang.String"))
                                           'void))
         (mainMethod (getSpecialMethod main-method-ptr s)))
    (if (equal mainMethod nil)
        (stopThread (alertUser "does not have a main function" s))
      (if (not (mem '*public* (method-accessflags mainMethod)))
          (stopThread (alertUser "main must be public" s))
        (let* (;;(class-ref (class-ref (class-by-name classname
               ;;                                     (instance-class-table s))))
               (locals (app (list ;; class-ref ;; Thu Nov 18 12:12:12 2004
                                  array-ref)
                            (fill-top (- (method-maxlocals mainMethod) 1))))
               (s1 (pushFrame main-method-ptr locals s))
               (s2 (set-top-frame-return-pc 'KILL_THREAD s1)))
          (if (mem '*synchronized* (method-accessflags mainMethod))
              ;; why need a synchronize object recorded on the frame??  because
              ;; we need to release the monitor when we return from the
              ;; methods.
              (let* ((class-obj-ref (class-ref-by-name classname s2))
                     (s3 (set-curframe-sync-obj class-obj-ref s2)))
                (mv-let (mstatus s4)
                    (monitorEnterX class-obj-ref s3)
                    (declare (ignore mstatus))
                    s4))
            (set-curframe-sync-obj -1 s2))))))) ;; use -1 to indicate null pointer.


(defun initThreadBehaviorFromThread (s)
  (let* ((s1 (popFrame s))
         (sync-obj-ref (sync-obj-ref (current-frame s1))))
    (if (not (equal sync-obj-ref -1))
        (mv-let (mstatus s2)
                (monitorEnterX sync-obj-ref s1)
                (declare (ignore mstatus))
                s2)
     s1)))
                


(defun interruptedGetOutput1Behavior (s)
  (prog2$ (acl2::debug-print "interruptedGetOutput1Behavior called")
          (mv-let (os-ref s1)
                  (new-instance "java.io.PrintStream" (popFrame s))
                  (pushStack os-ref s1))))


(defun  newInstanceReturnObject (s) 
  (popFrame s))



(defun searchForFuncPtr1 (l)
  (if (endp l)
      nil
    (if (callback-func-ptr? (car l))
        (car l)
      (searchForFuncPtr1 (cdr l)))))


(defun searchForFuncPtr (s) 
  (let* ((cur-thread (thread-by-id (current-thread s) (thread-table s)))
         (operand-stack (operand-stack (top (thread-call-stack cur-thread)))))
    (searchForFuncPtr1 operand-stack))) 


(defun invoke-CUSTOMCODE (s)
  (let* ((call-back-func (searchForFuncPtr s))
         (funcname (callback-funcname call-back-func)))
    (cond ((equal funcname '*runClinit*) 
              (runClinit s))
          ((equal funcname '*initInitialThreadBehavior*)
           (initInitialThreadBehavior s))
          ((equal funcname '*newInstanceReturnObject*)
           (newInstanceReturnObject s))
          ((equal funcname  '*initThreadBehaviorFromThread*)
           (initThreadBehaviorFromThread s))
          ((equal funcname  '*interruptedGetOutput1Behavior*)
           (interruptedGetOutput1Behavior s))
          (t s)))) ;; so far unknown

