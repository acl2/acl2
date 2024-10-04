(in-package "DJVM")
(include-book "../DJVM/consistent-state")
(include-book "../DJVM/consistent-state-to-sig-state")
(include-book "../DJVM/INST/base-djvm-functions")
(include-book "../BCV/typechecker-simple")
(include-book "../BCV/typechecker-ext")
(include-book "../BCV/bcv-good-env-encapsulate")
(include-book "../BCV/good-scl-strong-encapsulate")
;;
;; Tue Dec 20 11:09:21 2005. basically, we want to assert that DJVM is stepwise
;; compatible with the BCV's prediction.
;;

;;
;; We can assume consistent-state, even consistent-state-obj-init!!!
;;

;;
;; frameIsAssignable StackFrame MapFrame Environment)
;;
;----------------------------------------------------------------------

;;
;; (i-am-here)
;;


(acl2::set-verify-guards-eagerness 0)


(defun method-is-verified (method-ptr scl)
  (let* ((class-name (method-ptr-classname method-ptr))
         (method-name (method-ptr-methodname method-ptr))
         (method-args (method-ptr-args-type method-ptr))
         (method-returntype (method-ptr-returntype method-ptr)))
    (mv-let (class-exist curClass-static)
            (class-by-name-s class-name scl)
            (mv-let 
             (method-exist  curMethod-static)
             (jvm::method-by-name-s method-name 
                                    method-args 
                                    method-returntype
                                    (methods-s curClass-static))
             (and class-exist
                  method-exist
                  (BCV::bcv-simple-method  curClass-static 
                                           curMethod-static
                                           (bcv::collect-sig-frame-vector-for-method 
                                            curClass-static
                                            curMethod-static 
                                            scl)
                                           scl))))))

(defun class-loaded-from (classname cl scl)
  (let* ((curClass (class-by-name classname cl)))
    (mv-let (class-exist curClass-static)
            (class-by-name-s classname scl)
            (and class-exist
                 (class-is-loaded-from-helper
                  curClass
                  curClass-static)))))



(defun method-loaded-from (method-ptr cl scl)
  (let* ((class-name (method-ptr-classname method-ptr))
         (method-name (method-ptr-methodname method-ptr))
         (method-args (method-ptr-args-type method-ptr))
         (method-returntype (method-ptr-returntype method-ptr)))
    (mv-let 
     (class-exist curClass-static)
     (class-by-name-s class-name scl)
     (mv-let 
      (method-exist  curMethod-static)
      (jvm::method-by-name-s method-name 
                             method-args 
                             method-returntype
                             (methods-s curClass-static))
      (and class-exist
           method-exist
           (equal (runtime-method-rep curMethod-static
                                      class-name)
                  (deref-method method-ptr cl)))))))



(defun consistent-frame-bcv0 (method-ptr cl scl)
  (and (class-loaded-from (method-ptr-classname method-ptr) cl scl)
       (method-loaded-from method-ptr cl scl)
       (method-is-verified method-ptr scl)))



(defun sig-frame-compatible-with-recorded (pc sig-frame stack-maps scl)
  (bcv::frameisassignable sig-frame
                          (bcv::searchStackFrame 
                           pc 
                           (bcv::stack-map-wrap stack-maps))
                          (fake-env scl)))
                                                 

(defun stack-maps-witness (method-ptr scl)
  (let*  ((class-name (method-ptr-classname method-ptr))
          (method-name (method-ptr-methodname method-ptr))
          (method-args (method-ptr-args-type method-ptr))
          (method-returntype (method-ptr-returntype method-ptr)))
    (mv-let 
     (class-exist curClass-static)
     (class-by-name-s class-name scl)
     (declare (ignore class-exist))
     (mv-let 
      (method-exist  curMethod-static)
      (jvm::method-by-name-s method-name 
                             method-args 
                             method-returntype
                             (methods-s curClass-static))
      (declare (ignore method-exist))
      (bcv::collect-sig-frame-vector-for-method curClass-static
                                                curMethod-static 
                                                scl)))))


;;; the problem that in M6, the PC is not maintained in the frame but as a part
;;; of the state.  which make the reasoning about consistent-callee-frame-bcv 
;;; difficult. 
;;; 
;;; If the current thread is active, then, it is current (pc s)
;;; otherwise, it is "saved-pc" in the current thread. 

(defun consistent-callee-frame-bcv (pc frame hp hp-init cl scl)
  (let* ((method-ptr (method-ptr frame))
         (djvm-sig-frame (frame-sig frame cl hp hp-init)))
    (and (consistent-frame-bcv0 method-ptr cl scl)
         (bcv::searchStackFrame 
          pc 
          (bcv::stack-map-wrap (stack-maps-witness method-ptr scl)))
         (sig-frame-compatible-with-recorded
          pc 
          djvm-sig-frame 
          (stack-maps-witness method-ptr scl)
          scl))))


(defun consistent-caller-frame-bcv (caller return-type hp hp-init cl scl)
  (let* ((method-ptr (method-ptr caller))
         (djvm-sig-frame (frame-sig caller cl hp hp-init)))
    (and (consistent-frame-bcv0 method-ptr cl scl) 
         ;; method is verified 
         (sig-frame-compatible-with-recorded 
          (resume-pc caller)
          (BCV::TYPETRANSITION  
           ;; push the return-type onto the operand stack to match with bcv's
           ;; assumption.
           nil nil  return-type djvm-sig-frame)
          (stack-maps-witness method-ptr scl)
          scl))))


;----------------------------------------------------------------------
;;                CONSISTENT-ADJACENT-FRAME
;;                (CALLER CALLEE CL)
;;                (DECLARE
;;                 (XARGS
;;                   :GUARD (CONSISTENT-ADJACENT-FRAME-GUARD CALLER CALLEE CL)))
;;                (AND
;;                 (EQUAL (RETURN-PC CALLEE)
;;                        (RESUME-PC CALLER))
;;                 (VALID-OFFSET-INTO
;;                      (RETURN-PC CALLEE)
;;                      (METHOD-CODE (DEREF-METHOD (METHOD-PTR CALLER) CL)))
;;                 (<=
;;                   (+ (LEN (OPERAND-STACK CALLER))
;;                      (TYPE-SIZE (METHOD-PTR-RETURNTYPE (METHOD-PTR CALLEE))))
;;                   (METHOD-MAXSTACK (DEREF-METHOD (METHOD-PTR CALLER)
;;                                                  CL)))))

(defun return-type-callee (frame)
  (method-ptr-returntype (method-ptr frame)))


(defun consistent-call-stack-bcv1 (cs hp hp-init cl scl)
    (if (endp cs) t
      (if (endp (cdr cs)) t
        (and (consistent-caller-frame-bcv (cadr cs)
                                          (return-type-callee (car cs))
                                          hp hp-init cl scl)
             (consistent-adjacent-frame (cadr cs)
                                        (car cs) cl)
             (consistent-call-stack-bcv1 (cdr cs) hp hp-init cl scl)))))


(defun consistent-thread-entry-bcv (thread pc curthread hp hp-init cl scl)
  (if (equal (thread-id thread) curthread)
      (and (consistent-callee-frame-bcv pc (car (thread-call-stack thread))
                                        hp hp-init cl scl)
           (consistent-call-stack-bcv1 (thread-call-stack thread)
                                       hp hp-init cl scl))
    (and (consistent-callee-frame-bcv  (thread-saved-pc thread)
                                       (car (thread-call-stack thread))
                                       hp hp-init cl scl)
         (consistent-call-stack-bcv1 (thread-call-stack thread)
                                     hp hp-init cl scl))))

;; because our choice, this is complicated
;; if the thread is the current thread, the (pc s) records the next instruction
;; if the thread is not active, the (save-pc (top-frame ...)) is the next
;; instruction
;; for caller, the next instruction is (resume-pc frame) ... 

;----------------------------------------------------------------------

(defun consistent-thread-table-bcv (threads pc curthread hp hp-init cl scl)
  (if (endp threads) t
    (and (consistent-thread-entry-bcv 
          (car threads) pc curthread hp hp-init cl scl)
         (consistent-thread-table-bcv (cdr threads) pc curthread hp hp-init cl scl))))
                                      
;----------------------------------------------------------------------

;;;
;;; I don't want to guard verify these functions definitions. 
;;; 
;;; However, if they occur as part of the JVM operation. we have to verify
;;; those!!! 
;;; 

(defun consistent-state-bcv-on-track (s)
  (and (bcv::good-scl-strong (env-class-table (env s)))
       (consistent-thread-table-bcv 
        (thread-table s)
        (pc s)
        (current-thread s)
        (heap s)
        (heap-init-map (aux s))
        (instance-class-table s)
        (env-class-table (env s)))))

;----------------------------------------------------------------------






