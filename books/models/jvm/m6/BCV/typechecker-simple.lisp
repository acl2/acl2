(in-package "BCV")
(include-book "typechecker")

;; this is a very simple typechecker that takes a list of instructions and an
;; association list that maps instructions to the type state for executing the
;; instruction in. 

;; The bytecode verifier checks that, for each instruction
;;
;; 1. It is safe to execute the instruction in the recorded type state
;;
;; 2. All possible resulting state are compatible with the state registered in
;;    the associate list. 
;; 
;; 3. The type state associated with first instruction is compatible with the
;;    type state constructed from the method declarations! 
;;

;;;
;;; the problem is that we don't want to write a different set of 
;;;
;;; check-XXX 
;;;
;;; and 
;;; 
;;; execute-XXXX 

;;;
;;; instead we will create a fake-env with sig-vector
;;;
;;; which we will be able to prove easily that 
;;;  
;;; a DJVM step maintains the state compatible with the bcv state! 
;;; 

;;;;
;;;;   maybe we don't need such a bcv?
;;;;

;;;;
;;;;  Let's proved program verified this way, will execute safely! 
;;;;

;;;;
;;;; We will add an assertion that a consistent state is in sync with 
;;;; BCV state! 
;;;; 
;;;; We may not need to modify consistent-state after all.  We can leave the
;;;; additional assertion not as part of consistent-state but as an additonal
;;;; assertion. So that the consistent-state really asserts about inherent
;;;; consistency, which the matching BCV asserts something about the
;;;; predictability. Thu Dec 22 15:34:13 2005
;;;;
;;;;

;; (MAKEENVIRONMENT CLASS METHOD RETURNTYPE
;;                                       MERGEDCODE MAXSTACK HANDLERS CL))

;; (defun fake-env2 (stack-maps env)
;;   (makeenvironment (classEnvironment env)
;;                    (methodEnvironment env)
;;                    (methodReturnType (methodEnvironment env))
;;                    stack-maps
;;                    (maxstackenvironment env)
;;                    (exceptionHandlers env)
;;                    (classtableEnvironment env)))
  
(defun stack-map-wrap (stack-maps)
  (if (endp stack-maps)
      nil
    (cons (makeStackMap (car stack-maps))
          (stack-map-wrap (cdr stack-maps)))))


;; (defun bcv-simple-method1 (code stack-maps env)
;;   (if (endp code) nil ;; testing could have caught this. 
;;     (let* ((inst (car code)))
;;       (and (instructionIsTypeSafe inst env
;;                                   (searchStackFrame (instrOffset inst)
;;                                                     (stack-map-wrap stack-maps)))
;;            (mv-let (nextStackFrame exceptionStackFrame)
;;                    (sig-do-inst inst env
;;                                 (searchStackFrame (instrOffset inst)
;;                                                   (stack-map-wrap stack-maps)))
;;                    (and (instructionSatisfiesHandlers 
;;                          env
;;                          (instrOffset inst)
;;                          exceptionStackFrame)
;;                         (or (equal nextStackFrame 'aftergoto)
;;                             (and (consp (cdr code))
;;                                  (not (isEnd (cadr code)))
;;                                  (frameIsAssignable nextStackFrame
;;                                                     (searchStackFrame 
;;                                                      (instrOffset (cadr
;;                                                                    code))
;;                                                      (stack-map-wrap stack-maps))
;;                                                     env)))
;;                         (bcv-simple-method1 (cdr code) stack-maps env)))))))



(defun bcv-simple-method1 (code stack-maps env)
  (if (endp code) t ;; testing could have caught this. 
    (let* ((inst (car code)))
      (and (instructionIsTypeSafe inst env
                                  (searchStackFrame (instrOffset inst)
                                                    (stack-map-wrap stack-maps)))
           (mv-let (nextStackFrame exceptionStackFrame)
                   (sig-do-inst inst env
                                (searchStackFrame (instrOffset inst)
                                                  (stack-map-wrap stack-maps)))
                   (and (instructionSatisfiesHandlers 
                         env
                         (instrOffset inst)
                         exceptionStackFrame)
                        (or (equal nextStackFrame 'aftergoto)
                            (and (consp (cdr code))
                                 (not (isEnd (cadr code)))
                                 (frameIsAssignable nextStackFrame
                                                    (searchStackFrame 
                                                     (instrOffset (cadr
                                                                   code))
                                                     (stack-map-wrap stack-maps))
                                                    env)))
                        (bcv-simple-method1 (cdr code) stack-maps env)))))))


;; because of the invoke.. we will use a env with a full vector!! 
                                                

;----------------------------------------------------------------------

(defun bcv-simple-method (class method stack-maps cl)
  (and (iswellformedcodeattribute class method)
       (let* ((framesize  (framesize method class))
              (maxstack   (maxstack method class))
              (parsedcode (parsedcode method class))
              (handlers   (handlers method class))
              (MERGEDCODE (MERGESTACKMAPANDCODE STACK-MAPS PARSEDCODE))
              (STACKFRAME
               (METHODINITIALSTACKFRAME CLASS METHOD FRAMESIZE))
              (RETURNTYPE (METHODRETURNTYPE METHOD))
              (ENVIRONMENT
               (MAKEENVIRONMENT CLASS METHOD RETURNTYPE
                                mergedcode
                                MAXSTACK HANDLERS CL)))
         (AND (HANDLERSARELEGAL ENVIRONMENT)
              (consp parsedcode)
              (not (isEnd (car parsedcode)))
              (frameIsAssignable stackframe
                                 (searchStackFrame  
                                  (instrOffset (car parsedcode))
                                  (stack-map-wrap stack-maps))
                                 environment)
              (bcv-simple-method1 parsedcode stack-maps environment)))))

;----------------------------------------------------------------------


;----------------------------------------------------------------------


(defun bcv-simple-methods (class methods class-stack-maps cl)
  (if (endp methods) t
    (prog2$ 
     (cw "      method ~p0 (~p1)~%~%" 
         (methodname (car methods))
         (methodparameters (car methods)))
     (if (or (mem '*abstract*  (methodAccessFlags (car methods)))
             (mem '*native*  (methodAccessFlags (car methods))))
         (bcv-simple-methods class (cdr methods) class-stack-maps cl)
       (and (bcv-simple-method class (car methods)
                               (binding (car methods) class-stack-maps)
                               cl)
            (bcv-simple-methods class (cdr methods) class-stack-maps cl))))))


;----------------------------------------------------------------------


(defun bcv-simple-classes (l class-stack-maps-more cl)
  (if (endp l) t
    (prog2$ 
     (cw "class ~p0~%~%" (classClassName (car l)))
     (and (bcv-simple-methods
           (car l) 
           (classMethods (car l))
           (binding (car l) class-stack-maps-more)
           cl)
          (bcv-simple-classes (cdr l) class-stack-maps-more cl)))))

;----------------------------------------------------------------------










           
