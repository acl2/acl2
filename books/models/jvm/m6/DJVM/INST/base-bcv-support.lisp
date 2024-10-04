(in-package "DJVM")
(include-book "base")
(include-book "base-consistent-state")
(include-book "../../BCV/typechecker")

; supporting lemma for reasoning about (frame-sig ....) 



(in-theory (disable BCV::isMatchingType))

(in-theory (disable bcv::frameStack bcv::frameLocals bcv::frameFlags
                   locals operand-stack bcv::nth1OperandStackIs  
                   bcv::pushOperandStack popStack
                   nullp
                   CODE-STACKMAPS ENV-SIG HEAP-INIT-MAP 
                   MAKEENVIRONMENT BCV::ARRAYELEMENTTYPE
                   BCV::POP frame-sig BCV::SIZEOF
                   bcv::classtableEnvironment
                   BCV::popmatchingtype
                   BCV::MAXSTACKENVIRONMENT
                   bcv::make-sig-frame
                   value-sig
                   make-sig-frame))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;  (defthm bcv-check-aaload-ensures-djvm-check-aaload
;;    (implies (and (bcv::check-aaload inst (env-sig s) 
;;                                     (frame-sig  (current-frame s)
;;                                                 (instance-class-table s)
;;                                                 (heap s)
;;                                                 (heap-init-map (aux s))))
;;                  (not (mem '*native* (method-accessflags (current-method s))))
;;                  (consistent-state s))
;;             (check-aaload inst s)))
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;----------------------------------------------------------------------
;;
;; (defun frame-push-value-sig (v sig-frame)
;;   "push v onto the sig-operand-stack of sig-frame"
;;   (bcv::make-sig-frame 
;;       (bcv::frameLocals sig-frame)
;;       (push v (bcv::frameStack sig-frame))
;;       (bcv::frameFlags sig-frame)))
;;
;;
;; (defun frame-pop-opstack (frame)
;;   "pop one value/slot off the opstack of sig-frame"
;;   (frame-set-operand-stack 
;;     (pop (operand-stack frame))
;;     frame))
;;
;; (defun frame-top-opstack (frame)
;;   (top (operand-stack frame)))
;;
;; moved to base.lisp
;;
;----------------------------------------------------------------------

;----------------------------------------------------------------------
;;
;;
;; STRATEGY: Transforming a (frame-sig (current-frame s) ... )
;;           into a sequence of (frame-push-sig (value-sig (topStack (.... )))
;;                                 (frame-push-sig .....
;;                                     ....
;;                                     (frame-sig (current-frame (popStack ......)) ....)))
;;
;; 
;; This way, BCV-check can be expressed on (value-sig (topStack ...)) natually
;; 
;----------------------------------------------------------------------


(defthm bcv-make-sig-frame-normalize
   (equal (bcv::make-sig-frame l s f)
          (make-sig-frame l s f))
   :hints (("Goal" :in-theory (enable make-sig-frame bcv::make-sig-frame))))


(local 
 (defthm make-sig-frame-cons-is-frame-push-value-sig
   (equal (make-sig-frame l (cons x stack) flags)
          (frame-push-value-sig x (make-sig-frame l stack flags)))
   :hints (("Goal" :in-theory (enable make-sig-frame 
                                      bcv::make-sig-frame
                                      frame-push-value-sig
                                      bcv::frameFlags bcv::frameLocals
                                      bcv::frameStack)))))


(defthm bcv-make-sig-frame-accessor
  (and (equal (bcv::frameStack  (make-sig-frame l s f)) s)
       (equal (bcv::frameLocals (make-sig-frame l s f)) l)
       (equal (bcv::frameFlags  (make-sig-frame l s f)) f))
  :hints (("Goal" :in-theory (enable make-sig-frame
                                     bcv::frameFlags bcv::frameLocals bcv::frameStack))))


(in-theory (disable frame-push-value-sig
                    frame-pop-opstack
                    frame-top-opstack))


(defthm locals-not-change-pop-opstack
  (equal (locals (FRAME-POP-OPSTACK FRAME))
         (locals frame))
  :hints (("Goal" :in-theory (enable frame-set-operand-stack 
                                     frame-pop-opstack))))

(defthm method-ptr-not-change-pop-opstack
  (equal (method-ptr (FRAME-POP-OPSTACK FRAME))
         (method-ptr frame))
  :hints (("Goal" :in-theory (enable frame-set-operand-stack 
                                     frame-pop-opstack))))

(defthm frame-top-opstack-normalize
  (equal (CAR (OPERAND-STACK FRAME))
         (frame-top-opstack frame))
  :hints (("Goal" :in-theory (enable frame-top-opstack))))
              
;;(i-am-here)

(local 
 (defthm operand-stack-frame-set-opstack
  (equal (operand-stack (frame-set-operand-stack opstack frame))
        opstack)
  :hints (("Goal" :in-theory (enable make-frame frame-set-operand-stack
                                     operand-stack)))))

(local (in-theory (enable pop)))

(defthm frame-pop-opstack-normalize
  (equal (CDR (OPERAND-STACK FRAME))
         (operand-stack (frame-pop-opstack frame)))
  :hints (("Goal" :in-theory (e/d (pop frame-pop-opstack)))))

(local (defthm canPopCategory1-consp-stk
         (implies (canPopCategory1 stk)
                  (equal (opstack-sig stk cl hp hp-init method-ptr)
                         (cons (value-sig (car stk) cl hp hp-init
                                          method-ptr)
                               (opstack-sig (cdr stk)
                                            cl hp hp-init method-ptr))))
         :hints (("Goal" :in-theory (e/d (canPopCategory1) ())))))

;;(i-am-here) ;; Sun Jul 31 12:38:44 2005


(defthm frame-aux-frame-pop-opstack-no-change
  (equal (jvm::frame-aux (frame-pop-opstack frame))
         (jvm::frame-aux frame))
  :hints (("Goal" :in-theory (enable frame-pop-opstack
                                     make-frame
                                     jvm::frame-aux
                                     frame-set-operand-stack))))
                                     



(defthm canPopCategory1-frame-sig-lemma
   (implies (canPopCategory1 (operand-stack frame))
            (equal (frame-sig frame cl hp hp-init)
                   (frame-push-value-sig 
                    (value-sig (frame-top-opstack frame)
                               cl hp hp-init (method-ptr frame))
                    (frame-sig (frame-pop-opstack frame)
                               cl hp hp-init))))
   :hints (("Goal" :in-theory (e/d (frame-sig frame-push-value-sig)
                                   (MAKE-SIG-FRAME-CONS-IS-FRAME-PUSH-VALUE-SIG
                                    jvm::frame-aux
                                    )))))



;; (defthm canPopCategory1-frame-sig-lemma
;;    (implies (and (canPopCategory1 (operand-stack frame))
;;                  (not (equal (value-sig (frame-top-opstack frame)
;;                                         cl hp hp-init (method-ptr frame))
;;                              'uninitializedThis)))
;;             (equal (frame-sig frame cl hp hp-init)
;;                    (frame-push-value-sig 
;;                     (value-sig (frame-top-opstack frame)
;;                                cl hp hp-init (method-ptr frame))
;;                     (frame-sig (frame-pop-opstack frame)
;;                                cl hp hp-init))))
;;    :hints (("Goal" :in-theory (e/d (frame-sig frame-push-value-sig)
;;                                    (MAKE-SIG-FRAME-CONS-IS-FRAME-PUSH-VALUE-SIG)))))




;;
;; the goal is to make it easier to get (bcv::popmatchingtype (frame-sig ....)
;; easier
;;

;;;
;;; push PopStack into the s
;;;
;;; expand the meaningful portion of the operand stack! 


;; (defthm current-frame-popStack                           
;;   (implies (consistent-state s)                      
;;            (equal (frame-pop-opstack (current-frame s))  
;;                   (current-frame (popStack s))))         
;;   :hints (("Goal" :in-theory (enable popStack current-frame
;;                                      frame-pop-opstack
;;                                      frame-set-operand-stack
;;                                      popstack-of-thread))))

;; ;;; leave this here. This is part of normalization 
;; ;;; scheme that we want to use. 

;;;; moved to bcv-consistent-state.lisp



(defthm isMatchingType-INT-implies-canPopCategory1 
  (implies (bcv::isMatchingType 'INT (opstack-sig stack cl hp hp-init method-ptr) env)
           (canPopCategory1 stack))
  :hints (("Goal" :in-theory (e/d (bcv::isMatchingType) ())))
  :rule-classes :forward-chaining)



(defthm isMatchingType-INT-implies-canPopCategory1-specific-b
  (implies (bcv::isMatchingType 'INT 
                                (opstack-sig (operand-stack 
                                              (current-frame s))
                                             (instance-class-table s)
                                             (heap s)
                                             (heap-init-map (aux s))
                                             (method-ptr (current-frame s)))
                                (env-sig s))
           (canPopCategory1 (operand-stack (current-frame s))))
  :hints (("Goal" :in-theory (e/d (bcv::isMatchingType) ()))))



(defthm isAssignable-INT-INT-f
  (implies (bcv::isAssignable type 'INT env)
           (equal (equal type 'INT) t))
  :rule-classes :forward-chaining)


(local (defthm isMatchingType-implies-isAssignable-INT
  (implies (bcv::isMatchingType 'INT
                               (opstack-sig stack cl hp hp-init method-ptr) env)
           (bcv::isAssignable (value-sig (car stack) cl hp hp-init method-ptr)
                             'INT env))
  :hints (("Goal" :in-theory (e/d (bcv::isMatchingType) (bcv::isAssignable))))
  :rule-classes :forward-chaining))


(local (defthm isMatchingType-INT-implies-Value-sig-INT
   (implies (bcv::isMatchingType 'INT (opstack-sig stack cl hp hp-init
                                                  method-ptr) env)
            (equal (value-sig (car stack)
                              cl hp hp-init method-ptr)
                   'INT))
   :hints (("Goal" :in-theory (disable bcv::isAssignable bcv::isMatchingType
                                       value-sig opstack-sig)))))



(defthm isMatchingType-INT-implies-Value-sig-INT-specific
   (implies (bcv::isMatchingType 'INT (opstack-sig (operand-stack frame) cl hp hp-init
                                                  method-ptr) env)
            (equal (value-sig (frame-top-opstack frame)
                              cl hp hp-init method-ptr)
                   'INT))
   :hints (("Goal" :in-theory (e/d (frame-top-opstack)
                                   (bcv::isAssignable bcv::isMatchingType
                                                      frame-top-opstack-normalize
                                                     value-sig opstack-sig)))))



(defthm isMatchingType-INT-implies-Value-sig-INT-specific-2
   (implies (bcv::isMatchingType 'INT (opstack-sig (operand-stack
                                                    (current-frame s)) cl hp hp-init
                                                  method-ptr) env)
            (equal (value-sig (topStack s)
                              cl hp hp-init method-ptr)
                   'INT))
   :hints (("Goal" :in-theory (enable topStack))))





(defthm isMatchingType-INT-implies-frame-sig-is
  (implies (and (bcv::isMatchingType 'INT (opstack-sig (operand-stack (current-frame s))
                                                       (instance-class-table s)
                                                       (heap s)
                                                       (heap-init-map (aux s))
                                                       (method-ptr (current-frame s)))
                                     (env-sig s))
                (consistent-state s)
                (equal cl (instance-class-table s))
                (equal hp (heap s))
                (equal hp-init (heap-init-map (aux s)))
                (equal method-ptr (method-ptr (current-frame s))))
           (equal (frame-sig (current-frame s) 
                             cl hp hp-init)
                  (frame-push-value-sig 
                   (value-sig (topStack s)
                              cl hp hp-init method-ptr)
                   (frame-sig (current-frame (popStack s))
                              (instance-class-table s)
                              (heap s)
                              (heap-init-map (aux s))))))
  :hints (("Goal" :in-theory (e/d  (topStack top)
                                   (frame-sig bcv::isMatchingType
                                   frame-push-value-sig  current-frame env-sig
                                   opstack-sig value-sig popStack
                                   frame-pop-opstack
                                   method-ptr
                                   aux heap-init-map)))))

;;;
;;;
;;; we probably need the above kind of lemma for each of the primitive type
;;; and other class types. 
;;;
;;; Fri May  6 13:12:26 2005. 
;;;
;;; Maybe we can live without it. Relying on canPopCategory1 instead!! 
;;;


;;; similiarly! Tue Apr 19 22:14:15 2005
(defthm fact-about-bcv-isAssignable-4
  (NOT (BCV::ISASSIGNABLE 'LONG
                          '(ARRAY (CLASS "java.lang.Object"))
                          ENV))
  :hints (("Goal" :expand (BCV::ISASSIGNABLE 'LONG
                          '(ARRAY (CLASS "java.lang.Object"))
                          ENV))))

(defthm fact-about-bcv-isAssignable-5
  (NOT (BCV::ISASSIGNABLE 'DOUBLE
                          '(ARRAY (CLASS "java.lang.Object"))
                          ENV))
  :hints (("Goal" :expand (BCV::ISASSIGNABLE 'DOUBLE
                          '(ARRAY (CLASS "java.lang.Object"))
                          ENV))))



(defthm isMatchingType-AARRAY-implies-canPopCategory1 
  (implies (bcv::isMatchingType '(ARRAY (class "java.lang.Object")) 
                                (opstack-sig stack cl hp hp-init method-ptr) env)
           (canPopCategory1 stack))
  :hints (("Goal" :in-theory (enable bcv::isMatchingType canPopCategory1)))
  :rule-classes :forward-chaining)


(defthm isMatchingType-AARRAY-implies-canPopCategory1-specific-b
  (implies (bcv::isMatchingType '(ARRAY (class "java.lang.Object")) 
                               (opstack-sig (operand-stack (current-frame s))
                                            (instance-class-table s)
                                            (heap s)
                                            (heap-init-map (aux s))
                                            (method-ptr (current-frame s)))
                               (env-sig s))
           (canPopCategory1 (operand-stack (current-frame s)))))



(defthm bcv-isJavaAssignable-fact-1
  (not (bcv::isJavaAssignable 'uninitialized (list 'array any) env)))



(encapsulate ()
  (local (include-book "base-skip-proofs"))
  (defthm bcv-isJavaAssignable-fact-2
    (BCV::ISJAVAASSIGNABLE '(ARRAY (CLASS "java.lang.Object"))
                           '(ARRAY (CLASS "java.lang.Object"))
                           (BCV::CLASSTABLEENVIRONMENT ENV))))

;;;
;;; this needs to be fixed!  NOTE this is not true!! without some assumptions
;;; about ENV!!  We need to assert that ENV is obtained from a consistent
;;; state! via a env-sig mapping! 
;;;


(defthm bcv-isAssignable-fact-1
  (not (BCV::ISASSIGNABLE 'REFERENCE
                          '(ARRAY (CLASS "java.lang.Object"))
                          ENV))
  :hints (("Goal" :in-theory (enable bcv::isassignable)
           :expand (BCV::ISASSIGNABLE 'REFERENCE
                          '(ARRAY (CLASS "java.lang.Object"))
                          ENV))))


(defthm bcv-isAssignable-to-array-array-type-key-fact
  (implies (and (bcv::isAssignable typ '(array (class "java.lang.Object")) env)
                (not (equal typ 'null)))
           (bcv::isJavaAssignable typ '(array (class "java.lang.Object"))
                                  (bcv::classtableEnvironment env)))
  :hints (("Goal" :in-theory (e/d () (bcv::isJavaAssignable)))))


;;; note: Sun Jul 31 13:10:50 2005
;;; those theorems about some type not being 
;;;
;;; valid-sig something is not uninitializedThis!! 
;;;
;;; are not absolutely necessary!! 
;;; We not longer need those to show that push, pop something
;;; does not change the frame's FLAGS!! 
;;;

(defthm isJavaAssignable-not-equal-unintialize-key-fact
  (implies (bcv::isJavaAssignable typ any cl)
           (not (equal typ 'uninitializedThis))))

(defthm isJavaAssignable-not-equal-unintialized
  (implies (bcv::isJavaAssignable typ '(array (class "java.lang.Object")) cl)
           (not (equal typ 'uninitializedThis))))


(defthm isJavaAssignable-not-equal-unintialized-specific
  (implies (bcv::isJavaAssignable (value-sig v cl hp hp-init method-ptr) 
                                  '(array (class "java.lang.Object")) scl)
           (not (equal (value-sig v cl hp hp-init method-ptr) 'uninitializedThis))))


(defthm bcv-isAssignable-fact-x
  (not (BCV::ISASSIGNABLE NIL '(ARRAY (CLASS "java.lang.Object"))
                          ENV))
  :hints (("Goal" :in-theory (enable bcv::isassignable))))

(defthm isMatchingType-implies-isAssignable
  (implies (bcv::isMatchingType '(array (class "java.lang.Object"))
                               (opstack-sig stack cl hp hp-init method-ptr) env)
           (bcv::isAssignable (value-sig (car stack) cl hp hp-init method-ptr)
                             '(array (class "java.lang.Object")) env))
  :hints (("Goal" :in-theory (e/d (bcv::isMatchingType) (bcv::isAssignable)))))


(defthm isMatchingType-implies-isAssignable-f
  (implies (bcv::isMatchingType '(array (class "java.lang.Object"))
                               (opstack-sig stack cl hp hp-init method-ptr) env)
           (bcv::isAssignable (value-sig (car stack) cl hp hp-init method-ptr)
                             '(array (class "java.lang.Object")) env))
  :hints (("Goal" :in-theory (disable bcv::isAssignable)))
  :rule-classes :forward-chaining)



(defthm isMatchingType-implies-isAssignable-specific-b
  (implies (bcv::isMatchingType '(array (class "java.lang.Object"))
                               (opstack-sig (operand-stack frame) cl hp hp-init method-ptr) env)
           (bcv::isAssignable (value-sig (frame-top-opstack frame) cl hp hp-init method-ptr)
                             '(array (class "java.lang.Object")) env))
  :hints (("Goal" :in-theory (e/d (frame-top-opstack) (bcv::isAssignable frame-top-opstack-normalize)))))

(defthm value-sig-nullp
  (implies (nullp v)
           (equal (value-sig v cl hp hp-init method-ptr)
                  'NULL))
  :hints (("Goal" :in-theory (enable value-sig nullp))))


(defthm isJavaAssignable-not-equal-unintialized-specific-2
  (implies (bcv::isJavaAssignable (value-sig v cl hp hp-init (method-ptr
                                                              (current-frame s)))
                                  '(array (class "java.lang.Object"))
                                  (bcv::classtableEnvironment (env-sig s)))
           (not (equal (value-sig v cl hp hp-init (method-ptr (current-frame s))) 'uninitializedThis))))



(defthm isMatchingType-AARRAY-implies-frame-sig-is
  (implies (and (bcv::isMatchingType '(array (class "java.lang.Object"))
                                     (opstack-sig (operand-stack (current-frame s))
                                                  cl hp hp-init (method-ptr
                                                                 (current-frame s)))
                                    (env-sig s))
                (consistent-state s)
                (equal cl (instance-class-table s))
                (equal hp (heap s))
                (equal hp-init (heap-init-map (aux s)))
                (equal method-ptr (method-ptr (current-frame s))))
           (equal (frame-sig (current-frame s) 
                             cl hp hp-init)
                  (frame-push-value-sig 
                   (value-sig (topStack s)
                              cl hp hp-init method-ptr)
                   (frame-sig (current-frame (popStack s))
                              (instance-class-table s)
                              (heap s)
                              (heap-init-map (aux s))))))
  :hints (("Goal" :cases ((equal (value-sig (frame-top-opstack (current-frame s))
                                            (instance-class-table s)
                                            (heap s)
                                            (heap-init-map (aux s))
                                            (method-ptr (current-frame s)))
                                 'null))
           :in-theory (e/d  (topStack top)
                            (frame-sig bcv::isMatchingType
                                       frame-push-value-sig  current-frame env-sig
                                       opstack-sig value-sig popStack
                                       frame-pop-opstack
                                       method-ptr
                                       aux heap-init-map)))))


(defthm frame-stack-frame-sig-normlize
  (equal (BCV::FRAMESTACK (FRAME-SIG frame cl hp hp-init))
         (opstack-sig (operand-stack frame) cl hp hp-init (method-ptr frame)))
  :hints (("Goal" :in-theory (enable bcv::framestack frame-sig make-sig-frame))))



(defthm bcv-popMatchingType-fact-1
  (implies (equal (bcv::sizeof y) 1)
           (equal (bcv::popmatchingtype y (cons x any))
                  any))
  :hints (("Goal" :in-theory (enable bcv::popmatchingtype bcv::pop))))

(defthm bcv-popMatchingType-push-value-sig
  (implies (equal (bcv::sizeof x) 1)
           (equal  (BCV::POPMATCHINGTYPE x 
                                         (BCV::FRAMESTACK
                                          (FRAME-PUSH-VALUE-SIG y frame)))
                   (bcv::FrameStack frame)))
  :hints (("Goal" :in-theory (e/d (frame-push-value-sig bcv::pop bcv::popmatchingtype)
                                  (MAKE-SIG-FRAME-CONS-IS-FRAME-PUSH-VALUE-SIG)))))
                     

;;(i-am-here) ;; Tue Aug 16 15:55:14 2005
               
(defthm frame-pop-opstack-current-frame
  (implies (consistent-state s)
           (equal (FRAME-POP-OPSTACK (CURRENT-FRAME s))
                  (current-frame (popStack s))))
  :hints (("Goal" :in-theory (e/d (popStack frame-pop-opstack 
                                   popstack-of-thread         
                                   current-frame)
                                  (frame-pop-opstack-normalize
                                   topframe-normalization)))))




(defthm consp-bcv-frame-frame-push
  (consp (bcv::framestack (frame-push-value-sig x frame)))
  :hints (("Goal" :in-theory (e/d (frame-push-value-sig)
                                  (make-sig-frame-cons-is-frame-push-value-sig)))))



(defthm canPopCategory1-implies-consistent-state
  (implies (and (canPopCategory1 (operand-stack (current-frame s)))
                (NOT (MEM '*NATIVE*
                          (METHOD-ACCESSFLAGS (CURRENT-METHOD S))))
                (consistent-state s))
           (consistent-state (popStack s)))
  :hints (("Goal" :in-theory (e/d (topstack-guard-strong) 
                                  (canPopCategory1 op-stack-primitive-shared-guard))
           :use consistent-state-popStack)))


(local ;; check points 
 (defthm CanPop1-implies-frame-sig-is
  (implies (and (bcv::canPop1
                 '(INT (array (class "java.lang.Object")))
                 (bcv::frameStack (frame-sig (current-frame s)
                                            (instance-class-table s)
                                            (heap s)
                                            (heap-init-map (aux s))))
                 (env-sig s))
                (NOT (MEM '*NATIVE*
                          (METHOD-ACCESSFLAGS (CURRENT-METHOD S))))
                (consistent-state s))
           (equal (frame-sig (current-frame s) 
                             (instance-class-table s)
                             (heap s)
                             (heap-init-map (aux s)))
                  (frame-push-value-sig 
                   (value-sig (topStack s)
                              (instance-class-table s)
                              (heap s)
                              (heap-init-map (aux s))
                              (method-ptr (current-frame s)))
                   (frame-push-value-sig
                    (value-sig (topStack (popStack s))
                               (instance-class-table s)
                               (heap s)
                               (heap-init-map (aux s))
                               (method-ptr (current-frame s)))
                    (frame-sig (current-frame (popStack (popStack s)))
                               (instance-class-table s)
                               (heap s)
                               (heap-init-map (aux s)))))))
           :hints (("Goal" :in-theory (e/d  (topStack top)
                                            (frame-sig bcv::isMatchingType
                                                       pop
                                             frame-push-value-sig  current-frame env-sig
                                             opstack-sig value-sig canPopCategory1
                                             frame-pop-opstack bcv::frameStack
                                             method-ptr bcv::popMatchingType
                                             aux heap-init-map))))))

;;; canPop1 implies expand!! 

;; (defthm ValidTypeTransition-implies-frame-sig-is-test
;;   (implies (and (bcv::validtypetransition
;;                  (env-sig s)
;;                  '(INT INT (array (class "java.lang.Object")) INT)
;;                  any
;;                  (frame-sig (current-frame s)
;;                             (instance-class-table s)
;;                             (heap s)
;;                             (heap-init-map (aux s))))
;;                 (NOT (MEM '*NATIVE*
;;                           (METHOD-ACCESSFLAGS (CURRENT-METHOD S))))
;;                 (consistent-state s))
;;            (equal (frame-sig (current-frame s) 
;;                              (instance-class-table s)
;;                              (heap s)
;;                              (heap-init-map (aux s)))
;;                   (frame-push-value-sig 
;;                    (value-sig (topStack s)
;;                               (instance-class-table s)
;;                               (heap s)
;;                               (heap-init-map (aux s))
;;                               (method-ptr (current-frame s)))
;;                    (frame-push-value-sig
;;                     (value-sig (topStack (popStack s))
;;                                (instance-class-table s)
;;                                (heap s)
;;                                (heap-init-map (aux s))
;;                                (method-ptr (current-frame s)))
;;                     (frame-push-value-sig 
;;                      (value-sig (topStack (popStack (popStack s)))
;;                                 (instance-class-table s)
;;                                 (heap s)
;;                                 (heap-init-map (aux s))
;;                                 (method-ptr (current-frame s)))
;;                      (frame-push-value-sig 
;;                       (value-sig (topStack (popStack (popStack (popStack s))))
;;                                  (instance-class-table s)
;;                                  (heap s)
;;                                  (heap-init-map (aux s))
;;                                  (method-ptr (current-frame s)))
;;                       (frame-sig (current-frame (popStack (popStack (popStack (popStack s)))))
;;                                  (instance-class-table s)
;;                                  (heap s)
;;                                  (heap-init-map (aux s)))))))))
;;   :hints (("Goal" :in-theory (e/d  ()
;;                                    (frame-sig bcv::isMatchingType
;;                                               frame-push-value-sig  current-frame
;;                                               env-sig 
;;                                               opstack-sig value-sig canPopCategory1
;;                                               frame-pop-opstack bcv::frameStack
;;                                               method-ptr bcv::popMatchingType
;;                                               aux heap-init-map)))))

;; ;;; benchmark theorem
(defthm nth1OperandStackIs-1-frame-push-sig
  (equal (bcv::nth1OperandStackIs 
          1  (frame-push-value-sig v frame))
         v)
  :hints (("Goal" :in-theory (e/d (bcv::nth1OperandStackIs
                                   frame-push-value-sig)
                                  (make-sig-frame-cons-is-frame-push-value-sig)))))


(defthm nth1OperandStackIs-2-frame-push-sig
  (equal (bcv::nth1OperandStackIs 
          2  (frame-push-value-sig v1 
               (frame-push-value-sig v2 frame)))
         v2)
  :hints (("Goal" :in-theory (e/d (bcv::nth1OperandStackIs
                                   frame-push-value-sig)
                                  (make-sig-frame-cons-is-frame-push-value-sig)))))


(defthm topstack-guard-strong-implied-by-canPopCategory1
  (implies (and  (canPopCategory1 (operand-stack (current-frame s)))
                 (consistent-state s)
                 (NOT (MEM '*NATIVE*
                           (METHOD-ACCESSFLAGS (CURRENT-METHOD S)))))
           (topstack-guard-strong s))
  :hints (("Goal" :in-theory (enable topstack-guard-strong))))


;;
;; DJVM-check: talks about topStack-guard-strong
;;             it also talks about the TAG-OF the values from the operand
;;             stack.
;;
;; We need to use 
;;             isAssignable (value-sig (topStack ...)) 
;;
;; to get facts about 
;;
;;             (TAG-OF (topStack ...))
;;
;;
;; We know something about value-sig, we want conclude tag-of 

;(i-am-here)

(local (defthm REFp-implies-not-tag-of
  (implies (REFp v hp)
           (equal (tag-of v) 'REF))
  :hints (("Goal" :in-theory (enable wff-refp valid-REFp nullp tag-of)))))



(defthm REFp-implies-not-tag-of-specific
  (implies (REFp (topStack s) (heap s))
           (equal (tag-of (topStack s)) 'REF))
  :hints (("Goal" :in-theory (disable tag-of topStack REFp))))



(defthm value-sig-isAssignable-to-ARRRAY-implies-being-REFp
   (implies (and (bcv::isAssignable (value-sig v cl hp hp-init method-ptr)
                                   '(array (class "java.lang.Object"))
                                   env)
                 (consistent-value-x v cl hp))
            (REFp v hp))
   :hints (("Goal" :in-theory (enable value-sig consistent-value-x 
                                      consistent-value))))

(in-theory (disable REFp bcv::isAssignable))

(defthm value-sig-isAssignable-to-ARRRAY-implies-being-REFp-b
   (implies (and (bcv::isAssignable (value-sig (topStack s)
                                               (instance-class-table s)
                                               hp 
                                               (heap-init-map (aux s))
                                               (method-ptr (current-frame s)))
                                   '(array (class "java.lang.Object"))
                                   (env-sig s))
                 (consistent-value-x (topStack s) (instance-class-table s)
                                     (heap s))
                 (equal (heap s) hp))
            (REFp (topStack s) hp))
   :hints (("Goal" :in-theory (disable REFp bcv::isAssignable))))


(defthm bcv-isMatchingType-bcv-isAssignable
  (implies (and (bcv::isMatchingType typ stk env)
                (equal (bcv::sizeof typ) 1))
           (bcv::isAssignable (car stk) typ env))
  :hints (("Goal" :in-theory (enable bcv::isMatchingType))))


;; (defthm isMatchingType-typ-implies-canPopCategory1-specific-b
;;   (implies (and (bcv::isMatchingType typ
;;                                 (opstack-sig (operand-stack 
;;                                               (current-frame s))
;;                                              (instance-class-table s)
;;                                              (heap s)
;;                                              (heap-init-map (aux s))
;;                                              (method-ptr (current-frame s)))
;;                                 (env-sig s))
;;                 (equal (bcv::sizeof typ) 1))
;;            (canPopCategory1 (operand-stack (current-frame s))))
;;   :hints (("Goal" :in-theory (e/d (bcv::isMatchingType) ()))))


(defthm bcv-isMatchingType-bcv-isAssignable-specific
  (implies (and (bcv::isMatchingType typ (opstack-sig 
                                          (operand-stack (current-frame s))
                                          cl hp hp-init method-ptr) env)
                (canPopCategory1 (operand-stack (current-frame s)))
                (equal (bcv::sizeof typ) 1))
           (bcv::isAssignable (value-sig (topStack s)
                                         cl hp hp-init method-ptr) typ env))
  :hints (("Goal" :in-theory (e/d (topStack frame-top-opstack opstack-sig)
                                  (frame-top-opstack-normalize))
           :use ((:instance bcv-isMatchingType-bcv-isAssignable
                            (stk (opstack-sig 
                                  (operand-stack (current-frame s))
                                  cl hp hp-init method-ptr)))))))


;----------------------------------------------------------------------

;; (skip-proofs 
;;  (defthm consistent-state-obj-type-not-INT
;;    (implies (consistent-state s)
;;             (not (equal (obj-type (deref2 v (heap s))) 'INT)))))



;; (defthm value-sig-INT-not-REFp-if-v-being-consistent-value-x
;;    (implies (and (equal (value-sig v cl hp hp-init method-ptr) 'INT)
;;                  (consistent-value-x v cl hp)
;;                  (consistent-heap 
;;             (not (REFp v hp)))
;;    :hints (("Goal" :in-theory (enable value-sig fix-sig consistent-value-x
;;                                       consistent-value))))


;; (defthm car-opstack-sig-normalize
;;   (implies (canPopCategory1 (operand-stack (current-frame s)))
;;            (equal (CAR (OPSTACK-SIG (OPERAND-STACK (CURRENT-FRAME S))
;;                                     cl hp hp-init method-ptr))
;;                   (value-sig (topStack s)
;;                              cl hp hp-init method-ptr)))
;;   :hints (("Goal" :in-theory (e/d (opstack-sig topStack frame-top-opstack)
;;                                   (frame-top-opstack-normalize)))))



;; (defthm REFp-value-sig-is
;;   (implies (and (REFp v hp)
;;                 (nullp v))
;;            (equal (value-sig v cl hp hp-init method-ptr) 'NULL)))
;;
;;
;;
;;
;;
;; (defthm REFp-consistent-state-not-null
;;   (implies (and (REFp v (heap s))
;;                 (consistent-state s)
;;                 (equal (instance-class-table s) cl)
;;                 (not (nullp v)))
;;            (consistent-object (deref2 v (heap s)) (heap s) cl))
;;   :hints (("Goal" :in-theory (e/d (REFp consistent-heap deref2) (binding-rref-normalize)))))
;;
;;; moved to consistent-state.lisp
;;;
;;;


;;; try to get rid of the skip proofs!! 
;;; Mon May 16 18:24:55 2005

;;; (i-am-here) ;; Mon May 16 18:23:22 2005

(local 
 (encapsulate () 
   (local (include-book "base-consistent-state-more"))
   (defthm consistent-object-implies-object-type-not-primitive-type
     (implies (consistent-object obj (heap s) (instance-class-table s))
              (not (primitive-type? (obj-type obj)))))))


(defthm consistent-object-implies-object-type-not-primitive-type-deref2
  (implies (and (consistent-object (deref2 (topStack s) (heap s)) (heap s) (instance-class-table s))
                (equal (heap s) hp)
                (consistent-state s))
           (not (primitive-type? (obj-type (deref2 (topStack s) hp))))))


(defthm consistent-object-implies-object-type-not-primitive-type-deref2-x
  (implies (and (consistent-object (deref2 v (heap s)) (heap s) (instance-class-table s))
                (consistent-state s))
           (not (primitive-type? (obj-type (deref2 v (heap s)))))))



(defthm primitive-type-fact-1
  (NOT (PRIMITIVE-TYPE? (CONS 'UNINITIALIZED any)))
  :hints (("Goal" :in-theory (enable primitive-type?))))


(defthm primitive-type-fact-2
  (implies (not (primitive-type? typ))
           (not (primitive-type? (fix-sig typ))))
  :hints (("Goal" :in-theory (enable primitive-type?))))



(local 
 (encapsulate ()
              (local (include-book "base-consistent-state"))
              (defthm REFp-consistent-state-not-null
                (implies (and (REFp v (heap s))
                              (consistent-state s)
                              (equal (instance-class-table s) cl)
                              (not (nullp v)))
                         (consistent-object (deref2 v (heap s)) (heap s) cl)))))


(defthm REFp-value-sig-is-not-primitive-type
  (implies (and (REFp v (heap s))
                (not (nullp v))
                (equal (instance-class-table s) cl)
                (equal (heap-init-map (aux s)) hp-init)
                (equal (method-ptr (current-frame s)) method-ptr)
                (consistent-state s))
           (not (primitive-type? (value-sig v cl (heap s)
                                            hp-init method-ptr))))
  :hints (("Goal" :in-theory (e/d (value-sig) (nullp)))))
                        

                        
(defthm primitive-type-then-not-REFp-specific
  (implies (and (primitive-type? (value-sig (topStack s) (instance-class-table s)
                                            (heap s) (heap-init-map (aux s))
                                            (method-ptr (current-frame s))))
                (consistent-state s)
                (equal (heap s) hp))
           (not (REFp (topStack s) hp)))
  :hints (("Goal" :cases ((nullp (topStack s))))))



(defthm isMatchingType-INT-not-REFp
   (implies (and (bcv::isassignable (value-sig (topStack s)
                                               (instance-class-table s)
                                               (HEAP S)
                                               (HEAP-INIT-MAP (AUX S))
                                               (METHOD-PTR (CURRENT-FRAME S)))
                                    'INT
                                    (ENV-SIG S))
                 (consistent-state s)
                 (equal (heap s) hp))
            (not (REFp (topStack s) hp))))



(defthm not-REFp-value-sig-is-tag-of-specific
   (implies (not (REFp (topStack s) (heap s)))
            (equal (djvm-translate-int-type (tag-of (topStack s)))
                   (value-sig (topStack s)
                              (instance-class-table s)
                              (heap s)
                              (heap-init-map (aux s))
                              (method-ptr (current-frame s)))))
   :hints (("Goal" :in-theory (enable value-sig))))

(local (in-theory (disable djvm-translate-int-type)))
;;
;; this is eventually used to prove (tag-of (topStack ..) 'INT)!! 
;;



(defthm isAssignable-to-AARRAY-implies-array-type
  (implies (and (bcv::isAssignable 
                 (value-sig v (instance-class-table s)
                            (heap s)
                            (heap-init-map (aux s))
                            (method-ptr (current-frame s)))
                 '(array (class "java.lang.Object"))
                 (env-sig s))
                (not (nullp v))
                (consistent-state s)
                (REFp v (heap s)))
           (isArrayType (obj-type (deref2 v (heap s)))))
  :hints (("Goal" :in-theory (enable bcv::isAssignable 
                                     value-sig
                                     bcv::isJavaAssignable))))

(defthm not-nullp-implied-by-not-equal
  (implies (not (equal (value-of v) -1))
           (not (nullp v)))
  :hints (("Goal" :in-theory (enable nullp value-of rREF))))



(defthm array-type-value-sig-implies-array-type-runtime
  (implies (and (isArrayType  (obj-type (deref2 v (heap s))))
                (REFp v (heap s)) 
                (not (nullp v))
                ;; still need to relying on previous rules.  
                (consistent-state s))
           (array-type-s (obj-type (deref2 v (heap s))) 
                         (instance-class-table s)))
  :hints (("Goal" :in-theory (disable REFp reference-type-s))))



(defthm array-type-value-sig-implies-array-type-runtime-specific
  (implies (and (bcv::isAssignable 
                 (value-sig v (instance-class-table s)
                            (heap s)
                            (heap-init-map (aux s))
                            (method-ptr (current-frame s)))
                 '(array (class "java.lang.Object"))
                 (env-sig s))
                (REFp v (heap s))
                (not (nullp v))
                (consistent-state s))
           (array-type-s (obj-type (deref2 v (heap s))) 
                         (instance-class-table s)))
  :hints (("Goal" :in-theory (disable REFp reference-type-s))))

;----------------------------------------------------------------------

;----------------------------------------------------------------------
;
; Now we need to deal with component-type assertion of 
;
;  isMatchingType (array (class "java.lang.Object"))
;  
;  We want to conclude that the array-component-type is 
;  
;     not (primitive-type?) 
;
;  We need to make use of the 
;
;     the fact that is is assignable, to conclude it is 
;
;  a consistent-array-object, 
;
;  then conclude its component type is assignable to 
;       
;    java.lang.Object
;
; refer to bcv-check-djvm-check.lisp


(local (defthm isAssignable-to-AARRAY-implies-component-type
         (implies (bcv::isAssignable (fix-sig type)
                                     '(array (class "java.lang.Object"))
                                     env)
                  (not (primitive-type? (array-component-type type))))
         :hints (("Goal" :in-theory (e/d (array-component-type 
                                          bcv::isassignable
                                          primitive-type?)
                                         ())))))

(local (defthm isAssignable-to-AARRAY-implies-component-type-specific
  (implies (bcv::isAssignable (fix-sig (obj-type (deref2 (topStack s) hp)))
                              '(array (class "java.lang.Object"))
                              (env-sig s))
           (not (primitive-type? (array-component-type 
                                  (obj-type (deref2 (topStack s) hp))))))))


(local (defthm if-REFp-non-NULL-implies-value-sig
  (implies (and (REFp v hp)
                (not (nullp v))
                (not (consp (deref2-init v hp-init))))
           (equal (value-sig v cl hp hp-init method-ptr)  
                  (fix-sig (obj-type (deref2 v hp)))))
  :hints (("Goal" :in-theory (enable value-sig)))))


(local (defthm isAssignable-to-array-class-java-lang-Object-implies-not-deref2-init
  (implies (and (bcv::isAssignable (value-sig v cl hp hp-init method-ptr)
                                   '(array (class "java.lang.Object"))
                                   env)
                (not (nullp v))
                (consistent-value-x v cl hp))
           (not (consp (deref2-init v hp-init))))
  :hints (("Goal" :in-theory (enable value-sig nullp 
                                     consistent-value
                                     bcv::isAssignable
                                     consistent-value-x)))))

(local (defthm value-sig-reduce-to-fix-sig
  (implies (and (bcv::isAssignable (value-sig v cl hp hp-init method-ptr)
                                   '(array (class "java.lang.Object")) env)
                (not (nullp v))
                (consistent-value-x v cl hp))
           (equal (value-sig v cl hp hp-init method-ptr)
                  (fix-sig (obj-type (deref2 v hp)))))
  :hints (("Goal" :in-theory (disable REFp nullp deref2-init bcv::isAssignable value-sig)))))



(defthm bcv-isAssignable-value-sig-bcv-isAssignable-fix-sig
  (implies (and (bcv::isAssignable (value-sig v cl hp hp-init method-ptr)
                                   '(array (class "java.lang.Object")) env)
                (not (nullp v))
                (consistent-value-x v cl hp))
           (bcv::isAssignable (fix-sig (obj-type (deref2 v hp)))
                              '(array (class "java.lang.Object")) env))
  :hints (("Goal" :use value-sig-reduce-to-fix-sig
           :in-theory (disable value-sig-reduce-to-fix-sig
                               IF-REFP-NON-NULL-IMPLIES-VALUE-SIG))))


(in-theory (disable deref2-init))

;; (local (defthm isAssignable-to-AARRAY-implies-component-type-specific
;;   (implies (bcv::isAssignable (fix-sig (obj-type (deref2 (topStack s) hp)))
;;                               '(array (class "java.lang.Object"))
;;                               (env-sig s))
;;            (not (primitive-type? (array-component-type 
;;                                   (obj-type (deref2 (topStack s) hp))))))))

;; we have this and above we should have the following!!


;;; need fix!! 

(defthm isAssignable-to-array-class-java-lang-Object-not-primitive-type
  (implies (and (bcv::isAssignable (value-sig v  (instance-class-table s)
                                              (heap s)
                                              (heap-init-map (aux s))
                                              (method-ptr (current-frame s)))
                                   '(array (class "java.lang.Object"))
                                   (env-sig s))
                ;;(REFp v (heap s))
                (not (nullp v))
                ;;(consistent-state s)
                (consistent-value-x v (instance-class-table s) (heap s)))
           (not (primitive-type? (array-component-type 
                                  (obj-type (deref2 v (heap s)))))))
  :hints (("Goal" :restrict ((isAssignable-to-AARRAY-implies-component-type
                              ((env  (env-sig s))))))))


;----------------------------------------------------------------------
; 
;  (i-am-here)
;

(local (defthm fix-sig-not-void
         (not (equal (fix-sig sig) 'void))))


(local (defthm consistent-value-x-consistent-state-value-sig-not-void
         (implies (and (consistent-value-x v (instance-class-table s) (heap s))
                       (consistent-state s)
                       (equal (instance-class-table s) cl)
                       (equal (heap s) hp)
                       (equal (heap-init-map (aux s)) hp-init))
                  (not (equal (value-sig v cl hp hp-init 
                                         (method-ptr (current-frame s)))
                              'void)))
         :hints (("Goal" :in-theory (e/d (value-sig fix-sig consistent-value-x
                                                    consistent-value) ())))))
             

;; (i-am-here)                             

(local 
 (encapsulate ()
    (local (include-book "base-consistent-state-more"))
    (defthm operand-stack-current-frame-pushStack
      (implies (consistent-state s)
               (equal (operand-stack (current-frame (pushStack v s)))
                      (push v (operand-stack (current-frame s))))))))



(local (defthm opstack-sig-cons-equal
         (implies  (category1 v)
                   (equal (opstack-sig (cons v stk) cl hp hp-init method-ptr)
                          (cons (value-sig v cl hp hp-init method-ptr)
                                (opstack-sig stk cl hp hp-init method-ptr))))
         :hints (("Goal" :in-theory (enable category1)))))


(local 
 (encapsulate () 
              (local (include-book "base-consistent-state-more"))
              (defthm fix-sig-size-1
                (implies (consistent-state s)
                         (equal (bcv::sizeof (fix-sig (obj-type (deref2 v (heap s))))) 1))
                :hints (("Goal" :in-theory (enable fix-sig bcv::sizeof))))))


                         
(local (defthm bcv-size-of-1-or-2
         (implies (not (equal (bcv::sizeof x) 1))
                  (equal (bcv::sizeof x) 2))
         :hints (("Goal" :in-theory (enable bcv::sizeof)))))



(defthm category1-implies-equal-sizeof-value-sig
         (implies (and (category1 v)
                       (consistent-state s)
                       (consistent-value-x v (instance-class-table s)
                                           (heap s)))
                  (equal (bcv::sizeof (value-sig v cl (heap s) hp-init method-ptr))
                         1))
         :hints (("Goal" :in-theory (enable value-sig category1 
                                            consistent-value-x
                                            consistent-value
                                            bcv::sizeof 
                                            REFp WFF-REFp))))



;; (i-am-here)

(defthm opstack-sig-operand-stack-pushStack
  (implies (and (equal (instance-class-table s) cl)
                (equal (heap s) hp)
                (equal (heap-init-map (aux s)) hp-init)
                (equal (method-ptr (current-frame s)) method-ptr)
                (consistent-value-x v cl hp)
                (consistent-state s)
                (category1 v))
           (equal (opstack-sig (operand-stack (current-frame (pushStack v s)))
                               cl hp hp-init method-ptr)
                  (BCV::PUSHOPERANDSTACK (value-sig v cl hp hp-init
                                                    method-ptr)
                                         (OPSTACK-SIG (OPERAND-STACK (CURRENT-FRAME s))
                                                     cl hp hp-init
                                                      method-ptr))))
  :hints (("Goal" :in-theory (enable bcv::pushoperandstack))))


;----------------------------------------------------------------------
;; (i-am-here) ;; Tue May  3 21:45:41 2005

(defthm value-sig-being-fix-sig-NULL-short-cut
  (implies (NULLp v)
           (equal (value-sig v cl hp hp-init method-ptr)
                  'NULL)))

;----------------------------------------------------------------------

(defthm bcv-isAssignable-reflexive
  (bcv::isAssignable any1 any1 env)
  :hints (("Goal" :in-theory (enable bcv::isAssignable))))


(defthm TypeListAssignable-reflexive
  (bcv::typelistassignable anylist anylist env))

;----------------------------------------------------------------------

;----------------------------------------------------------------------


;;;

(local 
 (encapsulate ()
 (local (include-book "base-bcv-isAssignable-facts"))
 (defthm isAssignable-expander
   (implies (syntaxp (and (eq (car bcv::t1) 'QUOTE)
                          (eq (car bcv::t2) 'QUOTE)))
            (equal (bcv::isAssignable bcv::t1 bcv::t2 bcv::env)
                   (LET
                    ((BCV::CL (BCV::CLASSTABLEENVIRONMENT BCV::ENV)))
                    (IF
                     (EQUAL BCV::T1 BCV::T2)
                     T
                     (COND
                      ((AND (EQUAL BCV::T1 'ONEWORD)
                            (EQUAL BCV::T2 'topx))
                       T)
                      ((AND (EQUAL BCV::T1 'TWOWORD)
                            (EQUAL BCV::T2 'topx))
                       T)
                      ((EQUAL BCV::T1 'INT)
                       (BCV::ISASSIGNABLE 'ONEWORD
                                          BCV::T2 BCV::ENV))
                      ((EQUAL BCV::T1 'FLOAT)
                       (BCV::ISASSIGNABLE 'ONEWORD
                                          BCV::T2 BCV::ENV))
                      ((EQUAL BCV::T1 'LONG)
                       (BCV::ISASSIGNABLE 'TWOWORD
                                          BCV::T2 BCV::ENV))
                      ((EQUAL BCV::T1 'DOUBLE)
                       (BCV::ISASSIGNABLE 'TWOWORD
                                          BCV::T2 BCV::ENV))
                      ((EQUAL BCV::T1 'REFERENCE)
                       (BCV::ISASSIGNABLE 'ONEWORD
                                          BCV::T2 BCV::ENV))
                      ((EQUAL 'UNINITIALIZED BCV::T1)
                       (BCV::ISASSIGNABLE 'REFERENCE
                                          BCV::T2 BCV::ENV))
                      ((BCV::ISCLASSTYPE BCV::T1)
                       (OR (BCV::ISASSIGNABLE 'REFERENCE
                                              BCV::T2 BCV::ENV)
                           (BCV::ISJAVAASSIGNABLE BCV::T1 BCV::T2 BCV::CL)))
                      ((BCV::ISARRAYTYPE BCV::T1)
                       (OR
                        (BCV::ISASSIGNABLE 'REFERENCE
                                           BCV::T2 BCV::ENV)
                        (AND (BCV::ISCLASSTYPE BCV::T2)
                             (BCV::ISJAVAASSIGNABLE BCV::T1 BCV::T2 BCV::CL))
                        (AND (BCV::ISARRAYTYPE BCV::T2)
                             (BCV::ISJAVAASSIGNABLE BCV::T1 BCV::T2 BCV::CL))))
                      ((EQUAL BCV::T1 'UNINITIALIZEDTHIS)
                       (BCV::ISASSIGNABLE 'UNINITIALIZED
                                          BCV::T2 BCV::ENV))
                      ((BCV::ISUNINITIALIZEDOBJECT BCV::T1)
                       (BCV::ISASSIGNABLE 'UNINITIALIZED
                                          BCV::T2 BCV::ENV))
                      ((BCV::ISNULLTYPE BCV::T1)
                       (OR (BCV::ISCLASSTYPE BCV::T2)
                           (BCV::ISARRAYTYPE BCV::T2)
                           (BCV::ISASSIGNABLE '(CLASS "java.lang.Object")
                                              BCV::T2 BCV::ENV)))
                      (T NIL)))))))))




(defthm isMatchingType-class-Object-implies-canPopCategory1 
  (implies (bcv::isMatchingType '(class "java.lang.Object")
                                (opstack-sig stack cl hp hp-init method-ptr) env)
           (canPopCategory1 stack))
  :hints (("Goal" :in-theory (enable bcv::isMatchingType canPopCategory1)))
  :rule-classes :forward-chaining)



(defthm isMatchingType-class-Object-implies-canPopCategory1-specific-b
  (implies (bcv::isMatchingType '(class "java.lang.Object") 
                                (opstack-sig (operand-stack 
                                              (current-frame s))
                                             (instance-class-table s)
                                             (heap s)
                                             (heap-init-map (aux s))
                                             (method-ptr (current-frame s)))
                                (env-sig s))
           (canPopCategory1 (operand-stack (current-frame s))))
  :hints (("Goal" :in-theory (e/d () (canPopCategory1)))))


;----------------------------------------------------------------------


(defthm bcv::canPop1-implies-bcv-isMatchingType
  (implies (bcv::canPop1 (cons x prefix)
                         (opstack-sig stk cl hp hp-init method-ptr) env)
           (bcv::ismatchingtype x (opstack-sig stk cl hp hp-init method-ptr)
                                env)))


(defthm bcv::canPop1-implies-bcv-isMatchingType-specific
  (implies (bcv::canPop1 '((class "java.lang.Object") INT (array (class
                                                                  "java.lang.Object")))
                         (opstack-sig (operand-stack (current-frame s))
                                      (INSTANCE-CLASS-TABLE S)
                                      (HEAP S)
                                      (HEAP-INIT-MAP (AUX S))
                                      (METHOD-PTR (CURRENT-FRAME S)))
                         (ENV-SIG S))
           (BCV::ISMATCHINGTYPE '(class "java.lang.Object")
                     (OPSTACK-SIG (OPERAND-STACK (CURRENT-FRAME S))
                                  (INSTANCE-CLASS-TABLE S)
                                  (HEAP S)
                                  (HEAP-INIT-MAP (AUX S))
                                  (METHOD-PTR (CURRENT-FRAME S)))
                     (ENV-SIG S)))
  :hints (("Goal" :in-theory (disable opstack-sig bcv::canPop1
                                      CANPOPCATEGORY1-CONSP-STK
                                      FRAME-POP-OPSTACK-NORMALIZE
                                      FRAME-TOP-OPSTACK-NORMALIZE
                                      bcv::ismatchingtype))))

                       
(defthm bcv-canPop1-canPop1
  (equal  (bcv::canPop1 anylist (bcv::frameStack (frame-sig frame cl hp
                                                            hp-init)) env)
          (bcv::canPop1 anylist (opstack-sig (operand-stack frame) cl hp
                                             hp-init
                                             (method-ptr frame)) env)))




;----------------------------------------------------------------------

;;; the following is a difficult one!! ;; Mon May 16 19:04:36 2005
;;;

(local 
 (defthm isMatchingType-type-opstack-push
   (implies (canpopcategory1 stk)
            (equal (opstack-sig stk cl hp hp-init method-ptr)
                   (push (value-sig (car stk) cl hp hp-init method-ptr)
                         (opstack-sig (cdr stk) cl hp hp-init
                                      method-ptr))))))


(local 
 (defthm popMatchingType-of-push
   (implies (equal (bcv::sizeof type) 1)
            (equal (bcv::popMatchingType type (push any stk))
                   stk))))

(local 
 (defthm isAssignable-nil-not
   (implies type
            (not (bcv::isAssignable nil type env)))
   :hints (("Goal" :in-theory (enable bcv::isAssignable)))))


(local 
 (defthm isAssignable-top-top
   (implies (not (equal type 'topx))
            (not (bcv::isAssignable 'topx type env)))
   :hints (("Goal" :in-theory (enable bcv::isAssignable)))))


(local 
 (defthm isMatchingType-size-of-1-type-opstack-sig-implies-canPopCategory1
   (implies (and (bcv::ismatchingtype type (opstack-sig stk cl hp hp-init
                                                        method-ptr) env)
                 type
                 (equal (bcv::sizeof type) 1)
                 (not (equal type 'topx)))
            (canpopcategory1 stk))
   :hints (("Goal" :in-theory (e/d (bcv::sizeof bcv::ismatchingtype) (canpopcategory1))))))


(local 
 (defthm frame-pop-opstack-normalize-further
   (implies (consistent-state s)
            (equal (frame-pop-opstack (current-frame s))
                   (current-frame (popStack s))))
   :hints (("Goal" :in-theory (e/d (current-frame frame-pop-opstack popStack)
                                   (FRAME-POP-OPSTACK-NORMALIZE
                                    topframe-normalization))))))



(defthm isMatchingType-popMatchingType-form1
  (implies (and (bcv::ismatchingtype type (opstack-sig (operand-stack (current-frame s))
                                                       cl hp hp-init
                                                       method-ptr) (env-sig
                                                                    s))
                type
                (not (equal type 'topx))
                (equal (bcv::sizeof type) 1)
                (not   (equal type 'void))
                (consistent-state s)
                (equal (instance-class-table s) cl)
                (equal (heap s) hp)
                (equal (heap-init-map (aux s)) hp-init)
                (equal (method-ptr (current-frame s)) method-ptr))
           (equal (BCV::POPMATCHINGTYPE type
                                        (OPSTACK-SIG (OPERAND-STACK (CURRENT-FRAME S))
                                                     cl hp hp-init method-ptr))
                  (opstack-sig (operand-stack (current-frame (popStack s)))
                               cl hp hp-init method-ptr)))
  :hints (("Goal" :in-theory (e/d () 
                                  ()))))
  



;;            :cases ((canpopcategory1 (operand-stack (current-frame s)))))))


;----------------------------------------------------------------------

;; export this one. appear before! 


(defthm isAssignable-to-array-class-java-lang-Object-implies-not-deref2-init
  (implies (and (bcv::isAssignable (value-sig v cl hp hp-init method-ptr)
                                   '(array (class "java.lang.Object"))
                                   env)
                (not (nullp v))
                (consistent-value-x v cl hp))
           (not (consp (deref2-init v hp-init))))
  :hints (("Goal" :in-theory (enable value-sig nullp 
                                     consistent-value
                                     bcv::isAssignable
                                     consistent-value-x))))


;----------------------------------------------------------------------


