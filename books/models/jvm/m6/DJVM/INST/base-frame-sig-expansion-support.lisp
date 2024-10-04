(in-package "DJVM")
(include-book "../../BCV/typechecker")
(include-book "../../BCV/bcv-functions")

(include-book "base")
(include-book "base-consistent-state")
(include-book "base-bind-free")


(in-theory (disable bcv::frameStack bcv::frameLocals bcv::frameFlags
                   locals operand-stack bcv::nth1OperandStackIs  
                   bcv::pushOperandStack popStack
                   nullp BCV::isMatchingType
                   CODE-STACKMAPS ENV-SIG HEAP-INIT-MAP 
                   MAKEENVIRONMENT BCV::ARRAYELEMENTTYPE
                   BCV::POP frame-sig BCV::SIZEOF
                   bcv::classtableEnvironment
                   REFp
                   BCV::popmatchingtype
                   BCV::MAXSTACKENVIRONMENT
                   deref2-init
                   bcv::make-sig-frame
                   value-sig
                   make-sig-frame))


(in-theory (disable frame-push-value-sig
                    frame-pop-opstack 
                    frame-top-opstack))


(local 
 (defthm bcv-make-sig-frame-normalize
   (equal (bcv::make-sig-frame l s f)
          (make-sig-frame l s f))
   :hints (("Goal" :in-theory (enable make-sig-frame bcv::make-sig-frame)))))

(local 
 (defthm make-sig-frame-cons-is-frame-push-value-sig
   (equal (make-sig-frame l (cons x stack) flags)
          (frame-push-value-sig x (make-sig-frame l stack flags)))
   :hints (("Goal" :in-theory (enable make-sig-frame 
                                      bcv::make-sig-frame
                                      frame-push-value-sig
                                      bcv::frameFlags bcv::frameLocals
                                      bcv::frameStack)))))

(local 
 (defthm bcv-make-sig-frame-accessor
  (and (equal (bcv::frameStack  (make-sig-frame l s f)) s)
       (equal (bcv::frameLocals (make-sig-frame l s f)) l)
       (equal (bcv::frameFlags  (make-sig-frame l s f)) f))
  :hints (("Goal" :in-theory (enable make-sig-frame
                                     bcv::frameFlags bcv::frameLocals bcv::frameStack)))))

;; defthm pushStack-category1-canPopCateory1

(local 
 (defthm make-sig-frame-bcv-push-operandstack-normalize
    (implies (and (equal (bcv::frameLocals (frame-sig frame cl hp hp-init)) locals)
                  (equal (bcv::frameFlags (frame-sig frame cl hp hp-init)) flags)
                  (equal (bcv::sizeof resulttype) 1)
                  (not   (equal resulttype 'void))
                 (equal (method-ptr frame) method-ptr))
            (equal (MAKE-SIG-FRAME
                    locals
                    (BCV::PUSHOPERANDSTACK RESULTTYPE (opstack-sig
                                                       (operand-stack frame)
                                                       cl hp hp-init method-ptr))
                    flags)
                   (frame-push-value-sig resulttype (frame-sig frame cl hp hp-init))))
    :hints (("Goal" :in-theory (enable bcv::pushoperandstack frame-sig frame-push-value-sig)))))


(local 
 (encapsulate ()
   (local (include-book "base-bcv-support"))
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
                                                      method-ptr)))))))




(local 
 (defthm locals-frame-sig
   (equal (bcv::frameLocals (frame-sig frame cl hp hp-init))
          (locals-sig (locals frame) cl hp hp-init (method-ptr frame)))
   :hints (("Goal" :in-theory (enable frame-sig)))))



;; (local 
;;  (defthm flags-frame-sig
;;    (equal (bcv::frameFlags (frame-sig frame cl hp hp-init))
;;           (locals-sig (locals frame) cl hp hp-init (method-ptr frame)))
;;    :hints (("Goal" :in-theory (enable frame-sig)))))

(local 
 (encapsulate ()
    (local (include-book "base-bcv-support"))
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
                                            REFp WFF-REFp))))))


;; (local 
;;  (defthm fix-type-size-1
;;    (implies (not (primitive-type? type))
;;             (equal (bcv::sizeof (fix-sig type)) 1))
;;    :hints (("Goal" :in-theory (enable bcv::sizeof fix-sig primitive-type?)))))


;; (local 
;;  (defthm category1-implies-size-of-being-1
;;    (implies (and (category1 v)
;;             (EQUAL (BCV::SIZEOF (VALUE-SIG V cl hp hp-init method-ptr))
;;                    '1))
;;    :hints (("Goal" :in-theory (enable category1)))))


;;; fix-sig!!! Sun Jul 31 12:50:44 2005

;; (local 
;;  (defthm genflag-no-change
;;    (implies (not (equal type 'UNINITIALIZEDTHIS))
;;             (equal (gen-flags (bcv::pushoperandstack type stk))
;;                    (gen-flags stk)))
;;    :hints (("Goal" :in-theory (enable bcv::sizeof bcv::pushoperandstack)))))


;; (local 
;;   (defthm gen-frame-flag-no-change
;;     (implies (not (equal type 'uninitializedthis))
;;              (equal    (GEN-FRAME-FLAGS locals
;;                                         (BCV::PUSHOPERANDSTACK type stk))
;;                        (gen-frame-flags locals stk)))))


(local 
 (defthm frameFlags-frame-sig-is-local
   (equal (bcv::frameFlags (frame-sig frame cl hp hp-init))
          (gen-frame-flags frame hp-init))
   :hints (("Goal" :in-theory (enable frame-sig)))))



;; (local 
;;  (defthm frameFlags-frame-sig-is-local
;;    (equal (bcv::frameFlags (frame-sig frame cl hp hp-init))
;;           (gen-frame-flags (locals-sig (locals frame) cl hp hp-init (method-ptr
;;                                                                      frame))
;;                            (opstack-sig (operand-stack frame) cl hp hp-init 
;;                                         (method-ptr frame))))
;;    :hints (("Goal" :in-theory (enable frame-sig)))))




(local 
 (defthm not-fix-void
   (not (equal (fix-sig any) 'void))))

(local 
 (defthm consistent-value-x-implies-not-value-sig-void
   (implies (and (consistent-value-x v (instance-class-table s) (heap s))
                 (consistent-state s))
            (not (equal (value-sig v (instance-class-table s) (heap s) 
                                   (heap-init-map (aux s)) (method-ptr
                                                            (current-frame s)))
                        'void)))
   :hints (("Goal" :cases ((REFp v (heap s)))
            :in-theory (enable consistent-value-x value-sig 
                               NULLp
                               consistent-value)))))

(local 
 (defthm locals-pushStack-no-change
   (implies (consistent-state s)
            (equal (locals (current-frame (pushStack v s)))
                   (locals (current-frame s))))
   :hints (("Goal" :in-theory (enable pushStack current-frame
                                      push-stack-of-thread frame-set-operand-stack)))))

;; (i-am-here) ;; Tue May 17 15:22:59 2005

;; make-sig-frame-cons-is-frame-push-value-sig

;; (i-am-here) ;; Sun Jul 31 13:45:17 2005


(local (include-book "base-consistent-state-more"))


;;(i-am-here) ;; Tue Aug 16 17:32:46 2005


(defthm frame-sig-of-push-stack-is-frame-push-value-sig
  (implies  (and  (consistent-value-x v (instance-class-table s) (heap s))
                  (category1 v)
                  (consistent-state s)
                  (equal (instance-class-table s) cl) 
                  (equal (heap s) hp)
                  (equal (heap-init-map (aux s)) hp-init))
           (equal (FRAME-SIG  (CURRENT-FRAME (PUSHSTACK v s))  cl hp hp-init)
                  (frame-push-value-sig (value-sig v cl hp hp-init
                                                   (method-ptr (current-frame
                                                                s)))
                                        (frame-sig (current-frame s) cl hp
                                                   hp-init))))
  :hints (("Goal" :in-theory (e/d (frame-sig push opstack-sig pop
                                             frame-push-value-sig) 
                                  (gen-frame-flags
                                   MAKE-SIG-FRAME-CONS-IS-FRAME-PUSH-VALUE-SIG)))))



;; (defthm frame-sig-of-push-stack-is-frame-push-value-sig
;;   (implies (and (not (equal (value-sig v (instance-class-table s) (heap s) (heap-init-map
;;                                                                             (aux s))
;;                                        (method-ptr (current-frame s)))
;;                             'uninitializedThis))
;;                 (consistent-value-x v (instance-class-table s) (heap s))
;;              (category1 v)
;;                 (consistent-state s)
;;                 (equal (instance-class-table s) cl) 
;;                 (equal (heap s) hp)
;;                 (equal (heap-init-map (aux s)) hp-init))
;;            (equal (FRAME-SIG  (CURRENT-FRAME (PUSHSTACK v s))  cl hp hp-init)
;;                   (frame-push-value-sig (value-sig v cl hp hp-init
;;                                                    (method-ptr (current-frame
;;                                                                 s)))
;;                                         (frame-sig (current-frame s) cl hp
;;                                                    hp-init))))
;;   :hints (("Goal" :in-theory (e/d (frame-sig) 
;;                                   (gen-frame-flags)))))





