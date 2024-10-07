(in-package "DJVM")
(include-book "../../DJVM/djvm-type-value")
(include-book "../../DJVM/djvm-frame-manipulation-primitives")
(include-book "../../DJVM/djvm-state")
(include-book "../../DJVM/djvm-exceptions")
(include-book "../../DJVM/consistent-state")
(include-book "../../DJVM/consistent-state-properties")
(include-book "../../M6-DJVM-shared/jvm-bytecode")
(include-book "../../M6-DJVM-shared/jvm-bytecode-guard-verification")
(include-book "../../BCV/typechecker")
(include-book "../../DJVM/consistent-state-to-sig-state")
(include-book "../../DJVM/consistent-state-to-untag-state")

(include-book "base-bind-free")

;----------------------------------------------------------------------
; Simple Macro to simplify typing! 
; 

(defmacro ADVANCE-PC (s)
  `(state-set-pc (+ (pc ,s)
                    (inst-size inst))
                 ,s))

; This  assumes that variable "inst" is defined in the context. 
;   


(defmacro LLP (index)
  `(local-at ,index s))


;----------------------------------------------------------------------
;

(defun frame-push-value-sig (v sig-frame)
  "push v onto the sig-operand-stack of sig-frame"
  (bcv::make-sig-frame 
      (bcv::frameLocals sig-frame)
      (push v (bcv::frameStack sig-frame))
      (bcv::frameFlags sig-frame)))


(defun frame-pop-opstack (frame)
  "pop one value/slot off the opstack of sig-frame"
  (frame-set-operand-stack 
    (pop (operand-stack frame))
    frame))

(defun frame-top-opstack (frame)
  (top (operand-stack frame)))



(defun frame-push-value-sig-g (v frame)
  (if (equal (bcv::sizeof v) 1)
      (frame-push-value-sig v frame)
    (bcv::make-sig-frame (bcv::framelocals frame)
                         (push 'topx (push v (bcv::framestack frame)))
                         (bcv::frameflags frame))))

;;; Wed Jul 20 23:31:39 2005 ;; 

;----------------------------------------------------------------------



;----------------------------------------------------------------------

(defun CHECK-NULL (ref)
  (declare (xargs :guard (wff-REFp ref)))
  (equal (rREF ref) -1))


;----------------------------------------------------------------------
;
; Mon Apr 18 15:36:42 2005. The problem of trying reorganizing the files come 
; become how to sort out the dependencies!! 
;
;
; The following lemmas are about DJVM's operations. 

;; ;;

(defthm topStack-guard-strong-implies-not-mem-native
  (implies (topStack-guard-strong s)
           (not (mem '*native* (method-accessflags (current-method s)))))
  :hints (("Goal" :in-theory (enable topStack-guard-strong)))
  :rule-classes :forward-chaining)


;; ;; (defthm secondStack-guard-strong-implies-not-mem-native
;; ;;   (implies (secondStack-guard-strong s)
;; ;;            (not (mem '*native* (method-accessflags (current-method s)))))
;; ;;   :hints (("Goal" :in-theory (enable topStack-guard-strong)))
;; ;;   :rule-classes :forward-chaining)


;; ;; (defthm operand-stack-frame-set-opstack
;; ;;   (equal (operand-stack (frame-set-operand-stack opstack frame))
;; ;;          opstack)
;; ;;   :hints (("Goal" :in-theory (enable make-frame frame-set-operand-stack operand-stack))))
;; ;;
;; ;; moved into base-djvm
;; ;;
;; ;----------------------------------------------------------------------


;; (skip-proofs 
;;  (defthm popStack-popOpStack
;;   (implies   (TOPSTACK-GUARD-STRONG S)
;;              (equal (operand-stack (current-frame (safe-popStack s)))
;;                     (cdr (operand-stack (current-frame s)))))
;;   :hints (("Goal" :in-theory (e/d (safe-popStack 
;;                                    current-frame
;;                                    topstack-guard-strong)
;;                                   (topframe-normalization))))))

;; (defthm topstack-guard-strong-implies-consp-opstack
;;   (implies (topstack-guard-strong s)
;;            (consp (operand-stack (current-frame s))))
;;   :hints (("Goal" :in-theory (enable topstack-guard-strong))))


;; (defthm popStack-decrease-stack-size
;;   (implies (TOPSTACK-GUARD-STRONG S)
;;            (equal (len (operand-stack (current-frame (safe-popStack s))))
;;                   (- (len (operand-stack (current-frame s))) 1))))


;; (defthm method-ptr-frame-set-opstack
;;   (equal (method-ptr (frame-set-operand-stack opstack frame))
;;          (method-ptr frame))
;;   :hints (("Goal" :in-theory (enable frame-set-operand-stack))))

;; ;;; It does not hurt to add these rules. Mon Oct 18 08:37:57 2004
;; ;;; Although we could just keep a discipline of enabling
;; ;;; frame-set-operand-stack. RANDOM COMMENTS.

(in-theory (disable method-ptr))


;; (defthm integerp-inst-size
;;   (integerp (inst-size any)))


(in-theory (disable wff-tagged-value rREF 
                    check-NULL common-info
                    wff-internal-array
                    wff-array-type inst-size
                    obj-type binding bound?
                    wff-REFp value-of deref2))

;; ;;; Mon Apr 18 16:48:19 2005. the following should be easy


;; ;; (skip-proofs 
;; ;;  (defthm consistent-state-bound?-binding-wff-obj
;; ;;    (implies (and (consistent-state s)
;; ;;                  (bound? p (heap s)))
;; ;;             (wff-obj (binding p (heap s))))))

;; ;;; prove it somewhere in consistent-state-properties! 


(defthm binding-rREF-normalize
  (equal (binding (rREF tagged-value) hp)
         (deref2 tagged-value hp))
  :hints (("Goal" :in-theory (enable deref2))))


(defthm INT32p-implies-integerp
  (implies (INT32p x)
           (integerp x))
  :hints (("Goal" :in-theory (enable INT32p))))


(defthm INT32p-implies-integerp-f
  (implies (INT32p x)
           (integerp x))
  :hints (("Goal" :in-theory (enable INT32p)))
  :rule-classes :forward-chaining)


(in-theory (disable primitive-type?))
(in-theory (disable category1))


(defthm check-NULL-implies-value-being-negative-1
  (iff (check-NULL v)
       (equal (value-of v) -1))
  :hints (("Goal" :in-theory (enable check-NULL rREF value-of))))


(in-theory (disable class-exists?))

(defthm aux-popStack-no-change
  (equal (aux (popStack s))
         (aux s))
  :hints (("Goal" :in-theory (e/d (popStack frame-set-operand-stack
                                            replace-thread-table-entry
                                            state-set-thread-table
                                            thread-by-id
                                            current-thread)
                                  (topFrame-normalization aux)))))


;----------------------------------------------------------------------
; (i-am-here)

(defthm pc-set-element-at-array
  (equal (pc (set-element-at-array index value array-ref s))
         (pc s))
  :hints (("Goal" :in-theory (enable set-element-at-array set-element-at))))


;----------------------------------------------------------------------


(defthm array-class-table-not-change
  (equal (ARRAY-CLASS-TABLE (POPSTACK s))
         (array-class-table s)))

(defthm array-class-table-not-change-push
  (equal (ARRAY-CLASS-TABLE (PushSTACK v  s))
         (array-class-table s)))


;----------------------------------------------------------------------

(defthm current-frame-state-set-heap
  (equal (current-frame (state-set-heap hp s))
         (current-frame s)))

(defthm array-base-type-is-array-component-type
  (equal (array-base-type type)
         (array-component-type type))
  :hints (("Goal" :in-theory (enable array-base-type))))

;----------------------------------------------------------------------

;----------------------------------------------------------------------

(defthm tag-of-tag-is-when-primitive-type
  (implies (primitive-type? type)
           (equal (tag-of (tag v type))
                  type))
  :hints (("Goal" :in-theory (enable tag-of tag primitive-type?))))


;----------------------------------------------------------------------

(defthm primitive-type-not-REFp
  (implies (primitive-type? type)
           (not (REFp (tag v type) (heap s))))
  :hints (("Goal" :in-theory (enable REFp wff-REFp primitive-type? 
                                     NULLp
                                     tag tag-of))))

;----------------------------------------------------------------------

;; (i-am-here) ;; Thu Jul 21 13:31:36 2005

;; (defthm value-sig-primitive-type
;;   (implies (primitive-type? type)
;;            (equal (VALUE-SIG
;;                    (TAG v type)
;;                    (instance-class-table s)
;;                    (HEAP S)
;;                    (HEAP-INIT-MAP (AUX S))
;;                    (METHOD-PTR (CURRENT-FRAME s)))
;;                   type))
;;   :hints (("Goal" :in-theory (enable value-sig fix-sig 
;;                                      primitive-type? wff-REFp))))

(defthm value-sig-primitive-type
  (implies (primitive-type? type)
           (equal (VALUE-SIG
                   (TAG v type) 
                   cl hp hp-init method-ptr)
                  (djvm-translate-int-type type)))
  :hints (("Goal" :in-theory (enable value-sig fix-sig 
                                     primitive-type? wff-REFp))))



;; Thu Jul 21 13:34:47 2005

;;
;; (i-am-here) ;; Thu Jul 21 13:49:14 2005
;;

;----------------------------------------------------------------------

(defthm operand-stack-frame-set-operand-stack-is
  (equal  (OPERAND-STACK
           (FRAME-SET-OPERAND-STACK stack frame))
          stack)
  :hints (("Goal" :in-theory (enable operand-stack 
                                     make-frame
                                     frame-set-operand-stack))))


;----------------------------------------------------------------------

(defthm type-size-2-implies-primitive-type-f
  (implies (equal (type-size type) 2)
           (primitive-type? type))
  :hints (("Goal" :in-theory (enable type-size primitive-type?)))
  :rule-classes :forward-chaining)

;----------------------------------------------------------------------

(defthm frame-set-stackframe-set-stack
  (equal  (frame-set-operand-stack stack2 
           (FRAME-SET-OPERAND-STACK stack1 frame))
          (frame-set-operand-stack stack2 frame))
  :hints (("Goal" :in-theory (enable operand-stack 
                                     frame-set-operand-stack))))

;----------------------------------------------------------------------



(defthm safe-pushcategory2-primitive-type
  (implies (consistent-state s)
           (equal (current-frame (safe-pushcategory2 (tag v type) s))
                  (frame-set-operand-stack 
                   (push (tag v type)
                         (push '(topx . topx) (operand-stack (current-frame s))))
                   (current-frame s))))
  :hints (("Goal" :in-theory (enable safe-pushcategory2  
                                     current-frame
                                     push-stack-of-thread
                                     pushstack))))

;; generally useful! 
         
;----------------------------------------------------------------------


(defthm locals-frame-set-operand-stack
  (equal (LOCALS (FRAME-SET-OPERAND-STACK stack frame))
         (locals frame))
  :hints (("Goal" :in-theory (enable frame-set-operand-stack))))


;----------------------------------------------------------------------


(defthm type-size-2-not-category1
  (implies (equal (type-size type) 2)
           (not (CATEGORY1 (TAG V TYPE))))
  :hints (("Goal" :in-theory (enable category1 type-size))))


;----------------------------------------------------------------------


(defthm framelocals-make-sig-frame
  (equal (BCV::FRAMELOCALS
          (BCV::MAKE-SIG-FRAME locals stack flags))
         locals)
  :hints (("Goal" :in-theory (enable bcv::framelocals 
                                     bcv::make-sig-frame))))




(defthm framestack-make-sig-frame
  (equal (BCV::FRAMESTACK
          (BCV::MAKE-SIG-FRAME locals stack flags))
         stack)
  :hints (("Goal" :in-theory (enable bcv::framestack
                                     bcv::make-sig-frame))))


(defthm frameFlags-frame-sig-is
  (equal (BCV::FRAMEFLAGS
          (BCV::MAKE-SIG-FRAME locals stack flags))
         flags)
  :hints (("Goal" :in-theory (enable bcv::frameflags
                                     bcv::make-sig-frame))))


;----------------------------------------------------------------------

(defthm consistent-value-type-size-2-then-category2
  (implies (and (consistent-value (tag v type) type cl hp)
                (equal (type-size type) 2))
           (category2 (tag v type))))

;----------------------------------------------------------------------


(defthm nullp-implied-by
  (implies (and (EQUAL (TAG-OF v ) 'REF)
                (EQUAL (VALUE-OF v) -1))
           (NULLp v))
  :hints (("Goal" :in-theory (enable NULLp wff-REFp tag-of value-of))))


;----------------------------------------------------------------------

;------------ ADDED ---------------------------------------------------

;; (i-am-here) ;; Fri Jul 22 11:11:32 2005

(local 
 (defthm consistent-heap-init-state-bound-then-consistent-obj-init-state
   (implies (and (consistent-heap-init-state hp cl hp-init)
                 (bound? x hp))
            (consistent-object-init-state (binding x hp) cl hp-init))
   :hints (("Goal" :in-theory (e/d (bound? binding) (consistent-object-init-state))))))


(defthm REFp-implies-consistent-object-init-heap
  (implies (and (consistent-state s)
                (REFp v (heap s))
                (not (NULLp v)))
            (consistent-object-init-state (deref2 v (heap s))
                                          (instance-class-table s)
                                          (heap-init-map (aux s))))
  :hints (("Goal" :in-theory (e/d (deref2 consistent-state)
                                  (consistent-object-init-state
                                   binding-rREF-normalize)))))

(local 
 (defthm consistent-heap1-bound-then-consistent-object
   (implies (and (consistent-heap1  hp1 hp cl id)
                 (bound? x hp1))
            (consistent-object (binding x hp1) hp cl))
   :hints (("Goal" :in-theory (e/d (bound? binding) (consistent-object))))))



(defthm REFp-implies-consistent-object
  (implies (and (consistent-state s)
                (REFp v (heap s))
                (not (NULLp v)))
           (consistent-object (deref2 v (heap s))
                              (heap s)
                              (instance-class-table s)))
  :hints (("Goal" :in-theory (e/d (consistent-state consistent-heap
                                                    deref2)
                                  (binding-rREF-normalize
                                   consistent-object)))))

;;; Thu Jul 21 23:48:16 2005.
;;; note this is not a general enough theorem.


;----------------------------------------------------------------------

(local 
 (defthm NULLp-implies-REFp
   (implies (NULLp v)
            (REFp v hp))
   :hints (("Goal" :in-theory (enable NULLp REFp)))))


(defthm consistent-value-not-primitive-type-REFp
  (implies (and (not (primitive-type? type))
                (consistent-value (tag v type) type (instance-class-table s)
                                  (heap s)))
           (REFp (tag v type) (heap s)))
  :hints (("Goal" :in-theory (e/d (consistent-value) (primitive-type? NULLp REFp)))))


;----------------------------------------------------------------------

(defthm bcv-size-of-object-equal
  (implies (and (consistent-object (deref2 v (heap s))
                                   (heap s)
                                   (instance-class-table s))
                 (consistent-state s))
           (equal (bcv::sizeof (fix-sig (obj-type (deref2 v (heap s))))) 1)))

;----------------------------------------------------------------------

;; quite some skip proofs here!! 
;; Fri Jul 22 00:10:05 2005
;;
;; Fri Jul 22 11:43:16 2005 removed!! 

(defthm pending-exception-popStack
  (equal (pending-exception (popstack s))
         (pending-exception s)))

;----------------------------------------------------------------------

(in-theory (disable djvm-translate-int-type))

;----------------------------------------------------------------------

(defthm consistent-state-not-initilized
  (implies (not (equal type 'uninitializedthis))
           (not (EQUAL (DJVM-TRANSLATE-INT-TYPE TYPE)
                       'UNINITIALIZEDTHIS)))
  :hints (("Goal" :in-theory (enable djvm-translate-int-type))))


(defthm consistent-state-not-initilized-primitive-ype
  (implies (primitive-type? type)
           (not (EQUAL (DJVM-TRANSLATE-INT-TYPE TYPE)
                       'UNINITIALIZEDTHIS)))
  :hints (("Goal" :in-theory (enable primitive-type? djvm-translate-int-type))))


; Thu Aug  4 23:50:37 2005

;----------------------------------------------------------------------

;;(include-book "../../DJVM/consistent-state-strong") ;; Thu Aug  4 23:50:28 2005
;;(include-book "../../DJVM/consistent-state-obj-init-properties-export")

;----------------------------------------------------------------------

