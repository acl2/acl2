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




(encapsulate ()
  (local (include-book "base-frame-sig-expansion-support"))
  (defthm frame-sig-of-push-stack-is-frame-push-value-sig
    (implies (and (consistent-value-x v (instance-class-table s) (heap s))
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
                                                     hp-init))))))



;; (encapsulate ()
;;   (local (include-book "base-frame-sig-expansion-support"))
;;   (defthm frame-sig-of-push-stack-is-frame-push-value-sig
;;     (implies (and (not (equal (value-sig v (instance-class-table s) (heap s) (heap-init-map
;;                                                                               (aux s))
;;                                          (method-ptr (current-frame s)))
;;                               'uninitializedThis))
;;                   (consistent-value-x v (instance-class-table s) (heap s))
;;                   (category1 v)
;;                   (consistent-state s)
;;                   (equal (instance-class-table s) cl) 
;;                   (equal (heap s) hp)
;;                   (equal (heap-init-map (aux s)) hp-init))
;;              (equal (FRAME-SIG  (CURRENT-FRAME (PUSHSTACK v s))  cl hp hp-init)
;;                     (frame-push-value-sig (value-sig v cl hp hp-init
;;                                                      (method-ptr (current-frame
;;                                                                   s)))
;;                                           (frame-sig (current-frame s) cl hp
;;                                                      hp-init))))))



;----------------------------------------------------------------------

;;; some thing generally useful We want rewrite value-sig to fix-sig which we
;;; can prove more properities relatively easily value-sig has too many
;;; parameters!!
;;;


(encapsulate () 
   (local (include-book "base-bcv-djvm-assignable"))
   (defthm value-sig-being-fix-sig
     (implies (and (REFp v hp)
                   (not (NULLp v))
                   (not (consp (deref2-init v hp-init))))
              (equal (value-sig v cl hp hp-init method-ptr)
                     (fix-sig (obj-type (deref2 v hp)))))))

(defthm fix-sig-never-equal-uninitialized
  (not (equal (fix-sig typ) 'uninitializedThis)))
  

;----------------------------------------------------------------------
;;
;;
;; specific rule about value from array. 
;; 


(defthm element-at-array-normalize
  (equal (element-at-array index (value-of v) s)
         (element-at-array index (rREF v) s))
  :hints (("Goal" :in-theory (enable value-of rREF))))


;; isArrayType is relieved by first appealling to 
;;         wff-array-type
;; then in turn to 
;;          check-array-guard
;; in turn to 
;;          array-type-s 
;;
;; This is a bit magic. because of the rules in base-consistent-state.lisp!! 


(encapsulate ()
 (local (include-book "base-array-facts"))
 (defthm isArrayType-componenent-type-not-primitive-implies-initialized
   (implies (and (isArrayType (obj-type (deref2 v (heap s))))  
                 ;;; this is relieved by 
                 (not (primitive-type? (array-component-type 
                                        (obj-type (deref2 v (heap s))))))
                 (consistent-state s)
                 (not (equal (element-at-array index (rREF v) s) -1))
                 (check-array (rREF v) index s))
            (NOT (CONSP (DEREF2-INIT (TAG-REF (ELEMENT-AT-ARRAY INDEX
                                                                (rREF v)
                                                                S))
                                     (heap-init-map (aux s))))))))


(encapsulate () 
   (local (include-book "base-bcv-djvm-assignable"))
   (in-theory (disable TAG-REF-TAG))

   (defthm tag-tag-REF-specific
     (implies (not (primitive-type? (array-component-type (obj-type (deref2 v hp)))))
              (equal (tag x (array-component-type (obj-type (deref2 v hp))))
                     (tag-REF x)))
     :hints (("Goal" :in-theory (enable tag tag-REF)))))


(encapsulate ()
   (local (include-book "base-array-facts"))
   (defthm element-of-array-is-consistent-value-specific-AARARY
     (implies (and (isArrayType (obj-type (deref2 v (heap s))))
                   (not (primitive-type? (array-component-type (obj-type (deref2 v
                                                                                 (heap s))))))
                   (check-array (rREF v) index s)
                   (consistent-state s)
                   (equal (instance-class-table s) cl)
                   (equal (heap s) hp))
              (consistent-value-x  (tag-REF (element-at-array index (rREF v) s))
                                   cl hp))))


;; We want consistent-value-x, because we want category1.
;; this isn't a very good general rule. 


(defthm consistent-value-tag-REF-implies-REFp-specific-x
   (implies (and (consistent-value-x (tag-REF v) (instance-class-table s) (heap s))
                 (equal (heap s) hp))
            (REFp (tag-REF v) hp))
   :hints (("Goal" :in-theory (e/d () (REFp)))))


(local 
 (defthm REFp-implies-category1-frame-expansion
   (implies (REFp v hp)
            (category1 v))
  :hints (("Goal" :in-theory (enable REFp category1 NULLp wff-REFp)))))


(defthm tag-of-tag-REF
  (equal (tag-of (tag-REF v)) 'REF)
  :hints (("Goal" :in-theory (enable tag-of tag-REF))))


(defthm consistent-value-tag-category1-tag-ref-b-specific
  (implies (consistent-value-x (tag-ref (element-at-array array-ref index s)) (instance-class-table s) (heap s))
           (category1 (tag-ref (element-at-array array-ref index s))))
  :hints (("Goal" :in-theory (enable consistent-value-x ))))

;
; All above rules is about to conclude what is pushed on the operand stack is a
; Category 1 value.  frame-sig-of-push-stack-is-frame-push-value-sig
;

;----------------------------------------------------------------------


(defthm value-sig-being-fix-sig-NULL-short-cut
  (implies (NULLp v)
           (equal (value-sig v cl hp hp-init method-ptr)
                  'NULL))
  :hints (("Goal" :in-theory (enable REFp value-sig))))


;----------------------------------------------------------------------


;----------------------------------------------------------------------

(in-theory (disable arg))

;; now we need to show 

;;; if we copy some value out from local and push it to the opstack
;;; we will not change the sig flag. 
;;;

;(i-am-here)

(local 
 (encapsulate ()
  (local (include-book "base-consistent-state-more"))
  (defthm pushStack-does-not-change-locals
    (equal (locals (current-frame (pushStack v s)))
           (locals (current-frame s))))))





(local 
 (encapsulate ()
    (local (include-book "base-consistent-state-more"))
    (defthm operand-stack-current-frame-pushStack
      (implies (consistent-state s)
               (equal (operand-stack (current-frame (pushStack v s)))
                      (push v (operand-stack (current-frame s))))))))


(local 
 (defthm bcv-make-sig-frame-normalize
   (equal (bcv::make-sig-frame l s f)
          (make-sig-frame l s f))
   :hints (("Goal" :in-theory (enable make-sig-frame bcv::make-sig-frame)))))


(local 
 (defthm bcv-make-sig-frame-accessor
   (and (equal (bcv::frameStack  (make-sig-frame l s f)) s)
        (equal (bcv::frameLocals (make-sig-frame l s f)) l)
        (equal (bcv::frameFlags  (make-sig-frame l s f)) f))
   :hints (("Goal" :in-theory (enable make-sig-frame
                                      bcv::frameFlags bcv::frameLocals
                                      bcv::frameStack)))))


;; (i-am-here) ;; Wed Jul 27 00:06:22 2005

(local 
 (defthm equal-minus-one-minus-one-plus-negative-two
   (equal (+ -1 -1 i)
          (+ -2 i))))

(local 
 (defthm nth-i-specific
   (implies (and (< 0 i)
                 (integerp i))
            (equal (nth (- i 1) (cdr locals))
                   (nth i locals)))))


(local 
 (defthm nth-i-specific-2
   (implies (and (< 1 i)
                 (integerp i))
            (equal (nth (- i 2) (cddr locals))
                   (nth i locals)))
   :hints (("Goal" 
            :in-theory (disable nth-i-specific)
            :use ((:instance nth-i-specific
                             (i (- i 1))
                             (locals (cdr locals)))
                  (:instance nth-i-specific))
            :do-not-induct t))))

(local 
 (defthm valid-local-index-implies-i-positive
   (implies (VALID-LOCAL-INDEX (+ -2 I) any)
            (< 1 i))
   :rule-classes :forward-chaining))



(local 
 (defthm valid-local-index-in-locals-mem-locals-sig
   (implies (and (consistent-locals locals cl hp)
                 (integerp i)
                 (valid-local-index i locals))
            (mem (value-sig (nth i locals) cl hp hp-init method-ptr)
                 (locals-sig locals cl hp hp-init method-ptr)))))


;; (local 
;;  (defthm mem-uninitialziedThis-gen
;;    (implies (mem 'uninitializedthis l)
;;             (equal (gen-flags l) '(flagThisUninit)))))


;; (local 
;;  (defthm mem-uninitialziedThis-gen-general
;;    (implies (and (equal x 'uninitializedthis)
;;                  (mem x l))
;;             (equal (gen-flags l) '(flagThisUninit)))))



;; (local 
;;  (defthm valid-index-i-value-sig-uninitializedThis-is-flag
;;   (implies (and (consistent-locals locals cl hp) 
;;                 (integerp i)
;;                 (valid-local-index i locals)
;;                 (equal (value-sig (nth i locals) cl hp hp-init method-ptr)
;;                        'uninitializedthis))
;;            (equal (gen-flags (locals-sig locals cl hp hp-init method-ptr))
;;                   '(flagThisUninit)))
;;   :hints (("Goal" :in-theory (disable locals-sig gen-flags)
;;            :do-not-induct t
;;            :use ((:instance valid-local-index-in-locals-mem-locals-sig)
;;                  (:instance mem-uninitialziedThis-gen-general 
;;                             (x (value-sig (nth i locals) cl hp hp-init
;;                                           method-ptr))
;;                             (l (locals-sig locals cl hp hp-init method-ptr))))))))

;; ;; this above is extremely awkward!! 

;; (i-am-here) ;; Sun Jul 31 15:16:23 2005

(local (in-theory (disable frame-aux)))
(local (include-book "base-consistent-state-more"))

;;(i-am-here) ;; Tue Aug 16 18:05:42 2005

(defthm frame-sig-push-value-from-local-is
  (mylet* ((locals (locals (current-frame s)))
           (v (nth i locals)))
          (implies (and (consistent-state s)
                        (consistent-locals locals cl hp)
                        (category1 v)
                        (integerp i)
                        (valid-local-index i locals))
                   (equal (frame-sig (current-frame (pushStack v s)) cl hp hp-init)
                          (frame-push-value-sig (value-sig v cl hp hp-init 
                                                           (method-ptr (current-frame s)))
                                                (frame-sig (current-frame s)
                                                           cl hp hp-init)))))
  :hints (("Goal" :in-theory (e/d (frame-sig push pop
                                   frame-push-value-sig) (consistent-locals))
           :do-not-induct t)))

(local (in-theory (enable push pop top)))


;; (defthm frame-sig-push-value-from-local-is
;;   (mylet* ((locals (locals (current-frame s)))
;;            (v (nth i locals)))
;;           (implies (and (consistent-state s)
;;                         (consistent-locals locals cl hp)
;;                         (category1 v)
;;                         (integerp i)
;;                         (valid-local-index i locals))
;;                    (equal (frame-sig (current-frame (pushStack v s)) cl hp hp-init)
;;                           (frame-push-value-sig (value-sig v cl hp hp-init 
;;                                                            (method-ptr (current-frame s)))
;;                                                 (frame-sig (current-frame s)
;;                                                            cl hp hp-init)))))
;;   :hints (("Goal" :in-theory (e/d (frame-sig frame-push-value-sig) (consistent-locals))
;;            :cases ((equal (value-sig (nth i (locals (current-frame s))) cl hp hp-init
;;                                      (method-ptr (current-frame s)))
;;                           'uninitializedthis))
;;            :do-not-induct t)))





;----------------------------------------------------------------------

;; 1x (:REWRITE FRAME-SIG-OF-PUSH-STACK-IS-FRAME-PUSH-VALUE-SIG) failed
;; because :HYP 1 rewrote to 
;; (NOT
;;  (EQUAL
;;   (VALUE-SIG
;;    (TAG-REF
;;     (LEN
;;      (HEAP
;;         (GETARRAYCLASS (NORMALIZE-TYPE-REP (ARG INST))
;;                        (RESOLVECLASSREFERENCE (NORMALIZE-TYPE-REP (ARG INST))
;;                                               S)))))
;;    (INSTANCE-CLASS-TABLE
;;         (GETARRAYCLASS (NORMALIZE-TYPE-REP (ARG INST))
;;                        (RESOLVECLASSREFERENCE (NORMALIZE-TYPE-REP (ARG INST))
;;                                               S)))
;;    (BIND
;;     (LEN
;;      (HEAP
;;         (GETARRAYCLASS (NORMALIZE-TYPE-REP (ARG INST))
;;                        (RESOLVECLASSREFERENCE (NORMALIZE-TYPE-REP (ARG INST))
;;                                               S))))
;;     (CAR
;;      (BUILD-AN-ARRAY-INSTANCE
;;         (NORMALIZE-TYPE-REP (ARG INST))
;;         (VALUE-OF (TOPSTACK S))
;;         (GETARRAYCLASS (NORMALIZE-TYPE-REP (ARG INST))
;;                        (RESOLVECLASSREFERENCE (NORMALIZE-TYPE-REP (ARG INST))
;;                                               S))))
;;     (HEAP
;;         (GETARRAYCLASS (NORMALIZE-TYPE-REP (ARG INST))
;;                        (RESOLVECLASSREFERENCE (NORMALIZE-TYPE-REP (ARG INST))
;;                                               S))))
;;    (HEAP-INIT-MAP
;;     (AUX
;;         (GETARRAYCLASS (NORMALIZE-TYPE-REP (ARG INST))
;;                        (RESOLVECLASSREFERENCE (NORMALIZE-TYPE-REP (ARG INST))
;;                                               S))))
;;    (METHOD-PTR (CURRENT-FRAME S)))
;;   'UNINITIALIZEDTHIS)).
;; 1)

;; for ANEWARRAY. We need to show tag-REf

(defthm value-sig-of-tag-newly-created-array-instance-not-uninitialized
  (implies (not (bound? ref hp-init))
           (not (equal (value-sig (tag-REF ref) cl 
                                  (bind ref 
                                        (car (build-an-array-instance 
                                              (normalize-type-rep basetype) bound s))
                                        hp)
                                  hp-init
                                  method-ptr)
                       'uninitializedThis)))
  :hints (("Goal" :in-theory (e/d (value-sig build-an-array-instance
                                             deref2-init
                                             tag-REF
                                             REFp
                                             tag-of
                                             rREF bound? 
                                             binding
                                             deref2)
                                  (binding-rref-normalize)))))


(local 
 (defthm assoc-equal-bind
   (assoc-equal ref (bind ref obj hp))))

(local 
 (defthm binding-bind
   (equal (binding ref (bind ref obj hp))
          obj)
   :hints (("Goal" :in-theory (enable binding bind)))))


(local 
 (defthm fix-sig-normalize-type-rep
   (implies (wff-type-rep type)
            (equal (fix-sig (normalize-type-rep type))
                   type))
   :hints (("Goal" :in-theory (enable array-component-type
                                      primitive-type?
                                      isArrayType
                                      array-base-type)))))

(local 
 (defthm fix-sig-list-array
   (equal (FIX-SIG (LIST 'ARRAY x))
          (list 'array (fix-sig x)))
   :hints (("Goal" :in-theory (enable primitive-type? isArrayType)))))



(defthm value-sig-of-tag-newly-created-array-instance-make-array-type
  (implies (and (not (bound? ref hp-init))
                (integerp ref)
                (wff-type-rep basetype)
                (not (nullp (tag-REF ref))))
           (equal (value-sig (tag-REF ref) cl 
                             (bind ref 
                                   (car (build-an-array-instance 
                                         (normalize-type-rep basetype) bound s))
                                   hp)
                             hp-init
                             method-ptr)
                  (make-array-type basetype)))
  :hints (("Goal" :in-theory (e/d (value-sig build-an-array-instance
                                             deref2-init
                                             tag-REF
                                             REFp
                                             value-of
                                             wff-tagged-value
                                             obj-type
                                             common-info
                                             tag-of
                                             wff-REFp
                                             NULLp
                                             bind
                                             binding
                                             isArrayType
                                             primitive-type?
                                             rREF bound?
                                             deref2)
                                  (binding-rref-normalize
                                   fix-sig normalize-type-rep
                                   wff-type-rep)))))



(in-theory (disable consistent-frame))


(encapsulate ()
 (local 
  (encapsulate () 
               (local (include-book "base-loader-preserve-consistent-state"))
               (defthm consistent-state-implies-not-bound-len-heap
                 (implies (consistent-state s)
                          (not (bound? (len (heap s)) (heap s)))))


               (defthm consistent-heap-array-init-state2-bound-bound-b
                 (implies (and (consistent-heap-array-init-state2 hp hp-init)
                               (not (bound? ref hp)))
                          (not (bound? ref hp-init)))
                 :hints (("Goal" :in-theory (enable bound?))))))



 (local 
  (defthm consistent-state-implies-not-bound-heap-not-bound-heap-init
    (implies (and (consistent-state s)
                  (not (bound? x (heap s))))
             (not (bound? x (heap-init-map (aux s)))))
    :hints (("Goal" :in-theory (enable consistent-state
                                       consistent-heap-array-init-state)))))


 (defthm consistent-state-implies-not-bind-len-heap-init
   (implies (and (consistent-state s)
                 (equal (heap s) hp))
            (not (bound? (len hp)
                         (heap-init-map (aux s)))))))


(defthm consistent-state-implies-not-bind-len-heap-init-2
  (implies (and (consistent-state s)
                (equal (heap-init-map (aux s)) hp-init))
           (not (bound? (len (heap s))
                        hp-init))))




(encapsulate ()
  (local (include-book "base-frame-sig-after-class-loading"))

  (defthm equal-frame-sig-when-consistent-resolveClassReference
    (implies (and (consistent-frame frame
                                    (instance-class-table s)
                                    (heap s))
                  (equal (heap (resolveClassreference any s)) hp)
                  (equal (heap-init-map (aux (resolveClassreference any s)))
                         hp-init)
                  (consistent-state s))
             (equal (frame-sig frame 
                               (instance-class-table (resolveClassreference any s))
                               hp
                               hp-init)
                    (frame-sig frame (instance-class-table s) (heap s) 
                               (heap-init-map (aux s))))))



  
  (defthm equal-frame-sig-when-consistent-getArrayClass
    (implies (and (consistent-frame frame
                                    (instance-class-table s)
                                    (heap s))
                  (equal (heap (getArrayClass any s)) hp)
                  (equal (heap-init-map (aux (getArrayClass any s))) hp-init)
                  (consistent-state s))
             (equal (frame-sig frame 
                               (instance-class-table (getArrayClass any s))
                               hp
                               hp-init)
                    (frame-sig frame (instance-class-table s) (heap s) 
                               (heap-init-map (aux s))))))

  
  (defthm equal-frame-sig-bind-extra-object
    (implies (and (not (bound? ref hp))
                  (consistent-frame frame cl hp))
             (equal (frame-sig frame cl (bind ref obj hp) hp-init)
                    (frame-sig frame cl hp hp-init)))))


;; (i-am-here) ;; 

(local 
 (defthm consistent-state-consistent-frame-general
   (implies (and (consistent-state s)
                 (equal (instance-class-table s) cl)
                 (equal (heap s) hp))
            (consistent-frame (current-frame s) cl hp))))

           

(defthm consistent-frame-consistent-state-pushStack-b
  (implies (and (consistent-state (pushstack v s))
                (equal (instance-class-table (pushstack v s)) cl)
                (equal (heap (pushstack v s)) hp))
           (consistent-frame (current-frame (pushstack v s))
                             cl 
                             hp)))





(defthm consistent-frame-consistent-state-getArrayClass-b
  (implies (and (consistent-state (getArrayClass any s))
                (equal (current-frame (getArrayClass any s)) frame)
                (equal (heap (getArrayClass any s)) hp))
           (consistent-frame frame
                             (instance-class-table 
                              (getArrayClass any s))
                             hp)))



(defthm consistent-frame-consistent-state-resolveClassReference-b
  (implies (and (consistent-state (resolveClassReference any s))
                (equal (current-frame (resolveClassReference any s)) frame)
                (equal (heap (resolveClassReference any s)) hp))
           (consistent-frame frame
                             (instance-class-table 
                              (resolveClassReference any s))
                             hp))
  :hints (("Goal" :use ((:instance 
                         consistent-state-consistent-frame-general
                         (cl (instance-class-table 
                              (resolveClassReference any s)))
                         (s   (resolveClassReference any s))
                         (hp (heap (resolveClassReference any s))))))))




(defthm consistent-frame-consistent-state-popStack-b
  (implies (and (consistent-state (popStack s))
                (equal (instance-class-table (popStack s)) cl)
                (equal (heap (popStack s)) hp))
           (consistent-frame (current-frame (popStack s))
                             cl 
                             hp)))



;; (i-am-here) ;; Sun Jun  5 19:32:39 2005



(encapsulate ()
  (local 
    (defthm current-frame-popstack-is
      (implies (consistent-state s)
               (equal (current-frame (popStack s))
                      (frame-set-operand-stack (pop (operand-stack (current-frame s)))
                                               (current-frame s))))
      :hints (("Goal" :in-theory (e/d (popStack current-frame popstack-of-thread)
                                      (topframe-normalization
                                       car-thread-call-normalization))))))

 (local 
  (defthm operand-stack-current-frame-popStack-instance
    (implies (consistent-state s)
             (equal (operand-stack (current-frame (popStack s)))
                    (pop (operand-stack (current-frame s)))))
    :hints (("Goal" :in-theory (enable frame-set-operand-stack)))))


 (local 
  (defthm locals-no-change-popStack-local
    (equal (locals (frame-set-operand-stack any frame))
           (locals frame))
    :hints (("Goal" :in-theory (enable frame-set-operand-stack)))))



 (local 
  (defthm operand-stack-popStack-local
    (equal (operand-stack  (frame-set-operand-stack any frame))
           any)
    :hints (("Goal" :in-theory (enable frame-set-operand-stack)))))



 ;; (local 
 ;;  (encapsulate () 
 ;;      (local (include-book "base-consistent-state-more"))
 ;;      (defthm locals-no-change-popStack
 ;;        (equal (locals (current-frame (popStack s)))
 ;;               (locals (current-frame s))))))


 (local 
  (defthm wff-call-frame-frame-set-operand-stack
    (implies (and (wff-call-frame frame)
                  (true-listp any))
             (wff-call-frame (frame-set-operand-stack any frame)))
    :hints (("Goal" :in-theory (enable wff-call-frame 
                                       make-frame
                                       locals 
                                       operand-stack
                                       frame-set-operand-stack)))))


 (local 
  (defthm sync-obj-ref-frame-set-opstack-no-change
    (equal (sync-obj-ref (frame-set-operand-stack any frame))
           (sync-obj-ref frame))
    :hints (("Goal" :in-theory (enable frame-set-operand-stack)))))

 (defthm consistent-frame-consistent-frame-canPop1
   (implies (and (consistent-state s)
                 (consistent-frame (current-frame s) cl hp)
                 (topstack-guard-strong s))
            (consistent-frame (current-frame (popStack s))
                              cl hp))
   :hints (("Goal" :in-theory (e/d (consistent-frame
                                    topstack-guard-strong)
                                   ())))))



(encapsulate () 
 (local (include-book "base-load-class-normalize"))

 (defthm getArrayClass-reduce
   (and (equal (PC (GETARRAYCLASS any s))
               (pc s))
        (equal (current-thread (getarrayclass any s))
               (current-thread s))
        (equal (thread-table (getarrayclass any s))
               (thread-table s))
        (equal (current-frame (getarrayclass any s))
               (current-frame s))
        (equal (heap-init-map (aux (getarrayclass any s)))
               (heap-init-map (aux s))))
   :hints (("Goal" :in-theory (e/d (getarrayclass)
                                   (heap-init-map)))))


;;; getArrayClass will change heap, 

 (defthm resolveClassReference-reduce
   (and (equal (PC (resolveClassReference any s))
               (pc s))
        (equal (current-thread (resolveClassReference any s))
               (current-thread s))
        (equal (thread-table (resolveClassReference any s))
               (thread-table s))
        (equal (heap-init-map (aux (resolveClassReference any s)))
               (heap-init-map (aux s)))
        (equal (current-frame (resolveClassReference any s))
               (current-frame s)))
   :hints (("Goal" :in-theory (e/d (resolveClassReference)
                                   (heap-init-map))))))

 






(local 
 (defthm current-frame-equal-if-thread-thread-table-no-change
   (implies (and (equal (thread-table s2) (thread-table s1))
                 (equal (current-thread s2) (current-thread s1)))
            (equal (current-frame s2)
                   (current-frame s1)))
   :hints (("Goal" :in-theory (enable current-frame)))))



(local 
 (defthm current-frame-equal-if-thread-thread-table-no-change-specific
   (implies (and (equal (thread-table s2) (thread-table s1))
                 (equal (current-thread s2) (current-thread s1)))
            (equal (current-frame (popStack s2))
                   (current-frame (popStack s1))))
   :hints (("Goal" :in-theory (enable current-frame popStack)))))





(defthm current-frame-popstack-getArrayClass
  (equal 
   (CURRENT-FRAME
    (POPSTACK
     (GETARRAYCLASS any s)))
   (current-frame (popstack s)))
  :hints (("Goal" :in-theory (disable getarrayclass)
           :use ((:instance
                  current-frame-equal-if-thread-thread-table-no-change-specific
                  (s2 (getarrayclass any s))
                  (s1 s))))))


;;; this should be pro


(defthm current-frame-popstack-resolveClassReference
  (equal 
   (CURRENT-FRAME
    (POPSTACK
     (resolveClassReference any s)))
   (current-frame (popstack s)))
  :hints (("Goal" :in-theory (disable resolveClassReference)
           :use ((:instance
                  current-frame-equal-if-thread-thread-table-no-change-specific
                  (s2 (resolveClassReference any s))
                  (s1 s))))))




;; (skip-proofs 
;;    (defthm consistent-frame-consistent-state-bind-new-obj-b
;;      (implies (and (consistent-state (state-set-heap (bind ref obj (heap s)) s))
;;                    (equal (current-frame s) frame)
;;                    (equal (instance-class-table s) cl))
;;               (consistent-frame frame
;;                                 cl 
;;                                 (bind ref obj (heap s))))))
                                



(encapsulate () 
  (local (include-book "base-frame-sig-after-class-loading"))
  (defthm equal-frame-sig-bind-extra-object
    (implies (and (not (bound? ref hp))
                  (consistent-frame frame cl hp))
             (equal (frame-sig frame cl (bind ref obj hp) hp-init)
                    (frame-sig frame cl hp hp-init)))))




(encapsulate () 
 (local (include-book "base-loader-preserve-consistent-state"))
 (defthm consistent-state-implies-not-bound
   (implies (consistent-state s)
            (not (bound? (len (heap s))
                         (heap s))))))




;----------------------------------------------------------------------

;; (i-am-here) ;;; Wed Jul 20 23:54:44 2005
;; Thu Jul 21 15:40:21 2005

(local 
 (defthm value-sig-primitive-type-never-uninitialized
   (implies (primitive-type? type)
            (equal (value-sig (TAG V TYPE) cl hp hp-init method-ptr)
                   (djvm-translate-int-type type)))
   :hints (("Goal" :in-theory (enable primitive-type? value-sig fix-sig 
                                      REFp wff-REFp NULLp
                                      tag tag-of)))))
                     

;; (i-am-here) ;; Fri Jul 22 18:06:22 2005

(defthm frame-sig-current-pushStack-is-when-primitive-type
  (implies (and (primitive-type? type)
                (category1 (tag v type))
                (consistent-state s)
                (equal (instance-class-table s) cl)
                (equal (heap s) hp)
                (equal (heap-init-map (aux s)) hp-init))
           (equal (frame-sig
                   (current-frame 
                    (pushstack (tag v type) s))
                   cl hp hp-init)
                  (frame-push-value-sig
                    (djvm-translate-int-type type)
                    (frame-sig (CURRENT-FRAME s)
                               cl hp hp-init))))
  :hints (("Goal" :in-theory (enable frame-push-value-sig 
                                     frame-sig))))
                   
(defthm category2-implies-not-category1
  (implies (category2 (tag v type))
           (not (category1 (tag v type))))
  :hints (("Goal" :in-theory (enable category1 category2))))

;;
;; seem to be generally useful! 
;;

(local (in-theory (disable canPopCategory1 category1 
                           push
                           category2 canPopCategory2)))


(defthm canPopCategory1-not-pushCategory2
  (implies (category2 (tag v type))
           (not (canPopCategory1 (push (tag v type) stack))))
  :hints (("Goal" :in-theory (enable canPopCategory1 category2 push category1))))


(defthm category2-implies-bcv-size-2
  (implies (equal (bcv::sizeof type) 1)
           (not (category2 (tag v type))))
  :hints (("Goal" :in-theory (enable category2 bcv::sizeof tag tag-of))))


;; (defthm operand-stack-current-frame-pushStack
  
;;   (OPERAND-STACK (CURRENT-FRAME (PUSHSTACK (TAG V TYPE)
;;                                            (PUSHSTACK 'TOPX S))))



;; (defthm safe-pushcategory2-primitive-type
;;   (implies (consistent-state s)
;;            (equal (current-frame (safe-pushcategory2 (tag v type) s))
;;                   (frame-set-operand-stack 
;;                    (push (tag v type)
;;                          (push 'topx (operand-stack (current-frame s))))
;;                    (current-frame s))))
;;   :hints (("Goal" :in-theory (enable safe-pushcategory2  
;;                                      current-frame
;;                                      push-stack-of-thread
;;                                      pushstack))))
         

(defthm canPopCategory2-pushCategory2
  (implies (category2 (tag v type))
           (canPopCategory2 (push (tag v type) (push '(topx . topx)  stack))))
  :hints (("Goal" :in-theory (enable canPopCategory1 category2 canPopCategory2 push category1))))

;; (local 
;;  (defthm 
;;    (category2 (tag v type))
;;        (OPSTACK-SIG (PUSH (TAG V TYPE)
;;                           (PUSH 'TOPX
;;                                 (OPERAND-STACK (CURRENT-FRAME S))))
;;                     (INSTANCE-CLASS-TABLE S)
;;                     (HEAP S)
;;                     (HEAP-INIT-MAP (AUX S))
;;                     (METHOD-PTR (CURRENT-FRAME S)))


(local 
 (defthm category2-implies-primitive-type
   (implies (category2 (tag v type))
            (primitive-type? type))
   :hints (("Goal" :in-theory (enable category2 tag tag-of primitive-type?)))
   :rule-classes :forward-chaining))


(local 
 (defthm value-sig-category2
  (implies (category2 (tag v type))
           (equal (VALUE-SIG
                   (TAG v type) 
                   cl hp hp-init method-ptr)
                  type))
  :hints (("Goal" :in-theory (enable djvm-translate-int-type)))))


;;(i-am-here) ;; Tue Jul 26 20:04:45 2005

(local 
 (defthm opstack-sig-push-tag-v-type
   (implies (category2 (tag v type))
            (equal (opstack-sig (push (tag v type) (push '(topx . topx) stack))
                                cl hp hp-init method-ptr)
                   (push 'topx (push type (opstack-sig stack cl hp hp-init
                                                       method-ptr)))))
   :hints (("Goal" :expand (opstack-sig (push (tag v type) (push '(topx . topx) stack))
                                cl hp hp-init method-ptr)
            :use ((:instance canPopCategory1-not-pushCategory2))
            :in-theory (enable push canPopCategory1
                               canPopCategory2 canPopCategory2)))))

;;; get rid of it
;;;
;;; It not longer matters that value-sig is 'uninitializedThis or not!! 
;;; We made the change!! Sun Jul 31 14:09:23 2005
;;; see notes on fixing the Flags!! 

;; (local 
;;  (defthm gen-flags-no-change-push-primitive-type
;;    (implies (primitive-type? type)
;;             (equal (gen-flags (push type stack))
;;                    (gen-flags stack)))
;;    :hints (("Goal" :in-theory (enable push)))))


;; (local 
;;  (defthm gen-flags-no-change-push-topx
;;    (equal (gen-flags (push 'topx stack))
;;           (gen-flags stack))
;;    :hints (("Goal" :in-theory (enable push)))))
                       

(defthm frame-sig-current-pushStack-is-when-primitive-type-2
  (implies (and (primitive-type? type)
                (category2 (tag v type))
                (consistent-state s)
                (equal (instance-class-table s) cl)
                (equal (heap s) hp)
                (equal (heap-init-map (aux s)) hp-init))
           (equal (frame-sig
                   (current-frame 
                    (pushStack (tag v type)
                               (pushStack '(topx . topx) s)))
                   cl hp hp-init)
                  (frame-push-value-sig-g
                   type (frame-sig (CURRENT-FRAME s)
                                   cl hp hp-init))))
  :hints (("Goal" :in-theory (enable frame-push-value-sig 
                                     safe-pushcategory2
                                     frame-sig)
           :use ((:instance safe-pushcategory2-primitive-type)))))


;----------------------------------------------------------------------

;; (i-am-here) ;; Sun Aug  7 22:07:35 2005

(local 
 (encapsulate () 
  (local (include-book "base-object-field-always-initialized"))
  (defthm object-field-is-always-initialized
    (implies (and (case-split (not (primitive-type? 
                                    (get-field-type
                                     fieldclassname
                                     fieldname cl))))
                  (not (isArrayType (obj-type (deref2 v (heap s)))))
                  (not (bound? nil hp-init))
                  (not (bound? -1 hp-init))
                  (consistent-object-init-state 
                   (deref2 v (heap s))
                   cl hp-init)
                  (consistent-object (deref2 v (heap s))
                                     (heap s)
                                     cl))
             (not (bound? (m6-getfield fieldclassname
                                       fieldname
                                       (rREF v) s)
                          hp-init))))))



(local  
 (encapsulate () 
  (local (include-book "base-lookupfield-get-field-type"))
  (defthm lookupfield-field-type-equal
    (implies (and (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR fieldcp) S)
                  (consistent-state s))
             (equal (get-field-type 
                     (FIELD-CLASSNAME (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR fieldcp)
                                                   S))
                     (fieldcp-fieldname fieldcp)
                     (instance-class-table s))
                    (fieldcp-fieldtype fieldcp))))))


(local 
 (defthm not-bound-implies-not-deref
   (implies (not (bound? (m6-getfield cn fn (rREF v) s) hp-init))
            (not (consp (deref2-init (tag (m6-getfield cn fn (rREF v) s)
                                          ft)
                                     hp-init))))
   :hints (("Goal" :in-theory (e/d (deref2-init bound? tag binding deref2 rREF) 
                                   (m6-getfield binding-rref-normalize))))))




;; (CONSISTENT-JVP-INIT-STATE (JAVA-VISIBLE-PORTION (DEREF2 V (HEAP S)))
;;                            (INSTANCE-CLASS-TABLE S)
;;                            (HEAP-INIT-MAP (AUX S))).

(local 
 (encapsulate ()
  (local (include-book "base-consistent-state-lookupfield-support"))
  (defthm consistent-state-lookupfield-fail-if-array-type-assignable-into
    (implies (and  (consistent-state s)
                   (isArrayType typ1) 
                   (car (isAssignableTo typ1 (fieldcp-classname fieldcp) s)))
             (not (lookupField (fieldcp-to-field-ptr fieldcp) s)))
    :hints (("Goal" :in-theory (e/d () (consistent-state 
                                        isClassTerm
                                        fieldcp-classname)))))))


;;; proved in base.lisp?? 

;; (defthm REFp-implies-consistent-object-init-heap
;;   (implies (and (consistent-state s)
;;                 (REFp v (heap s))
;;                 (not (NULLp v)))
;;            (consistent-object-init-state (deref2 v (heap s))
;;                                          (instance-class-table s)
;;                                          (heap-init-map (aux s))))


;; (i-am-here) ;; Fri Jul 22 11:57:03 2005

(defthm object-field-is-always-initialized-m6-getfield
  (implies (and (case-split (not (primitive-type?
                                  (fieldcp-fieldtype fieldcp))))
                (lookupfield (fieldcp-to-field-ptr fieldcp) s)
                (consistent-state s)
                (consistent-object-init-state 
                 (deref2 v (heap s))
                 (instance-class-table s) (heap-init-map (aux s)))
                (consistent-object (deref2 v (heap s))
                                   (heap s)
                                   (instance-class-table s))
                (car (isAssignableTo (obj-type (deref2 v (heap s)))
                                     (fieldcp-classname fieldcp) s)))
            (not (consp (deref2-init 
                         (tag (m6-getfield 
                               (field-classname (lookupfield
                                                 (fieldcp-to-field-ptr fieldcp)
                                                 s))
                               (fieldcp-fieldname fieldcp) 
                               (rREF v) s)
                              (fieldcp-fieldtype fieldcp))
                         (heap-init-map (aux s))))))
  :hints (("Goal" 
           :in-theory (disable fieldcp-classname
                               field-classname
                               m6-getfield
                               fieldcp-fieldtype
                               fieldcp-to-field-ptr
                               fieldcp-fieldname)
           :cases ((isArrayType (obj-type (deref2 v (heap s)))))
           :restrict ((object-field-is-always-initialized
                       ((cl (instance-class-table s))))))))



;----------------------------------------------------------------------

;; (defthm consistent-value-not-primitive-type-REFp
;;   (implies (and (consistent-value (tag v type) type cl hp)
;;                 (not (primitive-type? type)))
;;            (REFp v hp)))

;;;
;;; Thu Jul 21 23:59:43 2005. base.lisp!! 
;;;

;;;
;;; skip verify-guard!! recursively skip guards!! 
;;;



(encapsulate ()
 (local (include-book "base-consistent-object-m6-getfield"))
 (defthm consistent-object-consistent-state-m6-getfield-consistent-value
   (implies (and (consistent-state s)
                 (car (isAssignableTo (obj-type (deref2 v (heap s)))
                                      (fieldcp-classname fieldCP)
                                      s))
                 (REFp v (heap s))
                 (equal (FIELD-CLASSNAME (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR fieldcp)
                                                      S))
                        classname)
                 (lookupField (fieldcp-to-field-ptr fieldCP) s)
                 (not (NULLp v)))
            (CONSISTENT-VALUE
             (TAG (M6-GETFIELD classname
                               (fieldcp-fieldname fieldcp)
                               (RREF v)
                               S)
                  (fieldcp-fieldtype fieldcp))
             (fieldcp-fieldtype fieldcp)
             (INSTANCE-CLASS-TABLE S)
             (HEAP S)))))




(defthm make-sig-frame-equal-normalize
  (equal (make-sig-frame locals stack flags)
         (bcv::make-sig-frame locals stack flags))
  :hints (("Goal" :in-theory (enable make-sig-frame
                                     bcv::make-sig-frame))))


;----------------------------------------------------------------------


(defthm type-size-bcv-sizeof
  (implies (primitive-type? type)
           (EQUAL (bcv::sizeof (djvm-translate-int-type type))
                  (type-size type)))
  :hints (("Goal" :in-theory (enable type-size bcv::sizeof djvm-translate-int-type))))
 
;; Fri Jul 22 00:16:24 2005

;----------------------------------------------------------------------


(defthm not-primitive-type-djvm-translate-int-type-identity
  (implies (not (primitive-type? type))
           (equal (djvm-translate-int-type type)
                  type))
  :hints (("Goal" :in-theory (enable primitive-type? djvm-translate-int-type))))



(defthm size-2-type-djvm-translate-int-type-identity
  (implies (equal (type-size type) 2)
           (equal (djvm-translate-int-type type)
                  type))
  :hints (("Goal" :in-theory (enable primitive-type?
                                     djvm-translate-int-type))))



(in-theory (disable push bcv::prefix-class))


;----------------------------------------------------------------------

;; Sat Jul 30 17:00:20 2005

;; (i-am-here) ;; Sat Jul 30 17:00:33 2005

(defthm consp-locals-implies-consps-locals-sig
  (implies (consp locals)
           (consp (locals-sig locals cl hp hp-init method-ptr))))



(encapsulate () 
 (local  
  (defthm value-sig-topx-is-topx
    (implies (equal (tag-of v) 'topx)
             (equal (VALUE-SIG v CL HP HP-INIT METHOD-PTR)
                    'topx))
    :hints (("Goal" :in-theory (enable value-sig NULLp REFp wff-REFp)))))

 (defthm locals-sig-consistent-sig-locals-implies-cdr
   (implies (consistent-locals locals cl hp)
            (equal (cdr (locals-sig locals cl hp hp-init method-ptr))
                   (locals-sig (cdr locals) cl hp hp-init method-ptr)))
   :hints (("Goal" :in-theory (e/d (category2 category1) ())))))

;;; not very sure where we want this theorem!! 

(local (in-theory (disable bcv-make-sig-frame-normalize)))

(defthm frame-aux-frame-set-locals-not-change
  (equal (frame-aux (frame-set-locals locals frame))
         (frame-aux frame))
  :hints (("Goal" :in-theory (enable frame-set-locals))))

(defthm gen-frame-flags-frame-set-locals-not-change
  (equal (gen-frame-flags (frame-set-locals locals frame) hp-init)
         (gen-frame-flags  frame hp-init))
  :hints (("Goal" :in-theory (enable gen-frame-flags))))


(defthm frame-sig-frame-set-locals
  (equal (frame-sig (frame-set-locals locals frame) cl hp hp-init)
         (make-sig-frame (locals-sig locals cl hp hp-init (method-ptr frame))
                         (opstack-sig (operand-stack frame) cl hp hp-init 
                                      (method-ptr frame))
                         (gen-frame-flags frame hp-init)))
  :hints (("Goal" :in-theory (e/d (gen-frame-flags frame-sig frame-set-locals frame-aux bcv::make-sig-frame)  
                                  ())
           :do-not '(preprocess))))

;;; Sun Jul 31 12:48:06 2005. Fixed see notes about the mistake in handling flags!!
;;; 
;; (defthm frame-sig-frame-set-locals
;;   (equal (frame-sig (frame-set-locals locals frame) cl hp hp-init)
;;          (make-sig-frame (locals-sig locals cl hp hp-init (method-ptr frame))
;;                          (opstack-sig (operand-stack frame) cl hp hp-init 
;;                                       (method-ptr frame))
;;                          (gen-frame-flags (locals-sig locals cl hp hp-init
;;                                                       (method-ptr frame))
;;                                           (opstack-sig (operand-stack frame) cl hp hp-init 
;;                                                        (method-ptr frame)))))
;;   :hints (("Goal" :in-theory (enable frame-sig frame-set-locals)
;;            :do-not '(preprocess))))



;----------------------------------------------------------------------


(defthm REFp-implies-size-1-object
  (implies (and (REFp v (heap s))
                (consistent-state s)
                (equal (instance-class-table s) cl)
                (equal (heap-init-map (aux s)) hp-init)
                (equal (method-ptr (current-frame s)) method-ptr))
           (equal (bcv::sizeof 
                   (value-sig v cl (heap s)
                              hp-init method-ptr)) 
                  1))
  :hints (("Goal" :in-theory (enable value-sig bcv::sizeof))))
                 
;----------------------------------------------------------------------


(local 
 (defthm bcv-modifylocalvariable-reduce-1
   (implies (and (< 0 i)
                 (< i (len locals-sig))
                 (integerp i)
                 (equal (bcv::sizeof (nth (- i 1) locals-sig)) 1)
                 (equal (bcv::sizeof v) 1))
            (equal (bcv::modifylocalvariable i v locals-sig)
                   (update-nth i v locals-sig)))))
                                                 
(local 
 (defthm bcv-modifylocalvariable-reduce-2
   (implies (and (< 0 i)
                 (< i (len locals-sig))
                 (integerp i)
                 (equal (bcv::sizeof (nth (- i 1) locals-sig)) 2)
                 (equal (bcv::sizeof v) 1))

            (equal (bcv::modifylocalvariable i v locals-sig)
                   (update-nth i v (update-nth (- i 1) 'topx locals-sig))))))


;----------------------------------------------------------------------

(local 
 (defthm consistent-locals-implies-wff-tagged-value
   (implies (and (consistent-locals locals cl hp)
                 (<= 0 i)
                 (< i (len locals)))
            (wff-tagged-value (nth i locals)))
   :hints (("Goal" :in-theory (enable category2 category1)))
   :rule-classes :forward-chaining))



(local            
 (defthm consistent-value-x-implies-category1
   (implies (and (EQUAL (BCV::SIZEOF (VALUE-SIG V CL HP HP-INIT METHOD-PTR))
                        1)
                 (CONSISTENT-VALUE-X V CL HP))
            (CATEGORY1 V))
   :hints (("Goal" :in-theory (enable category1 
                                      consistent-value 
                                      value-sig consistent-value-x)))
   :rule-classes :forward-chaining))



(local 
 (defun local-sig-induct-locals-i (locals cl hp i)
   (IF (NOT (CONSP LOCALS))
       (list locals cl hp i)
       (COND ((CATEGORY1LOC LOCALS)
              (AND (OR (EQUAL (TAG-OF (CAR LOCALS)) 'TOPX)
                       (CONSISTENT-VALUE-X (CATEGORY1VALUE LOCALS)
                                           CL HP))
                   (local-sig-induct-locals-i (shift1slot locals) cl hp (- i 1))))
             ((CATEGORY2LOC LOCALS)
              (AND (CONSISTENT-VALUE-X (CATEGORY2VALUE LOCALS)
                                       CL HP)
                   (local-sig-induct-locals-i
                    (SHIFT2SLOT LOCALS) 
                    CL HP
                    (- i 2))))))))


(local 
 (defthm local-sig-frame-set-locals-update-nth-plus-invalidate-1-local
   (implies (and (<= 0 i)
                 (< i (len locals))
                 (integerp i)
                 (consistent-locals locals cl hp)
                 (consistent-value-x v cl hp)
                 (equal (bcv::sizeof (value-sig v cl hp hp-init method-ptr)) 1)
                 (equal (bcv::sizeof (nth (- i 1)
                                          (locals-sig locals cl hp hp-init
                                                      method-ptr))) 1))
            (equal (locals-sig (UPDATE-NTH i v locals) cl hp hp-init method-ptr)
                   (update-nth i (value-sig v cl hp hp-init method-ptr)
                               (locals-sig locals cl hp hp-init method-ptr))))
   :hints (("Goal" :do-not '(generalize)
            :induct (local-sig-induct-locals-i locals cl hp i)))))


(local 
 (defthm value-sig-topx-topx-is-topx
   (EQUAL (VALUE-SIG '(TOPX . TOPX)
                     CL HP HP-INIT METHOD-PTR)
          'TOPX)
   :hints (("Goal" :in-theory (enable value-sig REFp wff-REFp NULLp)))))


(local 
 (defthm local-sig-frame-set-locals-update-nth-plus-invalidate-1-local-2
   (implies (and (< 0 i)
                 (< i (len locals))
                 (integerp i)
                 (consistent-locals locals cl hp)
                 (consistent-value-x v cl hp)
                 (equal (bcv::sizeof (value-sig v cl hp hp-init method-ptr)) 1)
                 (equal (bcv::sizeof (nth (- i 1)
                                          (locals-sig locals cl hp hp-init
                                                      method-ptr))) 2))
            (equal (locals-sig (UPDATE-NTH i v 
                                           (update-nth (- i 1) 
                                                       '(topx . topx) locals)) cl hp hp-init method-ptr)
                   (update-nth i (value-sig v cl hp hp-init method-ptr)
                               (update-nth (- i 1) 'topx
                                           (locals-sig locals cl hp hp-init method-ptr)))))
   :hints (("Goal" :do-not '(generalize)
            :induct (local-sig-induct-locals-i locals cl hp i)))))


;----------------------------------------------------------------------


;; (local 
;;  (defthm bcv-modifylocalvariable-reduce-1
;;    (implies (and (< 0 i)
;;                  (< i (len locals-sig))
;;                  (integerp i)
;;                  (equal (bcv::sizeof (nth (- i 1) locals-sig)) 1)
;;                  (equal (bcv::sizeof v) 1))
;;             (equal (bcv::modifylocalvariable i v locals-sig)
;;                    (update-nth i v locals-sig)))))
                                                 
;; (local 
;;  (defthm bcv-modifylocalvariable-reduce-2
;;    (implies (and (< 0 i)
;;                  (< i (len locals-sig))
;;                  (integerp i)
;;                  (equal (bcv::sizeof (nth (- i 1) locals-sig)) 2)
;;                  (equal (bcv::sizeof v) 1))

;;             (equal (bcv::modifylocalvariable i v locals-sig)
;;                    (update-nth i v (update-nth (- i 1) 'topx locals-sig))))))

(local 
 (defthm len-local-sig-is-len-local
   (implies (consistent-locals locals cl hp)
            (equal (len (locals-sig locals cl hp hp-init method-ptr))
                   (len locals)))))

(local 
 (defthm bcv-size-of-not-1-then-2
   (implies (not (equal (bcv::sizeof type) 1))
            (equal (bcv::sizeof type) 2))
   :hints (("Goal" :in-theory (enable bcv::sizeof)))
   :rule-classes :forward-chaining))


(local 
  (defthm local-sig-frame-set-locals-update-nth-is-modifylocalvariable-size-1
    (implies (and (< 0 i)
                  (< i (len locals))
                  (integerp i)
                  (consistent-locals locals cl hp)
                  (consistent-value-x v cl hp)
                  (equal (bcv::sizeof (nth (- i 1)
                                           (locals-sig locals cl hp hp-init
                                                       method-ptr))) 1)
                  (equal (bcv::sizeof (value-sig v cl hp hp-init method-ptr)) 1))
             (equal (locals-sig (UPDATE-NTH i v locals) cl hp hp-init method-ptr)
                    (bcv::modifylocalvariable i (value-sig v cl hp hp-init method-ptr)
                                              (locals-sig locals cl hp hp-init
                                                          method-ptr))))
    :hints (("Goal" :in-theory (disable locals-sig bcv::modifylocalvariable
                                        consistent-value-x)
             :do-not-induct t))))


(local 
 (defthm value-sig-topx-topx-is-topx-general
   (implies (equal (tag-of value) 'topx)
            (EQUAL (VALUE-SIG value
                              CL HP HP-INIT METHOD-PTR)
                   'TOPX))
   :hints (("Goal" :in-theory (enable value-sig REFp wff-REFp NULLp)))))



(local 
 (defthm nth-local-sig-value-sig-nth
   (implies (and (consistent-locals locals cl hp)
                 (<= 0 i)
                 (< i (len locals))
                 (integerp i))
            (equal (nth i (locals-sig locals cl hp hp-init method-ptr))
                   (value-sig (nth i locals) cl hp hp-init method-ptr)))
   :hints (("Goal" :do-not '(generalize)
            :induct (local-sig-induct-locals-i locals cl hp i)))))

(local 
 (defthm type-size-bcv-size-lemma
   (implies (and (equal (type-size (tag-of v)) 1)
                 (consistent-value-x v (instance-class-table s) (heap s))
                 (consistent-state s))
            (equal (bcv::sizeof (value-sig v (instance-class-table s)
                                           (heap s)
                                           (heap-init-map (aux s))
                                           (method-ptr (current-frame s))))
                   1))
 :hints (("Goal" :in-theory (enable bcv::sizeof value-sig 
                                    consistent-value
                                    consistent-value-x)))))


(local 
 (defthm type-size-bcv-size-lemma
   (implies (and (equal (type-size (tag-of v)) 1)
                 (consistent-value-x v (instance-class-table s) (heap s))
                 (consistent-state s))
            (equal (bcv::sizeof (value-sig v (instance-class-table s)
                                           (heap s)
                                           (heap-init-map (aux s))
                                           (method-ptr (current-frame s))))
                   1))
 :hints (("Goal" :in-theory (enable bcv::sizeof value-sig 
                                    consistent-value
                                    consistent-value-x)))))


(local
 (defthm consistent-locals-not-consistent-value-x-then-topx
   (implies (and (consistent-locals locals cl hp)
                 (case-split (not (equal (tag-of (nth i locals)) 'topx)))
                 (<= 0 i)
                 (< i (len locals)))
            (consistent-value-x (nth i locals) cl hp))
   :hints (("Goal" :induct (local-sig-induct-locals-i locals cl hp i)
            :do-not '(generalize)))))



;;; this is a fairly interesting lemma!! 

;;;
;;; for this above to true. we need that there is no class such as 
;;; 'DOUBLE be its class name!! 
;;;


;; (local 
;;  (defthm type-size-bcv-size
;;    (implies (and (equal (type-size (tag-of (nth i locals))) 1)
;;                  (consistent-locals locals cl hp))
;;             (equal (bcv::sizeof 
;;                     (nth i (locals-sig locals cl hp hp-init method-ptr)))
;;                    1))
;;    :hints (("Goal" :do-not '(generalize)))))





(defthm local-sig-frame-set-locals-update-nth-plus-invalidate-1-strong
  (implies (and (< 0 i)
                (< i (len (locals (current-frame s))))
                (integerp i)
                (consistent-state s)
                (consistent-value-x v (instance-class-table s) (heap s))
                (equal (type-size (tag-of v)) 1)
                (equal (type-size 
                        (tag-of (nth (- i 1) 
                                     (locals (current-frame s))))) 1))
    (equal (locals-sig (UPDATE-NTH i v (locals (current-frame s)))
                       (instance-class-table s) 
                       (heap s) 
                       (heap-init-map (aux s)) (method-ptr (current-frame s)))
           (bcv::modifylocalvariable 
            i 
            (value-sig v 
                       (instance-class-table s)
                       (heap s) 
                       (heap-init-map (aux s))
                       (method-ptr (current-frame s)))
            (locals-sig (locals (current-frame s))
                        (instance-class-table s)
                        (heap s)
                        (heap-init-map (aux s))
                        (method-ptr (current-frame s))))))
  :hints (("Goal" :in-theory (disable type-size)
           :do-not-induct t)))


;----------------------------------------------------------------------

(defthm not-type-size-implies-type-size-2
  (implies (NOT (EQUAL (TYPE-SIZE type)  1))
           (equal (type-size type) 2))
  :rule-classes :forward-chaining)

(defthm REFp-v-implies-type-size-of-tag
  (implies (REFp v hp)
           (equal (type-size (tag-of v)) 1))
  :rule-classes :forward-chaining)

;----------------------------------------------------------------------



;; (local 
;;  (defthm local-sig-frame-set-locals-update-nth-plus-invalidate-1-local-2
;;    (implies (and (< 0 i)
;;                  (< i (len locals))
;;                  (integerp i)
;;                  (consistent-locals locals cl hp)
;;                  (consistent-value-x v cl hp)
;;                  (equal (bcv::sizeof (value-sig v cl hp hp-init method-ptr)) 1)
;;                  (equal (bcv::sizeof (nth (- i 1)
;;                                           (locals-sig locals cl hp hp-init
;;                                                       method-ptr))) 2))
;;             (equal (locals-sig (UPDATE-NTH i v 
;;                                            (update-nth (- i 1) 
;;                                                        '(topx . topx) locals)) cl hp hp-init method-ptr)
;;                    (update-nth i (value-sig v cl hp hp-init method-ptr)
;;                                (update-nth (- i 1) 'topx
;;                                            (locals-sig locals cl hp hp-init method-ptr)))))
;;    :hints (("Goal" :do-not '(generalize)
;;             :induct (local-sig-induct-locals-i locals cl hp i)))))


(local 
  (defthm local-sig-frame-set-locals-update-nth-is-modifylocalvariable-size-2
    (implies (and (< 0 i)
                  (< i (len locals))
                  (integerp i)
                  (consistent-locals locals cl hp)
                  (consistent-value-x v cl hp)
                  (equal (bcv::sizeof (nth (- i 1)
                                           (locals-sig locals cl hp hp-init
                                                       method-ptr))) 2)
                  (equal (bcv::sizeof (value-sig v cl hp hp-init method-ptr)) 1))
             (equal (locals-sig (UPDATE-NTH i v (update-nth (- i 1) '(topx . topx) locals))
                                cl hp hp-init method-ptr)
                    (bcv::modifylocalvariable i (value-sig v cl hp hp-init method-ptr)
                                              (locals-sig locals cl hp hp-init
                                                          method-ptr))))
    :hints (("Goal" :in-theory (disable locals-sig bcv::modifylocalvariable
                                        consistent-value-x)
             :do-not-induct t))))


(local 
 (defthm type-size-bcv-size-lemma-size-2
   (implies (equal (type-size (tag-of v)) 2)
            (equal (bcv::sizeof (value-sig v cl hp hp-init method-ptr)) 2))
 :hints (("Goal" :in-theory (enable bcv::sizeof type-size value-sig REFp
                                    wff-REFp NULLp)))))




(defthm local-sig-frame-set-locals-update-nth-plus-invalidate-2
  (implies (and (< 0 i)
                (< i (len (locals (current-frame s))))
                (integerp i)
                (consistent-state s)
                (consistent-value-x v (instance-class-table s) (heap s))
                (equal (type-size (tag-of v)) 1)
                (equal (type-size 
                        (tag-of (nth (- i 1) 
                                     (locals (current-frame s))))) 2))
    (equal (locals-sig (UPDATE-NTH i v (update-nth (- i 1) '(topx . topx) 
                                                   (locals (current-frame s))))
                       (instance-class-table s) 
                       (heap s) 
                       (heap-init-map (aux s)) (method-ptr (current-frame s)))
           (bcv::modifylocalvariable 
            i 
            (value-sig v 
                       (instance-class-table s)
                       (heap s) 
                       (heap-init-map (aux s))
                       (method-ptr (current-frame s)))
            (locals-sig (locals (current-frame s))
                        (instance-class-table s)
                        (heap s)
                        (heap-init-map (aux s))
                        (method-ptr (current-frame s))))))
  :hints (("Goal" :in-theory (disable type-size)
           :do-not-induct t)))
