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

;;; bcv::excute-* expands into bcv::TypeTransition which expands into
;;; bcv::make-sig-frame
;;; 
;;; We just chose the make-sig-frame to be the normal form to write our other
;;; rewrite rules!! 

(defthm bcv-make-sig-frame-normalize
   (equal (bcv::make-sig-frame l s f)
          (make-sig-frame l s f))
   :hints (("Goal" :in-theory (enable make-sig-frame bcv::make-sig-frame))))


(defthm bcv-make-sig-frame-accessor
  (and (equal (bcv::frameStack  (make-sig-frame l s f)) s)
       (equal (bcv::frameLocals (make-sig-frame l s f)) l)
       (equal (bcv::frameFlags  (make-sig-frame l s f)) f))
  :hints (("Goal" :in-theory (enable make-sig-frame
                                     bcv::frameFlags bcv::frameLocals
                                     bcv::frameStack))))

;----------------------------------------------------------------------


;;; We are interested in the relation between (frame-sig (djvm::step s)) ...
;;; We will show (bcv::step (frame-sig s ...) ...) 

;;;
;;; The strategy is to rewrite all reference to stack of a sig-frame,
;;; into reference to opstack-sig of a concrete state. 
;;; 
;;; 

(defthm bcv-frame-Stack-frame-sig-is-opstack-sig
  (equal (bcv::frameStack (frame-sig frame cl hp hp-init))
         (opstack-sig (operand-stack frame) cl hp hp-init (method-ptr frame)))
  :hints (("Goal" :in-theory (enable frame-sig))))


(defthm bcv-frame-Locals-frame-sig-is-locals-sig
  (equal (bcv::frameLocals (frame-sig frame cl hp hp-init))
         (locals-sig (locals frame) cl hp hp-init (method-ptr frame)))
  :hints (("Goal" :in-theory (enable frame-sig))))




(defthm bcv-frame-Flags-frame-sig-is-genflags-sig
   (equal (bcv::frameFlags (frame-sig frame cl hp hp-init))
          (gen-frame-flags frame hp-init))
   :hints (("Goal" :in-theory (enable frame-sig))))


;;; Sun Jul 31 12:50:02 2005. fixed. see notes on flags!! 
;;;
;; (defthm bcv-frame-Flags-frame-sig-is-genflags-sig
;;    (equal (bcv::frameFlags (frame-sig frame cl hp hp-init))
;;           (gen-frame-flags (locals-sig (locals frame) cl hp hp-init
;;                                        (method-ptr frame))
;;                            (opstack-sig (operand-stack frame) cl hp hp-init
;;                                         (method-ptr frame))))
;;    :hints (("Goal" :in-theory (enable frame-sig)))

 


;----------------------------------------------------------------------

;;; these should appear in base-consistent-state
;;; and always enabled!! 

(encapsulate () 
  (local (include-book "base-consistent-state-more"))
  (defthm locals-no-change-pushStack
    (equal (locals (current-frame (pushstack v s)))
           (locals (current-frame s))))
  
  (defthm locals-no-change-popStack
    (equal (locals (current-frame (popStack s)))
           (locals (current-frame s))))

  (defthm gen-frame-flags-popStack-no-change
    (equal (gen-frame-flags (current-frame (popStack s)) hp-init)
           (gen-frame-flags (current-frame s) hp-init))))


; If we were using record book. proof of this may be automatic!
;----------------------------------------------------------------------


;----------------------------------------------------------------------

;;;
;;; rewrite typeTransition style state into frame-sig style state
;;;

(defthm make-sig-frame-bcv-push-operandstack-normalize
  (implies (and (equal (bcv::frameLocals (frame-sig frame cl hp hp-init)) locals)
                (equal (bcv::frameFlags (frame-sig frame cl hp hp-init)) flags)
                (equal (bcv::sizeof resulttype) 1)
                (not (equal resulttype 'void))
                (equal (method-ptr frame) method-ptr))
           (equal (MAKE-SIG-FRAME
                   locals
                   (BCV::PUSHOPERANDSTACK RESULTTYPE (opstack-sig
                                                      (operand-stack frame)
                                                      cl hp hp-init method-ptr))
                   flags)
                  (frame-push-value-sig resulttype (frame-sig frame cl hp hp-init))))
  :hints (("Goal" :in-theory (enable bcv::pushoperandstack
                                     frame-push-value-sig))))

;;; how popmatchingtype in BCV::typetransition maps to opstack-sig ....
;;;
;;; note the following is skip-proved (in base-bcv-support. need clean up
;;; there!!)

(encapsulate ()
   (local (include-book "base-bcv-support"))
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
                                     ())))))
  



(defthm car-opstack-sig-normalize
  (Implies (canPopCategory1 (operand-stack (current-frame s)))
           (equal (CAR (OPSTACK-SIG (OPERAND-STACK (CURRENT-FRAME S))
                                    cl hp hp-init method-ptr))
                  (value-sig (topStack s)
                             cl hp hp-init method-ptr)))
  :hints (("Goal" :in-theory (e/d (opstack-sig topStack current-frame 
                                               opstack-sig) (value-sig))
           :cases ((consp (operand-stack (current-frame s)))))
          ("Subgoal 1" :expand (opstack-sig (OPERAND-STACK (CURRENT-FRAME S))
                                            cl hp hp-init method-ptr))))

;;;
;;; reduce (car (opstack-sig ...)) into value-sig of (topStack ..))
;;;

(include-book "base-bcv-fact-nth-opstack-specific-env-sig")

;;; expand nth1operandstackis into a CAR of something. 
;;; together with our rule for isMatchingType-popMatchingType-form1
;;; and car-opstack-sig-normalize
;;;

(include-book "base-bcv-fact-isMatchingType-canPopCategory1")

;;;
;;; necessary for car-opstack-sig-normalize to work!! 
;;;

;;; Next we need to reduce value-sig which is a more complicated concept
;;; that deal with whether an object is initialized or not
;;; whether it is primitive type value. 
;;;
;;; We want to reduce it to the intuitive fix-sig. 
;;; 
;;; Basically, REFp and initialized, we will want to reduce it to fix-sig
;;; 

(encapsulate ()
 (local (include-book "base-bcv-djvm-assignable"))
 (defthm value-sig-being-fix-sig
   (implies (and (REFp v hp)
                 (not (NULLp v))
                 (not (consp (deref2-init v hp-init))))
            (equal (value-sig v cl hp hp-init method-ptr)
                   (fix-sig (obj-type (deref2 v hp)))))))

;;;
;;; this are proved before!! in efforts to expand frame-sig ...
;;; This helps in getting value-sig is not uninitializedThis 
;;; 

(defthm nullp-implies 
  (implies (and (not (nullp v))
                (REFp v hp))
           (not (EQUAL (VALUE-OF v)  -1)))
  :hints (("Goal" :in-theory (enable nullp REFp))))


;;; Note: the decision to only export isMatchingType implies 
;;; (not (consp ...))
;;; etc. 


;; (encapsulate () 
;;  (local (include-book "base-bcv-support"))
;;  ;; The problem we want to avoid all reference to isAssignable
;;  ;; part of strategy!! 
;;  (local 
;;   (defthm isAssignable-to-array-class-java-lang-Object-implies-not-deref2-init-specific
;;    (implies (and (bcv::isAssignable (value-sig (topStack s)
;;                                                (instance-class-table s)
;;                                                (heap s)
;;                                                (heap-init-map (aux s))
;;                                                (method-ptr (current-frame s)))
;;                                     '(array (class "java.lang.Object"))
;;                                     (env-sig s))
;;                  (not (nullp (topStack s)))
;;                  (consistent-value-x (topStack s) (instance-class-table s)
;;                                      (heap s))
;;                  (equal (heap-init-map (aux s)) hp-init))
;;             (not (consp (deref2-init (topStack s) hp-init))))))

;;  (local (include-book "base-bcv-fact-isMatchingType-isAssignable"))
 
;;  (local 
;;   (defthm bcv-isMatchingType-bcv-isAssignable-specific
;;    (implies (and (bcv::isMatchingType typ (opstack-sig 
;;                                            (operand-stack (current-frame s))
;;                                            cl hp hp-init method-ptr) env)
;;                  (canPopCategory1 (operand-stack (current-frame s)))
;;                  (equal (bcv::sizeof typ) 1))
;;             (bcv::isAssignable (value-sig (topStack s)
;;                                           cl hp hp-init method-ptr) typ env))))

;;  (defthm isMatchingType-to-array-class-java-lang-Object-implies-not-deref2-init-specific
;;    (implies (and (bcv::isMatchingType '(array (class "java.lang.Object"))
;;                                       (opstack-sig (operand-stack (current-frame s))
;;                                                    (instance-class-table s)
;;                                                    (heap s)
;;                                                    (heap-init-map (aux s))
;;                                                    (method-ptr (current-frame s)))
;;                                     (env-sig s))
;;                  (not (nullp (topStack s)))
;;                  (consistent-value-x (topStack s) (instance-class-table s)
;;                                      (heap s))
;;                  (equal (heap-init-map (aux s)) hp-init))
;;             (not (consp (deref2-init (topStack s) hp-init))))
;;    :hints (("Goal" :in-theory (disable consistent-value-x)))))

(encapsulate () 
  (local (include-book "base-bcv-fact-isMatchingType-value-initialized"))
  (defthm isMatchingType-to-array-class-java-lang-Object-implies-not-deref2-init-specific
    (implies (and (bcv::isMatchingType '(array (class "java.lang.Object"))
                                       (opstack-sig (operand-stack (current-frame s))
                                                    (instance-class-table s)
                                                    (heap s)
                                                    (heap-init-map (aux s))
                                                    (method-ptr (current-frame s)))
                                       (env-sig s))
                  (not (nullp (topStack s)))
                  (consistent-value-x (topStack s) (instance-class-table s)
                                      (heap s))
                  (equal (heap-init-map (aux s)) hp-init))
             (not (consp (deref2-init (topStack s) hp-init))))
    :hints (("Goal" :in-theory (disable consistent-value-x)))))
  


(in-theory (enable bcv::nth1OperandStackIs))

;; we will rely on rules in 
;;   (include-book "base-bcv-fact-nth-opstack-specific-env-sig")
;; to expand (nth i ...)
;;

(defthm car-operand-stack-current-frame
  (equal (car (operand-stack (current-frame s)))
         (topStack s))
  :hints (("Goal" :in-theory (enable topStack current-frame))))


(defthm element-type-of-fix-sig-is-fix-sig-of-element-type
  (implies (isArrayType type)
           (equal (bcv::arrayelementtype (fix-sig type))
                  (FIX-SIG (array-component-type type))))
  :hints (("Goal" :in-theory (enable fix-sig component-type 
                                     bcv::arrayelementtype
                                     primitive-type? isArrayType
                                     array-component-type))))


(in-theory (disable fix-sig))

(encapsulate ()
    (local (include-book "base-bcv-support"))
              
    (local (defthm isAssignable-to-array-class-java-lang-Object-not-primitive-type
      (implies (and (bcv::isAssignable (value-sig v  (instance-class-table s)
                                                  (heap s)
                                                  (heap-init-map (aux s))
                                                  (method-ptr (current-frame s)))
                                       '(array (class "java.lang.Object"))
                                       (env-sig s))
                    (not (nullp v))
                    (consistent-value-x v (instance-class-table s) (heap s)))
               (not (primitive-type? (array-component-type 
                                      (obj-type (deref2 v (heap s)))))))))

    (local (include-book "base-bcv-fact-isMatchingType-isAssignable"))
    (local (defthm bcv-isMatchingType-bcv-isAssignable-specific
             (implies (and (bcv::isMatchingType typ (opstack-sig 
                                                     (operand-stack (current-frame s))
                                                     cl hp hp-init method-ptr) env)
                           (canPopCategory1 (operand-stack (current-frame s)))
                           (equal (bcv::sizeof typ) 1))
                      (bcv::isAssignable (value-sig (topStack s)
                                                    cl hp hp-init method-ptr) typ env))))

    (defthm isMatchingType-to-array-class-java-lang-Object-not-primitive-type
      (implies (and (bcv::ismatchingtype '(array (class "java.lang.Object"))
                                         (opstack-sig (operand-stack (current-frame s))
                                                      (instance-class-table s)
                                                      (heap s)
                                                      (heap-init-map (aux s))
                                                      (method-ptr (current-frame s)))
                                         (env-sig s))
                    (REFp (topStack s) (heap s))
                    (not (nullp (topStack s)))
                    (equal (heap s) hp)
                    (consistent-value-x (topStack s) (instance-class-table s) (heap s)))
               (not (primitive-type? (array-component-type 
                                      (obj-type (deref2 (topStack s) hp))))))
      :hints (("Goal" :in-theory (disable bcv::isAssignable)))))


(encapsulate () 
   (local (include-book "base-bcv-support"))
   (local (defthm isAssignable-to-AARRAY-implies-array-type
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
                     (isArrayType (obj-type (deref2 v (heap s)))))))

    (local (include-book "base-bcv-fact-isMatchingType-isAssignable"))
    (local (defthm bcv-isMatchingType-bcv-isAssignable-specific
             (implies (and (bcv::isMatchingType typ (opstack-sig 
                                                     (operand-stack (current-frame s))
                                                     cl hp hp-init method-ptr) env)
                           (canPopCategory1 (operand-stack (current-frame s)))
                           (equal (bcv::sizeof typ) 1))
                      (bcv::isAssignable (value-sig (topStack s)
                                                    cl hp hp-init method-ptr) typ env))))

   (defthm isMatchingTypee-to-AARRAY-implies-array-type
     (implies (and (bcv::ismatchingtype '(array (class "java.lang.Object"))
                                        (opstack-sig (operand-stack (current-frame
                                                                     s))
                                                     (instance-class-table s)
                                                     (heap s)
                                                     (heap-init-map (aux s))
                                                     (method-ptr (current-frame s)))
                                        (env-sig s))
                   (not (nullp (topStack s)))
                   (equal (heap s) hp)
                   (consistent-state s)
                   (REFp (topStack s) (heap s)))
              (isArrayType (obj-type (deref2 (topStack s) hp))))))



;; we need isArrayType?? 
;;
;; Because we need element-type-of-fix-sig-is-fix-sig-of-element-type
;; fix-sig (array-component-type ...
;; being the same as 
;;         (array-component-type (fix-sig...))
;;

(defthm fix-sig-is-1-if-not-type
  (implies (not (primitive-type? type))
           (equal (bcv::sizeof (fix-sig type)) 1))
  :hints (("Goal" :in-theory (enable fix-sig bcv::sizeof primitive-type?))))


(defthm fix-sig-never-void
  (not (equal (fix-sig any) 'void))
  :hints (("Goal" :in-theory (enable fix-sig primitive-type?))))


(defthm fix-sig-never-uninitialized
  (not (equal (fix-sig any) 'uninitializedThis))
  :hints (("Goal" :in-theory (enable fix-sig primitive-type?))))




;; (defthm primitive-type-value-sig-reduce
;;   (implies (and (primitive-type? (tag-of v))
;;                 (not (NULLp v)))
;;            (equal (value-sig v cl hp hp-init method-ptr)
;;                   (tag-of v)))
;;   :hints (("Goal" :in-theory (enable value-sig fix-sig REFp wff-REFp))))


;;;
;;; we are almost there!! ;; Sun May 15 23:32:14 2005
;;; 


;; (skip-proofs 
;;  (defthm not-consp-operand-stack-operand-stack-pop-is-nil
;;    (implies (not (consp (operand-stack (current-frame s))))
;;             (equal (operand-stack (current-frame (popStack s))) nil))))



;;; Sun Jul 31 15:33:39 2005
;;; (include-book "base-bcv-fact-isMatchingType-gen-flags")
;;;
;;; not needed!!! Sun Jul 31 15:33:46 2005


(defthm frame-push-value-sig-locals
  (equal (bcv::frameLocals (frame-push-value-sig v frame))
         (bcv::frameLocals frame))
  :hints (("Goal" :in-theory (enable frame-push-value-sig))))


(defthm frame-push-value-sig-flags
  (equal (bcv::frameFlags (frame-push-value-sig v frame))
         (bcv::frameFlags frame))
  :hints (("Goal" :in-theory (enable frame-push-value-sig))))


(in-theory (disable frame-push-value-sig bcv::isMatchingType))


;----------------------------------------------------------------------


;;(i-am-here) ;; Tue May 17 23:33:28 2005

;; (i-am-here) ;; Sun Jul 31 15:38:36 2005

;;; modified the following as a result of the changing gen-frame-flags's
;;; definition!! 

(defthm make-sig-frame-normalize
  (implies (and (equal (locals (current-frame s)) locals)
                (equal (operand-stack (current-frame s)) stk)
                (equal (method-ptr (current-frame s)) method-ptr)
                (equal (gen-frame-flags (current-frame s) hp-init)
                       flags))
           (equal (equal (MAKE-SIG-FRAME
                          (LOCALS-SIG locals  cl hp hp-init method-ptr)
                          (OPSTACK-SIG stk cl hp hp-init method-ptr)
                          flags)
                         (FRAME-SIG (current-frame s)
                                    cl hp hp-init))
                  t))
  :hints (("Goal" :in-theory (disable frame-sig gen-frame-flags)
           :expand       (FRAME-SIG (current-frame s)
                                    cl hp hp-init))))

;; I seem to need this. 
(defthm push-void-no-change
  (equal (BCV::PUSHOPERANDSTACK 'void any) any)
  :hints (("Goal" :in-theory (enable bcv::pushoperandstack))))

;----------------------------------------------------------------------


(in-theory (disable bcv::isAssignable bcv::arg1 arg))


(defthm bcv-arg1-normalize-to-djvm-arg
  (equal (BCV::ARG1 INST)
         (djvm::arg inst))
  :hints (("Goal" :in-theory (enable bcv::arg1 djvm::arg))))


(defthm isAssignable-size-equal-specific-local
  (implies (and (bind-free (acl2::default-bind-free 's 's (acl2::pkg-witness
                                                           "DJVM"))
                           (s))
                (bcv::isAssignable y 'reference (env-sig s)))
           (equal (bcv::sizeof y) 1))
  :hints (("Goal" :in-theory (enable bcv::isAssignable bcv::sizeof))))


;; (defthm not-isAssignable-any-void
;;   (implies (not (equal x 'void))
;;            (not (isAssignable x 'VOID env)))
;;   :hints (("Goal" :expand (isAssignable x 'void env))))

(local 
 (defthm not-isAssignable-void-any
   (implies (not (equal x 'void))
            (not (bcv::isAssignable 'VOID x env)))
   :hints (("Goal" :expand (bcv::isAssignable 'void x env)))))


(defthm isAssignable-reference-not-void
  (implies (and (bind-free (acl2::default-bind-free 's 's (acl2::pkg-witness
                                                           "DJVM"))
                           (s))
                (bcv::isAssignable y 'reference (env-sig s)))
           (not (equal y 'void))))


;; (i-am-here) ;; Wed Jul 27 00:30:08 2005


(local 
 (defthm equal-minus-one-minus-one-plus-negative-two
   (equal (+ -1 -1 i)
          (+ -2 i))))



(local 
 (defthm nth-i-specific-cons
   (implies (and (< 0 i)
                 (integerp i))
            (equal (nth i (cons x locals))
                   (nth (- i 1) locals)))))


(local 
 (defthm nth-i-specific-2-cons
   (implies (and (< 1 i)
                 (integerp i))
            (equal (nth i (list*  x y locals))
                   (nth (- i 2) locals)))
   :hints (("Goal" 
            :in-theory (disable nth-i-specific-cons)
            :use ((:instance nth-i-specific-cons
                             (i (- i 1))
                             (locals (cdr locals)))
                  (:instance nth-i-specific-cons))
            :do-not-induct t))))

(local 
 (defthm valid-local-index-implies-i-positive
   (implies (VALID-LOCAL-INDEX (+ -2 I) any)
            (< 1 i))
   :rule-classes :forward-chaining))



(defthm valid-local-index-implies-nth-i-local-sig-reduce
  (implies (and (valid-local-index i locals)
                (integerp i))
           (equal (nth i (locals-sig locals cl hp hp-init method-ptr))
                  (value-sig (nth i locals) cl hp hp-init method-ptr)))
  :hints (("Goal" :in-theory (disable value-sig)
           :do-not '(generalize))))

;----------------------------------------------------------------------

(defthm bcv-size-of-array-1
  (equal (bcv::sizeof (cons 'array any)) 1)
  :hints (("Goal" :in-theory (enable bcv::sizeof))))


;----------------------------------------------------------------------

;; (i-am-here) ;; Sat Jul 23 17:18:59 2005

(in-theory (disable bcv::passesprotectedfieldcheck))
(in-theory (disable JVM::MEM-BASE-TYPES-IMPLIES-NOT-EQUAL))
(in-theory (disable fieldcp-classname
                    fieldcp-fieldname
                    fieldcp-fieldtype
                    field-classname
                    BCV::FIELDCLASSNAMECP
                    bcv::fieldnamecp
                    bcv::fieldtypecp
                    bcv::translate-type
                    arg))




(defthm bcv-size-of-prefix-class-is-1
  (equal (BCV::SIZEOF (bcv::prefix-class any)) 1)
  :hints (("Goal" :in-theory (enable bcv::prefix-class bcv::sizeof))))



(defthm equal-size-translate-type
  (equal (BCV::SIZEOF (BCV::TRANSLATE-TYPE type))
         (bcv::sizeof type))
  :hints (("Goal" :in-theory (enable bcv::sizeof bcv::translate-type))))


(defthm equal-size-djvm-translate-type
  (equal (BCV::SIZEOF (djvm-translate-int-type type))
         (bcv::sizeof type))
  :hints (("Goal" :in-theory (enable bcv::sizeof djvm-translate-int-type))))

(defthm translate-type-not-void
  (implies (not (equal type 'void))
           (NOT (EQUAL (BCV::TRANSLATE-TYPE type) 'VOID)))
  :hints (("Goal" :in-theory (enable bcv::translate-type))))


(defthm wff-type-rep-implies-not-void-type
  (implies (WFF-FIELDCP fieldcp)
           (not (equal (bcv::fieldtypecp fieldcp) 'void)))
  :hints (("Goal" :in-theory (enable wff-fieldcp bcv::fieldtypecp))))

;----------------------------------------------------------------------

;;; some thing like this.
;;; 
;;; 

(defthm bcv-translate-type-reduce-to-djvm-translate
  (equal (djvm-translate-int-type type)
         (bcv::translate-type type))
  :hints (("Goal" :in-theory (enable bcv::translate-type djvm-translate-int-type))))


(defthm type-size-fieldcp-type-implies-bcv-sizeof-1
  (implies (and (equal (type-size (fieldcp-fieldtype fieldcp)) 1)
                (wff-fieldcp fieldcp))
           (equal (bcv::sizeof (bcv::fieldtypecp fieldcp)) 1))
  :hints (("Goal" :in-theory (enable type-size bcv::sizeof fieldcp-fieldtype
                                     wff-fieldcp bcv::fieldtypecp
                                     normalize-type-rep))))



(defthm type-size-fieldcp-type-implies-bcv-sizeof-2
  (implies (and (equal (type-size (fieldcp-fieldtype fieldcp)) 2)
                (wff-fieldcp fieldcp))
           (equal (bcv::sizeof (bcv::fieldtypecp fieldcp)) 2))
  :hints (("Goal" :in-theory (enable type-size bcv::sizeof fieldcp-fieldtype
                                     wff-fieldcp wff-type-rep
                                     bcv::fieldtypecp 
                                     normalize-type-rep)
           :expand (WFF-TYPE-REP (NTH 3 FIELDCP)))))


;----------------------------------------------------------------------

; the following is a bit not trivial

(encapsulate () 
    (local (include-book "base-bcv-fact-isMatchingType-value-initialized"))
    (defthm isMatchingType-to-class-type-implies-not-deref2-init-specific
    (implies (and (bcv::isMatchingType (bcv::prefix-class any)
                                       (opstack-sig (operand-stack (current-frame s))
                                                    (instance-class-table s)
                                                    (heap s)
                                                    (heap-init-map (aux s))
                                                    (method-ptr (current-frame
                                                                 s)))
                                       (env-sig s))
                  (not (nullp (topStack s)))
                  (consistent-value-x (topStack s) (instance-class-table s)
                                      (heap s))
                  (equal (heap-init-map (aux s)) hp-init))
             (not (consp (deref2-init (topStack s) hp-init))))
    :hints (("Goal" :in-theory (disable consistent-value-x)))))
  
;----------------------------------------------------------------------

(defthm make-sig-frame-bcv-push-operandstack-normalize-size-2
  (implies (and (equal (bcv::frameLocals (frame-sig frame cl hp hp-init)) locals)
                (equal (bcv::frameFlags (frame-sig frame cl hp hp-init)) flags)
                (equal (bcv::sizeof resulttype) 2)
                (equal (method-ptr frame) method-ptr))
           (equal (MAKE-SIG-FRAME
                   locals
                   (BCV::PUSHOPERANDSTACK RESULTTYPE (opstack-sig
                                                      (operand-stack frame)
                                                      cl hp hp-init method-ptr))
                   flags)
                  (MAKE-SIG-FRAME 
                   locals
                   (cons 'topx (cons resulttype (opstack-sig
                                                      (operand-stack frame)
                                                      cl hp hp-init method-ptr)))
                   flags)))
  :hints (("Goal" :in-theory (enable bcv::pushoperandstack
                                     frame-push-value-sig))))



;----------------------------------------------------------------------

(in-theory (disable gen-frame-flags frame-aux))

;----------------------------------------------------------------------


;; (i-am-here) ;; Sun Jul 31 17:15:11 2005

(defthm consp-opstack-implies-consp-opstack-sig
  (implies (and (consistent-opstack stack cl hp)
                (consp stack))
           (consp (opstack-sig stack cl hp hp-init method-ptr))))


