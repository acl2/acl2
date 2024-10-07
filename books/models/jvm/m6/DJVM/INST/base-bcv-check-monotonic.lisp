(in-package "BCV")
(include-book "../../BCV/typechecker")
(include-book "../../BCV/bcv-functions")

(include-book "base-bind-free")

;;; Mon May  9 01:51:42 2005
;;; Redo using the "structure" development method!! 
;;;


(in-theory (disable bcv::good-icl 
                    bcv::consistent-sig-stack 
                    bcv::consistent-sig-type
                    bcv::arrayelementtype
                    BCV::FRAMEFLAGS
                    BCV::FRAMELOCALS 
                    BCV::FRAMESTACK
                    bcv::good-bcv-type
                    BCV::sizeof
                    bcv::isMatchingType
                    bcv::good-icl
                    bcv::popMatchingType
                    bcv::consistent-sig-type
                    BCV::NTH1OPERANDSTACKIS
                    BCV::MAXSTACKENVIRONMENT
                    bcv::good-java-type
                    bcv::classtableEnvironment
                    bcv::icl-scl-compatible
                    bcv::prefix-class))


;;;
;;; these are proved in base-bcv-check-monotonic.trash.lisp
;;; 

(acl2::set-verify-guards-eagerness 0)

(defthm popMatchingType-preserve-TypeListAssignable
  (implies (bcv::TypeListAssignable l1 l2 env)
           (bcv::TypeListAssignable (bcv::popMatchingType any l1)
                                    (bcv::popMatchingType any l2) env))
  :hints (("Goal" :in-theory (enable bcv::popMatchingType))))


(encapsulate ()
   (local (include-book "base-bcv-check-monotonic-support"))
   (defthm consistent-sig-stack-perserved-specific
     (implies (and (bind-free (acl2::default-bind-free 
                               'env 'env1 (acl2::pkg-witness "DJVM")) (env))
                   (isMatchingType any l env)
                   (not (equal any 'topx))
                   (consistent-sig-stack l icl))
              (consistent-sig-stack (popMatchingType any l) icl))))


(defthm good-icl-fact-1
  (implies (bcv::good-icl icl)
           (djvm::class-exists? "java.lang.Object" icl))
  :hints (("Goal" :in-theory (enable bcv::good-icl))))


(include-book "base-bcv-fact-isMatchingType-consp-stk")


(encapsulate ()
   (local (include-book "base-bcv-check-monotonic-support"))
   (defthm TypeListAssignable-isMatchType
     (implies (and (bind-free (replace-occurance-binding 'sFrame 'gframe sL 'gl)
                              (gl))
                   (bind-free (acl2::default-bind-free 'icl 'icl
                                                       (acl2::pkg-witness
                                                        "DJVM")) (icl))
                   (TypeListAssignable sL gL env)
                   (equal (sizeof any) 1)
                   (consistent-sig-stack sl icl)
                   (consistent-sig-stack gl icl)
                   (good-bcv-type any icl)
                   (good-icl icl)
                   (good-scl (classtableEnvironment env))
                   (icl-scl-compatible icl (classtableEnvironment env))
                   (consp gL)
                   (isMatchingType any gL env))
              (isMatchingType any sL env))))

   


(defthm consistent-sig-type-implies-good-bcv-type
  (implies (bcv::consistent-sig-type typ icl)
           (bcv::good-bcv-type typ icl))
  :hints (("Goal" :in-theory (enable bcv::consistent-sig-type))))



(defthm consistent-sig-type-fact-1
  (consistent-sig-type 'INT icl)
  :hints (("Goal" :in-theory (enable consistent-sig-type good-bcv-type good-java-type))))


(defthm consistent-sig-type-fact-2
  (implies (bcv::good-icl icl)
           (bcv::consistent-sig-type '(array (class "java.lang.Object"))  icl))
  :hints (("Goal" :in-theory (enable bcv::consistent-sig-type 
                                     bcv::good-bcv-type
                                     bcv::good-icl bcv::good-java-type))))

;; Tue May 17 16:35:36 2005

(defthm consistent-sig-type-fact-3
  (implies (bcv::good-icl icl)
           (bcv::consistent-sig-type '(class "java.lang.Object")  icl))
  :hints (("Goal" :in-theory (enable bcv::consistent-sig-type 
                                     bcv::good-bcv-type
                                     bcv::good-icl bcv::good-java-type))))


;; Tue May 17 16:35:41 2005

(defthm consistent-sig-type-fact-2-f
  (implies (good-icl icl)
           (consistent-sig-type '(array (class "java.lang.Object"))  icl)))




(defthm popMatchingType-size-1-implies-len-decrease
  (implies (and (equal (sizeof type) 1)
                (bind-free (acl2::default-bind-free 'env 'env1
                                                    (acl2::pkg-witness "DJVM")) (env))
                (isMatchingType type stk env)
                (consp stk)
                type)
           (equal (len (popMatchingType type stk))
                  (- (len stk) 1)))
  :hints (("Goal" :in-theory (enable popMatchingType))))


(in-theory (enable nth1OperandStackIs))

(include-book "base-bcv-fact-nth-opstack")
(include-book "base-bcv-fact-isMatchingType-array")



(in-theory (disable JVM::MEM-BASE-TYPES-IMPLIES-NOT-EQUAL))

;----------------------------------------------------------------------
;
; So far it knows how to expand opstack when ACL2 sees a CanPop1 
;
; For ALOAD to work. We need some extra rules
;
(in-theory (disable bcv::isAssignable bcv::arg1))

; just for nice looking 

; We do not want the following rule
; We always want to combine this rule with bcv::isAssignable is transitive fact
; 


;(i-am-here) ;; Sun May 22 19:08:00 2005

(defthm TypeListAssignable-implies-len-equal
  (implies (and (bind-free (acl2::default-bind-free
                            'env 'env1 (acl2::pkg-witness "DJVM"))
                           (env))
                (bcv::TypeListAssignable l1 l2 env))
           (equal (len l1) 
                  (len l2)))
  :hints (("Goal" :in-theory (disable isAssignable)))
  :rule-classes :linear)




(local 
 (defthm isAssignable-fact-nil-nil-local
   (bcv::isAssignable nil nil env)
   :hints (("Goal" :in-theory (enable bcv::isAssignable)))))

(local 
 (defthm TypeListAssignable-implies-element-assignable
   (implies (bcv::TypeListAssignable l1 l2 env)
            (bcv::isAssignable (nth i l1) (nth i l2) env))
   :hints (("Goal" :in-theory (disable isAssignable)))))

(local 
 (encapsulate ()
   (local (include-book "../../BCV/bcv-isAssignable-transitive"))
   (defthm isAssignable-Transitive
     (implies (and (good-bcv-type t1 icl)
                   (good-bcv-type t2 icl)
                   (good-bcv-type t3 icl)
                   (equal (classtableEnvironment env) scl)
                   (good-icl icl)
                   (good-scl scl)
                   (icl-scl-compatible icl scl)
                   (isAssignable t1 t2 env)
                   (isAssignable t2 t3 env))
              (isAssignable t1 t3 env)))))


(local 
 (defthm consistent-sig-type-topx
   (consistent-sig-type 'topx icl)
   :hints (("Goal" :in-theory (enable consistent-sig-type good-bcv-type)))))


(local 
 (defthm consistent-sig-locals-and-mem-implies-consistent-sig-type
   (implies (and (consistent-sig-locals locals icl)
                 (mem x locals))
            (consistent-sig-type x icl))))


(local 
 (defthm nth-i-being-mem
   (implies (and (<= 0 i) 
                 (< i (len l)))
            (mem (nth i l) l))))
(local 
 (defthm consistent-sig-locals-implies-nth-i-consistent-sig-type
   (implies (and (consistent-sig-locals locals icl)
                 (<= 0 i)
                 (< i (len locals)))
            (consistent-sig-type (nth i locals) icl))))


(local 
 (defthm consistent-sig-type-good-bcv-type
   (implies (consistent-sig-type type icl)
            (good-bcv-type type icl))))

(defthm reference-good-bcv-type
  (BCV::GOOD-BCV-TYPE 'REFERENCE ICL)
  :hints (("Goal" :in-theory (enable bcv::good-bcv-type))))

;(i-am-here)


(local 
 (defthm TypeListAssignable-implies-len-equal-f
   (implies (bcv::TypeListAssignable l1 l2 env)
            (equal (len l1) 
                   (len l2)))
   :hints (("Goal" :in-theory (disable isAssignable)))
   :rule-classes :forward-chaining))
 

; Matt K. mod: Avoid raw Lisp error in tau; see similar disable in
; BCV/bcv-isAssignable-transitive.lisp.
(local (in-theory (disable (:e tau-system))))

(defthm TypeListAssignable-isAssignable-local-assignable
  (implies (and (bind-free (replace-occurance-binding 'sFrame 'gframe sL 'gl)
                           (gl))
                (bind-free (acl2::default-bind-free 'icl 'icl
                                                    (acl2::pkg-witness
                                                     "DJVM")) (icl))

                (TypeListAssignable sL gL env)          
                (consistent-sig-locals gl icl)
                (consistent-sig-locals sl icl)
                (<= 0 i)
                (< i (len gl))
                ;;(< i (len sl))
                (good-bcv-type type icl)
                (good-icl icl)
                (good-scl (classtableEnvironment env))
                (icl-scl-compatible icl (bcv::classtableEnvironment env))
                (isAssignable (nth i gl) type env))
           (isAssignable (nth i sl) type env))
  :hints (("Goal" :do-not '(generalize)
           :do-not-induct t
           :use ((:instance isAssignable-Transitive
                            (t1 (nth i sl))
                            (t2 (nth i gl))
                            (t3 type)
                            (scl (bcv::classtableEnvironment env)))))))


;; (i-am-here) ;; Sun May 22 23:50:04 2005


(local 
 (defthm consistent-sig-type-not-void
   (not (consistent-sig-type 'void icl))
   :hints (("Goal" :in-theory (enable consistent-sig-type)))))
 

(local (defthm nth-out-of-bound-nil
         (implies (and (<= (len locals) i)
                       (integerp i))
                  (equal (nth i locals) nil))))

(local 
 (defthm if-consistent-sig-type-implies-not-void
   (implies (consistent-sig-type (nth i locals) icl)
            (not (equal (nth i locals) 'void)))))

(local (in-theory (disable CONSISTENT-SIG-TYPE-NOT-VOID)))

(defthm consistent-sig-locals-implies-not-void
  (implies (and (acl2::bind-free (acl2::default-bind-free 'env 'env1
                                                          (acl2::pkg-witness
                                                           "DJVM")) 
                                 (env))
                (bind-free (acl2::default-bind-free 'icl 'icl
                                                     (acl2::pkg-witness
                                                      "DJVM")) (icl))
                 (good-icl icl)
                 (integerp i)
                 (<= 0 i)
                 (icl-scl-compatible icl (bcv::classtableEnvironment env))
                 (consistent-sig-locals locals icl))
           (not (equal (nth i locals) 'void)))
  :hints (("Goal" :cases ((and (<= 0 i)
                               (< i (len locals))))
           :restrict ((if-consistent-sig-type-implies-not-void
                       ((icl icl))))
           :do-not-induct t)))


(defthm isAssignable-size-equal-specific
  (implies (and (acl2::bind-free (acl2::default-bind-free 'env 'env1
                                                          (acl2::pkg-witness
                                                           "DJVM")) 
                                 (env))
                (bcv::isAssignable y 'reference env))
           (equal (bcv::sizeof y) 1))
  :hints (("Goal" :in-theory (enable bcv::isAssignable bcv::sizeof))))

;----------------------------------------------------------------------

  
(defthm bcv-size-of-prefix-class
  (EQUAL (BCV::SIZEOF (BCV::PREFIX-CLASS any)) 1)
  :hints (("Goal" :in-theory (enable bcv::sizeof bcv::prefix-class))))

;; (encapsulate ()
;;    (local (include-book "base-bcv-check-monotonic-support"))
;;    (defthm TypeListAssignable-isMatchType
;;      (implies (and (bind-free (replace-occurance-binding 'sFrame 'gframe sL 'gl)
;;                               (gl))
;;                    (bind-free (acl2::default-bind-free 'icl 'icl
;;                                                        (acl2::pkg-witness
;;                                                         "DJVM")) (icl))
;;                    (TypeListAssignable sL gL env)
;;                    (equal (sizeof any) 1)
;;                    (consistent-sig-stack sl icl)
;;                    (consistent-sig-stack gl icl)
;;                    (good-bcv-type any icl) 
;;                    (good-icl icl)
;;                    (icl-scl-compatible icl (classtableEnvironment env))
;;                    (consp gL)
;;                    (isMatchingType any gL env))
;;               (isMatchingType any sL env))))


(defthm TypeListAssignable-isMatchType-prefix-class
  (implies (and (bind-free (replace-occurance-binding 'sFrame 'gframe sL 'gl)
                           (gl))
                 (bind-free (acl2::default-bind-free 'icl 'icl
                                                     (acl2::pkg-witness
                                                      "DJVM")) (icl))
                 (consistent-sig-stack sl icl)
                 (TypeListAssignable sL gL env)
                 (consistent-sig-stack gl icl)
                 (good-bcv-type (prefix-class any) icl) ;; why we need this?? 
                 ;; Fri Jul 15 11:30:49 2005
                 ;; Because we didn't assert very strong constraints on 
                 ;; "scl" (classtableEnvironment env)
                 ;; We rely on (icl-scl-compatible icl (classtableEnvironment
                 ;; env))
                 ;; to add some contraints 
                 (good-icl icl)                         ;; 
                 (good-scl (classtableEnvironment env))
                 (icl-scl-compatible icl (classtableEnvironment env))
                 (consp gL)
                 (isMatchingType (prefix-class any) gL env))
           (isMatchingType (prefix-class any) sL env))
  :hints (("Goal" :use ((:instance TypeListAssignable-isMatchType
                                   (any (prefix-class any)))))))


;; (defthm popMatchingType-size-1-implies-len-decrease
;;   (implies (and (equal (sizeof type) 1)
;;                 (bind-free (acl2::default-bind-free 'env 'env1
;;                                                     (acl2::pkg-witness "DJVM")) (env))
;;                 (isMatchingType type stk env)
;;                 (consp stk)
;;                 type)
;;            (equal (len (popMatchingType type stk))
;;                   (- (len stk) 1)))
;;   :hints (("Goal" :in-theory (enable popMatchingType))))


(defthm len-pushOperandStack
  (equal (len (BCV::PUSHOPERANDSTACK any stack))
         (if (equal any 'void)
             (len stack)
           (+ (bcv::sizeof any)
              (len stack))))
  :hints (("Goal" :in-theory (enable bcv::sizeof))))
             
;----------------------------------------------------------------------


(in-theory (disable bcv::fieldclassnamecp bcv::fieldtypecp 
                    BCV::ISPROTECTEDFIELD
                    bcv::translate-type
                    bcv::passesprotectedfieldcheck
                    BCV::COLLECT-SUPERCLASS-LIST))

;;(i-am-here)


(encapsulate ()
 (local (include-book "base-bcv-protected-check-monotonic"))
 (defthm passesprotectedfieldcheck-general-then-pass-in-specific
  (implies (and (bind-free (replace-occurance-binding 'sFrame 'gframe s 'g)
                            (g))
                (bind-free (acl2::default-bind-free 'icl 'icl
                                                    (acl2::pkg-witness
                                                     "DJVM")) (icl))
                (BCV::PASSESPROTECTEDFIELDCHECK
                 ENV1
                 fieldclassname
                 fieldname
                 fieldtype
                 g)
                (bcv::isassignable s g env1)
                (bcv::good-bcv-type g icl)
                (bcv::good-bcv-type s icl)
                (bcv::good-bcv-type (bcv::prefix-class
                                     (bcv::classClassname 
                                      (bcv::classenvironment env1)))
                                    icl)
                (bcv::good-icl icl)
                (bcv::good-scl (CLASSTABLEENVIRONMENT ENV1))
                (bcv::icl-scl-compatible icl (bcv::classtableEnvironment env1)))
           (BCV::PASSESPROTECTEDFIELDCHECK
            ENV1
            fieldclassname
            fieldname
            fieldtype
            s))))

;----------------------------------------------------------------------



(local (in-theory (disable bcv::good-scl)))

(defthm bcv-good-java-type-implies-good-bcv-type
  (implies (bcv::good-java-type typ icl)
           (bcv::good-bcv-type typ icl))
  :hints (("Goal" :in-theory (enable bcv::good-bcv-type))))

;; (defthm not-void-type
;;   (not (equal (BCV::TRANSLATE-TYPE (BCV::FIELDTYPECP (BCV::ARG1 INST)))
;;               'VOID)))


(defthm typelistassignable-isAssignable
  (implies (and (bcv::typelistassignable sl gl env1)
                (consp gl))
           (bcv::isassignable (car sl) 
                              (car gl) env1)))


(defthm consistent-sig-stack-implies
  (implies (and (bcv::consistent-sig-stack stack icl)
                (consp stack))
           (BCV::GOOD-BCV-TYPE (CAR stack) ICL))
  :hints (("Goal" :in-theory (enable bcv::consistent-sig-stack
                                     bcv::good-bcv-type
                                     bcv::consistent-sig-type))))


(defthm typelistassignable-consp-consp
  (implies (and (bcv::typelistassignable sl gl env1)
                (consp gl))
           (consp sl))
  :rule-classes :forward-chaining)


;----------------------------------------------------------------------

;;(i-am-here) ;; Thu Jul 28 00:39:32 2005

(local 
 (defun good-bcv-type-list (l icl)
   (if (endp l) t
     (and (good-bcv-type (car l) icl)
          (good-bcv-type-list (cdr l) icl)))))
   

;; (local 
;;  (encapsulate ()
;;    (local (include-book "../../BCV/bcv-isAssignable-transitive"))
;;    (defthm isAssignable-Transitive
;;      (implies (and (good-bcv-type t1 icl)
;;                    (good-bcv-type t2 icl)
;;                    (good-bcv-type t3 icl)
;;                    (equal (classtableEnvironment env) scl)
;;                    (good-icl icl)
;;                    (good-scl scl)
;;                    (icl-scl-compatible icl scl)
;;                    (isAssignable t1 t2 env)
;;                    (isAssignable t2 t3 env))
;;               (isAssignable t1 t3 env)))))


(local 
 (defthm TypelistAssignable-is-Transitive
   (implies (and (bcv::typelistassignable sl gl env1)
                 (bcv::typelistassignable gl ggl env1)
                 (good-bcv-type-list sl icl)
                 (good-bcv-type-list gl icl)
                 (good-bcv-type-list ggl icl)
                 (equal (classtableEnvironment env1) scl)
                 (good-icl icl)
                 (good-scl scl)
                 (icl-scl-compatible icl scl))
           (bcv::typelistassignable sl ggl env1))
  :hints (("Goal" :in-theory (e/d () (bcv::isassignable))
           :do-not  '(generalize))
          ("Subgoal *1/9"
           :use ((:instance isassignable-transitive
                            (t1 (car sl))
                            (t2 (car gl))
                            (t3 (car ggl))
                            (env env1)
                            (scl (classtableEnvironment env1))))))))

;;(i-am-here) ;; Thu Jul 28 02:54:22 2005

(local 
 (defthm consistent-sig-stack-implies-good-bcv-type-list
   (implies (bcv::consistent-sig-stack stack icl)
            (bcv::good-bcv-type-list stack icl))
   :hints (("Goal" :in-theory (enable bcv::consistent-sig-stack 
                                      bcv::consistent-sig-type)))
   :rule-classes :forward-chaining))



(local 
 (defthm consistent-sig-locals-implies-good-bcv-type-list
   (implies (consistent-sig-locals locals icl)
            (good-bcv-type-list locals icl))
   :hints (("Goal" :in-theory (enable consistent-sig-locals 
                                      consistent-sig-type)))
   :rule-classes :forward-chaining))



(defthm targetissafe-moregeneral-implies-more-specific
  (implies (and (bind-free (acl2::replace-occurance-binding 'djvm::sframe
                                                            'djvm::gframe 
                                                            sframe
                                                            'bcv::gframe)
                           (gframe))
                (bind-free (acl2::default-bind-free 'icl 'icl
                                                    (acl2::pkg-witness
                                                     "DJVM")))
                (bcv::targetistypesafe env1 gframe offset)
                ;;(equal (classtableEnvironment env1) scl)
                (icl-scl-compatible icl (classtableEnvironment env1))
                (good-icl icl)
                (good-scl (classtableEnvironment env1))
                (consistent-sig-stack (frameStack gframe) icl)
                (consistent-sig-stack (frameStack sframe) icl)
                (consistent-sig-stack (frameStack 
                                       (STACKFRAMEATOFFSET env1 offset)) icl)
                (consistent-sig-locals (frameLocals gframe) icl)
                (consistent-sig-locals (frameLocals sframe) icl)
                (consistent-sig-locals (frameLocals 
                                        (STACKFRAMEATOFFSET env1 offset)) icl)

                (bcv::sig-frame-more-general gframe sframe env1))
           (bcv::targetistypesafe env1 sframe offset))
   :hints (("Goal" :in-theory (disable bcv::getmap bcv::makeStackMap
                                       bcv::mapoffset
                                       TypelistAssignable-is-Transitive
                                       bcv::allinstructions
                                       bcv::isstackmapframe)
            :use ((:instance 
                   TypelistAssignable-is-Transitive
                   (sl (frameLocals sframe))
                   (gl (frameLocals gframe))
                   (ggl (frameLocals 
                         (STACKFRAMEATOFFSET env1 offset)))
                   (scl (classtableEnvironment env1)))
                  (:instance 
                   TypelistAssignable-is-Transitive
                   (sl (frameStack sframe))
                   (gl (frameStack gframe))
                   (ggl (frameStack 
                         (STACKFRAMEATOFFSET env1 offset)))
                   (scl (classtableEnvironment env1)))))))
                   

;----------------------------------------------------------------------

;;                 (equal (classtableEnvironment env1) scl)
;;                 (good-scl scl)
;;                 (icl-scl-compatible icl scl)
;;                 (good-icl icl)
;;                 (consistent-sig-stack sl icl)
;;                 (consistent-sig-stack gl icl))

(local 
 (defthm isassignable-INT-implies-int
   (implies (ISASSIGNABLE SL1 'INT ENV1)
            (equal SL1 'INT))
   :hints (("Goal" :in-theory (enable isassignable)))
   :rule-classes :forward-chaining))
            

(defthm isMatchingType-INT-general-more-specific
  (implies (and (bind-free (acl2::replace-occurance-binding 'djvm::sframe
                                                            'djvm::gframe 
                                                            sl
                                                            'bcv::gl) (gl))
                (bcv::ismatchingtype 'INT gl env1)
                (bcv::typelistassignable sl gl env1))
           (bcv::ismatchingtype 'INT sl env1))
  :hints (("Goal" :in-theory (enable bcv::ismatchingtype))))


;----------------------------------------------------------------------

(in-theory (disable bcv::targetistypesafe 
                    BCV::TYPELISTASSIGNABLE
                    bcv::make-sig-frame
                    bcv::good-icl
                    bcv::good-scl
                    bcv::allinstructions
                    bcv::stackframeatoffset
                    bcv::popmatchingtype
                    bcv::icl-scl-compatible
                    bcv::classtableEnvironment
                    bcv::popmatchingtype))

;;
;; these disable may be a problem!! 
;; 
