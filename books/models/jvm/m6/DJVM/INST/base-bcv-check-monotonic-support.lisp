(in-package "BCV")
(include-book "../../BCV/typechecker")

;; Sun Apr 24 11:06:00 2005. copied from
;; ../../BCV/bcv-check-general-implies-bcv-check-specific.lisp
;;

(include-book "../../BCV/bcv-functions")


(acl2::set-match-free-default :all)
(acl2::set-verify-guards-eagerness 0)

(defun sig-frame-more-general (gframe sframe env)
  (FrameIsAssignable sframe gframe env))


(defthm frame-accessor 
  (and (equal (frameLocals (make-sig-frame l s f)) l)
       (equal (frameStack  (make-sig-frame l s f)) s)
       (equal (frameFlags  (make-sig-frame l s f)) f)))

(in-theory (disable make-sig-frame frameFlags frameStack frameLocals))


(defthm TypeListAssignable-implies-len-equal
  (implies (TypeListAssignable l1 l2 cl)
           (equal (equal (len l1) (len l2)) t)))

;; byte, int, short values on the stack and local are int
(include-book "base")
(include-book "base-consistent-state")

;;
;; (defun good-java-type (typ icl)
;;   (declare (xargs :hints (("Goal" :in-theory (enable isArrayType)))))
;;   (or (JVM::PRIMITIVE-TYPE? typ)
;;       (and (isclasstype typ)
;;            (JVM::CLASS-EXISTS? (name-of typ) icl))
;;       (and (isArrayType typ)
;;            (not (equal (component-type typ) 'NULL))
;;            (good-java-type (component-type typ) icl))))
;;

;; (defun wff-icl (icl)
;;   (if (not (consp icl)) t
;;     (and (stringp (jvm::classname (car icl)))
;;          (wff-icl (cdr icl)))))

;; (defun good-icl (icl)
;;   (and (wff-icl icl)
;;        (djvm::class-exists? "java.lang.Object" icl)
;;        (djvm::consistent-class-hierachy icl)))

;; these are defined in bcv-functions.lisp

(include-book "../../BCV/bcv-isAssignable-transitive")

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
           (isAssignable t1 t3 env)))



;; (defun consistent-sig-type (type icl)
;;   (and (not (equal type 'TWOWORD))
;;        (not (equal type 'ONEWORD))
;;        (not (equal type 'VOID))
;;        ;; (not (equal type 'uninitialized))
;;        ;; (not (equal type 'reference))
;;        (good-bcv-type type icl)))

;; it is possible to have type TOP

;; (defun consistent-sig-stack (stack icl)
;;   ;; make sure two word values are always represented correctly 
;;   ;; occupy two slots and top element is in proper place.
;;   ;;
;;   ;; If we don't care the possibility of this kind of inconsistency, we could
;;   ;; change each instruction when pop a long, it pops a "top" "long" in
;;   ;; sequence.
;;   ;; 
;;   ;; Thu Jan 15 21:15:12 2004: if size 2, then 
;;   ;;   pushLong 
;;   ;;  
;;   ;; this make it diff

;;   (if (endp stack) t
;;     (if (endp (cdr stack)) 
;;         (and (equal (sizeof (car stack)) 1)
;;              (consistent-sig-type (car stack) icl)
;;              (consistent-sig-stack (cdr stack) icl))
;;       (if (equal (sizeof (cadr stack)) 2)
;;           (and (consistent-sig-type (cadr stack) icl)
;;                (equal (car stack) 'topx)
;;                (consistent-sig-stack (cddr stack) icl))
;;         (and (equal (sizeof (car stack)) 1)
;;              (consistent-sig-type (car stack) icl)
;;              (consistent-sig-stack (cdr stack) icl))))))


;;; need to define a consistent-sig-locals!! Tue Feb  1 15:43:22 2005          

(defthm not-isAssignable-any-void
  (implies (not (equal x 'void))
           (not (isAssignable x 'VOID env)))
  :hints (("Goal" :expand (isAssignable x 'void env))))

(defthm not-isAssignable-void-any
  (implies (not (equal x 'void))
           (not (isAssignable 'VOID x env)))
  :hints (("Goal" :expand (isAssignable 'void x env))))

(defthm isassignable-reference-top
  (ISASSIGNABLE 'reference 'topx ENV)
  :hints (("Goal" :expand (isAssignable 'reference 'topx env))))

(defthm isAssignable-uninitialized-top
  (ISASSIGNABLE 'UNINITIALIZED 'topx ENV)
  :hints (("Goal" :expand (isAssignable 'uninitialized 'topx env))))



;; (defstub consistent-env (*) => * )

;; (skip-proofs 
;;  (defthm consistent-env-class-by-name-nil-is-nil
;;    (implies (consistent-env env)
;;             (not (class-by-name nil (nth 6 env))))))


;; (skip-proofs 
;;  (defthm consistent-env-not-isJavaSubclass
;;    (implies (consistent-env env)
;;             (not (isjavasubclassof any nil (nth 6 env))))))

;; ;;
;; ;; a similar form is proved in consistent-class-table
;; ;; however this is on consistent-external-class-table!! 



;; Thu Mar 18 20:05:48 2004
;;

(local (in-theory (disable good-bcv-type 
                           good-icl
                           icl-scl-compatible)))

(defthm good-bcv-type-good-bcv-type
  (implies (good-bcv-type st icl)
           (GOOD-BCV-TYPE (CONVERTIFINT ST) ICL))
  :hints (("Goal" :in-theory (enable good-bcv-type good-java-type))))


; Matt K. mod: Avoid raw Lisp error in tau; see similar disable in
; BCV/bcv-isAssignable-transitive.lisp.
(local (in-theory (disable (:e tau-system))))

(defthm isMatchingType-general-specific-size-1
  (implies (and 
            (good-bcv-type sT icl)
            (good-bcv-type gT icl)
            (good-bcv-type any icl)
            (good-icl icl)
            (good-scl (classtableenvironment env))
            (icl-scl-compatible icl (classtableEnvironment env))
            (isAssignable sT gT env)
            (equal (sizeof any) 1)
            (isMatchingType any (cons gT anyStack1) env))
           (isMatchingType any (cons sT anyStack2) env))
  :hints (("Goal" :in-theory (disable convertIfInt
                                      isassignable-transitive)
           :do-not-induct t
           :use ((:instance isassignable-transitive
                            (t1 st)
                            (t2 gt)
                            (t3 any)
                            (scl (classtableEnvironment env)))))))


;;(i-am-here) ;; Fri Jul 15 11:02:34 2005

(defthm isArrayType-not-assignable-to-TWOWORD
  (implies (ISARRAYTYPE GT)
           (not (ISASSIGNABLE GT 'TWOWORD ENV))))

(defthm isClassType-not-assignable-to-TWOWORD
  (implies (ISCLASSTYPE GT)
           (not (ISASSIGNABLE GT 'TWOWORD ENV))))


(defthm not-isassignable-reference-TWOWORD
  (not (isassignable 'REFERENCE 'TWOWORD env))
  :hints (("Goal" :expand (isassignable 'REFERENCE 'TWOWORD env))))

;; (defthm isArrayType-not-assignable-to-TWOWORD
;;   (implies (ISARRAYTYPE GT)
;;            (not (ISASSIGNABLE GT 'TWOWORD ENV))))


;; (defthm isClassType-not-assignable-to-TWOWORD
;;   (implies (ISCLASSTYPE GT)
;;            (not (ISASSIGNABLE GT 'TWOWORD ENV))))

;;
;;
;; not so useful just a property
;;

;; (include-book "../BCV/bcv-isAssignable-transitive")

;;; Tue Feb  1 01:51:17 2005.... We updated how the BCV lay down value.

(defthm isMatchingType-general-specific-size-2
  (implies (and (isAssignable sT gT env)
                (equal (sizeof any) 2)
                (isMatchingType any (list* 'topx gT anyStack1) env))
           (isMatchingType any (list* 'topx sT anyStack2) env)))

;; this complication arise from the fact that isAssignable does not deal with
;; how many slots a value of that type occupy. only about relations, 
;; The funny case is both twoword and oneword is assignable to top. 

(defthm popMatchingType-preserve-TypeListAssignable
  (implies (TypeListAssignable l1 l2 env)
           (TypeListAssignable (popMatchingType any l1)
                               (popMatchingType any l2) env)))


(defthm sizeof-1-or-2
  (implies (not (equal (sizeof x) 1))
           (equal (sizeof x) 2)))

(local (in-theory (disable consistent-sig-type)))

(defthm consistent-sig-type-implies-good-bcv-type
  (implies (consistent-sig-type typ icl)
           (good-bcv-type typ icl))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable consistent-sig-type))))


(defthm consistent-sig-stack-cons
  (implies (consistent-sig-stack (cons gl1 gl) icl)
           (good-bcv-type gl1 icl))
  :hints (("Goal" :expand (consistent-sig-stack (cons gl1 gl) icl)
           :in-theory (enable good-bcv-type
                              consistent-sig-type))))



(defthm if-size-of-match-top
  (implies (and (equal (sizeof any) 1)
                (not (equal any 'topx)))
           (not (ISMATCHINGTYPE ANY (CONS 'topx GL2)
                                ENV))))

(defthm isMatch-isMatch-top
  (implies (and (equal (sizeof any) 1)
                (ISMATCHINGTYPE ANY (CONS 'topx GL2) ENV))
           (ISMATCHINGTYPE ANY (list* 'topx SL3) ENV))
  :hints (("Goal" :cases ((equal any 'topx)))))


(defthm isAssignable-top
  (implies (not (equal gl1 'topx))
           (not (ISASSIGNABLE 'topx GL1 ENV))))


(defthm TypeListAssignable-isMatchType-1
  (implies (and (TypeListAssignable sL gL env)
                (equal (sizeof any) 1)
                (consistent-sig-stack sl icl)
                (consistent-sig-stack gl icl)
                (good-bcv-type any icl)
                (good-icl icl)
                (good-scl (classtableEnvironment env))
                (icl-scl-compatible icl (classtableEnvironment env))
                (consp gl)
                (isMatchingType any gL env))
           (isMatchingType any sL env))
  :hints (("Goal" :in-theory (disable sizeof isAssignable isMatchingType)
           :restrict ((isMatchingType-general-specific-size-1
                       ((icl icl)
                        (st  sL1)
                        (gt  gL1))))
           :cases ((consp gl)))
          ("Subgoal *1/5" :cases ((equal (car gl) 'topx)))))


(defthm isAssignable-twoword-long-double
  (implies (and (not (equal x 'LONG))
                (not (equal x 'DOUBLE))
                (not (equal x 'TWOWORD)))
           (not (isAssignable x 'TWOWORD env))))


;; (defthm |Subgoal 1.1.1|
;;   (IMPLIES (AND (ISASSIGNABLE SL1 'topx ENV)
;;               (TYPELISTASSIGNABLE SL2 (CONS GL3 GL4)
;;                                   ENV)
;;               (EQUAL (SIZEOF ANY) 2)
;;               (NOT (EQUAL (SIZEOF (CAR SL2)) 2))
;;               (NOT (EQUAL SL1 'TWOWORD))
;;               (ISASSIGNABLE GL3 ANY ENV))
;;            (equal (EQUAL SL1 'topx) t)))



;; (defthm |Subgoal 5.1.1|
;;   (IMPLIES (AND (EQUAL (CADR GL) 'topx)
;;                 (ISASSIGNABLE (CAR GL) ANY ENV)
;;                 (ISASSIGNABLE SL1 (CAR GL) ENV)
;;                 (TYPELISTASSIGNABLE (CONS SL3 SL4)
;;                                     (CDR GL)
;;                                     ENV)
;;                 (EQUAL (SIZEOF ANY) 2)
;;                 (EQUAL (SIZEOF SL1) 1)
;;                 (NOT (EQUAL SL1 'TWOWORD))
;;                 (NOT (EQUAL SL1 'ONEWORD))
;;                 (CONSISTENT-SIG-STACK (CONS SL3 SL4))
;;                 (CONSISTENT-SIG-STACK GL))
;;            (equal (EQUAL SL3 'topx) t)))


;; Subgoal *1/2.3
;; (IMPLIES (AND (CONSP SL)
;;               (NOT (EQUAL (CAR SL) 'TWOWORD)) 
;;               ;;; should be not (equal (cadr sl) ...)
;;               (NOT (EQUAL (CAR SL) 'LONG))
;;               (NOT (EQUAL (CAR SL) 'DOUBLE))
;;               (CONSISTENT-SIG-TYPE (CAR SL))
;;               (TYPELISTASSIGNABLE (CDR SL)
;;                                   (CDR GL)
;;                                   ENV)
;;               (CONSP (CDR GL))
;;               (NOT (EQUAL (CADR GL) 'topx))
;;               (TYPELISTASSIGNABLE SL GL ENV)
;;               (ISMATCHINGTYPE ANY GL ENV)
;;               (EQUAL (SIZEOF ANY) 2)
;;               (CONSISTENT-SIG-STACK SL)
;;               (CONSISTENT-SIG-STACK GL))
;;          (ISMATCHINGTYPE ANY SL ENV)).

;; (INT LONG)
;; (TOP LONG)

;; (defthm |Subgoal *1/2.3|
;; (IMPLIES (AND (CONSP SL)
;;
;;               (NOT (EQUAL (CADR GL) 'topx))
;;               (TYPELISTASSIGNABLE SL GL ENV)
;;               (ISMATCHINGTYPE ANY GL ENV)
;;               (EQUAL (SIZEOF ANY) 2)
;;               (CONSISTENT-SIG-STACK SL)
;;               (CONSISTENT-SIG-STACK GL))



;;;
;;; Tue Feb 1 01:38:46 2005. We updated the how opstack lay out  
;;; LONG value. This following theorem does not go through!! 
;;;
;;; Because this is not true!!  .... 
;;;
;;                 (consistent-sig-stack sL icl)
;;                 (consistent-sig-stack gL icl)
;;                 (good-bcv-type any icl)
;;                 (good-icl icl)
;;                 (icl-scl-compatible icl (classtableEnvironment env)))


(local (in-theory (disable classtableEnvironment)))

(defthm TypeListAssignable-isMatchType-2
  (implies (and (TypeListAssignable sL gL env)
                (isMatchingType any gL env)                
                (equal (sizeof any) 2)
                (consistent-sig-stack sL icl)
                (consistent-sig-stack gL icl)
                (good-bcv-type any icl)
                (good-icl icl)
                (icl-scl-compatible icl (classtableEnvironment env)))
           (isMatchingType any sL env)))


;; #| 
;; (defthm TypeListAssignable-isMatchType
;;   (implies (and (isMatchingType any gL env)
;;                 (TypeListAssignable sL gL env)
;;                 (consistent-sig-stack sL)
;;                 (consistent-sig-stack gL))
;;            (isMatchingType any sL env))
;;   :hints (("Goal" :in-theory (disable  isMatchingType
;;                               sizeof) ;;isAssignable)
;;            :cases ((equal (sizeof any) 1)
;;                    (equal (sizeof any) 2))
;;            :use 
;;            :do-not-induct t)))
;; |#


;-------------------------------------------------
;
; Next we need to prove popMatchingType preserve the consistent-sig-stack
; 

;;; Thu Jan 15 21:48:21 2004 these rules are pretty bad that it has free avariable.s 
;;; 

(defthm isAssignable-size-equal
  (implies (and (isAssignable y x env)
                (not (equal x 'topx)))
            (equal (sizeof y) (sizeof x))))

(defthm not-consistent-stack
  (implies (and (equal (sizeof any) 2)
                (isAssignable x ANY env))
           (not (consistent-sig-stack (cons x l) icl)))
  :hints (("Goal" :in-theory (enable consistent-sig-stack))))
                                     

(defthm consistent-sig-stack-perserved
  (implies (and (isMatchingType any l env)
                (not (equal any 'topx))
                (consistent-sig-stack l icl))
           (consistent-sig-stack (popMatchingType any l) icl))
  :hints (("Goal" :in-theory 
           (disable isAssignable sizeof)
           :cases ((equal (sizeof any) 1)
                   (equal (sizeof any) 2))
           :do-not-induct t)
          ("Subgoal 2" :expand (consistent-sig-stack l icl))))

;; this is a problem. 

;; one invariant is the any won't be byte short char          
;; but we do not enforce it with consistent-sig


(defun valid-type (type icl)
  (and (not (equal type 'topx)) ;; discovered by 
       (consistent-sig-type type icl)))
  
;;
;; valid-type only assert possible list used in bcv spec. it is applied on
;; constant list. 
;; 

(defun valid-type-list (l icl)
  (if (endp l) t
    (and (valid-type (car l) icl)
         (valid-type-list (cdr l) icl))))
 
;; (i-am-here)


(local (in-theory (disable good-scl)))

(defthm canPop1-more-general-implies-canPop1-more-specific
  (implies (and  (TypeListAssignable sL gL env)
                 (canPop1 anyList gL env)
                 (consistent-sig-stack gL icl)
                 (consistent-sig-stack sL icl)
                 (valid-type-list anyList icl)
                 (good-icl icl)
                 (good-scl (classtableEnvironment env))
                 (icl-scl-compatible icl (classtableEnvironment env)))
           (canPop1 anyList sL env))
  :hints (("Goal" :in-theory 
           (disable isAssignable popMatchingType isMatchingType sizeof)
           :do-not '(generalize)
           :restrict ((TypeListAssignable-isMatchType-2
                       ((icl icl)
                        (sl sl)
                        (gl gl)))
                      (TypeListAssignable-isMatchType-1
                       ((icl icl)
                        (sl sl) (gl gl)))
                      (consistent-sig-stack-perserved
                       ((icl icl)
                        (env env)))))
          ("Subgoal *1/9" :cases ((equal (sizeof (car anyList)) 1)
                                  (equal (sizeof (car anyList)) 2)))))




(defthm canPop1-more-general-implies-canPop1-more-specific-f
  (implies (and (canPop1 anyList gL env)
                (TypeListAssignable sL gL env)
                 (consistent-sig-stack sL icl)
                 (consistent-sig-stack gL icl)
                 (valid-type-list anyList icl)
                 (good-icl icl)
                 (good-scl (classtableEnvironment env))
                 (icl-scl-compatible icl (classtableEnvironment env)))
           (canPop1 anyList sL env))
  :hints (("Goal" :in-theory  (disable isAssignable popMatchingType
                                       isMatchingType sizeof)))
  :rule-classes :forward-chaining)


;; Sun Mar 28 21:32:05 2004. We need valid-type-list assertion to make 
;; the theorem true!!

(defthm pop-canPopList-preserve-consistent-sig-stack
  (implies (and (consistent-sig-stack l icl)
                (valid-type-list popl icl)
                (canPop1 popl l env)
                (good-icl icl)
                (icl-scl-compatible icl (classtableEnvironment env)))
           (consistent-sig-stack (popMatchingList1 popl l) icl))
  :hints (("Goal" :in-theory (disable isMatchingType popMatchingType))))


(defthm lemma-perserve-typelistassignable
  (implies (and (TypeListAssignable sl gL env)
                (consistent-sig-stack sl icl)
                (consistent-sig-stack gl icl)
                (consp gl)
                (good-bcv-type tx icl)
                (not (equal tx 'topx))
                (isMatchingType tx gl env)
                (good-icl icl)
                (good-scl (classtableEnvironment env))
                (icl-scl-compatible icl (classtableEnvironment env)))
           (consistent-sig-stack (popMatchingType tx sl) icl))
  :hints (("Goal" :in-theory (disable isMatchingType sizeof
                                      popMatchingType)
           :restrict ((consistent-sig-stack-perserved
                       ((icl icl) (env env))))
           :cases ((not (equal (sizeof tx) 1)))
           :do-not-induct t)))


(defthm pop-canPopList-preserve-TypeListAssignable
  (implies (and (TypeListAssignable sL gL env)
                (canPop1 popl gl env)
                (consistent-sig-stack sl icl)
                (consistent-sig-stack gl icl)
                (valid-type-list popl icl)
                (good-icl icl)
                (good-scl (classtableEnvironment env))
                (icl-scl-compatible icl (classtableEnvironment env)))
           (TypeListAssignable (popMatchingList1 popl sl)
                               (popMatchingList1 popl gl) env))
  :hints (("Goal" :in-theory (disable isMatchingType popMatchingType))))

;; this is for monotonicity 
;;
;; (defthm pop-canPopList-preserve-TypeListAssignable
;;   (implies (and (TypeListAssignable sL gL env)
;;                 (consistent-sig-stack sl)
;;                 (consistent-sig-stack gl)
;;                 (valid-type-list popl)
;;                 (canPop1 popl gl env))
;;            (TypeListAssignable (popMatchingList1 popl sl)
;;                                (popMatchingList1 popl gl) env))
;;   :hints (("Goal" :in-theory (disable isMatchingType popMatchingType))))
;;


(defthm TypeListAssignable-length-instance
  (mylet*  ((sl (POPMATCHINGLIST1 ANYLIST (FRAMESTACK SFRAME)))
            (gl (POPMATCHINGLIST1 ANYLIST (FRAMESTACK GFRAME))))
    (implies (TypeListAssignable sl gl env)
             (equal (len sl) (len gl)))))


(defthm consistent-sig-type-fact-1
  (CONSISTENT-SIG-TYPE 'INT ICL)
  :hints (("Goal" :in-theory (enable consistent-sig-type good-bcv-type))))

;; strange why this rule does not trigger at all.


(defthm Valid-Type-Transition-more-general-implies-more-specific
  (implies (and (sig-frame-more-general gframe sframe env)
                (validtypetransition env anylist any gframe)
                (valid-type-list anyList icl)
                (consistent-sig-stack (frameStack gframe) icl)
                (consistent-sig-stack (frameStack sframe) icl)
                (good-icl icl)
                (good-scl (classtableEnvironment env))
                (icl-scl-compatible icl (classtableEnvironment env)))
           (validtypetransition env anylist any sframe))
  :hints (("Goal" :in-theory 
           (disable isAssignable sizeof isMatchingType)
           :do-not-induct t
           :restrict ((TypeListAssignable-length-instance ((env env)
                                                           (sframe sframe)
                                                           (gframe gframe)
                                                           (anylist
                                                            anylist)))))))

(defthm sig-check-IADD-on-more-general-implies-more-specific
  (implies (and (sig-frame-more-general gframe sframe env)
                (consistent-sig-stack (frameStack gframe) icl)
                (consistent-sig-stack (frameStack sframe) icl)
                (check-iadd inst env gframe)
                (good-icl icl)
                (good-scl (classtableEnvironment env))
                (icl-scl-compatible icl (classtableEnvironment env)))
           (check-iadd inst env sframe))
  :hints (("Goal" :in-theory (disable validtypetransition)
           :restrict ((Valid-Type-Transition-more-general-implies-more-specific
                       ((gframe gframe) (sframe sframe) (icl icl)))))))

(encapsulate ()
             (local (include-book "../../BCV/bcv-functions"))
             (defun normal-frame (frame-pair)
               (mv-nth 0 frame-pair)))

;; we may need stronger consistency as defined 
;; in the tagged-check-m6.lisp
;; which also check each typed being refered is valid.
;;
;; Deal with some form of the "Frame" problem, what change and what does not
;; State machine seems to be easy to keep track of the frame
;; using logic is hard!  
;; 
;; Difficult tasks ... 


(defthm pushOperandStack-perserve-consistent-sig-stack
   (implies (and (consistent-sig-type tx icl)
                 (not (equal tx 'topx)))
            (equal (consistent-sig-stack (pushOperandStack tx l) icl)
                   (consistent-sig-stack l icl))))


(defthm TypeTransition-perserve-consistent-stack
  (implies (and (ValidTypeTransition env anyList ResultType cframe)
                (consistent-sig-stack (frameStack cframe) icl)
                (consistent-sig-type ResultType icl)
                (valid-type-list anyList icl)
                (valid-type ResultType icl)
                (good-icl icl)
                (icl-scl-compatible icl (classtableEnvironment env)))
           (consistent-sig-stack 
            (frameStack (TypeTransition env anyList
                                        ResultType cframe)) icl))
  :hints (("Goal" :in-theory (disable pushOperandStack))))
           

(defthm execute-iadd-preserve-consistent-sig-stack
  (implies (and (consistent-sig-stack (frameStack curFrame) icl)
                (check-iadd inst env curFrame)
                (good-icl icl)
                (icl-scl-compatible icl (classtableEnvironment env)))
           (consistent-sig-stack 
            (frameStack (normal-frame (execute-iadd inst env curFrame))) icl))
  :hints (("Goal" :in-theory (disable TypeTransition validtypetransition))))
                                      
;
; with this above: iadd isub, lsub ladd, should be finished relatively easily
; 
; Still need to prove the monotonicity 

(defthm iadd-monotonicity
  (implies (sig-frame-more-general gframe sframe env)
           (sig-frame-more-general 
            (normal-frame (execute-iadd inst env gframe))
            (normal-frame (execute-iadd inst env sframe)) env)))

;;
;;
;; next to a getfield 
;----------------------------------------------


;; (defthm Valid-Type-Transition-push-consistent-sig-type
;;   (implies (and (validtypetransition env anylist anyx sframe)
;;                 (consistent-sig-type anyx)
;;                 (consistent-sig-type any)
;;                 (equal (sizeof anyx) (sizeof any)))
;;            (validtypetransition env anylist any sframe))
;;   :rule-classes :forward-chaining)

;;(i-am-here)              

(defthm Valid-Type-Transition-push-consistent-sig-type-type-b
  (implies (and (validtypetransition env anylist anyx gframe)
                (consistent-sig-type anyx icl)
                (consistent-sig-type any icl)
                (equal (sizeof anyx) (sizeof any))
                (good-icl icl)
                (good-scl (classtableEnvironment env))
                (icl-scl-compatible icl (classtableEnvironment env)))
           (validtypetransition env anylist any gframe))
  :hints (("Goal" :in-theory (enable consistent-sig-type))))

;; (i-am-here)

(local (defthm isAssignable-nil-nil
         (isAssignable nil nil env)))


(defthm type-list-assignable-sig-frame-more-general-isAssignable
  (implies (typelistassignable l1 l2 env)
           (isAssignable (nth any l1)
                         (nth any l2) env))
  :hints (("Goal" :in-theory (disable isAssignable))))


(defthm sig-frame-more-general-isAssignable
  (implies (sig-frame-more-general gframe sframe env)
           (isAssignable (nth1OperandStackIs any sframe)
                         (nth1OperandStackIs any gframe) env))
  :hints (("Goal" :in-theory (enable nth1OperandStackIs))))


;----------------------------------------------------------------------

(defthm good-icl-fact-1
  (implies (bcv::good-icl icl)
           (djvm::class-exists? "java.lang.Object" icl))
  :hints (("Goal" :in-theory (enable bcv::good-icl))))


(defthm good-icl-consistent-sig-type-array-type-implies-consistent-component-type
  (implies (and (bcv::good-icl icl)
                (bcv::consistent-sig-type typ icl)
                (bcv::isArrayType typ))
           (bcv::good-java-type (bcv::component-type typ) icl))
  :hints (("Goal" :in-theory (enable bcv::consistent-sig-type
                                     bcv::good-bcv-type
                                     djvm::primitive-type?
                                     bcv::good-java-type))))


(local (defthm bcv-good-java-type-implie-consistent-sig-type
         (implies (bcv::good-java-type typ icl)
                  (bcv::consistent-sig-type (bcv::translate-type typ) icl))
         :hints (("Goal" :in-theory (e/d (bcv::consistent-sig-type
                                          bcv::good-java-type
                                          bcv::good-bcv-type) 
                                        ())))))


(defthm bcv-good-java-type-implies-consistent-sig-type-specific
  (implies (bcv::good-java-type (bcv::component-type typ) icl)
           (bcv::consistent-sig-type (bcv::translate-type
                                      (bcv::arrayElementType typ)) icl))
  :hints (("Goal" :in-theory (enable bcv::arrayElementType
                                     bcv::consistent-sig-type
                                     bcv::good-bcv-type))))


;----------------------------------------------------------------------

;; property of BCV::isAssignable



(local 
 (defthm not-reference-isAssignable
   (not (isAssignable 'reference (list 'ARRAY any) env))
   :hints (("Goal" :in-theory (enable isAssignable)
            :expand (isAssignable 'reference (list 'ARRAY any) env)))))

(local 
 (defthm not-reference-isAssignable-2
   (not (isAssignable 'reference (list*  'ARRAY any1 any2) env))
   :hints (("Goal" :in-theory (enable isAssignable)
            :expand (isAssignable 'reference (list*  'ARRAY any1 any2) env)))))


;;; the proof of this is a bit not so robust!! 

;;; after the above two local events it should go through better!! 
;;;

(defthm assignable-assignable
  (implies (and (bcv::isassignable typ1 typ2 env)
                (bcv::isArrayType typ1)
                (bcv::isArrayType typ2))
           (bcv::isassignable (bcv::arrayElementType typ1)
                              (bcv::arrayElementType typ2) env))
  :hints (("Goal" :in-theory (enable bcv::isjavaassignable bcv::isassignable bcv::arrayElementType))))


(defthm not-component-type-top
  (implies (and (bcv::consistent-sig-type typ icl)
                (bcv::good-icl icl)
                (bcv::isArrayType typ))
           (not (equal (bcv::arrayElementType typ) 'topx)))
  :hints (("Goal" :in-theory (enable bcv::arrayElementType
                                     good-bcv-type
                                     jvm::primitive-type?
                                     good-java-type
                                     consistent-sig-type))))



;----------------------------------------------------------------------


(defthm consistent-sig-type-null
  (consistent-sig-type 'NULL env)
  :hints (("Goal" :in-theory (enable consistent-sig-type
                                     good-bcv-type))))


;----------------------------------------------------------------------
;
; The following are what is necessary for showing 
;  
;  bcv::execute-AALOAD is monotonic
;

(local 
 (encapsulate ()
     (local (include-book "base-canPop1-consistent-sig-stack-consistent-value"))

 (defthm canPop1-nth1-fact-3-array-type
  (implies (and (bcv::canPop1 '(int (array (class "java.lang.Object")))
                              (bcv::framestack frame)  env)
                (not (equal (bcv::nth1OperandStackIs 2 frame) 'NULL)))
           (bcv::isArrayType (bcv::nth1OperandStackIs 2 frame)))
  :hints (("Goal" :in-theory (disable bcv::canPop1 bcv::isArrayType
                                      bcv::nth1OperandStackIs))))))

;;(i-am-here)
(local 
 (defthm isAssignable-arraytype-not-null-arrayType
   (implies (and (isAssignable typ1 typ2 env1)
                 (isarraytype typ2)
                 (not (equal typ1 'NULL)))
            (isarraytype typ1))))


(defthm canPop1-sig-frame-more-general-isAssignable-element-type
  (implies (and (canPop1 '(int (array (class "java.lang.Object")))
                         (frameStack gframe) env)
                (consistent-sig-stack (frameStack sframe) icl)
                (consistent-sig-stack (frameStack gframe) icl)
                (not (equal (nth1OperandStackIs 2 gframe) 'NULL))
                (not (equal (nth1OperandStackIs 2 sframe) 'NULL))
                (good-icl icl)
                (good-scl (classtableEnvironment env))
                (icl-scl-compatible icl (classtableEnvironment env))
                (sig-frame-more-general gframe sframe env))
           (isAssignable (arrayElementType (nth1OperandStackIs 2 sframe))
                         (arrayElementType (nth1OperandStackIs 2 gframe)) env))
  :hints (("Goal" :in-theory (disable canPop1 arrayElementType isAssignable
                                      nth1OperandStackIs
                                      isarraytype
                                      bcv::translate-type
                                      consistent-sig-stack)
           :restrict ((canPop1-nth1-fact-3-array-type
                       ((env env))))
           :use ((:instance 
                  isAssignable-arraytype-not-null-arrayType
                  (env1 env)
                  (typ2 (nth1OperandStackIs 2 gframe))
                  (typ1 (nth1OperandStackIs 2 sframe)))))))


(local (defthm pushOperandStack-TypeListAssignable
         (implies (and (TypeListAssignable sL gL env)
                       (not (equal g 'topx))
                       (isAssignable s g env))
           (TypeListAssignable (pushOperandStack s sL)
                               (pushOperandStack g gL) env))))

(local (defthm TypeListAssignable-len-equal
         (implies (TypeListAssignable sL gL env)
                  (equal (len sL) (len gl)))))


(local (defthm TypeListAssignable-len-equal-f
         (implies (TypeListAssignable sL gL env)
                  (equal (len sL) (len gl)))
         :rule-classes :forward-chaining))



(local (defthm popMatchinglist1-len
         (implies (equal (len l1) (len l2))
                  (= (len (popMatchinglist1 l l1))
                     (len (popMatchinglist1 l l2))))
         :hints (("Goal" :in-theory (enable popMatchingType)))
         :rule-classes :linear))

(local (defthm TypeListAssignable-popMatchingList
  (implies (TypeListAssignable sl gl env)
           (TypeListAssignable (popMatchinglist1 l sl)
                               (popMatchinglist1 l gl) env))))


(defthm sig-frame-more-general-pushOperand-stack
  (implies (and (sig-frame-more-general gframe sframe env)
                (not (equal g 'topx))
                (isAssignable s g env))
           (sig-frame-more-general (TypeTransition env toPop g gframe)
                                   (TypeTransition env toPop s sframe) env))
  :hints (("Goal" :in-theory (disable make-sig-frame  isAssignable)
           :do-not-induct t)))

;
; key result to get the execute-* proof. 
;           
;----------------------------------------------------------------------


(defthm pushOperandStack-TypeListAssignable
  (implies (and (TypeListAssignable sL gL env)
                (not (equal g 'topx))
                (isAssignable s g env))
           (TypeListAssignable (pushOperandStack s sL)
                               (pushOperandStack g gL) env)))


;----------------------------------------------------------------------

(defthm len-pushOpstack
  (implies (and (equal (sizeof typ2) (sizeof typ1))
                (not (equal typ1 'void))
                (not (equal typ2 'void)))
           (equal (equal (len (pushoperandstack typ1 anystack))
                         (len (pushoperandstack typ2 anystack))) t))
  :hints (("Goal" :in-theory (enable pushoperandstack))))



;----------------------------------------------------------------------

;;;
;;; export these facts?? 
;;;
;;; 

(defthm good-icl-fact-1
   (implies (bcv::good-icl icl)
            (djvm::class-exists? "java.lang.Object" icl)))


(defthm good-icl-consistent-sig-type-array-type-implies-consistent-component-type
   (implies (and (bcv::good-icl icl)
                 (bcv::consistent-sig-type typ icl)
                 (bcv::isArrayType typ))
            (bcv::good-java-type (bcv::component-type typ) icl))
   :hints (("Goal" :in-theory (enable bcv::consistent-sig-type
                                      bcv::good-bcv-type
                                      djvm::primitive-type?
                                      bcv::good-java-type))))

(defthm bcv-good-java-type-implie-consistent-sig-type
  (implies (bcv::good-java-type typ icl)
           (bcv::consistent-sig-type (bcv::translate-type typ) icl))
  :hints (("Goal" :in-theory (e/d (bcv::consistent-sig-type
                                   bcv::good-java-type
                                   bcv::good-bcv-type) 
                                  ()))))

;; (i-am-here) ;; Fri Jul 29 22:14:25 2005

(defthm bcv-good-java-type-implies-consistent-sig-type-specific
  (implies (bcv::good-java-type (bcv::component-type typ) icl)
           (bcv::consistent-sig-type (bcv::translate-type (bcv::arrayElementType typ)) icl))
  :hints (("Goal" :in-theory (e/d (bcv::arrayElementType
                                   bcv::component-type) ()))))



;;              :restrict ((bcv::Valid-Type-Transition-more-general-implies-more-specific
;;                          ((bcv::gframe gframe) (bcv::sframe sframe) (bcv::icl
;;                                                                      icl)))
;;                         (bcv::not-component-type-top
;;                          ((bcv::icl icl)))
;;                         (bcv::sig-frame-more-general-isAssignable
;;                          ((bcv::env env)))
;;                         (isassignable-size-equal
;;                          ((env env)))
;;                         (canPop1-nth1-fact-1
;;                          ((env env)))
;;                         (canPop1-nth1-fact-2
;;                          ((env env)))
;;                         (canPop1-nth1-fact-3-array-type
;;                          ((env env)))
;;                         (bcv::valid-type-transition-push-consistent-sig-type-type-b
;;                          ((bcv::icl icl)
;;                           (bcv::gframe sframe)
;;                           (bcv::env env)
;;                           (bcv::any (bcv::arrayElementType 
;;                                      (bcv::nth1OperandStackIs 2 sframe)))
;;                           (bcv::anyx (bcv::arrayElementType 
;;                                       (bcv::nth1OperandStackIs 2
;;                                                                gframe))))))))))
