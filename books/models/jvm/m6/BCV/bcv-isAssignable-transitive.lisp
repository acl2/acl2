(in-package "BCV")
(include-book "../BCV/typechecker")

(acl2::set-match-free-default :all)



(defthm isJavaSubclassOf-Transitive 
  (implies (and (isJavaSubclassOf t1 t2 cl)
                (isJavaSubclassOf t2 t3 cl))
           (isJavaSubclassOf t1 t3 cl))
  :hints (("Goal" :do-not '(generalize))))


(include-book "../DJVM/consistent-state")


(local (in-theory (disable djvm::consistent-state name-of isClassType isArrayType)))

(defthm isArrayType-implies-not-isClassType
  (implies (isArrayType tx)
           (not (isClassType tx)))
  :hints (("Goal" :in-theory (enable isArrayType isClassType))))


(include-book "../BCV/bcv-functions")

;;;
;;; In type check we have 
;;;
;;;

;; (defun classname-s (scd)          (nth 1 scd))
;; (defun super-s     (scd)          (nth 2 scd))
;; (defun constantpool-s   (scd)     (cdr (nth 3 scd)))
;; (defun fields-s         (scd)     (cdr (nth 4 scd)))
;; (defun methods-s        (scd)     (cdr (nth 5 scd)))
;; (defun interfaces-s     (scd)     (cdr (nth 6 scd)))
;; (defun accessflags-s    (scd)     (cdr (nth 7 scd)))
;; (defun attributes-s     (scd)     (cdr (nth 8 scd)))

;; (defun make-class-def (raw-class)
;;   (make-class-term 
;;    (classname-s raw-class)
;;    (mem '*interface* (accessflags-s raw-class))
;;    (super-s     raw-class)
;;    (constantpool-s  raw-class)
;;    (interfaces-s    raw-class)
;;    (fields-s        raw-class)
;;    (methods-s       raw-class)
;;    (accessflags-s   raw-class)
;;    (attributes-s    raw-class)))


;; (defun make-static-class-decl (cn super cp fs ms is as ats)
;;   (LIST 'CLASS cn super
;;         (CONS 'CONSTANT_POOL CP)
;;         (CONS 'FIELDS fs)
;;         (CONS 'METHODS ms)
;;         (CONS 'INTERFACES is)
;;         (CONS 'ACCESSFLAGS as)
;;         (CONS 'ATTRIBUTES ats)))


;; ;; (defun classClassName (Class)
;; ;;   (nth 1 Class))

;; ;; (defun classIsInterface (Class)
;; ;;   (nth 2 Class))

;; ;; (defun classSuperClassName (Class)
;; ;;   (nth 3 Class))

;; ;; (defun classConstantPool (Class)
;; ;;   (cdr (nth 4 Class)))

;; ;; (defun classInterfaces (Class)
;; ;;   (cdr (nth 5 Class)))

;; ;; (defun classFields (Class)
;; ;;   (cdr (nth 6 Class)))

;; ;; (defun classMethods (Class)
;; ;;   (cdr (nth 7 Class)))

;; ;; (defun classAccessFlags (Class)
;; ;;   (cdr (nth 8 Class)))

;; ;; (defun classAttributes (Class)
;; ;;   (cdr (nth 9 Class)))


;; (defun scl-decl-bcv2jvm (scl-decl)
;;   (make-static-class-decl 
;;     (classClassName scl-decl)
;;     (classSuperClassName scl-decl)
;;     (classConstantPool scl-decl)
;;     (classFields scl-decl)
;;     (classMethods scl-decl)
;;     (classInterfaces scl-decl)
;;     (classAccessFlags scl-decl)
;;     (classAttributes scl-decl)))


;;; Tue Jul 12 21:24:30 2005
;;;
;;; start fixing this. 

(defthm equal-make-class-def-scl-decl-bcv2jvm
  (implies (jvm::wff-class-rep-static raw-class)
           (equal (scl-decl-bcv2jvm 
                   (make-class-def raw-class))
                  raw-class))
  :hints (("Goal" :in-theory (enable jvm::wff-class-rep-static))))



;; (skip-proofs 
;;  (defthm equal-make-class-def-scl-decl-bcv2jvm
;;    (implies (jvm::wff-class-rep-static raw-class)
;;             (equal (scl-decl-bcv2jvm 
;;                     (make-class-def raw-class))
;;                    raw-class))))

;; ;; (skip-proofs 
;; ;;  (defthm equal-make-class-def-scl-decl-bcv2jvm-2
;; ;;    (equal (make-class-def (scl-decl-bcv2jvm raw-class))
;; ;;           raw-class)))
   
;; ;;; need to fix jvm::wff-class-rep-static
;; ;;;


;; (defun scl-bcv2jvm (scl)
;;   (if (endp scl) nil
;;     (cons (scl-decl-bcv2jvm (car scl))
;;           (scl-bcv2jvm (cdr scl)))))

;; (defun scl-jvm2bcv (raw-scl)
;;   (if (endp raw-scl) nil
;;     (cons (make-class-def (car raw-scl))
;;           (scl-jvm2bcv (cdr raw-scl)))))


;; (defun good-scl (scl)
;;   (equal (scl-jvm2bcv (scl-bcv2jvm scl)) scl))

;; (defun icl-scl-compatible (icl scl)
;;   (and (good-scl scl)
;;        (djvm::class-table-is-loaded-from icl (scl-bcv2jvm scl))))

;; 
;;

(defthm wff-icl-implies-not-class-exists-array
  (implies (and (wff-icl icl)
                (not (stringp x)))
           (not (jvm::isclassterm (jvm::class-by-name x icl)))))
           

(defthm good-icl-implies-not-class-exists-array
  (implies (good-icl icl)
           (not (jvm::isclassterm (jvm::class-by-name (list* 'array any)
                                                      icl))))
  :hints (("Goal" :in-theory (e/d () (jvm::isclassterm)))))



(defthm good-java-type-good-component-type
  (implies (and (good-icl icl)
                (good-java-type typ icl)
                (isArrayType typ))
           (good-java-type (component-type typ) icl))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d (jvm::array-component-type isclasstype isArrayType)
                           (good-icl)))))
                
;;
;; first relate bcv::isClassTerm on SCL with jvm::isClassTerm on ICL
;; when icl and SCL are related! 
;;


(defthm icl-loaded-from-scl-implies-class-exists-class-exists-s
  (implies (and (jvm::class-table-is-loaded-from icl scl)
                (jvm::isClassTerm (jvm::class-by-name n icl)))
           (mv-nth 0 (jvm::class-by-name-s n scl))))



;; (i-am-here) ;; Fri Jul 15 02:10:55 2005


(defthm class-exists-s-implies-bcv-is-class-term
   (implies (and (mv-nth 0 (jvm::class-by-name-s n (scl-bcv2jvm scl)))
                 (equal (scl-jvm2bcv (scl-bcv2jvm scl)) scl))
            (equal (bcv::class-by-name n scl)
                   (make-class-def 
                    (mv-nth 1 (jvm::class-by-name-s n (scl-bcv2jvm scl))))))
   :hints (("Goal" :do-not '(generalize fertilize)
            :in-theory (enable jvm::classname-s class-by-name
                               ))))


;; (defthm class-exists-s-implies-bcv-is-class-term
;;    (implies (and (mv-nth 0 (jvm::class-by-name-s n (scl-bcv2jvm scl)))
;;                  (good-scl scl))
;;             (equal (bcv::class-by-name n scl)
;;                    (make-class-def 
;;                     (mv-nth 1 (jvm::class-by-name-s n (scl-bcv2jvm scl))))))
;;    :hints (("Goal" :do-not '(generalize fertilize)
;;             :in-theory (enable jvm::classname-s class-by-name
;;                                ))))




(defthm found-means-isClassTerm 
  (implies (and (mv-nth 0 (jvm::class-by-name-s n (scl-bcv2jvm scl)))
                (good-scl scl))
           (bcv::isClassTerm (bcv::class-by-name n scl))))


(defthm good-java-type-isClassType-isClassTerm
  (implies (and (good-java-type typ icl)
                (isclasstype typ))
           (jvm::isClassTerm (jvm::class-by-name (name-of typ) icl)))
  :hints (("Goal" :in-theory (enable isclasstype isArrayType jvm::primitive-type?))))


(defthm bcv-isClassTerm-jvm-isClassTerm
  (implies (and (icl-scl-compatible icl scl)
                (good-scl scl)
                (good-java-type typ icl)
                (isclasstype typ))
           (bcv::isClassTerm (bcv::class-by-name (name-of typ) scl))))

;;;
;;; the following is a bit difficult. 
;;;


;; (local 
;;  (defthm loaded-in-icl-then-found-in-scl
;;    (implies (and (icl-scl-compatible icl scl)
;;                  (jvm::isClassTerm (jvm::class-by-name n icl)))
;;             (mv-nth 0 (jvm::class-by-name-s n (scl-bcv2jvm scl))))))


(local 
 (defthm good-scl-not-class-exist
   (implies (good-scl scl)
            (not (isClassTerm 
                  (class-by-name 
                   (classSuperClassName 
                    (class-by-name "java.lang.Object" scl))
                   scl))))))


;;;
;;; we just add an assertion that scl does not have a super for
;;; "java.lang.Object"
;;;

;;
;; (skip-proofs 
;;  (local 
;;   (defthm icl-scl-compatible-not-class-term-not-class-static
;;     (implies (and (icl-scl-compatible icl scl)
;;                   (good-icl icl))
;;              (not (isC


(local 
 (defthm good-icl-icl-scl-implies-not-isJavaAssignable
   (implies (and (good-icl icl)
                 (icl-scl-compatible icl scl))
            (NOT (ISJAVASUBCLASSOF "java.lang.Object" NIL SCL)))))


(local 
 (defthm java-lang-Object-subclass-of-nothing-but-java-lang-Object-lemma
  (implies (and (good-icl icl)
                (not (equal t3 "java.lang.Object"))
                (icl-scl-compatible icl scl))
           (not (isjavasubclassof "java.lang.Object" t3 scl)))
  :hints (("Goal" :in-theory (e/d (name-of)
                                  (isClassTerm
                                   good-icl))
           :expand (isjavasubclassof "java.lang.Object" t3 scl)))))

(local 
 (defthm good-java-type-not-equal-class-implies-not-equal-name-of
   (implies (and (good-java-type typ icl)
                 (NOT (EQUAL '(CLASS "java.lang.Object") Typ)))
            (not (equal (name-of typ) "java.lang.Object")))
   :hints (("Goal" :in-theory (e/d (name-of isClassType) ())))))


(defthm java-lang-Object-subclass-of-nothing-but-java-lang-Object
  (implies (and (NOT (EQUAL '(CLASS "java.lang.Object") T3))
                (good-java-type t3 icl)
                (good-icl icl)
                (icl-scl-compatible icl scl))
           (not (isjavasubclassof "java.lang.Object" (NAME-OF T3) scl)))
  :hints (("Goal" :in-theory (e/d ()
                                  (icl-scl-compatible
                                   name-of
                                   isClassTerm
                                   good-icl))
           :expand (isjavasubclassof "java.lang.Object" (NAME-OF T3) scl))))


;;;
;;; maybe we just assert it (good-icl icl)
;;; 
;;; We know tha we can prove it from good-icl and icl-scl-compatible!  
;;; 
;;;
;;;
;;; because we can show that java.lang.Object is a super class of every thing. 
;;;
;;; We could simply add the assertion on the external class table 
;;;
;;; instead of relying on asserting there exists a icl that is compatible with
;;; the scl and that icl is good. 
;;;
;;;
;;; However then, we need run a test to assert that scl is well formed before
;;; BCV starts!! This is not what JVM is doing, where classes may be
;;; dynamically created!! 
;;; 
;;; IN JVM, we are relying on the dynamic class loading to discover problem at
;;; runtime!! 
;;;
;;; I seem to have do extra work to show that isjavasubclassof is transitive!! 
;;; 
;;; Wed Jul 13 16:13:46 2005



;; (skip-proofs 
;;  (defthm java-lang-Object-subclass-of-nothing-but-java-lang-Object
;;    (implies (and (NOT (EQUAL '(CLASS "java.lang.Object") T3))
;;                  (good-java-type t3 icl)
;;                  (good-icl icl)
;;                  (icl-scl-compatible icl scl))
;;             (not (isjavasubclassof "java.lang.Object" (NAME-OF T3) scl)))))


;;;
;;; we need extra assertion that if interface type, then 
;;; the superclass is "java.lang.Object" !!! 

(defthm jvm-wff-static-class-table-strong-implies-interface-type
  (implies (and (MEM '*INTERFACE* 
                     (jvm::accessflags-s 
                      (mv-nth 1 (jvm::class-by-name-s n scl))))
                (jvm::wff-static-class-table-strong scl))
           (equal (jvm::super-s (mv-nth 1 (jvm::class-by-name-s n scl)))
                  "java.lang.Object")))

;;; we don't have to add this assertion onto scl and check for that
;;;
;;; because we could conclude from this from the fact that 
;;; 
;;; there exists an icl and that in that icl all interfaces' super is
;;; java.lang.Object!! 
;;;

(defthm classisinterface-type-implies-mem-interface-flag
  (implies (classisinterface (class-by-name n (scl-jvm2bcv scl)))
           (mem '*interface* 
                (jvm::accessflags-s 
                 (mv-nth 1 (jvm::class-by-name-s n scl)))))
  :hints (("Goal" :in-theory (e/d (classisinterface
                                  jvm::classname-s
                                  scl-bcv2jvm
                                  CLASSACCESSFLAGS
                                  class-by-name
                                  make-class-term
                                  jvm::accessflags-s
                                  classclassname) ()))))

;; (i-am-here) ;;  Wed Jul 13 23:27:02 2005

(encapsulate ()
 (local
  (defthm classSuperClassname-equal-super-s
    (equal (classSuperClassname (class-by-name n (scl-jvm2bcv scl)))
           (jvm::super-s (mv-nth 1 (jvm::class-by-name-s n scl))))
    :hints (("Goal" :in-theory (e/d (classSuperClassname
                                     jvm::super-s
                                     jvm::classname-s
                                     make-class-term
                                     classclassname
                                     class-by-name))))))
                                
 (defthm icl-scl-compatible-and-interface-implies-java-lang-Object
   (implies (and (jvm::wff-static-class-table-strong scl)
                 (classisinterface (class-by-name t2 (scl-jvm2bcv scl))))
            (equal (classSuperClassName 
                    (class-by-name t2 (scl-jvm2bcv scl))) "java.lang.Object"))
   :hints (("Goal" :do-not '(generalize)
            :do-not-induct t
            :in-theory (disable scl-jvm2bcv)))))


(defthm interface-subclass-of-nothing-but-java-lang-Object
  (implies (and (NOT (EQUAL '(CLASS "java.lang.Object") T3))
                (good-icl icl)
                (good-java-type t3 icl)
                (not (equal (name-of t2) (name-of t3)))
                (classisinterface (class-by-name (name-of t2) scl))
                (icl-scl-compatible icl scl))
           (not (isjavasubclassof (name-of t2) (NAME-OF T3) scl)))
  :hints (("Goal" :in-theory (e/d (icl-scl-compatible) 
                                  (good-icl good-java-type))
           :expand (isjavasubclassof (name-of t2) (NAME-OF T3) scl)
           :use ((:instance
                  icl-scl-compatible-and-interface-implies-java-lang-Object
                  (scl (scl-bcv2jvm scl))
                  (t2 (name-of t2)))))))


;;
;; We do have a proof that any class in icl has a super class of 
;; java.lang.Object. Thu Jul 14 12:21:00 2005
;; 

(defthm superclass-no-loop1-superclass-no-loop1-super
  (implies (and (SUPERCLASS-NO-LOOP1 N SCL seen)
                (ISCLASSTERM (CLASS-BY-NAME N SCL)))
        (SUPERCLASS-NO-LOOP1 (CLASSSUPERCLASSNAME (CLASS-BY-NAME N SCL))
                             SCL (cons n seen))))
           

(defthm superclass-no-loop1-no-loop-cons
  (implies (SUPERCLASS-NO-LOOP1 N SCL (cons x seen))
           (SUPERCLASS-NO-LOOP1 n scl seen)))
                                

(defthm mem-collect-superclass-list1-implies-subclass
  (implies (and (mem x (collect-superclass-list1 n scl ss))
                (superclass-no-loop n scl))
           (isjavasubclassof n x scl))
  :hints (("Goal" :do-not '(generalize)
           :restrict ((superclass-no-loop1-no-loop-cons
                       ((x  n)))))))


(defthm mem-collect-superclass-list1-implies-subclass-specific
  (implies (and (mem x (collect-superclass-list1 n scl nil))
                (superclass-no-loop n scl))
           (isjavasubclassof n x scl))
  :hints (("Goal" :do-not '(generalize))))


(defthm class-table-is-loaded-from-implies-class-is-loaded-from
  (implies (and (jvm::class-table-is-loaded-from icl scl)
                (jvm::isclassterm (jvm::class-by-name n icl)))
           (jvm::class-is-loaded-from-helper (jvm::class-by-name n icl)
                                             (mv-nth 1 (jvm::class-by-name-s n
                                                                             scl))))
  :hints (("Goal" :in-theory (e/d (jvm::classname-s) ()))))


(defthm class-is-loaded-from-implies-name-matches
  (implies (jvm::class-is-loaded-from-helper class-rep class-static-rep)
           (equal (jvm::classSuperClassname class-rep)
                  (jvm::super-s class-static-rep)))
  :hints (("Goal" :in-theory (enable jvm::classSuperClassname))))


(encapsulate ()
  (local
   (defthm classSuperClassname-equal-super-s
     (equal (classSuperClassname (class-by-name n (scl-jvm2bcv scl)))
            (jvm::super-s (mv-nth 1 (jvm::class-by-name-s n scl))))
     :hints (("Goal" :in-theory (e/d (classSuperClassname
                                      jvm::super-s
                                      jvm::classname-s
                                      make-class-term
                                      classclassname
                                      class-by-name))))))

  (defthm collect-superclass-list1-djvm-collect-superclass-list-match-lemma
    (implies (and (jvm::class-table-is-loaded-from icl (scl-bcv2jvm scl))
                  (good-scl scl)
                  (jvm::isclassterm (jvm::class-by-name n icl)))
             (equal (classSuperClassname (class-by-name n scl))
                    (djvm::classSuperClassname 
                     (jvm::class-by-name n icl))))
    :hints (("Goal" :do-not '(generalize)
             :in-theory (e/d (jvm::super-s)
                             (djvm::classSuperClassname
                              jvm::isclassterm
                              jvm::class-is-loaded-from-helper))
             :restrict ((class-is-loaded-from-implies-name-matches
                         ((class-static-rep 
                           (mv-nth 1 (jvm::class-by-name-s 
                                      n 
                                      (scl-bcv2jvm scl)))))))))))



;; The following is a useful theorem!! 
;;
;; Thu Jul 14 16:04:43 2005. Don't have much time.... 

;; (i-am-here) ;; Thu Jul 14 16:44:30 2005

;; (skip-proofs
;;  (defthm skip-proofs-1
;;    (equal (NTH '2
;;               (MV-NTH '1 (JVM::CLASS-BY-NAME-S N scl)))
;;           n)))

(in-theory (disable class-exists-s-implies-bcv-is-class-term)) 



;; prove the following ;; Thu Jul 14 17:26:36 2005
;;
;; proved before somewhere!! 

(local 
 (defthm
   class-hierachy-consistent1-class-n-implies-not-java-lang-Object-super-bounded
   (implies 
    (and (jvm::class-hierachy-consistent1-class-n name cl)
         (not (equal name "java.lang.Object")))
    (jvm::isClassTerm (jvm::class-by-name (jvm::super (jvm::class-by-name name cl))
                                          cl)))
   :hints (("Goal" :in-theory (e/d (jvm::class-exists? jvm::class-loaded?) (jvm::isClassTerm))))))

(local 
 (defthm
   class-hierachy-consistent1-aux-implies-bounded-class-hierachy-consistent1-class-n
   (implies (and (jvm::class-hierachy-consistent1-aux cl1 cl)
                 (jvm::isClassTerm (jvm::class-by-name name cl1)))
            (jvm::class-hierachy-consistent1-class-n name cl))))

(defthm super-not-defined-then-java-lang-Object
  (implies (and (jvm::isclassterm (jvm::class-by-name n cl))
                (jvm::consistent-class-hierachy cl)
                (not (equal n "java.lang.Object")))
           (jvm::isclassterm (jvm::class-by-name 
                              (jvm::classSuperClassname 
                               (jvm::class-by-name n cl)) cl)))
  :hints (("Goal" :in-theory (e/d (jvm::classSuperClassname
                                   jvm::consistent-class-hierachy) 
                                  (jvm::super
                                   jvm::class-by-name
                                   jvm::isclassterm)))))


(defthm good-scl-implies-not-super-of-java-lang-Object-not-defined
  (implies (and (good-scl scl)
                (equal (classSuperClassname (class-by-name "java.lang.Object" scl))
                       n))
           (not (isclassterm (class-by-name n scl)))))


;;
;; the following is not straightforward. 
;;
;;
;; this it is not even true!! 
;; with out asserting something in SCL that 
;;
;; java.lang.Object does not has a "superclass"
;;

(defthm not-isClassTerm-icl-not-isClassTerm-scl-if-loaded
  (implies (and (good-icl icl)
                (good-scl scl)
                (jvm::class-table-is-loaded-from icl (scl-bcv2jvm scl))
                (jvm::isclassterm (jvm::class-by-name n icl))
                (NOT
                 (JVM::ISCLASSTERM
                  (JVM::CLASS-BY-NAME (JVM::CLASSSUPERCLASSNAME (JVM::CLASS-BY-NAME N ICL))
                                      ICL))))
           (not (isclassterm (class-by-name (JVM::CLASSSUPERCLASSNAME
                                             (JVM::CLASS-BY-NAME N ICL))
                                            scl))))
  :hints (("Goal" :cases ((equal n "java.lang.Object"))
           :in-theory (disable 
                       jvm::classsuperclassname
                       jvm::isclassterm))))
  
; Matt K. mod: Avoid raw Lisp error in tau due to the use of skip-proofs to
; guard verify some functions that aren't truly guard-verifiable:
; class-by-name, which tau was calling on an atomic classtable, 'JVM::ADDR; and
; good-scl, which tau was calling on (ARRAY BOOLEAN).
(local (in-theory (disable (:e tau-system))))

(defthm collect-superclass-list1-djvm-collect-superclass-list-match
  (implies (and (icl-scl-compatible icl scl)
                (good-icl icl)
                (jvm::isclassterm (jvm::class-by-name n icl)))
           (equal (collect-superclass-list1 n scl seen)
                  (djvm::collect-superclass-list1 n icl seen)))
  :hints (("Goal" :in-theory (e/d (class-by-name)
                                  (classSuperClassname
                                   good-icl
                                   good-scl
                                   CLASS-EXISTS-S-IMPLIES-BCV-IS-CLASS-TERM
                                   SUPERCLASS-NO-LOOP1
                                   jvm::super-s
                                   jvm::class-by-name
                                   jvm::isclassterm
                                   isclassterm
                                   jvm::class-table-is-loaded-from
                                   jvm::classSuperClassname
                                   CLASS-IS-LOADED-FROM-IMPLIES-NAME-MATCHES))
           :do-not '(generalize fertilize)
           :restrict ((COLLECT-SUPERCLASS-LIST1-DJVM-COLLECT-SUPERCLASS-LIST-MATCH-LEMMA
                       ((icl icl)))))
          ("Subgoal *1/3" :expand (JVM::COLLECT-SUPERCLASS-LIST1 N ICL SEEN))
          ("Subgoal *1/2" :expand (JVM::COLLECT-SUPERCLASS-LIST1 N ICL SEEN))))


;;; Thu Jul 14 17:06:24 2005
;;; 
;;; should be easy!! 
;----------------------------------------------------------------------


(defthm super-no-loop-no-loop
  (implies (and (jvm::class-table-is-loaded-from icl (scl-bcv2jvm scl))
                (jvm::SUPERCLASS-CHAIN-NO-LOOP-CLASS-N n icl seen)
                (good-scl scl)
                (jvm::isclassterm (jvm::class-by-name n icl))
                (jvm::class-hierachy-consistent1-aux icl icl))
           (superclass-no-loop1 n scl seen))
  :hints (("Goal" :do-not '(generalize fertilize)
           :in-theory (e/d (JVM::CLASSSUPERCLASSNAME) 
                           (jvm::isclassterm 
                            jvm::classSuperClassname
                            jvm::super
                            classSuperClassname)))
          ("Subgoal *1/6" :expand  (jvm::classSuperClassname
                                    (JVM::CLASS-BY-NAME N ICL)))
          ("Subgoal *1/5" :cases ((equal n "java.lang.Object")))
          ("Subgoal *1/5.1" :expand (superclass-no-loop1 "java.lang.Object" scl seen))))


(defthm class-hierachy2-class-n-implies-superclass-chain-no-loop
  (implies (and (jvm::class-hierachy-consistent2-aux cl1 cl)
                (jvm::isclassterm (jvm::class-by-name n cl1)))
           (jvm::superclass-chain-no-loop-class-n n cl nil)))
  

(defthm icl-scl-compatible-good-icl-implies-superclass-no-loop
   (implies (and (icl-scl-compatible icl scl)
                 (good-icl icl)
                 (good-scl scl)
                 (jvm::isclassterm (jvm::class-by-name n icl)))
            (superclass-no-loop1 n scl nil))
   :hints (("Goal" :do-not '(generalize fertilize)
            :in-theory (e/d (jvm::consistent-class-hierachy)
                            (jvm::isclassterm 
                             good-scl
                             superclass-no-loop1)))))


(defthm all-subclass-of-java-lang-Object-implies-mem
  (implies (and (all-subclass-of-java-lang-Object l  icl)
                (mem x l))
           (mem "java.lang.Object"
                (djvm::collect-superclass-list1 x icl nil))))

(defthm all-subclass-of-java-lang-Object-implies-mem-specific
  (implies (and (all-subclass-of-java-lang-Object (jvm::all-class-names icl)  icl)
                (mem x (jvm::all-class-names icl)))
           (mem "java.lang.Object"
                (djvm::collect-superclass-list1 x icl nil))))

(defthm isclassname-mem-x-all-classname
  (implies (jvm::isclassterm (jvm::class-by-name x icl))
           (mem x (jvm::all-class-names icl))))


(defthm everything-subclass-of-java-lang-Object
  (implies (and (good-icl icl)
                (isclasstype t1)
                (good-java-type t1 icl)
                (icl-scl-compatible icl scl))
           (isjavasubclassof (name-of t1) "java.lang.Object" scl))
  :hints (("Goal" 
           :in-theory (e/d (good-java-type isjavasubclassof) ())
           :restrict
           ((collect-superclass-list1-djvm-collect-superclass-list-match
             ((icl icl)))
            (icl-scl-compatible-good-icl-implies-superclass-no-loop
             ((icl icl)))))))
           
;;; because that we have a special object "java.lang.Object" 
;;; the test of isJavaAssignable follows a different path 
;;; when some object is "java.lang.object"

;; (skip-proofs 
;;  (defthm everything-subclass-of-java-lang-Object
;;    (implies (and (good-icl icl)
;;                  (isclasstype t1)
;;                  (good-java-type t1 icl)
;;                  (icl-scl-compatible icl scl))
;;             (isjavasubclassof (name-of t1) "java.lang.Object" scl))))
;;


(defthm isJavaAssignable-Transitive
   (implies (and  (good-java-type t1 icl)
                  (good-java-type t2 icl)
                  (good-java-type t3 icl)
                  (good-icl icl)
                  (good-scl scl)
                  (icl-scl-compatible icl scl)
                  (isJavaAssignable t1 t2 scl)
                  (isJavaAssignable t2 t3 scl))
            (isJavaAssignable  t1 t3 scl))
   :hints (("Goal" :do-not '(generalize fertilize)
            :in-theory (e/d () (good-java-type component-type 
                                good-scl   isArrayType good-icl)))
           ("Subgoal *1/5" :cases ((equal (name-of t3) (name-of t2))))
           ("Subgoal *1/2" :cases ((equal '(class "java.lang.Object") t3)))
           ("Subgoal *1/2.2" :cases ((equal (name-of t3) (name-of t2))))))


;;; At LAST !!! Thu Jul 14 21:13:05 2005
;;;
;;; Thu Jul 14 21:13:07 2005

;; (defun good-bcv-type (typ icl)
;;   (or (equal typ 'ONEWORD)
;;       (equal typ 'TWOWORD)
;;       (equal typ 'topx)
;;       (equal typ 'REFERENCE)
;;       (equal typ 'UNINITIALIZED)
;;       (equal typ 'UNINITIALIZEDTHIS)
;;       (good-java-type typ icl)))

(include-book "../BCV/bcv-functions")

(local (in-theory (disable classtableenvironment icl-scl-compatible good-icl good-scl)))

;; (skip-proofs 
;;  (defthm good-icl-not-java-assignable
;;    (implies (and (good-icl icl)
;;                  (not (good-java-type typ icl))
;;                  (icl-scl-compatible icl scl))
;;             (not (isJavaAssignable any typ scl)))))


;; (skip-proofs 
;;  (defthm good-icl-not-java-assignable-2
;;    (implies (and (good-icl icl)
;;                  (not (good-java-type typ icl))
;;                  (icl-scl-compatible icl scl))
;;             (not (isJavaAssignable typ any scl)))))



(defthm not-good-java-type-fact
  (not (good-java-type 'uninitializedthis icl)))

(defthm not-good-java-type-fact-2
  (not (good-java-type 'uninitialized icl)))

(defthm not-good-java-type-fact-3
  (not (good-java-type 'oneword icl)))

(defthm not-good-java-type-fact-4
  (not (good-java-type 'twoword icl)))



(defthm not-good-java-type-fact-5
  (not (good-java-type 'topx icl)))

(defthm not-good-java-type-fact-6
  (not (good-java-type 'reference icl)))

(local (in-theory (disable good-java-type)))

(defthm isJavaAssignable-not-class-type-not-arraytype
  (implies (and (not (isClassType typ))
                (not (isArrayType typ)))
           (not (isJavaAssignable any typ scl))))

(defthm isJavaAssignable-not-class-type-not-arraytype-2
  (implies (and (not (isClassType typ))
                (not (isArrayType typ)))
           (not (isJavaAssignable typ any scl))))


(defthm not-good-java-type-null
  (not (good-java-type 'null icl))
  :hints (("Goal" :in-theory (enable good-java-type))))



(defthm isAssignable-convertint
  (implies (isAssignable sT gT env)
           (isAssignable (convertIfInt sT) (convertIfInt gT) env)))

(defthm convertIfInt-fixed
  (equal (convertIfInt (convertIfInt x))
         (convertIfInt x)))

(defthm isAssignable-long-is-long
  (implies (isAssignable x 'LONG env)
           (equal x 'LONG))
  :rule-classes :forward-chaining)

(defthm isAssignable-double-is-double
  (implies (isAssignable x 'DOUBLE env)
           (equal x 'DOUBLE))
  :rule-classes :forward-chaining)

(defthm isAssignable-equal-equal
  (isAssignable x x env))

(defthm nothing-isAssignable-to-top
  (implies (not (equal any 'topx))
           (not (isAssignable 'topx any env))))




(defthm not-good-java-type
  (not (GOOD-JAVA-TYPE (CONS 'UNINITIALIZED T3)
                       ICL))
  :hints (("Goal" :in-theory (enable good-java-type isArrayType isClassType))))



(local 
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
                      (T NIL))))))))




(defthm isassignable-fact-1
  (implies (and (good-java-type t2 icl)
                (good-icl icl))
           (NOT (ISASSIGNABLE T2 'UNINITIALIZED ENV)))
  :hints (("Goal" :in-theory (enable good-java-type))))


;; (defthm isassignable-fact-2
;;   (implies (and (good-java-type t2 icl)
;;                 (good-icl icl))
;;            (NOT (ISASSIGNABLE T2 'TWOWORD ENV))))
;;; wrong!! 

(defthm isassignable-fact-2
   (implies (and (good-java-type t2 icl)
                 (not (equal t2 'LONG))
                 (not (equal t2 'DOUBLE))
                 (good-icl icl))
            (NOT (ISASSIGNABLE T2 'TWOWORD ENV))))

(defthm isassignable-fact-3
  (implies (and (good-java-type t2 icl)
                (good-icl icl))
           (NOT (ISASSIGNABLE T2 'UNINITIALIZEDTHIS
                              ENV))))


(skip-proofs 
 (defthm jvm-isclassterm-bcv-isclassterm
   (implies (and (JVM::ISCLASSTERM (JVM::CLASS-BY-NAME T4 ICL))
                 (GOOD-ICL ICL)
                 (GOOD-SCL SCL)
                 (ICL-SCL-COMPATIBLE ICL SCL))
            (ISCLASSTERM (CLASS-BY-NAME T4 SCL)))
   :hints (("Goal" :do-not '(generalize fertilize)))))

;;; this is such a basic result!! 


;;; we want this result, because we want the next one
;;; that assert that isassignable is equal to isJavaAssignable!! 


(defthm scl-decl-bcv2jvm-scl-decl-jvm2bcv-equal-implies-boolean
  (implies (equal (MAKE-CLASS-DEF (scl-decl-bcv2jvm class-rep)) classrep)
           (booleanp (classisinterface classrep)))
  :hints (("Goal" :in-theory (enable classisinterface make-class-term))))

;;; (i-am-here) ;; Fri Jul 15 02:19:37 2005

(defthm scl-decl-bcv2jvm-scl-decl-jvm2bcv-equal-implies-class-rep
  (implies (equal (MAKE-CLASS-DEF (scl-decl-bcv2jvm class-rep)) classrep)
           (isclassterm classrep)))


(defthm good-scl-all-isClassTerm
  (implies (and (good-scl scl)
                (consp scl))
           (isclassterm  (car scl)))
  :hints (("Goal" :in-theory (enable good-scl))))

;; to prove the following, we need something 


;; (defthm good-scl-implies-if-interface-type-boolean-weak
;;   (implies (and (equal (scl-jvm2bcv (scl-bcv2jvm scl)) scl)
;;                 (isclassterm (class-by-name n scl)))
;;            (booleanp (classisinterface (class-by-name n scl))))
;;   :hints (("Goal" :in-theory (e/d (class-by-name) (scl-decl-bcv2jvm 
;;                                                    classisinterface
;;                                                    make-class-def))
;;            :do-not '(generalize fertilize))))

(defthm good-scl-implies-if-interface-type-boolean
  (implies (equal (scl-jvm2bcv (scl-bcv2jvm scl)) scl)
           (booleanp (classisinterface (class-by-name n scl))))
  :hints (("Goal" :in-theory (e/d (class-by-name) (scl-decl-bcv2jvm 
                                                   classisinterface
                                                   make-class-def)))))

(defthm good-scl-implies-scl-jvm2bcv-scl-bcv2jvm-equal
   (implies (good-scl scl)
            (equal (scl-jvm2bcv (scl-bcv2jvm scl)) scl))
   :hints (("Goal" :in-theory (enable good-scl))))


(defthm good-scl-implies-classisinterface-t
  (implies (and  (CLASSISINTERFACE (CLASS-BY-NAME T4 SCL))
                 (GOOD-SCL SCL))
           (EQUAL (CLASSISINTERFACE (CLASS-BY-NAME T4 SCL))
                  T))
  :hints (("Goal" :do-not '(fertilize)
           :use ((:instance good-scl-implies-if-interface-type-boolean
                            (n t4)))
           :in-theory (disable jvm::isclassterm good-scl
                               classisinterface))))

;;(i-am-here) ;;Fri Jul 15 02:24:05 2005                               

(defthm isJavaAssignable-equal-equal
  (implies (and (good-java-type t1 icl)
                (not (jvm::primitive-type? t1))
                (good-icl icl)
                (good-scl scl)
                (icl-scl-compatible icl scl))
           (equal (isJavaAssignable t1 t1 scl) t))
  :hints (("Goal" :in-theory (e/d (jvm::primitive-type? name-of
                                   good-java-type isArrayType isclasstype)
                                  (jvm::isclassterm good-icl good-scl))
           :do-not '(generalize))))


;; note this is a stronger result than 
;;
;;
;; (defthm isJavaAssignable-equal-equal
;;   (implies (and (good-java-type t1 icl)
;;                 (not (jvm::primitive-type? t1))
;;                 (good-icl icl)
;;                 (good-scl scl)
;;                 (icl-scl-compatible icl scl))
;;           (isJavaAssignable t1 t1 scl))
;;   :hints (("Goal" :in-theory (e/d (jvm::primitive-type? name-of
;;                                    good-java-type isArrayType isclasstype)
;;                                   (jvm::isclassterm good-icl good-scl))
;;            :do-not '(generalize))))

(defthm not-good-java-type-uninitialized
  (not (GOOD-JAVA-TYPE (CONS 'UNINITIALIZED T4)
                       ICL))
  :hints (("Goal" :in-theory (enable good-java-type isclasstype isarraytype))))

(defthm isAssignable-reduced-to-isJavaAssignable
  (implies (and (good-java-type t1 icl)
                (not (jvm::primitive-type? t1))
                (good-java-type t2 icl)
                (not (jvm::primitive-type? t2))
                (good-icl icl)
                (good-scl (classtableenvironment env))
                (icl-scl-compatible icl (classtableenvironment env)))
           (equal (isAssignable t1 t2 env)
                  (isJavaAssignable t1 t2 (classtableenvironment env))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable good-scl)
           :restrict ((isJavaAssignable-equal-equal
                       ((icl icl)
                        (scl (classtableenvironment env))))))))

(defthm primitive-type-not-java-Assignable
  (implies (jvm::primitive-type? t2)
           (not (ISJAVAASSIGNABLE T1 T2 scl)))
  :hints (("Goal" :in-theory (enable isArrayType isclasstype jvm::primitive-type?))))


;; (defthm |Subgoal *1/11.5'|
;;   (IMPLIES (AND (NOT (EQUAL T1 T3))
;;               (NOT (EQUAL T1 'ONEWORD))
;;               (NOT (EQUAL T1 'TWOWORD))
;;               (NOT (EQUAL T1 'INT))
;;               (NOT (EQUAL T1 'FLOAT))
;;               (NOT (EQUAL T1 'LONG))
;;               (NOT (EQUAL T1 'DOUBLE))
;;               (NOT (EQUAL T1 'REFERENCE))
;;               (NOT (EQUAL 'UNINITIALIZED T1))
;;               (ISCLASSTYPE T1)
;;               (NOT (EQUAL 'REFERENCE T3))
;;               (NOT (EQUAL 'ONEWORD T3))
;;               (NOT (EQUAL T3 'topx))
;;               (GOOD-JAVA-TYPE T2 ICL)
;;               (GOOD-JAVA-TYPE T3 ICL)
;;               (NOT (EQUAL 'REFERENCE T2))
;;               (NOT (EQUAL 'ONEWORD T2))
;;               (NOT (EQUAL T2 'topx))
;;               (GOOD-JAVA-TYPE T1 ICL)
;;               (GOOD-ICL ICL)
;;               (ICL-SCL-COMPATIBLE ICL (CLASSTABLEENVIRONMENT ENV))
;;               (ISJAVAASSIGNABLE T1 T2 (CLASSTABLEENVIRONMENT ENV))
;;               (ISASSIGNABLE T2 T3 ENV))
;;          (ISJAVAASSIGNABLE T1 T3 (CLASSTABLEENVIRONMENT ENV))))

;(i-am-here)

;; the folllowing could be dealt with a rewrite rule that expands 
;;

;; (local 
;;  (defthm isassignable-null-fact-0
;;    (NOT (ISASSIGNABLE 'REFERENCE 'CHAR ENV))
;;    :hints (("Goal" :expand (ISASSIGNABLE 'REFERENCE 'CHAR ENV)))))

;; (local 
;;  (defthm isassignable-null-fact-0-0
;;    (NOT (ISASSIGNABLE 'REFERENCE 'BOOLEAN ENV))
;;    :hints (("Goal" :expand (ISASSIGNABLE 'REFERENCE 'BOOLEAN ENV)))))

;; (local 
;;  (defthm isassignable-null-fact-0-0-0
;;    (NOT (ISASSIGNABLE 'REFERENCE 'JVM::SHORT ENV))
;;    :hints (("Goal" :expand (ISASSIGNABLE 'REFERENCE 'JVM::SHORT ENV)))))

;; (local 
;;  (defthm isassignable-null-fact-0-0-0-0
;;    (NOT (ISASSIGNABLE 'REFERENCE 'FLOAT ENV))
;;    :hints (("Goal" :expand (ISASSIGNABLE 'REFERENCE 'FLOAT ENV)))))

;; (local 
;;  (defthm isassignable-null-fact-0-0-0-0-0
;;    (NOT (ISASSIGNABLE 'REFERENCE 'BYTE ENV))
;;    :hints (("Goal" :expand (ISASSIGNABLE 'REFERENCE 'BYTE ENV)))))

;; (local 
;;  (defthm isassignable-null-fact-0-0-0-0-0-0
;;    (NOT (ISASSIGNABLE 'REFERENCE 'LONG ENV))
;;    :hints (("Goal" :expand (ISASSIGNABLE 'REFERENCE 'LONG ENV)))))


;; (local 
;;  (defthm isassignable-null-fact-0-0-0-0-0-0-0
;;    (NOT (ISASSIGNABLE 'REFERENCE 'INT ENV))
;;    :hints (("Goal" :expand (ISASSIGNABLE 'REFERENCE 'INT ENV)))))


;; (local 
;;  (defthm isassignable-null-fact-0-0-0-0-0-0-0-0
;;    (NOT (ISASSIGNABLE 'REFERENCE 'DOUBLE ENV))
;;    :hints (("Goal" :expand (ISASSIGNABLE 'REFERENCE 'DOUBLE ENV)))))

;; (local 
;;  (defthm isassignable-null-fact-1
;;    (NOT (ISASSIGNABLE 'NULL 'CHAR ENV))
;;    :hints (("Goal" :expand (ISASSIGNABLE 'NULL 'CHAR ENV)))))




;; (local 
;;  (defthm isassignable-null-fact-2
;;    (NOT (ISASSIGNABLE 'NULL 'BOOLEAN ENV))
;;    :hints (("Goal" :expand (ISASSIGNABLE 'NULL 'BOOLEAN ENV)))))




;; (local 
;;  (defthm isassignable-null-fact-3
;;    (NOT (ISASSIGNABLE 'NULL 'JVM::SHORT ENV))
;;    :hints (("Goal" :expand (ISASSIGNABLE 'NULL 'JVM::SHORT ENV)))))


;; (local 
;;  (defthm isassignable-null-fact-4
;;    (NOT (ISASSIGNABLE 'NULL 'FLOAT ENV))
;;    :hints (("Goal" :expand (ISASSIGNABLE 'NULL 'FLOAT ENV)))))

;; (local 
;;  (defthm isassignable-null-fact-5
;;    (NOT (ISASSIGNABLE 'NULL 'BYTE ENV))
;;    :hints (("Goal" :expand (ISASSIGNABLE 'NULL 'BYTE ENV)))))

;; (local 
;;  (defthm isassignable-null-fact-6
;;    (NOT (ISASSIGNABLE 'NULL 'LONG ENV))
;;    :hints (("Goal" :expand (ISASSIGNABLE 'NULL 'LONG ENV)))))

;; (local 
;;  (defthm isassignable-null-fact-7
;;    (NOT (ISASSIGNABLE 'NULL 'INT ENV))
;;    :hints (("Goal" :expand (ISASSIGNABLE 'NULL 'INT ENV)))))

;; (defthm not-isAssignable-NULL
;;   (implies (jvm::primitive-type? typ)
;;            (not (ISASSIGNABLE 'NULL typ ENV)))
;;   :hints (("Goal" :in-theory (enable isassignable)
;;            :expand (ISASSIGNABLE 'NULL typ ENV))))

;;;
;;; replaced with isassignable-expander
;;;


(defthm not-isAssignable-UNINITIALIZEDTHIS
  (implies (jvm::primitive-type? typ)
           (not (ISASSIGNABLE 'UNINITIALIZEDTHIS typ ENV)))
  :hints (("Goal" :in-theory (enable isassignable)
           :expand (ISASSIGNABLE 'UNINITIALIZEDTHIS typ ENV))))
           
;; (skip-proofs 
;;  (defthm isassignable-NULL-fact-8
;;    (ISASSIGNABLE 'NULL 'ONEWORD ENV)))


;; (skip-proofs 
;;  (defthm isassignable-NULL-fact-9
;;    (ISASSIGNABLE 'NULL 'topx ENV)))

;; (skip-proofs 
;;  (defthm isassignable-NULL-fact-10
;;    (not (ISASSIGNABLE 'NULL 'UNINITIALIZED ENV))))

;; (skip-proofs 
;;  (defthm isassignable-NULL-fact-11
;;    (not (ISASSIGNABLE 'NULL 'UNINITIALIZEDTHIS ENV))))

;; (skip-proofs 
;;  (defthm isassignable-NULL-fact-12
;;    (not (ISASSIGNABLE 'NULL 'TWOWORD ENV))))


(defthm isassignable-uninitialized-any
  (implies (and (not (equal any 'uninitialized))
                (not (equal any 'uninitializedThis)) 
                ;; failed proof reveal the
                ;; additional constraints!! 
                (not (isuninitializedobject any)))   ;; 
           (NOT (ISASSIGNABLE any
                              'UNINITIALIZED
                              ENV)))
  :hints (("Goal" :in-theory (enable isclasstype isArrayType))))



(defthm isassignable-NULL-any
  (implies (not (equal any 'NULL))
           (NOT (ISASSIGNABLE any 'NULL ENV))))


(defthm isassignable-uninitializedthis-any
  (implies (not (equal any 'uninitializedThis))
           (NOT (ISASSIGNABLE any
                              'UNINITIALIZEDTHIS
                              ENV))))

;; (skip-proofs 
;;  (defthm isassignable-NULL-fact-13
;;    (ISASSIGNABLE 'NULL 'REFERENCE ENV)))


(defthm isassignable-reference-primitive-type
  (implies (jvm::primitive-type? any)
           (not (isassignable 'REFERENCE any env))))

(defthm good-java-type-primitive-type
  (implies (and (good-java-type typ icl)
                (not (isclasstype typ))
                (not (isArrayType typ)))
           (jvm::primitive-type? typ))
  :hints (("Goal" :in-theory (enable good-java-type)))
  :rule-classes :forward-chaining)
                     

(defthm good-java-type-not-NULL-assignable
  (implies (and (good-java-type typ icl)
                (ICL-SCL-COMPATIBLE ICL (CLASSTABLEENVIRONMENT ENV))
                (not (isclasstype typ))
                (not (isArrayType typ)))
           (not (ISASSIGNABLE 'NULL typ ENV)))
  :hints (("Goal" :cases ((jvm::primitive-type? typ))))
  :rule-classes :forward-chaining)

(defthm good-java-type-not-NULL-assignable-b
  (implies (and (good-java-type typ icl)
                (not (isclasstype typ))
                (not (isArrayType typ)))
           (not (ISASSIGNABLE 'NULL typ ENV)))
  :hints (("Goal" :expand (ISASSIGNABLE 'NULL typ ENV))))

(defthm not-primitive-type-primitive-type
  (implies (and (not (jvm::primitive-type? typ1))
                (jvm::primitive-type? typ2))
           (not (isassignable typ1 typ2 env))))

;; (i-am-here) ;; Fri Apr 29 17:07:10 2005
;; (defthm |Subgoal *1/20.2'|
;;   (IMPLIES
;;    (AND (NOT (EQUAL 'NULL T3))
;;         (NOT (ISCLASSTYPE T3))
;;           (NOT (ISARRAYTYPE T3))
;;           (CONSP (JVM::CLASS-BY-NAME "java.lang.Object" ICL))
;;           (NOT (EQUAL (LEN (CDR (JVM::CLASS-BY-NAME "java.lang.Object" ICL)))
;;                       11))
;;           (GOOD-JAVA-TYPE T2 ICL)
;;           (JVM::PRIMITIVE-TYPE? T3)
;;           (GOOD-ICL ICL)
;;           (ICL-SCL-COMPATIBLE ICL (CLASSTABLEENVIRONMENT ENV))
;;           (ISASSIGNABLE 'NULL T2 ENV))
;;      (NOT (ISASSIGNABLE T2 T3 ENV))))

;; Fri Jul 15 00:17:07 2005

(defthm good-icl-implies-good-java-type-java-lang-Object
  (implies (good-icl icl)
           (good-java-type '(class "java.lang.Object") icl))
  :hints (("Goal" :in-theory (enable good-java-type good-icl))))

;; (skip-proofs
;;  (defthm good-icl-implies-good-java-type-java-lang-Object
;;    (implies (good-icl icl)
;;             (good-java-type '(class "java.lang.Object") icl))))


(defthm not-long-not-double-then-not-assignable-to-twoword
  (implies (and (not (equal t2 'LONG))
                (not (equal t2 'DOUBLE))
                (not (equal t2 'twoword)))
         (NOT (ISASSIGNABLE T2 'TWOWORD ENV))))



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
           (isAssignable t1 t3 env))
  :hints (("Goal" :in-theory (e/d () (isjavaassignable good-scl jvm::primitive-type?))
           :do-not '(generalize fertilize))))



(defthm isArrayType-not-assignable-to-TWOWORD
  (implies (ISARRAYTYPE GT)
           (not (ISASSIGNABLE GT 'TWOWORD ENV))))


(defthm isClassType-not-assignable-to-TWOWORD
  (implies (ISCLASSTYPE GT)
           (not (ISASSIGNABLE GT 'TWOWORD ENV))))
