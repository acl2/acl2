(in-package "DJVM")
(include-book "../../M6-DJVM-shared/jvm-linker")
(include-book "../../M6-DJVM-shared/jvm-class-table")
(include-book "../../M6-DJVM-shared/jvm-object-type-hierachy")
(include-book "../../DJVM/consistent-state")


(local 
 (defthm searchfields-in-wff-class-fields
   (implies (and (wff-class-fields fields)
                 (searchfields field-ptr fields))
            (wff-field (searchfields field-ptr fields)))))


(local 
  (defthm consistent-state-wff-class-rep-strong-specific
    (implies (and (consistent-state s)
                  (class-by-name name (instance-class-table s)))
             (wff-class-rep-strong (class-by-name name (instance-class-table
                                                        s))))
    :hints (("Goal" :in-theory (e/d (wff-class-rep-strong) ())))))
 

(local 
 (defthm wff-class-fields-wff-class-rep-strong
   (implies (wff-class-rep-strong class-rep)
            (wff-class-fields (fields class-rep)))))

(local (in-theory (disable fields)))


(defthm consistent-state-field-found-wff-field-rep 
  (implies (and (consistent-state s)
                (lookupField field-ptr s))
           (wff-field (lookupField field-ptr s)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d () (wff-field 
                               consistent-state
                               fields)))))

;;;

(in-theory (disable wff-field))

(local 
 (in-theory (disable java-visible-portion field-classname
                     FIELDCP-TO-FIELD-PTR
                     field-fieldname
                     classname
                     binding bound?)))



(local 
 (defthm searchfields-found-correct-field
   (implies (searchfields field-ptr fields)
            (equal (field-fieldname (searchfields field-ptr fields))
                   (field-ptr-fieldname field-ptr)))))
 


(local (in-theory (disable obj-type)))



(local 
 (defthm consistent-fields-search-fields-implies-bound?
   (implies (and (consistent-fields fields field-decls cl hp)
                 (searchfields field-ptr field-decls))
            (bound? (field-ptr-fieldname field-ptr) fields))
   :hints (("Goal" :in-theory (enable field-ptr-fieldname field-fieldname bound?)))))
                    




(local 
 (defthm superclass-chain-no-loop-class-n-implies-superclass-no-loop1
   (implies (superclass-chain-no-loop-class-n any cl seen)
            (SUPERCLASS-NO-LOOP1 any cl seen))))


(local 
 (defthm class-hierachy-consistent-2-aux-implies-bound-superclass-chain-no-loop
   (implies (and (class-hierachy-consistent2-aux cl1 cl)
                 (class-by-name name cl1))
            (superclass-chain-no-loop-class-n name cl nil))
   :hints (("Goal" :in-theory (enable bound? classname)))))


(local 
 (defthm consistent-state-implies-superclass-no-loop
   (implies (consistent-state s)
            (SUPERCLASS-NO-LOOP1 any
                                 (INSTANCE-CLASS-TABLE S)
                                 nil))
   :hints (("Goal" 
            :in-theory (enable consistent-class-hierachy
                               class-hierachy-consistent2)
            :cases ((class-by-name any (instance-class-table s)))))))




(local 
  (defthm consistent-state-super-is-empty-implies-java-lang-Object
    (implies (and (consistent-state s)
                  (not (equal 
                        (super (class-by-name 
                                name 
                                (instance-class-table s))) "")))
             (not (equal name "java.lang.Object")))))


(local 
 (defun lookupfield-jvp-induct (field-ptr jvp s)
   (declare (xargs :measure
                   (lookupfield-measure field-ptr s)))
   (if (not (lookupfield-inv field-ptr s))
       (prog2$ (cw "lookupfield-inv violated~%")
               jvp)
     (mylet*
      ((classname (field-ptr-classname field-ptr))
       (class-rep
        (class-by-name classname
                       (instance-class-table s)))
       (super (super class-rep)))
      (if
          (not (isclassterm class-rep))
          nil
        (let
            ((field-rep (deref-field field-ptr s)))
          (if
              (not (equal field-rep nil))
              field-rep
            (if
                (equal super "")
                nil
              (lookupfield-jvp-induct
               (make-field-ptr super
                               (field-ptr-fieldname field-ptr)
                               (field-ptr-type field-ptr))
               (cdr jvp)
               s)))))))))


(local 
 (defthm bound?-bound?-cons
   (implies (bound? x alist)
            (bound? x (cons (cons key value) alist)))
   :hints (("Goal" :in-theory (enable bound?)))))
  

(local 
 (defthm searchFields-implies-equal-field-classname-equal
   (implies (searchFields field-ptr fields)
            (equal (field-classname (searchFields field-ptr fields))
                   (field-ptr-classname field-ptr)))))

(local 
 (defthm consistent-jvp-implies-bound?
   (implies (consistent-jvp name jvp cl hp)
            (bound? name jvp))
   :hints (("Goal" :in-theory (enable bound?)))))


(local 
 (defthm field-class-name-lookupfield-is-bounded
   (implies (and (consistent-state s)
                 (lookupField field-ptr s)
                 (consistent-jvp (field-ptr-classname field-ptr)
                                 jvp (instance-class-table s) (heap s)))
            (bound? (field-classname (lookupField field-ptr s))
                    jvp))
   :hints (("Goal" :do-not '(generalize)
            :in-theory (e/d () (consistent-state 
                                isClassTerm
                                class-exists?))
            :induct (lookupfield-jvp-induct field-ptr jvp s)))))


;;; field-classname ...
;;; ;;;



;;;
;;; now we showed that class name from lookup-field,  exists in the object
;;; we need to show that a field of that fieldname can in fact be found in 
;;;
;;; binding of that class name in the JVP!
;;;


;; Subgoal *1/3''
;; (IMPLIES
;;      (AND (CONSP JVP)
;;           (NOT (EQUAL ANY (CAAR JVP)))
;;           (NOT (CONSISTENT-JVP (SUPER (CLASS-BY-NAME "java.lang.Object" CL))
;;                                (CDR JVP)
;;                                CL HP))
;;           (CONSP (CAR JVP))
;;           (ALISTP (CDR JVP))
;;           (EQUAL (+ 1 (LEN (CDR JVP))) 1)
;;           (EQUAL NAME "java.lang.Object")
;;           (CONSISTENT-IMMEDIDATE-INSTANCE "java.lang.Object" (CAR JVP)
;;                                           CL HP)
;;           (ASSOC-EQUAL ANY (CDR JVP)))
;;      (CONSISTENT-FIELDS (CDR (ASSOC-EQUAL ANY (CDR JVP)))
;;                         (FIELDS (CLASS-BY-NAME ANY CL))
;;                         CL HP)).
;;
;;

(local 
 (defthm len-1-not-assoc-equal
   (implies (equal (len l) 1)
            (not (assoc-equal any (cdr l))))))


(local 
 (defthm consistent-immedidate-instance-implies-consistent-fields
   (implies (CONSISTENT-IMMEDIDATE-INSTANCE name name-and-fields CL HP)
            (consistent-fields (cdr name-and-fields)
                               (fields (class-by-name name cl))
                               cl hp))))

(local 
 (defthm consistent-immedidate-instance-implies-equal-caar
   (implies (CONSISTENT-IMMEDIDATE-INSTANCE name (CAR JVP)
                                            CL HP)
            (equal (caar jvp) name))))


(local 
 (defthm consistent-jvp-fields-field-decls-consistent
   (implies (and (consistent-jvp name jvp cl hp)
                 (bound? any jvp))
            (consistent-fields (binding any jvp)
                               (fields (class-by-name any cl))
                               cl
                               hp))
   :hints (("Goal" :in-theory (e/d (bound? binding)
                                   (consistent-immedidate-instance
                                    consistent-fields))))))


;; all we want consistent-fields
;;  is because we want to show that fields are in fact bounded!! 

;; (local 
;;  (defthm consistent-fields-search-fields-implies-bound?
;;    (implies (and (consistent-fields fields field-decls cl hp)
;;                  (searchfields field-ptr field-decls))
;;             (bound? (field-ptr-fieldname field-ptr) fields))
;;    :hints (("Goal" :in-theory (enable field-ptr-fieldname field-fieldname bound?)))))
;;
;; The second hyp                  (bound? any jvp)) here
;; will be relieved by                     
;;       field-class-name-lookupfield-is-bounded
;;


(defthm consistent-jvp-binding-alistp
  (implies (consistent-jvp name jvp cl hp)
           (alistp (binding any jvp)))
  :hints (("Goal" :in-theory (enable binding))))


;;; need expansion to consistent-jvp
;;;

;;
;; need to fix consistent-fields to make the above possible!! 
;; Thu Jun  9 13:33:15 2005. fixed. 

;; The following is still difficult!! 
;;

;; ;; (local 
;; ;;  (defthm field-class-name-lookupfield-is-bounded
;; ;;    (implies (and (consistent-state s)
;; ;;                  (lookupField field-ptr s)
;; ;;                  (consistent-jvp (field-ptr-classname field-ptr)
;; ;;                                  jvp (instance-class-table s) (heap s)))
;;;;;;;;;;;;;;;;;;;;;;;;  Here we expect a consistent-jvp from ptr-classname
;;;;;;;;;;;;;;;;;;;;;;;; 
;; ;;             (bound? (field-classname (lookupField field-ptr s))
;; ;;                     jvp))
;; ;;    :hints (("Goal" :do-not '(generalize)
;; ;;             :in-theory (e/d () (consistent-state 
;; ;;                                 isClassTerm
;; ;;                                 class-exists?))
;; ;;             :induct (lookupfield-jvp-induct field-ptr jvp s)))))
;;;;;
;;;;;
;;;;; In the real scenario, we have consistent-jvp from a name. 
;;;;; We know real (obj-type obj) is assignable to name!! 
;;;;; 
;;;;; We need the following theorem. 
;;;;;
;;;;; 
;;;;; 


(local 
 (defun get-jvp (name jvp)
   (if (not (consp jvp)) nil
     (if (not (consp (car jvp))) nil
       (if (equal (car (car jvp)) name) jvp
         (get-jvp name (cdr jvp)))))))


(local 
 (defthm isAssignable-consistent-jvp-consistent-jvp
   (implies (and (consistent-jvp name1 jvp1 (instance-class-table s)
                                 (heap s))
                 (car (isSuperClass1 name1 name2 s seen)))
            (consistent-jvp name2 (get-jvp name2 jvp1) 
                            (instance-class-table s)
                            (heap s)))
   :hints (("Goal" :in-theory (e/d () 
                                   (consistent-immedidate-instance))))))


;;;; Fri Jun 10 12:26:41 2005. Fri Jun 10 12:26:42 2005
;;;; 

(local 
 (defthm interface-loaded-from-wff-class-rep-static-strong-implies
   (implies (and (wff-class-rep-static-strong class-desc)
                 (class-is-loaded-from-helper class-rep class-desc)
                 (isInterface class-rep))
            (equal (super class-rep) "java.lang.Object"))
   :hints (("Goal" :in-theory (enable isInterface)))))
                 


(local 
 (defthm if-exists-then-loaded-from-some-class-file
   (implies (and (class-by-name name cl) 
                 (class-table-is-loaded-from cl scl))
            (class-is-loaded-from-helper 
             (class-by-name name cl)
             (mv-nth 1 (class-by-name-s name scl))))))

(local 
 (defthm consistent-state-implies-class-table-is-loaded-from
   (implies (consistent-state s)
            (class-table-is-loaded-from (instance-class-table s)
                                        (env-class-table (env s))))
   :hints (("Goal" :in-theory (enable consistent-state)))))


(local 
 (defthm
   wff-static-class-table-strong-implies-exists-implies-wff-static-class-rep-strong
   (implies (and (wff-static-class-table-strong scl)
                 (car (class-by-name-s name scl)))
            (wff-class-rep-static-strong (mv-nth 1 (class-by-name-s name
                                                                    scl))))
   :hints (("Goal" :in-theory (e/d () (wff-class-rep-static-strong))))))


(local 
 (defthm isInterface-implies-class-by-name
   (implies (isInterface (class-by-name name cl))
            (class-by-name name cl))
   :hints (("Goal" :in-theory (enable isInterface)))
   :rule-classes :forward-chaining))

(local 
 (defthm if-class-loaded-from-implies-car-class-by-name-s
   (implies (and (class-is-loaded-from-helper class-rep
                                              (mv-nth 1 (class-by-name-s name
                                                                         scl)))
                 (isInterface class-rep))
            (car (class-by-name-s name scl)))
   :hints (("Goal" :in-theory (enable isInterface)))))


(local 
 (defthm consistent-state-implies-wff-static-class-table-strong
   (implies (consistent-state s)
            (wff-static-class-table-strong (env-class-table (env s))))))


;;; Fri Jun 10 14:06:17 2005. 

;;;; don't care too much about the use hints now. 
;;;; this is a twisted proof anyway. 
;;;;

(local 
 (defthm consistent-state-implie-super-of-interface-is-java-lang-Object
   (implies (and (consistent-state s)
                 (isInterface (class-by-name name (instance-class-table s))))
            (equal (super (class-by-name name (instance-class-table s)))
                   "java.lang.Object"))
   :hints (("Goal" :in-theory (e/d () (consistent-state
                                       WFF-CLASS-REP-STATIC-STRONG
                                       JVM::WFF-STATIC-CP-OK-S))
            :use ((:instance 
                   interface-loaded-from-wff-class-rep-static-strong-implies
                   (class-rep  (class-by-name name (instance-class-table s)))
                   (class-desc (mv-nth 1 (class-by-name-s name (env-class-table
                                                                (env s))))))
                  (:instance if-class-loaded-from-implies-car-class-by-name-s
                             (class-rep (class-by-name name
                                                       (instance-class-table
                                                        s)))
                             (scl (env-class-table (env s)))))))))


;;;; we should be able to prove this .... 
;;;; However this may be an implementation specific detail not required of 
;;;; the JVM. 
;;;;
;;;; In fact, this is also independent of our proof (??)  No this is not
;;;; true. Our particular definition of of isAssignableTo has a short cut that
;;;; reject the possibility that some interface is assignable to some classs
;;;; other than "java.lang.Object"
;;;;
;;;; We may want to fix the isAssignableTo definition?? 
;;;; Fri Jun 10 12:32:36 2005

(local 
 (defthm consistent-state-implies-super-java-lang-Object-empty
   (implies (consistent-state s)
            (equal (super (class-by-name "java.lang.Object"
                                         (instance-class-table s)))
                   ""))))




(local 
 (defthm lookupfield-java-lang-Object-in-java-lang-Object
   (implies (and (consistent-state s)
                 (lookupfield (make-field-ptr "java.lang.Object" anyname anytype) s))
            (equal (field-classname (lookupfield (make-field-ptr
                                                  "java.lang.Object" anyname
                                                  anytype) s))
                   "java.lang.Object"))
   :hints (("Goal" :in-theory (e/d () (consistent-state))))))


                            

(local 
 (defthm consistent-class-decl-implies-not-field
   (implies (and (consistent-class-decl class-rep cl hp)
                 (isInterface class-rep))
            (equal (searchfields field-ptr (fields class-rep)) nil))))

(local 
 (defthm consistent-state-consistent-class-decls
   (implies (consistent-state s)
            (consistent-class-decls (instance-class-table s)
                                    (instance-class-table s)
                                    (heap s)))))


(local 
 (defthm consistent-class-decls-bound?-implies-consistent-class-decl
   (implies (and (consistent-class-decls cl1 cl hp)
                 (class-by-name name cl1))
            (consistent-class-decl (class-by-name name cl1) cl hp))
   :hints (("Goal" :in-theory (disable consistent-class-decl)))))
 
(local 
 (defthm not-class-by-name-not-interface
   (implies (not (class-by-name name cl1))
            (not (isInterface (class-by-name name cl1))))))


(local 
 (defthm consistent-state-isInterface-implies-consistent-class-decl
   (implies (and (consistent-state s)
                 (isInterface (class-by-name name (instance-class-table s))))
            (consistent-class-decl (class-by-name name (instance-class-table
                                                        s))
                                   (instance-class-table s)
                                   (heap s)))
   :hints (("Goal" :in-theory (e/d () (consistent-state 
                                       consistent-class-decl isInterface))
            :cases ((class-by-name name (instance-class-table s)))))))


(local 
 (defthm consistent-class-decl-implies-not-field-specific
   (implies (and (consistent-state s)
                 (isInterface (class-by-name (field-ptr-classname field-ptr) (instance-class-table s))))
            (equal (searchfields field-ptr (fields (class-by-name
                                                    (field-ptr-classname
                                                     field-ptr)
                                                    (instance-class-table s))))
                   nil))
   :hints (("Goal" :in-theory (e/d () (consistent-state consistent-class-decl))
            :use ((:instance consistent-class-decl-implies-not-field
                             (class-rep (class-by-name (field-ptr-classname
                                                        field-ptr)
                                                       (instance-class-table
                                                        s)))
                             (cl (instance-class-table s))
                             (hp (heap s))))))))


(local 
 (defthm lookupfield-in-interface-resulting-in-java-lang-Object
   (implies (and (consistent-state s)
                 (lookupfield field-ptr s)
                 (isInterface (class-by-name (field-ptr-classname field-ptr)
                                             (instance-class-table s))))
            (equal (field-classname (lookupfield field-ptr s))
                   "java.lang.Object"))
   :hints (("Goal" :do-not '(generalize)
            :in-theory (e/d () (consistent-state
                                isClassTerm))))))


(local 
 (defthm lookupfield-implies-not-interface
   (implies (and (consistent-state s)
                 (lookupfield field-ptr s)
                 ;; the following assertion added. 
                 (not (equal (field-classname (lookupfield field-ptr s))
                             "java.lang.Object")))
            (not (isInterface (class-by-name (field-ptr-classname field-ptr)
                                             (instance-class-table s)))))
   :hints (("Goal" :in-theory (e/d () (consistent-state))))))





;;;; which we know java.lang.Object is a super of every possible class...


;;; Originally, we miss the hyps that 
;;;;
;;;;  (equal (field-classname (lookupfield field-ptr s))
;;;;         "java.lang.Object")
;;;;
;;; this depends on the fact the java.lang.Object does not has any field!! 
;;; Thu Jun  9 19:03:11 2005
;;; 

(local 
 (defthm consistent-state-implies-interface-only-assignable-to
   (implies (and (not (equal name2 "java.lang.Object"))
                 (not (equal name1 name2))
                 (ISINTERFACE (CLASS-BY-NAME NAME1 (INSTANCE-CLASS-TABLE S)))
                 (consistent-state s))
            (not (car (isSuperClass1 name1 name2 s nil))))
   :hints (("Goal" :in-theory (e/d () (consistent-state))
            :expand (isSuperClass1 name1 name2 s nil)))))


(local 
 (defthm not-array-not-assignable-to-array
   (implies (and (not (isArrayType name1))
                 (isArrayType name2)
                 (consistent-state s))
            (not (car (isAssignableTo name1 name2 s))))
   :hints (("Goal" :in-theory (e/d () (consistent-state))))))



(local 
 (defthm
   class-hierachy-consistent1-class-n-implies-not-java-lang-Object-super-bounded
   (implies 
    (and (class-hierachy-consistent1-class-n name cl)
         (not (equal name "java.lang.Object")))
    (isClassTerm (class-by-name (super (class-by-name name cl))
                                       cl)))
   :hints (("Goal" :in-theory (disable isClassTerm)))))

(local 
 (defthm
   class-hierachy-consistent1-aux-implies-bounded-class-hierachy-consistent1-class-n
   (implies (and (class-hierachy-consistent1-aux cl1 cl)
                 (isClassTerm (class-by-name name cl1)))
            (class-hierachy-consistent1-class-n name cl))))


(local 
 (defthm consistent-state-implies-class-hierachy-consistent1-aux
   (implies (consistent-state s)
            (class-hierachy-consistent1-aux (instance-class-table s)
                                            (instance-class-table s)))
   :hints (("Goal" :in-theory (enable consistent-class-hierachy)))))





(local 
 (defthm consistent-state-implies-not-equal-java-lang-Object-super-bounded
   (implies (and (consistent-state s)
                 (not (equal name "java.lang.Object"))
                 (isClassTerm (class-by-name name (instance-class-table s))))
            (isClassTerm (class-by-name (super (class-by-name name
                                                              (instance-class-table s)))
                                        (instance-class-table s))))
   :hints (("Goal" :in-theory (e/d (consistent-class-hierachy)
                                   (class-hierachy-consistent1-class-n
                                    consistent-state
                                    isClassTerm))
            :use ((:instance
                   class-hierachy-consistent1-aux-implies-bounded-class-hierachy-consistent1-class-n
                   (cl1 (instance-class-table s))
                   (cl (instance-class-table s))))))))





;;;
;;; should be facts about consistent-class-hierachy ... 
;;;


(local 
 (defthm not-loaded-isSuperClass-of
   (implies (and (not (isClassTerm (class-by-name name (instance-class-table
                                                        s))))
                 (not (equal name "java.lang.Object"))
                 (not (equal name1 name))
                 (consistent-state s))
            (not (car (isSuperClass1 name1 name s seen))))
   :hints (("Goal" :in-theory (e/d (class-loaded?) (isClassTerm consistent-state))))))


(local 
 (defthm consistent-class-decls-implies-not-string-not-bound
   (implies (and (consistent-class-decls cl1 cl hp)
                 (not (stringp name)))
            (not (class-by-name name cl1)))
   :hints (("Goal" :in-theory (e/d (classname) 
                                   (wff-class-rep-strongx))))))
                                      
                                       
(local 
 (defthm consistent-state-impies-array-type-not-loaded-in-instance-table
   (implies (and (consistent-state s)
                 (isArrayType name2))
            (not (isClassTerm (class-by-name name2 (instance-class-table s)))))
   :hints (("Goal" :in-theory (e/d (consistent-state)
                                   ())
            :use ((:instance
                   consistent-class-decls-implies-not-string-not-bound
                   (cl1 (instance-class-table s))
                   (cl (instance-class-table s))
                   (name name2)
                   (hp (heap s))))))))





(local 
 (defthm consistent-state-not-isSuperClass-Array
   (implies (and (not (equal name1 name2))
                 (consistent-state s)
                 (isArrayType name2))
            (NOT (CAR (ISSUPERCLASS1 NAME1 name2
                                     S NIL))))
   :hints (("Goal" :in-theory (e/d () (consistent-state isClassTerm))))))



(local 
 (defthm not-interface-implies-isAssignable-reduce-to-isSuperClass
   (implies (and (not (isInterface (class-by-name name2 (instance-class-table
                                                         s))))
                 (not (equal name1 name2))
                 (not (equal name2 "java.lang.Object"))
                 (consistent-state s)
                 (not (primitive-type? name1))
                 (not (isArrayType name1)))
            (equal (car (isAssignableTo name1 name2 s))
                   (car (isSuperClass1 name1 name2 s nil))))
   :hints (("Goal" :in-theory (e/d () (primitive-type?
                                       consistent-state
                                       isSuperClass1))))))

;;; the problem is that isSuperClass1 check no-fatal-error?...
;;; and isAssignableTo don't on some corner cases. 



;;; not a trivial proof. Should be correct. Thu Jun  9 15:55:25 2005
;;;
;;; need a separate book? 



(local 
 (defthm lookupfield-implies-not-interface-specific
   (implies (and (consistent-state s)
                 (lookupfield (fieldcp-to-field-ptr fieldcp) s)
                 (not (equal (field-classname 
                              (lookupfield (fieldcp-to-field-ptr
                                            fieldcp) s))
                             "java.lang.Object")))
            (not (isInterface (class-by-name (fieldCP-classname fieldcp)
                                             (instance-class-table s)))))
   :hints (("Goal" :in-theory (e/d (fieldcp-to-field-ptr
                                    make-field-ptr
                                    field-ptr-classname)
                                   (consistent-state))
            :use ((:instance lookupfield-implies-not-interface
                             (field-ptr (fieldcp-to-field-ptr fieldcp))))))))

(local 
 (defthm consistent-jvp-bound?-java-lang-Object
   (implies (consistent-jvp name jvp cl hp)
            (bound? "java.lang.Object" jvp))
   :hints (("Goal" :in-theory (enable bound?)))))



;; (local 
;;  (defthm field-fieldname-search-fields
;;    (implies (searchfields field-ptr fields)
;;             (equal (field-fieldname (searchfields field-ptr fields))
;;                    (field-ptr-fieldname field-ptr)))))


(local 
 (defthm field-fieldname-reduce
   (implies (LOOKUPFIELD field-ptr s)
            (equal (FIELD-FIELDNAME (LOOKUPFIELD field-ptr s))
                   (field-ptr-fieldname field-ptr)))
   :hints (("Goal" :in-theory (e/d () (LOOKUPFIELD-INV
                                       searchfields 
                                       consistent-state
                                       field-fieldname 
                                       isClassTerm
                                       superclass-no-loop))
            :do-not '(generalize)))))


;;; diverged too much without disable consistent-state
;;;

;; 1. Simplifying the clause
;;      ((NOT (LOOKUPFIELD FIELD-PTR S))
;;       (EQUAL (FIELD-FIELDNAME (LOOKUPFIELD FIELD-PTR S))
;;              (FIELD-PTR-FIELDNAME FIELD-PTR)))
;; 2. Rewriting (to simplify) the atom of the first literal,
;;      (LOOKUPFIELD FIELD-PTR S),
;; 3. Attempting to apply (:DEFINITION LOOKUPFIELD) to
;;      (LOOKUPFIELD FIELD-PTR S)
;; 4. Rewriting (to simplify) the body,
;;      (IF (LOOKUPFIELD-INV JVM::FIELD-PTR JVM::S)
;;          (IF (ISCLASSTERM #)
;;              (# # JVM::S JVM::FIELD-PTR)
;;              'NIL)
;;          'NIL),
;;    under the substitution
;;      JVM::S : S
;;      JVM::FIELD-PTR : FIELD-PTR
;; 5. Rewriting (to simplify) the second argument,
;;      (IF (ISCLASSTERM (CLASS-BY-NAME # #))
;;          ((LAMBDA # #)
;;           (DEREF-FIELD JVM::FIELD-PTR JVM::S)
;;           JVM::S JVM::FIELD-PTR)
;;          'NIL),
;;    under the substitution
;;      JVM::S : S
;;      JVM::FIELD-PTR : FIELD-PTR
;; 6. Rewriting (to simplify) the first argument,
;;      (ISCLASSTERM (CLASS-BY-NAME (FIELD-PTR-CLASSNAME JVM::FIELD-PTR)
;;                                  (INSTANCE-CLASS-TABLE JVM::S))),
;;    under the substitution
;;      JVM::S : S
;;      JVM::FIELD-PTR : FIELD-PTR
;; 7. Attempting to apply (:REWRITE 
;;                         CONSISTENT-STATE-IMPIES-ARRAY-TYPE-NOT-LOADED-IN-INSTANCE-TABLE)
;; to
;;      (ISCLASSTERM (CLASS-BY-NAME (FIELD-PTR-CLASSNAME FIELD-PTR)
;;                                  (INSTANCE-CLASS-TABLE S)))
;; 8. Rewriting (to establish) the atom of the first hypothesis,
;;      (CONSISTENT-STATE S),
;;    under the substitution
;;      S : S
;;      NAME2 : (FIELD-PTR-CLASSNAME FIELD-PTR)
;; 9. Attempting to apply (:DEFINITION CONSISTENT-STATE) to


;; (local 

;;  (defthm field-fieldname-reduce
;;    (implies (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR FIELDCP) s)
;;             (equal (FIELD-FIELDNAME (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR FIELDCP) s))
;;                    (fieldcp-fieldname fieldcp)))))


;; (local 
;;  (defthm field-fieldname-reduce2
;;    (implies (searchfields (fieldcp-to-field-ptr fieldcp) fields)
;;             (equal (FIELD-FIELDNAME (searchfields (fieldcp-to-field-ptr
;;                                                    fieldcp) fields))
;;                    (fieldcp-fieldname fieldcp))))))


(defthm reduce-field-ptr-field-name
  (equal (FIELD-PTR-FIELDNAME (FIELDCP-TO-FIELD-PTR FIELDCP))
         (fieldcp-fieldname fieldcp))
  :hints (("Goal" :in-theory (enable fieldcp-fieldname field-ptr-fieldname
                                     make-field-ptr
                                     fieldcp-to-field-ptr))))



;; (local 
;;  (defthm consistent-fields-search-fields-implies-bound?
;;    (implies (and (consistent-fields fields field-decls cl hp)
;;                  (searchfields field-ptr field-decls))
;;             (bound? (field-ptr-fieldname field-ptr) fields))
;;    :hints (("Goal" :in-theory (enable field-ptr-fieldname field-fieldname bound?)))))

(include-book "base-bind-free")


;;; need rework!!! 
;;; Thu Jun  9 21:47:15 2005
;;; 

;; (local 
;;  (defthm consistent-fields-search-fields-implies-bound?-specific
;;    (implies (and (consistent-fields fields field-decls cl hp)
;;                  (searchfields (fieldcp-to-field-ptr fieldcp) field-decls))
;;             (bound? (fieldcp-fieldname fieldcp) fields))
;;    :hints (("Goal" :in-theory (e/d (field-ptr-fieldname 
;;                                     fieldcp-fieldname
;;                                     field-fieldname
;;                                     make-field-ptr
;;                                     bound?) ())
;;             :use ((:instance consistent-fields-search-fields-implies-bound?
;;                              (field-ptr (fieldcp-to-field-ptr fieldcp))))))))


(local 
 (defthm consistent-fields-search-fields-implies-bound?-specific-further
   (implies (and (bind-free (acl2::default-bind-free 's 's (acl2::pkg-witness "DJVM")))
                 (consistent-fields (binding name jvp)
                                    (fields 
                                     (class-by-name name (instance-class-table s)))
                                    (instance-class-table s)
                                    (heap s))
                 (searchfields (make-field-ptr
                                   name
                                   (fieldcp-fieldname fieldcp)
                                   (fieldcp-fieldtype fieldcp))
                               (fields
                                (class-by-name name (instance-class-table s)))))
            (bound? (fieldcp-fieldname fieldcp) (binding name jvp)))
   :hints (("Goal" :in-theory (e/d (make-field-ptr
                                    field-ptr-fieldname)
                                   (searchfields consistent-fields))
            :use ((:instance
                   consistent-fields-search-fields-implies-bound?
                   (cl (instance-class-table s))
                   (hp (heap s))
                   (fields (binding name jvp))
                   (field-decls  (fields 
                                    (class-by-name name (instance-class-table
                                                         s))))
                   (field-ptr 
                    (make-field-ptr
                     name
                     (fieldcp-fieldname fieldcp)
                     (fieldcp-fieldtype fieldcp)))))))))


(local 
 (defthm search-fields-normalize-ptr-no-change
   (equal (searchfields (make-field-ptr (field-ptr-classname field-ptr)
                                         (field-ptr-fieldname field-ptr)
                                         (field-ptr-type field-ptr))
                         fields)
          (searchfields field-ptr 
                        fields))))


(local 
  (defthm lookupfield-found-in-fact-found
    (implies (and (lookupfield field-ptr s)
                  (equal (field-ptr-fieldname field-ptr) fieldname)
                  (equal (field-ptr-type field-ptr) fieldtype))
             (equal (searchfields (make-field-ptr 
                                   (field-classname (lookupfield field-ptr s))
                                   fieldname
                                   fieldtype)
                                  (fields (class-by-name 
                                           (field-classname 
                                            (lookupfield field-ptr s))
                                           (instance-class-table s))))
                    (lookupfield field-ptr s)))
    :hints (("Goal" :in-theory (e/d () (consistent-state
                                        searchfields))
             :do-not '(generalize)))))


;; (local 
;;  (defthm lookupfield-found-in-fact-found
;;    (implies (lookupfield field-ptr s)
;;             (equal (searchfields field-ptr 
;;                                  (fields (class-by-name 
;;                                           (field-classname 
;;                                            (lookupfield field-ptr s))
;;                                           (instance-class-table s))))
;;                    (lookupfield field-ptr s)))
;;    :hints (("Goal" :in-theory (e/d () (consistent-state
;;                                        searchfields))
;;             :do-not '(generalize)))))


;;;
;;; this is wrong!! 
;;;


(local 
 (defthm lookupfield-found-in-fact-found-addition
   (implies (and (lookupfield field-ptr s)
                 (equal (field-classname (lookupfield field-ptr s)) 
                        "java.lang.Object")
                 (equal (field-ptr-fieldname field-ptr) fieldname)
                 (equal (field-ptr-type field-ptr) fieldtype))
            (equal (searchfields (make-field-ptr 
                                  "java.lang.Object" 
                                  fieldname
                                  fieldtype)
                                 (fields (class-by-name 
                                          "java.lang.Object"
                                          (instance-class-table s))))
                   (lookupfield field-ptr s)))
   :hints (("Goal" :use lookupfield-found-in-fact-found))))







;; field-class-name-lookupfield-is-bounded

(local 
 (defthm bound?-bound-get-jvp
   (implies (bound? name (get-jvp any jvp))
            (bound? name jvp))
   :hints (("Goal" :in-theory (enable bound?)))))


(local 
 (defthm field-class-name-lookupfield-is-bounded-general
   (implies (and (consistent-state s)
                 (lookupField field-ptr s)
                 (consistent-jvp (field-ptr-classname field-ptr)
                                 (get-jvp (field-ptr-classname field-ptr) jvp)
                                 (instance-class-table s) (heap s)))
            (bound? (field-classname (lookupField field-ptr s))
                    jvp))
   :hints (("Goal" :do-not '(generalize)
            :in-theory nil
            :use ((:instance field-class-name-lookupfield-is-bounded
                             (jvp (get-jvp (field-ptr-classname field-ptr)
                                           jvp)))
                  (:instance bound?-bound-get-jvp
                             (name (field-classname (lookupField field-ptr s)))
                             (any (field-ptr-classname field-ptr))))))))

(local 
 (defthm isAssignable-consistent-jvp-consistent-jvp-specific
  (implies (and (consistent-jvp (obj-type obj) (java-visible-portion obj) (instance-class-table s)
                                (heap s))
                (car (isSuperClass1 (obj-type obj) name2 s nil)))
           (consistent-jvp name2 (get-jvp name2 (java-visible-portion obj))
                           (instance-class-table s)
                           (heap s)))
  :hints (("Goal" :use ((:instance isAssignable-consistent-jvp-consistent-jvp
                                   (name1 (obj-type obj))
                                   (jvp1 (java-visible-portion obj))
                                   (seen nil)))))))
                            

(defthm field-ptr-classname-reduce
   (equal (FIELD-PTR-CLASSNAME (FIELDCP-TO-FIELD-PTR FIELDCP))
          (fieldcp-classname fieldcp))
   :hints (("Goal" :in-theory (enable fieldcp-classname
                                      fieldcp-to-field-ptr))))



(defthm field-ptr-fieldname-reduce
  (equal (field-ptr-fieldname (FIELDCP-TO-FIELD-PTR FIELDCP))
         (fieldcp-fieldname fieldcp))
  :hints (("Goal" :in-theory (enable fieldcp-classname fieldcp-to-field-ptr))))


(defthm field-ptr-fieldtype-reduce
  (equal (field-ptr-type (FIELDCP-TO-FIELD-PTR FIELDCP))
         (fieldcp-fieldtype fieldcp))
  :hints (("Goal" :in-theory (enable fieldcp-classname fieldcp-to-field-ptr))))


(local 
 (defthm java-lang-Object-lookup-field-if-found-then-found-in-java-lang-Object
   (implies (and (consistent-state s)
                 (EQUAL (FIELDCP-CLASSNAME FIELDCP)
                        "java.lang.Object")
                 (lookupField (FIELDCP-TO-FIELD-PTR FIELDCP) s))
            (EQUAL (FIELD-CLASSNAME (lookupField (FIELDCP-TO-FIELD-PTR FIELDCP) s))
                   "java.lang.Object"))
   :hints (("Goal" :in-theory (e/d () (consistent-state))))))

;;; do not export this!!! 

;; (i-am-here) ;; Mon Jun 13 18:50:12 2005



(local 
 (defthm wff-obj-strong-java-visible-portion-alistp
   (implies (WFF-OBJ-STRONG OBJ)
            (alistp (java-visible-portion obj)))
   :hints (("Goal" :in-theory (enable wff-obj-strong)))))


;; (i-am-here)

(local 
 (defthm
   consistent-object-and-field-found-in-lookup-implies-jvm-field-access-guard-lemma
   (implies (and (consistent-state s)
                 (consistent-object obj (heap s) (instance-class-table s))
                 (not (isArrayType (obj-type obj)))
                ;; need to strengthen GUARD 
                ;; and check for GETFIELD ;; Thu Jun  9 15:43:06 2005
                ;; done!! 
                (car (isAssignableTo (obj-type obj) (fieldCP-classname fieldcp) s))
                (lookupField (fieldcp-to-field-ptr fieldCP) s))
           (jvm::jvp-access-field-guard (field-classname 
                                         (lookupField (fieldcp-to-field-ptr
                                                       fieldCP) s))
                                        (FIELD-FIELDNAME
                                         (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR
                                                       fieldcp) s))
                                        (java-visible-portion obj)))
  :hints (("Goal" :in-theory (e/d (consistent-object
                                   jvm::jvp-access-field-guard) 
                                  (consistent-state
                                   lookupfield
                                   field-ptr-fieldname
                                   field-ptr-classname
                                   field-ptr-type
                                   fieldcp-fieldtype
                                   fieldcp-fieldname
                                   isAssignableTo
                                   isClassTerm
                                   fieldcp-classname
                                   ))
           :cases ((equal (field-classname (lookupfield 
                                            (fieldcp-to-field-ptr fieldCP) s))
                          "java.lang.Object")))
          ("Subgoal 2" :cases ((equal (obj-type obj)
                                      (fieldcp-classname fieldcp))
                               (equal (fieldcp-classname fieldcp) "java.lang.Object"))))))
                                    



(local 
 (defthm consistent-array-object-implies-consistent-jvp-java-lang-Object
   (implies (consistent-array-object obj hp cl acl)
            (consistent-jvp "java.lang.Object" (java-visible-portion obj) cl
                            hp))
   :rule-classes :forward-chaining))


(local 
 (defthm consistent-jvp-implies-bound-specific
   (implies (consistent-jvp type jvp cl hp)
            (bound? type jvp))
   :rule-classes :forward-chaining))

(local 
 (defthm consistent-array-object-bound-java-lang-Object
   (implies (consistent-array-object obj (heap s) (instance-class-table s) 
                                     (array-class-table s))
            (bound? "java.lang.Object" (java-visible-portion obj)))
   :hints (("Goal" :in-theory (disable consistent-jvp
                                       consistent-array-object)))))


                                       

;;; this above tooks Time:  
;;; 71.64 seconds (prove: 71.64, print: 0.00, other: 0.00)
;;; by simplification!! 


;; consistent-jvp-binding-alistp

(local 
 (defthm consistent-jvp-binding-alistp-specific
   (implies (and (bind-free (acl2::default-bind-free 's 's (acl2::pkg-witness "DJVM")))
                 (consistent-jvp any jvp (instance-class-table s) (heap s)))
            (alistp (binding any jvp)))
   :hints (("Goal" :use ((:instance consistent-jvp-binding-alistp 
                                    (cl (instance-class-table s))
                                    (hp (heap s))
                                    (name any)))))))




(local 
 (defthm consistent-jvp-fields-field-decls-consistent-specific
   (implies (and (consistent-jvp any jvp cl hp)
                 (bound? any jvp))
            (consistent-fields (binding any jvp)
                               (fields (class-by-name any cl))
                               cl
                               hp))
   :hints (("Goal" :use ((:instance
                          consistent-jvp-fields-field-decls-consistent
                          (name "java.lang.Object")))))))


(local 
 (defthm consistent-state-ipmlies-consistent-heap2
   (implies (consistent-state s)
            (consistent-heap2 (heap s) (heap s)
                              (instance-class-table s)
                              (array-class-table s) 0))))


(defthm consistent-heap2-implies-isArrayType-is-consistent-array-object
  (implies (and (consistent-heap2 hp1 hp cl acl id)
                (isArrayType (obj-type (binding v hp1))))
           (consistent-array-object (binding v hp1) hp cl acl))
  :hints (("Goal" :in-theory (e/d (binding)
                              (consistent-array-object)))))

(defthm isArrayType-implies-consistent-array-object-strong
  (implies (and (consistent-state s)
                (isArrayType (obj-type (deref2 v (heap s)))))
           (consistent-array-object (deref2 v (heap s))
                                    (heap s) (instance-class-table s)
                                    (array-class-table s)))
  :hints (("Goal" :in-theory (e/d (deref2 
                                   consistent-heap consistent-heap)
                                  (consistent-array-object
                                   obj-type
                                   isArrayType
                                   consistent-heap2-implies-isArrayType-is-consistent-array-object
                                   consistent-state
                                   binding
                                   nullp))
           :use ((:instance
                  consistent-heap2-implies-isArrayType-is-consistent-array-object
                  (hp1 (heap s)) 
                  (hp (heap s))
                  (v (cdr v))
                  (cl (instance-class-table s))
                  (acl (array-class-table s))
                  (id 0))))))



;;; (i-am-here) ;;; Mon Jun 20 14:47:43 2005

;;;; Really don't want to touch this. 
;;;; 
;;;; We later can prove if an arraytype is assignable to ...
;;;; then we can prove lookupfield from that type could never succeed!! 

(local 
 (defthm
  consistent-object-and-field-found-in-lookup-implies-jvm-field-access-guard-lemma2
  (implies (and (consistent-state s)
                (consistent-object obj (heap s) (instance-class-table s))
                (isArrayType (obj-type obj))
                (equal (fieldcp-classname fieldcp) "java.lang.Object")
                (consistent-array-object obj
                                         (heap s) (instance-class-table s)
                                         (array-class-table s))
                ;; need to strengthen GUARD 
                ;; and check for GETFIELD ;; Thu Jun  9 15:43:06 2005
                ;; done!! 
                (car (isAssignableTo (obj-type obj) (fieldCP-classname fieldcp) s))
                (lookupField (fieldcp-to-field-ptr fieldCP) s))
           (jvm::jvp-access-field-guard (field-classname (lookupField (fieldcp-to-field-ptr fieldCP) s))
                                        (fieldcp-fieldname fieldCP)
                                        (java-visible-portion obj)))
  :hints (("Goal" :in-theory (e/d (consistent-object
                                   jvm::jvp-access-field-guard) 
                                  (consistent-state
                                   consistent-array-object
                                   lookupfield
                                   consistent-jvp
                                   field-ptr-fieldname
                                   field-ptr-classname
                                   field-ptr-type
                                   fieldcp-fieldtype
                                   fieldcp-fieldname
                                   isAssignableTo
                                   isClassTerm
                                   fieldcp-classname
                                   ))))))


(in-theory (disable REFp jvm::jvp-access-field-guard consistent-object))

;;; we want to normalize the (field-fieldname (lookupfield ...))  to be ...

;; (defthm field-fieldname-reduce
;;   (implies (LOOKUPFIELD field-ptr s)
;;            (equal (FIELD-FIELDNAME (LOOKUPFIELD field-ptr s))
;;                   (field-ptr-fieldname field-ptr)))
;;   :hints (("Goal" :in-theory (e/d (lookupfield) (LOOKUPFIELD-INV
;;                                                  searchfields 
;;                                                  fields
;;                                                  field-fieldname 
;;                                                  isClassTerm
;;                                                  superclass-no-loop))
;;            :do-not '(generalize))))

(encapsulate () 
  (local (include-book "base-lookupfield-fieldname-normalize"))

  (defthm field-fieldname-reduce
    (implies (LOOKUPFIELD field-ptr s)
             (equal (FIELD-FIELDNAME (LOOKUPFIELD field-ptr s))
                    (field-ptr-fieldname field-ptr))))

  (defthm field-fieldtype-reduce
    (implies (LOOKUPFIELD field-ptr s)
             (equal (FIELD-FIELDTYPE (LOOKUPFIELD field-ptr s))
                    (field-ptr-type field-ptr)))))


(defthm
  consistent-object-and-field-found-in-lookup-implies-jvm-field-access-guard-weak
  (implies (and (consistent-state s)
                (consistent-object obj (heap s) (instance-class-table s))
                (or (not (isArrayType (obj-type obj)))
                    (and (equal (fieldcp-classname fieldcp) "java.lang.Object")
                         (consistent-array-object obj (heap s)
                                                  (instance-class-table s)
                                                  (array-class-table s))))
                ;; need to strengthen GUARD 
                ;; and check for GETFIELD ;; Thu Jun  9 15:43:06 2005
                ;; done!! 
                (car (isAssignableTo (obj-type obj) (fieldCP-classname fieldcp) s))
                (lookupField (fieldcp-to-field-ptr fieldCP) s))
           (jvm::jvp-access-field-guard (field-classname 
                                         (lookupField (fieldcp-to-field-ptr
                                                       fieldCP) s))
                                        (fieldcp-fieldname fieldcp)
                                        (java-visible-portion obj)))
  :hints (("Goal" :in-theory (e/d ()
                                  (consistent-state
                                   consistent-object
                                   jvm::jvp-access-field-guard
                                   lookupfield
                                   field-ptr-fieldname
                                   field-ptr-classname
                                   field-ptr-type
                                   fieldcp-fieldtype
                                   fieldcp-fieldname
                                   isAssignableTo
                                   isClassTerm
                                   fieldcp-classname
                                   ))
           :use ((:instance
                  consistent-object-and-field-found-in-lookup-implies-jvm-field-access-guard-lemma2)
                 (:instance 
                  consistent-object-and-field-found-in-lookup-implies-jvm-field-access-guard-lemma)))))

;----------------------------------------------------------------------

;;; proved before. export for base-consistent-object-m6-getfield.lisp!! 
;;;

(defthm java-lang-Object-lookup-field-if-found-then-found-in-java-lang-Object
  (implies (and (consistent-state s)
                (EQUAL (FIELDCP-CLASSNAME FIELDCP)
                       "java.lang.Object")
                (lookupField (FIELDCP-TO-FIELD-PTR FIELDCP) s))
           (EQUAL (FIELD-CLASSNAME (lookupField (FIELDCP-TO-FIELD-PTR FIELDCP) s))
                  "java.lang.Object"))
  :hints (("Goal" :in-theory (e/d () (consistent-state)))))



;; (defthm consistent-state-implies-java-lang-Object-not-fields
;;   (IMPLIES (AND (EQUAL (FIELDCP-CLASSNAME FIELDCP)
;;                        "java.lang.Object")
;;          (NOT (SEARCHFIELDS (FIELDCP-TO-FIELD-PTR FIELDCP)
;;                             (FIELDS (CONS L1 L2))))).


(defthm consistent-state-implies-java-lang-Object-not-fields
  (implies (consistent-state s)
           (not (fields (class-by-name "java.lang.Object" (instance-class-table s))))))


(defthm searchfields-in-nil-nil
  (not (searchfields field-ptr nil)))


(defthm consistent-state-lookupfield-fail-if-array-type-assignable-into
  (implies (and  (consistent-state s)
                 (isArrayType typ1) 
                 (car (isAssignableTo typ1 (fieldcp-classname fieldcp) s)))
           (not (lookupField (fieldcp-to-field-ptr fieldcp) s)))
  :hints (("Goal" :in-theory (e/d () (consistent-state 
                                      isClassTerm
                                      fieldcp-classname)))))



(defthm
  consistent-object-and-field-found-in-lookup-implies-jvm-field-access-guard
  (implies (and (consistent-state s)
                (consistent-object obj (heap s) (instance-class-table s))
                (car (isAssignableTo (obj-type obj) (fieldCP-classname fieldcp) s))
                (lookupField (fieldcp-to-field-ptr fieldCP) s))
           (jvm::jvp-access-field-guard (field-classname 
                                         (lookupField (fieldcp-to-field-ptr
                                                       fieldCP) s))
                                        (fieldcp-fieldname fieldcp)
                                        (java-visible-portion obj)))
  :hints (("Goal" :in-theory (e/d ()
                                  (consistent-state
                                   consistent-array-object
                                   consistent-object
                                   jvm::jvp-access-field-guard
                                   lookupfield
                                   isArrayType
                                   field-ptr-fieldname
                                   field-ptr-classname
                                   field-ptr-type
                                   fieldcp-fieldtype
                                   fieldcp-fieldname
                                   isAssignableTo
                                   isClassTerm
                                   fieldcp-classname
                                   ))
           :cases ((isArrayType (obj-type obj))))))



;----------------------------------------------------------------------


;; (i-am-here) ;; Tue Jun 21 16:02:00 2005


;; make this exportable also!! 

(defthm consistent-state-implie-super-of-interface-is-java-lang-Object
   (implies (and (consistent-state s)
                 (isInterface (class-by-name name (instance-class-table s))))
            (equal (super (class-by-name name (instance-class-table s)))
                   "java.lang.Object"))
   :hints (("Goal" :in-theory (e/d () (consistent-state
                                       WFF-CLASS-REP-STATIC-STRONG
                                       JVM::WFF-STATIC-CP-OK-S)))))


