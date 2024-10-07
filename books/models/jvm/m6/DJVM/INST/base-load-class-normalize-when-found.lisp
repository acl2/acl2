(in-package "DJVM")

(include-book "../../DJVM/consistent-state")
(include-book "../../DJVM/consistent-state-properties")
(include-book "../../M6-DJVM-shared/jvm-object-type-hierachy")

(in-theory (disable getArrayClass resolveClassReference))

(include-book "base-valid-type-s")


;; (defthm consistent-object-not-array-implies-class-loaded
;;   (implies (and (consistent-object obj (heap s) (instance-class-table s))
;;                 (not (isArrayType (obj-type obj))))
;;            (isClassTerm (class-by-name (obj-type obj)
;;                                        (instance-class-table s))))
;;   :hints (("Goal" :in-theory (enable consistent-object class-exists?))))
                 



(defthm valid-type-strong-not-array-type-implies-loaded
  (implies (and (valid-type-strong type (instance-class-table s))
                (not (isArrayType type)))
           (isClassTerm (class-by-name type (instance-class-table s))))
  :hints (("Goal" :expand  (VALID-TYPE-S TYPE (INSTANCE-CLASS-TABLE S) 0)
           :in-theory (e/d (wff-array-type class-exists? isArrayType)
                           (isClassTerm)))))


(encapsulate () 
  (local (include-book "base-isAssignableTo-properties"))
  (defthm isAssignable-to-then-loaded
    (implies (and (car (isAssignableTo typ1 typ2 s))
                  (not (equal typ1 typ2))
                  (consistent-state s))
             (valid-type-strong typ2 (instance-class-table s)))
    :hints (("Goal" :do-not '(generalize)))))

(defthm not-array-type-is-not-assignable-to-array-type
  (implies (and (not (isArrayType typ1))
                (car (isAssignableTo typ1 typ2 s)))
           (not (isArrayType typ2)))
  :hints (("Goal" :in-theory (enable isArrayType array-type?))))


(encapsulate ()
  (local (include-book "../../M6-DJVM-shared/jvm-state"))
  (defthm wff-state-implies-make-state-equal-state
    (implies (wff-state s)
             (equal (make-state (pc s)
                                (current-thread s)
                                (heap s)
                                (thread-table s)
                                (class-table s)
                                (env s)
                                (error-flag s)
                                (aux s))
                    s))))


(defthm load-loaded-class-no-change
  (implies (and (wff-state s)
                (isClassTerm (class-by-name name (instance-class-table s))))
           (equal (load_class name s) s))
  :hints (("Goal" :in-theory (e/d (load_class class-loaded?
                                   state-set-current-thread)
                                  (isClassTerm))
           :expand (LOAD_CLASS_X NAME
                                 (MAKE-STATE (PC S)
                                             -1 (HEAP S)
                                             (THREAD-TABLE S)
                                             (CLASS-TABLE S)
                                             (ENV S)
                                             (ERROR-FLAG S)
                                             (AUX S))
                                 NIL 3))))
           

(defthm resolveClassReference-no-change-if-not-array-type-and-loaded
  (implies (and (wff-state s)
                (not (isArrayType typ2))
                (isClassTerm (class-by-name typ2 (instance-class-table s))))
           (equal (resolveClassReference typ2 s) s))
  :hints (("Goal" :in-theory (e/d (resolveClassReference 
                                   state-set-current-thread
                                   isArrayType)
                                  (isClassTerm)))))


(encapsulate () 
  (local (include-book "base-consistent-state-consistent-object"))
  (defthm consistent-object-valid-type-strong
    (implies (and (consistent-object obj (heap s) (instance-class-table s))
                  (or (not (isArrayType (obj-type obj)))
                      (consistent-array-object obj (heap s) 
                                               (instance-class-table s)
                                               (array-class-table s)))
                  (consistent-state s))
             (valid-type-strong (obj-type obj) (instance-class-table s)))
    :hints (("Goal" :in-theory (e/d (consistent-object 
                                     consistent-array-object) ())))))

;;
;;(i-am-here) ;; Thu Jun 16 18:33:32 2005
;;

(defthm resolveClassReference-no-change-if-already-loaded-if-not-array-Object
  (implies (and (consistent-object obj (heap s) (instance-class-table s))
                (case-split (not (isArrayType (obj-type obj))))
                (car (isAssignableTo (obj-type obj) typ2 s))
                (consistent-state s))
           (equal (resolveClassReference typ2 s) s))
  :hints (("Goal" :in-theory (e/d () (obj-type 
                                      isClassTerm
                                      wff-state
                                      consistent-object))
           :use ((:instance isAssignable-to-then-loaded
                            (typ1 (obj-type obj)))))))


(local 
 (defthm consistent-state-implies-isClassTerm-java-lang-Object
   (implies (consistent-state s)
            (isClassTerm (class-by-name "java.lang.Object"
                                        (instance-class-table s))))
   :hints (("Goal" :in-theory (e/d (consistent-state
                                    class-loaded?)
                                   (isClassTerm))))
   :rule-classes :forward-chaining))


(defthm resolveClassReference-java-lang-Object-no-change
  (implies (consistent-state s)
           (equal (resolveClassReference "java.lang.Object" s) s))
  :hints (("Goal" :in-theory (e/d (resolveClassReference 
                                   class-loaded?)
                                  (isClassTerm)))))





;;;
;;;
;;; we need to prove is array type A is assignable to array type B.
;;; then array type B is already loaded!!! 
;;; However this may not be the case!!! 
;;;
;;; for example: 
;;;   (array (array (array "java.lang.String"))) exists
;;; may not implies 
;;; that 
;;;   (array (array (array "java.lang.Object"))) exists!!! 
;;; 
;;; so the class loading will change the the state!
;;; 
;;; What save us here is that we know we will not use getfield on 
;;; array-objects!! 
;;; 
;;;

;----------------------------------------------------------------------

