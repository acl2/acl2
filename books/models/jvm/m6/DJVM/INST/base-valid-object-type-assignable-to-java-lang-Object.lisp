(in-package "DJVM")
(include-book "../../M6-DJVM-shared/jvm-object-type-hierachy")
(include-book "../../DJVM/consistent-state")

(local 
 (defthm consistent-state-implies-obj-type-assignable-java-lang-Object-strong
   (implies (ISARRAYTYPE type)
            (CAR (ISASSIGNABLETO type
                                 "java.lang.Object" S)))
   :hints (("Goal" :in-theory (enable isarraytype primitive-type?)))))


;;;
;;; because of the way that isassignableto is defined
;;;
;;; there is a short cut for return T when we test against "java.lang.Object"
;;;
;;;
;;; This is why it is difficult to relate 
;;;  BCV::isAssignable
;;; to 
;;;  DJVM::isAssignableTo !!!
;;;
;;; What I have proved is that those optimization is in fact safe to do!!
;;; 
;;;

(defthm consistent-state-implies-obj-type-assignable-java-lang-Object
  (implies (and (consistent-state s)
                (ISARRAYTYPE (OBJ-TYPE (DEREF2 v  (heap s)))))
           (CAR (ISASSIGNABLETO (OBJ-TYPE (DEREF2 v (HEAP S)))
                                "java.lang.Object" S)))
  :hints (("Goal" :in-theory (disable consistent-state isarraytype
                                      isassignableto deref2))))

