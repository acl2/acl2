(in-package "DJVM")
(include-book "../../DJVM/consistent-state")
(include-book "../../DJVM/consistent-state-properties")

(include-book "base-valid-type-s")
(include-book "base-consistent-state")



(local (in-theory (e/d (class-exists?) ( array-type? obj-type isClassTerm))))


(defthm isArrayType-not-stringp
  (implies (isArrayType type)
           (not (stringp type)))
  :hints (("Goal" :in-theory (enable isArrayType))))

(defthm isArrayType-is-array-type-normalize
  (equal (isArrayType type)
         (array-type? type))
  :hints (("Goal" :in-theory (enable isArrayType array-type?))))


(defthm valid-type-s-is-instantiated
   (and (equal (reference-type-s type cl)
               (valid-type-s type cl 1))
        (equal (array-type-s type cl)
               (valid-type-s type cl 0)))
   :hints (("Goal" :use valid-type-s-is)))


(defthm consistent-object-valid-type-strong
  (implies (and (consistent-object obj (heap s) (instance-class-table s))
                (or (not (isArrayType (obj-type obj)))
                    (consistent-array-object obj (heap s) 
                                             (instance-class-table s)
                                             (array-class-table s)))
                (consistent-state s))
           (valid-type-strong (obj-type obj) (instance-class-table s)))
  :hints (("Goal" :in-theory (e/d (consistent-object 
                                   consistent-array-object) ()))))


(encapsulate () 
  (local (include-book "base-consistent-state-class-names-are-string"))
  (defthm consistent-state-class-name-is-stringp
  (implies (and (class-by-name name (instance-class-table s))
                (consistent-state s))
           (stringp name))
  :rule-classes :forward-chaining))


(defthm consistent-state-null-not-bounded
  (implies (CONSISTENT-STATE S)
           (not (ISCLASSTERM (CLASS-BY-NAME 'NULL
                                            (INSTANCE-CLASS-TABLE S)))))
  :hints (("Goal" 
           :use ((:instance consistent-state-class-name-is-stringp
                            (name 'NULL))))))



(defthm class-loaded-consistent-state-implies-valid-type-strong
  (implies (and (class-loaded? any s)
                (consistent-state s))
           (valid-type-strong any (instance-class-table s)))
  :hints (("Goal" :in-theory (enable class-loaded?))))



;; (defthm isAssignable-to-then-loaded
;;   (implies (and (car (isAssignableTo typ1 typ2 s))
;;                 (consistent-state s)
;;                 (valid-type-strong typ1 (instance-class-table s)))
;;            (valid-type-strong typ2 (instance-class-table s)))
;;   :hints (("Goal" :in-theory (enable isAssignableTo)
;;            :do-not '(generalize))))
