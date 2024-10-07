(in-package "DJVM")

(include-book "../../DJVM/consistent-state")
(include-book "../../DJVM/consistent-state-properties")
(include-book "../../M6-DJVM-shared/jvm-object-type-hierachy")


(include-book "base-valid-type-s")



(local (in-theory (e/d (class-exists? class-loaded? isAssignableTo) 
                       (consistent-state primitive-type?
                        array-type? obj-type isClassTerm))))



(encapsulate () 
  (local (include-book "base-consistent-state-class-names-are-string"))
  (defthm consistent-state-class-name-is-stringp
    (implies (and (class-by-name name (instance-class-table s))
                  (consistent-state s))
             (stringp name))
    :rule-classes :forward-chaining))



(defthm consistent-state-not-bound-null-classname
  (implies (consistent-state s)
           (not (CLASS-BY-NAME 'NULL
                               (INSTANCE-CLASS-TABLE S))))
  :hints (("Goal" :cases (CLASS-BY-NAME 'NULL
                               (INSTANCE-CLASS-TABLE S)))))


(local (in-theory (disable ISSUPERCLASS1-INVARIANT)))



(defthm wff-instance-class-table-implies-isClassTerm-equiv
  (implies (wff-instance-class-table cl)
           (iff (isClassTerm (class-by-name name cl))
                (class-by-name name cl)))
  :hints (("Goal" :in-theory (enable isClassTerm wff-class-rep))))
                


(defthm consistent-state-class-by-name-isClassTerm
   (implies (consistent-state s)
            (iff (isClassTerm (class-by-name name (instance-class-table s)))
                 (class-by-name name (instance-class-table s)))))
                
(defthm boot-strap-class-okp-implies-class-bound
  (implies (boot-strap-class-okp s)
           (class-by-name "java.lang.Object" 
                          (instance-class-table s)))
  :hints (("Goal" :in-theory (enable boot-strap-class-okp))))



(defthm consistent-state-implies-java-lang-Object-bound
  (implies (consistent-state s)
           (class-by-name "java.lang.Object" 
                          (instance-class-table s)))
  :hints (("Goal" :in-theory (e/d (consistent-state)
                                  (boot-strap-class-okp
                                   class-by-name)))))







(local 
 (defthm
   class-hierachy-consistent1-class-n-implies-not-java-lang-Object-super-bounded
   (implies 
    (and (class-hierachy-consistent1-class-n name cl)
         (not (equal name "java.lang.Object")))
    (class-by-name (super (class-by-name name cl))
                   cl))))


(local 
 (defthm
   class-hierachy-consistent1-aux-implies-bounded-class-hierachy-consistent1-class-n
   (implies (and (class-hierachy-consistent1-aux cl1 cl)
                 (class-by-name name cl1))
            (class-hierachy-consistent1-class-n name cl))))


(local 
 (defthm consistent-state-implies-class-hierachy-consistent1-aux
   (implies (consistent-state s)
            (class-hierachy-consistent1-aux (instance-class-table s)
                                            (instance-class-table s)))
   :hints (("Goal" :in-theory (enable consistent-state
                                      consistent-class-hierachy)))))



(defthm consistent-state-implies-not-equal-java-lang-Object-super-bounded
   (implies (and (consistent-state s)
                 (not (equal name "java.lang.Object"))
                 (class-by-name name (instance-class-table s)))
            (class-by-name (super (class-by-name name
                                                 (instance-class-table s)))
                           (instance-class-table s)))
   :hints (("Goal" :in-theory (e/d (consistent-class-hierachy)
                                   (class-hierachy-consistent1-class-n
                                    consistent-state
                                    isClassTerm))
            :use ((:instance
                   class-hierachy-consistent1-aux-implies-bounded-class-hierachy-consistent1-class-n
                   (cl1 (instance-class-table s))
                   (cl (instance-class-table s)))))))


(defthm bounded-implies-super-bound
  (implies (and (NOT (EQUAL TYP1 "java.lang.Object"))
                (CLASS-BY-NAME TYP1 (INSTANCE-CLASS-TABLE S))
                (CONSISTENT-STATE S))
           (class-by-name (super (class-by-name typ1
                                                (instance-class-table s)))
                          (instance-class-table s))))





(defthm consistent-state-java-lang-Object-super-empty
  (implies (consistent-state s)
           (equal (super (class-by-name "java.lang.Object"
                                        (instance-class-table s)))
                  ""))
  :hints (("Goal" :in-theory (enable consistent-state))))



(defthm super-never-null
  (implies (CONSISTENT-STATE S)
           (not (equal (super (class-by-name typ1
                                             (instance-class-table s)))
                       'NULL)))
  :hints (("Goal" :cases ((equal typ1 "java.lang.Object")))
          ("Subgoal 2" :cases ((CLASS-BY-NAME TYP1 (INSTANCE-CLASS-TABLE S))))
          ("Subgoal 2.1" :use bounded-implies-super-bound)))
                                           





(defthm issuperclass1-then-loaded
   (implies (and (car (issuperclass1 typ1 typ2 s seen))
                 (not (equal typ1 typ2))
                 (consistent-state s))
            (valid-type-strong typ2 (instance-class-table s)))
   :hints (("Goal" :do-not '(generalize)
            :in-theory (e/d (issuperclass1) ()))))





(defthm true-listp-implies-len-1-is-cons-nil
  (implies (and (true-listp l)
                (equal (len l) 1))
           (equal l (cons (car l) nil)))
  :rule-classes nil)

; Matt K. mod: The original proof of array-type-equal fails in October 2024,
; and I'm fixing that by proving the following lemma.

(local (defthm equal-len-opener
         (implies (and (syntaxp (quotep n))
                       (natp n))
                  (equal (equal (len x) n)
                         (if (equal n 0)
                             (atom x)
                           (and (consp x)
                                (equal (len (cdr x)) (1- n))))))))

(defthm array-type-equal
  (implies  (and (array-type? typ1)
                 (array-type? typ2)
                 (equal (array-base-type typ1)
                        (array-base-type typ2)))
            (equal (equal typ1 typ2) t))
  :hints (("Goal" :in-theory (enable array-type?
                                     array-base-type))
          #| Matt K. mod: No longer needed (see comment above):
          ("Subgoal 1" 
           :use ((:instance true-listp-implies-len-1-is-cons-nil
                            (l typ3))
                 (:instance true-listp-implies-len-1-is-cons-nil
                            (l typ4))))
          |#
          ))



(defthm equal-wff-array-type-is-array-type?
  (equal (wff-array-type typ)
         (array-type? typ))
  :hints (("Goal" :in-theory (enable array-type? wff-array-type))))

            
(defthm isinterface-implies-not-nil
  (implies (isinterface (class-by-name name cl))
           (class-by-name name cl)))


(defthm array-component-type-array-base-type
  (equal (array-base-type type)
         (array-component-type type))
  :hints (("Goal" :in-theory (enable array-component-type
                                     array-base-type))))


(defthm isAssignable-to-then-loaded
   (implies (and (car (isAssignableTo typ1 typ2 s))
                 (not (equal typ1 typ2))
                 (consistent-state s))
            (valid-type-strong typ2 (instance-class-table s)))
   :hints (("Goal" :do-not '(generalize))))

;
;----------------------------------------------------------------------
;
