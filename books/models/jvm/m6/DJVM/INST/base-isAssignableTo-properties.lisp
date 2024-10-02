(in-package "DJVM")

(include-book "../../DJVM/consistent-state")
(include-book "../../DJVM/consistent-state-properties")
(include-book "../../M6-DJVM-shared/jvm-object-type-hierachy")
(include-book "base-valid-type-s")



(local (in-theory (e/d (class-exists? class-loaded? isAssignableTo) 
                       (consistent-state primitive-type?
                        array-type? obj-type isClassTerm))))

(local (include-book "base-isAssignableTo-properties-support"))

(defthm isAssignable-to-then-loaded
   (implies (and (car (isAssignableTo typ1 typ2 s))
                 (not (equal typ1 typ2))
                 (consistent-state s))
            (valid-type-strong typ2 (instance-class-table s)))
   :hints (("Goal" :do-not '(generalize))))


;----------------------------------------------------------------------
;