(in-package "DJVM")
(include-book "../../BCV/typechecker")
(include-book "../../BCV/bcv-functions")
(include-book "base")
(include-book "base-consistent-state")
(include-book "base-bind-free")


(local (include-book "base-load-class-normalize-deref2-support"))


(defthm deref2-no-change-after-resolveClassReference
   (implies (and (not (NULLp v))
                 (consistent-state s)
                 (REFp v (heap s)))
            (equal (deref2 v (heap (resolveclassreference any s)))
                   (deref2 v (heap s))))
   :hints (("Goal" :in-theory (e/d (resolveclassreference)
                                   (REFp))
            :do-not '(generalize fertilize))))


(defthm REFp-remains-REFp-resolveCalssReference
   (implies (REFp v (heap s))
            (REFp v (heap (resolveClassReference any s))))
   :hints (("Goal" :in-theory (e/d (resolveClassReference) (REFp)))))




(defthm deref2-no-change-after-getArrayClass 
  (implies (and (not (NULLp v))
                (consistent-state s)
                (REFp v (heap s)))
           (equal (deref2 v (heap (getArrayClass any s)))
                  (deref2 v (heap s))))
  :hints (("Goal" :in-theory (e/d (resolveclassreference)
                                  (REFp))
           :do-not '(generalize fertilize))))


(defthm REFp-remains-REFp-getArrayClass
   (implies (REFp v (heap s))
            (REFp v (heap (getArrayClass any s))))
   :hints (("Goal" :in-theory (e/d (getArrayClass) (REFp)))))
