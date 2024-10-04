(in-package "DJVM")
(include-book "../../M6-DJVM-shared/jvm-linker")
(local (include-book "base-load-class-normalize-class-by-name-support"))



(defthm class-by-name-no-change-after-resolveClassReference
  (implies (isClassTerm (class-by-name name (instance-class-table s)))
           (equal (class-by-name name (instance-class-table
                                       (resolveclassreference any s)))
                  (class-by-name name (instance-class-table s)))))


  
(defthm class-by-name-no-change-after-getArrayClass
  (implies (isClassTerm (class-by-name name (instance-class-table s)))
           (equal (class-by-name name (instance-class-table
                                       (getArrayClass any s)))
                  (class-by-name name (instance-class-table s)))))
  
