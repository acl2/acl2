(IN-PACKAGE "ACL2")

(include-book "../lib1/rtl")
(include-book "../lib1/rtlarr")
(include-book "../lib1/bits")


(defthm bitn-setbitn-setbitn
  (implies (and (<  j w)
                (<= 0 j) 
                (integerp w)
                (integerp j))
           (equal (bitn (setbitn x w j y)
                        j)
                  (bitn y 0)))
  :hints (("Goal" :in-theory (enable setbitn BITN-CAT))))
