#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(include-book "ihs/ihs-lemmas" :dir :system)

(local (include-book "arithmetic"))
(include-book "evenp")

(defthmd open-logcons
  (implies (syntaxp (constant-syntaxp b))
           (equal (logcons b i)
                  (+ (bfix b) (* 2 (ifix i)))))
  :hints (("Goal" :in-theory (enable logcons))))

(defthm equal-logcons-0
  (equal (equal (logcons x y) 0)
         (and (equal (bfix x) 0) 
              (equal (ifix y) 0)))
  :hints (("goal" :in-theory (enable logcons 
                                     even-odd-different-2 
                                     ))))

(defthm evenp-of-logcons
  (equal (evenp (logcons b i))
         (evenp (bfix b)))
  :hints (("Goal" :in-theory (enable logcons))))

(defthm oddp-of-logcons
  (equal (oddp (logcons b i))
         (oddp (bfix b)))
  :hints (("Goal" :in-theory (enable logcons))))

(defthm logcons-of-0
  (equal (logcons 0 x)
         (ash x 1))
  :hints (("Goal" :in-theory (enable logcons ash))))

(defthm floor-of-logcons
  (equal (floor (logcons b i) 2)
         (ifix i)
         )
  :hints (("Goal" :expand  (logcons b i))))
