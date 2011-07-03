(in-package "ACL2")

(include-book "rtl")
(include-book "log")


(local (include-book "../../arithmetic/top"))


(local 
 (defthm bvecp-fl-1/2
   (implies (bvecp x (+ 1 n))
            (BVECP (FL (* 1/2 X)) n))
   :hints (("Goal" :in-theory (e/d (bvecp
                                    expt-2-reduce-leading-constant) ())))))

(local 
 (defthm bvecp-mod-2
   (implies (integerp x)
            (BVECP (MOD X 2) 1))
   :hints (("Goal" :in-theory (e/d (bvecp) ())))))



(defthm land-logand
  (implies (and (bvecp x n)
                (bvecp y n)
                (natp n))
           (equal (land x y n)
                  (logand x y)))
  :hints (("Goal" :in-theory (e/d (binary-land)
                                  ())
           :induct (binary-land x y n))
          ("Subgoal *1/4" :use ((:instance logand-def
                                           (i x)
                                           (j y)))))))


(defthm lior-logior
  (implies (and (bvecp x n)
                (bvecp y n)
                (natp n))
           (equal (lior x y n)
                  (logior x y)))
  :hints (("Goal" :in-theory (e/d (binary-lior)
                                  ())
           :induct (binary-lior x y n))
          ("Subgoal *1/4" :use ((:instance logior-def
                                           (i x)
                                           (j y)))))))

(defthmd lior-logior
  (implies (and (natp n)
                (> n 0)
                (integerp x)
                (integerp y))
           (equal (lior x y n)
                  (bits (logior x y) (+ -1 n) 0))))

