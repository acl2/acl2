(in-package "ACL2")

(local (include-book "../amdrtl/arithmetic/basic"))



(defthm expansion-normalize-3
  (implies (integerp k)
           (equal (* (EXPT 2 (+ -2 (* 2 K)))
                     -2 (BITN Y (+ -1 (* 2 K))))
                  (* -1 (expt 2 (+ -1 (* 2 k)))
                     (BITN Y (+ -1 (* 2 K))))))
  :hints (("Goal" :use ((:instance a15 (i 2)
                                 (j1 1)
                                 (j2 (+ -2 (* 2 k))))))))
