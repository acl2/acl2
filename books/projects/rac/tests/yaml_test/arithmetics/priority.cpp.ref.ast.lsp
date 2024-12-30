

(funcdef foo (a b c) (block (declare res1 (+ (* a b) c)) (declare res2 (+ (truncate (/ a b) 1) c)) (declare res3 (rem (* a b) c)) (declare res4 (* (truncate (/ a b) 1) b)) (declare res5 (* a (+ b c))) (return 0)))
