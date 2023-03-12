

(funcdef foo (a b c) (block (declare res1 (+ (* a b) c)) (declare res2 (+ (fl (/ a b)) c)) (declare res3 (rem (* a b) c)) (declare res4 (* (fl (/ a b)) b)) (declare res5 (* a (+ b c))) (return 0)))
