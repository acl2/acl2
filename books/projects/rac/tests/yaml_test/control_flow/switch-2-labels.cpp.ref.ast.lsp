

(funcdef foo (x) (block (declare a 0) (switch x ((0 1) (assign a 2)) (t (assign a 0))) (return a)))
