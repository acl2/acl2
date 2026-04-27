

(funcdef foo (x) (block (return (mv x x))))(funcdef bar () (block (list (declare x 0) (declare y 0)) (block (mv-assign (x y) (foo 3)) (assign x (bits x 1 0)) (assign y (bits y 1 0))) (return (true$))))
