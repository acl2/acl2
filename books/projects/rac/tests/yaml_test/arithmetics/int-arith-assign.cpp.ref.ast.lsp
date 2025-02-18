

(funcdef foo (a) (block (assign a (+ a 1)) (assign a (- a 1)) (assign a (* a 2)) (assign a (rem a 2)) (assign a (+ a 1)) (assign a (- a 1)) (return a)))
