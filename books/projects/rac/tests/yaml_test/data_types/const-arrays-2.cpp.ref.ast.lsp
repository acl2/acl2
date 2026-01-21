
(declare global_a (ainit (list (cons 0 1) (cons 1 2) (cons 2 3))))
(funcdef foo (a) (block (return (ag 2 a))))(funcdef bar () (block (declare local_a (ainit (list (cons 0 1) (cons 1 2) (cons 2 3)))) (return (+ (foo (global_a)) (foo local_a)))))
