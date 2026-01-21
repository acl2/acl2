

(funcdef foo () (block (list (declare a 0) (declare b 0) (declare c 0)) (assign a 2) (assign b 4) (list (declare d (ainit (list (cons 0 0) (cons 1 0) (cons 2 0)))) (declare e (ainit (list (cons 0 0) (cons 1 0) (cons 2 0)))) (declare f (ainit (list (cons 0 0) (cons 1 0) (cons 2 0))))) (return (+ a b))))
