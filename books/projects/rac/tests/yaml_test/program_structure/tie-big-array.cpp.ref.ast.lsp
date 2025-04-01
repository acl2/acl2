

(funcdef foo () (block (return (mv 1 2 3 4 5 6))))(funcdef bar () (block (declare a (ainit (list (cons 0 0) (cons 1 0) (cons 2 0) (cons 3 0) (cons 4 0) (cons 5 0)))) (block (declare temp-5) (declare temp-4) (declare temp-3) (declare temp-2) (declare temp-1) (declare temp-0) (mv-assign (temp-0 temp-1 temp-2 temp-3 temp-4 temp-5) (foo)) (assign a (as 0 temp-0 a)) (assign a (as 1 temp-1 a)) (assign a (as 2 temp-2 a)) (assign a (as 3 temp-3 a)) (assign a (as 4 temp-4 a)) (assign a (as 5 temp-5 a))) (return 0)))
