

(funcdef foo () (block (return (mv 2 1))))(funcdef main () (block (declare a (ainit (list (cons 0 0)))) (declare x 0) (block (declare temp-1) (mv-assign (x temp-1) (foo)) (assign a (as 0 temp-1 a))) (return 0)))
