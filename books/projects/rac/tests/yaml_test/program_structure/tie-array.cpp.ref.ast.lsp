

(funcdef foo () (block (return (mv 1 2))))(funcdef bar () (block (declare a ()) (block (declare temp-1) (declare temp-0) (mv-assign (temp-0 temp-1) (foo)) (assign a (as 0 temp-0 a)) (assign a (as 1 temp-1 a))) (return 0)))
