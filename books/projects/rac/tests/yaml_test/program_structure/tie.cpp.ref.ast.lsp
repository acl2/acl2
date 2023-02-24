

(funcdef foo () (block (return (mv 1 2))))(funcdef bar () (block (list (declare a 0) (declare b 0)) (mv-assign (a b) (foo)) (return 0)))
