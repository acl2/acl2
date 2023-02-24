

(funcdef foo (a) (block (declare b 0) (switch a (1 (assign b 1)) (2 (assign b 2)) (t (assign b 3))) (return b)))
