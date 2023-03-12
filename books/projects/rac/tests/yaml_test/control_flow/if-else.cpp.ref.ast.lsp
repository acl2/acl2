

(funcdef foo (a) (block (declare b 0) (if a (block (assign b 1)) (block (assign b 2))) (return b)))
