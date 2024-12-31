

(funcdef div (a) (block (assign a (truncate (/ a 2) 1)) (return a)))
