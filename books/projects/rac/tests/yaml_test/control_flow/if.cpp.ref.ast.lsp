

(funcdef foo (a) (block (declare b 0) (if a (block (assign b 1)) ()) (return b)))
