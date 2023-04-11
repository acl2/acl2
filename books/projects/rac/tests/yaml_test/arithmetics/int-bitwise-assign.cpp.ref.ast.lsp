

(funcdef foo (a) (block (assign a (ash a (- 1))) (assign a (ash a 1)) (assign a (logand a 1)) (assign a (logior a 1)) (assign a (logxor a 1)) (return a)))
