

(funcdef foo () (block (declare x (bits -1 31 0)) (declare y (bits (+ (ash (si x 32) (- 31)) 1) 31 0)) (return y)))
