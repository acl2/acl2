

(funcdef foo () (block (declare x (bits -1 31 0)) (declare y (bits (si (bits (+ (si (bits (ash (si x 32) (- 31)) 31 0) 32) 1) 32 0) 33) 31 0)) (return (bits y 31 0))))
