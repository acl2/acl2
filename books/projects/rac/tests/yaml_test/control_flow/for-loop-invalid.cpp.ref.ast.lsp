

(funcdef adder (a b) (block (declare res 0) (for ((assign res b) (log<> a 0) (bits (- a 1) 7 0)) (block (assign res (bits (+ res 1) 7 0)))) (return res)))
