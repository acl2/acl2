

(funcdef foo () (block (declare res 0) (for ((declare i 0) (log< i 5) (+ i 1)) (block (assign res (+ res i)))) (return res)))
