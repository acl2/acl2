

(funcdef foo () (block (declare res 0) (for ((declare i 0) (log< i 5) (+ i 1)) (block (assign res (si (bits (+ res i) 31 0) 32)))) (return res)))(funcdef bar () (block (declare res 0) (for ((declare i 0) (log< i 5) (+ i 1)) (block (assign res (si (bits (+ res i) 31 0) 32)))) (return res)))
