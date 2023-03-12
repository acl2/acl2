
(declare init 3)
(funcdef foo () (block (declare res 0) (for ((declare i (init)) (log< i 9) (+ i 1)) (block (assign res (+ res 1)))) (return res)))
