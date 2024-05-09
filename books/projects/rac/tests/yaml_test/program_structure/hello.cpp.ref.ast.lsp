

(funcdef reverseByte (mumble) (block (declare result 0) (for ((declare i 0) (log< i 4) (+ i 1)) (block (assign result (setbits result 8 (+ (* 2 i) 1) (* 2 i) (bits mumble (+ (- 6 (* 2 i)) 1) (- 6 (* 2 i))))))) (return result)))
