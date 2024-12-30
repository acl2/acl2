

(funcdef set_test (n x) (block (assign x (setbits x n (+ 0 (- (truncate (/ n 2) 1) 1)) 0 (bits (bits 0 (- (truncate (/ n 2) 1) 1) 0) (- (truncate (/ n 2) 1) 1) 0))) (assign x (setbits x n (+ (truncate (/ n 2) 1) (- (truncate (/ n 2) 1) 1)) (truncate (/ n 2) 1) (bits (bits #xFFFFFFFF (- (truncate (/ n 2) 1) 1) 0) (- (truncate (/ n 2) 1) 1) 0))) (return (si (bits x 31 0) 32))))(funcdef main () (block (return (set_test 4 5))))
