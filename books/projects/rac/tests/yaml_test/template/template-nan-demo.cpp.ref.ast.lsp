

(funcdef is_nan (manw expw x) (block (declare is_exp_saturated (log= (bits x (+ manw (- expw 1)) manw) (- (ash 1 expw) 1))) (declare is_man_zero (log= (bits x (+ 0 (- manw 1)) 0) 0)) (return (logand1 is_exp_saturated (lognot1 is_man_zero)))))(funcdef main () (block (declare sp_nan (is_nan 23 8 #xFFFFFFFF)) (declare sp_not_nan (is_nan 23 8 #x00000000)) (declare dp_nan (is_nan 52 10 #xFFFFFFFFFFFFFFFF)) (declare dp_not_nan (is_nan 52 11 #xFFFFFFFF)) (assert sp_nan main) (assert (lognot1 sp_not_nan) main) (assert dp_nan main) (assert (lognot1 dp_not_nan) main) (return 0)))
