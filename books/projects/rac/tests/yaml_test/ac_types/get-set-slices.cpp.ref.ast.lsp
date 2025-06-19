

(funcdef get_set_unsigned (x) (block (assign x (setbits x 32 3 0 (bits x 13 10))) (return x)))(funcdef get_set_signed (x) (block (assign x (setbits x 32 3 0 (bits (si (bits (si x 32) 13 10) 4) 3 0))) (return (bits (si x 32) 31 0))))(funcdef set_single (x) (block (declare y (bitn x 10)) (assign x (setbits x 16 0 0 y)) (return x)))
