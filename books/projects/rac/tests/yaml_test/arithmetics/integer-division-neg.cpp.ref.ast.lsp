

(funcdef div_int () (block (return (truncate (/ 10 -7) 1))))(funcdef div_reg () (block (declare a (bits 10 31 0)) (declare b (bits -7 31 0)) (return (bits (truncate (/ (si a 32) (si b 32)) 1) 31 0))))(funcdef mod_int () (block (return (rem 10 -7))))(funcdef mod_reg () (block (declare a (bits 10 31 0)) (declare b (bits -7 31 0)) (return (rem (si a 32) (si b 32)))))
