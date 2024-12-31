

(funcdef slc_test (n) (block (return (bits (bits 4 (- n 1) 0) (- n 1) 0))))(funcdef main () (block (return (si (bits (slc_test 4) 31 0) 32))))
