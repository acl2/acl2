

(funcdef slc_test (n s) (block (declare x (bits 4 (- n 1) 0)) (return (si (bits (if1 s (si x n) x) 31 0) 32))))(funcdef main () (block (return (slc_test 4 (true$)))))
