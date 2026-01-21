

(funcdef foo (si10_val si32_val) (block (declare a (si (bits 10 9 0) 10)) (declare b (si (bits 10 31 0) 32)) (declare a2 (bits (si (bits 10 9 0) 10) 31 0)) (declare b2 (bits (si (bits 10 31 0) 32) 31 0)) (declare c (bits (si si10_val 10) 31 0)) (declare d (bits (si si32_val 32) 9 0)) (declare f (bits (* (si c 32) (si d 10)) 31 0)) (return (si f 32))))
