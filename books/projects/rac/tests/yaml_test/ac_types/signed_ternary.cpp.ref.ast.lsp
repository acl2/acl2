

(funcdef foo (bsigned b) (block (declare bval (if1 bsigned (si (bits b 7 0) 8) b)) (return bval)))
