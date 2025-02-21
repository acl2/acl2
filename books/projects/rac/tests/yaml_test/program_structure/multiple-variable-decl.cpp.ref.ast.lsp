

(funcdef foo () (block (list (declare a 0) (declare b 0) (declare c 0)) (assign a 2) (assign b 4) (list (declare d (quote ((0 . 0) (1 . 0) (2 . 0)))) (declare e (quote ((0 . 0) (1 . 0) (2 . 0)))) (declare f (quote ((0 . 0) (1 . 0) (2 . 0))))) (return (+ a b))))
