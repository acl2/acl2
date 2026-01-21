
(declare a_global (ainit (list (cons 0 1) (cons 1 2) (cons 2 3))))(declare a_fast_global (list 1 2 3))
(funcdef global_use () (block (return (+ (ag 1 (a_global)) (nth 1 (a_fast_global))))))(funcdef local_use () (block (declare a_local (ainit (list (cons 0 1) (cons 1 2) (cons 2 3)))) (declare a_fast_local (list 1 2 3)) (return (+ (ag 1 a_local) (nth 1 a_fast_local)))))
