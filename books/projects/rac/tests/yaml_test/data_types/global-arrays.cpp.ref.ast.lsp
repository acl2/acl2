
(declare global_array (list 1 2))
(funcdef foo () (block (return (nth 1 (global_array)))))(funcdef bar () (block (declare local_array (list 3 5)) (return (ag 1 local_array))))(funcdef bar2 () (block (declare local_mutable_array (ainit (list (cons 0 3) (cons 1 5)))) (assign local_mutable_array (as 1 4 local_mutable_array)) (return (ag 1 local_mutable_array))))
