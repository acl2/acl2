
(declare global_array (quote (1 2)))
(funcdef foo () (block (return (nth 1 (global_array)))))(funcdef bar () (block (declare local_array (quote ((0 . 3) (1 . 5)))) (return (ag 1 local_array))))(funcdef bar2 () (block (declare local_mutable_array (quote ((0 . 3) (1 . 5)))) (assign local_mutable_array (as 1 4 local_mutable_array)) (return (ag 1 local_mutable_array))))
