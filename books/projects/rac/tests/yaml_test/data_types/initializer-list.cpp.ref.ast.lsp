

(funcdef bar () (block (declare t (quote ((0 . 1) (1 . 2)))) (return t)))(funcdef foo () (block (declare s (as (quote b) 4 (as (quote a) 3 ()))) (return s)))
