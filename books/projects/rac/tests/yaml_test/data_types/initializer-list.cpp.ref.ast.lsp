

(funcdef foo () (block (declare t (1 2)) (return t)))(funcdef bar () (block (declare t (quote ((0 . 1) (1 . 2)))) (return t)))
