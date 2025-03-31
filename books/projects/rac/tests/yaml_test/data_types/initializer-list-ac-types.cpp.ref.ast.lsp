

(funcdef foo () (block (declare t (mv 1 (bits 4 1 0))) (return t)))(funcdef bar () (block (declare t (quote ((0 . 1) (1 . (bits 4 1 0))))) (return t)))
