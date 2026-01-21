

(funcdef foo () (block (declare t (mv 1 (bits 4 1 0))) (return t)))(funcdef bar () (block (declare t (ainit (list (cons 0 1) (cons 1 (bits 4 1 0))))) (return t)))
