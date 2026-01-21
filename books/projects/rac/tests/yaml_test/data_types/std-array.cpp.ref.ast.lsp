

(funcdef foo (a) (block (return (ag 4 a))))(funcdef bar (a b) (block (declare arr (ainit (list (cons 0 0) (cons 1 0)))) (assign arr (as 0 a arr)) (assign arr (as 1 b arr)) (declare copied arr) (return arr)))
