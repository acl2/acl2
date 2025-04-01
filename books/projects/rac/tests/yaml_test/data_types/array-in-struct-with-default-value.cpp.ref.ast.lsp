

(funcdef foo () (block (declare s1 (as (quote a) (ainit (list (cons 0 1) (cons 1 2) (cons 2 3) (cons 3 4))) ())) (assign s1 (as (quote a) (as 3 1 (ag (quote a) s1)) s1)) (return (ag 3 (ag (quote a) s1)))))(funcdef bar () (block (declare s1 (as (quote a) (ainit (list (cons 0 1) (cons 1 2) (cons 2 3) (cons 3 4))) ())) (assign s1 (as (quote a) (as 3 1 (ag (quote a) s1)) s1)) (return (ag 3 (ag (quote a) s1)))))
