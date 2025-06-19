
(declare n 0)(declare s (as (quote a) 3 ()))(declare a 2)(declare b 2)(declare arr (ainit (list (cons 0 1) (cons 1 2) (cons 2 3) (cons 3 4))))(declare std_arr (ainit (list (cons 0 1) (cons 1 2))))
(funcdef foo () (block (return (+ (+ (a) (ag (quote a) (s))) (n)))))(funcdef bar () (block (list (declare c 4) (declare e 4) (declare f 4)) (return (ag 3 (arr)))))
