

(funcdef foo () (block (declare s (as (quote b) 4 (as (quote a) 3 ()))) (return (ag (quote a) s))))(funcdef bar () (block (declare s (as (quote b) 4 (as (quote a) 2 ()))) (return (ag (quote a) s))))
