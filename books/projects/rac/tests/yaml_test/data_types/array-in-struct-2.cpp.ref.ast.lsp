

(funcdef foo () (block (declare s1 (as (quote a) nil ())) (assign s1 (as (quote a) (as 3 1 (ag (quote a) s1)) s1)) (return (ag 3 (ag (quote a) s1)))))(funcdef bar () (block (declare s2 (as (quote a) nil ())) (assign s2 (as (quote a) (as 3 1 (ag (quote a) s2)) s2)) (return (ag 3 (ag (quote a) s2)))))
