

(funcdef get (ss) (block (return (ag (quote b) ss))))(funcdef set () (block (declare ss ()) (assign ss (as (quote a) 2 ss)) (assign ss (as (quote b) 9 ss)) (declare copied ss) (return (+ (ag (quote a) ss) (ag (quote b) ss)))))
