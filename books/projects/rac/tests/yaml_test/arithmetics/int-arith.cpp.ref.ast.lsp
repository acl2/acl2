

(funcdef add (a b) (block (return (+ a b))))(funcdef sub (a b) (block (return (- a b))))(funcdef minus (a) (block (return (- a))))(funcdef mult (a b) (block (return (* a b))))(funcdef div (a b) (block (return (truncate (/ a b) 1))))(funcdef mod (a b) (block (return (rem a b))))(funcdef parenthesis (a) (block (return a)))
