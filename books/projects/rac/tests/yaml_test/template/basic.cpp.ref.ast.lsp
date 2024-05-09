

(funcdef foo-0 () (block (return (+ 2 4))))(funcdef foo2-0 () (block (return (+ 1 3))))(funcdef bar () (block (return (+ (foo-0) (foo2-0)))))
