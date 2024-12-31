

(funcdef foo (i j) (block (return (+ i j))))(funcdef foo2 (i j) (block (return (+ i j))))(funcdef bar () (block (return (+ (foo 2 4) (foo2 1 3)))))
