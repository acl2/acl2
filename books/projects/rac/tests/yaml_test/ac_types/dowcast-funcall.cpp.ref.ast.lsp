

(funcdef foo (f) (block (return f)))(funcdef bar (f) (block (return (si (bits f 31 0) 32))))(funcdef main () (block (return (+ (foo (bits 255 1 0)) (bar 255)))))
