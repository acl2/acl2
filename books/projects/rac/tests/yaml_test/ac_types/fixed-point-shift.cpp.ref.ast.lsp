

(funcdef rshift (x) (block (return (* (/ x (expt 2 1)) (expt 2 2)))))(funcdef lshift (x) (block (return (/ (/ x (expt 2 1)) (expt 2 2)))))
