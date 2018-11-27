

(include-book "build/ifdef" :dir :system)

(ifndef "DEFS_ONLY"
        (include-book "thm-base")
        :endif)

(ifdef "THMS_ONLY"
        (include-book "defs")
        :endif)

(encapsulate nil

  (defun make-b+ (x y)
    `(binary-+ ,x ,y))

  (ifndef "DEFS_ONLY"
          (defthm make-b+-correct
            (equal (myev (make-b+ x y) a)
                   (+ (myev x a)
                      (myev y a))))
          :endif))
    
    
