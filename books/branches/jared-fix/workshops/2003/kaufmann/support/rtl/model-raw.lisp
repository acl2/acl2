(in-package "ACL2")

(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)

(set-inhibit-warnings "THEORY" "DISABLE" "NON-REC")

(include-book "common")

(local
  (in-theory
       (set-difference-theories (current-theory :here)
                                (theory 'rtl-operators-after-macro-expansion))))

(defmacro FOO$RAW::out1 (n)
          (list 'FOO$RAW::out1$ n '$path))

(defmacro FOO$RAW::out2 (n)
          (list 'FOO$RAW::out2$ n '$path))

(set-irrelevant-formals-ok t)

(set-ignore-ok t)

(deflabel model-raw-start-of-defs)

(set-bogus-mutual-recursion-ok t)

(MUTUAL-RECURSION

(defun FOO$RAW::out2$ (n $path)
       (declare (xargs :normalize
                       nil :measure (cons (1+ (nfix n)) 0)))
       (if (zp n)
           (reset 'ACL2::OUT2 4)
           (mod+ (cat (n! 0 1)
                      1 (bits (ww (1- n)) 2 0)
                      3)
                 (n! 1 4)
                 4)))

(defun FOO$RAW::out1$ (n $path)
       (declare (xargs :normalize
                       nil :measure (cons (1+ (nfix n)) 1)))
       (bind case-select (bits (sel n) 1 0)
             (if1 (log= (n! 0 2) case-select)
                  (bitn (in0 n) 0)
                  (if1 (log= (n! 1 2) case-select)
                       (bitn (in1 n) 0)
                       (if1 (log= (n! 2 2) case-select)
                            (bitn (in2 n) 0)
                            (if1 (log= (n! 3 2) case-select)
                                 (bitn (in3 n) 0)
                                 (n! 0 1)))))))

)

(add-macro-alias FOO$RAW::out1 FOO$RAW::out1$)

(add-macro-alias FOO$RAW::out2 FOO$RAW::out2$)

(deflabel model-raw-end-of-defs)

(deftheory raw-tmp-names 'nil)

(deftheory
     model-raw-defs
     (union-theories
          (set-difference-theories (current-theory 'model-raw-end-of-defs)
                                   (current-theory 'model-raw-start-of-defs))
          (union-theories (theory 'loop-defs)
                          (theory 'clock-defs))))

(in-theory (set-difference-theories (current-theory :here)
                                    (theory 'model-raw-defs)))

