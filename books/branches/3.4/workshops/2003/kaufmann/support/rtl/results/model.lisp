(in-package "ACL2")

(include-book "../../../../../ordinals/e0-ordinal")

(set-well-founded-relation e0-ord-<)

(set-inhibit-warnings "THEORY" "DISABLE" "NON-REC")

(include-book "common")

(include-book "model-macros")

(set-irrelevant-formals-ok t)

(set-ignore-ok t)

(deflabel model-start-of-defs)

(set-bogus-mutual-recursion-ok t)

(MUTUAL-RECURSION

(defun out2$ (n $path)
       (declare (xargs :normalize nil
                       :measure (cons (1+ (nfix n)) 0)))
       (if (zp n)
           (reset 'out2 4)
           (bits (+ 1 (ww (+ -1 n))) 3 0)))

(defun out1$ (n $path)
       (declare (xargs :normalize nil
                       :measure (cons (1+ (nfix n)) 1)))
       (cond1 ((log= 0 (sel n)) (in0 n))
              ((log= 1 (sel n)) (in1 n))
              ((log= 2 (sel n)) (in2 n))
              ((log= 3 (sel n)) (in3 n))
              (t 0)))

)

(add-macro-alias out1 out1$)

(add-macro-alias out2 out2$)

(deflabel model-end-of-defs)

(deftheory tmp-names 'nil)

(deftheory
 model-defs
 (union-theories (set-difference-theories (current-theory 'model-end-of-defs)
                                          (current-theory 'model-start-of-defs))
                 (union-theories (theory 'loop-defs)
                                 (theory 'clock-defs))))

(in-theory (set-difference-theories (current-theory :here)
                                    (theory 'model-defs)))

