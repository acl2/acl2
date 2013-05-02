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

