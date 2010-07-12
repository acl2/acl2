(in-package "ACL2")

(set-inhibit-warnings "THEORY" "DISABLE" "NON-REC")

(include-book "../../../../../rtl/rel4/lib/rtl")

(include-book "../../../../../rtl/rel4/lib/rtlarr")

(include-book "../../../../../rtl/rel4/lib/util")

(include-book "../../../../../misc/symbol-btree")

(include-book "../../../../../misc/rtl-untranslate")

(deftheory rtl-operators-after-macro-expansion
           *rtl-operators-after-macro-expansion*)

(local
  (in-theory
       (set-difference-theories (current-theory :here)
                                (theory 'rtl-operators-after-macro-expansion))))

(defmacro ww (n) (list 'ww$ n '$path))

(defmacro sel (n) (list 'sel$ n '$path))

(defmacro in3 (n) (list 'in3$ n '$path))

(defmacro in2 (n) (list 'in2$ n '$path))

(defmacro in1 (n) (list 'in1$ n '$path))

(defmacro in0 (n) (list 'in0$ n '$path))

(ENCAPSULATE
 (
  (ww$ (n $path) t)

  (sel$ (n $path) t)

  (in3$ (n $path) t)

  (in2$ (n $path) t)

  (in1$ (n $path) t)

  (in0$ (n $path) t)

 )

 (local (defun ww$ (n $path)
               (declare (ignore n $path))
               0))

 (local (defun sel$ (n $path)
               (declare (ignore n $path))
               0))

 (local (defun in3$ (n $path)
               (declare (ignore n $path))
               0))

 (local (defun in2$ (n $path)
               (declare (ignore n $path))
               0))

 (local (defun in1$ (n $path)
               (declare (ignore n $path))
               0))

 (local (defun in0$ (n $path)
               (declare (ignore n $path))
               0))

 (defbvecp ww (n) 3)

 (defbvecp sel (n) 2)

 (defbvecp in3 (n) 1)

 (defbvecp in2 (n) 1)

 (defbvecp in1 (n) 1)

 (defbvecp in0 (n) 1)

)

(add-macro-alias ww ww$)

(add-macro-alias sel sel$)

(add-macro-alias in3 in3$)

(add-macro-alias in2 in2$)

(add-macro-alias in1 in1$)

(add-macro-alias in0 in0$)

(deflabel start-of-loop-defs)

(set-ignore-ok t)

(set-irrelevant-formals-ok t)

(deflabel end-of-loop-defs)

(deflabel start-of-clock-defs)

(defun clk (n)
  (declare (ignore n))
  1)

(deflabel end-of-clock-defs)

(deftheory loop-defs
           (set-difference-theories (current-theory 'end-of-loop-defs)
                                    (current-theory 'start-of-loop-defs)))

(deftheory
    clock-defs
    (set-difference-theories
         (union-theories (function-theory 'end-of-clock-defs)
                         (executable-counterpart-theory 'end-of-clock-defs))
         (union-theories (function-theory 'start-of-clock-defs)
                         (executable-counterpart-theory 'start-of-clock-defs))))

(table rtl-tbl 'sigs-btree
       (symbol-alist-to-btree
            (dollar-alist '(ww sel in3 in2 in1 in0
                               out1 FOO$RAW::OUT1 out2 FOO$RAW::OUT2)
                          nil)))

