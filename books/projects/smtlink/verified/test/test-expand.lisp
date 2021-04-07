(in-package "SMT")
(include-book "../expand-cp")
(ld "test-smtlink-hint.lisp")

(set-guard-checking :none)

(defun term ()
  '(if (if (integerp x)
           (rationalp y)
         'nil)
       (< (foo x y) '0)
     't)
  )

(expand-cp (list (term)) (my-hint) state)

(defun term2 ()
  '(if (if (integerp x)
           (rationalp y)
         'nil)
       (< ((lambda (a b) (binary-+ a b)) x y) '0)
     't))

(expand-cp (list (term2)) (my-hint) state)

(defun term3 ()
  '(if (if (< x y)
           (if (integerp x)
               (rationalp y)
             'nil)
         'nil)
       (< (foo x y) '0)
     't)
  )

(expand-cp (list (term3)) (my-hint) state)
