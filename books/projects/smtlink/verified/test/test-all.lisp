(in-package "SMT")
(include-book "../expand-cp")
(include-book "../type-inference")
(include-book "../reorder-hypotheses")
(ld "test-smtlink-hint.lisp")

(define test ((cl pseudo-term-listp)
              (hints smtlink-hint-p)
              state)
  :verify-guards nil
  (b* ((cl (pseudo-term-list-fix cl))
       (hints (smtlink-hint-fix hints))
       ((mv & expanded-term state) (expand-cp cl hints state))
       (- (cw "after expand-cp: ~q0" (cdr (car expanded-term))))
       (reordered-term
        (reorder-hypotheses-cp (cdr (car expanded-term)) hints))
       (- (cw "after reorder-hypotheses-cp: ~q0"
              (cdr (car reordered-term))))
       ((mv & term-with-type state)
        (type-judge-cp (cdr (car reordered-term)) hints state))
       (- (cw "after type-judge-cp: ~q0" (cdr (car term-with-type)))))
    (value (cadr (car term-with-type)))))

(defun term1 ()
  '(if (if (integerp x)
           (rationalp y)
         'nil)
       (not (< (binary-+ (binary-* x y) (binary-* x y))
               (binary-* '2 (binary-* x y))))
     't)
  )

(test (list (term1)) (my-hint) state)

(defun term2 ()
  '(if (if (integerp x)
           (rationalp y)
         'nil)
       (< (foo x y) '0)
     't)
  )

(test (list (term2)) (my-hint) state)

(defun term3 ()
  '(if (if (integerp x)
           (rationalp y)
         'nil)
       (< ((lambda (a b) (binary-+ a b)) x y) '0)
     't))

(test (list (term3)) (my-hint) state)

(defun term4 ()
  '(if (if (< x y)
           (if (integerp x)
               (rationalp y)
             'nil)
         'nil)
       (< (foo x y) '0)
     't)
  )

(test (list (term4)) (my-hint) state)
