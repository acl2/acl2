;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software


;; This file contains all examples appearing in the
;; workshop paper.
(in-package "ACL2")

(include-book "arithmetic/top" :dir :system)
(include-book "../top")
(value-triple (tshell-ensure))


;; 2.1 A simple example
(defthm A-simple-example
  (implies (and (and (rationalp x)
                     (rationalp y))
                (and (>= x 2)
                     (<= y -2)))
           (>= (+ (* x x) (* y y)) 4))
  :hints (("Goal"
           :clause-processor
           (Smtlink clause '() )
           ))
  )

;; 2.2 User defined functions
(defun udf-func (a b) (+ (* a a) (* b b)))

(defthm User-defined-functions-2
  (implies (and (and (rationalp x)
                     (rationalp y))
                (and (>= x 2)
                     (<= y -2)))
           (>=  (udf-func (+ x 1) (- y 1)) 9))
  :hints (("Goal"
           :clause-processor
           (Smtlink clause
                    '((:expand ((:functions ((udf-func rationalp)))
                                (:expansion-levels 1)))
                      )
                    )
           ))
  )


;; 2.3 User supplied substitutions and hypothesis
(defthm User-supplied-substitution-&-hypothesis
    (implies (and (and (rationalp a)
                       (rationalp b)
                       (rationalp gamma)
                       (integerp m)
                       (integerp n))
                  (and (> gamma 0)
                       (< gamma 1)
                       (> m 0)
                       (< m n)))
             (>= (* (expt gamma m) (- (* (+ a b) (+ a b)) (* 2 a b)))
                 (* (expt gamma n) (* 2 a b))))
  :hints
  (("Goal"
    :clause-processor
    (Smtlink clause
	     '((:let ((expt_gamma_m (expt gamma m) rationalp)
		      (expt_gamma_n (expt gamma n) rationalp)))
	       (:hypothesize ((< expt_gamma_n expt_gamma_m)
			      (> expt_gamma_m 0)
			      (> expt_gamma_n 0)))
	       )
	     ))))


;; 2.4 Nested hints
;; See Section 2.2 User defined functions under function expansion

;; 2.5 Uinterpreted functions
(local
 (progn
   (defun my-smtlink-expt-config ()
     (declare (xargs :guard t))
     (change-smtlink-config *default-smtlink-config*
        :dir-interface
        "../z3_interface"
			  :SMT-module
			  "RewriteExpt"
			  :SMT-class
			  "to_smt_w_expt"
        ))
   (defattach smt-cnf my-smtlink-expt-config)))

(defthm Uninterpreted-function
  (implies (and (and (rationalp x)
                     (integerp n))
                (and (> x 0)))
           (> (expt x n) 0))
  :hints
  (("Goal"
    :clause-processor
    (Smtlink-custom-config clause
             '((:uninterpreted-functions ((expt rationalp integerp rationalp))))
             )))
  )

;; Under construction ...
;; I want to come up with more examples to show Smtlink's capabilities.
;; For example, what counter-examples it can provide,
;; what other features or difficult theorems it can handle.
