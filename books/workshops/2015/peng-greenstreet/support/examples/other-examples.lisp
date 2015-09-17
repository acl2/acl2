;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software


;; This file contains all examples appearing in the
;; workshop paper.
(in-package "ACL2")

(include-book "arithmetic/top" :dir :system)
(add-include-book-dir :cp "../")
(include-book "top" :dir :cp)
(tshell-ensure)


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

;; (defthm stop nil)

;; function expansion example
(defun fac (n)
  (if (or (<= n 0) (not (integerp n)))
      1
    (* n (fac (1- n)))))

(defthm test-lemma (implies  (and
                             (IMPLIES
                              (IF
                               (INTEGERP N)
                               (IF (EQUAL |var4| (FAC (BINARY-+ '-1 |var3|)))
                                   (NOT (< '2 N))
                                   'NIL)
                               'NIL)
                              (INTEGERP |var4|))
                            
                             (IMPLIES
                              (IF (INTEGERP N) (NOT (< '2 N)) 'NIL)
                              (<
                               ((LAMBDA
                                 (|var0|)
                                 (IF
                                  (IF (NOT (< '0 |var0|))
                                      (NOT (< '0 |var0|))
                                      (NOT (INTEGERP |var0|)))
                                  '1
                                  (BINARY-*
                                   |var0|
                                   ((LAMBDA
                                     (|var1|)
                                     (IF
                                      (IF (NOT (< '0 |var1|))
                                          (NOT (< '0 |var1|))
                                          (NOT (INTEGERP |var1|)))
                                      '1
                                      (BINARY-*
                                       |var1|
                                       ((LAMBDA
                                         (|var2|)
                                         (IF
                                          (IF (NOT (< '0 |var2|))
                                              (NOT (< '0 |var2|))
                                              (NOT (INTEGERP |var2|)))
                                          '1
                                          (BINARY-*
                                           |var2|
                                           ((LAMBDA
                                             (|var3|)
                                             (IF
                                              (IF (NOT (< '0 |var3|))
                                                  (NOT (< '0 |var3|))
                                                  (NOT (INTEGERP |var3|)))
                                              '1
                                              (BINARY-*
                                               |var3|
                                               (FAC (BINARY-+ '-1 |var3|)))))
                                            (BINARY-+ '-1 |var2|)))))
                                        (BINARY-+ '-1 |var1|)))))
                                    (BINARY-+ '-1 |var0|)))))
                                N)
                               '10)))
                            (IMPLIES (IF (INTEGERP N) (NOT (< '2 N)) 'NIL)
                                     (< (FAC N) '10))))

(defthm fac-thm
  (implies (and (and (integerp n))
                (and (<= n 1)))
           (< (+ (fac n) (fac (+ n 1))) 10))
  :hints
  (("Goal"
    :clause-processor
    (Smtlink clause
             '((:expand ((:functions ((fac integerp)))
                         (:expansion-level 4)))
               (:use ((:main (test-lemma)))))
             )))
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
