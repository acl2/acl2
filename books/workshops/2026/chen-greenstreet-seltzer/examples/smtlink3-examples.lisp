;; Copyright (C) 2026, The University of British Columbia
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2


(in-package "ACL2")
(include-book "hints/hint-wrapper" :dir :system)
(include-book "smtlink3-hint")

(value-triple (tshell-ensure))
(add-default-hints '((hint-wrapper-hint clause)))
(add-default-hints '((SMT::SMT-computed-hint clause)))

;; Nonlinear Inequality
(defun x^2-y^2 (x y)
  (- (* x x) (* y y)))

(defthm poly-ineq-example
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (<= (+ (* (/ 9 8) x x) (* y y)) 1)
                (<= (x^2-y^2 x y) 1))
           (< y
              (- (* 3 (- x (/ 17 8)) (- x (/ 17 8)))
                 3)))
  :hints (("Goal''" :smtlink
                    (:translation-theory
                     (union-theories
                       (theory 'minimal-theory)
                       '(smt::return-of-rational-+
                         smt::return-of-rational--
                         smt::return-of-rational-*
                         smt::return-of-rational-/
                         smt::return-of-rational-<
                         smt::specialize-binary-rational-operators
                         smt::specialize-unary-rational-
                         smt::specialize-unary-rational-/))))))

(acl2::must-fail
  (defthm poly-ineq-example-bad
    (implies (and (real/rationalp x)
                  (real/rationalp y)
                  (<= (+ (* (/ 9 8) x x) (* y y)) 1)
                  (<= (x^2-y^2 x y) 1))
             (< y
                (- (* 3 (- x (/ 13 8)) (- x (/ 13 8)))
                   3)))
    :hints (("Goal''" :smtlink
                      (:translation-theory
                       (union-theories
                         (theory 'minimal-theory)
                         '(smt::return-of-rational-+
                           smt::return-of-rational--
                           smt::return-of-rational-*
                           smt::return-of-rational-/
                           smt::return-of-rational-<
                           smt::specialize-binary-rational-operators
                           smt::specialize-unary-rational-
                           smt::specialize-unary-rational-/)))))))

;; Alists
(encapsulate nil
  (local (in-theory (disable assoc-equal)))

  (defthm alist-example
    (implies (and (natp k1)
                  (natp k2)
                  (symbolp v1)
                  (symbolp v2)
                  (smt::int-sym-alist-p al)
                  (not (equal k1 k2)))
             (equal (assoc-equal k2
                                 (cons (cons k1 v1)
                                       (cons (cons k2 v2) al)))
                    (cons k2 v2)))
    :hints (("Goal'" :smtlink-custom
                     (:global-hint :int-sym-arrays
                      :translation-theory
                      (union-theories
                        (theory 'minimal-theory)
                        '(smt::return-of-int-sym-consp
                          smt::return-of-int-sym-alist-p
                          smt::return-of-cons-int-sym
                          smt::return-of-cons-int-sym-consp-int-sym-alist-p
                          smt::return-of-cons-int-sym-consp-nil
                          smt::return-of-assoc-equal-int-sym-alist-p
                          smt::return-of-equal-maybe-int-sym-consp-int-sym-consp
                          smt::int-sym-top-down-translation-of-assoc-equal
                          smt::int-sym-top-down-translation-of-acons
                          smt::int-sym-top-down-translation-of-nil
                          smt::return-of-integer-+
                          smt::return-of-integer--
                          smt::return-of-integer-*
                          smt::return-of-integer-<
                          smt::specialize-binary-integer-operators
                          smt::specialize-unary-integer-)))))))
