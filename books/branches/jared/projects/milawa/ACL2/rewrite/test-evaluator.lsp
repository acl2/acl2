(in-package "MILAWA")
(include-book "evaluator")
(include-book "../builders/evaluator")

(defconst *fib*
  (pequal '(fib x)
          '(if (zp x)
               '1
             (if (equal x '1)
                 '1
               (+ (fib (- x '1))
                  (fib (- x '2)))))))

(defconst *zp*
  (pequal '(zp x)
          '(if (natp x)
               (equal x '0)
             't)))

(defconst *<=*
  (pequal '(<= x y)
          '(not (< y x))))

(defconst *not*
  (pequal '(not p)
          '(if p 'nil 't)))

(defconst *defs*
  (list *fib* *zp* *<=* *not*))


(ACL2::time$ (ACL2::prog2$ (generic-evaluator '(fib '19) *defs* 25) nil))      ;; 0.70 seconds
(ACL2::time$ (ACL2::prog2$ (generic-evaluator-bldr '(fib '19) *defs* 25) nil)) ;; 9.66 seconds


(conclusion (generic-evaluator-bldr '(fib '2) *defs* 25))
(rank (generic-evaluator-bldr '(fib  '0) *defs* 25)) ;; 5,858
(rank (generic-evaluator-bldr '(fib  '1) *defs* 25)) ;; 8,255
(rank (generic-evaluator-bldr '(fib  '2) *defs* 25)) ;; 25,385         (originally 790 million)
(rank (generic-evaluator-bldr '(fib  '5) *defs* 25)) ;; 137,753
(rank (generic-evaluator-bldr '(fib '10) *defs* 25)) ;; 1,645,133
(rank (generic-evaluator-bldr '(fib '15) *defs* 25)) ;; 18,358,208
(rank (generic-evaluator-bldr '(fib '16) *defs* 25)) ;; 29,711,177
(rank (generic-evaluator-bldr '(fib '17) *defs* 25)) ;; 48,080,657
(rank (generic-evaluator-bldr '(fib '18) *defs* 25)) ;; 77,803,106
(rank (generic-evaluator-bldr '(fib '19) *defs* 25)) ;; 125,895,035

;; cons space exhausted (with 131,072 max pages)
(rank (generic-evaluator-bldr '(fib '20) *defs* 25))

;; (ACL2::trace$ (transitivity-of-pequal-bldr
;;                :entry (list (equal (get-conclusion (first acl2::arglist))
;;                                    (get-conclusion (second acl2::arglist))))
;;                :exit nil))

