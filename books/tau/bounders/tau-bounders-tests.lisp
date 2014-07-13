(in-package "ACL2")
(include-book "ihs/basic-definitions" :dir :system)

; Original "elementary-bounders" does not prove test-expt and test-expt2
; Modified  "elementary-bounders" does prove.
(include-book "tau/bounders/elementary-bounders" :dir :system)

(defthm tau-bounders-test-expt2
  (implies
   (and (natp w) (> w 2))
   (>= (expt2 (* w w)) 512)))

(defthm tau-bounders-test-expt
  (implies
   (and (integerp w) (< w 2))
   (>= (/ (+ 1 (expt 2 w)))  1/3)))
