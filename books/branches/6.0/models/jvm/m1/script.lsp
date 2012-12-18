; % (time acl2 < script.lisp) > script.log
; or
; ACL2 !>(ld "script.lisp" :ld-pre-eval-print t)

(defpkg "M1"
  (set-difference-eq (union-eq *acl2-exports*
                               *common-lisp-symbols-from-main-lisp-package*)
                     '(push pop pc program step
                            nth update-nth nth-update-nth)))

(certify-book "m1" 1)
(u)
(u)

; This is just an illustration of the capability of m1.lisp.
(include-book "m1")

(certify-book "template" 1)
(u)
(certify-book "sum" 1)
(u)
(certify-book "sumsq" 1)
(u)
(certify-book "fact" 1)
(u)
(certify-book "power" 1)
(u)
(certify-book "expt" 1)
(u)
(certify-book "alternating-sum" 1)
(u)
(certify-book "alternating-sum-variant" 1)
(u)
(certify-book "fib" 1)
(u)
(certify-book "lessp" 1)
(u)
(certify-book "even-solution-1" 1)
(u)
(certify-book "even-solution-2" 1)
(u)
(certify-book "sign" 1)
(u)
(certify-book "div" 1)
(u)
(certify-book "bexpt" 1)
(u)
(certify-book "magic" 1)
(u)
(certify-book "funny-fact" 1)
(u)
(certify-book "wormhole-abstraction" 1)
(u)
(u)

; Beginning of Turing Equivalence proofs

; Reduce tmi to tmi3
(include-book "m1")
(certify-book "tmi-reductions" 1)
(u)
(u)

(include-book "m1")
(certify-book "defsys-utilities" 1)
(u)
(u)

(include-book "defsys-utilities")
(certify-book "defsys" 1)
(u)
(u)

; Test defsys
(include-book "defsys")
(certify-book "low-seven" 1)
(u)
(u)

(include-book "tmi-reductions")
(certify-book "implementation" 1)
(u)
(u)

(include-book "m1")
(certify-book "theorems-a-and-b" 1)
(u)
(u)

(include-book "theorems-a-and-b")
(certify-book "find-k!" 1)
(u)
(u)
