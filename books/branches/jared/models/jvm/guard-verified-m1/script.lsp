; % (time acl2 < script.lsp) > script.log
; or
; acl2
; ACL2 !>(ld "script.lsp" :ld-pre-eval-print t)

; -----------------------------------------------------------------
; Section 1:  The M1 Machine

(certify-book "use-when")
(u)

(defpkg "M1"
  (set-difference-eq (union-eq *acl2-exports*
                               *common-lisp-symbols-from-main-lisp-package*)
                     '(push pop pc program step)))

(certify-book "good-statep" 1)
(u)
(u)

(include-book "good-statep")
(certify-book "m1" 1)
(u)
(u)

(include-book "m1")
(certify-book "verify-guards" 1)
(u)
(u)

; -----------------------------------------------------------------
; Section 2: Verifying Simple M1 Programs

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

; -----------------------------------------------------------------
; Section 3:  Turing Equivalence of M1

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

(include-book "defsys")
(certify-book "low-seven" 1) ; irrelevant to Turing Equivalence goal
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
