; top.lisp
;
; Includes, in dependency order, every book in this verification.
; Certifying this book certifies (transitively) all the others and
; confirms the whole chain loads with no errors from a clean state.
;
;   cert.pl top
;
; Requires ACL2 with the standard community books available (uses
; arithmetic-5/top :dir :system).

(in-package "ACL2")

(include-book "00-complex-vectors")
(include-book "01-euler-identities")
(include-book "02-roots-of-unity")
(include-book "03-zeta-deduction")
(include-book "04-collapse-lemma")
(include-book "05-torque-sign-correction")
(include-book "06-generic-omega-collapse")
(include-book "07-inductance-note")
