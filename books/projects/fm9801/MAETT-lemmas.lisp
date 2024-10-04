;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; MAETT-lemmas.lisp
; Author  Jun Sawada, University of Texas at Austin
;
;  This book combines the results of MAETT-lemmas1.lisp and
;  and MAETT-lemmas2.lisp.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package "ACL2")

(include-book "MA2-lemmas")
(include-book "invariants-def")

(deflabel begin-MAETT-lemmas)
(include-book "MAETT-lemmas1")
(include-book "MAETT-lemmas2")
