#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "PATH")
(include-book "pm")

;; DAG -- for now we will import this globally.
(include-book "../util/iff")

;; jcd - bzo - I'd really like to work on removing this file.  It would be
;; better if we could come up with a unified theory rather than having to do
;; this kind of stuff.  It's especially bad when events in here enable the
;; recursive functions that we wanted to leave disabled.

;; Just not the right direction
(in-theory
 (disable
  path::clrp-of-nil-two
  PATH::CLRP-OF-SP
  PATH::SP-TO-CLRP
  PATH::SP-OF-SP
  PATH::SP-DOES-NOTHING
  PATH::SP-OF-SP-DIVERGE
  PATH::GP-OF-SP
  PATH::GP-OF-NON-CONSP
  ))

;; Introduce PATH::EFFECT-ON-SPOT
(in-theory
 (disable
  path::gp-of-mp-better
  path::mp-of-sp-when-not-dominated-by-some
  path::mp-of-sp
  ))

;; Expensive disjointness 
;; jcd Cheapened with a backchain limit, trying to leave enabled
;; (in-theory
;;  (disable
;;   PATH::DOMINATES-WHEN-NOT-DIVERGE-AND-NOT-DOMINATES
;;   ))

;; Introduces nthcdr
(in-theory
 (disable
  ;path::gp-of-sp-subpath-case-one
  ;path::gp-of-sp-subpath-case-two
  path::sp-of-sp-dominating-case-two
  path::gp-of-mp-when-dominated-by-some-all-diverge
  path::gp-of-mp-all-diverge
  path::gp-of-mp-when-dominated-by-some
  path::gp-of-mp
  PATH::DOMINATES-MEANS-NOT-DIVERGE-ALT
  PATH::GP-OF-MP-WHEN-P-DOMINATES
  LIST::MEMBERP-OF-CONS-IRREL
  LIST::MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP
  PATH::NOT-DIVERGES-FROM-ALL-WHEN-MEMBERP

  PATH::DIVERGE-WHEN-FIRSTNS-DIVERGE
  PATH::DIVERGE-FROM-ALL-DIVERGE-AND-UNIQUE-MEMBERPS
  PATH::DIVERGE-WHEN-ALL-DIVERGE-FROM-ALL-AND-MEMBERP-AND-MEMBERP-ALT
  PATH::DIVERGE-WHEN-ALL-DIVERGE-FROM-ALL-AND-MEMBERP-AND-MEMBERP

;; jcd these got renamed
;  PATH::DIVERGE-FROM-MEMBERP-AND-DIVERGES-FROM-ALL-FOUR
;  PATH::DIVERGE-FROM-MEMBERP-AND-DIVERGES-FROM-ALL-THREE
;  PATH::DIVERGE-FROM-MEMBERP-AND-DIVERGES-FROM-ALL-TWO
  PATH::DIVERGE-WHEN-MEMBERP-AND-DIVERGES-FROM-ALL-FOUR
  PATH::DIVERGE-WHEN-MEMBERP-AND-DIVERGES-FROM-ALL-THREE
  PATH::DIVERGE-WHEN-MEMBERP-AND-DIVERGES-FROM-ALL-TWO

  PATH::DIVERGE-WHEN-MEMBERP-AND-DIVERGES-FROM-ALL-ONE
;jcd removed this  PATH::DIVEREG-WHEN-DOMINATE-DIVERGENT

;; jcd this got renamed  PATH::DIVERGE-WHEN-DIVERGE-WITH-DOMINATOR-ALT
;; why are we disabling this but not the other rules?  maybe it should
;; just be left enabled?
  PATH::DIVERGE-WHEN-DIVERGE-WITH-DOMINATOR-ONE-ALT

  PATH::DIVERGE-OF-NON-CONSP-TWO
  PATH::DIVERGE-OF-NON-CONSP-ONE
  PATH::TWO-DOMINATORS-CANNOT-DIVERGE

  PATH::SP-OF-SP-DOMINATING-CASE-ONE
;;  LIST::EQUAL-OF-IF-HACK
;;  PATH::FIRST-DOMINATOR-WHEN-P-DOMINATES-IT-YUCK
  PATH::DIVERGES-FROM-WHEN-NOT-STRICTLY-DOMINATED-BY-SOME-AND-NOT-DOMINATES-SOME
  ;PATH::SP-OF-NON-CONSP
  ))


;; This is introduced and must simplify
;; bzo we have rules about this now... maybe we should disable it?
(in-theory (enable nthcdr))


(in-theory
 (disable
  PATH::DIVERGES-FROM-ALL-WHEN-NO-DOMINATION-ALT
  PATH::NOT-STRICTLY-DOMINATED-BY-SOME-WHEN-DIVERGES-FROM-ALL
  PATH::DIVERGES-FROM-ALL-WHEN-NO-DOMINATION
  PATH::NOT-DOMINATED-BY-SOME-WHEN-DIVERGES-FROM-ALL

;; jcd renamed this  PATH::DIVERGE-WHEN-DIVERGE-WITH-DOMINATOR
  PATH::DIVERGE-WHEN-DIVERGE-WITH-DOMINATOR-ONE
  ))

(in-theory
 (e/d (path::keys)
      (path::keys-of-cdr)))

(in-theory
 (disable
  PATH::DIVERGES-FROM-ALL-WHEN-DOMINATED
  PATH::DIVERGES-FROM-ALL-OF-NON-CONSP-ONE

;jcd these got renamed
;  PATH::DIVERGES-FROM-ALL-WHEN-DIVERGES-FROM-ALL-AND-SUBBAGP
;  PATH::DIVERGES-FROM-ALL-WHEN-DIVERGES-FROM-ALL-AND-SUBBAGP-ALT
  PATH::diverges-from-all-by-subbagp-one
  PATH::diverges-from-all-by-subbagp-two

  PATH::DIVERGES-FROM-ALL-OF-NON-CONSP-TWO
  PATH::MP-OF-NON-CONSP
  PATH::ALL-DIVERGE-WHEN-MEMBERP-NIL
;; jcd this got renamed  PATH::ALL-DIVERGE-WHEN-ALL-DIVERGE-AND-SUBBAGP
  PATH::all-diverge-when-subbag
  ))

;; jcd removed this entirely
;; (in-theory
;;  (disable
;;   PATH::DIVERGE-OF-CONS-AND-CONS
;;   ))

(in-theory
 (disable
  PATH::ALL-DIVERGE-FROM-ALL-CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS-IMPLIES-DIVERGE
  PATH::CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS
  PATH::CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS-APPEND-1
;;  LIST::LEN-FW-TO-CONSP
  LIST::LEN-OF-NON-CONSP
  LIST::APPEND-OF-NON-CONSP-ONE
  LIST::APPEND-OF-NON-CONSP-2
  ))

(in-theory
 (disable
  PATH::DOMINATES-OF-NON-CONSP-TWO
  PATH::DOMINATES-OF-NON-CONSP-ONE
;; jcd removed this  PATH::DOMINATES-OF-CONS-AND-CONS
  PATH::DOMINATES-OF-APPEND-TWO-ONE
  PATH::DOMINATES-OF-SINGLETON-TWO
  PATH::DOMINATES-OF-APPEND-AND-APPEND
  PATH::DOMINATES-TRANSITIVE-ONE
  PATH::EQUAL-PRUNE-LEN-IMPLIES-DOMINATION
;; jcd renamed this PATH::TWO-DOMINATORS-HACK
  PATH::linear-domination-hierarchy

  PATH::DOMINATES-TRANSITIVE-THREE
  PATH::DOMINATES-FROM-DOMINATES-OF-NTHCDR-ETC
  ))

(in-theory
 (disable
  PATH::DIVERGE-TAIL-DOMINATOR-BODY-BODY-REC-IMPLIES-DIVERGE
;; jcd renamed this  PATH::DIVERGE-COMMUTATIVE
  PATH::DIVERGE-SYMMETRIC
  PATH::ALL-DIVERGE-FROM-ALL-TAIL-DOMINATOR-BODY-IMPLIES-DIVERGE
  ))

#+joe
(in-theory
 (disable
  PATH::GP-OF-USE
  ))

(in-theory
 (disable
  PATH::GP-OF-SP-SUBPATH-CASE-ONE
  PATH::GP-OF-SP-SUBPATH-CASE-TWO
  ;PATH::GP-OF-DEF
  ))

(in-theory
 (disable
  ;jcd - removed this theorem entirely - PATH::OPEN-DIVERGES-FROM-ALL
  DIVERGES-FROM-ALL
  PATH::DIVERGE-OF-APPEND-FROM-DIVERGE-ONE
  PATH::DIVERGE-OF-APPEND-FROM-DIVERGE-TWO
  PATH::DIVERGE-OF-APPEND-AND-APPEND
  path::sp-of-non-consp
  ;PATH::OPEN-USE
  ;PATH::OPEN-DEFS
  ))

;; We don't yet have the cp infrastructure ..

(in-theory
 (disable
  PATH::MP-OF-SP-WHEN-DIVERGES-FROM-ALL
  PATH::GP-OF-MP-DIVERGES-FROM-ALL-CASE
  ))

(in-theory
 (enable
  mp
  ))

(in-theory
 (enable
  sp==r
  ))

;; jcd - bzo - this seems bad!
(in-theory
 (enable
  dominated-by-some
  diverges-from-all
  ))

(in-theory
 (e/d
  (
   member
   )
  (
   ;; JCD - updated these
   LIST::member-is-memberp-propositionally
   LIST::member-eq-is-memberp-propositionally
   LIST::member-equal-is-memberp-propositionally
   ;; REDUCE-MEMBERX-TO-MEMBERP
   )))

(in-theory
 (disable
  g-to-gp
  s-to-sp
  ))
