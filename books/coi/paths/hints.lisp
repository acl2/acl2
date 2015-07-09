; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.

(in-package "CPATH")
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
  cpath::clrp-of-nil-two
  CPATH::CLRP-OF-SP
  CPATH::SP-TO-CLRP
  CPATH::SP-OF-SP
  CPATH::SP-DOES-NOTHING
  CPATH::SP-OF-SP-DIVERGE
  CPATH::GP-OF-SP
  CPATH::GP-OF-NON-CONSP
  ))

;; Introduce CPATH::EFFECT-ON-SPOT
(in-theory
 (disable
  cpath::gp-of-mp-better
  cpath::mp-of-sp-when-not-dominated-by-some
  cpath::mp-of-sp
  ))

;; Expensive disjointness
;; jcd Cheapened with a backchain limit, trying to leave enabled
;; (in-theory
;;  (disable
;;   CPATH::DOMINATES-WHEN-NOT-DIVERGE-AND-NOT-DOMINATES
;;   ))

;; Introduces nthcdr
(in-theory
 (disable
  ;cpath::gp-of-sp-subpath-case-one
  ;cpath::gp-of-sp-subpath-case-two
  cpath::sp-of-sp-dominating-case-two
  cpath::gp-of-mp-when-dominated-by-some-all-diverge
  cpath::gp-of-mp-all-diverge
  cpath::gp-of-mp-when-dominated-by-some
  cpath::gp-of-mp
  CPATH::DOMINATES-MEANS-NOT-DIVERGE-ALT
  CPATH::GP-OF-MP-WHEN-P-DOMINATES
  LIST::MEMBERP-OF-CONS-IRREL
  LIST::MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP
  CPATH::NOT-DIVERGES-FROM-ALL-WHEN-MEMBERP

  CPATH::DIVERGE-WHEN-FIRSTNS-DIVERGE
  CPATH::DIVERGE-FROM-ALL-DIVERGE-AND-UNIQUE-MEMBERPS
  CPATH::DIVERGE-WHEN-ALL-DIVERGE-FROM-ALL-AND-MEMBERP-AND-MEMBERP-ALT
  CPATH::DIVERGE-WHEN-ALL-DIVERGE-FROM-ALL-AND-MEMBERP-AND-MEMBERP

;; jcd these got renamed
;  CPATH::DIVERGE-FROM-MEMBERP-AND-DIVERGES-FROM-ALL-FOUR
;  CPATH::DIVERGE-FROM-MEMBERP-AND-DIVERGES-FROM-ALL-THREE
;  CPATH::DIVERGE-FROM-MEMBERP-AND-DIVERGES-FROM-ALL-TWO
  CPATH::DIVERGE-WHEN-MEMBERP-AND-DIVERGES-FROM-ALL-FOUR
  CPATH::DIVERGE-WHEN-MEMBERP-AND-DIVERGES-FROM-ALL-THREE
  CPATH::DIVERGE-WHEN-MEMBERP-AND-DIVERGES-FROM-ALL-TWO

  CPATH::DIVERGE-WHEN-MEMBERP-AND-DIVERGES-FROM-ALL-ONE
;jcd removed this  CPATH::DIVEREG-WHEN-DOMINATE-DIVERGENT

;; jcd this got renamed  CPATH::DIVERGE-WHEN-DIVERGE-WITH-DOMINATOR-ALT
;; why are we disabling this but not the other rules?  maybe it should
;; just be left enabled?
  CPATH::DIVERGE-WHEN-DIVERGE-WITH-DOMINATOR-ONE-ALT

  CPATH::DIVERGE-OF-NON-CONSP-TWO
  CPATH::DIVERGE-OF-NON-CONSP-ONE
  CPATH::TWO-DOMINATORS-CANNOT-DIVERGE

  CPATH::SP-OF-SP-DOMINATING-CASE-ONE
;;  LIST::EQUAL-OF-IF-HACK
;;  CPATH::FIRST-DOMINATOR-WHEN-P-DOMINATES-IT-YUCK
  CPATH::DIVERGES-FROM-WHEN-NOT-STRICTLY-DOMINATED-BY-SOME-AND-NOT-DOMINATES-SOME
  ;CPATH::SP-OF-NON-CONSP
  ))


;; This is introduced and must simplify
;; bzo we have rules about this now... maybe we should disable it?
(in-theory (enable nthcdr))


(in-theory
 (disable
  CPATH::DIVERGES-FROM-ALL-WHEN-NO-DOMINATION-ALT
  CPATH::NOT-STRICTLY-DOMINATED-BY-SOME-WHEN-DIVERGES-FROM-ALL
  CPATH::DIVERGES-FROM-ALL-WHEN-NO-DOMINATION
  CPATH::NOT-DOMINATED-BY-SOME-WHEN-DIVERGES-FROM-ALL

;; jcd renamed this  CPATH::DIVERGE-WHEN-DIVERGE-WITH-DOMINATOR
  CPATH::DIVERGE-WHEN-DIVERGE-WITH-DOMINATOR-ONE
  ))

(in-theory
 (e/d (cpath::keys)
      (cpath::keys-of-cdr)))

(in-theory
 (disable
  CPATH::DIVERGES-FROM-ALL-WHEN-DOMINATED
  CPATH::DIVERGES-FROM-ALL-OF-NON-CONSP-ONE

;jcd these got renamed
;  CPATH::DIVERGES-FROM-ALL-WHEN-DIVERGES-FROM-ALL-AND-SUBBAGP
;  CPATH::DIVERGES-FROM-ALL-WHEN-DIVERGES-FROM-ALL-AND-SUBBAGP-ALT
  CPATH::diverges-from-all-by-subbagp-one
  CPATH::diverges-from-all-by-subbagp-two

  CPATH::DIVERGES-FROM-ALL-OF-NON-CONSP-TWO
  CPATH::MP-OF-NON-CONSP
  CPATH::ALL-DIVERGE-WHEN-MEMBERP-NIL
;; jcd this got renamed  CPATH::ALL-DIVERGE-WHEN-ALL-DIVERGE-AND-SUBBAGP
  CPATH::all-diverge-when-subbag
  ))

;; jcd removed this entirely
;; (in-theory
;;  (disable
;;   CPATH::DIVERGE-OF-CONS-AND-CONS
;;   ))

(in-theory
 (disable
  CPATH::ALL-DIVERGE-FROM-ALL-CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS-IMPLIES-DIVERGE
  CPATH::CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS
  CPATH::CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS-APPEND-1
;;  LIST::LEN-FW-TO-CONSP
  LIST::LEN-OF-NON-CONSP
  LIST::APPEND-OF-NON-CONSP-ONE
  LIST::APPEND-OF-NON-CONSP-2
  ))

(in-theory
 (disable
  CPATH::DOMINATES-OF-NON-CONSP-TWO
  CPATH::DOMINATES-OF-NON-CONSP-ONE
;; jcd removed this  CPATH::DOMINATES-OF-CONS-AND-CONS
  CPATH::DOMINATES-OF-APPEND-TWO-ONE
  CPATH::DOMINATES-OF-SINGLETON-TWO
  CPATH::DOMINATES-OF-APPEND-AND-APPEND
  CPATH::DOMINATES-TRANSITIVE-ONE
  CPATH::EQUAL-PRUNE-LEN-IMPLIES-DOMINATION
;; jcd renamed this CPATH::TWO-DOMINATORS-HACK
  CPATH::linear-domination-hierarchy

  CPATH::DOMINATES-TRANSITIVE-THREE
  CPATH::DOMINATES-FROM-DOMINATES-OF-NTHCDR-ETC
  ))

(in-theory
 (disable
  CPATH::DIVERGE-TAIL-DOMINATOR-BODY-BODY-REC-IMPLIES-DIVERGE
;; jcd renamed this  CPATH::DIVERGE-COMMUTATIVE
  CPATH::DIVERGE-SYMMETRIC
  CPATH::ALL-DIVERGE-FROM-ALL-TAIL-DOMINATOR-BODY-IMPLIES-DIVERGE
  ))

#+joe
(in-theory
 (disable
  CPATH::GP-OF-USE
  ))

(in-theory
 (disable
  CPATH::GP-OF-SP-SUBPATH-CASE-ONE
  CPATH::GP-OF-SP-SUBPATH-CASE-TWO
  ;CPATH::GP-OF-DEF
  ))

(in-theory
 (disable
  ;jcd - removed this theorem entirely - CPATH::OPEN-DIVERGES-FROM-ALL
  DIVERGES-FROM-ALL
  CPATH::DIVERGE-OF-APPEND-FROM-DIVERGE-ONE
  CPATH::DIVERGE-OF-APPEND-FROM-DIVERGE-TWO
  CPATH::DIVERGE-OF-APPEND-AND-APPEND
  cpath::sp-of-non-consp
  ;CPATH::OPEN-USE
  ;CPATH::OPEN-DEFS
  ))

;; We don't yet have the cp infrastructure ..

(in-theory
 (disable
  CPATH::MP-OF-SP-WHEN-DIVERGES-FROM-ALL
  CPATH::GP-OF-MP-DIVERGES-FROM-ALL-CASE
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
