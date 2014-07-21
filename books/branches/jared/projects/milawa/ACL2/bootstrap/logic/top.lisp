; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
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
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")

(include-book "arities-okp")
(include-book "appeal-identity")
(include-book "base-evaluator")
(include-book "disjoin-formulas")
(include-book "find-proof")
(include-book "formula-size")
(include-book "formulas")
(include-book "fterm-lists")
(include-book "functional-axiom")
(include-book "groundp")
(include-book "negate-formulas")
(include-book "negate-term")
;; Stupid file, don't implement (include-book "pand")
;; Never used, probably don't care? (include-book "patmatch-formula")
(include-book "patmatch-term")
(include-book "pequal-list")
;; Stupid file, don't implement (include-book "piff")
(include-book "por-list")
(include-book "proofp")
(include-book "quote-range")
(include-book "replace-subterm")
(include-book "substitute-formula")
(include-book "substitute-term")
(include-book "subtermp")
;; Probably don't care?  (include-book "termination")
(include-book "term-formula")
(include-book "term-order")
(include-book "terms")
;; ACL2-specific, move elsewhere? (include-book "trace-proofp")
;; Probably don't care? (include-book "translate")
;; Probably don't care? (include-book "translate-sigma")



(%create-theory formula-decomposition)
(%enable formula-decomposition
         aggressive-equal-of-logic.pors
         aggressive-equal-of-logic.pnots
         aggressive-equal-of-logic.pequals
         forcing-equal-of-logic.pequal-rewrite
         forcing-equal-of-logic.pequal-rewrite-two
         forcing-equal-of-logic.por-rewrite
         forcing-equal-of-logic.por-rewrite-two
         forcing-equal-of-logic.pnot-rewrite
         forcing-equal-of-logic.pnot-rewrite-two
         forcing-equal-of-logic.pequal-list-rewrite
         forcing-equal-of-logic.pequal-list-rewrite-alt
         forcing-equal-of-logic.function-with-three-args-alt
         equal-of-logic.function-rewrite
         equal-of-logic.function-rewrite-alt
         [outside]equal-of-logic.function-and-logic.function
         equal-logic.pequal-logic.pequal-rewrite
         [outside]equal-logic.pequal-logic.pequal-rewrite
         equal-logic.por-logic.por-rewrite
         [outside]equal-logic.por-logic.por-rewrite)

(%create-theory expensive-term/formula-inference)
(%enable expensive-term/formula-inference
         logic.termp-when-logic.formulap
         logic.termp-when-invalid-maybe-expensive
         logic.formulap-when-logic.termp
         logic.constantp-when-not-consp
         logic.constantp-when-logic.variablep
         logic.constantp-when-logic.functionp
         logic.constantp-when-logic.lambdap-cheap
         logic.constantp-of-car-when-logic.constant-listp
         logic.constantp-of-second-when-logic.constant-listp
         logic.constantp-of-third-when-logic.constant-listp
         logic.constantp-of-car-when-logic.none-constantp
         logic.constantp-when-memberp-of-logic.constant-listp
         logic.constant-listp-when-not-consp
         logic.constant-listp-of-subsetp-when-logic.constant-listp
         logic.variablep-when-consp
         logic.variablep-when-logic.constantp
         logic.variablep-when-logic.functionp
         logic.variablep-when-logic.lambdap-cheap
         logic.functionp-when-not-other-stuff-cheap
         logic.functionp-when-logic.lambdap-cheap
         forcing-logic.functionp-when-logic.base-evaluablep
         forcing-logic.functionp-when-logic.base-evaluablep
         logic.lambdap-when-not-other-stuff-cheap
         logic.lambdap-when-not-anything-else-maybe-expensive
         logic.lambdap-when-consp-of-car-cheap
         logic.lambdap-when-logic.functionp-cheap
         forcing-true-listp-of-logic.function-args)

(%enable expensive-subsetp-rules
         memberp-when-logic.all-terms-larger-cheap)

(%enable unusual-memberp-rules
         memberp-when-logic.all-terms-larger-cheap)

(%enable unusual-consp-rules
         consp-when-memberp-of-logic.sigmap-alt
         consp-when-memberp-of-logic.arity-tablep-alt
         consp-when-logic.functionp-cheap
         consp-when-logic.lambdap-cheap)


(%finish "logic")
(%save-events "logic.events")

;; Clear out the thmfiles table since we'll use the saved image from now on.
(ACL2::table tactic-harness 'thmfiles nil)
