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
(include-book "crewrite-if-same-compiler")
(%interactive)

(%autoadmit rw.compile-crewrite-if-generalcase-trace)

(local (%enable default rw.compile-crewrite-if-generalcase-trace))

(local (%enable default
                lemma-1-for-rw.compile-crewrite-if-specialcase-same-trace
                lemma-2-for-rw.compile-crewrite-if-specialcase-same-trace
                lemma-3-for-rw.compile-crewrite-if-specialcase-same-trace
                lemma-4-for-rw.compile-crewrite-if-specialcase-same-trace
                lemma-5-for-rw.compile-crewrite-if-specialcase-same-trace
                lemma-6-for-rw.compile-crewrite-if-specialcase-same-trace
                lemma-7-for-rw.compile-crewrite-if-specialcase-same-trace))

(local (%enable default
                rw.crewrite-if-generalcase-tracep
                rw.compile-crewrite-if-generalcase-trace
                rw.trace-conclusion-formula
                rw.trace-formula
                rw.hypbox-formula
                logic.term-formula))

(local (%splitlimit 20))

(local (%disable default
                 expensive-arithmetic-rules
                 expensive-arithmetic-rules-two
                 type-set-like-rules
                 expensive-subsetp-rules
                 same-length-prefixes-equal-cheap
                 formula-decomposition
                 unusual-consp-rules
                 usual-consp-rules
                 expensive-term/formula-inference))


(local (%create-theory locally-useless-rules))

(local (%enable locally-useless-rules
                CAR-WHEN-NOT-CONSP
                CDR-OF-CDR-WHEN-TRUE-LISTP-WITH-LEN-FREE-PAST-THE-END
                CDR-OF-CDR-WITH-LEN-FREE-PAST-THE-END
                CDR-WHEN-TRUE-LISTP-WITH-LEN-FREE-PAST-THE-END
                CLAUSE.NEGATIVE-TERMP-WHEN-CLAUSE.SIMPLE-NEGATIVEP
                DEFINITION-LISTP-OF-CDR-WHEN-DEFINITION-LISTP
                DEFINITION-LISTP-WHEN-NOT-CONSP
                DEFINITIONP-OF-CAR-WHEN-DEFINITION-LISTP
                FORCING-LOGIC.=LHS-UNDER-IFF
                FORCING-LOGIC.FORMULAP-OF-LOGIC.VLHS
                FORCING-LOGIC.FORMULAP-OF-LOGIC.~ARG
                FORCING-LOGIC.FUNCTION-OF-LOGIC.FUNCTION-NAME-AND-LOGIC.FUNCTION-ARGS-FREE
                FORCING-LOGIC.VRHS-UNDER-IFF
                LEN-2-WHEN-NOT-CDR-OF-CDR
                LEN-WHEN-NOT-CONSP
                LEN-WHEN-NOT-CONSP-OF-CDR-CHEAP
                LIST-OF-FIRST-AND-SECOND-WHEN-LEN-2
                LOGIC.ALL-FUNCTIONSP-WHEN-NOT-CONSP
                LOGIC.APPEAL-LISTP-WHEN-NOT-CONSP
                LOGIC.APPEALP-OF-CAR-WHEN-LOGIC.APPEAL-LISTP
                LOGIC.APPEALP-WHEN-MEMBERP-OF-LOGIC.APPEAL-LISTP
                LOGIC.CONSTANT-LISTP-OF-CDR-WHEN-LOGIC.CONSTANT-LISTP
                LOGIC.CONSTANT-LISTP-OF-LOGIC.FUNCTION-ARGS-WHEN-LOGIC.BASE-EVALUABLEP
                LOGIC.CONSTANT-LISTP-WHEN-NOT-CONSP
                LOGIC.CONSTANTP-WHEN-LOGIC.LAMBDAP-CHEAP
                LOGIC.CONSTANTP-WHEN-LOGIC.VARIABLEP
                LOGIC.CONSTANTP-WHEN-NOT-CONSP
                LOGIC.DISJOIN-FORMULAS-WHEN-NOT-CONSP
                LOGIC.FMTYPE-OF-CAR-WHEN-LOGIC.ALL-ATOMICP
                LOGIC.FMTYPE-OF-CAR-WHEN-LOGIC.ALL-DISJUNCTIONSP
                LOGIC.FMTYPE-OF-CAR-WHEN-LOGIC.ALL-NEGATIONSP
                LOGIC.FMTYPE-WHEN-DEFINITIONP
                LOGIC.FORMULA-LISTP-OF-CDR-WHEN-LOGIC.FORMULA-LISTP
                LOGIC.FORMULA-LISTP-WHEN-DEFINITION-LISTP
                LOGIC.FORMULA-LISTP-WHEN-NOT-CONSP
                LOGIC.FORMULAP-OF-CAR-WHEN-LOGIC.FORMULA-LISTP
                LOGIC.FORMULAP-OF-SECOND-WHEN-LOGIC.FORMULA-LISTP
                LOGIC.FORMULAP-WHEN-DEFINITIONP
                LOGIC.FORMULAP-WHEN-LOGIC.TERMP
                LOGIC.FORMULAP-WHEN-MALFORMED-CHEAP
                LOGIC.FORMULAP-WHEN-NOT-CONSP
                LOGIC.FUNCTIONP-OF-CAR-WHEN-LOGIC.ALL-FUNCTIONSP
                LOGIC.FUNCTIONP-OF-LOGIC.=LHS-WHEN-DEFINITIONP
                LOGIC.FUNCTIONP-WHEN-CLAUSE.NEGATIVE-TERMP
                LOGIC.FUNCTIONP-WHEN-LOGIC.LAMBDAP-CHEAP
                LOGIC.LAMBDAP-WHEN-CONSP-OF-CAR-CHEAP
                LOGIC.LAMBDAP-WHEN-NOT-ANYTHING-ELSE-MAYBE-EXPENSIVE
                LOGIC.LAMBDAP-WHEN-NOT-OTHER-STUFF-CHEAP
                LOGIC.PROOF-LISTP-WHEN-NOT-CONSP
                LOGIC.STRIP-CONCLUSIONS-WHEN-NOT-CONSP
                LOGIC.TERM-LIST-FORMULAS-WHEN-NOT-CONSP
                LOGIC.TERM-LISTP-WHEN-LOGIC.CONSTANT-LISTP-CHEAP
                LOGIC.TERM-LISTP-WHEN-LOGIC.VARIABLE-LISTP-CHEAP
                LOGIC.TERM-LISTP-WHEN-NOT-CONSP
                LOGIC.TERMP-WHEN-INVALID-MAYBE-EXPENSIVE
                LOGIC.TERMP-WHEN-LOGIC.CONSTANTP
                LOGIC.TERMP-WHEN-LOGIC.FORMULAP
                LOGIC.TERMP-WHEN-LOGIC.VARIABLEP
                LOGIC.TERMP-WHEN-NOT-CONSP-CHEAP
                LOGIC.VARIABLE-LISTP-OF-CDR-WHEN-LOGIC.VARIABLE-LISTP
                LOGIC.VARIABLE-LISTP-WHEN-NOT-CONSP
                LOGIC.VARIABLEP-OF-CAR-WHEN-LOGIC.VARIABLE-LISTP
                LOGIC.VARIABLEP-WHEN-CONSP
                LOGIC.VARIABLEP-WHEN-LOGIC.CONSTANTP
                LOGIC.VARIABLEP-WHEN-LOGIC.FUNCTIONP
                LOGIC.VARIABLEP-WHEN-LOGIC.LAMBDAP-CHEAP
                LOOKUP-WHEN-NOT-CONSP
                MEMBERP-WHEN-MEMBERP-OF-CDR
                MEMBERP-WHEN-NOT-CONSP
                RW.TRACE-LIST-FORMULAS-WHEN-NOT-CONSP
                SECOND-UNDER-IFF-WHEN-LOGIC.TERM-LISTP-WITH-LEN-FREE
                TRUE-LIST-LISTP-WHEN-NOT-CONSP
                TRUE-LISTP-OF-CAR-WHEN-TRUE-LIST-LISTP
                TRUE-LISTP-WHEN-NOT-CONSP))

(%autoprove rw.compile-crewrite-if-generalcase-trace-under-iff)


(encapsulate
 ()
 (local (%max-proof-size 1300000000))
 ;; this is 1100 seconds
 (%autoprove logic.appealp-of-rw.compile-crewrite-if-generalcase-trace
             (%enable default expensive-term/formula-inference usual-consp-rules)
             (%disable default locally-useless-rules)
             (%auto :strategy (split cleanup urewrite))
             (%crewrite default) ;; 296 seconds
             (%forcingp nil)
             (%auto :strategy (split cleanup urewrite crewrite))
             (%forcingp t)
             (%crewrite default)
             (%forcingp nil)
             (%auto :strategy (split cleanup urewrite crewrite))
             (%enable default logic.appealp-when-memberp-of-logic.appeal-listp)))

(encapsulate
 ()
 (local (%max-proof-size 1300000000))
 (%autoprove logic.conclusion-of-rw.compile-crewrite-if-generalcase-trace
             (%enable default expensive-term/formula-inference usual-consp-rules)
             (%disable default locally-useless-rules)
             (%auto :strategy (split cleanup urewrite))
             (%crewrite default)
             (%forcingp nil)
             (%auto :strategy (split cleanup urewrite crewrite))
             (%forcingp t)
             (%crewrite default)
             (%forcingp nil)
             (%auto :strategy (split cleanup urewrite crewrite))
             (%enable default
                      forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                      logic.appealp-when-memberp-of-logic.appeal-listp)))

(encapsulate
 ()
 (local (%max-proof-size 900000000))
 (%autoprove logic.proofp-of-rw.compile-crewrite-if-generalcase-trace
             (%enable default expensive-term/formula-inference usual-consp-rules)
             (%disable default locally-useless-rules)
             (%disable default
                       cdr-when-not-consp
                       consp-when-true-listp-cheap
                       consp-when-consp-of-cdr-cheap
                       equal-of-booleans-rewrite)
             (%auto :strategy (split cleanup urewrite))
             (%crewrite default)
             (%forcingp nil)
             (%auto :strategy (split cleanup urewrite crewrite))
             (%forcingp t)
             (%crewrite default)
             (%forcingp nil)
             (%auto :strategy (split cleanup urewrite crewrite))
             (%enable default
                      consp-when-true-listp-cheap
                      logic.appealp-when-memberp-of-logic.appeal-listp)))


