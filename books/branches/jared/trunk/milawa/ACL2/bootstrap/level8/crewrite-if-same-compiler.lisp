;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           __    __        __    __                                        ;;
;;          /  \  /  \      (__)  |  |    ____   ___      __    ____         ;;
;;         /    \/    \      __   |  |   / _  |  \  \ __ /  /  / _  |        ;;
;;        /  /\    /\  \    |  |  |  |  / / | |   \  '  '  /  / / | |        ;;
;;       /  /  \__/  \  \   |  |  |  |  \ \_| |    \  /\  /   \ \_| |        ;;
;;      /__/          \__\  |__|  |__|   \____|     \/  \/     \____|        ;;
;; ~ ~~ \  ~ ~  ~_~~ ~/~ /~ | ~|~ | ~| ~ /~_ ~|~ ~  ~\  ~\~ ~  ~ ~  |~~    ~ ;;
;;  ~ ~  \~ \~ / ~\~ / ~/ ~ |~ | ~|  ~ ~/~/ | |~ ~~/ ~\/ ~~ ~ / / | |~   ~   ;;
;; ~ ~  ~ \ ~\/ ~  \~ ~/ ~~ ~__|  |~ ~  ~ \_~  ~  ~  .__~ ~\ ~\ ~_| ~  ~ ~~  ;;
;;  ~~ ~  ~\  ~ /~ ~  ~ ~  ~ __~  |  ~ ~ \~__~| ~/__~   ~\__~ ~~___~| ~ ~    ;;
;; ~  ~~ ~  \~_/  ~_~/ ~ ~ ~(__~ ~|~_| ~  ~  ~~  ~  ~ ~~    ~  ~   ~~  ~  ~  ;;
;;                                                                           ;;
;;            A   R e f l e c t i v e   P r o o f   C h e c k e r            ;;
;;                                                                           ;;
;;       Copyright (C) 2005-2009 by Jared Davis <jared@cs.utexas.edu>        ;;
;;                                                                           ;;
;; This program is free software; you can redistribute it and/or modify it   ;;
;; under the terms of the GNU General Public License as published by the     ;;
;; Free Software Foundation; either version 2 of the License, or (at your    ;;
;; option) any later version.                                                ;;
;;                                                                           ;;
;; This program is distributed in the hope that it will be useful, but       ;;
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABIL-  ;;
;; ITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public      ;;
;; License for more details.                                                 ;;
;;                                                                           ;;
;; You should have received a copy of the GNU General Public License along   ;;
;; with this program (see the file COPYING); if not, write to the Free       ;;
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "MILAWA")
(include-book "trace-okp")
(%interactive)

(%autoprove lemma-1-for-rw.compile-crewrite-if-specialcase-same-trace)
(%autoprove lemma-2-for-rw.compile-crewrite-if-specialcase-same-trace (%forcingp nil))
(%autoprove lemma-3-for-rw.compile-crewrite-if-specialcase-same-trace (%forcingp nil))
(%autoprove lemma-4-for-rw.compile-crewrite-if-specialcase-same-trace)
(%autoprove lemma-5-for-rw.compile-crewrite-if-specialcase-same-trace)
(%autoprove lemma-6-for-rw.compile-crewrite-if-specialcase-same-trace)
(%autoprove lemma-7-for-rw.compile-crewrite-if-specialcase-same-trace (%forcingp nil))

(local (%enable default
                rw.crewrite-if-specialcase-same-tracep
                rw.trace-conclusion-formula
                rw.trace-formula
                rw.hypbox-formula
                logic.term-formula))

(local (%enable default
                lemma-1-for-rw.compile-crewrite-if-specialcase-same-trace
                lemma-2-for-rw.compile-crewrite-if-specialcase-same-trace
                lemma-3-for-rw.compile-crewrite-if-specialcase-same-trace
                lemma-4-for-rw.compile-crewrite-if-specialcase-same-trace
                lemma-5-for-rw.compile-crewrite-if-specialcase-same-trace
                lemma-6-for-rw.compile-crewrite-if-specialcase-same-trace
                lemma-7-for-rw.compile-crewrite-if-specialcase-same-trace))

(local (%create-theory locally-useless-rules))
(local (%enable locally-useless-rules
                CDR-WHEN-TRUE-LISTP-WITH-LEN-FREE-PAST-THE-END
                LOGIC.FUNCTIONP-WHEN-LOGIC.LAMBDAP-CHEAP
                LOGIC.FMTYPE-WHEN-DEFINITIONP
                TRUE-LISTP-WHEN-NOT-CONSP
                LOGIC.TERM-LIST-FORMULAS-WHEN-NOT-CONSP
                LOGIC.STRIP-CONCLUSIONS-WHEN-NOT-CONSP
                LOGIC.DISJOIN-FORMULAS-WHEN-NOT-CONSP
                LOGIC.PROOF-LISTP-WHEN-NOT-CONSP
                FORCING-LOGIC.=LHS-UNDER-IFF
                MEMBERP-WHEN-MEMBERP-OF-CDR
                FORCING-LOGIC.VRHS-UNDER-IFF
                CDR-OF-CDR-WHEN-TRUE-LISTP-WITH-LEN-FREE-PAST-THE-END
                CDR-OF-CDR-WITH-LEN-FREE-PAST-THE-END
                MEMBERP-WHEN-NOT-CONSP
                LOGIC.TERMP-WHEN-LOGIC.CONSTANTP
                LOGIC.TERMP-WHEN-LOGIC.VARIABLEP
                FORCING-LOGIC.FORMULAP-OF-LOGIC.~ARG
                LOGIC.LAMBDAP-WHEN-NOT-ANYTHING-ELSE-MAYBE-EXPENSIVE
                LOGIC.LAMBDAP-WHEN-NOT-OTHER-STUFF-CHEAP
                LOGIC.LAMBDAP-WHEN-CONSP-OF-CAR-CHEAP
                LOGIC.VARIABLEP-WHEN-LOGIC.CONSTANTP
                LOGIC.CONSTANTP-WHEN-LOGIC.VARIABLEP
                LOGIC.TERMP-WHEN-INVALID-MAYBE-EXPENSIVE
                FORCING-LOGIC.FORMULAP-OF-LOGIC.VLHS
                LOGIC.VARIABLEP-WHEN-LOGIC.LAMBDAP-CHEAP
                LOGIC.VARIABLEP-WHEN-CONSP
                CLAUSE.NEGATIVE-TERMP-WHEN-CLAUSE.SIMPLE-NEGATIVEP
                LOGIC.FORMULA-LISTP-WHEN-DEFINITION-LISTP
                LOGIC.TERMP-WHEN-LOGIC.FORMULAP
                LOGIC.CONSTANTP-WHEN-NOT-CONSP
                LOGIC.CONSTANTP-WHEN-LOGIC.LAMBDAP-CHEAP
                DEFINITION-LISTP-WHEN-NOT-CONSP
                LOGIC.TERM-LISTP-WHEN-LOGIC.CONSTANT-LISTP-CHEAP
                LOGIC.FUNCTIONP-OF-LOGIC.=LHS-WHEN-DEFINITIONP
                LOGIC.TERM-LISTP-WHEN-LOGIC.VARIABLE-LISTP-CHEAP
                LOGIC.FORMULA-LISTP-WHEN-NOT-CONSP
                LOGIC.FORMULAP-WHEN-NOT-CONSP
                LOGIC.TERMP-WHEN-NOT-CONSP-CHEAP
                LOGIC.FORMULAP-WHEN-MALFORMED-CHEAP
                LOGIC.VARIABLE-LISTP-WHEN-NOT-CONSP
                LOGIC.CONSTANT-LISTP-WHEN-NOT-CONSP
                LOGIC.FORMULAP-WHEN-DEFINITIONP
                LOGIC.TERM-LISTP-WHEN-NOT-CONSP
                LOGIC.VARIABLEP-OF-CAR-WHEN-LOGIC.VARIABLE-LISTP
                LIST-OF-FIRST-AND-SECOND-WHEN-LEN-2))

(local (%disable default
                 expensive-arithmetic-rules
                 expensive-arithmetic-rules-two
                 type-set-like-rules
                 expensive-subsetp-rules
                 same-length-prefixes-equal-cheap
                 formula-decomposition
                 unusual-consp-rules
                 usual-consp-rules
                 expensive-term/formula-inference
                 locally-useless-rules))

(%autoadmit rw.compile-crewrite-if-specialcase-same-trace-iff)

(local (%enable default rw.compile-crewrite-if-specialcase-same-trace-iff))

(%autoprove rw.compile-crewrite-if-specialcase-same-trace-iff-under-iff)



; These are hard proofs.
;
; I've cut the rules back so far that there's not much more to be gained.
; I've also tried mucking around with limiting the asusmptions system, but
; it really doesn't seem to help.


;; appealp.  the time to beat is 486 seconds.  394 million conses.  1.6 gb.


#||
(%autorule logic.appealp-of-rw.compile-crewrite-if-specialcase-same-trace-iff)

(%enable default
                     expensive-term/formula-inference)
(%disable default
                      locally-useless-rules
                      equal-of-booleans-rewrite
                      logic.appeal-listp-when-not-consp
                      LOGIC.FUNCTIONP-WHEN-NOT-OTHER-STUFF-CHEAP
                      RW.TRACE-LIST-FORMULAS-WHEN-NOT-CONSP
                      LEN-WHEN-NOT-CONSP
                      LEN-WHEN-NOT-CONSP-OF-CDR-CHEAP
                      FORCING-LOGIC.FUNCTIONP-WHEN-LOGIC.BASE-EVALUABLEP
                      iff)
(%liftlimit 10)
(%splitlimit 2)
(%auto :strategy (cleanup split urewrite))
(%crewrite default) ;; this gets us all the forcing goals together.
(%auto :strategy (cleanup split urewrite))
(%forcingp nil)
(%enable default usual-consp-rules)
(acl2::time$ (%waterfall default 50))
(%forcingp t)

(%auto)

||#


(%autoprove logic.appealp-of-rw.compile-crewrite-if-specialcase-same-trace-iff
            (%enable default
                     expensive-term/formula-inference)
            (%disable default
                      locally-useless-rules
                      equal-of-booleans-rewrite
                      logic.appeal-listp-when-not-consp
                      LOGIC.FUNCTIONP-WHEN-NOT-OTHER-STUFF-CHEAP
                      RW.TRACE-LIST-FORMULAS-WHEN-NOT-CONSP
                      LEN-WHEN-NOT-CONSP
                      LEN-WHEN-NOT-CONSP-OF-CDR-CHEAP
                      FORCING-LOGIC.FUNCTIONP-WHEN-LOGIC.BASE-EVALUABLEP
                      iff)
            (%auto)
            (%enable default usual-consp-rules))

(%autoprove logic.conclusion-of-rw.compile-crewrite-if-specialcase-same-trace-iff
            (%enable default
                     expensive-term/formula-inference)
            (%disable default
                      locally-useless-rules
                      equal-of-booleans-rewrite
                      logic.appeal-listp-when-not-consp
                      LOGIC.FUNCTIONP-WHEN-NOT-OTHER-STUFF-CHEAP
                      RW.TRACE-LIST-FORMULAS-WHEN-NOT-CONSP
                      LEN-WHEN-NOT-CONSP
                      LEN-WHEN-NOT-CONSP-OF-CDR-CHEAP
                      FORCING-LOGIC.FUNCTIONP-WHEN-LOGIC.BASE-EVALUABLEP
                      iff)
            (%auto)
            (%enable default usual-consp-rules))

(%autoprove logic.proofp-of-rw.compile-crewrite-if-specialcase-same-trace-iff
            (%enable default
                     expensive-term/formula-inference)
            (%disable default
                      locally-useless-rules
                      equal-of-booleans-rewrite
                      logic.appeal-listp-when-not-consp
                      LOGIC.FUNCTIONP-WHEN-NOT-OTHER-STUFF-CHEAP
                      RW.TRACE-LIST-FORMULAS-WHEN-NOT-CONSP
                      LEN-WHEN-NOT-CONSP
                      LEN-WHEN-NOT-CONSP-OF-CDR-CHEAP
                      FORCING-LOGIC.FUNCTIONP-WHEN-LOGIC.BASE-EVALUABLEP
                      iff)
            (%auto)
            (%enable default usual-consp-rules))




(%autoadmit rw.compile-crewrite-if-specialcase-same-trace-equal)

(local (%enable default rw.compile-crewrite-if-specialcase-same-trace-equal))

(%autoprove rw.compile-crewrite-if-specialcase-same-trace-equal-under-equal)
;; badly named


(%autoprove logic.appealp-of-rw.compile-crewrite-if-specialcase-same-trace-equal
            (%enable default
                     expensive-term/formula-inference)
            (%disable default
                      locally-useless-rules
                      equal-of-booleans-rewrite
                      logic.appeal-listp-when-not-consp
                      LOGIC.FUNCTIONP-WHEN-NOT-OTHER-STUFF-CHEAP
                      RW.TRACE-LIST-FORMULAS-WHEN-NOT-CONSP
                      LEN-WHEN-NOT-CONSP
                      LEN-WHEN-NOT-CONSP-OF-CDR-CHEAP
                      FORCING-LOGIC.FUNCTIONP-WHEN-LOGIC.BASE-EVALUABLEP
                      iff)
            (%auto)
            (%enable default usual-consp-rules))

(%autoprove logic.conclusion-of-rw.compile-crewrite-if-specialcase-same-trace-equal
            (%enable default
                     expensive-term/formula-inference)
            (%disable default
                      locally-useless-rules
                      equal-of-booleans-rewrite
                      logic.appeal-listp-when-not-consp
                      LOGIC.FUNCTIONP-WHEN-NOT-OTHER-STUFF-CHEAP
                      RW.TRACE-LIST-FORMULAS-WHEN-NOT-CONSP
                      LEN-WHEN-NOT-CONSP
                      LEN-WHEN-NOT-CONSP-OF-CDR-CHEAP
                      FORCING-LOGIC.FUNCTIONP-WHEN-LOGIC.BASE-EVALUABLEP
                      iff)
            (%auto)
            (%enable default usual-consp-rules))

(%autoprove logic.proofp-of-rw.compile-crewrite-if-specialcase-same-trace-equal
            (%enable default
                     expensive-term/formula-inference)
            (%disable default
                      locally-useless-rules
                      equal-of-booleans-rewrite
                      logic.appeal-listp-when-not-consp
                      LOGIC.FUNCTIONP-WHEN-NOT-OTHER-STUFF-CHEAP
                      RW.TRACE-LIST-FORMULAS-WHEN-NOT-CONSP
                      LEN-WHEN-NOT-CONSP
                      LEN-WHEN-NOT-CONSP-OF-CDR-CHEAP
                      FORCING-LOGIC.FUNCTIONP-WHEN-LOGIC.BASE-EVALUABLEP
                      iff)
            (%auto)
            (%enable default usual-consp-rules))



(local (%disable default
                 rw.compile-crewrite-if-specialcase-same-trace-iff
                 rw.compile-crewrite-if-specialcase-same-trace-equal))

(%autoadmit rw.compile-crewrite-if-specialcase-same-trace)

(local (%enable default rw.compile-crewrite-if-specialcase-same-trace))

(%autoprove rw.compile-crewrite-if-specialcase-same-trace-under-equal)

(local (%splitlimit 8))
(local (%liftlimit 8))

(%autoprove logic.appealp-of-rw.compile-crewrite-if-specialcase-same-trace)

(%autoprove logic.conclusion-of-rw.compile-crewrite-if-specialcase-same-trace)

(%autoprove logic.proofp-of-rw.compile-crewrite-if-specialcase-same-trace)

#|










(%autorule logic.appealp-of-rw.compile-crewrite-if-specialcase-same-trace-equal)
(%enable default
         expensive-term/formula-inference)
(%disable default
          locally-useless-rules
          equal-of-booleans-rewrite
          logic.appeal-listp-when-not-consp
          LOGIC.FUNCTIONP-WHEN-NOT-OTHER-STUFF-CHEAP
          RW.TRACE-LIST-FORMULAS-WHEN-NOT-CONSP
          LEN-WHEN-NOT-CONSP
          LEN-WHEN-NOT-CONSP-OF-CDR-CHEAP
          FORCING-LOGIC.FUNCTIONP-WHEN-LOGIC.BASE-EVALUABLEP
          iff)
(%auto :strategy (split cleanup urewrite))
(%crewrite default)

(%forcingp nil)
(%auto :strategy (split cleanup urewrite))
(ACL2::time$ (%crewrite default)) ;; 135 seconds
(%auto :strategy (split cleanup urewrite))
(ACL2::time$ (%crewrite default))





(%auto :strategy (split cleanup urewrite))
(%crewrite default)
(%auto :strategy (split cleanup urewrite))

(%crewrite default)



(%auto :strategy (split cleanup urewrite))

;; This is the point of interest.

(ACL2::time$ (%crewrite default)) ;; no assm-tweaking, 177 seconds
(%auto :strategy (split cleanup urewrite)) ;; this leaves us with 114 goals

(ACL2::time$ (%crewrite default)) ;; 135 seconds
(%auto :strategy (split cleanup urewrite)) ;; this leaves us with 22 goals

(%enable default usual-consp-rules)
(ACL2::time$ (%crewrite default)) ;; 35 seconds
(%auto :strategy (split cleanup urewrite)) ;; this leaves us with 27 goals

(ACL2::time$ (%crewrite default)) ;; 27 seconds
(%auto :strategy (split cleanup urewrite)) ;; this leaves us with 13 goals

(%auto) ;; win




;; Undoing to the point of interest.

(%assmctrl :primaryp nil :secondaryp nil :directp nil :negativep nil)

(ACL2::time$ (%crewrite default)) ;; 11 seconds
(%auto :strategy (split cleanup urewrite)) ;;  109 goals

(%assmctrl :primaryp t :secondaryp t :directp t :negativep t)
(%enable default usual-consp-rules)
(ACL2::time$ (%crewrite default)) ;; 288 seconds
(%auto :strategy (split cleanup urewrite))



;; Undoing to the point of interest

(%assmctrl :primaryp nil :secondaryp nil :directp t :negativep t)
(ACL2::time$ (%crewrite default)) ;; 46 seconds
(%auto :strategy (split cleanup urewrite)) ;; 109 goals

(ACL2::time$ (%crewrite default)) ;; 46 seconds
(%auto :strategy (split cleanup urewrite)) ;; 109 goals

(ACL2::time$ (%crewrite default)) ;; fail to make progress



;; Undoing to the point of interest

;; A big chunk of this is the equalities.  Probably because so many hyps are equal hyps,
;; caused by the forcing of goals.

(%assmctrl :primaryp t :secondaryp t :directp nil :negativep nil)
(ACL2::time$ (%crewrite default)) ;; 121 seconds,  splitting going nuts

(%splitlimit 8)
(%liftlimit 8)
(%auto :strategy (split cleanup urewrite)) ;; much longer

(ACL2::time$ (%crewrite default)) ;; 402 goals.  man, this seems loserly



;; Undoing to the point of interest

(%assmctrl :primaryp t :secondaryp nil :directp nil :negativep t)
(ACL2::time$ (%crewrite default)) ;; 108 seconds
(%auto :strategy (split cleanup urewrite)) ;; 109 goals

(ACL2::time$ (%crewrite default)) ;; 112 seconds
(%auto :strategy (split cleanup urewrite)) ;; 109 goals





;; Undoing to the point of interest

(%assmctrl :primaryp t :secondaryp t :directp nil :negativep t)
(ACL2::time$ (%crewrite default)) ;; 100 seconds
(%auto :strategy (split cleanup urewrite)) ;; 109 goals


(%enable default usual-consp-rules)
(ACL2::time$ (%crewrite default)) ;; 35 seconds
(%auto :strategy (split cleanup urewrite)) ;; this leaves us with 27 goals

(ACL2::time$ (%crewrite default)) ;; 27 seconds
(%auto :strategy (split cleanup urewrite)) ;; this leaves us with 13 goals

(%auto)




(%assmctrl :primaryp nil :secondaryp nil :directp nil :negativep nil)
(%auto :strategy (split cleanup urewrite crewrite))

(%assmctrl :primaryp t :secondaryp t :directp nil :negativep nil)
(%splitlimit 20)
(acl2::time$ (%auto :strategy (split cleanup urewrite crewrite)))


(%auto :strategy (cleanup split urewrite))
(%crewrite default)
(%auto :strategy (cleanup split urewrite))

;; curious, would a very low backchain-limit allow us to make progress more quickly?  i.e.,
;; prove off goals that are very simple to see without spending extra time on them, so we
;; can then turn up the volume later?
(%blimit 50)
(%assmctrl :primaryp nil
           :secondaryp nil
           :directp nil
           :negativep nil)
(%crewrite default)
(%auto :strategy (split cleanup urewrite)) ;; hrmn, maybe throw out elim?  it seems to be going nuts


(%assmctrl :primaryp nil
           :secondaryp nil
           :directp nil
           :negativep t)
(%crewrite default)



(%blimit 50)
(%forcingp t)
(%crewrite default)

(%blimit 3)
(%forcingp nil)
(%auto :strategy (split cleanup urewrite))

; oddly this dosen't seem much faster.  maybe the cost is in assembling the assumptions system?

(%blimit 0)
(acl2::time$ (%crewrite default))

(strip-lens (tactic.skeleton->goals (tactic.harness->skeleton (acl2::w acl2::state))))







(%disable default
         CAR-OF-LOGIC.TERM-LIST-FORMULAS
         CONSP-WHEN-TRUE-LISTP-CHEAP
         EQUAL-OF-CONS-REWRITE
         FORCING-LOGIC.FMTYPE-OF-LOGIC.DISJOIN-FORMULAS
         FORCING-LOGIC.VLHS-OF-LOGIC.DISJOIN-FORMULAS
         FORCING-LOGIC.VRHS-OF-LOGIC.DISJOIN-FORMULAS
         LEMMA-7-FOR-RW.COMPILE-CREWRITE-IF-SPECIALCASE-SAME-TRACE
         ;RW.TRACE-CONCLUSION-FORMULA
         )
(%auto)



(%auto :strategy (cleanup split dist crewrite elim)) ;; no urewrite for profile

(%enable default usual-consp-rules)
(%auto :strategy (cleanup split dist crewrite elim)) ;; no urewrite for profile







(%create-theory actually-used-rules)
(%enable actually-used-rules
         SYMMETRY-OF-EQUAL
         LOGIC.DISJOIN-FORMULAS-WHEN-SINGLETON-LIST
         CDR-WHEN-NOT-CONSP
         CAR-WHEN-NOT-CONSP
         [OUTSIDE]CONSP-OF-LOGIC.TERM-LIST-FORMULAS
         FORCING-LOGIC.APPEALP-OF-RW.DISJOINED-IFF-OF-IF-X-Y-Y-BLDR
         CONSP-WHEN-TRUE-LISTP-CHEAP
         [OUTSIDE]CDR-OF-LOGIC.TERM-LIST-FORMULAS
         CDR-WHEN-TRUE-LISTP-WITH-LEN-FREE-PAST-THE-END
         CONSP-WHEN-CONSP-OF-CDR-CHEAP
         CONSP-OF-LOGIC.TERM-LIST-FORMULAS
         LOGIC.FUNCTIONP-WHEN-CLAUSE.NEGATIVE-TERMP
         FORCING-LOGIC.CONCLUSION-OF-RW.CREWRITE-TWIDDLE-BLDR
         FORCING-LOGIC.FORMULA-LISTP-OF-LOGIC.TERM-LIST-FORMULAS
         LEMMA-5-FOR-RW.COMPILE-CREWRITE-IF-SPECIALCASE-SAME-TRACE
         FORCING-LOGIC.VLHS-OF-LOGIC.DISJOIN-FORMULAS
         RW.TRACE-CONCLUSION-FORMULA
         RW.TRACEP-OF-CAR-WHEN-RW.TRACE-LISTP
         FORCING-RW.HYPBOXP-OF-RW.TRACE->HYPBOX
         [OUTSIDE]REDEFINITION-OF-CLAUSE.CLAUSE-FORMULA
         RW.TRACE-FORMULA
         FORCING-LOGIC.TERM-LISTP-OF-RW.HYPBOX->LEFT
         LEMMA-6-FOR-RW.COMPILE-CREWRITE-IF-SPECIALCASE-SAME-TRACE
         CDR-OF-CDR-WITH-LEN-FREE-PAST-THE-END
         CDR-OF-CDR-WHEN-TRUE-LISTP-WITH-LEN-FREE-PAST-THE-END
         LOGIC.TERM-FORMULA
         CAR-OF-LOGIC.TERM-LIST-FORMULAS
         FORCING-LOGIC.CONCLUSION-OF-RW.CREWRITE-TWIDDLE2-BLDR
         RW.HYPBOX-FORMULA
         RW.TRACE-LISTP-OF-CDR-WHEN-RW.TRACE-LISTP
         CONSP-OF-CDR-WITH-LEN-FREE
         FORCING-LOGIC.APPEALP-OF-RW.IFF-OF-IF-X-Y-Y-BLDR
         FORCING-TRUE-LISTP-OF-RW.HYPBOX->LEFT
         REFLEXIVITY-OF-EQUAL
         LOGIC.VLHS-OF-LOGIC.POR
         LOGIC.VRHS-OF-LOGIC.POR
         EQUAL-OF-NIL-ONE
         FORCING-LOGIC.TERM-LISTP-OF-RW.HYPBOX->RIGHT
         FORCING-LOGIC.FMTYPE-OF-LOGIC.DISJOIN-FORMULAS
         FORCING-LOGIC.APPEALP-OF-RW.CREWRITE-TWIDDLE-BLDR
         LOGIC.APPEALP-OF-SECOND-WHEN-LOGIC.APPEAL-LISTP
         FORCING-LOGIC.VRHS-OF-LOGIC.DISJOIN-FORMULAS
         FORCING-RW.TRACE-LISTP-OF-RW.TRACE->SUBTRACES
         CONSP-OF-CDR-OF-CDR-WITH-LEN-FREE
         [OUTSIDE]LOGIC.VLHS-OF-LOGIC.POR
         LOGIC.=LHS-OF-LOGIC.PEQUAL
         FORCING-LOGIC.APPEALP-OF-RW.CREWRITE-TWIDDLE2-BLDR
         RW.TRACE->RHS-UNDER-IFF
         LEMMA-4-FOR-RW.COMPILE-CREWRITE-IF-SPECIALCASE-SAME-TRACE
         LEMMA-2-FOR-RW.COMPILE-CREWRITE-IF-SPECIALCASE-SAME-TRACE
         LEN-2-WHEN-NOT-CDR-OF-CDR
         LOGIC.FUNCTION-ARGS-OF-LOGIC.FUNCTION
         LOGIC.APPEALP-WHEN-MEMBERP-OF-LOGIC.APPEAL-LISTP
         [OUTSIDE]LOGIC.VRHS-OF-LOGIC.POR
         CDR-OF-CONS
         [OUTSIDE]LOGIC.FUNCTION-UNDER-IFF
         LOGIC.~ARG-OF-LOGIC.PNOT
         FORCING-TRUE-LISTP-OF-LOGIC.FUNCTION-ARGS
         EQUAL-OF-LOGIC.DISJOIN-FORMULAS-AND-LOGIC.DISJOIN-FORMULAS-WHEN-SAME-LEN
         LOGIC.FUNCTION-ARGS-UNDER-IFF-WITH-LEN-FREE
         LOGIC.FMTYPE-OF-LOGIC.POR
         CAR-OF-CONS
         [OUTSIDE]LOGIC.~ARG-OF-LOGIC.PNOT
         LOGIC.APPEAL-LISTP-OF-SUBSETP-WHEN-LOGIC.APPEAL-LISTP
         LOGIC.APPEALP-OF-CAR-WHEN-LOGIC.APPEAL-LISTP
         LOGIC.=RHS-OF-LOGIC.PEQUAL
         LOGIC.FMTYPE-OF-LOGIC.PEQUAL
         LOGIC.FUNCTION-NAME-OF-LOGIC.FUNCTION
         SUBSETP-OF-CDR
         [OUTSIDE]LOGIC.FMTYPE-OF-LOGIC.POR
         LEMMA-3-FOR-RW.COMPILE-CREWRITE-IF-SPECIALCASE-SAME-TRACE
         LOGIC.FMTYPE-OF-LOGIC.PNOT
         LEMMA-1-FOR-RW.COMPILE-CREWRITE-IF-SPECIALCASE-SAME-TRACE
         [OUTSIDE]LEN-OF-CONS
         FORCING-LOGIC.FUNCTIONP-OF-LOGIC.FUNCTION
         LEN-OF-CONS
         LEMMA-7-FOR-RW.COMPILE-CREWRITE-IF-SPECIALCASE-SAME-TRACE
         EQUAL-OF-NIL-TWO
         CONSP-OF-CONS
         [OUTSIDE]SUBSETP-REFLEXIVE
         LIST-FIX-WHEN-TRUE-LISTP
         [OUTSIDE]LOGIC.FMTYPE-OF-LOGIC.PEQUAL
         [OUTSIDE]LEN-OF-LOGIC.TERM-LIST-FORMULAS
         [OUTSIDE]CLAUSE.NEGATIVE-TERMP-OF-LOGIC.FUNCTION-OF-NOT
         [OUTSIDE]LOGIC.FMTYPE-OF-LOGIC.PNOT
         [OUTSIDE]MEMBERP-OF-CAR
         [OUTSIDE]TRUE-LISTP-OF-LOGIC.TERM-LIST-FORMULAS
         EQUAL-OF-CONS-REWRITE
         RW.COMPILE-CREWRITE-IF-SPECIALCASE-SAME-TRACE-IFF
         RW.CREWRITE-IF-SPECIALCASE-SAME-TRACEP)









(%disable default
          CAR-OF-LOGIC.TERM-LIST-FORMULAS
          CONSP-WHEN-TRUE-LISTP-CHEAP
          FORCING-LOGIC.FMTYPE-OF-LOGIC.DISJOIN-FORMULAS
          FORCING-LOGIC.VLHS-OF-LOGIC.DISJOIN-FORMULAS
          FORCING-LOGIC.VRHS-OF-LOGIC.DISJOIN-FORMULAS
          RW.TRACE-CONCLUSION-FORMULA
          LEMMA-7-FOR-RW.COMPILE-CREWRITE-IF-SPECIALCASE-SAME-TRACE)
(%auto)





(CAR-OF-LOGIC.TERM-LIST-FORMULAS
     CONSP-WHEN-TRUE-LISTP-CHEAP
     FORCING-LOGIC.FMTYPE-OF-LOGIC.DISJOIN-FORMULAS
     FORCING-LOGIC.VLHS-OF-LOGIC.DISJOIN-FORMULAS
     FORCING-LOGIC.VRHS-OF-LOGIC.DISJOIN-FORMULAS
     LEMMA-7-FOR-RW.COMPILE-CREWRITE-IF-SPECIALCASE-SAME-TRACE
     RW.TRACE-CONCLUSION-FORMULA)




(%create-theory actually-used-rules)
(%enable actually-used-rules
         SYMMETRY-OF-EQUAL
         LOGIC.DISJOIN-FORMULAS-WHEN-SINGLETON-LIST
         CDR-WHEN-NOT-CONSP
         CAR-WHEN-NOT-CONSP
         [OUTSIDE]CONSP-OF-LOGIC.TERM-LIST-FORMULAS
         FORCING-LOGIC.APPEALP-OF-RW.DISJOINED-IFF-OF-IF-X-Y-Y-BLDR
         CONSP-WHEN-TRUE-LISTP-CHEAP
         CONSP-WHEN-CONSP-OF-CDR-CHEAP
         [OUTSIDE]CDR-OF-LOGIC.TERM-LIST-FORMULAS
         CDR-WHEN-TRUE-LISTP-WITH-LEN-FREE-PAST-THE-END
         FORCING-LOGIC.CONCLUSION-OF-RW.CREWRITE-TWIDDLE-BLDR
         LEMMA-5-FOR-RW.COMPILE-CREWRITE-IF-SPECIALCASE-SAME-TRACE
         FORCING-LOGIC.FORMULA-LISTP-OF-LOGIC.TERM-LIST-FORMULAS
         LOGIC.FUNCTIONP-WHEN-CLAUSE.NEGATIVE-TERMP
         CONSP-OF-LOGIC.TERM-LIST-FORMULAS
         RW.TRACE-CONCLUSION-FORMULA
         FORCING-LOGIC.VLHS-OF-LOGIC.DISJOIN-FORMULAS
         [OUTSIDE]REDEFINITION-OF-CLAUSE.CLAUSE-FORMULA
         RW.TRACE-FORMULA
         RW.TRACEP-OF-CAR-WHEN-RW.TRACE-LISTP
         LEMMA-6-FOR-RW.COMPILE-CREWRITE-IF-SPECIALCASE-SAME-TRACE
         FORCING-LOGIC.CONCLUSION-OF-RW.CREWRITE-TWIDDLE2-BLDR
         FORCING-RW.HYPBOXP-OF-RW.TRACE->HYPBOX
         LOGIC.TERM-FORMULA
         FORCING-LOGIC.TERM-LISTP-OF-RW.HYPBOX->LEFT
         CAR-OF-LOGIC.TERM-LIST-FORMULAS
         RW.HYPBOX-FORMULA
         RW.TRACE-LISTP-OF-CDR-WHEN-RW.TRACE-LISTP
         EQUAL-OF-NIL-TWO
         CDR-OF-CDR-WITH-LEN-FREE-PAST-THE-END
         CDR-OF-CDR-WHEN-TRUE-LISTP-WITH-LEN-FREE-PAST-THE-END
         FORCING-LOGIC.APPEALP-OF-RW.IFF-OF-IF-X-Y-Y-BLDR
         CONSP-OF-CDR-WITH-LEN-FREE
         REFLEXIVITY-OF-EQUAL
         LOGIC.VLHS-OF-LOGIC.POR
         LOGIC.VRHS-OF-LOGIC.POR
         FORCING-TRUE-LISTP-OF-RW.HYPBOX->LEFT
         LOGIC.APPEALP-OF-SECOND-WHEN-LOGIC.APPEAL-LISTP
         FORCING-LOGIC.APPEALP-OF-RW.CREWRITE-TWIDDLE-BLDR
         FORCING-LOGIC.FMTYPE-OF-LOGIC.DISJOIN-FORMULAS
         FORCING-LOGIC.TERM-LISTP-OF-RW.HYPBOX->RIGHT
         CONSP-OF-CDR-OF-CDR-WITH-LEN-FREE
         FORCING-LOGIC.VRHS-OF-LOGIC.DISJOIN-FORMULAS
         LEMMA-4-FOR-RW.COMPILE-CREWRITE-IF-SPECIALCASE-SAME-TRACE
         FORCING-RW.TRACE-LISTP-OF-RW.TRACE->SUBTRACES
         FORCING-LOGIC.APPEALP-OF-RW.CREWRITE-TWIDDLE2-BLDR
         LEMMA-2-FOR-RW.COMPILE-CREWRITE-IF-SPECIALCASE-SAME-TRACE
         LOGIC.APPEALP-WHEN-MEMBERP-OF-LOGIC.APPEAL-LISTP
         LEN-2-WHEN-NOT-CDR-OF-CDR
         FORCING-TRUE-LISTP-OF-LOGIC.FUNCTION-ARGS
         LOGIC.FUNCTION-ARGS-UNDER-IFF-WITH-LEN-FREE
         LOGIC.FMTYPE-OF-LOGIC.POR
         LOGIC.APPEAL-LISTP-OF-SUBSETP-WHEN-LOGIC.APPEAL-LISTP
         LOGIC.APPEALP-OF-CAR-WHEN-LOGIC.APPEAL-LISTP
         LOGIC.=LHS-OF-LOGIC.PEQUAL
         CDR-OF-CONS
         LOGIC.FUNCTION-ARGS-OF-LOGIC.FUNCTION
         SUBSETP-OF-CDR
         LEMMA-3-FOR-RW.COMPILE-CREWRITE-IF-SPECIALCASE-SAME-TRACE
         LEMMA-1-FOR-RW.COMPILE-CREWRITE-IF-SPECIALCASE-SAME-TRACE
         FORCING-LOGIC.FUNCTIONP-OF-LOGIC.FUNCTION
         [OUTSIDE]LEN-OF-CONS
         LOGIC.FMTYPE-OF-LOGIC.PNOT
         LOGIC.FUNCTION-NAME-OF-LOGIC.FUNCTION
         LOGIC.=RHS-OF-LOGIC.PEQUAL
         EQUAL-OF-NIL-ONE
         LOGIC.FMTYPE-OF-LOGIC.PEQUAL
         [OUTSIDE]SUBSETP-REFLEXIVE
         CAR-OF-CONS
         LEN-OF-CONS
         [OUTSIDE]CLAUSE.NEGATIVE-TERMP-OF-LOGIC.FUNCTION-OF-NOT
         LEMMA-7-FOR-RW.COMPILE-CREWRITE-IF-SPECIALCASE-SAME-TRACE
         [OUTSIDE]MEMBERP-OF-CAR
         RW.TRACE->RHS-UNDER-IFF
         CONSP-OF-CONS
         [OUTSIDE]LOGIC.FUNCTION-UNDER-IFF)

(%create-theory splitting-used-rules)
(%enable splitting-used-rules
         (gather from actually-used-rules
                  (not (clause.simple-termp rhs))))




(%describe-theory splitting-used-rules)




    (if (

    (or theory
        (cw "W
         (rules    (rw.gather-rules-from-theory
    (sort-symbols
     (rw.rule-list-names
      (rw.gather-rules-from-theory
       (cdr (lookup 'splitting-used-rules (tactic.world->theories (tactic.harness->world (acl2::w acl2::state)))))
       ''t
       (tactic.world->syndefs (tactic.harness->world (acl2::w acl2::state)))
       nil)))






         (%autoadmit rw.compile-crewrite-if-generalcase-trace)

         (local (%enable default rw.compile-crewrite-if-generalcase-trace))

         (%autoprove rw.compile-crewrite-if-generalcase-trace-under-iff)



         (ACL2::time$
          (%autoprove logic.appealp-of-rw.compile-crewrite-if-generalcase-trace
                      (%enable default
                               expensive-term/formula-inference)
                      (%disable default
                                locally-useless-rules
                                equal-of-booleans-rewrite
                                logic.appeal-listp-when-not-consp
                                LOGIC.FUNCTIONP-WHEN-NOT-OTHER-STUFF-CHEAP
                                RW.TRACE-LIST-FORMULAS-WHEN-NOT-CONSP
                                LEN-WHEN-NOT-CONSP
                                LEN-WHEN-NOT-CONSP-OF-CDR-CHEAP
                                FORCING-LOGIC.FUNCTIONP-WHEN-LOGIC.BASE-EVALUABLEP
                                iff)
                      (%auto)
                      (%enable default usual-consp-rules)))








         (%auto)

         (%splitlimit nil)
         (%liftlimit nil)
         (%auto :strategy (split cleanup urewrite))
         (%crewrite default)

         (%auto :strategy (split cleanup urewrite))

         (%disable default usual-consp-rules)
         (%crewrite default)




         (%create-theory temp)
         (%enable temp (gather from default (not (clause.simple-termp rhs))))
         (%disable default temp)

         (%auto :strategy (split cleanup urewrite))
         (%crewrite default)

         (%auto :strategy (split cleanup urewrite))
         (%enable default temp)


         (%crewrite default first)
         (%crewrite default first)
         (%crewrite default first)
         (%crewrite default first)
         (%crewrite default first)
         (%crewrite default first)
         (%crewrite default first)


         (%splitlimit nil)
         (%liftlimit nil)
         (%auto :strategy (split cleanup urewrite))

         (%profile)
         (%crewrite default first)



         (%enable default equal-of-booleans-rewrite iff)







         (%auto)
         (%enable default
                  ;; really need eobr and iff?
                  equal-of-booleans-rewrite
                  iff
                  usual-consp-rules)))







(%profile)
(%crewrite default)

(encapsulate
 ()
 (local (%max-proof-size 800000000))
 (%autoprove logic.appealp-of-rw.compile-crewrite-if-specialcase-same-trace
             (%auto :strategy (split cleanup urewrite))
             (%crewrite default)
             (%auto :strategy (split cleanup urewrite))
             (%forcingp nil)
             (%auto :strategy (split cleanup urewrite crewrite))
             (%enable default expensive-term/formula-inference)
             (%disable default locally-useless-rules)
             (%forcingp t)
             (%crewrite default)
             (%forcingp nil)
             (%enable default usual-consp-rules)
             (%auto :strategy (split cleanup urewrite crewrite))))

(encapsulate
 ()
 (local (%max-proof-size 900000000))
 (%autoprove logic.conclusion-of-rw.compile-crewrite-if-specialcase-same-trace
             (%auto :strategy (split cleanup urewrite))
             (%crewrite default)
             (%auto :strategy (split cleanup urewrite))
             (%forcingp nil)
             (%auto :strategy (split cleanup urewrite crewrite))
             (%enable default expensive-term/formula-inference)
             (%disable default locally-useless-rules)
             (%forcingp t)
             (%crewrite default)
             (%forcingp nil)
             (%enable default usual-consp-rules)
             (%auto :strategy (split cleanup urewrite crewrite))))

(encapsulate
 ()
 (local (%max-proof-size 1000000000))
 (%autoprove logic.proofp-of-rw.compile-crewrite-if-specialcase-same-trace
             (%auto :strategy (split cleanup urewrite))
             (%crewrite default)
             (%forcingp nil)
             (%auto :strategy (split cleanup urewrite crewrite))
             (%enable default expensive-term/formula-inference)
             (%disable default locally-useless-rules)
             (%forcingp t)
             (%crewrite default)
             (%forcingp nil)
             (%auto :strategy (split cleanup urewrite crewrite))
             (%enable default usual-consp-rules)
             (%forcingp nil)
             (%auto :strategy (split cleanup urewrite crewrite))))






(%autoadmit rw.compile-crewrite-if-specialcase-same-trace)

(%autoprove rw.compile-crewrite-if-specialcase-same-trace-under-iff)

(encapsulate
 ()
 (local (%max-proof-size 800000000))
 (%autoprove logic.appealp-of-rw.compile-crewrite-if-specialcase-same-trace
             (%auto :strategy (split cleanup urewrite))
             (%crewrite default)
             (%auto :strategy (split cleanup urewrite))
             (%forcingp nil)
             (%auto :strategy (split cleanup urewrite crewrite))
             (%enable default expensive-term/formula-inference)
             (%disable default locally-useless-rules)
             (%forcingp t)
             (%crewrite default)
             (%forcingp nil)
             (%enable default usual-consp-rules)
             (%auto :strategy (split cleanup urewrite crewrite))))

(encapsulate
 ()
 (local (%max-proof-size 900000000))
 (%autoprove logic.conclusion-of-rw.compile-crewrite-if-specialcase-same-trace
             (%auto :strategy (split cleanup urewrite))
             (%crewrite default)
             (%auto :strategy (split cleanup urewrite))
             (%forcingp nil)
             (%auto :strategy (split cleanup urewrite crewrite))
             (%enable default expensive-term/formula-inference)
             (%disable default locally-useless-rules)
             (%forcingp t)
             (%crewrite default)
             (%forcingp nil)
             (%enable default usual-consp-rules)
             (%auto :strategy (split cleanup urewrite crewrite))))

(encapsulate
 ()
 (local (%max-proof-size 1000000000))
 (%autoprove logic.proofp-of-rw.compile-crewrite-if-specialcase-same-trace
             (%auto :strategy (split cleanup urewrite))
             (%crewrite default)
             (%forcingp nil)
             (%auto :strategy (split cleanup urewrite crewrite))
             (%enable default expensive-term/formula-inference)
             (%disable default locally-useless-rules)
             (%forcingp t)
             (%crewrite default)
             (%forcingp nil)
             (%auto :strategy (split cleanup urewrite crewrite))
             (%enable default usual-consp-rules)
             (%forcingp nil)
             (%auto :strategy (split cleanup urewrite crewrite))))

|#