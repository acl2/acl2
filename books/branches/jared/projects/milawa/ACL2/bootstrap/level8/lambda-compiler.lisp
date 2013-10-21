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
(include-book "equiv-by-args-compiler")
(%interactive)


(%autoadmit build.lambda-equal-by-args)
(encapsulate
 ()
 (local (%enable default build.lambda-equal-by-args))
 (%autoprove build.lambda-equal-by-args-under-iff)
 (%autoprove forcing-logic.appealp-of-build.lambda-equal-by-args)
 (%autoprove forcing-logic.conclusion-of-build.lambda-equal-by-args)
 (%autoprove forcing-logic.proofp-of-build.lambda-equal-by-args))

(%autoadmit build.disjoined-lambda-equal-by-args)
(encapsulate
 ()
 (local (%enable default build.disjoined-lambda-equal-by-args))
 (%autoprove build.disjoined-lambda-equal-by-args-under-iff)
 (%autoprove forcing-logic.appealp-of-build.disjoined-lambda-equal-by-args)
 (%autoprove forcing-logic.conclusion-of-build.disjoined-lambda-equal-by-args)
 (%autoprove forcing-logic.proofp-of-build.disjoined-lambda-equal-by-args))

(%autoprove forcing-equal-when-equal-of-logic.lambda-parts
            (%enable default
                     logic.lambda-formals
                     logic.lambda-body
                     logic.lambda-actuals
                     logic.lambdap)
            (%restrict default definition-of-logic.termp (memberp x '(x y)))
            (%disable default
                      logic.term-vars-when-bad
                      logic.constantp-when-logic.variablep
                      logic.variablep-of-car-when-logic.variable-listp
                      logic.term-vars-when-constant
                      logic.term-vars-when-variable
                      logic.term-vars-when-logic.lambda
                      logic.variablep-when-logic.constantp
                      expensive-subsetp-rules
                      logic.formulap-when-logic.termp
                      logic.termp-when-logic.formulap
                      logic.termp-when-logic.variablep
                      logic.termp-when-logic.constantp
                      logic.termp-of-car-when-logic.term-listp
                      logic.term-vars-when-function-call))

(%autoadmit rw.compile-lambda-equiv-by-args-trace)

(local (%enable default
                rw.trace-conclusion-formula
                rw.trace-formula
                rw.lambda-equiv-by-args-tracep
                rw.compile-lambda-equiv-by-args-trace))

(local (%disable default
                 expensive-arithmetic-rules
                 expensive-arithmetic-rules-two
                 type-set-like-rules
                 expensive-subsetp-rules
                 same-length-prefixes-equal-cheap
                 formula-decomposition
                 forcing-logic.vrhses-of-logic.por-list-free))

(%autoprove lemma-for-rw.compile-lambda-equiv-by-args-trace
            (%disable default
                      len-of-rw.trace-list-lhses
                      [outside]len-of-rw.trace-list-lhses)
            (%use (%instance (%thm len-of-rw.trace-list-lhses)
                             (x y))))

(local (%enable default
                lemma-for-rw.compile-lambda-equiv-by-args-trace
                lemma-1-for-logic.proofp-of-rw.compile-equiv-by-args-trace
                lemma-2-for-logic.proofp-of-rw.compile-equiv-by-args-trace))

(%autoprove rw.compile-lambda-equiv-by-args-trace-under-iff)

(%autoprove logic.appealp-of-rw.compile-lambda-equiv-by-args-trace)

(%autoprove logic.conclusion-of-rw.compile-lambda-equiv-by-args-trace
            (%auto)
            (%enable default
                     type-set-like-rules
                     forcing-equal-when-equal-of-logic.lambda-parts
                     expensive-arithmetic-rules-two
                     expensive-term/formula-inference
                     formula-decomposition))

(%autoprove logic.proofp-of-rw.compile-lambda-equiv-by-args-trace
            (%disable default
                      unusual-memberp-rules
                      memberp-when-memberp-of-cdr
                      memberp-when-not-consp))


