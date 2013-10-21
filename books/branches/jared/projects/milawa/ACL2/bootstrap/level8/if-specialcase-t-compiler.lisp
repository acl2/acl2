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

(local (%splitlimit 20)) ;; BOZO Consider this globally at this level

(%autoadmit rw.compile-if-specialcase-t-trace)

(local (%enable default
                rw.if-specialcase-t-tracep
                rw.compile-if-specialcase-t-trace
                rw.trace-conclusion-formula
                rw.trace-formula
                equal-of-2-and-len))

(local (%disable default
                 expensive-arithmetic-rules
                 expensive-arithmetic-rules-two
                 type-set-like-rules
                 expensive-subsetp-rules
                 same-length-prefixes-equal-cheap
                 formula-decomposition
                 unusual-consp-rules
                 expensive-term/formula-inference))

(local (%disable default
                 logic.appealp-of-car-when-logic.appeal-listp
                 logic.appealp-of-second-when-logic.appeal-listp
                 logic.appealp-when-memberp-of-logic.appeal-listp
                 logic.appeal-listp-of-cdr-when-logic.appeal-listp
                 logic.proofp-when-memberp-of-logic.proof-listp
                 logic.proofp-of-car-when-logic.proof-listp
                 logic.proof-listp-of-cdr-when-logic.proof-listp
                 rw.tracep-of-car-when-rw.trace-listp
                 rw.trace-listp-of-cdr-when-rw.trace-listp
                 rw.trace-listp-when-not-consp
                 logic.appeal-listp-when-not-consp
                 logic.proofp-when-not-consp
                 logic.proof-listp-when-not-consp
                 logic.strip-conclusions-when-not-consp
                 rw.trace-list-formulas-when-not-consp
                 rw.tracep-when-memberp-of-rw.trace-listp
                 forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                 forcing-equal-of-logic.function-with-two-args-alt))

(local (%enable default
                ;; This rules were added to formula-decomposition and broke the proofs below.  We
                ;; just leave them all enabled.  It would be better to figure out which ones we
                ;; really need.  We could probably do that by profiling and experimentation.
                equal-of-logic.function-rewrite
                equal-logic.por-logic.por-rewrite
                forcing-equal-of-logic.function-with-three-args-alt
                equal-of-logic.function-rewrite-alt
                equal-logic.pequal-logic.pequal-rewrite
                [outside]equal-of-logic.function-and-logic.function
                [outside]equal-logic.pequal-logic.pequal-rewrite
                equal-logic.por-logic.por-rewrite
                [outside]equal-logic.por-logic.por-rewrite))


(%autoprove rw.compile-if-specialcase-t-trace-under-iff)

(%autoprove logic.appealp-of-rw.compile-if-specialcase-t-trace
            (%use (%instance (%thm forcing-rw.trace-listp-of-rw.trace->subtraces)))
            (%restrict default logic.strip-conclusions          (memberp x '(proofs (cdr proofs))))
            (%restrict default definition-of-logic.appeal-listp (memberp x '(proofs (cdr proofs))))
            (%restrict default rw.trace-list-formulas           (memberp x '((rw.trace->subtraces x) (cdr (rw.trace->subtraces x)))))
            (%restrict default definition-of-rw.trace-listp     (memberp x '((rw.trace->subtraces x) (cdr (rw.trace->subtraces x)))))
            (%forcingp nil)
            (%auto :strategy (split cleanup urewrite crewrite))
            (%enable default
                     formula-decomposition
                     expensive-term/formula-inference) ;; may not need this with formula-decomposition changes
            (%disable default
                      aggressive-equal-of-logic.pequals
                      aggressive-equal-of-logic.pnots
                      aggressive-equal-of-logic.pors)
            (%auto :strategy (split cleanup urewrite crewrite)))

(%autoprove logic.conclusion-of-rw.compile-if-specialcase-t-trace
            (%use (%instance (%thm forcing-rw.trace-listp-of-rw.trace->subtraces)))
            (%restrict default logic.strip-conclusions          (memberp x '(proofs (cdr proofs))))
            (%restrict default definition-of-logic.appeal-listp (memberp x '(proofs (cdr proofs))))
            (%restrict default rw.trace-list-formulas           (memberp x '((rw.trace->subtraces x) (cdr (rw.trace->subtraces x)))))
            (%restrict default definition-of-rw.trace-listp     (memberp x '((rw.trace->subtraces x) (cdr (rw.trace->subtraces x)))))
            (%forcingp nil)
            (%auto :strategy (split cleanup urewrite crewrite))
            (%enable default
                     formula-decomposition
                     expensive-term/formula-inference)
            (%disable default
                      aggressive-equal-of-logic.pequals
                      aggressive-equal-of-logic.pnots
                      aggressive-equal-of-logic.pors)
            (%forcingp t)
            (%crewrite default)
            (%forcingp nil)
            (%auto :strategy (split cleanup urewrite crewrite)))

(%autoprove logic.proofp-of-rw.compile-if-specialcase-t-trace
            (%use (%instance (%thm forcing-rw.trace-listp-of-rw.trace->subtraces)))
            (%restrict default logic.strip-conclusions          (memberp x '(proofs (cdr proofs))))
            (%restrict default definition-of-logic.appeal-listp (memberp x '(proofs (cdr proofs))))
            (%restrict default definition-of-logic.proof-listp  (memberp x '(proofs (cdr proofs))))
            (%restrict default rw.trace-list-formulas           (memberp x '((rw.trace->subtraces x) (cdr (rw.trace->subtraces x)))))
            (%restrict default definition-of-rw.trace-listp     (memberp x '((rw.trace->subtraces x) (cdr (rw.trace->subtraces x)))))
            (%forcingp nil)
            (%auto :strategy (split cleanup urewrite crewrite))
            (%enable default
                     formula-decomposition
                     expensive-term/formula-inference)
            (%disable default
                      aggressive-equal-of-logic.pequals
                      aggressive-equal-of-logic.pnots
                      aggressive-equal-of-logic.pors)
            (%forcingp t)
            (%crewrite default)
            (%forcingp nil)
            (%auto :strategy (split cleanup urewrite crewrite)))

