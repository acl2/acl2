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
(include-book "fail-compiler")
(%interactive)

(%autoadmit rw.compile-transitivity-trace)

(local (%splitlimit 20)) ;; BOZO Consider this globally at this level

(local (%enable default
                rw.transitivity-tracep
                rw.compile-transitivity-trace
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

(%autoprove rw.compile-transitivity-trace-under-iff)

(%autoprove logic.appealp-of-rw.compile-transitivity-trace
            (%use (%instance (%thm forcing-rw.trace-listp-of-rw.trace->subtraces)))
            (%restrict default logic.strip-conclusions          (memberp x '(proofs (cdr proofs))))
            (%restrict default definition-of-logic.appeal-listp (memberp x '(proofs (cdr proofs))))
            (%restrict default rw.trace-list-formulas           (memberp x '((rw.trace->subtraces x) (cdr (rw.trace->subtraces x)))))
            (%restrict default definition-of-rw.trace-listp     (memberp x '((rw.trace->subtraces x) (cdr (rw.trace->subtraces x)))))
            (%forcingp nil)
            (%auto :strategy (split cleanup urewrite crewrite))
            (%enable default formula-decomposition)
            (%disable default
                      aggressive-equal-of-logic.pequals
                      aggressive-equal-of-logic.pnots
                      aggressive-equal-of-logic.pors
                      equal-of-2-and-len)
            (%auto :strategy (split cleanup urewrite crewrite)))


(%autoprove logic.conclusion-of-rw.compile-transitivity-trace
            (%use (%instance (%thm forcing-rw.trace-listp-of-rw.trace->subtraces)))
            (%restrict default logic.strip-conclusions          (memberp x '(proofs (cdr proofs))))
            (%restrict default definition-of-logic.appeal-listp (memberp x '(proofs (cdr proofs))))
            (%restrict default rw.trace-list-formulas           (memberp x '((rw.trace->subtraces x) (cdr (rw.trace->subtraces x)))))
            (%restrict default definition-of-rw.trace-listp     (memberp x '((rw.trace->subtraces x) (cdr (rw.trace->subtraces x)))))
            (%auto :strategy (split cleanup urewrite crewrite))
            (%enable default formula-decomposition)
            (%disable default
                      aggressive-equal-of-logic.pequals
                      aggressive-equal-of-logic.pnots
                      aggressive-equal-of-logic.pors
                      equal-of-2-and-len)
            (%auto :strategy (split cleanup urewrite crewrite)))

(encapsulate
 ()
 (local (%max-proof-size 700000000))
 (%autoprove logic.proofp-of-rw.compile-transitivity-trace
             (%use (%instance (%thm forcing-rw.trace-listp-of-rw.trace->subtraces)))
             (%restrict default logic.strip-conclusions          (memberp x '(proofs (cdr proofs))))
             (%restrict default definition-of-logic.appeal-listp (memberp x '(proofs (cdr proofs))))
             (%restrict default definition-of-logic.proof-listp  (memberp x '(proofs (cdr proofs))))
             (%restrict default rw.trace-list-formulas           (memberp x '((rw.trace->subtraces x) (cdr (rw.trace->subtraces x)))))
             (%restrict default definition-of-rw.trace-listp     (memberp x '((rw.trace->subtraces x) (cdr (rw.trace->subtraces x)))))
             (%auto :strategy (split cleanup urewrite crewrite))
             (%enable default formula-decomposition)
             (%disable default
                       aggressive-equal-of-logic.pequals
                       aggressive-equal-of-logic.pnots
                       aggressive-equal-of-logic.pors
                       equal-of-2-and-len)
             (%auto :strategy (split cleanup urewrite crewrite))))

