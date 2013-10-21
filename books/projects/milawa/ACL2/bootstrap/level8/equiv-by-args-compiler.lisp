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

(defthm equal-of-cons-and-repeat
  ;; BOZO a nice and useful rule in need of a good home
  (equal (equal (cons a x)
                (repeat b n))
         (and (not (zp n))
              (equal a b)
              (equal x (repeat b (- n 1))))))

(%autoprove equal-of-cons-and-repeat
            (%autoinduct repeat b n)
            (%restrict default repeat (equal n 'n)))


(%autoadmit rw.compile-equiv-by-args-trace)

(local (%enable default
                rw.trace-conclusion-formula
                rw.trace-formula
                rw.equiv-by-args-tracep
                rw.compile-equiv-by-args-trace))

(local (%disable default
                 expensive-arithmetic-rules
                 expensive-arithmetic-rules-two
                 type-set-like-rules
                 expensive-subsetp-rules
                 same-length-prefixes-equal-cheap
                 formula-decomposition))

(%autoprove rw.compile-equiv-by-args-trace-under-iff)

(%autoprove logic.appealp-of-rw.compile-equiv-by-args-trace)

(%autoprove lemma-for-logic.conclusion-of-rw.compile-equiv-by-args-trace
            (%enable default logic.function-name logic.function-args))

(local (%enable default lemma-for-logic.conclusion-of-rw.compile-equiv-by-args-trace))

(%autoprove logic.conclusion-of-rw.compile-equiv-by-args-trace
            (%auto)
            (%enable default
                     type-set-like-rules
                     formula-decomposition
                     expensive-arithmetic-rules-two)
            (%disable default
                      aggressive-equal-of-logic.pequals
                      aggressive-equal-of-logic.pors
                      aggressive-equal-of-logic.pnots
                      equal-of-logic.function-rewrite
                      equal-of-logic.function-rewrite-alt))

(%autoprove lemma-1-for-logic.proofp-of-rw.compile-equiv-by-args-trace
            (%disable default
                      len-of-rw.trace-list-conclusion-formulas
                      [outside]len-of-rw.trace-list-conclusion-formulas)
            (%use (%instance (%thm len-of-rw.trace-list-conclusion-formulas)
                             (x (rw.trace->subtraces x)))))

(%autoprove lemma-2-for-logic.proofp-of-rw.compile-equiv-by-args-trace
            (%disable default
                      len-of-rw.trace-list-conclusion-formulas
                      [outside]len-of-rw.trace-list-conclusion-formulas)
            (%use (%instance (%thm len-of-rw.trace-list-conclusion-formulas)
                             (x (rw.trace->subtraces x)))))

(%autoprove lemma-3-for-logic.proofp-of-rw.compile-equiv-by-args-trace)

(%autoprove logic.proofp-of-rw.compile-equiv-by-args-trace
            (%enable default
                            lemma-1-for-logic.proofp-of-rw.compile-equiv-by-args-trace
                            lemma-2-for-logic.proofp-of-rw.compile-equiv-by-args-trace
                            lemma-3-for-logic.proofp-of-rw.compile-equiv-by-args-trace)
            (%auto)
            (%enable default
                     type-set-like-rules
                     expensive-arithmetic-rules-two))

