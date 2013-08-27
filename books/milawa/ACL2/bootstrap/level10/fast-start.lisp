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
(include-book "crewrite")
(%interactive)



(%autoadmit rw.fast-flag-crewrite)
(%disable default rw.fast-flag-crewrite)
(%splitlimit 10)


(%rwn 1000)


(defsection fast-irrelevant-argument-reduction
  (%autoprove rw.fast-flag-crewrite-of-term-reduction
              (%restrict default rw.fast-flag-crewrite (and (equal flag ''term) (equal x 'x))))
  (%autoprove rw.fast-flag-crewrite-of-list-reduction
              (%restrict default rw.fast-flag-crewrite (and (equal flag ''list) (equal x 'x))))
  (%autoprove rw.fast-flag-crewrite-of-rule-reduction
              (%restrict default rw.fast-flag-crewrite (and (equal flag ''rule) (equal x 'x))))
  (%autoprove rw.fast-flag-crewrite-of-rules-reduction
              (%restrict default rw.fast-flag-crewrite (and (equal flag ''rules) (equal rule[s] 'rule[s]))))
  (%autoprove rw.fast-flag-crewrite-of-hyp-reduction
              (%restrict default rw.fast-flag-crewrite (and (equal flag ''hyp) (equal x 'x))))
  (%autoprove rw.fast-flag-crewrite-of-hyps-reduction
              (%restrict default rw.fast-flag-crewrite (and (equal flag ''hyps) (equal x 'x)))))


(defsection fast-flag-wrapper-functions
  (%autoadmit rw.fast-crewrite-core)
  (%autoadmit rw.fast-crewrite-core-list)
  (%autoadmit rw.fast-crewrite-try-rule)
  (%autoadmit rw.fast-crewrite-try-rules)
  (%autoadmit rw.fast-crewrite-try-match)
  (%autoadmit rw.fast-crewrite-try-matches)
  (%autoadmit rw.fast-crewrite-relieve-hyp)
  (%autoadmit rw.fast-crewrite-relieve-hyps))



(defsection rw.fast-flag-crewrite-removal
  (%autoprove rw.fast-flag-crewrite-of-term
              (%enable default rw.fast-crewrite-core)
              (%use (%thm rw.fast-flag-crewrite-of-term-reduction)))
  (%autoprove rw.fast-flag-crewrite-of-list
              (%enable default rw.fast-crewrite-core-list)
              (%use (%thm rw.fast-flag-crewrite-of-list-reduction)))
  (%autoprove rw.fast-flag-crewrite-of-rule
              (%enable default rw.fast-crewrite-try-rule)
              (%use (%thm rw.fast-flag-crewrite-of-rule-reduction)))
  (%autoprove rw.fast-flag-crewrite-of-rules
              (%enable default rw.fast-crewrite-try-rules)
              (%use (%thm rw.fast-flag-crewrite-of-rules-reduction)))
  (%autoprove rw.fast-flag-crewrite-of-match
              (%enable default rw.fast-crewrite-try-match))
  (%autoprove rw.fast-flag-crewrite-of-matches
              (%enable default rw.fast-crewrite-try-matches))
  (%autoprove rw.fast-flag-crewrite-of-hyp
              (%enable default rw.fast-crewrite-relieve-hyp)
              (%use (%thm rw.fast-flag-crewrite-of-hyp-reduction)))
  (%autoprove rw.fast-flag-crewrite-of-hyps
              (%enable default rw.fast-crewrite-relieve-hyps)
              (%use (%thm rw.fast-flag-crewrite-of-hyps-reduction))))




(local (%disable default
                 formula-decomposition
                 expensive-term/formula-inference
                 expensive-arithmetic-rules
                 expensive-arithmetic-rules-two
                 type-set-like-rules
                 unusual-memberp-rules
                 unusual-subsetp-rules
                 unusual-consp-rules
                 usual-consp-rules
                 same-length-prefixes-equal-cheap
                 forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                 equal-of-booleans-rewrite))

(local (%max-proof-size 0))

(%autoprove definition-of-rw.fast-crewrite-core
            (%use (%instance (%thm rw.fast-flag-crewrite) (flag 'term)))
            (%betamode nil)
            (%auto)
            (%betamode once))

(%autoprove definition-of-rw.fast-crewrite-core-list
            (%use (%instance (%thm rw.fast-flag-crewrite) (flag 'list))))

(%autoprove definition-of-rw.fast-crewrite-try-rule
            (%use (%instance (%thm rw.fast-flag-crewrite) (flag 'rule))))

(%autoprove definition-of-rw.fast-crewrite-try-rules
            (%use (%instance (%thm rw.fast-flag-crewrite) (flag 'rules))))

(%autoprove definition-of-rw.fast-crewrite-try-match
            (%use (%instance (%thm rw.fast-flag-crewrite) (flag 'match))))

(%autoprove definition-of-rw.fast-crewrite-try-matches
            (%use (%instance (%thm rw.fast-flag-crewrite) (flag 'matches))))

(%autoprove definition-of-rw.fast-crewrite-relieve-hyp
            (%use (%instance (%thm rw.fast-flag-crewrite) (flag 'hyp))))

(%autoprove definition-of-rw.fast-crewrite-relieve-hyps
            (%use (%instance (%thm rw.fast-flag-crewrite) (flag 'hyps))))




(%autoprove rw.fast-crewrite-core-list-when-not-consp
            (%restrict default definition-of-rw.fast-crewrite-core-list (equal x 'x)))

(%autoprove rw.fast-crewrite-core-list-of-cons
            (%restrict default definition-of-rw.fast-crewrite-core-list (equal x '(cons a x))))

(%autoprove len-of-rw.ftraces->rhses-of-rw.cresult->data-of-rw.fast-crewrite-core-list$
            (%autoinduct rw.fast-crewrite-list-induction))



(%autoprove rw.fast-crewrite-try-rules-when-not-consp
            (%restrict default definition-of-rw.fast-crewrite-try-rules (equal rule[s] 'rule[s])))

(%autoprove rw.fast-crewrite-try-rules-of-cons
            (%restrict default definition-of-rw.fast-crewrite-try-rules (equal rule[s] '(cons rule rules))))



(%autoprove rw.fast-crewrite-try-matches-when-not-consp
            (%restrict default definition-of-rw.fast-crewrite-try-matches (equal sigma[s] 'sigma[s])))

(%autoprove rw.fast-crewrite-try-matches-of-cons
            (%restrict default definition-of-rw.fast-crewrite-try-matches (equal sigma[s] '(cons sigma sigmas))))



(%autoprove rw.fast-crewrite-relieve-hyps-when-not-consp
            (%restrict default definition-of-rw.fast-crewrite-relieve-hyps (equal x 'x)))

(%autoprove rw.fast-crewrite-relieve-hyps-of-cons
            (%restrict default definition-of-rw.fast-crewrite-relieve-hyps (equal x '(cons a x))))

(%autoprove booleanp-of-rw.hypresult->successp-of-rw.fast-crewrite-relieve-hyps
            (%use (%instance (%thm definition-of-rw.fast-crewrite-relieve-hyps))))
