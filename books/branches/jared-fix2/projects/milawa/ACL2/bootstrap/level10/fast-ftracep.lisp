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
;;       Copyright (C) 2005-2007 by Jared Davis <jared@cs.utexas.edu>        ;;
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
(include-book "fast-start")
(%interactive)

(local (include-book "crewrite-local-settings"))
(local (%max-proof-size 0))

(%autoprove lemma-for-forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-core

            (%quiet t)
            (%forcingp nil)
            (%splitlimit 2)
            (%liftlimit 10)
            (%rwn 20)
            (%urwn 20)

            (%autoinduct rw.fast-flag-crewrite flag assms x rule[s] sigma[s]
                         cache iffp blimit rlimit anstack control)

            (%disable default
                      forcing-lookup-of-logic.function-name
                      forcing-lookup-of-logic.function-name-free)

            (%waterfall default 40) ;; 476 seconds, 7 GB, 3.8 allocated at finish, 1120 remain, 2.7 freed after gc

            (%enable default
                     splitters
                     special-disables-for-fast-pruning)
            (%betamode once)

            (%waterfall default 40) ;; 365 seconds, 5.2 gb allocated, 806 remain, 2.35 gb at finish, 1 freed after gc

            (%cleanup) ;; 796 goals

            (%restrict default definition-of-rw.fast-crewrite-core (equal x 'x))
            (%restrict default definition-of-rw.fast-crewrite-try-rule (equal x 'x) (equal rule[s] 'rule[s]))
            (%restrict default definition-of-rw.fast-crewrite-try-match (equal x 'x) (equal sigma[s] 'sigma[s]))
            (%restrict default definition-of-rw.fast-crewrite-relieve-hyp (equal x 'x))

            (%disable default ;; speed hint
                      rw.fast-crewrite-try-rules-when-not-consp)

; I used this trick in fast-image.  Will it work here?  The size to beat is 27 GC.  wow, down to 4bn.
; this is freaking wonderful.

            ;(%urwn 50)
            (%betamode t)
            (%crewrite default)
            (%waterfall default 40) ;; 414 seconds, 9.7 GB allocated, 173 remain, 4.78 gb at finish, 3.1 freed by gc

            (%enable default
                     expensive-term/formula-inference
                     formula-decomposition
                     rw.crewrite-try-rules-when-not-consp
                     rw.tracep-when-memberp-of-rw.trace-listp
                     expensive-arithmetic-rules
                     expensive-arithmetic-rules-two
                     type-set-like-rules
                     usual-consp-rules
                     unusual-consp-rules
                     unusual-memberp-rules
                     unusual-subsetp-rules
                     min
                     equal-of-booleans-rewrite
                     )

            (%waterfall default 40) ;; 695 seconds, 11 GB allocated, 4.6 GB allocated at finish, 2.9 freed by gc, 20 goals remain
            (%auto))


(%autoprove forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-core
            (%use (%instance (%thm lemma-for-forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-core)
                             (flag 'term))))

(%autoprove forcing-rw.fast-cachep-of-rw.cresult->cache-of-rw.fast-crewrite-core
            (%use (%instance (%thm lemma-for-forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-core)
                             (flag 'term))))

(%autoprove forcing-rw.ftracesp-of-rw.cresult->data-of-rw.fast-crewrite-core-list
            (%use (%instance (%thm lemma-for-forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-core)
                             (flag 'list))))

(%autoprove forcing-rw.fast-cachep-of-rw.cresult->cache-of-rw.fast-crewrite-core-list
            (%use (%instance (%thm lemma-for-forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-core)
                             (flag 'list))))

(%autoprove forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-try-rule
            (%use (%instance (%thm lemma-for-forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-core)
                             (flag 'rule))))

(%autoprove forcing-rw.fast-cachep-of-rw.cresult->cache-of-rw.fast-crewrite-try-rule
            (%use (%instance (%thm lemma-for-forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-core)
                             (flag 'rule))))

(%autoprove forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-try-rules
            (%use (%instance (%thm lemma-for-forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-core)
                             (flag 'rules))))

(%autoprove forcing-rw.fast-cachep-of-rw.cresult->cache-of-rw.fast-crewrite-try-rules
            (%use (%instance (%thm lemma-for-forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-core)
                             (flag 'rules))))

(%autoprove forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-try-match
            (%use (%instance (%thm lemma-for-forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-core)
                             (flag 'match))))

(%autoprove forcing-rw.fast-cachep-of-rw.cresult->cache-of-rw.fast-crewrite-try-match
            (%use (%instance (%thm lemma-for-forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-core)
                             (flag 'match))))

(%autoprove forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-try-matches
            (%use (%instance (%thm lemma-for-forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-core)
                             (flag 'matches))))

(%autoprove forcing-rw.fast-cachep-of-rw.cresult->cache-of-rw.fast-crewrite-try-matches
            (%use (%instance (%thm lemma-for-forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-core)
                             (flag 'matches))))

(%autoprove forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-relieve-hyp
            (%use (%instance (%thm lemma-for-forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-core)
                             (flag 'hyp))))

(%autoprove forcing-rw.fast-cachep-of-rw.cresult->cache-of-rw.fast-crewrite-relieve-hyp
            (%use (%instance (%thm lemma-for-forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-core)
                             (flag 'hyp))))

(%autoprove forcing-rw.ftracesp-of-rw.hypresult->traces-of-rw.fast-crewrite-relieve-hyps
            (%use (%instance (%thm lemma-for-forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-core)
                             (flag 'hyps))))

(%autoprove forcing-rw.fast-cachep-of-rw.hypresult->cache-of-rw.fast-crewrite-relieve-hyps
            (%use (%instance (%thm lemma-for-forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-core)
                             (flag 'hyps))))

