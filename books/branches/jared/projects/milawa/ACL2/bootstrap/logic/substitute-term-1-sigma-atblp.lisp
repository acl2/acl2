;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
(include-book "terms")
(%interactive)


(%defmap :map (logic.sigma-atblp x atbl)
         :key (logic.variablep x)
         :val (logic.term-atblp x atbl)
         :key-list (logic.variable-listp x)
         :val-list (logic.term-list-atblp x atbl)
         :val-of-nil nil)

;; (DEFSECTION LOGIC.SIGMA-ATBLP
;; (%AUTOADMIT LOGIC.SIGMA-ATBLP)
;; (%AUTOPROVE LOGIC.SIGMA-ATBLP-WHEN-NOT-CONSP
;;               (%RESTRICT DEFAULT LOGIC.SIGMA-ATBLP (EQUAL X 'X)))
;; (%AUTOPROVE LOGIC.SIGMA-ATBLP-OF-CONS
;;               (%RESTRICT DEFAULT LOGIC.SIGMA-ATBLP
;;                          (EQUAL X '(CONS A X))))
;; (%AUTOPROVE CONSP-WHEN-MEMBERP-OF-LOGIC.SIGMA-ATBLP
;;               (%CDR-INDUCTION X)
;;               (%AUTO)
;;               (%CAR-CDR-ELIM X))
;; (%AUTOPROVE CONSP-WHEN-MEMBERP-OF-LOGIC.SIGMA-ATBLP-ALT)
;; (%AUTOPROVE LOGIC.VARIABLEP-OF-CAR-WHEN-MEMBERP-OF-LOGIC.SIGMA-ATBLP
;;               (%CDR-INDUCTION X)
;;               (%AUTO)
;;               (%CAR-CDR-ELIM X))
;; (%AUTOPROVE LOGIC.VARIABLEP-WHEN-LOOKUP-IN-LOGIC.SIGMA-ATBLP
;;               (%CDR-INDUCTION X)
;;               (%AUTO)
;;               (%CAR-CDR-ELIM X))
;; (%AUTOPROVE LOGIC.TERM-ATBLP-OF-CDR-WHEN-MEMBERP-OF-LOGIC.SIGMA-ATBLP
;;               (%CDR-INDUCTION X)
;;               (%AUTO)
;;               (%CAR-CDR-ELIM X))
;; (%AUTOPROVE BOOLEANP-OF-LOGIC.SIGMA-ATBLP
;;               (%CDR-INDUCTION X))
;; (%AUTOPROVE LOGIC.SIGMA-ATBLP-OF-LIST-FIX
;;               (%CDR-INDUCTION X))



;; (ACL2::defttag disable-caching)

;; (ACL2::progn!
;;  (ACL2::set-raw-mode t)
;;  (ACL2::defun rw.cache-update (term trace cache)
;;               (declare (xargs :guard (and (logic.termp term)
;;                                           (rw.tracep trace)
;;                                           (rw.cachep cache)))
;;                        (ignore term trace))
;;               cache)
;;  (ACL2::defun rw.cache-lookup (term iffp cache)
;;               (declare (xargs :guard (and (logic.termp term)
;;                                           (booleanp iffp)
;;                                           (rw.cachep cache)))
;;                        (ignore term iffp cache))
;;               nil))



;; (%AUTORULE LOGIC.SIGMA-ATBLP-OF-APP)
;; (%CDR-INDUCTION X)
;; ;; (%auto):
;; (%cleanup)
;; ;; No progress
;; (%split)
;; ;; Progress; 11 goals remain
;; (%cleanup)
;; ;; Progress; 4 goals remain
;; (%cleanup)
;; ;; No progress
;; (%split)
;; ;; Progress; 8 goals remain
;; (%cleanup)
;; ;; No progress
;; (%split)
;; ;; No progress
;; (%distribute)
;; ;; No progress
;; (%urewrite default)
;; ;; Progress; 8 goals remain
;; (%cleanup)
;; ;; Progress; 7 goals remain
;; (%cleanup)
;; ;; No progress
;; (%split)
;; ;; No progress
;; (%distribute)
;; ;; No progress
;; (%urewrite default)
;; ;; No progress
;; (%profile)
;; (%crewrite default)                           ;; THE FIRST REWRITE
;; (%profile.report)
;; (%profile.clear)
;; ; Rewrote 7 clauses; 4 remain (0 forced)
;; ;; Progress; 4 goals remain
;; (%cleanup)
;; ;; No progress
;; (%split)
;; ;; Progress; 16 goals remain
;; (%cleanup)
;; ;; Progress; 7 goals remain
;; (%cleanup)
;; ;; No progress
;; (%split)
;; ;; No progress
;; (%distribute)
;; ;; No progress
;; (%urewrite default)
;; ;; No progress
;; (%crewrite default)                            ;; THE SECOND REWRITE
;; (%profile.report)

;; ;; No progress
;; (%auto-elim)
;; ;; Progress; 15 goals remain
;; (%cleanup)
;; ;; Progress; 8 goals remain
;; (%cleanup)
;; ;; No progress
;; (%split)
;; ;; No progress
;; (%distribute)
;; ;; No progress
;; (%urewrite default)
;; ;; Progress; 8 goals remain
;; (%cleanup)
;; ;; Progress; 8 goals remain
;; (%cleanup)
;; ;; No progress
;; (%split)
;; ;; Progress; 114 goals remain
;; (%cleanup)
;; ;; Progress; 0 goals remain
;; ;All goals have been proven.



;;   (%AUTOPROVE LOGIC.SIGMA-ATBLP-OF-REV
;;               (%CDR-INDUCTION X))
;;   (%AUTOPROVE LOGIC.SIGMA-ATBLP-OF-REMOVE-ALL-WHEN-LOGIC.SIGMA-ATBLP
;;               (%CDR-INDUCTION X))
;;   (%AUTOPROVE LOGIC.SIGMA-ATBLP-OF-REMOVE-DUPLICATES
;;               (%CDR-INDUCTION X))
;;   (%AUTOPROVE LOGIC.SIGMA-ATBLP-OF-DIFFERENCE-WHEN-LOGIC.SIGMA-ATBLP
;;               (%CDR-INDUCTION X))
;;   (%AUTOPROVE LOGIC.SIGMA-ATBLP-OF-SUBSET-WHEN-LOGIC.SIGMA-ATBLP
;;               (%CDR-INDUCTION X))
;;   (%AUTOPROVE LOGIC.SIGMA-ATBLP-OF-SUBSET-WHEN-LOGIC.SIGMA-ATBLP-ALT)
;;   (%AUTOPROVE LOGIC.VARIABLE-LISTP-OF-DOMAIN-WHEN-LOGIC.SIGMA-ATBLP
;;               (%CDR-INDUCTION X))
;;   (%AUTOPROVE LOGIC.TERM-LIST-ATBLP-OF-RANGE-WHEN-LOGIC.SIGMA-ATBLP
;;               (%CDR-INDUCTION X))
;;   (%AUTOPROVE MAPP-WHEN-LOGIC.SIGMA-ATBLP
;;               (%CDR-INDUCTION X))
;;   (%AUTOPROVE LOGIC.TERM-ATBLP-OF-CDR-OF-LOOKUP-WHEN-LOGIC.SIGMA-ATBLP
;;               (%CDR-INDUCTION X))
;;   (%AUTOPROVE
;;    CDR-OF-LOOKUP-UNDER-IFF-WHEN-LOGIC.SIGMA-ATBLP
;;    (%USE
;;        (%INSTANCE
;;             (%THM LOGIC.TERM-ATBLP-OF-CDR-OF-LOOKUP-WHEN-LOGIC.SIGMA-ATBLP)))
;;    (%DISABLE DEFAULT
;;              LOGIC.TERM-ATBLP-OF-CDR-OF-LOOKUP-WHEN-LOGIC.SIGMA-ATBLP)))



(%autoprove forcing-logic.sigma-atblp-of-pair-lists
            (%autoinduct pair-lists))



(%deflist logic.sigma-list-atblp (x atbl)
  (logic.sigma-atblp x atbl))

(%autoprove logic.sigma-atblp-of-second-when-logic.sigma-list-atblp)

(%autoprove forcing-logic.sigma-list-atblp-of-revappend-onto-each
            (%cdr-induction x))



(%deflist logic.sigma-list-list-atblp (x atbl)
  (logic.sigma-list-atblp x atbl))

