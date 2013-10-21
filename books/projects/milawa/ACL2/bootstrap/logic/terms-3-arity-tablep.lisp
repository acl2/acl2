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
(include-book "terms-2")
(%interactive)

(%defmap :map (logic.arity-tablep x)
         :key (logic.function-namep x)
         :val (natp x)
         :key-list (logic.function-symbol-listp x)
         :val-list (nat-listp x)
         :val-of-nil nil)

(%autoprove logic.arity-tablep-of-halve-list
            (%disable default
                      halve-list-correct
                      [outside]halve-list-correct
                      logic.arity-tablep-of-list-fix
                      [outside]logic.arity-tablep-of-list-fix
                      logic.arity-tablep-of-subset-when-logic.arity-tablep)
            (%use (%instance (%thm halve-list-correct)))
            (%use (%instance (%thm logic.arity-tablep-of-list-fix)))
            (%auto :strategy (cleanup split urewrite))
            (%fertilize (list-fix x)
                        (app (rev (car (halve-list x)))
                             (cdr (halve-list x))))
            (%auto)
            (%fertilize (list-fix x)
                        (app (rev (car (halve-list x)))
                             (cdr (halve-list x))))
            (%auto))

(%autoprove logic.arity-tablep-of-halve-list-1
            (%use (%instance (%thm logic.arity-tablep-of-halve-list))))

(%autoprove logic.arity-tablep-of-halve-list-2
            (%use (%instance (%thm logic.arity-tablep-of-halve-list))))

(%autoprove logic.arity-tablep-of-merge-maps
            (%autoinduct merge-maps x y)
            (%restrict default merge-maps (and (equal x 'x) (equal y 'y)))
            (%disable default
                      logic.arity-tablep-of-subset-when-logic.arity-tablep
                      LOGIC.ARITY-TABLEP-WHEN-NOT-CONSP))

(%autoprove logic.arity-tablep-of-mergesort-map
            (%autoinduct mergesort-map)
            (%restrict default mergesort-map (equal x 'x))
            (%disable default
                      logic.arity-tablep-of-subset-when-logic.arity-tablep
                      LOGIC.ARITY-TABLEP-WHEN-NOT-CONSP
                      MERGESORT-MAP-WHEN-NOT-CONSP-OF-CDR
                      MERGESORT-MAP-WHEN-NOT-CONSP
                      ))
