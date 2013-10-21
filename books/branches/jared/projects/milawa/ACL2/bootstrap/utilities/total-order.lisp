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
(include-book "primitives")
(%interactive)


(defsection consp-when-nothing-else-cheap
  (%prove (%rule consp-when-nothing-else-cheap
                 :hyps (list (%hyp (not (natp x)) :limit 0)
                             (%hyp (not (symbolp x)) :limit 0))
                 :lhs (consp x)
                 :rhs t))
  (%use (build.axiom (axiom-closed-universe)))
  (%auto)
  (%qed)
  (%enable default consp-when-nothing-else-cheap))

(%autoadmit <<)

(defmacro %<<-induction (x y)
  `(%induct (rank x)
            ((natp x) nil)
            ((natp y) nil)
            ((symbolp x) nil)
            ((symbolp y) nil)
            ((and (consp x)
                  (consp y))
             (((,x (car ,x)) (,y (car ,y)))
              ((,x (cdr ,x)) (,y (cdr ,y)))))))

(%autoprove booleanp-of-<<
            (%<<-induction x y)
            (%restrict default << (equal x 'x)))

(%autoprove irreflexivity-of-<<
            (%induct (rank x)
                     ((natp x) nil)
                     ((symbolp x) nil)
                     ((consp x)
                      (((x (car x)))
                       ((x (cdr x))))))
            (%restrict default << (equal x 'x)))

(%autoprove asymmetry-of-<<
            (%<<-induction x y)
            (%restrict default << (or (equal x 'x)
                                      (equal x 'y))))

(%autoprove transitivity-of-<<
            (%induct (rank x)
                     ((not (consp x))
                      nil)
                     ((consp x)
                      (((x (car x)) (y (car y)) (z (car z)))
                       ((x (cdr x)) (y (cdr y)) (z (cdr z))))))
            (%auto :strategy (cleanup split crewrite))
            (%restrict default << (or (equal x 'x)
                                      (equal x 'y)))
            (%auto :strategy (cleanup split crewrite elim)))

(%autoprove forcing-trichotomy-of-<<
            (%<<-induction x y)
            (%restrict default << (or (equal x 'x)
                                      (equal x 'y))))

(%ensure-exactly-these-rules-are-missing "../../utilities/total-order")

