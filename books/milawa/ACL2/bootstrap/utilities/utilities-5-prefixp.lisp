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
(include-book "utilities-4")
(%interactive)



(%autoadmit prefixp)

(%autoprove prefixp-when-not-consp-one
            (%restrict default prefixp (equal x 'x)))

(%autoprove prefixp-when-not-consp-two
            (%restrict default prefixp (equal x 'x)))

(%autoprove prefixp-of-cons-and-cons
            (%restrict default prefixp (equal x '(cons a x)))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove booleanp-of-prefixp
            (%cdr-cdr-induction x y))

(%autoprove prefixp-of-list-fix-one
            (%cdr-cdr-induction x y))

(%autoprove prefixp-of-list-fix-two
            (%cdr-cdr-induction x y))

(%autoprove same-length-prefixes-equal-cheap
            (%cdr-cdr-induction x y))

(%autoprove prefixp-when-lengths-wrong
            (%cdr-cdr-induction x y))

(defsection prefixp-when-lengths-wrong-replacement
  ;; BOZO see if we still need this?  If so, change the ACL2 rule to
  ;; add a backchain limit.  Else, just use the above autoprove.
  (%prove (%rule prefixp-when-lengths-wrong-replacement
                 :hyps (list (%hyp (< (len y) (len x)) :limit 1))
                 :lhs (prefixp x y)
                 :rhs nil))
  (%auto)
  (%qed)
  (%disable default prefixp-when-lengths-wrong)
  (%enable default prefixp-when-lengths-wrong-replacement))



(%autoadmit prefixp-badguy)

(%autoprove prefixp-badguy-when-not-consp
            (%restrict default prefixp-badguy (equal x 'x)))

(%autoprove prefixp-badguy-of-cons
            (%restrict default prefixp-badguy (equal x '(cons a x)))
            (%auto :strategy (cleanup split crewrite)))

(local (%enable default prefixp-badguy-when-not-consp prefixp-badguy-of-cons))

(%autoprove natp-of-prefixp-badguy
            (%cdr-induction x))

(%autoprove lemma-for-prefixp-badguy-index-property
  (%induct (rank x)
           ((not (consp x))
            nil)
           ((consp x)
            (((x (cdr x))
              (y (cdr y)))))))

(%autoprove lemma-2-for-prefixp-badguy-index-property
  (%induct (rank x)
           ((not (consp x))
            nil)
           ((consp x)
            (((x (cdr x))
              (y (cdr y)))))))

(%autoprove prefixp-badguy-index-property
            (%enable default
                     lemma-for-prefixp-badguy-index-property
                     lemma-2-for-prefixp-badguy-index-property))

(%autoprove forcing-prefixp-when-not-prefixp-badguy
            (%cdr-cdr-induction x y))

(local (%disable default prefixp-badguy-when-not-consp prefixp-badguy-of-cons))



(%autoprove subsetp-when-prefixp-cheap
            (%cdr-cdr-induction x y))

