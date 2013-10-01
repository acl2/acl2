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
(include-book "utilities")
(%interactive)


(%autoadmit ordered-subsetp)

(%autoprove ordered-subsetp-when-not-consp-one
            (%restrict default ordered-subsetp (equal y 'y)))

(%autoprove ordered-subsetp-when-not-consp-two
            (%restrict default ordered-subsetp (equal y 'y)))

(%autoprove ordered-subsetp-of-cons-and-cons
            (%restrict default ordered-subsetp (equal y '(cons b y))))

(%autoprove booleanp-of-ordered-subsetp
            (%autoinduct ordered-subsetp))

(%autoprove ordered-subsetp-of-cdr-when-ordered-subsetp
            (%induct (rank y)
                     ((or (not (consp x))
                          (not (consp y)))
                      nil)
                     ((and (consp x)
                           (consp y))
                      (((x (cdr x)) (y (cdr y)))
                       ((x x) (y (cdr y)))))))

(%autoprove ordered-subsetp-when-ordered-subsetp-of-cons
            (%use (%instance (%thm ordered-subsetp-of-cdr-when-ordered-subsetp)
                             (x (cons a x))
                             (y y))))

(%autoprove ordered-subsetp-of-cons-when-ordered-subsetp
            (%restrict default ordered-subsetp (equal y '(cons a y))))

(%autoprove ordered-subsetp-when-ordered-subsetp-of-cdr)

(%autoprove ordered-subsetp-is-reflexive
            (%cdr-induction x))

(%autoprove ordered-subsetp-is-transitive
            (%induct (+ (rank x) (+ (rank y) (rank z)))
                     ((or (not (consp x))
                          (not (consp y))
                          (not (consp z)))
                      nil)
                     ((and (consp x)
                           (consp y)
                           (consp z))
                      (((x (cdr x)) (y (cdr y)) (z (cdr z)))
                       ((x (cdr x)) (y (cdr y)) (z z))
                       ((x x) (y (cdr y)) (z (cdr z)))
                       ((x x) (y y) (z (cdr z))))))
            ;; These seem to be expensive here.  In fact this rewrite is pretty slow.
            (%disable default squeeze-law-two |a <= b, c != 0 --> a < c+b|))

(%autoprove ordered-subsetp-of-list-fix-one (%autoinduct ordered-subsetp))
(%autoprove ordered-subsetp-of-list-fix-two (%autoinduct ordered-subsetp))
(%autoprove ordered-subsetp-of-app-when-ordered-subsetp-one (%autoinduct ordered-subsetp))
(%autoprove ordered-subsetp-of-app-one)
(%autoprove ordered-subsetp-of-app-two (%cdr-induction y))
(%autoprove ordered-subsetp-of-app-when-ordered-subsetp-two)
(%autoprove subsetp-when-ordered-subsetp (%autoinduct ordered-subsetp))
(%autoprove ordered-subsetp-of-remove-duplicates (%cdr-induction x))
(%autoprove ordered-subsetp-of-remove-all (%cdr-induction x))
(%autoprove ordered-subsetp-of-difference (%cdr-induction x))

(%ensure-exactly-these-rules-are-missing "../../utilities/ordered-subsetp")