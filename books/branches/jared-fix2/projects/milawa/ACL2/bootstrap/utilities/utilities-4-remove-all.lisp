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
(include-book "utilities-3")
(%interactive)



(%autoadmit remove-all)

(%autoprove remove-all-when-not-consp
            (%restrict default remove-all (equal x 'x)))

(%autoprove remove-all-of-cons
            (%restrict default remove-all (equal x '(cons b x))))

(%autoprove remove-all-of-list-fix
            (%cdr-induction x))

(%autoprove true-listp-of-remove-all
            (%cdr-induction x))

(%autoprove memberp-of-remove-all
            (%cdr-induction x))

(%autoprove remove-all-of-app
            (%cdr-induction x))

(%autoprove rev-of-remove-all
            (%cdr-induction x))

(%autoprove subsetp-of-remove-all-with-x
            (%cdr-induction x))

(%autoprove subsetp-of-remove-all-with-remove-all
            (%use (%instance (%thm subsetp-badguy-membership-property)
                             (x (remove-all a x))
                             (y (remove-all a y)))))

(%autoprove subsetp-of-remove-all-when-subsetp)

(%autoprove remove-all-of-non-memberp
            (%cdr-induction x))

(%autoprove remove-all-of-remove-all
            (%cdr-induction x))

(%autoprove subsetp-of-cons-and-remove-all-two
            (%use (%instance (%thm subsetp-badguy-membership-property)
                             (x (cons a y))
                             (y (cons a (remove-all a y))))))




(%autoprove lemma-for-equal-of-len-of-remove-all-and-len
            (%cdr-induction x))

(%autoprove equal-of-len-of-remove-all-and-len
            (%enable default lemma-for-equal-of-len-of-remove-all-and-len))


(%autoadmit fast-remove-all$)

(%autoprove fast-remove-all$-when-not-consp
            (%restrict default fast-remove-all$ (equal x 'x)))

(%autoprove fast-remove-all$-of-cons
            (%restrict default fast-remove-all$ (equal x '(cons b x))))

(%autoprove forcing-fast-remove-all$-removal
            (%autoinduct fast-remove-all$)
            (%enable default fast-remove-all$-when-not-consp fast-remove-all$-of-cons))
