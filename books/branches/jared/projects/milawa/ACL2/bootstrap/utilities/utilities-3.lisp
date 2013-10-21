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
(include-book "utilities-2")
(%interactive)



(%autoadmit rev)

(%autoprove rev-when-not-consp
            (%restrict default rev (equal x 'x)))

(%autoprove rev-of-cons
            (%restrict default rev (equal x '(cons a x))))

(%autoprove rev-of-list-fix
            (%cdr-induction x))

(%autoprove true-listp-of-rev
            (%car-cdr-elim x))

(%autoprove rev-under-iff)

(%autoprove len-of-rev
            (%cdr-induction x))

(%autoprove memberp-of-rev
            (%cdr-induction x))

(%autoprove memberp-of-first-of-rev
            (%cdr-induction x))

(%autoprove subsetp-of-rev-one
            (%use (%instance (%thm subsetp-badguy-membership-property) (x (rev x)) (y x)))
            (%use (%instance (%thm subsetp-badguy-membership-property) (x x) (y (rev x)))))

(%autoprove subsetp-of-rev-two
            (%use (%instance (%thm subsetp-badguy-membership-property) (x y) (y (rev y))))
            (%use (%instance (%thm subsetp-badguy-membership-property) (x (rev y)) (y y))))

(%autoprove lemma-for-rev-of-rev
            (%cdr-induction x))

(%autoprove rev-of-rev
            (%cdr-induction x)
            (%enable default lemma-for-rev-of-rev))

(%autoprove rev-of-app
            (%cdr-induction x)
            (%auto)
            (%fertilize (rev (app x2 y)) (app (rev y) (rev x2))))

(%autoprove subsetp-of-app-of-rev-of-self-one
            (%cdr-induction x))

(%autoprove subsetp-of-app-of-rev-of-self-two
            (%cdr-induction x))



(%autoadmit revappend)

(%autoprove revappend-when-not-consp
            (%restrict default revappend (equal x 'x)))

(%autoprove revappend-of-cons
            (%restrict default revappend (equal x '(cons a x))))

(%autoprove forcing-revappend-removal
            (%autoinduct revappend)
            (%enable default revappend-when-not-consp revappend-of-cons))



(%autoadmit fast-rev)

(%autoprove fast-rev-removal
            (%enable default fast-rev))



(%autoadmit fast-app)

(%autoprove fast-app-removal
            (%enable default fast-app))

