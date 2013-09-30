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
(include-book "deflist")
(include-book "cons-listp")
(%interactive)



(%deflist member-of-nonep (e x)
          (memberp e x)
          :negatedp t)


(%autoadmit lists-lookup)
(%autoprove lists-lookup-when-not-consp (%restrict default lists-lookup (equal xs 'xs)))
(%autoprove lists-lookup-of-cons (%restrict default lists-lookup (equal xs '(cons x xs))))
(%autoprove lists-lookup-of-list-fix (%cdr-induction xs))
(%autoprove lists-lookup-of-app (%cdr-induction xs))
(%autoprove consp-of-lists-lookup (%cdr-induction xs))
(%autoprove lists-lookup-under-iff (%cdr-induction xs))
(%autoprove lists-lookup-of-rev-under-iff (%cdr-induction xs))
(%autoprove memberp-of-element-in-lists-lookup (%cdr-induction xs))
(%autoprove memberp-of-in-lists-lookup-in-lists (%cdr-induction xs))



(%deflist none-consp (x)
          (consp x)
          :negatedp t)

(%deflist disjoint-from-allp (e x)
          (disjointp e x))

(%autoprove disjoint-from-allp-when-not-consp-left (%cdr-induction x))
(%autoprove disjoint-from-allp-of-cons-left (%cdr-induction x))
(%autoprove disjoint-from-allp-of-cdr-left)
(%autoprove member-of-nonep-when-memberp-of-disjoint-from-allp (%cdr-induction x))
(%autoprove member-of-nonep-when-memberp-of-disjoint-from-allp-alt)
(%autoprove disjointp-when-memberp-of-disjoint-from-allp-one (%cdr-induction ys))
(%autoprove disjointp-when-memberp-of-disjoint-from-allp-two (%cdr-induction ys))
(%autoprove disjointp-when-memberp-of-disjoint-from-allp-three)
(%autoprove disjointp-when-memberp-of-disjoint-from-allp-four)
(%autoprove disjoint-from-allp-when-subsetp-of-disjoint-from-allp-one (%cdr-induction x))
(%autoprove disjoint-from-allp-when-subsetp-of-disjoint-from-allp-two)
(%autoprove disjoint-from-allp-when-subsetp-of-disjoint-from-allp-three (%cdr-induction ys))
(%autoprove disjoint-from-allp-when-subsetp-of-disjoint-from-allp-four)

(%autoprove disjoint-from-allp-when-memberp (%cdr-induction ys))
(%autoprove disjoint-from-allp-of-list-fix-left)
(%autoprove disjoint-from-allp-of-app-left (%cdr-induction x))
(%autoprove disjoint-from-allp-of-rev-left (%cdr-induction x))
(%autoprove remove-all-when-disjoint-from-allp-and-cons-listp (%cdr-induction x))


(%autoadmit all-disjoint-from-allp)
(%autoprove all-disjoint-from-allp-when-not-consp-one (%restrict default all-disjoint-from-allp (equal xs 'xs)))
(%autoprove all-disjoint-from-allp-of-cons-one (%restrict default all-disjoint-from-allp (equal xs '(cons x xs))))
(%autoprove all-disjoint-from-allp-when-not-consp-two (%cdr-induction xs))
(%autoprove all-disjoint-from-allp-of-cons-two (%cdr-induction xs))
(%autoprove booleanp-of-all-disjoint-from-allp (%cdr-induction xs))
(%autoprove symmetry-of-all-disjoint-from-allp (%cdr-induction xs))
(%autoprove all-disjoint-from-allp-of-list-fix-two (%cdr-induction ys))
(%autoprove all-disjoint-from-allp-of-list-fix-one)
(%autoprove all-disjoint-from-allp-of-app-two (%cdr-induction ys))
(%autoprove all-disjoint-from-allp-of-app-one)
(%autoprove all-disjoint-from-allp-of-rev-two (%cdr-induction ys))
(%autoprove all-disjoint-from-allp-of-rev-one)
(%autoprove all-disjoint-from-allp-when-subsetp-of-other-one (%cdr-induction xs))
(%autoprove all-disjoint-from-allp-when-subsetp-of-other-two)
(%autoprove disjoint-from-allp-when-memberp-of-all-disjoint-from-allp-one (%cdr-induction xs))
(%autoprove disjoint-from-allp-when-memberp-of-all-disjoint-from-allp-two (%cdr-induction ys))
(%autoprove disjointp-when-members-of-all-disjoint-from-allp (%cdr-induction xs))
(%autoprove all-disjoint-from-allp-when-subsetp-of-all-disjoint-one (%cdr-induction xs))
(%autoprove all-disjoint-from-allp-when-subsetp-of-all-disjoint-two)
(%autoprove all-disjoint-from-allp-when-subsetp-of-all-disjoint-three (%cdr-induction ys))
(%autoprove all-disjoint-from-allp-when-subsetp-of-all-disjoint-four)


(%autoadmit mutually-disjointp)
(%autoprove mutually-disjointp-when-not-consp (%restrict default mutually-disjointp (equal xs 'xs)))
(%autoprove mutually-disjointp-of-cons (%restrict default mutually-disjointp (equal xs '(cons x xs))))
(%autoprove booleanp-of-mutually-disjointp (%cdr-induction xs))
(%autoprove mutually-disjointp-of-cdr-when-mutually-disjointp)
(%autoprove mutually-disjointp-of-list-fix (%cdr-induction x))
(%autoprove mutually-disjointp-of-app (%cdr-induction x))
(%autoprove mutually-disjointp-of-rev (%cdr-induction x))
(%autoprove mutually-disjointp-of-remove-all-when-mutually-disjointp (%cdr-induction x))
(%autoprove disjointp-when-both-membersp-of-mutually-disjointp (%cdr-induction xs))


(%autoadmit disjoint-from-allp-badguy)

(defsection disjoint-from-allp-badguy-property
  ;; BOZO the lemmas need to be unlocalized, and the defthm needs to be added to
  ;; :rule-classes nil instead of just using defthmd, since it screws up autoprove
  ;; to have dual conclusions.  Actually, do we want to switch this the way that we
  ;; have done for subsetp-badguy and use the iff rule or whatever?
  (%prove (%rule disjoint-from-allp-badguy-property
                 :hyps (list (%hyp (not (disjoint-from-allp x ys))))
                 :lhs (and (memberp (disjoint-from-allp-badguy x ys) ys)
                           (not (disjointp x (disjoint-from-allp-badguy x ys))))
                 :rhs t))
  (%cdr-induction ys)
  (%restrict default disjoint-from-allp-badguy (equal ys 'ys))
  (%auto)
  (%qed))

(%autoprove disjoint-from-allp-of-remove-all-when-memberp-of-mutually-disjointp
            (%use (%instance (%thm disjoint-from-allp-badguy-property)
                             (x x)
                             (ys (remove-all x xs)))))

(%autoprove member-of-nonep-of-remove-all-when-mutually-disjointp
            (%cdr-induction xs))

(%autoprove disjoint-from-allp-when-subsetp-of-remove-all-of-mutually-disjointp)
(%autoprove disjoint-from-allp-when-subsetp-of-remove-all-of-mutually-disjointp-two)



(%autoprove lists-lookup-of-rev-when-mutually-disjointp (%cdr-induction xs))
(%autoprove lists-lookup-when-memberp-in-lists-lookup-when-mutually-disjointp (%cdr-induction xs))

(%autoprove lists-lookup-of-remove-all-from-mutually-disjointp
            (%cdr-induction xs))

(%autoprove lists-lookup-when-mutually-disjointp
            (%cdr-induction xs))

(%autoprove lists-lookup-of-car-of-lists-lookup
            (%use (%instance (%thm lists-lookup-when-mutually-disjointp)
                             (x (lists-lookup a xs))
                             (b (car (lists-lookup a xs))))))

(%autoprove member-of-nonep-when-member-of-lists-lookup
            (%cdr-induction xs))

(%autoprove member-of-nonep-when-member-of-cdr-of-lists-lookup
            (%use (%thm member-of-nonep-when-member-of-lists-lookup)))

(%autoprove member-of-nonep-of-car-of-lists-lookup
            (%cdr-induction xs))

(%autoprove member-of-lists-lookup-when-members-of-mutually-disjointp
            (%auto)
            (%fertilize (lists-lookup a xs) (lists-lookup c xs)))



(%deflist disjoint-from-nonep (e x)
          (disjointp e x)
          :negatedp t)

(%autoprove disjoint-from-nonep-when-not-consp-left (%cdr-induction x))
(%autoprove disjoint-from-nonep-of-cons-left        (%cdr-induction x))
(%autoprove disjoint-from-nonep-of-list-fix-left    (%cdr-induction x))
(%autoprove disjoint-from-nonep-of-app-left-one     (%cdr-induction x))
(%autoprove disjoint-from-nonep-of-app-left-two     (%cdr-induction x))
(%autoprove disjoint-from-nonep-of-rev-left         (%cdr-induction x))

(%ensure-exactly-these-rules-are-missing "../../utilities/mutually-disjoint")

