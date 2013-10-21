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
(include-book "utilities-5")
(%interactive)



(%autoadmit submapp1)

(%autoprove submapp1-when-not-consp
            (%restrict default submapp1 (equal domain 'domain)))

(%autoprove submapp1-of-cons
            (%restrict default submapp1 (equal domain '(cons a domain))))

(%autoprove booleanp-of-submapp1
            (%cdr-induction domain))

(%autoprove equal-of-lookups-when-memberp-of-submapp1-domain
            (%cdr-induction domain))

(%autoprove lookup-when-memberp-of-submapp1
            (%use (%instance (%thm equal-of-lookups-when-memberp-of-submapp1-domain))))



(%autoadmit submapp1-badguy)

(%autoprove submapp1-badguy-when-not-consp
            (%restrict default submapp1-badguy (equal domain 'domain)))

(%autoprove submapp1-badguy-of-cons
            (%restrict default submapp1-badguy (equal domain '(cons a domain))))

(%autoprove submapp1-badguy-membership-property
            (%cdr-induction domain)
            (%enable default submapp1-badguy-when-not-consp submapp1-badguy-of-cons))


(%autoprove submapp1-badguy-under-iff
            (%cdr-induction domain)
            (%enable default submapp1-badguy-when-not-consp submapp1-badguy-of-cons))

(%autoprove submapp1-when-submapp1-of-domain-superset-one
            (%use (%instance (%thm submapp1-badguy-membership-property) (domain domain1) (x x) (y y))))

(%autoprove submapp1-when-submapp1-of-domain-superset-two
            (%use (%instance (%thm submapp1-when-submapp1-of-domain-superset-one))))

(%autoprove submapp1-of-list-fix-one)

(%autoprove submapp1-of-list-fix-two
            (%cdr-induction domain))

(%autoprove submapp1-of-list-fix-three
            (%cdr-induction domain))



(%autoadmit submapp)

(%autoprove booleanp-of-submapp
            (%enable default submapp))

(%autoprove submapp-of-list-fix-one
            (%enable default submapp))

(%autoprove submapp-of-list-fix-two
            (%enable default submapp))

(%autoprove equal-of-lookups-when-submapp
            (%enable default submapp))

(%autoprove equal-of-cdrs-of-lookups-when-submapp
            (%disable default equal-of-lookups-when-submapp)
            (%use (%instance (%thm equal-of-lookups-when-submapp))))

(%autoprove lookup-when-lookup-in-submapp-one
            (%enable default submapp))

(%autoprove lookup-when-lookup-in-submapp-two
            (%use (%instance (%thm lookup-when-lookup-in-submapp-one))))



(%autoadmit submapp-badguy)

(%autoprove submapp-badguy-membership-property
            (%enable default submapp-badguy)
            (%use (%instance (%thm submapp1-badguy-membership-property)
                             (domain (domain x)))))

(%autoprove submapp-badguy-under-iff
            (%enable default submapp submapp-badguy))

(%autoprove subsetp-of-domains-when-submap
            (%use (%instance (%thm subsetp-badguy-membership-property) (x (domain x)) (y (domain y)))))

(%autoprove submapp-reflexive
            (%use (%instance (%thm submapp-badguy-membership-property) (x x) (y x))))

(%autoprove submapp-transitive
            (%use (%instance (%thm submapp-badguy-membership-property) (x x) (y z)))
            (%waterfall default 40)
            (%disable default equal-of-lookups-when-submapp)
            (%use (%instance (%thm equal-of-lookups-when-submapp) (a (cdr (submapp-badguy x z))) (x x) (y y)))
            (%use (%instance (%thm equal-of-lookups-when-submapp) (a (cdr (submapp-badguy x z))) (x y) (y z)))
            (%waterfall default 40))

(%autoprove submapp-transitive-alt)





(%autoprove lemma-for-submapp1-of-app
            (%use (%instance (%thm submapp1-badguy-membership-property) (domain (app d1 d2)) (x a) (y b))))

(%autoprove submapp1-of-app
            (%enable default lemma-for-submapp1-of-app))




(%autoprove lemma-for-submapp-of-cons-onto-map
            (%cdr-induction x))

(%autoprove submapp-of-cons-onto-map
            (%cdr-induction map)
            (%enable default lemma-for-submapp-of-cons-onto-map submapp))

(%autoprove lemma-for-submapp-when-unique-domains-and-subsetp
            (%cdr-induction x))

(%autoprove lemma2-for-submapp-when-unique-domains-and-subsetp
            (%enable default lemma-for-submapp-when-unique-domains-and-subsetp)
            (%cdr-induction x))

(%autoprove submapp-when-unique-domains-and-subsetp
            (%enable default lemma2-for-submapp-when-unique-domains-and-subsetp)
            (%use (%instance (%thm submapp-badguy-membership-property) (x x) (y y))))

(%autoprove lemma-for-submapp-of-app-when-submapp
            (%cdr-induction dom))

(%autoprove submapp-of-app-when-submapp
            (%enable default submapp lemma-for-submapp-of-app-when-submapp))

(%autoprove submapp-of-rev-when-uniquep
            (%enable default domain-of-rev)
            (%disable default [outside]rev-of-domain rev-of-domain))
