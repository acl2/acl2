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


(%autoadmit mapp)

(%autoprove mapp-when-not-consp
            (%restrict default mapp (equal x 'x)))

(%autoprove mapp-of-cons
            (%restrict default mapp (equal x '(cons a x))))

(%autoprove booleanp-of-mapp
            (%cdr-induction x))

(%autoprove mapp-of-list-fix
            (%cdr-induction x))

(%autoprove mapp-of-app
            (%cdr-induction x))



(%autoadmit cons-fix)

(%autoprove cons-fix-when-not-consp
            (%restrict default cons-fix (equal x 'x)))

(%autoprove cons-fix-when-consp
            (%restrict default cons-fix (equal x 'x)))

(%autoprove consp-of-cons-fix
            (%car-cdr-elim x))

(%autoprove cons-fix-under-iff
            (%car-cdr-elim x))

(%autoprove cons-fix-of-cons)

(%autoprove car-of-cons-fix)

(%autoprove cdr-of-cons-fix)



(%autoadmit lookup)

(%autoprove lookup-when-not-consp
            (%restrict default lookup (equal x 'x)))

(%autoprove lookup-of-cons
            (%restrict default lookup (equal x '(cons b x))))

(%autoprove lookup-of-list-fix
            (%cdr-induction x))

(%autoprove lookup-of-app
            (%cdr-induction x))

(%autoprove car-of-lookup-when-found
            (%cdr-induction map))

(%autoprove consp-of-lookup-under-iff
            (%cdr-induction x))



(%autoadmit update)

(%autoprove car-of-update
            (%enable default update))

(%autoprove cdr-of-update
            (%enable default update))

(%autoprove consp-of-update
            (%enable default update))

(%autoprove update-of-list-fix
            (%enable default update))

(%autoprove mapp-of-update-when-mapp
            ;; BOZO I think this should be forced
            (%enable default update))

(%autoprove lookup-of-update
            (%enable default update))



(%autoadmit domain)

(%autoprove domain-when-not-consp
            (%restrict default domain (equal x 'x)))

(%autoprove domain-of-cons
            (%restrict default domain (equal x '(cons a x))))

(%autoprove domain-of-list-fix
            (%cdr-induction x))

(%autoprove consp-of-domain)

(%autoprove true-listp-of-domain
            (%cdr-induction x))

(%autoprove domain-of-app
            (%cdr-induction x))

(%autoprove domain-of-update
            (%enable default update))

(%autoprove memberp-of-domain-when-memberp
            (%cdr-induction x))

(%autoprove memberp-of-domain-when-memberp-of-subset-domain
            (%cdr-induction x))

(%autoprove subsetp-of-domains
            (%use (%instance (%thm subsetp-badguy-membership-property)
                             (x (domain x))
                             (y (domain y)))))

(%autoprove uniquep-when-uniquep-of-domain
            (%cdr-induction x))

(%autoprove memberp-of-domain-under-iff
            (%cdr-induction x))

(%autoprove rev-of-domain
            (%cdr-induction x))

(%autoprove domain-of-rev)



(%autoadmit fast-domain$)

(%autoprove fast-domain$-when-not-consp
            (%restrict default fast-domain$ (equal x 'x)))

(%autoprove fast-domain$-of-cons
            (%restrict default fast-domain$ (equal x '(cons a x))))

(%autoprove forcing-fast-domain$-removal
            (%autoinduct fast-domain$)
            (%enable default fast-domain$-when-not-consp fast-domain$-of-cons))



(%autoadmit range)

(%autoprove range-when-not-consp
            (%restrict default range (equal x 'x)))

(%autoprove range-of-cons
            (%restrict default range (equal x '(cons a x))))

(%autoprove range-of-list-fix
            (%cdr-induction x))

(%autoprove true-listp-of-range
            (%cdr-induction x))

(%autoprove len-of-range
            (%cdr-induction x))

(%autoprove range-of-app
            (%cdr-induction x))



(%autoadmit fast-range$)

(%autoprove fast-range$-when-not-consp
            (%restrict default fast-range$ (equal x 'x)))

(%autoprove fast-range$-of-cons
            (%restrict default fast-range$ (equal x '(cons a x))))

(%autoprove forcing-fast-range$-removal
            (%autoinduct fast-range$)
            (%enable default fast-range$-when-not-consp fast-range$-of-cons))

