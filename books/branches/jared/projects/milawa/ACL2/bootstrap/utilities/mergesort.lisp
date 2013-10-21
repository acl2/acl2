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
(include-book "total-order")
(%interactive)


(%autoprove mapp-of-rev
            (%cdr-induction x))

(%autoadmit halve-list-aux)

(%autoadmit halve-list)

(%autoprove halve-list-aux-when-not-consp
            (%autoinduct halve-list-aux)
            (%restrict default halve-list-aux (equal x 'x)))

(%autoprove halve-list-aux-when-not-consp-of-cdr
            (%autoinduct halve-list-aux)
            (%restrict default halve-list-aux (equal x 'x)))

(%autoprove halve-list-aux-append-property
            (%autoinduct halve-list-aux)
            (%restrict default halve-list-aux (equal x 'x)))

(%autoprove halve-list-aux-len-1
            (%autoinduct halve-list-aux)
            (%restrict default halve-list-aux (equal x 'x)))

(%autoprove halve-list-aux-len-2
            (%autoinduct halve-list-aux)
            (%restrict default halve-list-aux (equal x 'x)))

(%autoprove halve-list-correct
            (%enable default halve-list))

(%autoprove halve-list-len-1
            (%enable default halve-list)
            (%disable default halve-list-aux-len-1)
            (%use (%instance (%thm halve-list-aux-len-1)
                             (mid x) (x x) (acc nil))))

(%autoprove halve-list-len-2
            (%enable default halve-list))

(%autoprove halve-list-membership-property
            (%disable default memberp-of-app)
            (%use (%instance (%thm memberp-of-app)
                             (x (rev (car (halve-list x))))
                             (y (cdr (halve-list x))))))

(%autoprove halve-list-lookup-property
            (%disable default lookup-of-app)
            (%use (%instance (%thm lookup-of-app)
                             (x (rev (car (halve-list x))))
                             (y (cdr (halve-list x))))))

(%autoprove mapp-of-first-of-halve-list-aux-1
            (%autoinduct halve-list-aux)
            (%restrict default halve-list-aux (equal x 'x)))

(%autoprove mapp-of-first-of-halve-list-aux-2
            (%autoinduct halve-list-aux)
            (%restrict default halve-list-aux (equal x 'x)))

(%autoprove mapp-of-first-of-halve-list-1
            (%enable default halve-list))

(%autoprove mapp-of-first-of-halve-list-2
            (%enable default halve-list))


(%autoadmit ordered-listp)

(%autoprove ordered-listp-when-not-consp
            (%restrict default ordered-listp (equal x 'x)))

(%autoprove ordered-listp-when-not-consp-of-cdr
            (%restrict default ordered-listp (equal x 'x)))

(%autoprove ordered-listp-of-cons
            (%restrict default ordered-listp (equal x '(cons a x))))

(%autoprove booleanp-of-ordered-listp
            (%cdr-induction x))

(%autoprove lemma-for-uniquep-when-ordered-listp
            (%cdr-induction x))

(%autoprove uniquep-when-ordered-listp
            (%cdr-induction x)
            (%enable default lemma-for-uniquep-when-ordered-listp))


(%autoadmit merge-lists)

(%autoprove merge-lists-when-not-consp-left
            (%restrict default merge-lists (and (equal x 'x) (equal y 'y))))

(%autoprove merge-lists-when-not-consp-right
            (%restrict default merge-lists (and (equal x 'x) (equal y 'y))))

(%autoprove merge-lists-of-cons-and-cons
            (%restrict default merge-lists (and (or (equal x '(cons a x))
                                                    (equal x '(cons b x)))
                                                (or (equal y '(cons a y))
                                                    (equal y '(cons b y))))))

(%autoprove consp-of-merge-lists
            (%autoinduct merge-lists)
            (%restrict default merge-lists (and (equal x 'x) (equal y 'y))))

(%autoprove smaller-than-merge-lists
            (%autoinduct merge-lists)
            (%restrict default merge-lists (and (equal x 'x) (equal y 'y))))

(%autoprove ordered-listp-of-merge-lists
            (%autoinduct merge-lists)
            (%restrict default merge-lists (and (equal x 'x) (equal y 'y))))

(%autoprove memberp-of-merge-lists
            (%autoinduct merge-lists)
            (%restrict default merge-lists (and (equal x 'x) (equal y 'y))))


(%autoadmit mergesort)

(%autoprove mergesort-when-not-consp
            (%restrict default mergesort (equal x 'x)))

(%autoprove mergesort-when-not-consp-of-cdr
            (%restrict default mergesort (equal x 'x)))

(%autoprove ordered-listp-of-mergesort
            (%autoinduct mergesort)
            (%restrict default mergesort (equal x 'x)))

(%autoprove uniquep-of-mergesort
            (%enable default uniquep-when-ordered-listp))

(%autoprove lemma-for-memberp-of-mergesort
            (%use (%instance (%thm halve-list-membership-property))))

(%autoprove lemma-2-for-memberp-of-mergesort
            (%use (%instance (%thm halve-list-membership-property))))

(%autoprove memberp-of-mergesort
            (%autoinduct mergesort)
            (%restrict default mergesort (equal x 'x))
            (%auto :strategy (cleanup split urewrite crewrite))
            (%enable default
                     lemma-for-memberp-of-mergesort
                     lemma-2-for-memberp-of-mergesort))

(%autoprove subsetp-of-mergesort-left
            (%use (%instance (%thm subsetp-badguy-membership-property)
                             (x (mergesort x))
                             (y y)))
            (%use (%instance (%thm subsetp-badguy-membership-property)
                             (x x)
                             (y y))))

(%autoprove subsetp-of-mergesort-right
            (%use (%instance (%thm subsetp-badguy-membership-property)
                             (x x)
                             (y (mergesort y)))))



(%autoadmit ordered-list-subsetp)

(%autoprove booleanp-of-ordered-list-subsetp
            (%autoinduct ordered-list-subsetp)
            (%restrict default ordered-list-subsetp (and (equal x 'x) (equal y 'y))))

(%autoprove lemma-1-for-ordered-list-subsetp-property)

(%autoprove lemma-2-for-ordered-list-subsetp-property)

(%autoprove lemma-3-for-ordered-list-subsetp-property
            (%cdr-induction x)
            (%enable default
                     lemma-2-for-ordered-list-subsetp-property
                     lemma-for-uniquep-when-ordered-listp))

(%autoprove lemma-4-for-ordered-list-subsetp-property
            (%autoinduct ordered-listp x)
            (%enable default
                     lemma-1-for-ordered-list-subsetp-property
                     lemma-2-for-ordered-list-subsetp-property
                     lemma-3-for-ordered-list-subsetp-property))

(%autoprove ordered-list-subsetp-property
            (%autoinduct ordered-list-subsetp x y)
            (%restrict default ordered-list-subsetp (and (equal x 'x) (equal y 'y)))
            (%enable default
                     lemma-1-for-ordered-list-subsetp-property
                     lemma-2-for-ordered-list-subsetp-property
                     lemma-3-for-ordered-list-subsetp-property
                     lemma-4-for-ordered-list-subsetp-property))


