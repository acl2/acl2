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
(%interactive)


(%defprojection :list (rev-lists x)
                :element (rev x)
                :nil-preservingp t)

(%autoprove rev-lists-of-rev-lists
            (%cdr-induction x))


(%autoadmit fast-app-lists$)
(%autoadmit app-lists)

(%autoadmit slow-app-lists)
(%autoprove slow-app-lists-when-not-consp
            (%restrict default slow-app-lists (equal x 'x)))
(%autoprove slow-app-lists-of-cons
            (%restrict default slow-app-lists (equal x '(cons a x))))
(%autoprove true-listp-of-slow-app-lists
            (%cdr-induction x))
(%autoprove slow-app-lists-of-list-fix
            (%cdr-induction x))
(%autoprove slow-app-lists-of-app
            (%cdr-induction x))
(%autoprove rev-of-slow-app-lists
            (%cdr-induction x))
(%autoprove slow-app-lists-of-list-list-fix
            (%cdr-induction x))




(ACL2::skip-proofs
 ;; BOZO unlocalize/rename
 ;; Damn theory invariants -- I'll just skip it.  It's locally proved there.
 (defthmd lemma1-for-definition-of-app-lists
   (implies (true-listp acc)
            (equal (fast-app-lists$ x acc)
                   (app (slow-app-lists (rev (rev-lists x)))
                        acc)))
   :hints(("Goal" :in-theory (enable fast-app-lists$)))))

(ACL2::skip-proofs
 (defthmd lemma2-for-definition-of-app-lists
   (equal (app-lists x)
          (slow-app-lists x))
   :hints(("Goal" :in-theory (enable app-lists)))))


;; BOZO def of app-lists is screwed up in tactics/partition.
;; Should say app-lists in recursive case, says slow-app-lists.
(defthmd definition-of-app-lists-alt
  (equal (app-lists x)
         (if (consp x)
             (app (car x)
                  (app-lists (cdr x)))
           nil))
   :rule-classes :definition)

(%autoprove lemma1-for-definition-of-app-lists
            (%autoinduct fast-app-lists$)
            (%restrict default fast-app-lists$ (equal x 'x)))

(%autoprove lemma2-for-definition-of-app-lists
            (%enable default lemma1-for-definition-of-app-lists)
            (%restrict default app-lists (equal x 'x)))

(%autoprove definition-of-app-lists-alt
            (%enable default lemma2-for-definition-of-app-lists))

(%autoprove app-lists-when-not-consp
            (%restrict default definition-of-app-lists-alt (equal x 'x)))

(%autoprove app-lists-of-cons
            (%restrict default definition-of-app-lists-alt (equal x '(cons a x))))

(%autoprove true-listp-of-app-lists
            (%cdr-induction x))

(%autoprove app-lists-of-list-fix
            (%cdr-induction x))

(%autoprove app-lists-of-app
            (%cdr-induction x))

(%autoprove rev-of-app-lists
            (%cdr-induction x))

(%autoprove app-lists-of-list-list-fix
            (%cdr-induction x))



(%autoadmit fast-sum-list)
(%autoadmit sum-list)
(%autoadmit slow-sum-list)


(ACL2::skip-proofs
 ;; BOZO unlocalize/rename
 (defthm lemma-for-definition-of-sum-list
   (implies (force (natp acc))
            (equal (fast-sum-list x acc)
                   (+ (slow-sum-list x) acc)))
   :hints(("Goal" :in-theory (enable fast-sum-list
                                     slow-sum-list)))))

(%autoprove lemma-for-definition-of-sum-list
            (%autoinduct fast-sum-list)
            (%restrict default fast-sum-list (equal x 'x))
            (%restrict default slow-sum-list (equal x 'x)))

(%autoprove definition-of-sum-list
            (%restrict default slow-sum-list (equal x 'x))
            (%enable default sum-list))

(%autoprove sum-list-when-not-consp
            (%restrict default definition-of-sum-list (equal x 'x)))

(%autoprove sum-list-of-cons
            (%restrict default definition-of-sum-list (equal x '(cons a x))))

(%autoprove natp-of-sum-list
            (%cdr-induction x))

(%autoprove sum-list-of-list-fix
            (%cdr-induction x))

(%autoprove sum-list-of-app
            (%cdr-induction x))

(%autoprove sum-list-of-rev
            (%cdr-induction x))


(%autoprove len-of-restn
            ;; BOZO move to utilities
            (%autoinduct restn)
            (%restrict default restn (equal n 'n)))

;; Hrmn, we already have len-of-firstn?? I wonder where that got defined...

(%autoadmit partition)

(%autoprove partition-when-not-consp
            (%restrict default partition (equal lens 'lens)))

(%autoprove partition-of-cons
            (%restrict default partition (equal lens '(cons len lens))))

(%autoprove partition-of-list-fix-one
            (%autoinduct partition))

(%autoprove partition-of-list-fix-two
            (%autoinduct partition))

(%autoprove true-listp-of-partition
            (%autoinduct partition))


;; BOZO we don't seem to need the arith lemma that is here in tactics/partition

(%autoprove forcing-app-lists-of-partition
            (%autoinduct partition))

(%autoprove partition-of-strip-lens-of-app-lists
            (%cdr-induction x))

(%autoprove partition-of-strip-lens-of-app-lists-free)

(%autoprove partition-of-simple-flatten
            (%cdr-induction x))

(%ensure-exactly-these-rules-are-missing "../../tactics/partition"
                                         ;; BOZO fix this; it's broken, see above, we used -alt.
                                         definition-of-app-lists)