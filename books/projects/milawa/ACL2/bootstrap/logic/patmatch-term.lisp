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
(include-book "substitute-term")
(%interactive)

(%autoadmit logic.flag-patmatch)
(%autoadmit logic.patmatch)
(%autoadmit logic.patmatch-list)

(%autoprove definition-of-logic.patmatch
            (%enable default logic.patmatch logic.patmatch-list)
            (%restrict default logic.flag-patmatch (equal pat 'pat)))

(%autoprove definition-of-logic.patmatch-list
            (%enable default logic.patmatch logic.patmatch-list)
            (%restrict default logic.flag-patmatch (equal pat 'pat)))

(%autoprove logic.flag-patmatch-term-removal (%enable default logic.patmatch))
(%autoprove logic.flag-patmatch-list-removal (%enable default logic.patmatch-list))

(defmacro %logic.flag-patmatch-induction (flag pat term sigma)
  `(%induct (rank ,pat)
            ((and (equal ,flag 'term)
                  (logic.constantp ,pat))
             nil)
            ((and (equal ,flag 'term)
                  (logic.variablep ,pat))
             nil)
            ((and (equal ,flag 'term)
                  (logic.functionp ,pat))
             (((,flag 'list)
               (,pat (logic.function-args ,pat))
               (,term (logic.function-args ,term))
               (,sigma ,sigma))))
            ((and (equal ,flag 'term)
                  (logic.lambdap ,pat))
             nil)
            ((and (equal ,flag 'term)
                  (not (logic.constantp ,pat))
                  (not (logic.variablep ,pat))
                  (not (logic.functionp ,pat))
                  (not (logic.lambdap ,pat)))
             nil)
            ((and (not (equal flag 'term))
                  (or (not (consp ,pat))
                      (not (consp ,term))))
             nil)
            ((and (not (equal flag 'term))
                  (consp ,pat)
                  (consp ,term))
             (((,flag 'term)
               (,pat (car ,pat))
               (,term (car ,term))
               (,sigma ,sigma))
              ((,flag 'list)
               (,pat (cdr ,pat))
               (,term (cdr ,term))
               (,sigma (logic.flag-patmatch 'term (car ,pat) (car ,term) ,sigma)))))))


;; (%autoprove lemma-for-consp-of-logic.patmatch
;;             (%logic.flag-patmatch-induction flag x y sigma)
;;             (%auto)
;;             (%restrict default definition-of-logic.patmatch (equal pat 'x))
;;             (%restrict default definition-of-logic.patmatch-list (equal pat 'x)))

;; (%autoprove consp-of-logic.patmatch
;;             (%use (%instance (%thm lemma-for-consp-of-logic.patmatch)
;;                              (flag 'term))))

;; (%autoprove consp-of-logic.patmatch-list
;;             (%use (%instance (%thm lemma-for-consp-of-logic.patmatch)
;;                              (flag 'list))))



;; (%autoprove lemma-for-booleanp-of-car-of-logic.patmatch
;;             (%logic.flag-patmatch-induction flag x y sigma)
;;             (%auto)
;;             (%restrict default definition-of-logic.patmatch (equal pat 'x))
;;             (%restrict default definition-of-logic.patmatch-list (equal pat 'x)))

;; (%autoprove booleanp-of-car-of-logic.patmatch
;;             (%use (%instance (%thm lemma-for-booleanp-of-car-of-logic.patmatch)
;;                              (flag 'term))))

;; (%autoprove booleanp-of-car-of-logic.patmatch-list
;;             (%use (%instance (%thm lemma-for-booleanp-of-car-of-logic.patmatch)
;;                              (flag 'list))))


(%autoprove lemma-for-forcing-logic.sigmap-of-logic.patmatch
            (%logic.flag-patmatch-induction flag x y sigma)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%restrict default definition-of-logic.patmatch (equal pat 'x))
            (%restrict default definition-of-logic.patmatch-list (equal pat 'x)))

(%autoprove forcing-logic.sigmap-of-logic.patmatch
            (%use (%instance (%thm lemma-for-forcing-logic.sigmap-of-logic.patmatch)
                             (flag 'term))))

(%autoprove forcing-logic.sigmap-of-logic.patmatch-list
            (%use (%instance (%thm lemma-for-forcing-logic.sigmap-of-logic.patmatch)
                             (flag 'list))))



(%autoprove lemma-for-forcing-logic.sigma-atblp-of-logic.patmatch
            (%logic.flag-patmatch-induction flag x y sigma)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%restrict default definition-of-logic.patmatch (equal pat 'x))
            (%restrict default definition-of-logic.patmatch-list (equal pat 'x)))

(%autoprove forcing-logic.sigma-atblp-of-logic.patmatch
            (%use (%instance (%thm lemma-for-forcing-logic.sigma-atblp-of-logic.patmatch)
                             (flag 'term))))

(%autoprove forcing-logic.sigma-atblp-of-logic.patmatch-list
            (%use (%instance (%thm lemma-for-forcing-logic.sigma-atblp-of-logic.patmatch)
                             (flag 'list))))



(%autoprove lemma-for-forcing-submapp-of-logic.patmatch
            (%logic.flag-patmatch-induction flag x y sigma)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%restrict default definition-of-logic.patmatch (equal pat 'x))
            (%restrict default definition-of-logic.patmatch-list (equal pat 'x)))

(%autoprove forcing-submapp-of-logic.patmatch
            (%use (%instance (%thm lemma-for-forcing-submapp-of-logic.patmatch)
                             (flag 'term))))

(%autoprove forcing-submapp-of-logic.patmatch-list
            (%use (%instance (%thm lemma-for-forcing-submapp-of-logic.patmatch)
                             (flag 'list))))





(%autoprove two-deep-submapp-of-logic.patmatch
            (%disable default forcing-submapp-of-logic.patmatch)
            (%use (%instance (%thm forcing-submapp-of-logic.patmatch)
                             (x a) (y b) (sigma sigma)))
            (%use (%instance (%thm forcing-submapp-of-logic.patmatch)
                             (x c) (y d) (sigma (logic.patmatch a b sigma)))))



(%autoprove lemma-2-for-memberp-of-domain-of-logic.patmatch
            (%disable default equal-of-lookups-when-submapp)
            (%use (%instance (%thm equal-of-lookups-when-submapp)
                             (a key)
                             (x (cons (cons key val) sigma))
                             (y (logic.patmatch-list x y (cons (cons key val) sigma))))))

(%autoprove lemma-for-memberp-of-domain-of-logic.patmatch
            (%logic.flag-patmatch-induction flag x y sigma)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%enable default lemma-2-for-memberp-of-domain-of-logic.patmatch)
            (%restrict default definition-of-logic.patmatch (equal pat 'x))
            (%restrict default definition-of-logic.patmatch-list (equal pat 'x)))

(%autoprove memberp-of-domain-of-logic.patmatch
            (%use (%instance (%thm lemma-for-memberp-of-domain-of-logic.patmatch)
                             (flag 'term))))

(%autoprove memberp-of-domain-of-logic.patmatch-list
            (%use (%instance (%thm lemma-for-memberp-of-domain-of-logic.patmatch)
                             (flag 'list))))



(%autoprove two-deep-memberp-of-logic.patmatch
            (%disable default memberp-of-domain-of-logic.patmatch)
            (%use (%instance (%thm memberp-of-domain-of-logic.patmatch)
                             (a e) (x a) (y b) (sigma sigma)))
            (%use (%instance (%thm memberp-of-domain-of-logic.patmatch)
                             (a e) (x c) (y d) (sigma (logic.patmatch a b sigma)))))

(%autoprove subsetp-of-logic.term-vars-and-domain-of-logic.patmatch
            (%disable default memberp-of-domain-under-iff [outside]memberp-of-domain-under-iff)
            (%use (%instance (%thm subsetp-badguy-membership-property)
                             (x (logic.term-vars x))
                             (y (domain (logic.patmatch x y sigma))))))

(%autoprove subsetp-of-logic.term-list-vars-and-domain-of-logic.patmatch-list
            (%disable default memberp-of-domain-under-iff [outside]memberp-of-domain-under-iff)
            (%use (%instance (%thm subsetp-badguy-membership-property)
                             (x (logic.term-list-vars x))
                             (y (domain (logic.patmatch-list x y sigma))))))

(%autoprove two-deep-subsetp-of-logic.patmatch
            (%disable default subsetp-of-logic.term-vars-and-domain-of-logic.patmatch)
            (%use (%instance (%thm subsetp-of-logic.term-vars-and-domain-of-logic.patmatch)
                             (x a) (y b) (sigma sigma)))
            (%use (%instance (%thm subsetp-of-logic.term-vars-and-domain-of-logic.patmatch)
                             (x c) (y d) (sigma (logic.patmatch a b sigma)))))





(%autoprove lemma-2-for-forcing-logic.substitute-of-logic.patmatch
            (%disable default equal-of-logic.substitutes-of-expansion)
            (%use (%instance (%thm equal-of-logic.substitutes-of-expansion)
                             (x (car x))
                             (sigma1 (logic.patmatch (car x) (car y) sigma))
                             (sigma2 (logic.patmatch-list (cdr x) (cdr y) (logic.patmatch (car x) (car y) sigma))))))

(%autoprove lemma-for-forcing-logic.substitute-of-logic.patmatch
            (%logic.flag-patmatch-induction flag x y sigma)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%enable default lemma-2-for-forcing-logic.substitute-of-logic.patmatch)
            (%restrict default definition-of-logic.patmatch-list (equal pat 'x))
            (%restrict default definition-of-logic.patmatch (equal pat 'x)))

(%autoprove forcing-logic.substitute-of-logic.patmatch
            (%use (%instance (%thm lemma-for-forcing-logic.substitute-of-logic.patmatch)
                             (flag 'term))))

(%autoprove forcing-logic.substitute-list-of-logic.patmatch-list
            (%use (%instance (%thm lemma-for-forcing-logic.substitute-of-logic.patmatch)
                             (flag 'list))))



(%autoprove forcing-logic.substitute-of-logic.patmatch-expansion
            (%disable default equal-of-logic.substitutes-of-expansion)
            (%use (%instance (%thm equal-of-logic.substitutes-of-expansion)
                             (x x)
                             (sigma1 (logic.patmatch x y sigma))
                             (sigma2 sigma2))))

(%autoprove forcing-logic.substitute-of-logic.patmatch-list-expansion
            (%disable default equal-of-logic.substitute-lists-of-expansion)
            (%use (%instance (%thm equal-of-logic.substitute-lists-of-expansion)
                             (x x)
                             (sigma1 (logic.patmatch-list x y sigma))
                             (sigma2 sigma2))))


;; BOZO take "cdr" out of the name now that patmatch has been optimized a bit

(%autoprove lemma-for-forcing-uniquep-of-domain-of-cdr-of-logic.patmatch
            (%logic.flag-patmatch-induction flag x y sigma)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%restrict default definition-of-logic.patmatch (equal pat 'x))
            (%restrict default definition-of-logic.patmatch-list (equal pat 'x)))

(%autoprove forcing-uniquep-of-domain-of-cdr-of-logic.patmatch
            (%use (%instance (%thm lemma-for-forcing-uniquep-of-domain-of-cdr-of-logic.patmatch)
                             (flag 'term))))

(%autoprove forcing-uniquep-of-domain-of-cdr-of-logic.patmatch-list
            (%use (%instance (%thm lemma-for-forcing-uniquep-of-domain-of-cdr-of-logic.patmatch)
                             (flag 'list))))


(%ensure-exactly-these-rules-are-missing "../../logic/patmatch-term"
                                         lemma-1-for-forcing-logic.substitute-of-logic.patmatch)

