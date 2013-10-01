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
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defun logic.flag-patmatch (flag pat term sigma)
  ;; We attempt to match a pattern term (list) against a target term (list)
  ;; under some sigma.  That is, we try to find a new sigma', which is a
  ;; supermap of sigma, which can be substituted into the pattern term in order
  ;; to obtain the target term.
  ;;
  ;; We return a pair of values, e.g., (successp . sigma'), where successp is a
  ;; boolean indicator of success, and if successp is t, then sigma' extends
  ;; sigma in an acceptable way as described above.
  (declare (xargs :guard (if (equal flag 'term)
                             (and (logic.termp pat)
                                  (logic.termp term)
                                  (logic.sigmap sigma))
                           (and (logic.term-listp pat)
                                (logic.term-listp term)
                                (logic.sigmap sigma)))
                  :verify-guards nil))
  (if (equal flag 'term)
      (cond ((logic.constantp pat)
             (if (equal term pat)
                 sigma
               'fail))
            ((logic.variablep pat)
             (let ((value (lookup pat sigma)))
               (if (consp value)
                   (if (equal term (cdr value))
                       sigma
                     'fail)
                 (cons (cons pat term) sigma))))
            ((logic.functionp pat)
             (if (and (logic.functionp term)
                      (equal (logic.function-name term) (logic.function-name pat)))
                 (logic.flag-patmatch 'list (logic.function-args pat) (logic.function-args term) sigma)
               'fail))
            ((logic.lambdap pat)
             'fail)
            (t 'fail))
    ;; List case
    (if (or (not (consp pat))
            (not (consp term)))
        (if (and (not (consp pat))
                 (not (consp term)))
            sigma
          'fail)
      (let* ((match-car (logic.flag-patmatch 'term (car pat) (car term) sigma)))
        (if (equal match-car 'fail)
            'fail
          (logic.flag-patmatch 'list (cdr pat) (cdr term) match-car))))))

(definlined logic.patmatch (pat term sigma)
  (declare (xargs :guard (and (logic.termp pat)
                              (logic.termp term)
                              (logic.sigmap sigma))
                  :verify-guards nil))
  (logic.flag-patmatch 'term pat term sigma))

(definlined logic.patmatch-list (pat term sigma)
  (declare (xargs :guard (and (logic.term-listp pat)
                              (logic.term-listp term)
                              (logic.sigmap sigma))
                  :verify-guards nil))
  (logic.flag-patmatch 'list pat term sigma))

(defthmd definition-of-logic.patmatch
  (equal (logic.patmatch pat term sigma)
         (cond ((logic.constantp pat)
                (if (equal term pat)
                    sigma
                  'fail))
               ((logic.variablep pat)
                (let ((value (lookup pat sigma)))
                  (if (consp value)
                      (if (equal term (cdr value))
                          sigma
                        'fail)
                    (cons (cons pat term) sigma))))
               ((logic.functionp pat)
                (if (and (logic.functionp term)
                         (equal (logic.function-name term) (logic.function-name pat)))
                    (logic.patmatch-list (logic.function-args pat) (logic.function-args term) sigma)
                  'fail))
               ((logic.lambdap pat)
                'fail)
               (t 'fail)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.flag-patmatch
                                    logic.patmatch
                                    logic.patmatch-list))))

(defthmd definition-of-logic.patmatch-list
  (equal (logic.patmatch-list pat term sigma)
         (if (or (not (consp pat))
                 (not (consp term)))
             (if (and (not (consp pat))
                      (not (consp term)))
                 sigma
               'fail)
           (let* ((match-car (logic.patmatch (car pat) (car term) sigma)))
             (if (equal match-car 'fail)
                 'fail
               (logic.patmatch-list (cdr pat) (cdr term) match-car)))))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.flag-patmatch
                                    logic.patmatch
                                    logic.patmatch-list))))

(defthm logic.flag-patmatch-term-removal
  (equal (logic.flag-patmatch 'term pat term sigma)
         (logic.patmatch pat term sigma))
  :hints(("Goal" :in-theory (enable logic.patmatch))))

(defthm logic.flag-patmatch-list-removal
  (equal (logic.flag-patmatch 'list pat term sigma)
         (logic.patmatch-list pat term sigma))
  :hints(("Goal" :in-theory (enable logic.patmatch-list))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.patmatch))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.patmatch-list))))




(defthms-flag
  :shared-hyp (force (logic.sigmap sigma))
  :thms ((term forcing-logic.sigmap-of-logic.patmatch
               (implies (and (force (logic.termp x))
                             (force (logic.termp y)))
                        (equal (logic.sigmap (logic.patmatch x y sigma))
                               t)))
         (t forcing-logic.sigmap-of-logic.patmatch-list
            (implies (and (force (logic.term-listp x))
                          (force (logic.term-listp y)))
                     (equal (logic.sigmap (logic.patmatch-list x y sigma))
                            t))))
  :hints (("Goal"
           :induct (logic.flag-patmatch flag x y sigma)
           :in-theory (enable definition-of-logic.patmatch
                              definition-of-logic.patmatch-list))))


(defthms-flag
  :shared-hyp (force (logic.sigma-atblp sigma atbl))
  :thms ((term forcing-logic.sigma-atblp-of-logic.patmatch
               (implies (and (force (logic.term-atblp x atbl))
                             (force (logic.term-atblp y atbl)))
                        (equal (logic.sigma-atblp (logic.patmatch x y sigma) atbl)
                               t)))
         (t forcing-logic.sigma-atblp-of-logic.patmatch-list
            (implies (and (force (logic.term-list-atblp x atbl))
                          (force (logic.term-list-atblp y atbl)))
                     (equal (logic.sigma-atblp (logic.patmatch-list x y sigma) atbl)
                            t))))
  :hints (("Goal"
           :induct (logic.flag-patmatch flag x y sigma)
           :in-theory (enable definition-of-logic.patmatch
                              definition-of-logic.patmatch-list))))

(verify-guards logic.flag-patmatch)
(verify-guards logic.patmatch)
(verify-guards logic.patmatch-list)


(defthms-flag
  ;; BOZO these are called forcing, but they don't have any forced hyps
  ;; I think they used to have hyps that I got rid of.
  :thms ((term forcing-submapp-of-logic.patmatch
               (implies (not (equal 'fail (logic.patmatch x y sigma)))
                        (equal (submapp sigma (logic.patmatch x y sigma))
                               t)))
         (t forcing-submapp-of-logic.patmatch-list
            (implies (not (equal 'fail (logic.patmatch-list x y sigma)))
                     (equal (submapp sigma (logic.patmatch-list x y sigma))
                            t))))
  :hints (("Goal"
           :in-theory (enable definition-of-logic.patmatch
                              definition-of-logic.patmatch-list)
           :induct (logic.flag-patmatch flag x y sigma))))

(defthm two-deep-submapp-of-logic.patmatch
  (implies (and (not (equal 'fail (logic.patmatch a b sigma)))
                (not (equal 'fail (logic.patmatch c d (logic.patmatch a b sigma)))))
           (equal (submapp sigma (logic.patmatch c d (logic.patmatch a b sigma)))
                  t))
  :hints(("Goal"
          :in-theory (disable forcing-submapp-of-logic.patmatch)
          :use ((:instance forcing-submapp-of-logic.patmatch
                           (x a) (y b) (sigma sigma))
                (:instance forcing-submapp-of-logic.patmatch
                           (x c) (y d) (sigma (logic.patmatch a b sigma)))))))

(defthmd lemma-2-for-memberp-of-domain-of-logic.patmatch
  (implies (not (equal 'fail (logic.patmatch-list x y (cons (cons key val) sigma))))
           (equal (lookup key (logic.patmatch-list x y (cons (cons key val) sigma)))
                  (cons key val)))
  :hints(("Goal"
          :in-theory (disable equal-of-lookups-when-submapp)
          :use ((:instance equal-of-lookups-when-submapp
                           (a key)
                           (x (cons (cons key val) sigma))
                           (y (logic.patmatch-list x y (cons (cons key val) sigma))))))))

(defthms-flag
  ;; BOZO add -when... to these names?
  :thms ((term memberp-of-domain-of-logic.patmatch
               (implies (and (not (equal 'fail (logic.patmatch x y sigma)))
                             (memberp a (logic.term-vars x)))
                        (equal (memberp a (domain (logic.patmatch x y sigma)))
                               t)))
         (t memberp-of-domain-of-logic.patmatch-list
            (implies (and (not (equal 'fail (logic.patmatch-list x y sigma)))
                          (memberp a (logic.term-list-vars x)))
                     (equal (memberp a (domain (logic.patmatch-list x y sigma)))
                            t))))
  :hints (("Goal"
           :in-theory (enable definition-of-logic.patmatch
                              definition-of-logic.patmatch-list
                              lemma-2-for-memberp-of-domain-of-logic.patmatch)
           :induct (logic.flag-patmatch flag x y sigma))))

(defthm two-deep-memberp-of-logic.patmatch
  (implies (and (memberp e (logic.term-vars a))
                (not (equal 'fail (logic.patmatch a b sigma)))
                (not (equal 'fail (logic.patmatch c d (logic.patmatch a b sigma)))))
           (equal (memberp e (domain (logic.patmatch c d (logic.patmatch a b sigma))))
                  t))
  :hints(("Goal"
          :in-theory (disable memberp-of-domain-of-logic.patmatch)
          :use ((:instance memberp-of-domain-of-logic.patmatch
                           (a e) (x a) (y b) (sigma sigma))
                (:instance memberp-of-domain-of-logic.patmatch
                           (a e) (x c) (y d) (sigma (logic.patmatch a b sigma)))))))

(defthm subsetp-of-logic.term-vars-and-domain-of-logic.patmatch
  (implies (not (equal 'fail (logic.patmatch x y sigma)))
           (equal (subsetp (logic.term-vars x) (domain (logic.patmatch x y sigma)))
                  t))
  :hints(("Goal"
          ;; yuck, but we don't want to think of this as a mapp right now.
          :in-theory (disable memberp-of-domain-under-iff)
          :use ((:instance subsetp-badguy-membership-property
                           (x (logic.term-vars x))
                           (y (domain (logic.patmatch x y sigma))))))))

(defthm subsetp-of-logic.term-list-vars-and-domain-of-logic.patmatch-list
  (implies (not (equal (logic.patmatch-list x y sigma) 'fail))
           (equal (subsetp (logic.term-list-vars x)
                           (domain (logic.patmatch-list x y sigma)))
                  t))
  :hints(("Goal"
          ;; yuck, but we don't want to think of this as a mapp right now.
          :in-theory (disable memberp-of-domain-under-iff)
          :use ((:instance subsetp-badguy-membership-property
                           (x (logic.term-list-vars x))
                           (y (domain (logic.patmatch-list x y sigma))))))))

(defthm two-deep-subsetp-of-logic.patmatch
  (implies (and (not (equal 'fail (logic.patmatch a b sigma)))
                (not (equal 'fail (logic.patmatch c d (logic.patmatch a b sigma)))))
           (equal (subsetp (logic.term-vars a)
                           (domain (logic.patmatch c d (logic.patmatch a b sigma))))
                  t))
  :hints(("Goal"
          :in-theory (disable subsetp-of-logic.term-vars-and-domain-of-logic.patmatch)
          :use ((:instance subsetp-of-logic.term-vars-and-domain-of-logic.patmatch
                           (x a) (y b) (sigma sigma))
                (:instance subsetp-of-logic.term-vars-and-domain-of-logic.patmatch
                           (x c) (y d) (sigma (logic.patmatch a b sigma)))))))



(encapsulate
 ()
 (defthmd lemma-1-for-forcing-logic.substitute-of-logic.patmatch
   ;; This isn't needed by Milawa for some reason
   (implies (and (not (equal 'fail (logic.patmatch-list x y sigma)))
                 (lookup key sigma))
            (equal (lookup key (logic.patmatch-list x y sigma))
                   (lookup key sigma)))
   :hints(("Goal"
           :in-theory (disable equal-of-lookups-when-submapp)
           :use ((:instance equal-of-lookups-when-submapp
                            (a key)
                            (x sigma)
                            (y (logic.patmatch-list x y sigma)))))))

 (defthmd lemma-2-for-forcing-logic.substitute-of-logic.patmatch
   (implies (and (consp x)
                 (consp y)
                 (not (equal 'fail (logic.patmatch (car x) (car y) sigma)))
                 (not (equal 'fail (logic.patmatch-list (cdr x) (cdr y) (logic.patmatch (car x) (car y) sigma))))
                 (equal (logic.substitute (car x) (logic.patmatch (car x) (car y) sigma)) (car y))
                 (equal (logic.substitute-list (cdr x) (logic.patmatch-list (cdr x) (cdr y) (logic.patmatch (car x) (car y) sigma)))
                        (list-fix (cdr y))))
            (equal (logic.substitute-list x (logic.patmatch-list (cdr x) (cdr y) (logic.patmatch (car x) (car y) sigma)))
                   (list-fix y)))
   :hints(("Goal"
           :in-theory (e/d (lemma-1-for-forcing-logic.substitute-of-logic.patmatch
                            definition-of-logic.patmatch
                            definition-of-logic.patmatch-list)
                           (equal-of-logic.substitutes-of-expansion))
           :use ((:instance equal-of-logic.substitutes-of-expansion
                            (x (car x))
                            (sigma1 (logic.patmatch (car x) (car y) sigma))
                            (sigma2 (logic.patmatch-list (cdr x) (cdr y) (logic.patmatch (car x) (car y) sigma))))))))

 (defthms-flag
   :thms ((term forcing-logic.substitute-of-logic.patmatch
                (implies (and (not (equal 'fail (logic.patmatch x y sigma)))
                              (force (logic.termp y)))
                         (equal (logic.substitute x (logic.patmatch x y sigma))
                                y)))
          (t forcing-logic.substitute-list-of-logic.patmatch-list
             (implies (and (not (equal 'fail (logic.patmatch-list x y sigma)))
                           (force (logic.term-listp y)))
                      (equal (logic.substitute-list x (logic.patmatch-list x y sigma))
                             (list-fix y)))))
   :hints (("Goal"
            :induct (logic.flag-patmatch flag x y sigma)
            :in-theory (enable definition-of-logic.patmatch
                               definition-of-logic.patmatch-list))
           ("Subgoal *1/13"
            :use ((:instance lemma-2-for-forcing-logic.substitute-of-logic.patmatch))))))




;; Theorem: In fact, if any extension of the sigma returned by logic.patmatch(-list)
;; is substituted into the pattern term, we still obtain the target term.

(defthm forcing-logic.substitute-of-logic.patmatch-expansion
  (implies (and (not (equal 'fail (logic.patmatch x y sigma)))
                (submapp (logic.patmatch x y sigma) sigma2)
                (force (logic.termp y)))
            (equal (logic.substitute x sigma2)
                   y))
  :hints(("Goal"
          :in-theory (disable equal-of-logic.substitutes-of-expansion)
          :use ((:instance equal-of-logic.substitutes-of-expansion
                           (x x)
                           (sigma1 (logic.patmatch x y sigma))
                           (sigma2 sigma2))))))

(defthm forcing-logic.substitute-of-logic.patmatch-list-expansion
  (implies (and (not (equal 'fail (logic.patmatch-list x y sigma)))
                (submapp (logic.patmatch-list x y sigma) sigma2)
                (force (logic.term-listp y)))
            (equal (logic.substitute-list x sigma2)
                   (list-fix y)))
  :hints(("Goal"
          :in-theory (disable equal-of-logic.substitute-lists-of-expansion)
          :use ((:instance equal-of-logic.substitute-lists-of-expansion
                           (x x)
                           (sigma1 (logic.patmatch-list x y sigma))
                           (sigma2 sigma2))))))

(defthms-flag
  :shared-hyp (force (uniquep (domain sigma)))
  :thms ((term forcing-uniquep-of-domain-of-cdr-of-logic.patmatch
               (equal (uniquep (domain (logic.patmatch x y sigma)))
                      t))
         (t forcing-uniquep-of-domain-of-cdr-of-logic.patmatch-list
            (equal (uniquep (domain (logic.patmatch-list x y sigma)))
                   t)))
  :hints (("Goal"
           :in-theory (enable definition-of-logic.patmatch
                              definition-of-logic.patmatch-list)
           :induct (logic.flag-patmatch flag x y sigma))))


