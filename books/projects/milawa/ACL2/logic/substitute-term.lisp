;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
(include-book "terms")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; (logic.sigmap x)
;;
;; A sigma is a mapping from variables to term structures.  Normally these are
;; called "substitution lists", but we think sigmas is a better name since,
;; e.g., "sigma list" seems more clear than "substitution list list", etc.

(defmap :map (logic.sigmap x)
        :key (logic.variablep x)
        :val (logic.termp x)
        :key-list (logic.variable-listp x)
        :val-list (logic.term-listp x)
        :val-of-nil nil)

;; BOZO consider adding something like this to defmap
(defthm forcing-logic.sigmap-of-pair-lists
  (implies (and (force (logic.variable-listp x))
                (force (logic.term-listp y))
                (force (equal (len x) (len y))))
           (equal (logic.sigmap (pair-lists x y))
                  t))
  :hints(("Goal" :in-theory (enable pair-lists))))

(deflist logic.sigma-listp (x)
  (logic.sigmap x)
  :elementp-of-nil t)

;; BOZO consider adding something like this to deflist
(defthm logic.sigmap-of-second-when-logic.sigma-listp
  (implies (logic.sigma-listp x)
           (equal (logic.sigmap (second x))
                  t)))

(defthm forcing-logic.sigma-listp-of-revappend-onto-each
  (implies (force (and (logic.sigmap a)
                       (logic.sigma-listp x)
                       (true-list-listp x)))
           (equal (logic.sigma-listp (revappend-onto-each a x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))



(deflist logic.sigma-list-listp (x)
  (logic.sigma-listp x)
  :elementp-of-nil t)

;; BOZO consider adding something like this to deflist
(defthm logic.sigma-listp-of-second-when-logic.sigma-list-listp
  (implies (logic.sigma-list-listp x)
           (equal (logic.sigma-listp (second x))
                  t)))

(defthm forcing-logic.sigma-listp-of-simple-flatten
  (implies (force (logic.sigma-list-listp x))
           (equal (logic.sigma-listp (simple-flatten x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))




(defmap :map (logic.sigma-atblp x atbl)
        :key (logic.variablep x)
        :val (logic.term-atblp x atbl)
        :key-list (logic.variable-listp x)
        :val-list (logic.term-list-atblp x atbl)
        :guard (and (logic.sigmap x)
                    (logic.arity-tablep atbl))
        :val-of-nil nil)

;; BOZO consider adding something like this to defmap
(defthm forcing-logic.sigma-atblp-of-pair-lists
  (implies (and (force (logic.variable-listp x))
                (force (logic.term-list-atblp y atbl))
                (force (equal (len x) (len y))))
           (equal (logic.sigma-atblp (pair-lists x y) atbl)
                  t))
  :hints(("Goal" :in-theory (enable pair-lists))))



(deflist logic.sigma-list-atblp (x atbl)
  (logic.sigma-atblp x atbl)
  :elementp-of-nil t
  :guard (and (logic.sigma-listp x)
              (logic.arity-tablep atbl)))

;; BOZO consider adding something like this to deflist
(defthm logic.sigma-atblp-of-second-when-logic.sigma-list-atblp
  (implies (logic.sigma-list-atblp x atbl)
           (equal (logic.sigma-atblp (second x) atbl)
                  t)))

(defthm forcing-logic.sigma-list-atblp-of-revappend-onto-each
  (implies (force (and (logic.sigma-atblp a atbl)
                       (logic.sigma-list-atblp x atbl)
                       (true-list-listp x)))
           (equal (logic.sigma-list-atblp (revappend-onto-each a x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))



(deflist logic.sigma-list-list-atblp (x atbl)
  (logic.sigma-list-atblp x atbl)
  :elementp-of-nil t
  :guard (and (logic.sigma-list-listp x)
              (logic.arity-tablep atbl)))






(defund logic.flag-substitute (flag x sigma)
  ;; We walk through the term x, "simultaneously" replacing all occurrences of
  ;; all variables bound by the sigma with their replacements, and leaving the
  ;; rest of the term unchanged.
  (declare (xargs :guard (and (if (equal flag 'term)
                                  (logic.termp x)
                                (and (equal flag 'list)
                                     (logic.term-listp x)))
                              (logic.sigmap sigma))
                  :verify-guards nil))
  (if (equal flag 'term)
      (cond ((logic.variablep x)
             (if (lookup x sigma)
                 (cdr (lookup x sigma))
               x))
            ((logic.constantp x)
             x)
            ((logic.functionp x)
             (let ((fn   (logic.function-name x))
                   (args (logic.function-args x)))
               (logic.function fn (logic.flag-substitute 'list args sigma))))
            ((logic.lambdap x)
             (let ((formals (logic.lambda-formals x))
                   (body    (logic.lambda-body x))
                   (actuals (logic.lambda-actuals x)))
               (logic.lambda formals body (logic.flag-substitute 'list actuals sigma))))
            (t nil))
    (if (consp x)
        (cons (logic.flag-substitute 'term (car x) sigma)
              (logic.flag-substitute 'list (cdr x) sigma))
     nil)))

(definlined logic.substitute (x sigma)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.sigmap sigma))
                  :verify-guards nil))
  (logic.flag-substitute 'term x sigma))

(definlined logic.substitute-list (x sigma)
  (declare (xargs :guard (and (logic.term-listp x)
                              (logic.sigmap sigma))
                  :verify-guards nil))
  (logic.flag-substitute 'list x sigma))

(defthmd definition-of-logic.substitute
  (equal (logic.substitute x sigma)
         (cond ((logic.variablep x)
                (if (lookup x sigma)
                    (cdr (lookup x sigma))
                  x))
               ((logic.constantp x)
                x)
               ((logic.functionp x)
                (let ((fn   (logic.function-name x))
                      (args (logic.function-args x)))
                  (logic.function fn (logic.substitute-list args sigma))))
               ((logic.lambdap x)
                (let ((formals (logic.lambda-formals x))
                      (body    (logic.lambda-body x))
                      (actuals (logic.lambda-actuals x)))
                  (logic.lambda formals body (logic.substitute-list actuals sigma))))
               (t nil)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.substitute
                                    logic.substitute-list
                                    logic.flag-substitute))))

(defthmd definition-of-logic.substitute-list
  (equal (logic.substitute-list x sigma)
         (if (consp x)
             (cons (logic.substitute (car x) sigma)
                   (logic.substitute-list (cdr x) sigma))
           nil))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.substitute
                                    logic.substitute-list
                                    logic.flag-substitute))))

(defthm logic.flag-substitute-of-term
  (equal (logic.flag-substitute 'term x sigma)
         (logic.substitute x sigma))
  :hints(("Goal" :in-theory (enable logic.substitute))))

(defthm logic.flag-substitute-of-term-list
  (equal (logic.flag-substitute 'list x sigma)
         (logic.substitute-list x sigma))
  :hints(("Goal" :in-theory (enable logic.substitute-list))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.substitute))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.substitute-list))))



(defthm logic.substitute-when-malformed-cheap
  (implies (and (not (logic.constantp x))
                (not (logic.variablep x))
                (not (logic.functionp x))
                (not (logic.lambdap x)))
           (equal (logic.substitute x sigma)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-logic.substitute))))

(defthm logic.substitute-list-when-not-consp
  (implies (not (consp x))
           (equal (logic.substitute-list x sigma)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-logic.substitute-list))))

(defthm logic.substitute-list-of-cons
  (equal (logic.substitute-list (cons a x) sigma)
         (cons (logic.substitute a sigma)
               (logic.substitute-list x sigma)))
  :hints(("Goal" :in-theory (enable definition-of-logic.substitute-list))))

(defprojection :list (logic.substitute-list x sigma)
               :element (logic.substitute x sigma)
               :nil-preservingp t
               :already-definedp t)



(defthm logic.substitute-when-logic.constantp
  ;; BOZO why is this not cheap while the function and lambda cases are cheap?
  (implies (logic.constantp x)
           (equal (logic.substitute x sigma)
                  x))
  :hints(("Goal" :in-theory (enable definition-of-logic.substitute))))

(defthm logic.substitute-when-logic.variablep
  ;; BOZO why is this not cheap while the function and lambda cases are cheap?
  (implies (logic.variablep x)
           (equal (logic.substitute x sigma)
                  (if (lookup x sigma)
                      (cdr (lookup x sigma))
                    x)))
  :hints(("Goal" :in-theory (enable definition-of-logic.substitute))))

(defthm logic.substitute-when-logic.functionp-cheap
  (implies (logic.functionp x)
           (equal (logic.substitute x sigma)
                  (logic.function (logic.function-name x)
                                  (logic.substitute-list (logic.function-args x) sigma))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-logic.substitute))))

(defthm logic.substitute-when-logic.lambdap-cheap
  (implies (logic.lambdap x)
           (equal (logic.substitute x sigma)
                  (logic.lambda (logic.lambda-formals x)
                                (logic.lambda-body x)
                                (logic.substitute-list (logic.lambda-actuals x) sigma))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-logic.substitute))))

(defthm forcing-logic.substitute-of-logic.function
  (implies (force (logic.function-namep fn))
           (equal (logic.substitute (logic.function fn args) sigma)
                  (logic.function fn (logic.substitute-list args sigma)))))

(defthm forcing-logic.function-name-of-logic.substitute
  (implies (force (logic.functionp x))
           (equal (logic.function-name (logic.substitute x sigma))
                  (logic.function-name x)))
  :hints(("Goal" :in-theory (enable definition-of-logic.substitute))))

(defthm forcing-logic.function-args-of-logic.substitute
  (implies (force (logic.functionp x))
           (equal (logic.function-args (logic.substitute x sigma))
                  (logic.substitute-list (logic.function-args x) sigma)))
  :hints(("Goal" :in-theory (enable definition-of-logic.substitute))))

(defthm forcing-logic.substitute-of-logic.lambda
  (equal (logic.substitute (logic.lambda formals body actuals) sigma)
         (logic.lambda formals body (logic.substitute-list actuals sigma)))
  :hints(("Goal" :in-theory (enable definition-of-logic.substitute))))

(defthm forcing-logic.lambda-formals-of-logic.substitute
  (implies (force (logic.lambdap x))
           (equal (logic.lambda-formals (logic.substitute x sigma))
                  (logic.lambda-formals x)))
  :hints(("Goal" :in-theory (enable definition-of-logic.substitute))))

(defthm forcing-logic.lambda-body-of-logic.substitute
  (implies (force (logic.lambdap x))
           (equal (logic.lambda-body (logic.substitute x sigma))
                  (logic.lambda-body x)))
  :hints(("Goal" :in-theory (enable definition-of-logic.substitute))))

(defthm forcing-logic.lambda-actuals-of-logic.substitute
  (implies (force (logic.lambdap x))
           (equal (logic.lambda-actuals (logic.substitute x sigma))
                  (logic.substitute-list (logic.lambda-actuals x) sigma)))
  :hints(("Goal" :in-theory (enable definition-of-logic.substitute))))



(defthm forcing-logic.substitute-under-iff
  (implies (and (force (logic.termp term))
                (force (logic.sigmap sigma)))
           (iff (logic.substitute term sigma)
                t))
  :hints(("Goal"
          :in-theory (e/d (definition-of-logic.substitute)
                          (logic.termp-of-cdr-of-lookup-when-logic.sigmap))
          :use ((:instance logic.termp-of-cdr-of-lookup-when-logic.sigmap (x term))))))



(defthms-flag
  :thms ((term forcing-logic.termp-of-logic.substitute
               (implies (and (force (logic.termp x))
                             (force (logic.sigmap sigma)))
                        (equal (logic.termp (logic.substitute x sigma))
                               t)))
         (t forcing-logic.term-listp-of-logic.substitute-list
            (implies (and (force (logic.term-listp x))
                          (force (logic.sigmap sigma)))
                     (equal (logic.term-listp (logic.substitute-list x sigma))
                            t))))
  :hints(("Goal" :induct (logic.term-induction flag x))))

(defthms-flag
  :thms ((term forcing-logic.term-atblp-of-logic.substitute
               (implies (and (force (logic.term-atblp x atbl))
                             (force (logic.sigma-atblp sigma atbl)))
                        (equal (logic.term-atblp (logic.substitute x sigma) atbl)
                               t)))
         (t forcing-logic.term-list-atblp-of-logic.substitute-list
            (implies (and (force (logic.term-list-atblp x atbl))
                          (force (logic.sigma-atblp sigma atbl)))
                     (equal (logic.term-list-atblp (logic.substitute-list x sigma) atbl)
                            t))))
  :hints (("Goal" :induct (logic.term-induction flag x))))

(verify-guards logic.flag-substitute)
(verify-guards logic.substitute)
(verify-guards logic.substitute-list)

(defthms-flag
  :shared-hyp (not (consp sigma))
  :thms ((term forcing-logic.substitute-of-empty-sigma
               (implies (force (logic.termp x))
                        (equal (logic.substitute x sigma)
                               x)))
         (t forcing-logic.substitute-list-of-empty-sigma
            (implies (force (logic.term-listp x))
                     (equal (logic.substitute-list x sigma)
                            (list-fix x)))))
  :hints (("Goal"
           :induct (logic.term-induction flag x))))

(defthms-flag
  ;; If some sigma contains all of the variables mentioned in x, and some sigma'
  ;; is a supermap of sigma, then we obtain exactly the same result when we
  ;; instantiate x with sigma or sigma'.
  :shared-hyp (submapp sigma1 sigma2)
  :thms ((term equal-of-logic.substitutes-of-expansion
               (implies (subsetp (logic.term-vars x) (domain sigma1))
                        (equal (equal (logic.substitute x sigma1)
                                      (logic.substitute x sigma2))
                               t)))
         (t equal-of-logic.substitute-lists-of-expansion
            (implies (subsetp (logic.term-list-vars x) (domain sigma1))
                     (equal (equal (logic.substitute-list x sigma1)
                                   (logic.substitute-list x sigma2))
                            t))))
  :hints (("Goal" :induct (logic.term-induction flag x))))

(defthms-flag
  ;; Suppose x is a term and sigma is [v1 <- t1, ..., vn <- tn].  If the
  ;; free variables of x are a subset of these v's, then
  ;;     (x/sigma)/sigma2 = x/[v1<-t1/sigma2, ..., vn<-tn/sigma2]
  :thms ((term logic.substitute-of-logic.substitute-when-all-bound
               (implies (subsetp (logic.term-vars x) (domain sig1))
                        (equal (logic.substitute (logic.substitute x sig1) sig2)
                               (logic.substitute x (pair-lists (domain sig1) (logic.substitute-list (range sig1) sig2))))))
         (t logic.substitute-list-of-logic.substitute-list-when-all-bound
            (implies (subsetp (logic.term-list-vars x) (domain sig1))
                     (equal (logic.substitute-list (logic.substitute-list x sig1) sig2)
                            (logic.substitute-list x (pair-lists (domain sig1) (logic.substitute-list (range sig1) sig2)))))))
  :hints (("Goal"
           :in-theory (enable definition-of-logic.substitute)
           :induct (logic.term-induction flag x))))


(encapsulate
 ()
 ;; Suppose vars is a list of unique variables, i.e., [v1, ..., vn].
 ;; Then, (v1 ... vn)/[v1<-t1, ..., vn<-tn] = (t1 ... tn).
 (defthmd lemma-for-logic.substitute-list-of-vars-with-pair-lists
   (implies (and (equal (len vars) (len vals))
                 (logic.variable-listp vars)
                 (uniquep vars))
            (prefixp (logic.substitute-list vars (pair-lists vars vals))
                     vals))
   :hints(("Goal"
           :use ((:instance prefixp-badguy-index-property
                            (x (logic.substitute-list vars (pair-lists vars vals)))
                            (y vals))))))

 (defthm logic.substitute-list-of-vars-with-pair-lists
   (implies (and (equal (len vars) (len vals))
                 (logic.variable-listp vars)
                 (uniquep vars))
            (equal (logic.substitute-list vars (pair-lists vars vals))
                   (list-fix vals)))
   :hints(("Goal" :in-theory (enable lemma-for-logic.substitute-list-of-vars-with-pair-lists)))))




(defprojection :list (logic.substitute-list-list x sigma)
               :element (logic.substitute-list x sigma)
               :guard (and (logic.term-list-listp x)
                           (logic.sigmap sigma))
               :nil-preservingp t)

(defthm strip-lens-of-logic.substitute-list-list
  (equal (strip-lens (logic.substitute-list-list x sigma))
         (strip-lens x))
  :hints(("Goal" :induct (cdr-induction x))))



(defthm logic.substitute-list-of-repeat
  (equal (logic.substitute-list (repeat x n) sigma)
         (repeat (logic.substitute x sigma) n))
  :hints(("Goal" :in-theory (enable repeat))))

