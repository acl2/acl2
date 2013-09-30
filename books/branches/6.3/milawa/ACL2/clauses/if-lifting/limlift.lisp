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
(include-book "depth")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; BOZO find this stuff a home

(defthms-flag
  :thms ((term consp-of-clause.simple-tests
               (equal (consp (clause.simple-tests x))
                      (if (clause.simple-tests x)
                          t
                        nil)))
         (t consp-of-clause.simple-tests-list
            (equal (consp (clause.simple-tests-list x))
                   (if (clause.simple-tests-list x)
                       t
                     nil))))
  :hints (("Goal" :induct (clause.simple-term-induction flag x))))


(defthms-flag
  :thms ((term clause.simple-tests-when-not-clause.simple-termp-under-iff
               (implies (not (clause.simple-termp x))
                        (iff (clause.simple-tests x)
                             t)))
         (t clause.simple-tests-list-when-not-clause.simple-term-listp-under-iff
            (implies (not (clause.simple-term-listp x))
                     (iff (clause.simple-tests-list x)
                          t))))
  :hints (("Goal" :induct (clause.simple-term-induction flag x))))



(defthm forcing-logic.term-listp-of-firstn
  ;; BOZO move to terms
  (implies (force (logic.term-listp x))
           (equal (logic.term-listp (firstn n x))
                  t)))

(defthm forcing-logic.term-list-atblp-of-firstn
  ;; BOZO move to terms
  (implies (force (logic.term-list-atblp x atbl))
           (equal (logic.term-list-atblp (firstn n x) atbl)
                  t)))




;; (clause.limlift-term1 x k)
;;
;; This is a k-limited version of clause.lift1.  We perform if-lifting on the
;; term x, but only do up to k case-splits.  We return the number of
;; case-splits still available.

(defund clause.limlift-term1 (x k)
  (declare (xargs :guard (and (logic.termp x)
                              (natp k))
                  :verify-guards nil))
  (cond ((logic.constantp x)
         (cons x k))
        ((logic.variablep x)
         (cons x k))
        ((logic.functionp x)
         (let ((name (logic.function-name x))
               (args (logic.function-args x)))
           (cond ((and (equal name 'if)
                       (equal (len args) 3))
                  ;; The term is (if a b c).  This level of the term is already
                  ;; split, but a,b,c might not be split.  So, we just need to
                  ;; go down into the term and split it up.
                  (let* ((lift-first+  (clause.limlift-term1 (first args) k))
                         (lift-second+ (clause.limlift-term1 (second args) (cdr lift-first+)))
                         (lift-third+  (clause.limlift-term1 (third args) (cdr lift-second+))))
                    (cons (logic.function 'if (list (car lift-first+) (car lift-second+) (car lift-third+)))
                          (cdr lift-third+))))
                 ((clause.simple-term-listp args)
                  ;; Nothing to do...
                  (cons x k))
                 (t
                  ;; The term is (f a b c ...) and there are ifs inside the
                  ;; a,b,c.  Go into the args and collect the terms and lift as
                  ;; many as we can.
                  (let* ((tests    (clause.simple-tests x))
                         (numtests (fast-len tests 0)))
                    (if (<= numtests k)
                        (cons (clause.casesplit x tests nil) (- k numtests))
                      (cons (clause.casesplit x (firstn k tests) nil) 0)))))))
        ((logic.lambdap x)
         (let ((actuals (logic.lambda-actuals x)))
           (if (clause.simple-term-listp actuals)
               (cons x k)
             (let* ((tests    (clause.simple-tests x))
                    (numtests (fast-len tests 0)))
               (if (<= numtests k)
                   (cons (clause.casesplit x tests nil) (- k numtests))
                 (cons (clause.casesplit x (firstn k tests) nil) 0))))))
        (t
         (cons x k))))

(defthm forcing-logic.termp-of-car-of-clause.limlift-term1
  (implies (force (logic.termp x))
           (equal (logic.termp (car (clause.limlift-term1 x k)))
                  t))
  :hints(("Goal" :in-theory (enable clause.limlift-term1))))

(defthm forcing-natp-of-cdr-of-clause.limlift-term1
  (implies (force (natp k))
           (equal (natp (cdr (clause.limlift-term1 x k)))
                  t))
  :hints(("Goal" :in-theory (enable clause.limlift-term1))))

(verify-guards clause.limlift-term1)

(defthm forcing-logic.term-atblp-of-car-of-clause.lift1
  (implies (and (force (logic.termp x))
                (force (logic.term-atblp x atbl))
                (force (equal (cdr (lookup 'if atbl)) 3)))
           (equal (logic.term-atblp (car (clause.limlift-term1 x k)) atbl)
                  t))
  :hints(("Goal" :in-theory (enable clause.limlift-term1))))

(defthm car-of-clause.lift1-when-clause.lifted-termp
  (implies (and (clause.lifted-termp x)
                (force (logic.termp x)))
           (equal (car (clause.limlift-term1 x k))
                  x))
  :hints(("Goal" :in-theory (enable clause.limlift-term1))))

(defthm cdr-of-clause.lift1-when-clause.lifted-termp
  (implies (clause.lifted-termp x)
           (equal (cdr (clause.limlift-term1 x k))
                  k))
  :hints(("Goal" :in-theory (e/d (clause.limlift-term1)
                                 ((:executable-counterpart ACL2::force))))))

(defthm cdr-of-clause.limlift-term1-never-increases
  (equal (< k (cdr (clause.limlift-term1 x k)))
         nil)
  :hints(("Goal" :in-theory (enable clause.limlift-term1))))

(defthm cdr-of-clause.limlift-term1-stays-at-zero
  (equal (cdr (clause.limlift-term1 x 0))
         0)
  :hints(("Goal" :in-theory (e/d (clause.limlift-term1)
                                 ((:executable-counterpart acl2::force))))))

(defthm cdr-of-clause.limlift-term1-usually-decreases
  (implies (and (not (clause.lifted-termp x))
                (not (zp k)))
           (equal (< (cdr (clause.limlift-term1 x k)) k)
                  t))
  :hints(("Goal"
          :induct (clause.limlift-term1 x k)
          :in-theory (enable clause.limlift-term1 clause.lifted-termp)
          :do-not-induct t)))



;; (clause.limlift-term x k)
;;
;; This is full, multi-pass if-lifting.  We repeatedly call if-lift1 to bring
;; up tests to the top of a term, until the term is in lifted form.

(defund clause.limlift-term (x k)
  (declare (xargs :guard (and (logic.termp x)
                              (natp k))
                  :measure (nfix k)))
  (cond ((zp k)
         x)
        ((clause.lifted-termp x)
         x)
        (t
         (let* ((lift1      (clause.limlift-term1 x k))
                (lift1-term (car lift1))
                (lift1-k    (cdr lift1)))
           (clause.limlift-term lift1-term lift1-k)))))

(defthm forcing-logic.termp-of-clause.limlift-term
  (implies (force (logic.termp x))
           (equal (logic.termp (clause.limlift-term x k))
                  t))
  :hints(("Goal" :in-theory (enable clause.limlift-term))))

(defthm forcing-logic.term-atblp-of-clause.limlift-term
  (implies (and (force (logic.termp x))
                (force (logic.term-atblp x atbl))
                (force (equal (cdr (lookup 'if atbl)) 3)))
           (equal (logic.term-atblp (clause.limlift-term x k) atbl)
                  t))
  :hints(("Goal" :in-theory (enable clause.limlift-term))))

(defthm clause.limlift-term-when-clause.simple-termp
  (implies (clause.simple-termp x)
           (equal (clause.limlift-term x k)
                  x))
  :hints(("Goal" :in-theory (enable clause.limlift-term))))

(defthm clause.limlift-term-when-clause.lifted-termp
  (implies (clause.lifted-termp x)
           (equal (clause.limlift-term x k)
                  x))
  :hints(("Goal" :in-theory (enable clause.limlift-term))))



(defprojection :list (clause.limlift-term-list x k)
               :element (clause.limlift-term x k)
               :guard (and (logic.term-listp x)
                           (natp k))
               :nil-preservingp t)

(defthm forcing-logic.term-listp-of-clause.limlift-term-list
  (implies (force (logic.term-listp x))
           (equal (logic.term-listp (clause.limlift-term-list x k))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-atblp-of-clause.limlift-term-list
  (implies (and (force (logic.term-listp x))
                (force (logic.term-list-atblp x atbl))
                (force (equal (cdr (lookup 'if atbl)) 3)))
           (equal (logic.term-list-atblp (clause.limlift-term-list x k) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.limlift-term-list-when-clause.simple-term-listp
  (implies (clause.simple-term-listp x)
           (equal (clause.limlift-term-list x k)
                  (list-fix x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.limlift-term-list-when-clause.lifted-term-listp
  (implies (clause.lifted-term-listp x)
           (equal (clause.limlift-term-list x k)
                  (list-fix x)))
  :hints(("Goal" :induct (cdr-induction x))))




(defprojection :list (clause.limlift-term-list-list x k)
               :element (clause.limlift-term-list x k)
               :guard (and (logic.term-list-listp x)
                           (natp k))
               :nil-preservingp t)

(defthm forcing-logic.term-list-listp-of-clause.limlift-term-list-list
  (implies (force (logic.term-list-listp x))
           (equal (logic.term-list-listp (clause.limlift-term-list-list x k))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-list-atblp-of-clause.limlift-term-list-list
  (implies (and (force (logic.term-list-listp x))
                (force (logic.term-list-list-atblp x atbl))
                (force (equal (cdr (lookup 'if atbl)) 3)))
           (equal (logic.term-list-list-atblp (clause.limlift-term-list-list x k) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.limlift-term-list-list-when-clause.simple-term-list-listp
  (implies (clause.simple-term-list-listp x)
           (equal (clause.limlift-term-list-list x k)
                  (list-list-fix x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm cons-listp-of-clause.limlift-term-list-list
  (implies (force (cons-listp x))
           (equal (cons-listp (clause.limlift-term-list-list x k))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))
