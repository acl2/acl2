; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "trace-okp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defthm revappend-under-iff
  (iff (revappend x acc)
       (or (consp x)
           acc))
  :hints(("Goal" :in-theory (e/d (revappend)
                                 (forcing-revappend-removal)))))

(defthm consp-of-revappend
  (equal (consp (revappend x acc))
         (or (consp x)
             (consp acc)))
  :hints(("Goal" :in-theory (e/d (revappend)
                                 (forcing-revappend-removal)))))

(defthm memberp-of-revappend
  (equal (memberp a (revappend x acc))
         (or (memberp a x)
             (memberp a acc)))
  :hints(("Goal" :in-theory (e/d (revappend)
                                 (forcing-revappend-removal)))))

(defthm subsetp-of-revappend-one
  (equal (subsetp x (revappend x acc))
         t)
  :hints(("Goal" :in-theory (e/d (revappend)
                                 (forcing-revappend-removal)))))

(defthm subsetp-of-revappend-two
  (equal (subsetp acc (revappend x acc))
         t)
  :hints(("Goal" :in-theory (e/d (revappend)
                                 (forcing-revappend-removal)))))

(defthm true-listp-of-revappend
  (equal (true-listp (revappend x acc))
         (true-listp acc))
  :hints(("Goal" :in-theory (e/d (revappend)
                                 (forcing-revappend-removal)))))

(defthm logic.formula-listp-of-revappend
  (implies (force (and (logic.formula-listp x)
                       (logic.formula-listp acc)))
           (equal (logic.formula-listp (revappend x acc))
                  t))
  :hints(("Goal" :in-theory (e/d (revappend)
                                 (forcing-revappend-removal)))))

(defthm logic.formula-list-atblp-of-revappend
  (implies (force (and (logic.formula-list-atblp x atbl)
                       (logic.formula-list-atblp acc atbl)))
           (equal (logic.formula-list-atblp (revappend x acc) atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (revappend)
                                 (forcing-revappend-removal)))))



(definlined fast-merge (x y)
  ;; This is never worse and is sometimes faster than revappend.  But unlike
  ;; revappend is does not produce a very predictable result.  You may be able
  ;; to use it when the only thing you care about is that the joined list has
  ;; all the members of x and y.
  (declare (xargs :guard (and (true-listp x)
                              (true-listp y))))
  (if (consp x)
      (if (consp y)
          ;; This is just an inlined call of revappend.
          (revappend (cdr x) (cons (car x) y))
        x)
    y))

(defthm consp-of-fast-merge
  (equal (consp (fast-merge x y))
         (or (consp x)
             (consp y)))
  :hints(("Goal" :in-theory (e/d (fast-merge)
                                 (forcing-revappend-removal)))))

(defthm true-listp-of-fast-merge
  (implies (force (and (true-listp x)
                       (true-listp y)))
           (equal (true-listp (fast-merge x y))
                  t))
  :hints(("Goal" :in-theory (enable fast-merge))))

(defthm memberp-of-fast-merge
  (equal (memberp a (fast-merge x y))
         (or (memberp a x)
             (memberp a y)))
  :hints(("Goal" :in-theory (e/d (fast-merge)
                                 (forcing-revappend-removal)))))

(defthm subsetp-of-fast-merge-one
  (equal (subsetp x (fast-merge x y))
         t)
  :hints(("Goal" :in-theory (e/d (fast-merge)
                                 (forcing-revappend-removal)))))

(defthm subsetp-of-fast-merge-two
  (equal (subsetp y (fast-merge x y))
         t)
  :hints(("Goal"
          :in-theory (e/d (fast-merge)
                          (forcing-revappend-removal
                           subsetp-of-revappend-two))
          :use ((:instance subsetp-of-revappend-two
                           (x x)
                           (acc y)))
          :expand (revappend x y))))

(defthm logic.formula-listp-of-fast-merge
  (implies (force (and (logic.formula-listp x)
                       (logic.formula-listp y)))
           (equal (logic.formula-listp (fast-merge x y))
                  t))
  :hints(("Goal" :in-theory (e/d (fast-merge)
                                 (forcing-revappend-removal)))))

(defthm logic.formula-list-atblp-of-fast-merge
  (implies (force (and (logic.formula-list-atblp x atbl)
                       (logic.formula-list-atblp y atbl)))
           (equal (logic.formula-list-atblp (fast-merge x y) atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (fast-merge)
                                 (forcing-revappend-removal)))))

(defthm fast-merge-when-not-consp-left
  (implies (not (consp x))
           (equal (fast-merge x y)
                  y))
  :hints(("Goal" :in-theory (enable fast-merge))))

(defthm fast-merge-with-nil-left
  (equal (fast-merge nil x)
         x)
  :hints(("Goal" :in-theory (enable fast-merge))))

(defthm fast-merge-when-not-consp-right
  (implies (not (consp y))
           (equal (fast-merge x y)
                  (if (consp x)
                      x
                    y)))
  :hints(("Goal" :in-theory (enable fast-merge))))

(defthm fast-merge-with-nil-right
  (equal (fast-merge x nil)
         (if (consp x)
             x
           nil))
  :hints(("Goal" :in-theory (enable fast-merge))))


;; Collecting forced goals from traces.
;;
;; I originally implemented the forced-goals collection with the following very
;; fast, tail-recursive, accumulator-style routine:
;;
;;   (defund rw.flag-collect-forced-goals (flag x acc)
;;     (declare (xargs :guard (if (equal flag 'term)
;;                                (rw.tracep x)
;;                              (rw.trace-listp x))
;;                     :measure (two-nats-measure (rank x) (if (equal flag 'term) 1 0))))
;;     (if (equal flag 'term)
;;         (cond ((equal (rw.trace->method x) 'force)
;;                (cons (rw.trace-formula x) acc))
;;               (t
;;                (rw.flag-collect-forced-goals 'list (rw.trace->subtraces x) acc)))
;;       (if (consp x)
;;           (rw.flag-collect-forced-goals 'term
;;                                         (car x)
;;                                         (rw.flag-collect-forced-goals 'list (cdr x) acc))
;;         acc)))
;;
;; This routine is provably equal to:
;;
;;   (defund rw.slow-collect-forced-goals (flag x)
;;     (declare (xargs :guard (if (equal flag 'term)
;;                                (rw.tracep x)
;;                              (rw.trace-listp x))
;;                     :measure (two-nats-measure (rank x) (if (equal flag 'term) 1 0))))
;;     (if (equal flag 'term)
;;         (cond ((equal (rw.trace->method x) 'force)
;;                (list (rw.trace-formula x)))
;;               (t
;;                (rw.slow-collect-forced-goals 'list (rw.trace->subtraces x))))
;;       (if (consp x)
;;           (app (rw.slow-collect-forced-goals 'term (car x))
;;                (rw.slow-collect-forced-goals 'list (cdr x)))
;;         nil)))
;;
;; But now I use a less-optimized routine based on revappend.  Why?  The
;; problem is that we want to compute exactly the same forced goals on fast
;; traces as for regular traces.  But in the fast traces, we have to collect
;; the forced goals incrementally as we construct the trace, and we do not have
;; the benefit of an accumulator.  This means that the fast rewriter would have
;; to aggregate its forced goals with app (or fast-app), as above in
;; slow-collect-forced-goals.  But we would prefer to make the fast rewriter
;; faster by using revappend, even though it means making the regular rewriter
;; slightly slower.

(defund rw.flag-collect-forced-goals (flag x)
  (declare (xargs :guard (if (equal flag 'term)
                             (rw.tracep x)
                           (rw.trace-listp x))
                  :measure (two-nats-measure (rank x) (if (equal flag 'term) 1 0))
                  :verify-guards nil))
  (if (equal flag 'term)
      (cond ((equal (rw.trace->method x) 'force)
             (list (rw.trace-formula x)))
            (t
             (rw.flag-collect-forced-goals 'list (rw.trace->subtraces x))))
    (if (consp x)
        (fast-merge (rw.flag-collect-forced-goals 'term (car x))
                    (rw.flag-collect-forced-goals 'list (cdr x)))
      nil)))

(defthm true-listp-of-rw.flag-collect-forced-goals
  (equal (true-listp (rw.flag-collect-forced-goals flag x))
         t)
   :hints(("Goal" :in-theory (enable rw.flag-collect-forced-goals))))

(verify-guards rw.flag-collect-forced-goals)


(definlined rw.collect-forced-goals (x)
  (declare (xargs :guard (rw.tracep x)))
  (rw.flag-collect-forced-goals 'term x))

(definlined rw.collect-forced-goals-list (x)
  (declare (xargs :guard (rw.trace-listp x)))
  (rw.flag-collect-forced-goals 'list x))

(defthmd definition-of-rw.collect-forced-goals
  (equal (rw.collect-forced-goals x)
         (cond ((equal (rw.trace->method x) 'force)
                (list (rw.trace-formula x)))
               (t
                (rw.collect-forced-goals-list (rw.trace->subtraces x)))))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable rw.collect-forced-goals
                                    rw.collect-forced-goals-list
                                    rw.flag-collect-forced-goals))))

(defthmd definition-of-rw.collect-forced-goals-list
  (equal (rw.collect-forced-goals-list x)
         (if (consp x)
             (fast-merge (rw.collect-forced-goals (car x))
                         (rw.collect-forced-goals-list (cdr x)))
           nil))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable rw.collect-forced-goals
                                    rw.collect-forced-goals-list
                                    rw.flag-collect-forced-goals))))

(defthm rw.flag-collect-forced-goals-of-term
  (equal (rw.flag-collect-forced-goals 'term x)
         (rw.collect-forced-goals x))
  :hints(("Goal" :in-theory (enable rw.collect-forced-goals))))

(defthm rw.flag-collect-forced-goals-of-list
  (equal (rw.flag-collect-forced-goals 'list x)
         (rw.collect-forced-goals-list x))
  :hints(("Goal" :in-theory (enable rw.collect-forced-goals-list))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.collect-forced-goals))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.collect-forced-goals-list))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.flag-collect-forced-goals))))

(defthm rw.collect-forced-goals-list-when-not-consp
  (implies (not (consp x))
           (equal (rw.collect-forced-goals-list x)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-rw.collect-forced-goals-list))))

(defthm rw.collect-forced-goals-list-of-cons
  (equal (rw.collect-forced-goals-list (cons a x))
         (fast-merge (rw.collect-forced-goals a)
                     (rw.collect-forced-goals-list x)))
  :hints(("Goal" :in-theory (enable definition-of-rw.collect-forced-goals-list))))

(defthms-flag
  :thms ((term true-listp-of-rw.collect-forced-goals
               (equal (true-listp (rw.collect-forced-goals x))
                      t))
         (t true-listp-of-rw.collect-forced-goals-list
            (equal (true-listp (rw.collect-forced-goals-list x))
                   t)))
  :hints (("Goal"
           :induct (rw.trace-induction flag x)
           :in-theory (enable definition-of-rw.collect-forced-goals))))

(defthms-flag
  :thms ((term forcing-logic.formula-listp-of-rw.collect-forced-goals
               (implies (force (rw.tracep x))
                        (equal (logic.formula-listp (rw.collect-forced-goals x))
                               t)))
         (t forcing-logic.formula-listp-of-rw.collect-forced-goals-list
            (implies (force (rw.trace-listp x))
                     (equal (logic.formula-listp (rw.collect-forced-goals-list x))
                            t))))
  :hints (("Goal"
           :induct (rw.trace-induction flag x)
           :in-theory (enable definition-of-rw.collect-forced-goals))))

(defthms-flag
  :shared-hyp (force (and (equal (cdr (lookup 'equal atbl)) 2)
                          (equal (cdr (lookup 'iff atbl)) 2)))
  :thms ((term forcing-logic.formula-list-atblp-of-rw.collect-forced-goals
               (implies (force (and (rw.tracep x)
                                    (rw.trace-atblp x atbl)))
                        (equal (logic.formula-list-atblp (rw.collect-forced-goals x) atbl)
                               t)))
         (t forcing-logic.formula-list-atblp-of-rw.collect-forced-goals-list
            (implies (force (and (rw.trace-listp x)
                                 (rw.trace-list-atblp x atbl)))
                     (equal (logic.formula-list-atblp (rw.collect-forced-goals-list x) atbl)
                            t))))
  :hints (("Goal"
           :induct (rw.trace-induction flag x)
           :in-theory (enable definition-of-rw.collect-forced-goals))))

(defthm memberp-of-rw.trace-conclusion-formula-in-rw.collect-forced-goals
  (implies (force (equal (rw.trace->method x) 'force))
           (equal (memberp (rw.trace-formula x) (rw.collect-forced-goals x))
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.collect-forced-goals))))

(defthm forcing-subsetp-of-rw.collect-forced-goals-list-of-subtraces
  (implies (force (and (rw.tracep x)
                       (rw.trace-okp x defs)))
           (subsetp (rw.collect-forced-goals-list (rw.trace->subtraces x))
                    (rw.collect-forced-goals x)))
  :hints(("Goal" :in-theory (enable definition-of-rw.collect-forced-goals
                                    definition-of-rw.trace-okp
                                    rw.trace-step-okp
                                    rw.force-tracep))))



(defund rw.collect-forced-goals-list-list (x)
  (declare (xargs :guard (rw.trace-list-listp x)))
  (if (consp x)
      (fast-merge (rw.collect-forced-goals-list (car x))
                  (rw.collect-forced-goals-list-list (cdr x)))
    nil))

(defthm true-listp-of-rw.collect-forced-goals-list-list
   (equal (true-listp (rw.collect-forced-goals-list-list x))
          t)
   :hints(("Goal" :in-theory (enable rw.collect-forced-goals-list-list))))

(defthm rw.collect-forced-goals-list-list-when-not-consp
  (implies (not (consp x))
           (equal (rw.collect-forced-goals-list-list x)
                  nil))
  :hints(("Goal" :in-theory (enable rw.collect-forced-goals-list-list))))

(defthm rw.collect-forced-goals-list-list-of-cons
  (equal (rw.collect-forced-goals-list-list (cons a x))
         (fast-merge (rw.collect-forced-goals-list a)
                     (rw.collect-forced-goals-list-list x)))
  :hints(("Goal" :in-theory (enable rw.collect-forced-goals-list-list))))

(defthm forcing-rw.formula-listp-of-rw.collect-forced-goals-list-list
  (implies (force (rw.trace-list-listp x))
           (equal (logic.formula-listp (rw.collect-forced-goals-list-list x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

;; BOZO errr, don't have a trace-list-list-atblp, maybe we won't need it.
;; (defthm forcing-rw.formula-list-atblp-of-rw.collect-forced-goals-list-list
;;   (implies (force (rw.trace-list-list-atblp x atbl))
;;            (equal (logic.formula-list-atblp (rw.collect-forced-goals-list-list x) atbl)
;;                   t))
;;   :hints(("Goal" :induct (cdr-induction x))))


