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
(include-book "../assms/hypboxp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defthm rank-of-cdr-of-lookup-weak
  ;; BOZO move me to utilities
  ;; BOZO we don't actually need this anymore.
  (equal (< (rank map)
            (rank (cdr (lookup key map))))
         nil)
  :hints(("Goal" :induct (cdr-induction map))))

(defthm rank-of-cdr-of-cdr-of-cdr-of-cdr-weak
  (equal (< (rank x)
            (rank (cdr (cdr (cdr (cdr x))))))
         nil))



;; Essay on rewrite traces.
;;
;; When we rewrite x ==> x', we don't just return x'.  Instead, we return a
;; "trace" of the rewriter's evaluation.
;;
;; Each trace is an aggregate:
;;
;;   - Method is a symbol that just says what we did,
;;   - Hypbox stores the assumptions being used (see the rewrite/assms directory),
;;   - Lhs is the term we rewrote, e.g., x,
;;   - Rhs is the term we produced, e.g., x',
;;   - Iffp says if we rewrote w.r.t. iff or equal,
;;   - Subtraces are recursively a list of traces that we built upon, and
;;   - Extras are any additional information for this step.
;;
;; These traces are often convenient.  Here are a few comments:
;;
;;   (1) Traces unify successful rewrites with failures, by always returning a
;;       single entity, which means the rewriter is simpler and need not ask
;;       "was the rewriting attempt successful?" and can instead just ask for
;;       the rhs of the trace.
;;
;;   (2) It splits the verification of the rewriter into two independent
;;       components: building traces and compiling traces.  This makes it much
;;       easier to change the rewriter, because we just need to show that it
;;       produces a valid trace.
;;
;;   (3) It provides a convenient place to store forced hypotheses.
;;
;;   (4) It gives certain efficiencies.  For example, when we are trying to
;;       apply a rule and some hyp fails, we don't record this effort in the
;;       trace.  So, when we are compiling the trace, we only build proofs for
;;       the "useful" steps in our rewriting.  Also, when we do use a rule, we
;;       can record which rule we have used so that we don't have to try all of
;;       our rules a second time.  You can look at this as separating search
;;       from proof construction as Boulton advocated in his dissertation.
;;
;; There are a lot of similarities between traces and appeals.  Our generic
;; trace recognizer, tracep, mirrors the generic appealp recognizer.  We have
;; step recognizers (fail-tracep, trans-tracep, etc.) that are like the
;; primitive appeal recognizers (axiom-okp, cut-okp, etc.), and combine these
;; into our trace-okp function which is similar to proofp.

(defund rw.flag-tracep (flag x)
  (declare (xargs :guard t
                  :measure (two-nats-measure (rank x) (if (equal flag 'term) 1 0))))
  (if (equal flag 'term)
      ;; We use the following custom cons structure.  We would like to build this
      ;; with defaggregate, but subtraces need to be mutually recursive.
      ;;
      ;;                   .
      ;;    (method . rhs)                  .
      ;;                       (lhs . iffp)           .
      ;;                                       hypbox   (extras . subtraces)
      ;;
      ;; This gives 2-link access to method and rhs, which are needed during
      ;; rewriting, while giving 3 or 4 point access to the other fields which
      ;; aren't needed as often.
      (let ((method    (car (car x)))
            (rhs       (cdr (car x)))
            (lhs       (car (car (cdr x))))
            (iffp      (cdr (car (cdr x))))
            (hypbox    (car (cdr (cdr x))))
            ;(extras    (car (cdr (cdr (cdr x)))))
            (subtraces (cdr (cdr (cdr (cdr x))))))
        (and (symbolp method)
             (rw.hypboxp hypbox)
             (logic.termp lhs)
             (logic.termp rhs)
             (booleanp iffp)
             (rw.flag-tracep 'list subtraces)))
    (if (consp x)
        (and (rw.flag-tracep 'term (car x))
             (rw.flag-tracep 'list (cdr x)))
      t)))

(definlined rw.tracep (x)
  (declare (xargs :guard t))
  (rw.flag-tracep 'term x))

(definlined rw.trace-listp (x)
  (declare (xargs :guard t))
  (rw.flag-tracep 'list x))

(defthmd definition-of-rw.tracep
  (equal (rw.tracep x)
         (let ((method    (car (car x)))
               (rhs       (cdr (car x)))
               (lhs       (car (car (cdr x))))
               (iffp      (cdr (car (cdr x))))
               (hypbox    (car (cdr (cdr x))))
               ;(extras    (car (cdr (cdr (cdr x)))))
               (subtraces (cdr (cdr (cdr (cdr x))))))
           (and (symbolp method)
                (rw.hypboxp hypbox)
                (logic.termp lhs)
                (logic.termp rhs)
                (booleanp iffp)
                (rw.trace-listp subtraces))))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable rw.tracep
                                    rw.trace-listp
                                    rw.flag-tracep))))

(defthmd definition-of-rw.trace-listp
  (equal (rw.trace-listp x)
         (if (consp x)
             (and (rw.tracep (car x))
                  (rw.trace-listp (cdr x)))
           t))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable rw.tracep
                                    rw.trace-listp
                                    rw.flag-tracep))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.tracep))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.trace-listp))))



(defun rw.raw-trace-induction (flag x)
  (declare (xargs :verify-guards nil
                  :measure (two-nats-measure (rank x) (if (equal flag 'term) 1 0))))
  (if (equal flag 'term)
      (rw.raw-trace-induction 'list (cdr (cdr (cdr (cdr x)))))
    (if (consp x)
        (list (rw.raw-trace-induction 'term (car x))
              (rw.raw-trace-induction 'list (cdr x)))
      nil)))


(defthm rw.trace-listp-when-not-consp
  (implies (not (consp x))
           (equal (rw.trace-listp x)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.trace-listp))))

(defthm rw.trace-listp-of-cons
  (equal (rw.trace-listp (cons a x))
         (and (rw.tracep a)
              (rw.trace-listp x)))
  :hints(("Goal" :in-theory (enable definition-of-rw.trace-listp))))

(defthms-flag
  :thms ((term booleanp-of-rw.tracep
               (equal (booleanp (rw.tracep x))
                      t))
         (t booleanp-of-rw.trace-listp
            (equal (booleanp (rw.trace-listp x))
                   t)))
  :hints (("Goal"
           :in-theory (enable definition-of-rw.tracep)
           :induct (rw.raw-trace-induction flag x))))

(deflist rw.trace-listp (x)
  (rw.tracep x)
  :elementp-of-nil nil
  :already-definedp t)

(deflist rw.trace-list-listp (x)
  (rw.trace-listp x)
  :elementp-of-nil t)



(definlined rw.trace->method (x)
  (declare (xargs :guard (rw.tracep x)
                  :guard-hints (("Goal" :in-theory (enable definition-of-rw.tracep)))))
  (car (car x)))

(definlined rw.trace->hypbox (x)
  (declare (xargs :guard (rw.tracep x)
                  :guard-hints (("Goal" :in-theory (enable definition-of-rw.tracep)))))
  (car (cdr (cdr x))))

(definlined rw.trace->lhs (x)
  (declare (xargs :guard (rw.tracep x)
                  :guard-hints (("Goal" :in-theory (enable definition-of-rw.tracep)))))
  (car (car (cdr x))))

(definlined rw.trace->rhs (x)
  (declare (xargs :guard (rw.tracep x)
                  :guard-hints (("Goal" :in-theory (enable definition-of-rw.tracep)))))
  (cdr (car x)))

(definlined rw.trace->iffp (x)
  (declare (xargs :guard (rw.tracep x)
                  :guard-hints (("Goal" :in-theory (enable definition-of-rw.tracep)))))
  (cdr (car (cdr x))))

(definlined rw.trace->subtraces (x)
  (declare (xargs :guard (rw.tracep x)
                  :guard-hints (("Goal" :in-theory (enable definition-of-rw.tracep)))))
  (cdr (cdr (cdr (cdr x)))))

(definlined rw.trace->extras (x)
  (declare (xargs :guard (rw.tracep x)
                  :guard-hints (("Goal" :in-theory (enable definition-of-rw.tracep)))))
  (car (cdr (cdr (cdr x)))))

(defprojection :list (rw.trace-list-iffps x)
               :element (rw.trace->iffp x)
               :guard (rw.trace-listp x))

(defprojection :list (rw.trace-list-lhses x)
               :element (rw.trace->lhs x)
               :guard (rw.trace-listp x))

(defprojection :list (rw.trace-list-rhses x)
               :element (rw.trace->rhs x)
               :guard (rw.trace-listp x))

(defprojection :list (rw.trace-list-hypboxes x)
               :element (rw.trace->hypbox x)
               :guard (rw.trace-listp x))

(defprojection :list (rw.trace-list-list-rhses x)
               :element (rw.trace-list-rhses x)
               :guard (rw.trace-list-listp x))


(definlined rw.trace (method hypbox lhs rhs iffp subtraces extras)
  (declare (xargs :guard (and (symbolp method)
                              (rw.hypboxp hypbox)
                              (logic.termp lhs)
                              (logic.termp rhs)
                              (booleanp iffp)
                              (rw.trace-listp subtraces))))
  (cons (cons method rhs)
        (cons (cons lhs iffp)
              (cons hypbox
                    (cons extras subtraces)))))

(defthm rw.trace-under-iff
  (iff (rw.trace method hypbox lhs rhs iffp subtraces extras)
       t)
  :hints(("Goal" :in-theory (enable rw.trace))))

(defthm rw.trace->method-of-rw.trace
  (equal (rw.trace->method (rw.trace method hypbox lhs rhs iffp subtraces extras))
         method)
  :hints(("Goal" :in-theory (enable rw.trace rw.trace->method))))

(defthm rw.trace->hypbox-of-rw.trace
  (equal (rw.trace->hypbox (rw.trace method hypbox lhs rhs iffp subtraces extras))
         hypbox)
  :hints(("Goal" :in-theory (enable rw.trace rw.trace->hypbox))))

(defthm rw.trace->lhs-of-rw.trace
  (equal (rw.trace->lhs (rw.trace method hypbox lhs rhs iffp subtraces extras))
         lhs)
  :hints(("Goal" :in-theory (enable rw.trace rw.trace->lhs))))

(defthm rw.trace->rhs-of-rw.trace
  (equal (rw.trace->rhs (rw.trace method hypbox lhs rhs iffp subtraces extras))
         rhs)
  :hints(("Goal" :in-theory (enable rw.trace rw.trace->rhs))))

(defthm rw.trace->iffp-of-rw.trace
  (equal (rw.trace->iffp (rw.trace method hypbox lhs rhs iffp subtraces extras))
         iffp)
  :hints(("Goal" :in-theory (enable rw.trace rw.trace->iffp))))

(defthm rw.trace->subtraces-of-rw.trace
  (equal (rw.trace->subtraces (rw.trace method hypbox lhs rhs iffp subtraces extras))
         subtraces)
  :hints(("Goal" :in-theory (enable rw.trace rw.trace->subtraces))))

(defthm rw.trace->extras-of-rw.trace
  (equal (rw.trace->extras (rw.trace method hypbox lhs rhs iffp subtraces extras))
         extras)
  :hints(("Goal" :in-theory (enable rw.trace rw.trace->extras))))

(defthm forcing-rw.tracep-of-rw.trace
  (implies (force (and (symbolp method)
                       (rw.hypboxp hypbox)
                       (logic.termp lhs)
                       (logic.termp rhs)
                       (booleanp iffp)
                       (rw.trace-listp subtraces)))
           (equal (rw.tracep (rw.trace method hypbox lhs rhs iffp subtraces extras))
                  t))
  :hints(("Goal" :in-theory (enable rw.trace definition-of-rw.tracep))))

(defthm forcing-symbolp-of-rw.trace->method
  (implies (force (rw.tracep x))
           (equal (symbolp (rw.trace->method x))
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.tracep rw.trace->method))))

(defthm forcing-rw.hypboxp-of-rw.trace->hypbox
  (implies (force (rw.tracep x))
           (equal (rw.hypboxp (rw.trace->hypbox x))
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.tracep rw.trace->hypbox))))

(defthm forcing-logic.termp-of-rw.trace->lhs
  (implies (force (rw.tracep x))
           (equal (logic.termp (rw.trace->lhs x))
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.tracep rw.trace->lhs))))

(defthm forcing-logic.termp-of-rw.trace->rhs
  (implies (force (rw.tracep x))
           (equal (logic.termp (rw.trace->rhs x))
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.tracep rw.trace->rhs))))

(defthm forcing-booleanp-of-rw.trace->iffp
  (implies (force (rw.tracep x))
           (equal (booleanp (rw.trace->iffp x))
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.tracep rw.trace->iffp))))

(defthm forcing-rw.trace-listp-of-rw.trace->subtraces
  (implies (force (rw.tracep x))
           (equal (rw.trace-listp (rw.trace->subtraces x))
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.tracep rw.trace->subtraces))))

(defthm forcing-logic.term-listp-of-rw.trace-list-lhses
  (implies (force (rw.trace-listp x))
           (equal (logic.term-listp (rw.trace-list-lhses x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-listp-of-rw.trace-list-rhses
  (implies (force (rw.trace-listp x))
           (equal (logic.term-listp (rw.trace-list-rhses x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-listp-of-rw.trace-list-list-rhses
  (implies (force (rw.trace-list-listp x))
           (equal (logic.term-list-listp (rw.trace-list-list-rhses x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm cons-listp-of-rw.trace-list-list-rhses
  (equal (cons-listp (rw.trace-list-list-rhses x))
         (cons-listp x))
  :hints(("Goal" :induct (cdr-induction x))))




(defthm rw.trace->lhs-under-iff
  (implies (rw.tracep x)
           (iff (rw.trace->lhs x)
                t))
  :hints(("Goal" :in-theory (enable definition-of-rw.tracep rw.trace->lhs))))

(defthm rw.trace->rhs-under-iff
  (implies (rw.tracep x)
           (iff (rw.trace->rhs x)
                t))
  :hints(("Goal" :in-theory (enable definition-of-rw.tracep rw.trace->rhs))))



(defthm rank-of-rw.trace->subtraces-weak
  (equal (< (rank x)
            (rank (rw.trace->subtraces x)))
         nil)
  :hints(("Goal" :in-theory (enable rw.trace->subtraces))))




(defund rw.flag-trace-atblp (flag x atbl)
  (declare (xargs :guard (and (if (equal flag 'term)
                                  (rw.tracep x)
                                (rw.trace-listp x))
                              (logic.arity-tablep atbl))
                  :measure (two-nats-measure (rank x) (if (equal flag 'term) 1 0))))
  (if (equal flag 'term)
      (and (rw.hypbox-atblp (rw.trace->hypbox x) atbl)
           (logic.term-atblp (rw.trace->lhs x) atbl)
           (logic.term-atblp (rw.trace->rhs x) atbl)
           (rw.flag-trace-atblp 'list (rw.trace->subtraces x) atbl))
    (if (consp x)
        (and (rw.flag-trace-atblp 'term (car x) atbl)
             (rw.flag-trace-atblp 'list (cdr x) atbl))
      t)))

(definlined rw.trace-atblp (x atbl)
  (declare (xargs :guard (and (rw.tracep x)
                              (logic.arity-tablep atbl))))
  (rw.flag-trace-atblp 'term x atbl))

(definlined rw.trace-list-atblp (x atbl)
  (declare (xargs :guard (and (rw.trace-listp x)
                              (logic.arity-tablep atbl))))
  (rw.flag-trace-atblp 'list x atbl))

(defthmd definition-of-rw.trace-atblp
  (equal (rw.trace-atblp x atbl)
         (and (rw.hypbox-atblp (rw.trace->hypbox x) atbl)
              (logic.term-atblp (rw.trace->lhs x) atbl)
              (logic.term-atblp (rw.trace->rhs x) atbl)
              (rw.trace-list-atblp (rw.trace->subtraces x) atbl)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable rw.trace-atblp
                                    rw.trace-list-atblp
                                    rw.flag-trace-atblp))))

(defthmd definition-of-rw.trace-list-atblp
  (equal (rw.trace-list-atblp x atbl)
         (if (consp x)
             (and (rw.trace-atblp (car x) atbl)
                  (rw.trace-list-atblp (cdr x) atbl))
           t))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable rw.trace-atblp
                                    rw.trace-list-atblp
                                    rw.flag-trace-atblp))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.trace-atblp))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.trace-list-atblp))))

(defthm rw.trace-atblp-of-nil
  (equal (rw.trace-atblp nil atbl)
         nil)
  :hints(("Goal" :in-theory (enable definition-of-rw.trace-atblp))))

(defun rw.trace-induction (flag x)
  (declare (xargs :verify-guards nil
                  :measure (two-nats-measure (rank x) (if (equal flag 'term) 1 0))))
  (if (equal flag 'term)
      (rw.trace-induction 'list (rw.trace->subtraces x))
    (if (consp x)
        (list (rw.trace-induction 'term (car x))
              (rw.trace-induction 'list (cdr x)))
      nil)))

(defthm rw.trace-list-atblp-when-not-consp
  (implies (not (consp x))
           (equal (rw.trace-list-atblp x atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.trace-list-atblp))))

(defthm rw.trace-list-atblp-of-cons
  (equal (rw.trace-list-atblp (cons a x) atbl)
         (and (rw.trace-atblp a atbl)
              (rw.trace-list-atblp x atbl)))
  :hints(("Goal" :in-theory (enable definition-of-rw.trace-list-atblp))))

(defthms-flag
  :thms ((term booleanp-of-rw.trace-atblp
               (equal (booleanp (rw.trace-atblp x atbl))
                      t))
         (t booleanp-of-rw.trace-list-atblp
            (equal (booleanp (rw.trace-list-atblp x atbl))
                   t)))
  :hints (("Goal"
           :in-theory (enable definition-of-rw.trace-atblp)
           :induct (rw.trace-induction flag x))))

(deflist rw.trace-list-atblp (x atbl)
  (rw.trace-atblp x atbl)
  :elementp-of-nil nil
  :already-definedp t)

(defthm forcing-rw.hypbox-atblp-of-rw.trace->hypbox
  (implies (force (rw.trace-atblp x atbl))
           (equal (rw.hypbox-atblp (rw.trace->hypbox x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.trace-atblp))))

(defthm forcing-logic.term-atblp-of-rw.trace->lhs
  (implies (force (rw.trace-atblp x atbl))
           (equal (logic.term-atblp (rw.trace->lhs x) atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (definition-of-rw.trace-atblp)
                                 (forcing-rw.hypbox-atblp-of-rw.trace->hypbox)))))

(defthm forcing-logic.term-atblp-of-rw.trace->rhs
  (implies (force (rw.trace-atblp x atbl))
           (equal (logic.term-atblp (rw.trace->rhs x) atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (definition-of-rw.trace-atblp)
                                 (forcing-rw.hypbox-atblp-of-rw.trace->hypbox
                                  forcing-logic.term-atblp-of-rw.trace->lhs)))))

(defthm forcing-logic.term-list-atblp-of-rw.trace->subtraces
  (implies (force (rw.trace-atblp x atbl))
           (equal (rw.trace-list-atblp (rw.trace->subtraces x) atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (definition-of-rw.trace-atblp)
                                 (forcing-rw.hypbox-atblp-of-rw.trace->hypbox
                                  forcing-logic.term-atblp-of-rw.trace->lhs
                                  forcing-logic.term-atblp-of-rw.trace->rhs)))))

;; no equivalent of this for hypboxes
;; (defthm forcing-logic.term-list-list-atblp-of-rw.trace-list-assms
;;   (implies (force (rw.trace-list-atblp x atbl))
;;            (equal (rw.assms-list-atblp (rw.trace-list-assms x) atbl)
;;                   t))
;;   :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-atblp-of-rw.trace-list-lhses
  (implies (force (rw.trace-list-atblp x atbl))
           (equal (logic.term-list-atblp (rw.trace-list-lhses x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-atblp-of-rw.trace-list-rhses
  (implies (force (rw.trace-list-atblp x atbl))
           (equal (logic.term-list-atblp (rw.trace-list-rhses x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-rw.trace-atblp-of-rw.trace
  (implies (force (and (rw.hypbox-atblp hypbox atbl)
                       (logic.term-atblp lhs atbl)
                       (logic.term-atblp rhs atbl)
                       (rw.trace-list-atblp subtraces atbl)))
           (equal (rw.trace-atblp (rw.trace method hypbox lhs rhs iffp subtraces extras) atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.trace-atblp))))





;; Trace Formulas.
;;
;; We say each trace represents the goal formula:
;;
;;    [hyps ->] (equiv lhs rhs) = t.
;;
;; If there are no nhyps, by this we mean:
;;
;;    (equiv lhs rhs) = t
;;
;; Otherwise, we mean:
;;
;;    assms-formula v (equiv lhs rhs) = t

(definlined rw.trace-conclusion-formula (x)
  ;; Construct (equiv lhs rhs) = t
  (declare (xargs :guard (rw.tracep x)))
  (logic.pequal (logic.function (if (rw.trace->iffp x) 'iff 'equal)
                                (list (rw.trace->lhs x)
                                      (rw.trace->rhs x)))
                ''t))

(in-theory (disable (:e rw.trace-conclusion-formula)))

(defthm forcing-logic.formulap-of-rw.trace-conclusion-formula
  (implies (force (rw.tracep x))
           (equal (logic.formulap (rw.trace-conclusion-formula x))
                  t))
  :hints(("Goal" :in-theory (enable rw.trace-conclusion-formula))))

(defthm forcing-logic.formula-atblp-of-rw.trace-conclusion-formula
  (implies (force (and (rw.trace-atblp x atbl)
                       (equal (cdr (lookup 'iff atbl)) 2)
                       (equal (cdr (lookup 'equal atbl)) 2)))
           (equal (logic.formula-atblp (rw.trace-conclusion-formula x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.trace-conclusion-formula))))



(defprojection
  :list (rw.trace-list-conclusion-formulas x)
  :element (rw.trace-conclusion-formula x)
  :guard (rw.trace-listp x))

(defthm forcing-logic.formula-listp-of-rw.trace-list-conclusion-formulas
  (implies (force (rw.trace-listp x))
           (equal (logic.formula-listp (rw.trace-list-conclusion-formulas x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.formula-list-atblp-of-rw.trace-list-conclusion-formulas
  (implies (force (and (rw.trace-list-atblp x atbl)
                       (equal (cdr (lookup 'iff atbl)) 2)
                       (equal (cdr (lookup 'equal atbl)) 2)))
           (equal (logic.formula-list-atblp (rw.trace-list-conclusion-formulas x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(definlined rw.trace-formula (x)
  ;; Construct [hyps ->] (equiv lhs rhs) = t
  (declare (xargs :guard (rw.tracep x)))
  (let ((hypbox (rw.trace->hypbox x)))
    (if (and (not (rw.hypbox->left hypbox))
             (not (rw.hypbox->right hypbox)))
        (rw.trace-conclusion-formula x)
      (logic.por (rw.hypbox-formula hypbox)
                 (rw.trace-conclusion-formula x)))))

(defthm forcing-logic.formulap-of-rw.trace-formula
  (implies (force (rw.tracep x))
           (equal (logic.formulap (rw.trace-formula x))
                  t))
  :hints(("Goal" :in-theory (enable rw.trace-formula))))

(defthm forcing-logic.formula-atblp-of-rw.trace-formula
  (implies (force (and (rw.tracep x)
                       (rw.trace-atblp x atbl)
                       (equal (cdr (lookup 'iff atbl)) 2)
                       (equal (cdr (lookup 'equal atbl)) 2)))
           (equal (logic.formula-atblp (rw.trace-formula x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.trace-formula))))

(defprojection :list (rw.trace-list-formulas x)
               :element (rw.trace-formula x)
               :guard (rw.trace-listp x))

(defthm forcing-logic.formula-listp-of-rw.trace-list-formulas
  (implies (force (rw.trace-listp x))
           (equal (logic.formula-listp (rw.trace-list-formulas x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.formula-list-atblp-of-rw.trace-list-formulas
  (implies (force (and (rw.trace-listp x)
                       (rw.trace-list-atblp x atbl)
                       (equal (cdr (lookup 'iff atbl)) 2)
                       (equal (cdr (lookup 'equal atbl)) 2)))
           (equal (logic.formula-list-atblp (rw.trace-list-formulas x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))


(encapsulate
 ()
 (local (in-theory (enable rw.trace-conclusion-formula
                           rw.trace-formula)))

 (defthm logic.all-atomicp-of-rw.trace-list-conclusion-formulas
   (equal (logic.all-atomicp (rw.trace-list-conclusion-formulas x))
          t)
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm logic.all-atomicp-of-rw.trace-list-conclusion-formulas-free
   (implies (equal conclusions (rw.trace-list-conclusion-formulas x))
            (equal (logic.all-atomicp conclusions)
                   t)))

 (defthm logic.=rhses-of-rw.trace-list-conclusion-formulas
   (equal (logic.=rhses (rw.trace-list-conclusion-formulas x))
          (repeat ''t (len x)))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm logic.=rhses-of-rw.trace-list-conclusion-formulas-free
   (implies (equal conclusions (rw.trace-list-conclusion-formulas x))
            (equal (logic.=rhses conclusions)
                   (repeat ''t (len x))))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm logic.all-functionsp-of-logic.=lhses-of-rw.trace-list-conclusion-formulas
   (equal (logic.all-functionsp (logic.=lhses (rw.trace-list-conclusion-formulas x)))
          t)
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm logic.all-functionsp-of-logic.=lhses-of-rw.trace-list-conclusion-formulas-free
   (implies (equal conclusions (rw.trace-list-conclusion-formulas x))
            (equal (logic.all-functionsp (logic.=lhses conclusions))
                   t)))

 (defthm logic.strip-function-names-of-logic.=lhses-of-rw.trace-list-conclusion-formulas
   (implies (all-equalp nil (rw.trace-list-iffps x))
            (equal (logic.strip-function-names (logic.=lhses (rw.trace-list-conclusion-formulas x)))
                   (repeat 'equal (len x))))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm logic.strip-function-names-of-logic.=lhses-of-rw.trace-list-conclusion-formulas-free
   (implies (and (all-equalp nil (rw.trace-list-iffps x))
                 (equal conclusions (rw.trace-list-conclusion-formulas x)))
            (equal (logic.strip-function-names (logic.=lhses conclusions))
                   (repeat 'equal (len conclusions)))))

 (defthm strip-lens-of-logic.strip-function-args-of-logic.=lhses-of-rw.trace-list-conclusion-formulas
   (implies (all-equalp nil (rw.trace-list-iffps x))
            (equal (strip-lens (logic.strip-function-args (logic.=lhses (rw.trace-list-conclusion-formulas x))))
                   (repeat 2 (len x))))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm strip-lens-of-logic.strip-function-args-of-logic.=lhses-of-rw.trace-list-conclusion-formulas-free
   (implies (and (all-equalp nil (rw.trace-list-iffps x))
                 (equal conclusions (rw.trace-list-conclusion-formulas x)))
            (equal (strip-lens (logic.strip-function-args (logic.=lhses conclusions)))
                   (repeat 2 (len conclusions)))))

 (defthm strip-firsts-of-logic.strip-function-args-of-logic.=lhses-of-rw.trace-list-lhses
   (equal (strip-firsts (logic.strip-function-args (logic.=lhses (rw.trace-list-conclusion-formulas x))))
          (rw.trace-list-lhses x))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm strip-firsts-of-logic.strip-function-args-of-logic.=lhses-of-rw.trace-list-lhses-free
   (implies (equal conclusions (rw.trace-list-conclusion-formulas x))
            (equal (strip-firsts (logic.strip-function-args (logic.=lhses conclusions)))
                   (rw.trace-list-lhses x))))

 (defthm strip-seconds-of-logic.strip-function-args-of-logic.=lhses-of-rw.trace-list-lhses
   (equal (strip-seconds (logic.strip-function-args (logic.=lhses (rw.trace-list-conclusion-formulas x))))
          (rw.trace-list-rhses x))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm strip-seconds-of-logic.strip-function-args-of-logic.=lhses-of-rw.trace-list-lhses-free
   (implies (equal conclusions (rw.trace-list-conclusion-formulas x))
            (equal (strip-seconds (logic.strip-function-args (logic.=lhses conclusions)))
                   (rw.trace-list-rhses x))))

 (local (in-theory (disable forcing-equal-of-logic.por-list-rewrite)))

 (defthm rw.trace-list-formulas-when-all-equalp-of-rw.trace-list-hypboxes
   (implies (and (all-equalp hypbox (rw.trace-list-hypboxes x))
                 (force (rw.trace-listp x)))
            (equal (rw.trace-list-formulas x)
                   (cond ((not (consp x))
                          nil)
                         ((and (not (rw.hypbox->left hypbox))
                               (not (rw.hypbox->right hypbox)))
                          (rw.trace-list-conclusion-formulas x))
                         (t
                          (logic.por-list
                           (repeat (rw.hypbox-formula hypbox) (len x))
                           (rw.trace-list-conclusion-formulas x))))))
   :hints(("Goal" :induct (cdr-induction x)))))





(defund rw.faster-flag-tracep (flag x ext-hypbox)
  (declare (xargs :guard (rw.hypboxp ext-hypbox)
                  :measure (two-nats-measure (rank x) (if (equal flag 'term) 1 0))))

; This is a fancy, fast tracep check.  We take an "external hypbox" as an extra
; argument.  Before we check whether our hypbox is a valid hypbox, we check
; whether it is equal to this external box.  If so, we do not need to check
; whether it is valid.  Note that when we check our subtraces, we use our own
; hypbox, not the ext-hypbox.
;
; Why is this fast?  In practice, traces other than the "if" traces share the
; same hypbox.  So most of the time we should be able to say, "Yes, they are
; the same," by a simple pointer-equality check, and thus avoid the more
; expensive hypboxp check.  Also note that for "if" traces such as
; crewrite-if-generalcase, the equality can be settled fairly quickly.  The net
; result is that putting this in, instead of tracep, in ccstep-listp, led to
; about a 6x speedup in our ccstep-listp check.

  (if (equal flag 'term)
      (let* ((method    (car (car x)))
             (rhs       (cdr (car x)))
             (lhs       (car (car (cdr x))))
             (iffp      (cdr (car (cdr x))))
             (hypbox    (car (cdr (cdr x))))
             (subtraces (cdr (cdr (cdr (cdr x))))))
        (and (symbolp method)
             (or (equal hypbox ext-hypbox)
                 (rw.faster-hypboxp hypbox))
             (logic.termp lhs)
             (logic.termp rhs)
             (booleanp iffp)
             (rw.faster-flag-tracep 'list subtraces hypbox)))
    (if (consp x)
        (and (rw.faster-flag-tracep 'term (car x) ext-hypbox)
             (rw.faster-flag-tracep 'list (cdr x) ext-hypbox))
      t)))

(defund rw.faster-tracep (x ext-hypbox)
  (declare (xargs :guard (rw.hypboxp ext-hypbox)))
  (rw.faster-flag-tracep 'term x ext-hypbox))

(defund rw.faster-trace-listp (x ext-hypbox)
  (declare (xargs :guard (rw.hypboxp ext-hypbox)))
  (rw.faster-flag-tracep 'list x ext-hypbox))

(defthmd definition-of-rw.faster-tracep
  (equal (rw.faster-tracep x ext-hypbox)
         (let* ((method    (car (car x)))
                (rhs       (cdr (car x)))
                (lhs       (car (car (cdr x))))
                (iffp      (cdr (car (cdr x))))
                (hypbox    (car (cdr (cdr x))))
                (subtraces (cdr (cdr (cdr (cdr x))))))
           (and (symbolp method)
                (or (equal hypbox ext-hypbox)
                    (rw.faster-hypboxp hypbox))
                (logic.termp lhs)
                (logic.termp rhs)
                (booleanp iffp)
                (rw.faster-trace-listp subtraces hypbox))))
  :rule-classes :definition
  :hints(("Goal"
          :expand (rw.faster-flag-tracep 'term x ext-hypbox)
          :in-theory (enable rw.faster-tracep rw.faster-trace-listp))))

(defthmd definition-of-rw.faster-trace-listp
  (equal (rw.faster-trace-listp x ext-hypbox)
         (if (consp x)
             (and (rw.faster-tracep (car x) ext-hypbox)
                  (rw.faster-trace-listp (cdr x) ext-hypbox))
           t))
  :rule-classes :definition
  :hints(("Goal"
          :expand (rw.faster-flag-tracep 'list x ext-hypbox)
          :in-theory (enable rw.faster-tracep rw.faster-trace-listp))))

(defthm rw.faster-flag-tracep-of-term
  (equal (rw.faster-flag-tracep 'term x hypbox)
         (rw.faster-tracep x hypbox))
  :hints(("Goal" :in-theory (enable rw.faster-tracep))))

(defthm rw.faster-flag-tracep-of-list
  (equal (rw.faster-flag-tracep 'list x hypbox)
         (rw.faster-trace-listp x hypbox))
  :hints(("Goal" :in-theory (enable rw.faster-trace-listp))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.faster-tracep))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.faster-trace-listp))))

(defthm rw.faster-trace-listp-when-not-consp
  (implies (not (consp x))
           (equal (rw.faster-trace-listp x ext-hypbox)
                  t))
  :hints(("Goal" :expand ((rw.faster-trace-listp x ext-hypbox)))))

(defthm rw.faster-trace-listp-of-cons
  (equal (rw.faster-trace-listp (cons a x) ext-hypbox)
         (and (rw.faster-tracep a ext-hypbox)
              (rw.faster-trace-listp x ext-hypbox)))
  :hints(("Goal"
          :expand ((rw.faster-trace-listp (cons a x) ext-hypbox)))))

;; (defthm rw.faster-tracep-of-nil
;;   (equal (rw.faster-tracep nil ext-hypbox)
;;          nil)
;;   :hints(("Goal" :expand (rw.faster-tracep nil ext-hypbox))))

;; (deflist rw.faster-trace-listp (x ext-hypbox)
;;   (rw.faster-tracep x ext-hypbox)
;;   :elementp-of-nil nil
;;   :already-definedp t)

(defthms-flag
  :shared-hyp (force (rw.hypboxp hypbox))
  :thms ((term rw.faster-tracep-removal
               (equal (rw.faster-tracep x hypbox)
                      (rw.tracep x)))
         (t rw.faster-trace-listp-removal
            (equal (rw.faster-trace-listp x hypbox)
                   (rw.trace-listp x))))
  :hints(("Goal"
          :induct (rw.faster-flag-tracep flag x hypbox)
          :in-theory (e/d ((:i rw.faster-flag-tracep))
                          ((:e acl2::force)))
          :expand ((rw.faster-tracep x hypbox)
                   (rw.tracep x)))))
