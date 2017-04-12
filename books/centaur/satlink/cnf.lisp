; SATLINK - Link from ACL2 to SAT Solvers
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

; cnf.lisp -- Semantics of CNF formulas and basic CNF functions like gathering
; indices, determining maximum indices, etc.

(in-package "SATLINK")
(include-book "varp")
(include-book "litp")
(include-book "std/stobjs/clone" :dir :system)
(include-book "std/stobjs/bitarr" :dir :system)
(local (include-book "data-structures/list-defthms" :dir :system))
(local (std::add-default-post-define-hook :fix))

(defsection env$
  :parents (cnf)
  :short "A bit array that serves as the environment for @(see eval-formula)."

  (defstobj-clone env$ bitarr
    :exports (env$-length env$-get env$-set env$-resize)))

(local (defthm equal-1-when-bitp
         (implies (bitp x)
                  (equal (equal x 1)
                         (not (equal x 0))))))


(defxdoc cnf
  :parents (satlink)
  :short "Our representation (syntax and semantics) for <a
href='http://en.wikipedia.org/wiki/Conjunctive_normal_form'>conjunctive normal
form</a> formulas."

  :long "<p>To express what it means to call a SAT solver, we need a
representation and a semantics for Boolean formulas in conjunctive normal form.
Our syntax is as follows:</p>

<ul>

<li>A <b>variable</b> is a natural number.  To help keep variables separate
from literals, we represent them @(see varp)s, instead of @(see natp)s.</li>

<li>A <b>literal</b> represents either a variable or a negated variable.  We
represent these using a typical numeric encoding: the least significant bit is
the negated bit, and the remaining bits are the variable.  See @(see
litp).</li>

<li>A <b>clause</b> is a disjunction of literals.  We represent these as
ordinary lists of literals.  See @(see lit-listp).</li>

<li>A <b>formula</b> is a conjunction of clauses.  We represent these using
@(see lit-list-listp).</li>

</ul>

<p>The semantics of these formulas are given by @(see eval-formula).</p>")


(define eval-var ((var varp) env$)
  :returns (bit bitp)
  :inline t
  (mbe :logic (get-bit (var-fix var) env$)
       ;; We'll pay the price of a bounds check just to make the guards
       ;; here much easier to satisfy.
       :exec (if (< (the (integer 0 *) var)
                    (the (integer 0 *) (bits-length env$)))
                 (get-bit var env$)
               0)))

(define eval-lit ((lit litp) env$)
  :returns (bit bitp)
  (b-xor (lit->neg lit)
         (eval-var (lit->var lit) env$)))

(define eval-clause ((clause lit-listp) env$)
  :returns (bit bitp)
  (if (atom clause)
      0
    (mbe :logic (b-ior (eval-lit (car clause) env$)
                       (eval-clause (cdr clause) env$))
         :exec (if (bit->bool (eval-lit (car clause) env$))
                   1
                 (eval-clause (cdr clause) env$)))))

(define eval-formula
  :parents (cnf)
  :short "Semantics of CNF formulas."

  ((formula lit-list-listp) env$)
  :returns (bit bitp)

  :long "<p>We define a simple evaluator for CNF formulas that uses an
environment to assign values to the identifiers.</p>

<p>The environment, @(see env$), is an abstract stobj that implements a simple
bit array.  Our evaluators produce a <b>BIT</b> (i.e., 0 or 1) instead of a
BOOL (i.e., T or NIL) to make it directly compatible with the bitarr
stobj.</p>"
  (if (atom formula)
      1
    (mbe :logic
         (b-and (eval-clause (car formula) env$)
                (eval-formula (cdr formula) env$))
         :exec
         (if (bit->bool (eval-clause (car formula) env$))
             (eval-formula (cdr formula) env$)
           0))))

(define eval-cube ((cube lit-listp) env$)
  :returns (bit bitp)
  (if (atom cube)
      1
    (mbe :logic (b-and (eval-lit (car cube) env$)
                       (eval-cube (cdr cube) env$))
         :exec (if (bit->bool (eval-lit (car cube) env$))
                   (eval-cube (cdr cube) env$)
                 0))))


(define fast-max-index-clause ((clause lit-listp) (max natp))
  :parents (max-index-clause)
  :short "Tail-recursive version of @(see max-index-clause)."
  (b* (((when (atom clause))
        (lnfix max))
       (id1 (lit->var (car clause)))
       (max (max (lnfix max) id1)))
    (fast-max-index-clause (cdr clause) max)))

(define max-index-clause ((clause lit-listp))
  :returns (max natp :rule-classes :type-prescription)
  :parents (cnf)
  :short "Maximum index of any identifier used anywhere in a clause."
  :verify-guards nil
  (mbe :logic
       (if (atom clause)
           0
         (max (lit->var (car clause))
              (max-index-clause (cdr clause))))
       :exec
       (fast-max-index-clause clause 0))
  ///
  (defthm fast-max-index-clause-removal
    (equal (fast-max-index-clause clause max)
           (max (nfix max) (max-index-clause clause)))
    :hints(("Goal" :in-theory (enable fast-max-index-clause))))

  (verify-guards max-index-clause))



(define fast-max-index-formula ((formula lit-list-listp) (max natp))
  :parents (max-index-formula)
  :short "Tail recursive version of @(see max-index-formula)."
  (b* (((when (atom formula))
        (lnfix max))
       (max (fast-max-index-clause (car formula) max)))
    (fast-max-index-formula (cdr formula) max)))

(define max-index-formula ((formula lit-list-listp))
  :returns (max natp :rule-classes :type-prescription)
  :parents (cnf)
  :short "Maximum index of any identifier used anywhere in a formula."
  :verify-guards nil
  (mbe :logic
       (if (atom formula)
           0
         (max (max-index-clause (car formula))
              (max-index-formula (cdr formula))))
       :exec (fast-max-index-formula formula 0))
  ///
  (defthm fast-max-index-formula-removal
    (equal (fast-max-index-formula formula max)
           (max (nfix max) (max-index-formula formula)))
    :hints(("Goal" :in-theory (enable fast-max-index-formula))))

  (verify-guards max-index-formula))



(define clause-indices ((clause lit-listp))
  :parents (cnf)
  :short "Collect indices of all identifiers used throughout a clause."

  (if (atom clause)
      nil
    (cons (lit->var (car clause))
          (clause-indices (cdr clause))))

  ///
  (defthm clause-indices-when-atom
    (implies (atom clause)
             (equal (clause-indices clause)
                    nil)))

  (defthm clause-indices-of-cons
    (equal (clause-indices (cons lit clause))
           (cons (lit->var lit)
                 (clause-indices clause)))))



(define formula-indices ((formula lit-list-listp))
  :parents (cnf)
  :short "Collect indices of all identifiers used throughout a formula."

  (if (atom formula)
      nil
    (append (clause-indices (car formula))
            (formula-indices (cdr formula))))

  ///
  (defthm formula-indices-when-atom
    (implies (atom formula)
             (equal (formula-indices formula)
                    nil)))

  (defthm formula-indices-of-cons
    (equal (formula-indices (cons clause formula))
           (append (clause-indices clause)
                   (formula-indices formula)))))

(defstobj-clone assums$ bitarr
  :exports (assums$-length assums$-get assums$-set assums$-resize))


(define lit-assumedp ((lit litp) assums$)
  :guard (< (+ 1 (* 2 (lit->var lit))) (bits-length assums$))
  :guard-hints ('(:use ((:instance lit-fix-bound-by-lit->var (x lit))))
                (and stable-under-simplificationp
                     '(:in-theory (enable lit-val litp))))
  (eql 1 (get-bit (lit-fix lit) assums$)))

(define lit-assume ((lit litp) assums$)
  :guard (< (+ 1 (* 2 (lit->var lit))) (bits-length assums$))
  :guard-hints ('(:use ((:instance lit-fix-bound-by-lit->var (x lit))))
                (and stable-under-simplificationp
                     '(:in-theory (enable litp))))
  (set-bit (mbe :logic (lit-fix lit) :exec lit) 1 assums$)
  ///
  (defthm lit-assumedp-of-lit-assume
    (equal (lit-assumedp lit1 (lit-assume lit assums$))
           (if (lit-equiv lit1 lit) t (lit-assumedp lit1 assums$)))
    :hints(("Goal" :in-theory (enable lit-assumedp))))

  (defthm len-of-lit-assume
    (<= (len assums$) (len (lit-assume lit assums$)))
    :rule-classes :linear))

(defun-sk env-satisfies-assums (env$ assums$)
  (forall var
          (and (implies (lit-assumedp (make-lit var 0) assums$)
                        (equal (eval-var var env$) 1))
               (implies (lit-assumedp (make-lit var 1) assums$)
                        (equal (eval-var var env$) 0))))
  :rewrite :direct)

(in-theory (disable env-satisfies-assums))

(defthm env-satisfies-assums-implies-lit-eval
  (implies (and (env-satisfies-assums env$ assums$)
                (lit-assumedp lit assums$))
           (equal (eval-lit lit env$) 1))
  :hints (("goal" :use ((:instance env-satisfies-assums-necc
                         (var (lit->var lit)))
                        (:instance make-lit-identity))
           :in-theory (e/d (eval-lit) (make-lit-identity
                                       equal-of-lit-fix-backchain)))))

(defthm env-satisfies-assums-implies-not-lit-eval
  (implies (and (env-satisfies-assums env$ assums$)
                (lit-assumedp (lit-negate lit) assums$))
           (equal (eval-lit lit env$) 0))
  :hints (("goal" :use ((:instance env-satisfies-assums-necc
                         (var (lit->var lit)))
                        (:instance make-lit-identity))
           :in-theory (e/d (eval-lit lit-negate) (make-lit-identity
                                                  equal-of-lit-fix-backchain
                                                  equal-of-make-lit)))))

;; (local (defthm equal-of-lit-val
;;          (equal (equal (lit-val x) (lit-val y))
;;                 (equal (lit-fix x) (lit-fix y)))))

;; (local (defthm equal-of-var->index
;;          (equal (equal (var->index x) (var->index y))
;;                 (equal (var-fix x) (var-fix y)))))

;; (local (defthm make-lit-of-var-fix
;;          (equal (make-lit (var-fix x) neg)
;;                 (make-lit x neg))))

(defthm lit-assumedp-of-opposite-when-env-satisfies
  (implies (and (lit-assumedp (lit-negate lit) assums$)
                (env-satisfies-assums env$ assums$))
           (not (lit-assumedp lit assums$)))
  :hints (("goal" :use ((:instance env-satisfies-assums-implies-lit-eval)
                        (:instance env-satisfies-assums-implies-not-lit-eval))
           :in-theory (disable env-satisfies-assums-implies-not-lit-eval
                               env-satisfies-assums-implies-lit-eval))))

(defthm equal-var-fix-forward
  (implies (equal (var-fix x) y)
           (var-equiv x y))
  :rule-classes :forward-chaining)

(defthm equal-var-fix-forward2
  (implies (equal y (var-fix x))
           (var-equiv x y))
  :rule-classes :forward-chaining)

(defthm env-satisfies-assums-of-lit-assume
  (iff (env-satisfies-assums env$ (lit-assume lit assums$))
       (and (equal 1 (eval-lit lit env$))
            (env-satisfies-assums env$ assums$)))
  :hints ((and stable-under-simplificationp
               (b* ((lit (assoc 'env-satisfies-assums clause)))
                 `(:expand (,lit)
                   ; :use ((:instance not-env-satisfies-assums-when-both
                   :in-theory (enable eval-lit equal-of-make-lit))))
          (and stable-under-simplificationp
               '(:use ((:instance lit-assumedp-of-opposite-when-env-satisfies
                        (assums$ (lit-assume lit assums$))
                        (lit (make-lit (env-satisfies-assums-witness env$ assums$) 0))))
                 :in-theory (disable lit-assumedp-of-opposite-when-env-satisfies)))))

(defthm env-satisfies-assums-of-empty-assums
  (env-satisfies-assums env$ (resize-list nil size 0))
  :hints(("Goal" :in-theory (e/d (env-satisfies-assums
                                  lit-assumedp
                                  acl2::nth-of-resize-list-split)
                                 (acl2::resize-list-when-empty))
          :do-not-induct t)))
                   

(define clause-unsat-under-assums ((clause lit-listp)
                                   (assums$))
  :guard (< (+ 1 (* 2 (max-index-clause clause))) (bits-length assums$))
  :guard-hints (("goal" :expand ((max-index-clause clause))))
  :returns (unsatp)
  (b* (((when (atom clause)) t)
       (lit (car clause)))
    (and (lit-assumedp (lit-negate lit) assums$)
         (clause-unsat-under-assums (cdr clause) assums$)))
  ///
  (defthm clause-unsat-under-assums-not-true-when-satisfied
    (implies (and (env-satisfies-assums env$ assums$)
                  (equal (eval-clause clause env$) 1))
             (not (clause-unsat-under-assums clause assums$)))
    :hints(("Goal" :in-theory (enable eval-clause)))))

(define clause-unit-under-assums
  ((clause lit-listp)
   (assums$))
  :returns (mv (final-possibles natp :rule-classes :type-prescription
                                "0 for unsat, 1 for unit, 2 otherwise")
               (unit-lit (implies (equal 1 final-possibles)
                                  (litp unit-lit))))

  :guard (< (+ 1 (* 2 (max-index-clause clause))) (bits-length assums$))
  :guard-hints (("goal" :expand ((max-index-clause clause))))
  (b* (((when (atom clause)) (mv 0 nil))
       (lit (car clause))
       (falsep (lit-assumedp (lit-negate lit) assums$))
       ((when falsep)
        (clause-unit-under-assums (cdr clause) assums$))
       ((when (clause-unsat-under-assums (cdr clause) assums$))
        (mv 1 (lit-fix lit))))
    (mv 2 nil))
  ///
  (std::defret clause-unit-under-assums-0-implies-unsat
    (implies (and (env-satisfies-assums env$ assums$)
                  (equal 1 (eval-clause clause env$)))
             (not (equal 0 final-possibles)))
    :hints(("Goal" :in-theory (enable eval-clause))))

  (std::defret clause-unit-under-assums-1-implies-unit
    (implies (and (env-satisfies-assums env$ assums$)
                  (equal 1 (eval-clause clause env$))
                  (equal 1 final-possibles))
             (equal (eval-lit unit-lit env$) 1))
    :hints(("Goal" :in-theory (enable eval-clause))))

  (std::defret clause-unit-under-assums-unit-lit-implies-in-bounds
    (implies (equal final-possibles 1)
             (<= (lit->var unit-lit)
                 (max-index-clause clause)))
    :hints(("Goal" :in-theory (enable max-index-clause)))
    :rule-classes :linear))

(define trivial-unsat-p1 ((formula lit-list-listp)
                          (assums$))
  :returns (mv unsat-p new-assums$)
  :guard (< (+ 1 (* 2 (max-index-formula formula))) (bits-length assums$))
  :guard-hints (("goal" :expand ((max-index-formula formula))))
  (b* (((when (atom formula)) (mv nil assums$))
       ((mv status unit-lit) (clause-unit-under-assums (car formula) assums$))
       ((when (eql status 0)) ;; unsat
        (mv t assums$))
       ((unless (eql status 1)) ;; not unit
        (trivial-unsat-p1 (cdr formula) assums$))
       ;; unit
       (assums$ (lit-assume unit-lit assums$)))
    (trivial-unsat-p1 (cdr formula) assums$))
  ///
  (std::defret trivial-unsat-p1-correct
    (implies (and (not (equal (eval-formula formula env$) 0))
                  (env-satisfies-assums env$ assums$))
             (not unsat-p))
    :hints(("Goal" :in-theory (enable eval-formula)))))

(define trivial-unsat-p ((formula lit-list-listp))
  :returns unsat-p
  (b* (((acl2::local-stobjs assums$) (mv unsat-p assums$))
       (max-index (max-index-formula formula))
       (assums$ (resize-bits (+ 2 (* 2 max-index)) assums$)))
    (trivial-unsat-p1 formula assums$))
  ///
  (std::defretd trivial-unsat-p-correct
    (implies unsat-p
             (equal (eval-formula formula env$) 0))
    :hints(("Goal" :in-theory (disable acl2::resize-list-when-empty)))))


