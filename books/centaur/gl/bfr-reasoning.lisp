; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")
(include-book "bfr")

;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;; BFR reasoning clause processor
;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(local (xdoc::set-default-parents bfr-reasoning))

(defsection bfr-patterns
  :short "Patterns for recognizing functions that return BFRs."

  (defmacro bfr-patterns ()
    '(acl2::get-term-patterns bfr))

  (defmacro set-bfr-patterns (val)
    `(acl2::set-term-patterns bfr ,val))

  (defmacro add-bfr-pat (val)
    `(acl2::add-term-pattern bfr ,val))

  (defmacro add-bfr-pats (&rest val)
    `(acl2::add-term-patterns bfr . ,val))

  (defmacro add-bfr-fn-pat (val)
    `(acl2::add-fn-term-pattern bfr ,val))

  (defmacro add-bfr-fn-pats (&rest val)
    `(acl2::add-fn-term-patterns bfr . ,val))

  (set-bfr-patterns nil)

  (add-bfr-fn-pats bfr-binary-and
                   bfr-not
                   bfr-binary-or
                   bfr-xor
                   bfr-iff
                   bfr-ite-fn)

  (add-bfr-pats 't 'nil)

  (defun bfr-termp (x bfr-terms pats)
    (or (member-equal x bfr-terms)
        (acl2::match-term-pattern x pats))))


(defsection bfr-eval-patterns
  :short "Patterns for recognizing @(see bfr-eval) calls."

  (defmacro bfr-eval-patterns ()
    '(acl2::get-term-patterns bfr-eval))

  (defmacro set-bfr-eval-patterns (val)
    `(acl2::set-term-patterns bfr-eval ,val))

  (defmacro add-bfr-eval-pat (val)
    `(acl2::add-term-pattern bfr-eval ,val))

  (defmacro add-bfr-eval-pats (&rest val)
    `(acl2::add-term-patterns bfr-eval . ,val))

  (set-bfr-eval-patterns nil)
  (add-bfr-eval-pats (bfr-eval & env))
  (add-bfr-eval-pat (bfr-eval-list & env))
  (add-bfr-eval-pats (bfr-list->u & env))
  (add-bfr-eval-pats (bfr-list->s & env))
  ;; bozo why not also bfr-eval-alist?
  )






(defsection bfr-cp-ev
  :short "Basic evaluator for meta-reasoning about @(see bfr-eval)."
  :long "@(def bfr-cp-ev)"

  (defevaluator bfr-cp-ev bfr-cp-evl
    ((bfr-eval a b)
     (equal a b)
     (not a)
     (implies a b)
     (if a b c)))

  (acl2::def-join-thms bfr-cp-ev))


(defines collect-bfr-eval-vals
  :parents (bfr-eval-cp)
  :verify-guards nil

  (define collect-bfr-eval-vals (term patterns)
    :flag :term
    :returns (terms pseudo-term-listp :hyp (pseudo-termp term))
    (cond ((atom term) nil)
          ((eq (car term) 'quote) nil)
          (t (let ((match (acl2::match-term-pattern term patterns)))
               (if match
                   (list (cdr (assoc 'env match)))
                 (collect-bfr-eval-vals-list (cdr term) patterns))))))

  (define collect-bfr-eval-vals-list (clause patterns)
    :flag :list
    :returns (terms pseudo-term-listp :hyp (pseudo-term-listp clause))
    (if (atom clause)
        nil
      (union-equal (collect-bfr-eval-vals (car clause) patterns)
                   (collect-bfr-eval-vals-list (cdr clause) patterns))))

  :prepwork
  ((local (defthm pseudo-term-listp-union-equal
           (implies (and (pseudo-term-listp x)
                         (pseudo-term-listp y))
                    (pseudo-term-listp (union-equal x y)))))))


(define bfr-eval-vals (clause patterns)
  :parents (bfr-eval-cp)
  :verify-guards nil
  (let ((collect (collect-bfr-eval-vals-list clause patterns)))
    (or collect '(arbitrary-vals)))
  ///
  (defthm bfr-eval-vals-pseudo-term-listp
    (implies (pseudo-term-listp clause)
             (pseudo-term-listp (bfr-eval-vals clause patterns)))))


(define instantiate-bfr-evals (a b vals)
  :parents (bfr-eval-cp)
  :verify-guards nil
  (if (atom vals)
      nil
    (cons `(not (equal (bfr-eval ,a ,(car vals))
                       (bfr-eval ,b ,(car vals))))
          (instantiate-bfr-evals a b (cdr vals))))
  ///

  (defthm instantiate-bfr-evals-correct
    (implies (equal (bfr-cp-ev x a)
                    (bfr-cp-ev y a))
             (not (bfr-cp-ev (disjoin (instantiate-bfr-evals x y vals)) a)))
    :hints (("goal" :induct (instantiate-bfr-evals a b vals))))

  (defthm pseudo-term-listp-instantiate-bfr-evals
    (implies (and (pseudo-term-listp vals)
                  (pseudo-termp a)
                  (pseudo-termp b))
             (pseudo-term-listp (instantiate-bfr-evals a b vals)))))

(define instantiate-equals-with-bfr-evals (clause vals bfr-terms patterns)
  :parents (bfr-eval-cp)
  :verify-guards nil
  (if (atom clause)
      nil
    (let* ((rst-clause (instantiate-equals-with-bfr-evals
                        (cdr clause) vals bfr-terms patterns))
           (lit (car clause)))
      (mv-let (a b)
        (case-match lit
          (('not ('equal a b))
           (mv a b))
          (a (mv a ''nil))
          (& (mv nil nil)))
        (if (and (bfr-termp a bfr-terms patterns)
                 (bfr-termp b bfr-terms patterns))
            (cons (disjoin (instantiate-bfr-evals a b vals))
                  rst-clause)
          (cons lit rst-clause)))))
  ///
  (defthm instantiate-equals-with-bfr-evals-correct
    (implies (bfr-cp-ev (disjoin (instantiate-equals-with-bfr-evals
                                  clause vals bfr-terms patterns))
                        a)
             (bfr-cp-ev (disjoin clause) a))
    :hints (("goal" :induct (len clause)
             :in-theory (disable equal-of-booleans-rewrite
                                 bfr-termp
                                 (:type-prescription bfr-termp)
                                 instantiate-equals-with-bfr-evals
                                 (:type-prescription member-equal)
                                 (:type-prescription acl2::match-term-pattern))
             :expand ((instantiate-equals-with-bfr-evals
                       clause vals bfr-terms patterns)))))

  (defthm pseudo-term-listp-instantiate-equals-with-bfr-evals
    (implies (and (pseudo-term-listp clause)
                  (pseudo-term-listp vals))
             (pseudo-term-listp (instantiate-equals-with-bfr-evals
                                 clause vals bfr-terms patterns)))
    :hints (("goal" :induct (len clause)
             :in-theory (disable equal-of-booleans-rewrite
                                 bfr-termp
                                 (:type-prescription bfr-termp)
                                 instantiate-equals-with-bfr-evals
                                 (:type-prescription member-equal)
                                 (:type-prescription acl2::match-term-pattern))
             :expand ((instantiate-equals-with-bfr-evals
                       clause vals bfr-terms patterns)
                      (instantiate-equals-with-bfr-evals
                       nil vals bfr-terms patterns))))))

(define bfr-eval-cp (clause hints)
  :short "The actual clause processor for bfr-reasoning."
  :verify-guards nil
  (let* ((bfr-terms (car hints))
         (patterns (cadr hints))
         (eval-patterns (caddr hints))
         (vals (bfr-eval-vals clause eval-patterns))
         (clause (instantiate-equals-with-bfr-evals
                  clause vals bfr-terms patterns)))
    (list clause))
  ///
  (defthm bfr-eval-cp-correct
    (implies (and (pseudo-term-listp clause)
                  (alistp a)
                  (bfr-cp-ev (conjoin-clauses
                              (bfr-eval-cp clause hints))
                             a))
             (bfr-cp-ev (disjoin clause) a))
    :rule-classes :clause-processor))


(defsection bfr-reasoning
  :parents (bfr)
  :short "Clause processor for @(see acl2::witness)-style BFR reasoning."
  :long "<p>Tries to apply the @(see bfr-eval-cp) clause processor when goals are
stable-under-simplificationp.  Typical usage:</p>

  @({ :hints ((bfr-reasoning [:or-hint t])) })"

  (defmacro bfr-reasoning (&key or-hint)
    `(if stable-under-simplificationp
         (er-progn
          ;; This just lets us collect the clauses on which this hint is used.
          ,'(assign bfr-eval-cp-clauses
                    (cons clause
                          (and (boundp-global
                                'bfr-eval-cp-clauses state)
                               (@ bfr-eval-cp-clauses))))
          (let ((bfr-patterns (bfr-patterns))
                (bfr-eval-patterns (bfr-eval-patterns)))
            ,(let ((cphint '`(:clause-processor
                              (bfr-eval-cp
                               clause
                               (list nil ',bfr-patterns
                                     ',bfr-eval-patterns)))))
               `(value ,(if or-hint
                            ``(:or (,,cphint
                                    (:no-thanks t)))
                          cphint)))))
       (value nil))))


(defsection bfr-reasoning-mode
  :short "Turn @(see bfr-reasoning) on or off in the @(see default-hints)."
  :long "<p>Usage:</p>
@({
      (bfr-reasoning-mode t)
      (defthm bfr-related-theorem-1 ...)  ;; bfr reasoning is active here
      (defthm bfr-related-theorem-2 ...)  ;; bfr reasoning is active here
      (bfr-reasoning-mode nil)
      (defthm other-theorem ...)          ;; bfr reasoning is disabled here
})"

  (defmacro bfr-reasoning-mode (flg)
    (if flg
        '(add-default-hints '((bfr-reasoning)))
      '(remove-default-hints '((bfr-reasoning))))))


