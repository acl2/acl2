; SATLINK - Link from ACL2 to SAT Solvers
;   Interface with Heule/Hunt/Kaufmann LRAT checker
;
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
; Original author: Sol Swords <sswords@centtech.com>


(in-package "SATLINK")

(include-book "cnf")
(include-book "projects/sat/lrat/list-based/lrat-checker" :dir :system)
(include-book "std/alists/alist-keys" :dir :system)
(local (include-book "cnf-basics"))


(define lit-to-lrat-literal ((x litp))
  :returns (lrat-x lrat::literalp
                   :hints(("Goal" :in-theory (enable lrat::literalp lit->neg lit->var))))
  (b* ((negate (mbe :logic (if (eql (lit->neg x) 1) -1 1)
                    :exec (- 1 (* 2 (lit->neg x))))))
    (* negate (+ 1 (lit->var x))))
  ///
  (std::defret negate-of-lit-to-lrat-literal
    ;; is this the direction to go?
    (equal (lrat::negate lrat-x)
           (lit-to-lrat-literal (lit-negate x))))
  
  (local (defthmd lit-fix-is-make-lit
           (equal (lit-fix x)
                  (make-lit (lit->var x) (lit->neg x))))) 


  (defthm equal-of-lit-to-lrat-literal
    (equal (equal (lit-to-lrat-literal x) (lit-to-lrat-literal y))
           (equal (lit-fix x) (lit-fix y)))
    :hints(("Goal" :in-theory (e/d (equal-of-make-lit
                                    lit-fix-is-make-lit)
                                   (make-lit-identity))))))
           
(define env$-to-lrat-assignment ((idx natp)
                                 (env$))
  :returns (assign lrat::literal-listp)
  :guard (<= idx (bits-length env$))
  (b* (((when (zp idx)) nil)
       (idx (1- idx))
       (val (eval-var idx env$))
       (lit (make-lit idx (b-not val))))
    (cons (lit-to-lrat-literal lit)
          (env$-to-lrat-assignment idx env$)))
  ///

  (local (std::defret not-member-literal
           (implies (<= (nfix idx) (lit->var lit))
                    (not (member (lit-to-lrat-literal lit)
                                 assign)))
           :hints(("Goal" :in-theory (enable equal-of-make-lit)))))
  ;; (local (std::defret not-member-when-greater-than-idx
  ;;          (implies (< (nfix idx) x)
  ;;                   (not (member x assign)))
  ;;          :hints (("goal" :induct t)
  ;;                  (and stable-under-simplificationp
  ;;                       '(:in-theory (enable lit-to-lrat-literal make-var))))))

  ;; (local (std::defret not-member-when-negation-greater-than-idx
  ;;          (implies (< (nfix idx) (lrat::negate x))
  ;;                   (not (member x assign)))))

  (std::defret unique-literalsp-of-env$-to-lrat-assignment
    (lrat::unique-literalsp assign))

  (std::defret not-conflicting-literalsp-of-env$-to-lrat-assignment
    (not (lrat::conflicting-literalsp assign)))

  (std::defret clause-or-assignment-p-of-env$-to-lrat-assignment
    (lrat::clause-or-assignment-p assign)
    :hints(("Goal" :in-theory (enable lrat::clause-or-assignment-p))))

  (std::defret evaluate-literal-of-env$-to-lrat-assignment
    (implies (< (lit->var lit) (nfix idx))
             (equal (lrat::evaluate-literal (lit-to-lrat-literal lit) assign)
                    (acl2::bit->bool (eval-lit lit env$))))
    :hints(("Goal" :in-theory (enable eval-lit equal-of-make-lit)))))

(local (in-theory (disable lrat::evaluate-literal)))


;; In the lrat checker, a clause must have no duplicate or complementary
;; literals.  If we have a clause with duplicate literals we can remove all but
;; the last, but if we have a clause with complementary literals then we
;; actually have to delete that clause completely.  (That's not the same thing
;; as returning the empty clause!) So we'll return an lrat clause and a
;; tautology flag.
(define clause-to-lrat-clause ((clause lit-listp))
  :returns (mv tautologyp
               (lrat-clause lrat::literal-listp))
  (b* (((when (atom clause)) (mv nil nil))
       ((mv taut rest) (clause-to-lrat-clause (cdr clause)))
       ((when taut) (mv t nil))
       (new-lit (lit-to-lrat-literal (car clause)))
       ((when (member (lrat::negate new-lit) rest))
        (mv t nil))
       ((when (member new-lit rest))
        (mv nil rest)))
    (mv nil (cons new-lit rest)))
  ///
  (std::defret unique-literals-of-clause-to-lrat-clause
    (lrat::unique-literalsp lrat-clause))

  (std::defret not-conflicting-literals-of-clause-to-lrat-clause
    (not (lrat::conflicting-literalsp lrat-clause)))

  (std::defret clause-or-assignment-p-of-clause-to-lrat-clause
    (lrat::clause-or-assignment-p lrat-clause)
    :hints(("Goal" :in-theory (enable lrat::clause-or-assignment-p))))

  (local (std::defret eval-clause-when-true-member
           (implies (and (member (lit-to-lrat-literal lit) lrat-clause)
                         (equal (eval-lit lit env$) 1))
                    (equal (eval-clause clause env$) 1))
           :hints(("Goal" :in-theory (enable eval-clause)))))

  (std::defret clause-to-lrat-clause-tautologyp-implies
    (implies tautologyp
             (equal (eval-clause clause env$) 1))
    :hints(("Goal" :in-theory (enable eval-clause eval-lit))))

  (std::defret eval-of-clause-to-lrat-clause
    (implies (and (not tautologyp)
                  (< (max-index-clause clause) (nfix idx)))
             (equal (lrat::evaluate-clause lrat-clause
                                           (env$-to-lrat-assignment idx env$))
                    (acl2::bit->bool (eval-clause clause env$))))
    :hints(("Goal" :in-theory (enable eval-clause max-index-clause)))))


(local (in-theory (disable lrat::formula-truep)))

(local (defthm formula-truep-redef
         (implies (no-duplicatesp (alist-keys formula))
                  (equal (lrat::formula-truep formula assign)
                         (if (atom formula)
                             t
                           (if (and (consp (car formula))
                                    (not (lrat::deleted-clause-p (cdar formula))))
                               (and (equal (lrat::evaluate-clause (cdar formula) assign) t)
                                    (lrat::formula-truep (cdr formula) assign))
                             (lrat::formula-truep (cdr formula) assign)))))
           :hints (("goal" :cases ((lrat::formula-truep formula assign)))
                   (and stable-under-simplificationp
                        (b* ((lit (assoc 'lrat::formula-truep clause))
                             ((unless lit) ;; must be the formula => eval-clause case
                              '(:use ((:instance lrat::formula-truep-necc
                                       (index (caar formula))
                                       (assignment assign)
                                       (formula formula)))
                                :in-theory (disable lrat::formula-truep-necc)))
                             (other-form (if (eq (cadr lit) 'formula)
                                             '(cdr formula)
                                           'formula)))
                          `(:expand (,lit
                                     (alist-keys formula))
                            :use ((:instance lrat::formula-truep-necc
                                   (index ,(cons 'lrat::formula-truep-witness (cdr lit)))
                                   (assignment assign)
                                   (formula ,other-form)))
                            :in-theory (disable lrat::formula-truep-necc)))))
           :rule-classes ((:definition :controller-alist ((lrat::formula-truep t nil))))))

(local (defthm formula-truep-of-cons
         (implies (no-duplicatesp (alist-keys (cons a b)))
                  (equal (lrat::formula-truep (cons a b) assign)
                         (if (and (consp a)
                                  (not (lrat::deleted-clause-p (cdr a))))
                             (and (equal (lrat::evaluate-clause (cdr a) assign) t)
                                  (lrat::formula-truep b assign))
                           (lrat::formula-truep b assign))))))


;; (define eval-lrat-formula ((formula lrat::formula-p)
;;                            (assign lrat::clause-or-assignment-p))
;;   :returns (truep)
;;   (if (atom formula)
;;       t
;;     (if (and (mbt (consp (car formula)))
;;              (not (lrat::deleted-clause-p (cdar formula))))
;;         (and (lrat::evaluate-clause (cdar formula) assign)
;;              (eval-lrat-formula (cdr formula) assign))
;;       (eval-lrat-formula (cdr formula) assign)))
;;   ///
  
;;   (local (std::defret formula-truep-implies-eval-lrat-formula
;;            (implies (and (lrat::formula-truep formula assign)
;;                          (no-duplicatesp (alist-keys formula)))
;;                     (eval-lrat-formula formula assign))
;;            :hints (("goal" :induct t)

;;   (local (std::defret eval-lrat-formula-implies-formula-truep
;;            (implies (and (eval-lrat-formula formula assign)
;;                          (no-duplicatesp (alist-keys formula)))
;;                     (lrat::formula-truep formula assign)))))





(define formula-to-lrat-formula ((formula lit-list-listp)
                                 (clause-idx posp))
  :returns (lrat-formula lrat::formula-p)
  (b* (((when (atom formula)) nil)
       ((mv taut lrat-clause) (clause-to-lrat-clause (car formula)))
       ((when taut)
        (formula-to-lrat-formula (cdr formula) clause-idx))
       (clause-idx (acl2::lposfix clause-idx)))
    (hons-acons clause-idx lrat-clause
                (formula-to-lrat-formula (cdr formula) (+ 1 clause-idx))))
  ///
  (std::defret formula-to-lrat-formula-lookup-key-too-small
    (implies (< key (acl2::lposfix clause-idx))
             (not (hons-assoc-equal key lrat-formula)))
    :hints(("Goal" :in-theory (enable hons-assoc-equal))))

  (std::defret no-duplicate-keys-of-formula-to-lrat-formula
    (no-duplicatesp (alist-keys lrat-formula)))

  (std::defret eval-of-formula-to-lrat-formula
    (implies (< (max-index-formula formula) (nfix idx))
             (equal (lrat::formula-truep lrat-formula (env$-to-lrat-assignment idx env$))
                    (acl2::bit->bool (eval-formula formula env$))))
    :hints(("Goal" :in-theory (enable eval-formula max-index-formula)))))


