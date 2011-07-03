; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

; witness-cp.lisp:  Clause processor for reasoning about quantifier-like
; predicates.

(in-package "ACL2")

(include-book "clause-processors/use-by-hint" :dir :system)
(include-book "clause-processors/generalize" :dir :system)
(include-book "clause-processors/unify-subst" :dir :system)
(include-book "tools/bstar" :dir :system)
(include-book "clause-processors/ev-theoremp" :dir :system)
(include-book "tools/def-functional-instance" :dir :system)
(include-book "tools/oracle-eval" :dir :system)
(include-book "data-structures/no-duplicates" :dir :system)

(set-inhibit-warnings "theory")


(local (in-theory (disable state-p1-forward)))

;; WITNESS-CP is an extensible clause processor that can use
;; various sets of rules to do "witnessing" transformations.  Taking set-based
;; reasoning as an example,  we might want to look at hypotheses of the form
;; (subsetp-equal a b) and conclude specific examples such as
;; (or (not (member-equal k a)) (member-equal k b)) for various k.  We might
;; also want to look at hypotheses of the form (not (subsetp-equal c d)) and
;; conclude (and (member-equal j c) (not (member-equal j d))) for some witness
;; j.

;; There are thus four steps to this transformation:
;; 1. Introduce witnesses for negative occurrences of universally-quantified
;; predicates and positive occurrences of existentially-quantified ones.
;; 2. Find the set of examples with which to instantiate positive
;; of universally-quantified and negative existentially-quantified predicates.
;; 3. Instantiate these predicates with these examples.
;; 4. (Not yet implemented.) Optionally, generalize newly introduced witness
;; terms into fresh variables, for readability.

;; The clause processor needs two types of information to accomplish this:
;; - what predicates are to be taken as universal/existential quantifiers and
;;   what they mean; i.e. how to introduce witnesses/instantiate.
;; - what examples to use when doing the instantiation.

;; The witness-introduction and instantiation may both be lossy.

;; To set up witnessing for not-subsetp-equal hypotheses:

;; (defwitness subsetp-equal-witnessing
;;   :predicate (not (subsetp-equal a b))
;;   :expr (and (member-equal (subsetp-equal-witness a b) a)
;;              (not (member-equal (subsetp-equal-witness a b) b)))
;;   :generalize (((subsetp-equal-witness a b) . ssew)
;;   :hint ('(:in-theory (e/d (subsetp-equal-witness-correct)
;;                            (subsetp-equal member-equal)))))

;; This means that in the witnessing phase, we search for hypotheses of the
;; form (not (subsetp-equal a b)) and for each such hypothesis, we add the
;; hypothesis
;; (let ((k (car (set-difference-equal a b))))
;;    (and (member-equal k a) (not (member-equal k b))))
;; incurring the proof obligation:
;; (implies (not (subsetp-equal a b))
;;          (let ((k (car (set-difference-equal a b))))
;;            (and (member-equal k a)
;;                 (not (member-equal k b))))).
;;

;; To set up instantiation of subsetp-equal hypotheses:

;; (definstantiate subsetp-equal-instance
;;   :predicate (subsetp-equal a b)
;;   :witness-var k
;;   :expr (implies (member-equal k a)
;;                  (member-equal k b)))

;; This will mean that for each  subsetp-equal hypothesis we find, we'll add
;; hypotheses of the form (implies (member-equal k a) (member-equal k b)) for
;; some set of k.  However, we need to collect a list of such k.  To define
;; examples, we use defexample:

;;  (defexample subsetp-equal-instance
;;   :expr (member-equal k a)
;;   :witness-var k)

;; This means that in phase 2, we'll look throughout the clause for expressions
;; (member-equal k a) and include k in the list of witnesses to use for
;; instantiating using the subsetp-equal-instance rule.

;; This will cause :witness expressions introduced by subset-equal-witness,
;; i.e. (car (set-difference-equal a b)), to be replaced by variable names
;; generated starting from the root SSWIT.

(local (in-theory (disable true-listp default-car default-cdr
                           alistp default-+-2 default-+-1
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;                            assoc
                           pseudo-termp pseudo-term-listp
                           pseudo-term-list-listp nth
                           intersectp-equal-non-cons
                           substitute-into-term
                           state-p-implies-and-forward-to-state-p1)))


(defevaluator witness-ev witness-ev-lst
  ((if a b c) (not a) (equal a b) (use-these-hints x)
   (implies a b) (hide x)))


(verify-termination
 (dumb-negate-lit
  (declare
   (xargs
    :guard-hints(("Goal" :in-theory (enable pseudo-termp)))))))

(defthm ev-dumb-negate-lit
  (implies (pseudo-termp lit)
           (iff (witness-ev (dumb-negate-lit lit) a)
                (not (witness-ev lit a))))
  :hints(("Goal" :in-theory (enable pseudo-termp))))

(defthm pseudo-termp-dumb-negate-lit
  (implies (pseudo-termp lit)
           (pseudo-termp (dumb-negate-lit lit)))
  :hints(("Goal" :in-theory (enable pseudo-termp
                                    pseudo-term-listp))))

(in-theory (disable dumb-negate-lit))

(def-ev-theoremp witness-ev :untranslate t)

(defun witness-ev-alist (x al)
  (if (atom x)
      nil
    (cons (cons (caar x) (witness-ev (cdar x) al))
          (witness-ev-alist (cdr x) al))))

(def-functional-instance
  simple-one-way-unify-usage-witness-ev
  simple-one-way-unify-usage
  ((unify-ev witness-ev)
   (unify-ev-lst witness-ev-lst)
   (unify-ev-alist witness-ev-alist))
  :hints((and stable-under-simplificationp
              '(:in-theory (enable witness-ev-constraint-0)))))

(def-functional-instance
  substitute-into-term-correct-witness-ev
  substitute-into-term-correct
  ((unify-ev witness-ev)
   (unify-ev-lst witness-ev-lst)
   (unify-ev-alist witness-ev-alist)))

(defun assert-msg (msg arg)
  (declare (xargs :guard t))
  (b* (((mv str alist) (if (atom msg)
                           (mv msg nil)
                         (mv (car msg) (cdr msg)))))
    (cons str (cons (cons #\t arg) alist))))


(defun asserts-macro (msg terms)
  (if (atom terms)
      t
    `(and (or ,(car terms)
              (cw "~@0~%" (assert-msg ,msg ',(car terms))))
          ,(asserts-macro msg (cdr terms)))))

(defmacro asserts (msg &rest terms)
  `(let ((msg ,msg))
     ,(asserts-macro 'msg terms)))


;;========================================================================
;; WITNESS-CP-EXPAND-WITNESSES
;;========================================================================
;; (phase 1)

(defun good-witness-rulesp (x)
  (declare (Xargs :guard t))
  (or (atom x)
      (and (b* ((rule (car x)))
             (asserts (msg "Failure in GOOD-WITNESS-RULESP: ~
                            The following rule does not satisfy ~xt: ~x0.~%" rule)
                      (true-listp rule)
                      (equal (len rule) 7)
                      (pseudo-termp (nth 2 rule))
                      (pseudo-termp (nth 3 rule))
                      (alistp (nth 6 rule))
                      (pseudo-term-listp (strip-cars (nth 6 rule)))
                      (symbol-listp (strip-cdrs (nth 6 rule)))))
           (good-witness-rulesp (cdr x)))))

(defun witness-generalize-alist (generalize-map alist)
  (declare (xargs :guard (and (alistp generalize-map)
                              (pseudo-term-listp
                               (strip-cars generalize-map))
                              (alistp alist))))
  (pairlis$ (substitute-into-list (strip-cars generalize-map) alist)
            (strip-cdrs generalize-map)))

(defthm alistp-witness-generalize-alist
  (alistp (witness-generalize-alist generalize-map alist))
  :hints(("Goal" :in-theory (enable alistp))))

(defthm symbol-listp-cdrs-witness-generalize-alist
  (implies (symbol-listp (strip-cdrs generalize-map))
           (symbol-listp
            (strip-cdrs (witness-generalize-alist generalize-map alist)))))

(in-theory (Disable witness-generalize-alist))

;; Lit is a member of the clause.  witness-rules is a list of tuples
;; conaining:
;; rulename: name of the witness rule
;; term: predicate term to match against
;; expr: expression implied by the predicate.
;; restriction: term in terms of the free vars of the predicate which
;;    will be evaluated with those variables bound to their matching
;;    terms; the witnessing will not be done if this evaluates to NIL
;; hint: hint to use to prove the resulting obligation.
;; generalize-exprs:  alist mapping subterms of EXPR to symbols; these
;;    will be generalized away to similar symbols.

;; Returns:
;; list of witnessing terms
;; alist (term . symbol) for generalization
;; list of proof obligations.

;; Example: lit is (subsetp-equal a b), i.e. hyp is
;; (not (subsetp-equal a b))
;; new hyp is:
;; (and (member-equal (car (set-difference-equal a b)) a)
;;      (not (member-equal (car (set-difference-equal a b)) b)))
;; therefore new-lits contains:
;; (not (and (member-equal (car (set-difference-equal a b)) a)
;;           (not (member-equal (car (set-difference-equal a b)) b))))
;; proof oblig is:
;; (implies (not (subsetp-equal a b))
;;          (and (member-equal (car (set-difference-equal a b)) a)
;;               (not (member-equal (car (set-difference-equal a b)) b))))

(defun match-lit-with-witnesses (lit witness-rules state)
  (declare (xargs :guard (and (pseudo-termp lit)
                              (good-witness-rulesp witness-rules))
                  :stobjs state))
  (b* (((when (atom witness-rules))
        (mv nil nil nil state))
       ((when (not (mbt (pseudo-termp lit))))
        (mv nil nil nil state))
       ((mv newlits genmap obligs state)
        (match-lit-with-witnesses lit (cdr witness-rules) state))
       ((nths ?rulename enabledp term expr restriction hint generalize)
        (car witness-rules))
       ((when (not enabledp))
        (mv newlits genmap obligs state))
       ((when (not (mbt (and (pseudo-termp term)
                             (pseudo-termp expr)))))
        (mv newlits genmap obligs state))
       ((mv unify-ok alist)
        (simple-one-way-unify term lit nil))
       ((when (not unify-ok))
        (mv newlits genmap obligs state))
       ((mv erp val state)
        (if (equal restriction ''t)
            (mv nil t state)
          (oracle-eval restriction alist state)))
       ((when erp)
        (if (equal erp *fake-oracle-eval-msg*)
            (cw "Note: Oracle-eval is not enabled, so witness rules with
restrictions are not used~%")
          (er hard? 'match-lit-with-witnesses
              "Evaluation of the restriction term, ~x0, produced an error: ~@1~%"
              restriction erp))
        (mv newlits genmap obligs state))
       ((when (not val))
        ;; Did not conform to restriction
        (mv newlits genmap obligs state))
       (genmap1 (witness-generalize-alist generalize alist))
       (new-lit (substitute-into-term expr alist))
       (oblig (list `(not (use-these-hints ',hint))
                    `(implies
                      ;; (not (subsetp-equal a b))
                      ,(dumb-negate-lit term)
                      ;; (and (member-equal ... a)
                      ;;      (not (member-equal ... b)))
                      ,(dumb-negate-lit expr)))))
    (mv (cons new-lit newlits)
        (append genmap1 genmap)
        (cons oblig obligs)
        state)))

(local (in-theory (Disable substitute-into-one-way-unify-reduce-list
                           substitute-into-one-way-unify-reduce)))

(defthm match-lit-with-witnesses-correct
  (implies (not (witness-ev lit a)) ;; (not (subsetp-equal a b))
           (mv-let (newlits rules obligs state)
             (match-lit-with-witnesses lit witness-rules state)
             (declare (ignore rules state))
             (implies (witness-ev-theoremp
                       (conjoin-clauses obligs))
                      ;; (not (or (not (and (member-equal ... a)
                      ;;                    (not (member-equal ... b))))))
                      (not (witness-ev (disjoin newlits) a)))))
  :hints (("goal" :induct (len witness-rules)
           :do-not-induct t
           :in-theory (e/d (use-these-hints)
                           (pseudo-termp assoc-equal substitute-into-term
                                         pseudo-term-listp
                                         simple-one-way-unify simple-term-vars
                                         nth)))
          (and stable-under-simplificationp
               '(:use ((:instance witness-ev-falsify
                                  (x (disjoin
                                      (car (mv-nth 2 (match-lit-with-witnesses
                                                      lit
                                                      witness-rules state)))))
                                  (a (witness-ev-alist
                                      (mv-nth 1 (simple-one-way-unify
                                                 (nth 2 (car witness-rules))
                                                 lit nil))
                                      a)))))))
  :otf-flg t)

(defthm pseudo-term-listp-match-lit-with-witnesses-0
  (pseudo-term-listp
   (mv-nth 0 (match-lit-with-witnesses lit witness-rules state)))
  :hints(("Goal" :in-theory (enable pseudo-term-listp pseudo-termp))))

(defthm pseudo-term-list-listp-match-lit-with-witnesses-2
  (pseudo-term-list-listp
   (mv-nth 2 (match-lit-with-witnesses lit witness-rules state)))
  :hints(("Goal" :in-theory (enable pseudo-term-list-listp
                                    pseudo-term-listp
                                    pseudo-termp))))

(defthm alistp-append
  (implies (and (alistp a) (alistp b))
           (alistp (append a b)))
  :hints(("Goal" :in-theory (enable alistp))))

(defthm alistp-match-lit-with-witnesses-1
  (alistp
   (mv-nth 1 (match-lit-with-witnesses lit witness-rules state))))

(defthm symbol-listp-of-append
  (implies (and (symbol-listp x)
                (symbol-listp y))
           (symbol-listp (append x y))))

(defthm strip-cdrs-of-append
  (equal (strip-cdrs (append a b))
         (append (strip-cdrs a) (strip-cdrs b))))

(defthm symbol-listp-cdrs-match-lit-with-witnesses-1
  (implies (good-witness-rulesp witness-rules)
           (symbol-listp
            (strip-cdrs
             (mv-nth 1 (match-lit-with-witnesses lit witness-rules state))))))

(defthm state-p1-match-lit-with-witnesses-3
  (implies
   (state-p1 state)
   (state-p1
    (mv-nth 3 (match-lit-with-witnesses lit witness-rules state)))))

(in-theory (disable match-lit-with-witnesses))

(defthmd pseudo-term-listp-true-listp
  (implies (pseudo-term-listp x)
           (true-listp x)))

(defthmd pseudo-term-list-listp-true-listp
  (implies (pseudo-term-list-listp x)
           (true-listp x))
  :hints(("Goal" :in-theory (enable pseudo-term-list-listp))))

(defthmd alistp-implies-true-listp
  (implies (alistp x) (true-listp x))
  :hints(("Goal" :in-theory (enable alistp))))


;; Transforms the clause by adding witnessing expressions and hiding the literals
;; that generated them. Returns (mv clause rule-witness-list obligs state).
(defun witness-cp-expand-witnesses (clause witness-rules state)
  (declare (xargs :guard (and (pseudo-term-listp clause)
                              (good-witness-rulesp witness-rules))
                  :verify-guards nil
                  :stobjs state))
  (b* (((when (atom clause))
        (mv nil nil nil state))
       ((mv rest genmap obligs state)
        (witness-cp-expand-witnesses (cdr clause) witness-rules state))
       (lit (car clause))
       ((when (not (mbt (pseudo-termp lit))))
        (mv (cons lit rest) genmap obligs state))
       ((mv new-lits genmap1 obligs1 state)
        (match-lit-with-witnesses lit witness-rules state))
       (clause (if new-lits
                   (cons `(not (hide ,(dumb-negate-lit lit)))
                         (append new-lits rest))
                 (mbe :logic (cons lit rest)
                      :exec (if (equal rest (cdr clause))
                                clause
                              (cons lit rest))))))
    (mv clause (append genmap1 genmap)
        (append obligs1 obligs)
        state)))

(verify-guards witness-cp-expand-witnesses
               :hints (("goal" :do-not-induct t
                        :in-theory (enable
                                    alistp-implies-true-listp
                                    pseudo-term-list-listp-true-listp
                                    pseudo-term-listp
                                    pseudo-term-listp-true-listp))))

(defthm witness-cp-expand-witnesses-correct
  (implies (not (witness-ev (disjoin clause) a))
           (mv-let (newclause rules obligs)
             (witness-cp-expand-witnesses clause witness-rules state)
             (declare (ignore rules))
             (implies (witness-ev-theoremp
                       (conjoin-clauses obligs))
                      ;; (not (or (not (and (member-equal ... a)
                      ;;                    (not (member-equal ... b))))))
                      (not (witness-ev (disjoin newclause) a)))))
  :hints (("goal" :induct (len clause)
           :do-not-induct t
           :in-theory (e/d ()
                           (pseudo-termp assoc-equal substitute-into-term
                                         pseudo-term-listp
                                         simple-one-way-unify simple-term-vars
                                         nth match-lit-with-witnesses))
           :expand ((:free (x) (hide x))))))

(defthm pseudo-term-list-listp-append
  (implies (and (pseudo-term-list-listp a)
                (pseudo-term-list-listp b))
           (pseudo-term-list-listp (append a b)))
  :hints(("Goal" :in-theory (enable pseudo-term-list-listp))))


(defthm pseudo-term-listp-append
  (implies (and (pseudo-term-listp a)
                (pseudo-term-listp b))
           (pseudo-term-listp (append a b)))
  :hints(("Goal" :in-theory (enable pseudo-term-listp))))

(defthm pseudo-term-listp-witness-cp-expand-witnesses-0
  (implies (pseudo-term-listp clause)
           (pseudo-term-listp
            (mv-nth 0 (witness-cp-expand-witnesses
                       clause witness-rules state))))
  :hints(("Goal" :in-theory (enable pseudo-term-listp
                                    pseudo-termp))))

(defthm pseudo-term-list-listp-witness-cp-expand-witnesses-2
  (implies (pseudo-term-listp clause)
           (pseudo-term-list-listp
            (mv-nth 2 (witness-cp-expand-witnesses
                       clause witness-rules state))))
  :hints(("Goal" :in-theory (enable pseudo-term-listp))))

(defthm alistp-witness-cp-expand-witnesses-1
  (alistp (mv-nth 1 (witness-cp-expand-witnesses
                     clause witness-rules state))))

(defthm symbol-listp-cdrs-witness-cp-expand-witnesses-1
  (implies (good-witness-rulesp witness-rules)
           (symbol-listp
            (strip-cdrs
             (mv-nth 1 (witness-cp-expand-witnesses
                        clause witness-rules state))))))

(defthm state-p1-witness-cp-expand-witnesses-3
  (implies (state-p1 state)
           (state-p1 (mv-nth 3 (witness-cp-expand-witnesses
                                clause witness-rules state)))))

(in-theory (disable witness-cp-expand-witnesses))





;;========================================================================
;; WITNESS-CP-EXPAND-INSTANCES
;;========================================================================
;; (phase 3)


(defun good-examplesp (len examples)
  (declare (Xargs :guard t))
  (or (atom examples)
      (and (pseudo-term-listp (car examples))
           (equal (len (car examples)) len)
           (good-examplesp len (Cdr examples)))))


(defthm alistp-pairlis$
  (alistp (pairlis$ a b))
  :hints(("Goal" :in-theory (enable alistp))))

(defun instantiate-examples (expr vars examples alist)
  (declare (xargs :guard (and (pseudo-termp expr)
                              (symbol-listp vars)
                              (good-examplesp (len vars) examples)
                              (alistp alist))))
  (if (atom examples)
      nil
    (if (mbt (pseudo-term-listp (car examples)))
        (cons (substitute-into-term
               expr
               (append (pairlis$ vars (car examples))
                       alist))
              (instantiate-examples expr vars (cdr examples) alist))
      (instantiate-examples expr vars (cdr examples) alist))))

(defthm pseudo-term-val-alistp-append
  (implies (and (pseudo-term-val-alistp a)
                (pseudo-term-val-alistp b))
           (pseudo-term-val-alistp (append a b))))

(defthm pseudo-term-listp-instantiate-examples
  (implies (and (pseudo-termp expr)
                (pseudo-term-val-alistp alist))
           (pseudo-term-listp (instantiate-examples expr var examples
                                                    alist)))
  :hints(("Goal" :in-theory (enable pseudo-term-listp))))

(defthm-simple-term-vars-flag
  witness-ev-remove-non-var-lemma
  (simple-term-vars
   (implies (and (pseudo-termp term)
                 (not (member-equal var (simple-term-vars term))))
            (equal (witness-ev term (cons (cons var val) a))
                   (witness-ev term a)))
   :name witness-ev-remove-non-var)
  (simple-term-vars-lst
   (implies (and (pseudo-term-listp term)
                 (not (member-equal var (simple-term-vars-lst term))))
            (equal (witness-ev-lst term (cons (cons var val) a))
                   (witness-ev-lst term a)))
   :name witness-ev-lst-remove-non-var)
  :hints (("goal" :induct (simple-term-vars-flag flag term)
           :in-theory (enable pseudo-termp pseudo-term-listp))
          (and stable-under-simplificationp
               '(:in-theory (enable witness-ev-constraint-0)))))

(defthm witness-ev-remove-non-vars
  (implies (and (pseudo-termp term)
                (not (intersectp-equal vars (simple-term-vars term))))
           (equal (witness-ev term (append (pairlis$ vars vals) a))
                  (witness-ev term a))))

(defchoose witness-ev-satisfy-vars (vals) (term vars al)
  (witness-ev term (append (pairlis$ vars vals) al)))

(defthm witness-ev-alist-append
  (equal (witness-ev-alist (append al1 al2) a)
         (append (witness-ev-alist al1 a)
                 (witness-ev-alist al2 a))))

(defthm witness-ev-alist-pairlis$
  (equal (witness-ev-alist (pairlis$ vars vals) a)
         (pairlis$ vars (witness-ev-lst vals a))))


(defthm instantiate-examples-correct
  (implies (and (pseudo-termp expr)
                (not (witness-ev expr
                                 (append (pairlis$ vars
                                                   (witness-ev-satisfy-vars
                                                    expr vars (witness-ev-alist
                                                               alist a)))
                                       (witness-ev-alist alist a)))))
           (not (witness-ev (disjoin (instantiate-examples expr vars examples
                                                           alist))
                            a)))
  :hints (("goal" :induct (len examples))
          (and stable-under-simplificationp
               '(:use ((:instance witness-ev-satisfy-vars
                                  (term expr)
                                  (vars vars)
                                  (vals (witness-ev-lst (car examples) a))
                                  (al (witness-ev-alist alist
                                                        a))))))))

(in-theory (disable instantiate-examples))

(defthm true-listp-union-equal
  (equal (true-listp (union-equal a b))
         (true-listp b))
  :hints(("Goal" :in-theory (enable true-listp))))

(defthm true-listp-simple-term-vars-lst
  (true-listp (simple-term-vars-lst x))
  :hints (("goal" :induct (len x)
           :expand ((simple-term-vars-lst x)))))

(defthm true-listp-simple-term-vars
  (true-listp (simple-term-vars x))
  :hints (("goal" :expand (simple-term-vars x))))

(verify-guards simple-term-vars)

(defun good-instance-rules-and-examplesp (instance-rules example-alist)
  (declare (xargs :guard (alistp example-alist)))
  (b* (((when (atom instance-rules)) t)
       (rule (car instance-rules))
       ((when (not (true-listp rule)))
        (cw "Not true-listp: ~x0~%" rule))
       ((when (not (equal (len rule) 7)))
        (cw "Wrong length: ~x0~%" rule))
       ((nths rulename ?enabledp pred vars expr ?restriction ?hint) rule)
       ((when (not (pseudo-termp pred)))
        (cw "Not pseudo-termp: ~x0~%" pred))
       ((when (not (pseudo-termp expr)))
        (cw "Not pseudo-termp: ~x0~%" expr))
       ((when (not (symbol-listp vars)))
        (cw "Not symbol-listp: ~x0~%" vars))
       ((when (not (symbolp rulename)))
        (cw "Not symbolp: ~x0~%" rulename))
       ((when (not ;; could be intersectp
               (not (intersectp-equal vars (simple-term-vars pred)))))
        (cw "Intersecting vars: ~x0 ~x1~%" vars pred))
       (look (assoc rulename example-alist))
;;        ((when (not look))
;;         (cw "No entry in example-alist: ~x0 ~x1~%" rulename example-alist))
       ((when (not (good-examplesp (len vars) (cdr look))))
        (cw "Bad examples for ~x1: ~x0~%" (cdr look) vars)))
    (good-instance-rules-and-examplesp (cdr instance-rules) example-alist)))


;; example-alist maps instance-rule name -> list of example expression-lists
;; instance rules: tuple of
;; - predicate term to match
;; - instance-rule name
;; - variables of example
;; - expression implied by predicate
;; - hint for proof oblig.

;; returns: (mv new-lits obligs)

(defun match-lit-with-instances (lit example-alist instance-rules state)
  (declare (xargs :guard (and (pseudo-termp lit)
                              (alistp example-alist)
                              (good-instance-rules-and-examplesp
                               instance-rules example-alist))
                  :stobjs state))
  (b* (((when (atom instance-rules))
        (mv nil nil state))
       ((when (not (mbt (pseudo-termp lit))))
        (mv nil nil state))
       ((mv newlits obligs state)
        (match-lit-with-instances
         lit example-alist (cdr instance-rules) state))
       ((nths rulename enabledp pred vars expr restriction hint)
        (car instance-rules))
       ((when (not enabledp))
        (mv newlits obligs state))
       ((when (not (mbt (and (pseudo-termp pred)
                             (pseudo-termp expr)
                             (not (intersectp-equal
                                   vars (simple-term-vars pred)))))))
        (er hard? 'match-lit-with-instances
            "Non pseudo-term: bad instantiate rule? ~x0~%"
            (car instance-rules))
        (mv newlits obligs state))
       ((mv unify-ok alist)
        (simple-one-way-unify pred lit nil))
       ((when (not unify-ok)) (mv newlits obligs state))
       ((mv erp val state)
        (if (equal restriction ''t)
            (mv nil t state)
          (oracle-eval restriction alist state)))
       ((when erp)
        (if (equal erp *fake-oracle-eval-msg*)
            (cw "Note: Oracle-eval is not enabled, so instantiations with
restrictions are not used~%")
          (er hard? 'match-lit-with-instances
              "Evaluation of the restriction term, ~x0, produced an error: ~@1~%"
              restriction erp))
        (mv newlits obligs state))
       ((when (not val))
        ;; Did not conform to restriction
        (mv newlits obligs state))
       (examples (cdr (assoc rulename example-alist)))
       (new-lits1 (instantiate-examples expr vars examples alist))
       (oblig (list `(not (use-these-hints ',hint))
                    `(implies ,(dumb-negate-lit pred)
                              ,(dumb-negate-lit expr)))))
    (mv (append new-lits1 newlits)
        (cons oblig obligs)
        state)))



(defthm match-lit-with-instances-correct
  (implies (not (witness-ev lit a))
           (mv-let (newlits obligs state)
             (match-lit-with-instances lit example-alist
                                       instance-rules state)
             (declare (ignore state))
             (implies (witness-ev-theoremp
                       (conjoin-clauses obligs))
                      (not (witness-ev (disjoin newlits) a)))))
  :hints (("goal" :induct (len instance-rules)
           :do-not-induct t
           :in-theory (e/d (use-these-hints)
                           (pseudo-termp assoc-equal substitute-into-term
                                         pseudo-term-listp
                                         simple-one-way-unify simple-term-vars
                                         nth)))
          (and stable-under-simplificationp
               '(:use ((:instance witness-ev-falsify
                                  (x (disjoin
                                      (car (mv-nth 1 (match-lit-with-instances
                                                      lit example-alist
                                                      instance-rules state)))))
                                  (a (append
                                      (pairlis$ (nth 3 (car instance-rules))
                                                (witness-ev-satisfy-vars
                                                 (nth 4 (car instance-rules))
                                                 (nth 3 (car instance-rules))
                                                 (witness-ev-alist
                                                  (mv-nth 1 (simple-one-way-unify
                                                             (nth 2 (car instance-rules))
                                                             lit nil))
                                                  a)))
                                      (witness-ev-alist
                                       (mv-nth 1 (simple-one-way-unify
                                                  (nth 2 (car instance-rules))
                                                  lit nil))
                                       a))))))))
  :otf-flg t)


(defthm pseudo-term-listp-match-lit-with-instances-0
  (pseudo-term-listp
   (mv-nth 0 (match-lit-with-instances lit example-alist
                                       instance-rules state))))

(defthm pseudo-term-list-listp-match-lit-with-instances-1
  (pseudo-term-list-listp
   (mv-nth 1 (match-lit-with-instances lit example-alist
                                       instance-rules state)))
  :hints(("Goal" :in-theory (enable pseudo-term-list-listp
                                    pseudo-term-listp
                                    pseudo-termp))))

(defthm state-p1-match-lit-with-instances-2
  (implies (state-p1 state)
           (state-p1
            (mv-nth 2 (match-lit-with-instances
                       lit example-alist instance-rules state))))
  :hints(("Goal" :in-theory (e/d ()
                                 (state-p-implies-and-forward-to-state-p1
                                  pseudo-termp state-p1
                                  (:type-prescription state-p1))))))

(in-theory (disable match-lit-with-instances))




;; Returns (new-clause obligs).
(defun witness-cp-expand-instances
  (clause example-alist instance-rules state)
  (declare (xargs :guard (and (pseudo-term-listp clause)
                              (alistp example-alist)
                              (good-instance-rules-and-examplesp
                               instance-rules example-alist))
                  :verify-guards nil
                  :stobjs state))
  (b* (((when (atom clause))
        (mv nil nil state))
       ((mv rest obligs state)
        (witness-cp-expand-instances
         (cdr clause) example-alist instance-rules state))
       (lit (car clause))
       ((when (not (mbt (pseudo-termp lit))))
        (mv (cons lit rest) obligs state))
       ((mv new-lits obligs1 state)
        (match-lit-with-instances lit example-alist instance-rules
                                  state))
       (clause (if new-lits
                   (cons `(not (hide ,(dumb-negate-lit lit)))
                         (append new-lits rest))
                 (mbe :logic (cons lit rest)
                      :exec (if (equal rest (cdr clause))
                                clause
                              (cons lit rest))))))
    (mv clause (append obligs1 obligs) state)))

(verify-guards witness-cp-expand-instances
               :hints (("goal" :in-theory
                        (enable pseudo-term-list-listp-true-listp
                                pseudo-term-listp
                                pseudo-term-listp-true-listp)
                        :do-not-induct t)))


(defthm witness-cp-expand-instances-correct
  (implies (not (witness-ev (disjoin clause) a))
           (mv-let (new-clause obligs)
             (witness-cp-expand-instances
              clause example-alist instance-rules state)
             (implies (witness-ev-theoremp
                       (conjoin-clauses obligs))
                      (not (witness-ev (disjoin new-clause) a)))))
  :hints (("goal" :induct (len clause)
           :do-not-induct t
           :in-theory (e/d ()
                           (pseudo-termp assoc-equal substitute-into-term
                                         pseudo-term-listp
                                         simple-one-way-unify simple-term-vars
                                         nth))
           :expand ((:free (x) (hide x))))))


(defthm pseudo-term-listp-witness-cp-expand-instances-0
  (implies (pseudo-term-listp clause)
           (pseudo-term-listp
            (mv-nth 0 (witness-cp-expand-instances
                       clause example-alist instance-rules state))))
  :hints(("Goal" :in-theory (enable pseudo-term-listp
                                    pseudo-termp))))



(defthm pseudo-term-list-listp-witness-cp-expand-instances-2
  (implies (pseudo-term-listp clause)
           (pseudo-term-list-listp
            (mv-nth 1 (witness-cp-expand-instances
                       clause example-alist instance-rules state))))
  :hints(("Goal" :in-theory (enable pseudo-term-listp))))

(defthm state-p1-witness-cp-expand-instances-2
  (implies (state-p1 state)
           (state-p1
            (mv-nth 2 (witness-cp-expand-instances
                       clause example-alist instance-rules state)))))





;;========================================================================
;; WITNESS-CP-COLLECT-EXAMPLES
;;========================================================================
;; (phase 2)


;; (defun extract-from-alist (keys al)
;;   (declare (xargs :guard (and (alistp al)
;;                               (symbol-listp keys))))
;;   (if (atom keys)
;;       nil
;;     (cons (cdr (assoc (car keys) al))
;;           (extract-from-alist (cdr keys) al))))



;; Example templates are of the form
;; (term example instance-rulename)
;; where term is the term to match,
;; example is a list of terms using the same variables as terms,
;; and instance-rulename is the name of the associated instance-rule.

(defun good-templatesp (templates)
  (declare (xargs :guard t))
  (or (atom templates)
      (let ((rule (car templates)))
        (and (asserts
              (msg "Failure in GOOD-TEMPLATESP: ~
                  The following rule does not satisfy ~xt: ~x0.~%" rule)
              (true-listp rule)
              (equal (len rule) 6)
              (pseudo-termp (nth 2 rule))
              (pseudo-term-listp (nth 3 rule))
              (symbolp (nth 4 rule)))
             (good-templatesp (cdr templates))))))

(defun pseudo-term-list-list-alistp (x)
  (declare (xargs :guard t))
  (or (atom x)
      (and (consp (car x))
           (pseudo-term-list-listp (cdar x))
           (pseudo-term-list-list-alistp (cdr x)))))

(defthm pseudo-term-list-list-alistp-assoc
  (implies (pseudo-term-list-list-alistp x)
           (pseudo-term-list-listp (cdr (assoc k x))))
  :hints(("Goal" :in-theory (enable assoc))))

(defthm pseudo-term-val-alistp-assoc
  (implies (pseudo-term-val-alistp x)
           (pseudo-termp (cdr (assoc k x))))
  :hints(("Goal" :in-theory (enable assoc))))

;; (defthm pseudo-term-listp-extract-from-alist
;;   (implies (pseudo-term-val-alistp alist)
;;            (pseudo-term-listp (extract-from-alist vars alist))))

(defun examples-for-term (term templates acc state)
  (declare (xargs :guard (and (pseudo-termp term)
                              (good-templatesp templates)
                              (alistp acc)
                              (pseudo-term-list-list-alistp acc))
                  :verify-guards nil
                  :stobjs state))
  (b* (((when (atom templates)) (mv acc state))
       ((nths ?exname enabledp pat templ rulename restriction) (car templates))
       ((when (not enabledp))
        (examples-for-term term (cdr templates) acc state))
       ((mv unify-ok alist) (simple-one-way-unify pat term nil))
       ((when (not unify-ok))
        (examples-for-term term (cdr templates) acc state))
       ((mv erp val state)
        (if (equal restriction ''t)
            (mv nil t state)
          (oracle-eval restriction alist state)))
       ((when erp)
        (if (equal erp *fake-oracle-eval-msg*)
            (cw "Note: Oracle-eval is not enabled, so examples with
restrictions are not used~%")
          (er hard? 'examples-for-term
              "Evaluation of the restriction term, ~x0, produced an error: ~@1~%"
              restriction erp))
        (examples-for-term term (cdr templates) acc state))
       ((when (not val))
        ;; Restriction not met
        (examples-for-term term (cdr templates) acc state))
       (example (substitute-into-list templ alist))
       (other-examples (cdr (assoc rulename acc)))
       ((when (member-equal example other-examples))
        (examples-for-term term (cdr templates) acc state)))
    (examples-for-term term (cdr templates)
                       (cons (cons rulename
                                   (cons example other-examples))
                             acc)
                       state)))

(verify-guards examples-for-term
               :hints(("Goal" :in-theory (enable
                                          pseudo-term-list-listp
                                          pseudo-term-list-listp-true-listp
                                          alistp)
                       :do-not-induct t)))

(defthm pseudo-term-list-list-alistp-examples-for-term
  (implies (and (pseudo-termp term)
                (good-templatesp templates)
                (pseudo-term-list-list-alistp acc))
           (pseudo-term-list-list-alistp
            (mv-nth 0 (examples-for-term term templates acc state))))
  :hints(("Goal" :in-theory (enable pseudo-term-list-listp))))

(defthm alistp-examples-for-term
  (implies (alistp acc)
           (alistp
            (mv-nth 0 (examples-for-term term templates acc state))))
  :hints(("Goal" :in-theory (enable alistp))))

(defthm state-p1-examples-for-term
  (implies (state-p1 state)
           (state-p1
            (mv-nth 1 (examples-for-term term templates acc state)))))

(in-theory (disable examples-for-term))

(mutual-recursion
 (defun beta-reduce-term (x)
   (declare (Xargs :guard (pseudo-termp x)
                   :verify-guards nil))
   (b* (((when (or (atom x) (eq (car X) 'quote))) x)
        (f (car x))
        (args (beta-reduce-list (cdr x)))
        ((when (atom f)) (cons f args))
        (vars (cadr f))
        (body (beta-reduce-term (caddr f))))
     (substitute-into-term body (pairlis$ vars args))))
 (defun beta-reduce-list (x)
   (declare (xargs :guard (pseudo-term-listp x)))
   (if (atom x)
       nil
     (cons (beta-reduce-term (car x))
           (beta-reduce-list (cdr x))))))

(flag::make-flag beta-reduce-flag beta-reduce-term)

(defthm-beta-reduce-flag
  pseudo-termp-beta-reduce-flag
  (beta-reduce-term
   (implies (pseudo-termp x)
            (pseudo-termp (beta-reduce-term x)))
   :name pseudo-termp-beta-reduce-term)
  (beta-reduce-list
   (implies (pseudo-term-listp x)
            (pseudo-term-listp (beta-reduce-list x)))
   :name pseudo-termp-beta-reduce-list)
  :hints (("goal" :induct (beta-reduce-flag flag x)
           :in-theory (enable pseudo-termp pseudo-term-listp))))

(verify-guards beta-reduce-term
               :hints (("goal" :in-theory (enable pseudo-termp
                                                  pseudo-term-listp))))

(mutual-recursion
 (defun witness-cp-collect-examples-term (x templates acc state)
   (declare (xargs :guard (and (pseudo-termp x)
                               (good-templatesp templates)
                               (alistp acc)
                               (pseudo-term-list-list-alistp acc))
                   :verify-guards nil
                   :stobjs state))
   (b* (((when (atom x)) (mv acc state))
        ((when (eq (car x) 'quote)) (mv acc state))
        ((mv acc state)
         (witness-cp-collect-examples-list (cdr x) templates acc state))
        ;; no lambdas -- beta reduced
        )
     (examples-for-term x templates acc state)))

 (defun witness-cp-collect-examples-list (x templates acc state)
   (declare (xargs :guard (and (pseudo-term-listp x)
                               (good-templatesp templates)
                               (alistp acc)
                               (pseudo-term-list-list-alistp acc))
                   :stobjs state))
   (b* (((when (atom x)) (mv acc state))
        ((mv acc state)
         (witness-cp-collect-examples-list
          (cdr x) templates acc state)))
     (witness-cp-collect-examples-term
      (car x) templates acc state))))

(set-state-ok t)

(flag::make-flag witness-cp-collect-examples-flag
                 witness-cp-collect-examples-term)

(defthm-witness-cp-collect-examples-flag
  alistp-witness-cp-collect-examples
  (witness-cp-collect-examples-term
   (implies (alistp acc)
            (alistp (mv-nth 0 (witness-cp-collect-examples-term
                               x templates acc state))))
   :name alistp-witness-cp-collect-examples-term)
  (witness-cp-collect-examples-list
   (implies (alistp acc)
            (alistp (mv-nth 0 (witness-cp-collect-examples-list
                               x templates acc state))))
   :name alistp-witness-cp-collect-examples-list)
  :hints (("goal" :induct (witness-cp-collect-examples-flag
                           flag x templates acc state))))

(defthm-witness-cp-collect-examples-flag
  pseudo-term-list-list-alistp-witness-cp-collect-examples
  (witness-cp-collect-examples-term
   (implies (and (pseudo-termp x)
                 (good-templatesp templates)
                 (pseudo-term-list-list-alistp acc))
            (pseudo-term-list-list-alistp
             (mv-nth 0 (witness-cp-collect-examples-term
                        x templates acc state))))
   :name pseudo-term-list-list-alistp-witness-cp-collect-examples-term)
  (witness-cp-collect-examples-list
   (implies (and (pseudo-term-listp x)
                 (good-templatesp templates)
                 (pseudo-term-list-list-alistp acc))
            (pseudo-term-list-list-alistp
             (mv-nth 0 (witness-cp-collect-examples-list
                        x templates acc state))))
   :name pseudo-term-list-list-alistp-witness-cp-collect-examples-list)
  :hints (("goal" :induct (witness-cp-collect-examples-flag
                           flag x templates acc state)
           :in-theory (enable pseudo-term-listp
                              pseudo-termp))))

(verify-guards witness-cp-collect-examples-term
               :hints(("Goal" :in-theory (enable pseudo-term-listp
                                                 pseudo-termp)
                       :expand ((pseudo-termp x)))))

(defthm-witness-cp-collect-examples-flag
  state-p1-witness-cp-collect-examples-lemma
  (witness-cp-collect-examples-term
   (implies (state-p1 state)
            (state-p1
             (mv-nth 1 (witness-cp-collect-examples-term
                        x templates acc state))))
   :name state-p1-witness-cp-collect-examples-term)
  (witness-cp-collect-examples-list
   (implies (state-p1 state)
            (state-p1
             (mv-nth 1 (witness-cp-collect-examples-list
                        x templates acc state))))
   :name state-p1-witness-cp-collect-examples-list)
  :hints (("goal" :induct (witness-cp-collect-examples-flag
                           flag x templates acc state))))




;;========================================================================
;; WITNESS-CP-GENERALIZE
;;========================================================================
;; (step 4)

(defun witness-ev-replace-alist-to-bindings (alist bindings)
  (if (atom alist)
      nil
    (cons (cons (cdar alist) (witness-ev (caar alist) bindings))
          (witness-ev-replace-alist-to-bindings (cdr alist) bindings))))

(def-functional-instance
  witness-ev-disjoin-replace-subterms-list
  disjoin-replace-subterms-list
  ((replace-alist-to-bindings witness-ev-replace-alist-to-bindings)
   (gen-eval witness-ev)
   (gen-eval-lst witness-ev-lst))
  :hints((and stable-under-simplificationp
              '(:in-theory (enable witness-ev-constraint-0)))))


(defun make-non-dup-vars (x avoid)
  (declare (xargs :guard (and (symbol-listp x)
                              (true-listp avoid))))
  (if (atom x)
      nil
    (let ((newvar (make-n-vars 1 (if (mbt (symbolp (car x)))
                                     (car x)
                                   'x) 0 avoid)))
      (append newvar
              (make-non-dup-vars (cdr x) (append newvar avoid))))))



(defthm symbol-listp-make-non-dup-vars
  (symbol-listp (make-non-dup-vars x avoid)))

(defthm member-equal-of-append
  (iff (member-equal x (append a b))
       (or (member-equal x a)
           (member-equal x b))))

(defthm make-non-dup-vars-not-nil
  (not (member-equal nil (make-non-dup-vars x avoid))))

(defthm len-append
  (equal (len (append a b))
         (+ (len a) (len b))))

(defthm len-make-non-dup-vars
  (equal (len (make-non-dup-vars x avoid))
         (len x)))

(defthm no-intersect-make-non-dup-vars
  (not (intersectp-equal avoid (make-non-dup-vars x avoid)))
  :hints (("goal" :induct (make-non-dup-vars x avoid))
          (and stable-under-simplificationp
               '(:use ((:instance make-n-vars-not-in-avoid
                                  (n 1)
                                  (base (if (symbolp (car x)) (car x) 'x)) (m 0)
                                  (avoid-lst avoid)))
                      :in-theory (disable
                                  make-n-vars-not-in-avoid)))))

(defthm no-duplicates-make-non-dup-vars
  (no-duplicatesp-equal (make-non-dup-vars x avoid))
  :hints (("goal" :induct t)
          (and stable-under-simplificationp
               '(:use
                 ((:instance no-intersect-make-non-dup-vars
                             (x (cdr x))
                             (avoid (append
                                     (make-n-vars
                                      1 (if (symbolp (car x)) (car x)
                                          'x)
                                      0 avoid)
                                     avoid))))
                 :in-theory (disable
                             no-intersect-make-non-dup-vars)))))

(defun fix-generalize-alist (alist used-vars)
  (declare (xargs :guard (and (alistp alist)
                              (symbol-listp (strip-cdrs alist))
                              (true-listp used-vars))))
  (pairlis$ (strip-cars alist)
            (make-non-dup-vars (strip-cdrs alist) used-vars)))

(local
 (defthm strip-cdrs-pairlis$
   (implies (and (equal (len a) (len b))
                 (true-listp b))
            (equal (strip-cdrs (pairlis$ a b)) b))))

(defthm len-strip-cars
  (equal (len (strip-cars x)) (len x)))

(defthm len-strip-cdrs
  (equal (len (strip-cdrs x)) (len x)))

(defthm fix-generalize-alist-lemmas
  (let ((genalist (fix-generalize-alist alist used-vars)))
    (and (not (intersectp-equal used-vars
                                (strip-cdrs genalist)))
         (symbol-listp (strip-cdrs genalist))
         (not (member-equal nil (strip-cdrs genalist)))
         (no-duplicatesp-equal (strip-cdrs genalist)))))


(defun witness-cp-generalize-clause (genalist clause)
  (declare (xargs :guard (and (alistp genalist)
                              (symbol-listp (strip-cdrs genalist))
                              (pseudo-term-listp clause))))
  (replace-subterms-list
   clause (fix-generalize-alist genalist
                                (term-vars-list clause))))



(defthm witness-cp-generalize-clause-correct
  (implies (and (not (witness-ev-theoremp
                      (disjoin clause)))
                (pseudo-term-listp clause))
           (not (witness-ev-theoremp
                 (disjoin (witness-cp-generalize-clause
                           genalist clause)))))
  :hints (("goal" :in-theory (e/d ()
                                  (replace-subterms-list
                                   fix-generalize-alist
                                   term-vars-list))
           :use ((:instance witness-ev-falsify
                            (x (disjoin
                                (witness-cp-generalize-clause
                                 genalist clause)))
                            (a (append
                                (witness-ev-replace-alist-to-bindings
                                 (fix-generalize-alist
                                  genalist (term-vars-list clause))
                                 (witness-ev-falsify (disjoin clause)))
                                (witness-ev-falsify (disjoin clause)))))))))

(in-theory (disable witness-cp-generalize-clause))



;;========================================================================
;; WITNESS-CP
;;========================================================================
;; (top level)


(defun witness-cp (clause hints state)
  (declare (xargs :guard (pseudo-term-listp clause)
                  :stobjs state
                  :verify-guards nil))
  (b* (((when (not (and (true-listp hints)
                        (equal (len hints) 4))))
        (er hard? 'witness-cp "Bad hints: wrong format~%")
        (value (list clause)))
       ((nths generalizep
              witness-rules example-templates instance-rules) hints)
       ((when (not (good-witness-rulesp witness-rules)))
        (er hard? 'witness-cp "Bad hints: bad witness-rules~%")
        (value (list clause)))
       ((when (not (good-templatesp example-templates)))
        (er hard? 'witness-cp "Bad hints: bad example-templates~%")
        (value (list clause)))
       ((mv witnessed-clause generalize-alist witness-obligs state)
        (witness-cp-expand-witnesses clause witness-rules state))
       ((mv example-alist state)
        (witness-cp-collect-examples-list
         (beta-reduce-list witnessed-clause)
         example-templates nil state))
       ((when (not (good-instance-rules-and-examplesp
                    instance-rules example-alist)))
        (er hard? 'witness-cp
            "Bad hints: bad instance rules or generated bad example~%")
        (value (list clause)))
       ((mv instanced-clause instance-obligs state)
        (witness-cp-expand-instances
         witnessed-clause example-alist instance-rules state))
       (generalized-clause
        (if generalizep
            (witness-cp-generalize-clause
             generalize-alist instanced-clause)
          instanced-clause)))
    (value
     (cons generalized-clause
           (remove-duplicates-equal
            (append instance-obligs witness-obligs))))))

(verify-guards witness-cp
               :hints (("goal" :in-theory
                        (enable pseudo-term-list-listp-true-listp))))




(defthm conjoin-clauses-remove-duplicates-equal
  (iff (witness-ev-theoremp
        (conjoin-clauses (remove-duplicates-equal clauses)))
       (witness-ev-theoremp
        (conjoin-clauses clauses))))

(defthm witness-cp-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (witness-ev-theoremp
                 (conjoin-clauses
                  (clauses-result
                   (witness-cp clause hints state)))))
           (witness-ev (disjoin clause) a))
  :hints(("Goal" :in-theory
          (e/d () (good-instance-rules-and-examplesp
                   good-witness-rulesp good-templatesp
                   witness-cp-expand-witnesses
                   witness-cp-collect-examples-list
                   witness-cp-expand-instances))
          :use ((:instance witness-ev-falsify
                           (x (disjoin clause))
                           (a a))
                (:instance witness-ev-falsify
                           (x (disjoin
                               (car (mv-nth 1 (witness-cp
                                               clause
                                               (update-nth 0 nil
                                                           hints)
                                               state)))))
                           (a a)))
          :do-not-induct t))
  :otf-flg t
  :rule-classes :clause-processor)


#||


;; Replicate some of the proofs in equal-sets.lisp using witness-cp instead of
;; the (set-reasoning) hint.

(include-book
 "equal-sets")

(set-inhibit-warnings "theory")

(defconst *witness-set-cp-hints*
  '( ;; witness-rules: (pat rulename witness expr hint)
    ((subsetp-equal-witnessing
      (subsetp-equal x y)
      (subsetp-equal-witness x y)
      (implies (member-equal (subsetp-equal-witness
                              x y) x)
               (member-equal (subsetp-equal-witness
                              x y) y))
      ('(:in-theory (e/d
                     (subsetp-equal-witness-correct)
                     (subsetp-equal
                      member-equal)))))
     (intersectp-equal-witnessing
      (not (intersectp-equal x y))
      (intersectp-equal-witness x y)
      (not (if (member-equal (intersectp-equal-witness
                              x y) x)
               (member-equal (intersectp-equal-witness
                              x y) y)
             'nil))
      ('(:in-theory (e/d
                     (intersectp-equal-witness-correct)
                     (intersectp-equal
                      member-equal)))))
     (consp-witnessing
      (not (consp x))
      (car x)
      (not (member-equal (car x) x))
      ('(:in-theory (enable member-equal)))))
    ;; example templates: (pat vars rulename)
    (((member-equal k y)
      (k)
      intersectp-equal-instancing)
     ((member-equal k y)
      (k)
      subsetp-equal-instancing)
     ((member-equal k y)
      (k)
      consp-instancing))
; instance-rules: (pat rulename vars expr hint)
    ((subsetp-equal-instancing
      (not (subsetp-equal x y))
      (k)
      (not (implies (member-equal k x)
                    (member-equal k y)))
      ('(:in-theory (e/d (subsetp-equal-member)
                         (subsetp-equal
                          member-equal)))))
     (intersectp-equal-instancing
      (intersectp-equal x y)
      (k)
      (if (member-equal k x)
          (member-equal k y)
        'nil)
      ('(:in-theory (e/d (intersectp-equal-member)
                         (intersectp-equal
                          member-equal)))))
     (consp-instancing
      (consp x)
      (k)
      (member-equal k x)
      ('(:in-theory (enable member-equal)))))))

(defthm intersectp-equal-iff-intersection-equal2
  (iff (consp (intersection-equal x y))
       (intersectp-equal x y))
  :hints (("Goal" :do-not-induct t)
          (and stable-under-simplificationp
               '(:computed-hint-replacement
                 ((use-these-hints-hint clause))
                 :clause-processor
                 (witness-cp clause
                             *witness-set-cp-hints*))))
  :otf-flg t
  :rule-classes nil)

(defthm intersectp-of-superset-2
  (implies (and (intersectp-equal a b)
                (subsetp-equal a c))
           (intersectp-equal c b))
  :hints (("Goal" :do-not-induct t)
          (and stable-under-simplificationp
               '(:computed-hint-replacement
                 ((use-these-hints-hint clause))
                 :clause-processor
                 (witness-cp clause
                             *witness-set-cp-hints*))))
  :otf-flg t
  :rule-classes nil)

(defthm intersectp-of-superset2-2
  (implies (and (subsetp-equal a c)
                (intersectp-equal b a))
           (intersectp-equal b c))
  :hints (("Goal" :do-not-induct t)
          (and stable-under-simplificationp
               '(:computed-hint-replacement
                 ((use-these-hints-hint clause))
                 :clause-processor
                 (witness-cp clause
                             *witness-set-cp-hints*))))
  :otf-flg t
  :rule-classes nil)

(defthm subsetp-equal-cons-same-2
  (implies (subsetp-equal a b)
           (subsetp-equal (cons x a) (cons x b)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable subsetp-equal-cons-same))
          (and stable-under-simplificationp
               '(:computed-hint-replacement
                 ((use-these-hints-hint clause))
                 :clause-processor
                 (witness-cp clause
                             *witness-set-cp-hints*))))
  :otf-flg t
  :rule-classes nil)




||#


;; Keep the various kinds of rules in a table.
;; Witness rules:     witness-cp-witness-rules
;; Example templates: witness-cp-example-templates
;; Instance rules:    witness-cp-instance-rules.

;; Another table, witness-cp-rulesets, will be used to store subsets
;; of these rules.

(defun run-test-with-hint-replacement (term hints ctx state)
  (declare (xargs :mode :program))
  (b* (((er hint)
        (translate-hints+ 'thm '((use-these-hints-hint clause))
                          nil 'ctx (w state) state))
       (clauses `(((not (use-these-hints ',hints))
                   ,term)))
       (pspv (make-pspv (ens state) (w state) :orig-hints hint)))
    (prove-loop clauses pspv hint (ens state) (w state) ctx state)))


(defun wcp-translate-lst (lst state)
  (declare (xargs :mode :program))
  (if (atom lst)
      (value nil)
    (b* (((er rest) (wcp-translate-lst (cdr lst) state))
         ((er first)
          (translate (car lst) t t nil 'defexample (w state) state)))
      (value (cons first rest)))))

(defun defwitness-fn (name predicate expr restriction generalize hints
                           state)
  (declare (xargs :mode :program))
  (b* (((when (not predicate))
        (mv "DEFWITNESS: Must supply a :PREDICATE.~%" nil state))
       ((when (not expr))
        (mv "DEFWITNESS: Must supply an :EXPR.~%" nil state))
       ((er predicate)
        (translate predicate t t nil 'defwitness (w state) state))
       ((er expr)
        (translate expr t t nil 'defwitness (w state) state))
       ((er generalize-terms)
        (wcp-translate-lst (strip-cars generalize) state))
       (generalize (pairlis$ generalize-terms (strip-cdrs generalize)))
       ((er &) (run-test-with-hint-replacement
                `(implies ,predicate ,expr)
                hints 'defwitness state))
       ;;                         `((prog2$ (cw "clause: ~x0~%" clause)
       ;;                                   '(:computed-hint-replacement
       ;;                                     :do-not '(preprocess simplify)))) nil nil))
       )
    (value
     `(table witness-cp-witness-rules
             ',name ',(list t
                            (dumb-negate-lit predicate)
                            (dumb-negate-lit expr)
                            restriction hints generalize)))))


(defmacro defwitness (name &key predicate expr
                           (restriction ''t)
                           generalize hints)
  `(make-event (defwitness-fn ',name ',predicate ',expr ',restriction
                 ',generalize ',hints state)))




(defun definstantiate-fn (name predicate vars expr restriction hints
                               state)
  (declare (xargs :mode :program))
  (b* (((when (not predicate))
        (mv "DEFINSTANTIATE: Must supply a :PREDICATE.~%" nil state))
       ((when (not vars))
        (mv "DEFINSTANTIATE: Must supply :VARS.~%" nil state))
       ((when (not expr))
        (mv "DEFINSTANTIATE: Must supply an :EXPR.~%" nil state))
       ((er predicate)
        (translate predicate t t nil 'definstantiate (w state) state))
       ((er expr)
        (translate expr t t nil 'definstantiate (w state) state))
       ((er &) (run-test-with-hint-replacement
                `(implies ,predicate ,expr)
                hints 'definstantiate state)))
    (value
     `(table witness-cp-instance-rules
             ',name ',(list t
                            (dumb-negate-lit predicate)
                            vars
                            (dumb-negate-lit expr)
                            restriction hints)))))

(defmacro definstantiate (name &key predicate vars expr
                               (restriction ''t) hints)
  `(make-event (definstantiate-fn
                 ',name ',predicate ',vars ',expr ',restriction
                 ',hints state)))



(defun defexample-fn (name pattern templates instancename restriction
                           state)
  (declare (Xargs :mode :program))
  (b* (((when (not pattern))
        (mv "DEFEXAMPLE: Must supply a :PATTERN.~%" nil state))
       ((when (not templates))
        (mv "DEFEXAMPLE: Must supply :TEMPLATES.~%" nil state))
       ((when (not instancename))
        (mv "DEFEXAMPLE: Must supply an :INSTANCE-RULENAME.~%" nil state))
       ((er pattern)
        (translate pattern t t nil 'defexample (w state) state))
       ((er templates)
        (wcp-translate-lst templates state)))
    (value
     `(table witness-cp-example-templates
             ',name ',(list t pattern templates instancename restriction)))))

(defmacro defexample (name &key pattern templates instance-rulename
                           (restriction ''t))
  `(make-event
    (defexample-fn ',name ',pattern ',templates ',instance-rulename
      ',restriction state)))



(defun look-up-witness-rules (rules table)
  (if (atom rules)
      (mv nil nil)
    (b* (((mv rest missing) (look-up-witness-rules (cdr rules) table))
         (look (assoc (car rules) table)))
      (if look
          (mv (cons look rest) missing)
        (mv rest (cons (car rules) missing))))))


;; (defun def-witness-ruleset-fn (name witness-names instance-names
;;                                     example-names state)
;;   (b* (((mv witness-rules missing)
;;         (look-up-witness-rules
;;          witness-names
;;          (table-alist 'witness-cp-witness-rules (w state))))
;;        ((when missing)
;;         (mv (msg "DEF-WITNESS-RULESET: Witness ~s0 not found: ~x1~%"
;;                  (if (consp (cdr missing)) "rules" "rule")
;;                  missing)
;;             nil state))
;;        ((mv instance-rules missing)
;;         (look-up-witness-rules
;;          instance-names
;;          (table-alist 'witness-cp-instance-rules (w state))))
;;        ((when missing)
;;         (mv (msg "DEF-WITNESS-RULESET: Instance ~s0 not found: ~x1~%"
;;                  (if (consp (cdr missing)) "rules" "rule")
;;                  missing)
;;             nil state))
;;        ((mv example-templates missing)
;;         (look-up-witness-rules
;;          example-names
;;          (table-alist 'witness-cp-example-templates (w state))))
;;        ((when missing)
;;         (mv (msg "DEF-WITNESS-RULESET: Example ~s0 not found: ~x1~%"
;;                  (if (consp (cdr missing)) "templates" "template")
;;                  missing)
;;             nil state)))
;;     (value `(table witness-cp-rulesets ',name
;;                    ',(list witness-rules
;;                            example-templates
;;                            instance-rules)))))

(defmacro def-witness-ruleset (name rules)
  `(table witness-cp-rulesets ',name ,rules))

(defun defquant-witness-binding1 (n qvars witness-expr)
  (if (atom qvars)
      nil
    (cons `(,(car qvars) (mv-nth ,n ,witness-expr))
          (defquant-witness-binding1 (1+ n) (cdr qvars) witness-expr))))

(defun defquant-witness-binding (qvars witness-expr body)
  (if (eql (len qvars) 1)
      `(let ((,(car qvars) ,witness-expr)) ,body)
    `(let ,(defquant-witness-binding1 0 qvars witness-expr)
       ,body)))

(defun defquant-generalize-alist1 (n qvars witness-expr generalize-vars)
  (if (atom qvars)
      nil
    (cons `((mv-nth ,n ,witness-expr)
            . ,(or (car generalize-vars) (car qvars)))
          (defquant-generalize-alist1 (1+ n) (cdr qvars)
            witness-expr (cdr generalize-vars)))))


(defun defquant-generalize-alist (qvars witness-expr generalize-vars)
  (if (eql (len qvars) 1)
      `((,witness-expr . ,(or (car generalize-vars) (car qvars))))
    (defquant-generalize-alist1 0 qvars witness-expr generalize-vars)))

(defun defquant-fn (name vars quant-expr generalize-vars witness-rulename
                         instance-rulename define witness-dcls
                         witness-dcls-p strengthen)
  (b* ((witness-rulename (or witness-rulename
                             (intern-in-package-of-symbol
                              (concatenate 'string (symbol-name name)
                                           "-WITNESSING")
                              name)))
       (witness-name (intern-in-package-of-symbol
                      (concatenate 'string (symbol-name name)
                                   "-WITNESS")
                      name))
       (witness-expr (cons witness-name vars))
       (qcall (cons name vars))
       (instance-rulename (or instance-rulename
                              (intern-in-package-of-symbol
                               (concatenate 'string (symbol-name name)
                                            "-INSTANCING")
                               name)))
       ((when (not (and (eql (len quant-expr) 3)
                        (member (car quant-expr) '(forall exists))
                        (or (symbolp (cadr quant-expr))
                            (symbol-listp (cadr quant-expr))))))
        (er hard? 'defquant "Malformed quantifier expression: ~x0~%" quant-expr))
       (quantifier (nth 0 quant-expr))
       (qvars (nth 1 quant-expr))
       (qvars (if (atom qvars) (list qvars) qvars))
       (qexpr (nth 2 quant-expr))
       (necc-suff-name (intern-in-package-of-symbol
                        (concatenate 'string (symbol-name name)
                                     (if (eq quantifier 'forall)
                                         "-NECC" "-SUFF"))
                        name)))

  `(progn
     ,@(and define `((defun-sk ,name ,vars ,quant-expr
                       ,@(and witness-dcls-p
                              `(:witness-dcls ,witness-dcls))
                       :strengthen ,strengthen)))
     (defwitness ,witness-rulename
       :predicate ,(if (eq quantifier 'forall)
                       `(not ,qcall)
                     qcall)
       :expr ,(defquant-witness-binding qvars witness-expr
                (if (eq quantifier 'forall)
                    `(not ,qexpr) qexpr))
       :generalize ,(defquant-generalize-alist
                      qvars witness-expr generalize-vars)
       :hints ('(:in-theory '(,name))))
     (definstantiate ,instance-rulename
       :predicate ,(if (eq quantifier 'forall)
                       qcall
                     `(not ,qcall))
       :vars ,qvars
       :expr ,(if (eq quantifier 'forall)
                  qexpr `(not ,qexpr))
       :hints ('(:in-theory nil :use ,necc-suff-name)))
     (in-theory (disable ,name ,necc-suff-name)))))


(defmacro defquant (name vars quant-expr &key generalize-vars
                         witness-rulename instance-rulename
                         (define 't) (witness-dcls 'nil witness-dcls-p)
                         (strengthen 'nil))
  (defquant-fn name vars quant-expr generalize-vars witness-rulename
    instance-rulename define witness-dcls witness-dcls-p strengthen))


(defun witness-rule-e/d-event (rulename tablename enablep world)
  (b* ((al (table-alist tablename world))
       (look (assoc rulename al)))
    (and look
         `((table ,tablename
                  ',rulename ',(update-nth 0 enablep (cdr look)))))))


(defun witness-rule-e/d-fn (rulename enablep world)
  (let ((events (append (witness-rule-e/d-event
                         rulename 'witness-cp-witness-rules enablep world)
                        (witness-rule-e/d-event
                         rulename 'witness-cp-instance-rules enablep world)
                        (witness-rule-e/d-event
                         rulename 'witness-cp-example-templates enablep world))))
    (if events
        `(progn . ,events)
      (er hard? 'witness-rule-e/d
          "There is no witness-cp rule named ~x0.~%" rulename))))

(defmacro witness-enable (rulename)
  `(make-event (witness-rule-e/d-fn ',rulename t (w state))))

(defmacro witness-disable (rulename)
  `(make-event (witness-rule-e/d-fn ',rulename nil (w state))))

(defun union-assoc (a b)
  (cond ((atom a) b)
        ((assoc (caar a) b)
         (union-assoc (cdr a) b))
        (t (cons (car a) (union-assoc (cdr a) b)))))

(defun remove-dups-assoc (a)
  (cond ((atom a) nil)
        ((assoc (caar a) (cdr a))
         (remove-dups-assoc (cdr a)))
        (t (cons (car a) (remove-dups-assoc (cdr a))))))

(defun instance-rules-for-examples (example-templates)
  (if (atom example-templates)
      nil
    (cons (nth 4 (car example-templates))
          (instance-rules-for-examples (cdr example-templates)))))


(mutual-recursion
 (defun witness-expand-ruleset (names world)
   (declare (xargs :mode :program))
   ;; Union together the rules mentioned as well as the rules within the
   ;; rulesets.
   (b* (((mv witness-rules instance-rules example-templates rest)
         (witness-expand-ruleset-names names world))
        ((mv witness-rules1 &)
         (look-up-witness-rules rest (table-alist 'witness-cp-witness-rules world)))
        ((mv example-templates1 &)
         (look-up-witness-rules rest (table-alist 'witness-cp-example-templates
                                                  world)))
        (example-templates1 (remove-dups-assoc example-templates1))
        ((mv instance-rules1 &)
         (look-up-witness-rules (instance-rules-for-examples example-templates1)
                                (table-alist 'witness-cp-instance-rules world))))
     (mv (union-assoc (remove-dups-assoc witness-rules1) witness-rules)
         (union-assoc (remove-dups-assoc instance-rules1) instance-rules)
         (union-assoc example-templates1 example-templates))))

 (defun witness-expand-ruleset-names (names world)
   (if (atom names)
       (mv nil nil nil nil)
     (b* (((mv witness-rules instance-rules example-templates rest)
           (witness-expand-ruleset-names (cdr names) world))
          (ruleset-look
           (assoc (car names)
                  (table-alist 'witness-cp-rulesets world)))
          ((when (not ruleset-look))
           (mv witness-rules instance-rules example-templates
               (cons (car names) rest)))
          ((mv witness-rules1 instance-rules1 example-templates1)
           (witness-expand-ruleset (cdr ruleset-look) world)))
       (mv (union-assoc witness-rules1 witness-rules)
           (union-assoc instance-rules1 instance-rules)
           (union-assoc example-templates1 example-templates)
           rest)))))



(defmacro witness (&key ruleset (generalize 't))
  `(and stable-under-simplificationp
        (b* ((ruleset ',ruleset)
             (rules
              (if ruleset
                  (mv-let (w i e)
                    (witness-expand-ruleset
                     (if (atom ruleset) (list ruleset) ruleset)
                     world)
                    (list w e i))
                (list (table-alist 'witness-cp-witness-rules world)
                      (table-alist 'witness-cp-example-templates
                                   world)
                      (table-alist 'witness-cp-instance-rules
                                   world))))
               (hints (cons ',generalize rules)))
          `(:computed-hint-replacement
            ((use-these-hints-hint clause))
            :clause-processor
            (witness-cp clause ',hints state)))))



