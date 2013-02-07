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

(include-book "use-by-hint")
(include-book "generalize")
(include-book "unify-subst")
(include-book "tools/bstar" :dir :system)
(include-book "ev-theoremp")
(include-book "tools/def-functional-instance" :dir :system)
(include-book "tools/oracle-eval" :dir :system)
(include-book "data-structures/no-duplicates" :dir :system)

(set-inhibit-warnings "theory")


(local (in-theory (disable state-p1-forward)))

;; See :DOC WITNESS-CP, or read it below.


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
   (implies a b) (hide x)
   (cons a b) (binary-+ a b)))


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

(def-ev-theoremp witness-ev)

(def-unify witness-ev witness-ev-alist)

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


;; Vars is the list of quantified vars for the instance rule.
;; Examples is a list of lists of expressions, each of same length as vars, to
;; be bound to the vars.
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

;; example-alist maps each instance rulename to a list of lists of terms, each
;; of the same length as the quantified vars of the instance rule.
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
              (symbol-listp (nth 4 rule)))
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

(defun add-example-for-instance-rules (inst-rules example acc)
  (declare (xargs :guard (and (symbol-listp inst-rules)
                              (alistp acc)
                              (pseudo-term-listp example)
                              (pseudo-term-list-list-alistp acc))
                  :guard-hints (("goal" :in-theory
                                 (enable pseudo-term-list-listp-true-listp
                                         pseudo-term-list-listp
                                         alistp)))))
  (if (atom inst-rules)
      acc
    (b* ((rule (car inst-rules))
         (other-examples (cdr (assoc rule acc)))
         ((when (member-equal example other-examples))
          (add-example-for-instance-rules (cdr inst-rules) example acc))
         (acc (cons (cons rule (cons example other-examples)) acc)))
      (add-example-for-instance-rules (cdr inst-rules) example acc))))

(defthm pseudo-term-list-list-alistp-add-example-for-instance-rules
  (implies (and (pseudo-term-listp example)
                (pseudo-term-list-list-alistp acc))
           (pseudo-term-list-list-alistp
            (add-example-for-instance-rules
             inst-rules example acc)))
  :hints(("Goal" :in-theory (enable pseudo-term-list-listp))))

(defthm alistp-add-example-for-instance-rules
  (implies (alistp acc)
           (alistp (add-example-for-instance-rules
                    inst-rules example acc)))
  :hints(("Goal" :in-theory (enable alistp))))


(defun examples-for-term (term templates acc state)
  (declare (xargs :guard (and (pseudo-termp term)
                              (good-templatesp templates)
                              (alistp acc)
                              (pseudo-term-list-list-alistp acc))
                  :verify-guards nil
                  :stobjs state))
  (b* (((when (atom templates)) (mv acc state))
       ((nths ?exname enabledp pat templ rulenames restriction) (car templates))
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
       (acc (add-example-for-instance-rules rulenames example acc)))
    (examples-for-term term (cdr templates) acc state)))

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

(mutual-recursion ;; witness-cp-collect-examples
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

(local (defthm true-listp-make-non-dup-vars
         (equal (true-listp (make-non-dup-vars x avoid)) t)))

(local (defthm strip-cdrs-pairlis
         (implies (and (equal (len a) (len b))
                       (true-listp b))
                  (equal (strip-cdrs (pairlis$ a b)) b))))

(local (defthm pseudo-term-listp-when-symbol-listp
         (implies (symbol-listp x)
                  (pseudo-term-listp x))
         :hints (("goal" :induct (len x)
                  :in-theory (enable symbol-listp
                                     pseudo-term-listp
                                     pseudo-termp)))))

(defthm pseudo-term-listp-witness-cp-generalize-clause
  (implies (and (pseudo-term-listp clause)
                (alistp genalist)
                (symbol-listp (strip-cdrs genalist)))
           (pseudo-term-listp
            (witness-cp-generalize-clause genalist clause)))
  :hints (("goal" :do-not-induct t)))

(in-theory (disable witness-cp-generalize-clause))



;;========================================================================
;; WITNESS-CP
;;========================================================================
;; (top level)

;; User-provided list of examples has form:
;;   ((instance-rulename1 term1 term2 ...)
;;    (instance-rulename2 term1 term2 ...) ...)
;;  --- note: not an alist, "shadowed pairs" are multiple instances of the same rule
;; whereas we need example alist of the form
;;   ((instance-rulename1 (term1 term2 ...) ;; example1
;;                        (term11 term12 ...) ;; example2
;;                        ...)
;;    (instance-rulename2 ...))
;;  --- note: alist, shadowed pairs ignored.


;; (defun pseudo-term-bindingsp (x)
;;   ;; like LET bindings
;;   (declare (xargs :guard t))
;;   (if (Atom x)
;;       (eq x nil)
;;     (and (consp (car x))
;;          (symbolp (caar x))
;;          (consp (cdar x))
;;          (pseudo-termp (cadar x))
;;          (eq (cddar x) nil)
;;          (pseudo-term-bindingsp (cdr x)))))

;; (local (defthm assoc-in-pseudo-term-bindingsp
;;          (implies (and (pseudo-term-bindingsp x)
;;                        (assoc k x))
;;                   (and (consp (cdr (assoc k x)))
;;                        (pseudo-termp (cadr (assoc k x)))))))

;; (local (defthm pseudo-term-bindingsp-implies-alistp
;;          (implies (pseudo-term-bindingsp x)
;;                   (alistp x))
;;          :hints(("Goal" :in-theory (enable alistp)))))

;; (local (defthm pseudo-term-bindingsp-implies-eqlable-alistp
;;          (implies (pseudo-term-bindingsp x)
;;                   (eqlable-alistp x))))
           
;; (local (defthm consp-assoc
;;          (implies (and (alistp x)
;;                        (assoc k x))
;;                   (consp (assoc k x)))))
                  
;; (defun missing-bindings (keys bindings)
;;   (declare (xargs :guard (pseudo-term-bindingsp bindings)))
;;   (if (atom keys)
;;       nil
;;     (if (assoc (car keys) bindings)
;;         (missing-bindings (cdr keys) bindings)
;;       (cons (car keys)
;;             (missing-bindings (cdr keys) bindings)))))

;; (defun bindings-to-ordered-list (keys bindings)
;;   (declare (xargs :guard (pseudo-term-bindingsp bindings)))
;;   (if (atom keys)
;;       nil
;;     (cons (cdr (assoc (car keys) bindings))
;;           (bindings-to-ordered-list (cdr keys) bindings))))


;; just checks syntax, nothing sophisticated
(defun good-user-examplesp (x)
  (declare (Xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (consp (car x))
         (symbolp (caar x))
         (pseudo-term-listp (cdar x))
         (good-user-examplesp (cdr x)))))



(defun user-examples-to-example-alist (user-examples acc)
  (declare (xargs :guard (and (good-user-examplesp user-examples)
                              (alistp acc)
                              (pseudo-term-list-list-alistp acc))
                  :guard-hints (("goal" :in-theory (enable alistp pseudo-term-list-listp)))))
  (if (endp user-examples)
      acc
    (b* (((cons rulename termlist) (car user-examples))
         (other-examples (cdr (assoc rulename acc)))
         (acc (cons (cons rulename (cons termlist other-examples)) acc)))
      (user-examples-to-example-alist (cdr user-examples) acc))))
  
(defthm user-examples-to-example-alist-type
  (let ((res (user-examples-to-example-alist user-examples acc)))
    (and (implies (alistp acc)
                  (alistp res))
         (implies (and (pseudo-term-list-list-alistp acc)
                       (good-user-examplesp user-examples))
                  (pseudo-term-list-list-alistp res))))
  :hints(("Goal" :in-theory (enable alistp pseudo-term-list-listp))))


(defun witness-cp (clause hints state)
  ":doc-section witness-cp
 witness-cp -- clause processor for quantifier-based reasoning~/

 You should not call witness-cp directly, but rather using the WITNESS macro
 as a computed hint.  This documentation is an overview of the witness-cp
 system.

 WITNESS-CP is an extensible clause processor that can use
 various sets of rules to do \"witnessing\" transformations.  Taking set-based
 reasoning as an example,  we might want to look at hypotheses of the form
 (subsetp-equal a b) and conclude specific examples such as
 (implies (member-equal k a) (member-equal k b)) for various k.  We might
 also want to look at hypotheses of the form (not (subsetp-equal c d)) and
 conclude (and (member-equal j c) (not (member-equal j d))) for some witness
 j.

 There are thus four steps to this transformation:
 1. Introduce witnesses for negative occurrences of universally-quantified
 predicates and positive occurrences of existentially-quantified ones.
 1a. Optionally, generalize newly introduced witness terms into fresh
 variables, for readability.
 2. Find the set of examples with which to instantiate positive
 universally-quantified and negative existentially-quantified predicates.
 3. Instantiate these predicates with these examples.

 The clause processor needs two types of information to accomplish this:
 - what predicates are to be taken as universal/existential quantifiers and
   what they mean; i.e. how to introduce witnesses/instantiate.
 - what examples to use when doing the instantiation.

 The witness-introduction and instantiation may both be lossy, i.e. result
 in a formula that isn't a theorem even if the original formula is one.~/

 To set up witnessing for not-subsetp-equal hypotheses:

 (defwitness subsetp-witnessing
   :predicate (not (subsetp-equal a b))
   :expr (and (member-equal (subsetp-equal-witness a b) a)
              (not (member-equal (subsetp-equal-witness a b) b)))
   :generalize (((subsetp-equal-witness a b) . ssew)
   :hints ('(:in-theory '(subsetp-equal-witness-correct))))

 This means that in the witnessing phase, we search for hypotheses of the
 form (not (subsetp-equal a b)) and for each such hypothesis, we add the
 hypothesis
 (and (member-equal (subsetp-equal-witness a b) a)
      (not (member-equal (subsetp-equal-witness a b) b)))
 but then generalize away the term (subsetp-equal-witness a b) to a fresh
 variable from the set SSEW0, SSEW1, ... yielding new hyps:
     (member-equal ssew0 a)
     (not (member-equal ssew0 b))
 So effectively we've taken an existential assumption and introduced a fresh
 variable witnessing it.  We wrap (hide ...) around the original hyp to leave
 a trace of what we've done (otherwise it would likely be rewritten away,
 since the two hyps we've introduced imply its truth).

 We add these new hypotheses to our main formula.  To ensure that this is
 sound, the clause processor produces an additional proof obligation:
 (implies (not (subsetp-equal a b))
          (and (member-equal (subsetp-equal-witness a b) a)
               (not (member-equal (subsetp-equal-witness a b) b))))
 To ensure that we'll be able to satisfy this, the defwitness event tries to
 prove this using the computed hints provided by the :hint argument to
 defwitness.  In this case, this puts ACL2 into a theory containing only the
 subsetp-equal-witness-correct rule.  If the proof works, then the witness-cp
 hint will arrange for this same computed hint to be provided when the clause
 processor produces this proof obligation, and it's a fair bet that ACL2 will
 also be able to prove it then.  The hint provided is a good one because it
 puts ACL2 into a known theory (not dependent on the ambient theory); a :by
 hint is another good candidate.

 To set up instantiation of subsetp-equal hypotheses:

 (definstantiate subsetp-equal-instancing
   :predicate (subsetp-equal a b)
   :vars (k)
   :expr (implies (member-equal k a)
                  (member-equal k b))
   :hints ('(:in-theory '(subsetp-member))))

 This will mean that for each subsetp-equal hypothesis we find, we'll add
 hypotheses of the form (implies (member-equal k a) (member-equal k b)) for
 each of (possibly) several k.  The terms we use to instantiate k are
 determined by defexample; see below.
 To make it sound to add these hypotheses, the clause processor again
 introduces a proof obligation:
  (implies (subsetp-equal a b)
           (implies (member-equal k a)
                    (member-equal k b)))
 Again, the :hints argument is used to prove this, both (as a test) when the
 definstantiate form is submitted and when it is used.

 The terms used to instantiate k above are determined by defexample rules,
 like the following:
  (defexample subsetp-member-template
   :pattern (member-equal k a)
   :templates (k)
   :instance-rulename subsetp-equal-instancing)

 This means that in phase 2, we'll look through the clause for expressions
 (member-equal k a) and whenever we find one, include k in the list of
 witnesses to use for instantiating using the subsetp-equal-instance rule.
 Defexample doesn't require any proof obligation; it's just a heuristic that
 adds to the set of terms used to instantiate universal quantifiers.

 To use the scheme we've introduced for reasoning about subsetp-equal, we can
 introduce a witness ruleset:

 (def-witness-ruleset subsetp-witnessing-rules
   '(subsetp-witnessing
     subsetp-equal-instancing
     subsetp-member-template))

 Then when we want to use this reasoning strategy, we can provide a computed
 hint:
 :hints ((witness :ruleset subsetp-witnessing-rules))

 This implicitly waits til the formula is stable-under-simplification and
 invokes the witness-cp clause processor, allowing it to use the
 witnessing/instancing/example rules listed.  It also sets things up so that
 the right hints will be provided to the extra proof obligations produced by
 applying defwitness and definstantiate rules.  You can also define a macro
 so that you don't have to remember this syntax:

 (defmacro subset-reasoning () '(witness :ruleset subsetp-witnessing-rules))
 (defthm foo
   ...
  :hints ((\"goal\" ...)
          (subset-reasoning)))

 Documentation is available for defwitness, definstantiate, and defexample.
 Also defquantexpr, which is a shortcut for the common pattern (as above) of
 doing both a defwitness and definstantiate for a certain term.
 Also defquant, which defines a quantified function (using defun-sk) and sets
 up defwitness/definstantiate rules for it."
  (declare (xargs :guard (pseudo-term-listp clause)
                  :stobjs state
                  :verify-guards nil))
  (b* (((when (not (and (true-listp hints)
                        (>= (len hints) 5))))
        (er hard? 'witness-cp "Bad hints: wrong format~%")
        (value (list clause)))
       ((nths generalizep
              witness-rules example-templates instance-rules
              user-examples) hints)
       ((when (not (good-witness-rulesp witness-rules)))
        (er hard? 'witness-cp "Bad hints: bad witness-rules~%")
        (value (list clause)))
       ((when (not (good-templatesp example-templates)))
        (er hard? 'witness-cp "Bad hints: bad example-templates~%")
        (value (list clause)))
       ((when (not (good-user-examplesp user-examples)))
        (er hard? 'witness-cp "Bad hints: bad user examples~%")
        (value (list clause)))
       (example-alist (user-examples-to-example-alist user-examples nil))
       ((when (not (good-instance-rules-and-examplesp
                    instance-rules example-alist)))
        (er hard? 'witness-cp "Bad hints: bad instance rule or user example~%")
        (value (list clause)))
       ((mv witnessed-clause generalize-alist witness-obligs state)
        (witness-cp-expand-witnesses clause witness-rules state))
       (generalized-clause
        (if generalizep
            (witness-cp-generalize-clause
             generalize-alist witnessed-clause)
          witnessed-clause))
       ((mv example-alist state)
        (witness-cp-collect-examples-list
         (beta-reduce-list generalized-clause)
         example-templates example-alist state))
       ((when (not (good-instance-rules-and-examplesp
                    instance-rules example-alist)))
        (er hard? 'witness-cp
            "Bad hints: bad instance rule or generated example~%")
        (value (list clause)))
       ((mv instanced-clause instance-obligs state)
        (witness-cp-expand-instances
         generalized-clause example-alist instance-rules state))
       ;; (generalized-clause
       ;;  (if generalizep
       ;;      (witness-cp-generalize-clause
       ;;       generalize-alist instanced-clause)
       ;;    instanced-clause))
       )
    (value
     (cons instanced-clause
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
                   witness-cp-expand-instances
                   nth len update-nth nth-0-cons nth-add1))
          :use ((:instance witness-ev-falsify
                           (x (disjoin clause))
                           (a a))
                (:instance witness-ev-falsify
                 (x (disjoin (mv-nth 0 (witness-cp-expand-witnesses
                                        clause (nth 1 hints) state))))
                 (a a))
                (:instance witness-ev-falsify
                           (x (disjoin
                               (car (mv-nth 1 (witness-cp clause hints state)))))
                           (a a))
                (:instance witness-ev-falsify
                 (x (disjoin
                     (car (mv-nth 1 (witness-cp clause hints state)))))
                 (a (witness-ev-falsify
                     (disjoin (witness-cp-generalize-clause
                               (mv-nth 1 (witness-cp-expand-witnesses
                                          clause (nth 1 hints) state))
                               (mv-nth 0 (witness-cp-expand-witnesses
                                          clause (nth 1 hints) state))))))))
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
    ((subsetp-witnessing
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
      ('(:in-theory (e/d (subsetp-member)
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
  (declare (xargs :mode :program :stobjs state))
  (with-ctx-summarized
    ctx
    (b* (((er hint)
          (translate-hints+ 'thm '((use-these-hints-hint clause))
                            nil 'ctx (w state) state))
         (clauses `(((not (use-these-hints ',hints))
                     ,term)))
         (pspv (make-pspv (ens state) (w state) :orig-hints hint
                          :displayed-goal term))
         ((er ttree)
          (prove-loop clauses pspv hint (ens state) (w state) ctx state)))
      (chk-assumption-free-ttree ttree ctx state))))


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
  (declare (xargs :mode :program :stobjs state))
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
                hints (cons 'defwitness name) state))
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
  ":doc-section witness-cp
 Defwitness -- add a WITNESS-CP rule providing a witness for an
 existential-quantifier hypothesis (or universal-quantifier conclusion).~/

 Usage example:
 (defwitness subsetp-witnessing
   :predicate (not (subsetp-equal a b))
   :expr (and (member-equal (subsetp-equal-witness a b) a)
              (not (member-equal (subsetp-equal-witness a b) b)))
   :generalize (((subsetp-equal-witness a b) . ssew)
   :hints ('(:in-theory '(subsetp-equal-witness-correct))))

 Additional arguments:
   :restriction term
 where term may have free variables that occur also in the :predicate term.

 The above example tells WITNESS-CP how to expand a hypothesis of the form
 (not (subsetp-equal a b)) or, equivalently, a conclusion of the form
 (subsetp-equal a b), generating a fresh variable named SSEW or similar that
 represents an object that proves that A is not a subset of B (because that
 object is in A but not B.)

 See ~il[witness-cp] for background.~/

 When this rule is in place, WITNESS-CP will look for literals in the clause
 that unify with the negation of PREDICATE.  It will replace these by a term
 generated from EXPR.  It will generalize away terms that are keys in
 GENERALIZE, replacing them by fresh variables based on their corresponding
 values.  It will use HINTS to relieve the proof obligation that this
 replacement is sound (which is also done when the defwitness form is run).

 If a RESTRICTION is given, then this replacement will only take place when
 it evaluates to a non-nil value.    This requires oracle-eval to be allowed;
 ~l[oracle-eval].~/"
  `(make-event (defwitness-fn ',name ',predicate ',expr ',restriction
                 ',generalize ',hints state)))




(defun definstantiate-fn (name predicate vars expr restriction hints
                               state)
  (declare (xargs :mode :program :stobjs state))
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
                hints (cons 'definstantiate name) state)))
    (value
     `(table witness-cp-instance-rules
             ',name ',(list t
                            (dumb-negate-lit predicate)
                            vars
                            (dumb-negate-lit expr)
                            restriction hints)))))

(defmacro definstantiate (name &key predicate vars expr
                               (restriction ''t) hints)
  ":doc-section witness-cp
 Definstantiate -- add a WITNESS-CP rule showing how to instantiate a
 universial-quantifier hyptothesis (or an existential-quantifier conclusion).~/

 Usage example:
 (definstantiate subsetp-equal-instancing
   :predicate (subsetp-equal a b)
   :vars (k)
   :expr (implies (member-equal k a)
                  (member-equal k b))
   :hints ('(:in-theory '(subsetp-member))))

 Additional arguments:
   :restriction term
 where term may have free variables that occur also in the :predicate term or
 the list :vars.

 The above example tells WITNESS-CP how to expand a hypothesis of the form
 (subsetp-equal a b) or, equivalently, a conclusion of the form
 (not (subsetp-equal a b)), introducing a term of the form EXPR for each of
 some set of K.  Which K are chosen depends on the set of existing ~il[defexample]
 rules and the user-provided examples from the call of WITNESS.

 See ~il[witness-cp] for background.~/

 In more detail, WITNESS-CP will look in the clause for literals that unify
 with the negation of PREDICATE.  It will replace these with a conjunction of
 several instantiations of EXPR, with the free variables present in VARS
 replaced by either user-provided terms or terms generated by a defexample rule.
 It will use HINTS to relieve the proof obligation that this replacement is
 sound (which is also done when the definstantiate form is run).

 If a RESTRICTION is given, then this replacement will only take place when
 it evaluates to a non-nil value.  This requires  oracle-eval to be allowed;
 ~l[oracle-eval].
 ~/"
  `(make-event (definstantiate-fn
                 ',name ',predicate ',vars ',expr ',restriction
                 ',hints state)))


(defun quantexpr-bindings-to-generalize (bindings)
  (b* (((when (atom bindings)) nil)
       ((list var expr) (car bindings)))
    (cons (cons expr var)
          (quantexpr-bindings-to-generalize (cdr bindings)))))
    

(defun defquantexpr-fn (name predicate quantifier expr witnesses
                             instance-restriction witness-restriction
                             instance-hints witness-hints
                             witness-rulename instance-rulename
                             generalize in-package-of)
  (b* ((in-package-of (or in-package-of name))
       ((unless (member quantifier '(:forall :exists)))
        (er hard? 'defquantexpr
            "Quantifier argument must be either :FORALL or :EXISTS~%"))
       (witness-rulename
        (or witness-rulename
            (intern-in-package-of-symbol
             (concatenate 'string (symbol-name name) "-WITNESSING")
             in-package-of)))
       (instance-rulename
        (or instance-rulename
            (intern-in-package-of-symbol
             (concatenate 'string (symbol-name name) "-INSTANCING")
             in-package-of)))
       ((mv witness-pred instance-pred witness-expr instance-expr)
        (if (eq quantifier :forall)
            (mv `(not ,predicate)
                predicate
                `(let ,witnesses
                   (not ,expr))
                expr)
          (mv predicate
              `(not ,predicate)
              `(let ,witnesses ,expr)
              `(not ,expr))))
       (generalize-alist (quantexpr-bindings-to-generalize witnesses)))
    `(progn (defwitness ,witness-rulename
              :predicate ,witness-pred
              :expr ,witness-expr
              :hints ,witness-hints
              ,@(and generalize `(:generalize ,generalize-alist))
              :restriction ,witness-restriction)
            (definstantiate ,instance-rulename
              :predicate ,instance-pred
              :vars ,(strip-cars witnesses)
              :expr ,instance-expr
              :hints ,instance-hints
              :restriction ,instance-restriction))))

(defmacro defquantexpr (name &key predicate
                             (quantifier ':forall)
                             expr witnesses
                             (instance-restriction ''t)
                             (witness-restriction ''t)
                             instance-hints witness-hints
                             witness-rulename
                             instance-rulename
                             in-package-of
                             (generalize 't))
  ":doc-section witness-cp
 Defquantexpr -- shortcut to perform both a DEFWITNESS and DEFINSTANTIATE~/

 Usage:
~bv[]
 (defquantexpr subsetp-equal
  :predicate (subsetp-equal x y)
  :quantifier :forall
  :witnesses ((k (subsetp-equal-witness x y)))
  :expr (implies (member-equal k x)
                 (member-equal k y))
  :witness-hints ('(:in-theory '(subsetp-equal-witness-correct)))
  :instance-hints ('(:in-theory '(subsetp-member))))
~ev[]
 This expands to a DEFWITNESS and DEFINSTANTIATE form.  The names of the
 defwitness and definstantiate rules produced are generated from the name
 (first argument) of the defquantexpr form; in this case they are
 subsetp-witnessing and subsetp-equal-instancing.  Keyword arguments
 witness-rulename and instance-rulename may be provided to override these
 defaults.

 Witness-hints and instance-hints are the hints passed to the two forms.

 Additional arguments: instance-restriction, witness-restriction, generalize.
 Instance-restriction and witness-restriction are the :restriction arguments
 passed to defwitness and definstantiate, respectively.  If :generalize is nil,
 then the defwitness rule will not do generalization; otherwise, it will use
 the keys of :witnesses as the variable names.~/

 The meaning of this form is as follows:
~bv[]
 \":predicate holds iff (:quantifier) (keys of :witnesses), :expr.\"
~ev[]

 In our example above:

~bv[]
 \"(subsetp-equal x y) iff for all k,
   (implies (member-equal k x)
            (member-equal k y)).\"
~ev[]

 An example of this with an existential quantifier:
~bv[]
 (defquantexpr intersectp-equal
  :predicate (intersectp-equal x y)
  :quantifier :exists
  :witnesses ((k (intersectp-equal-witness x y)))
  :expr (and (member-equal k x)
             (member-equal k y))
  :witness-hints ('(:in-theory '(intersectp-equal-witness-correct)))
  :instance-hints ('(:in-theory '(intersectp-equal-member))))
~ev[]

 meaning:
~bv[]
 \"(intersectp-equal x y) iff there exists k such that
      (and (member-equal k x)
           (member-equal k y))\".
~ev[]

 the values bound to each key in :witnesses should be witnesses for the
 existential quantifier in the direction of the bi-implication that involves
 (the forward direction for :exists and the backward for :forall):

 for the first example,
~bv[]
 \"(let ((k (subsetp-equal-witness x y)))
      (implies (member-equal k x)
               (member-equal k y)))
   implies
   (subsetp-equal x y).\"
~ev[]

 for the second example,
~bv[]
 \"(intersectp-equal x y)
   implies
   (let ((k (intersectp-equal-witness x y)))
     (and (member-equal k x)
          (member-equal k y))).\"
~ev[]~/

"
  (defquantexpr-fn name predicate quantifier expr witnesses
     instance-restriction witness-restriction
     instance-hints witness-hints witness-rulename instance-rulename generalize in-package-of))







(defun missing-instance-rules (instance-rules alist)
  (declare (xargs :guard (and (alistp alist)
                              (symbol-listp instance-rules))))
  (if (atom instance-rules)
      nil
    (if (assoc (car instance-rules) alist)
        (missing-instance-rules (cdr instance-rules) alist)
      (cons (car instance-rules)
            (missing-instance-rules (cdr instance-rules) alist)))))


(defun wrong-arity-instance-rules (arity instance-rules alist)
  (declare (xargs :mode :program))
  (if (atom instance-rules)
      nil
    (if (= (len (nth 3 (assoc (car instance-rules) alist))) arity)
        (wrong-arity-instance-rules arity (cdr instance-rules) alist)
      (cons (car instance-rules)
            (wrong-arity-instance-rules arity (cdr instance-rules) alist)))))

(defun defexample-fn (name pattern templates instance-rules restriction
                           state)
  (declare (Xargs :mode :program :stobjs state))
  (b* (((when (not pattern))
        (mv "DEFEXAMPLE: Must supply a :PATTERN.~%" nil state))
       ((when (not templates))
        (mv "DEFEXAMPLE: Must supply :TEMPLATES.~%" nil state))
       ((when (not instance-rules))
        (mv "DEFEXAMPLE: Must supply an :INSTANCE-RULENAME.~%" nil state))
       (instance-rule-alist (table-alist 'witness-cp-instance-rules
                                         (w state)))
       (missing-rules (missing-instance-rules instance-rules instance-rule-alist))
       ((when missing-rules)
        (mv (msg "DEFEXAMPLE: The following instance rules do not exist: ~x0~%"
                 missing-rules)
            nil state))
       (nvars (len templates))
       (bad-rules (wrong-arity-instance-rules nvars instance-rules instance-rule-alist))
       ((when bad-rules)
        (mv (msg "DEFEXAMPLE: The following instance rules do not have the
right number of free variables (~x0): ~x1~%"
                 nvars bad-rules)
            nil state))
       ((er pattern)
        (translate pattern t t nil 'defexample (w state) state))
       ((er templates)
        (wcp-translate-lst templates state)))
    (value
     `(table witness-cp-example-templates
             ',name ',(list t pattern templates instance-rules restriction)))))

(defmacro defexample (name &key pattern templates instance-rulename
                           instance-rules
                           (restriction ''t))
  ":doc-section witness-cp
Defexample -- tell witness-cp how to instantiate the free variables of
definstantiate rules~/

Example:
~bv[]
 (defexample set-reasoning-member-template
   :pattern (member-equal k y)
   :templates (k)
   :instance-rules
   (subsetp-equal-instancing
    intersectp-equal-instancing
    set-equiv-instancing
    set-consp-instancing))
~ev[]

Additional arguments:
  :restriction term
 where term may have free variables present in pattern,
  :instance-rulename rule
 may be used instead of :instance-rules when there is only one rule.

Meaning: Find terms of the form ~c[(member-equal k y)] throughout the clause,
and for each such ~c[k], for any match of one of the instance-rules listed, add
an instance using that ~c[k].  For example, if we have a hypothesis
~c[(subsetp-equal a b)] and terms
~bv[]
 (member-equal (foo x) (bar y))
 (member-equal q a)
~ev[]
present somewhere in the clause, then this rule along with the
subsetp-equal-instancing rule will cause the following hyps to be added:
~bv[]
 (implies (member-equal (foo x) a)
          (member-equal (bar x) a))
 (implies (member-equal q a)
          (member-equal q b)).
~ev[]

If a :restriction is present, then the rule only applies to occurrences of
pattern for which the restriction evaluates to non-nil.  This requires
oracle-eval to be allowed; ~l[oracle-eval].~/~/"
  `(make-event
    (defexample-fn ',name ',pattern ',templates
      ',(if instance-rulename (list instance-rulename) instance-rules)
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
  ":doc-section witness-cp
Def-witness-ruleset: name a set of witness-cp rules~/

The WITNESS computed-hint macro takes a :ruleset argument that determines
which witness-cp rules are allowed to fire.  Def-witness-ruleset allows
one name to abbreviate several actual rules in this context.

Usage:
~bv[]
 (def-witness-ruleset foo-rules
    '(foo-instancing
      foo-witnessing
      bar-example-for-foo
      baz-example-for-foo))
~ev[]

After submitting this form, the following invocations of WITNESS are
equivalent:

~bv[]
 (witness :ruleset foo-rules)
 (witness :ruleset (foo-rules))
 (witness :ruleset (foo-instancing
                    foo-witnessing
                    bar-example-for-foo
                    baz-example-for-foo))
~ev[]

 These rulesets are defined using a table event.  If multiple different
definitions are given for the same ruleset name, the latest one is always in
effect.

 Rulesets can contain other rulesets.  These are expanded at the time the
WITNESS hint is run.  A ruleset can be expanded with
~bv[]
 (witness-expand-ruleset names (w state))
~ev[]

Witness rules can also be enabled/disabled using ~il[witness-enable] and
~il[witness-disable]; these settings take effect when WITNESS is called without
specifying a ruleset.  Ruleset names may be used in witness-enable and
witness-disable just as they are used in the ruleset argument of WITNESS.
~/~/"
  `(table witness-cp-rulesets ',name ,rules))

;; (defun defquant-witness-binding1 (n qvars witness-expr)
;;   (if (atom qvars)
;;       nil
;;     (cons `(,(car qvars) (mv-nth ,n ,witness-expr))
;;           (defquant-witness-binding1 (1+ n) (cdr qvars) witness-expr))))

;; (defun defquant-witness-binding (qvars witness-expr body)
;;   (if (eql (len qvars) 1)
;;       `(let ((,(car qvars) ,witness-expr)) ,body)
;;     `(let ,(defquant-witness-binding1 0 qvars witness-expr)
;;        ,body)))

;; (defun defquant-generalize-alist1 (n qvars witness-expr generalize-vars)
;;   (if (atom qvars)
;;       nil
;;     (cons `((mv-nth ,n ,witness-expr)
;;             . ,(or (car generalize-vars) (car qvars)))
;;           (defquant-generalize-alist1 (1+ n) (cdr qvars)
;;             witness-expr (cdr generalize-vars)))))


;; (defun defquant-generalize-alist (qvars witness-expr generalize-vars)
;;   (if (eql (len qvars) 1)
;;       `((,witness-expr . ,(or (car generalize-vars) (car qvars))))
;;     (defquant-generalize-alist1 0 qvars witness-expr generalize-vars)))

(defun defquant-witnesses-mv (n vars witness-call)
  (if (atom vars)
      nil
    (cons `(,(car vars) (mv-nth ,n ,witness-call))
          (defquant-witnesses-mv (1+ n) (cdr vars) witness-call))))

(defun defquant-witnesses (vars witness-call)
  (cond ((atom vars) nil) ;; ?
        ((atom (cdr vars))
         `((,(car vars) ,witness-call)))
        (t (defquant-witnesses-mv 0 vars witness-call))))
  

(defun defquant-fn (name vars quant-expr define
                         witness-rulename
                         instance-rulename
                         doc
                         quant-ok
                         skolem-name
                         thm-name
                         rewrite
                         strengthen
                         witness-dcls
                         in-package-of)
  (b* ((in-package-of (or in-package-of name))
       (qcall (cons name vars))
       ((when (not (and (eql (len quant-expr) 3)
                        (member-equal (symbol-name (car quant-expr))
                                     '("FORALL" "EXISTS"))
                        (or (symbolp (cadr quant-expr))
                            (symbol-listp (cadr quant-expr))))))
        (er hard? 'defquant "Malformed quantifier expression: ~x0~%"
            quant-expr))
       (exists-p (equal (symbol-name (car quant-expr)) "EXISTS"))
       (qvars (nth 1 quant-expr))
       (qvars (if (atom qvars) (list qvars) qvars))
       (qexpr (nth 2 quant-expr))
       ;; these need to be chosen the same way as in defun-sk
       (skolem-name (or skolem-name
                        (intern-in-package-of-symbol
                         (concatenate 'string (symbol-name name)
                                      "-WITNESS")
                         in-package-of)))
       (witness-expr (cons skolem-name vars))
       (thm-name (or thm-name
                     (intern-in-package-of-symbol
                      (concatenate 'string (symbol-name name)
                                   (if exists-p
                                       "-SUFF" "-NECC"))
                      in-package-of))))

  `(progn
     ,@(and define `((defun-sk ,name ,vars ,quant-expr
                       :doc ,doc
                       :quant-ok ,quant-ok
                       :skolem-name ,skolem-name
                       :thm-name ,thm-name
                       :rewrite ,rewrite
                       :strengthen ,strengthen
                       :witness-dcls ,witness-dcls)))
     (defquantexpr ,name
       :predicate ,qcall
       :quantifier ,(if exists-p :exists :forall)
       :witnesses ,(defquant-witnesses qvars witness-expr)
       :expr ,qexpr
       :witness-hints ('(:in-theory '(,name)))
       :instance-hints ('(:in-theory nil :use ,thm-name))
       :witness-rulename ,witness-rulename
       :instance-rulename ,instance-rulename)
     (in-theory (disable ,name ,thm-name)))))


(defmacro defquant (name vars quant-expr &key
                         (define 't)
                         witness-rulename
                         instance-rulename
                         ;; defun-sk args
                         doc
                         quant-ok
                         skolem-name
                         thm-name
                         rewrite
                         strengthen
                         in-package-of
                         (witness-dcls '((DECLARE (XARGS :NON-EXECUTABLE T)))))
  ":doc-section witness-cp
Defquant -- define a quantified function and corresponding witness-cp rules~/

Defquant introduces a quantified function using ~il[defun-sk] and subsequently
adds appropriate defwitness and definstantiate rules for that function.  Note
that no defexample rules are provided (we judge these too hard to get right
automatically).

Usage: Defquant takes the same arguments as ~il[defun-sk], plus the following
additional keywords:

  :define -- default t, use nil to skip the defun-sk step (useful if it
       has already been done)

  :witness-rulename, :instance-rulename --
     name the generated witness and instance rules.  The defaults are
     name-witnessing and name-instancing.~/~/"

  (defquant-fn name vars quant-expr define witness-rulename instance-rulename
    doc
    quant-ok
    skolem-name
    thm-name
    rewrite
    strengthen
    witness-dcls
    in-package-of))


(defun witness-rule-e/d-event (rulename tablename enablep world)
  (b* ((al (table-alist tablename world))
       (look (assoc rulename al)))
    (and look
         `((table ,tablename
                  ',rulename ',(update-nth 0 enablep (cdr look)))))))

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
    (append (nth 4 (car example-templates))
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
                                (table-alist 'witness-cp-instance-rules
                                             world)))
        ((mv instance-rules2 &)
         (look-up-witness-rules rest (table-alist 'witness-cp-instance-rules
                                                  world))))
     (mv (union-assoc (remove-dups-assoc witness-rules1) witness-rules)
         (union-assoc (remove-dups-assoc instance-rules1)
                      (union-assoc (remove-dups-assoc instance-rules2)
                                   instance-rules))
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

(defun witness-e/d-events (names tablename enablep world)
  (if (atom names)
      nil
    (append (witness-rule-e/d-event (car names) tablename enablep world)
            (witness-e/d-events (cdr names) tablename enablep world))))

(defun witness-e/d-ruleset-fn (names enablep world)
  (declare (xargs :mode :program))
  (b* ((names (if (atom names) (list names) names))
       ((mv w i e) (witness-expand-ruleset names world)))
    `(with-output :off :all :on error
       (progn
         ,@(witness-e/d-events (strip-cars w) 'witness-cp-witness-rules enablep world)
         ,@(witness-e/d-events (strip-cars i) 'witness-cp-instance-rules enablep world)
         . ,(witness-e/d-events (strip-cars e) 'witness-cp-example-templates enablep world)))))

(defmacro witness-enable (&rest names)
  ":doc-section witness-cp
 Witness-enable -- enable some witness-cp rules~/

 Usage:
~bv[]
 (witness-enable name1 name2 ...)
~ev[]
 
 Sets the witness-cp rules name1, name2... to be enabled by default.
When name1 is the name of a witness-ruleset rather than a rule, all rules in
the ruleset are set enabled.

The enabled/disabled setting of a witness-cp rule takes effect only when
WITNESS is called with no :ruleset argument; otherwise, the ruleset specified
ignores the enabled/disabled status.~/~/"
  `(make-event (witness-e/d-ruleset-fn ',names t (w state))))

(defmacro witness-disable (&rest names)
  ":doc-section witness-cp
 Witness-disable -- disable some witness-cp rules~/

 Usage:
~bv[]
 (witness-disable name1 name2 ...)
~ev[]
 
 Sets the witness-cp rules name1, name2... to be disabled by default.
When name1 is the name of a witness-ruleset rather than a rule, all rules in
the ruleset are set disabled.

The enabled/disabled setting of a witness-cp rule takes effect only when
WITNESS is called with no :ruleset argument; otherwise, the ruleset specified
ignores the enabled/disabled status.~/~/"
  `(make-event (witness-e/d-ruleset-fn ',names nil (w state))))



(defmacro witness (&key ruleset (generalize 't) examples)
  ":doc-section witness-cp
Witness -- computed-hint that runs witness-cp~/

Usage:
~bv[]
 (witness :ruleset (rule ruleset ...)
          :examples
           ((inst-rulename1 term1 term2 ...)
            (inst-rulename2 term3 ...) ...)
          :generalize t)
~ev[]

 Calls the clause processor WITNESS-CP.  If a ruleset is provided, only those
witness-cp rules will be available; otherwise, all rules that are currently
enabled (~l[witness-enable], ~il[witness-disable]) are used.

The :generalize argument is T by default; if set to NIL, the generalization
step is skipped (~l[witness-cp]).

The :examples argument is empty by default.  Usually, examples are generated by
defexample rules.  However, in some cases the user might like to instantiate
universally-quantified hyps in a particular way on a one-off basis; this may be
done using the :examples field.  Each inst-rulename must be the name of a
definstantiate rule, and the terms following it correspond to that rule's :vars
 (in partiular, the list of terms must be the same length as the :vars of the
rule).~/~/"
  `(and stable-under-simplificationp
        (b* ((ruleset ',ruleset)
             (examples ',examples)
             (rules/user-examples
              (if ruleset
                  (mv-let (w i e)
                    (witness-expand-ruleset
                     (if (atom ruleset) (list ruleset) ruleset)
                     world)
                    (list w e i examples))
                (list (table-alist 'witness-cp-witness-rules world)
                      (table-alist 'witness-cp-example-templates
                                   world)
                      (table-alist 'witness-cp-instance-rules
                                   world)
                      examples)))
               (hints (cons ',generalize rules/user-examples)))
          `(:computed-hint-replacement
            ((use-these-hints-hint clause))
            :clause-processor
            (witness-cp clause ',hints state)))))



