; Correctness of the ACL2 system function cnf-dnf
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; CNF-DNF (in tau.lisp) converts SIGN/TERM (TERM if SIGN is T, else its
;; negation) into conjunctive or disjunctive normal form: a list of lists of
;; literals, read as a conjunction of disjunctions if CNFP is T and as a
;; disjunction of conjunctions otherwise.  It recognizes NOT and the IFs that
;; represent AND and OR.  SPLIT-ON-CONJOINED-DISJUNCTIONS uses it (with CNFP
;; = NIL) to split the hypotheses of tau rules on disjunctions, so it is
;; soundness-critical: each resulting list of hypotheses must imply the
;; original hypotheses.

;; In the current sources CNF-DNF is wrong for NOT (see
;; cnf-dnf-incorrect-for-not in cnf-dnf-tests.lisp), and this allows a proof
;; of NIL using a tau rule.  So we prove correct a copy, CNF-DNF-FIXED, with a one-line fix,
;; and prove the splitting functions correct assuming CNF-DNF is correct on
;; the hypotheses.  Once CNF-DNF is fixed in the sources, the two
;; counterexample theorems in cnf-dnf-tests.lisp will fail; CNF-DNF-FIXED-CORRECT should then
;; be restated for CNF-DNF itself, which discharges the assumption.

(include-book "kestrel/evaluators/defevaluator-plus" :dir :system)
(local (include-book "kestrel/lists-light/reverse" :dir :system))
(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))

;; These functions are in :program mode in the sources.  We put them in
;; :logic mode here.
(verify-termination cross-prod1)
(verify-termination cross-prod2)
(verify-termination cross-prod)
(verify-termination cnf-dnf)
(verify-termination split-on-conjoined-disjunctions)
(verify-termination split-on-conjoined-disjunctions-in-hyps-of-pairs)

;; An evaluator that knows the functions CNF-DNF gives special treatment to.
(defevaluator+ cnf-dnf-eval if not)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The meanings of lists of literals and of lists of lists of literals:

(defund cnf-dnf-eval-disjunction (lits a)
  (if (endp lits)
      nil
    (if (cnf-dnf-eval (car lits) a)
        t
      (cnf-dnf-eval-disjunction (cdr lits) a))))

(defund cnf-dnf-eval-conjunction (lits a)
  (if (endp lits)
      t
    (if (cnf-dnf-eval (car lits) a)
        (cnf-dnf-eval-conjunction (cdr lits) a)
      nil)))

;; Conjunction of disjunctions
(defund cnf-dnf-eval-cnf (clauses a)
  (if (endp clauses)
      t
    (if (cnf-dnf-eval-disjunction (car clauses) a)
        (cnf-dnf-eval-cnf (cdr clauses) a)
      nil)))

;; Disjunction of conjunctions
(defund cnf-dnf-eval-dnf (clauses a)
  (if (endp clauses)
      nil
    (if (cnf-dnf-eval-conjunction (car clauses) a)
        t
      (cnf-dnf-eval-dnf (cdr clauses) a))))

(defthm cnf-dnf-eval-disjunction-of-append
  (equal (cnf-dnf-eval-disjunction (append x y) a)
         (or (cnf-dnf-eval-disjunction x a)
             (cnf-dnf-eval-disjunction y a)))
  :hints (("Goal" :in-theory (enable cnf-dnf-eval-disjunction append))))

(defthm cnf-dnf-eval-conjunction-of-append
  (equal (cnf-dnf-eval-conjunction (append x y) a)
         (and (cnf-dnf-eval-conjunction x a)
              (cnf-dnf-eval-conjunction y a)))
  :hints (("Goal" :in-theory (enable cnf-dnf-eval-conjunction append))))

(defthm cnf-dnf-eval-cnf-of-append
  (equal (cnf-dnf-eval-cnf (append x y) a)
         (and (cnf-dnf-eval-cnf x a)
              (cnf-dnf-eval-cnf y a)))
  :hints (("Goal" :in-theory (enable cnf-dnf-eval-cnf append))))

(defthm cnf-dnf-eval-dnf-of-append
  (equal (cnf-dnf-eval-dnf (append x y) a)
         (or (cnf-dnf-eval-dnf x a)
             (cnf-dnf-eval-dnf y a)))
  :hints (("Goal" :in-theory (enable cnf-dnf-eval-dnf append))))

(defthm cnf-dnf-eval-cnf-of-revappend
  (equal (cnf-dnf-eval-cnf (revappend x y) a)
         (and (cnf-dnf-eval-cnf x a)
              (cnf-dnf-eval-cnf y a)))
  :hints (("Goal" :induct (revappend x y)
           :in-theory (enable cnf-dnf-eval-cnf revappend))))

(defthm cnf-dnf-eval-dnf-of-revappend
  (equal (cnf-dnf-eval-dnf (revappend x y) a)
         (or (cnf-dnf-eval-dnf x a)
             (cnf-dnf-eval-dnf y a)))
  :hints (("Goal" :induct (revappend x y)
           :in-theory (enable cnf-dnf-eval-dnf revappend))))

(defthm cnf-dnf-eval-cnf-when-not-consp
  (implies (not (consp clauses))
           (equal (cnf-dnf-eval-cnf clauses a)
                  t))
  :hints (("Goal" :in-theory (enable cnf-dnf-eval-cnf))))

(defthm cnf-dnf-eval-dnf-when-not-consp
  (implies (not (consp clauses))
           (equal (cnf-dnf-eval-dnf clauses a)
                  nil))
  :hints (("Goal" :in-theory (enable cnf-dnf-eval-dnf))))

(defthm cnf-dnf-eval-cnf-of-reverse
  (equal (cnf-dnf-eval-cnf (reverse x) a)
         (cnf-dnf-eval-cnf x a))
  :hints (("Goal" :in-theory (enable reverse))))

(defthm cnf-dnf-eval-dnf-of-reverse
  (equal (cnf-dnf-eval-dnf (reverse x) a)
         (cnf-dnf-eval-dnf x a))
  :hints (("Goal" :in-theory (enable reverse))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; CROSS-PROD of two DNFs is their conjunction, and of two CNFs is their
;; disjunction.

(defthm cnf-dnf-eval-dnf-of-cross-prod1
  (equal (cnf-dnf-eval-dnf (cross-prod1 lst lst-lst acc) a)
         (or (and (cnf-dnf-eval-conjunction lst a)
                  (cnf-dnf-eval-dnf lst-lst a))
             (cnf-dnf-eval-dnf acc a)))
  :hints (("Goal" :induct (cross-prod1 lst lst-lst acc)
           :in-theory (enable cross-prod1 cnf-dnf-eval-dnf))))

(defthm cnf-dnf-eval-cnf-of-cross-prod1
  (equal (cnf-dnf-eval-cnf (cross-prod1 lst lst-lst acc) a)
         (and (or (cnf-dnf-eval-disjunction lst a)
                  (cnf-dnf-eval-cnf lst-lst a))
              (cnf-dnf-eval-cnf acc a)))
  :hints (("Goal" :induct (cross-prod1 lst lst-lst acc)
           :in-theory (enable cross-prod1 cnf-dnf-eval-cnf))))

(defthm cnf-dnf-eval-dnf-of-cross-prod2
  (equal (cnf-dnf-eval-dnf (cross-prod2 lst1 lst2 acc) a)
         (or (and (cnf-dnf-eval-dnf lst1 a)
                  (cnf-dnf-eval-dnf lst2 a))
             (cnf-dnf-eval-dnf acc a)))
  :hints (("Goal" :induct (cross-prod2 lst1 lst2 acc)
           :in-theory (enable cross-prod2 cnf-dnf-eval-dnf))))

(defthm cnf-dnf-eval-cnf-of-cross-prod2
  (equal (cnf-dnf-eval-cnf (cross-prod2 lst1 lst2 acc) a)
         (and (or (cnf-dnf-eval-cnf lst1 a)
                  (cnf-dnf-eval-cnf lst2 a))
              (cnf-dnf-eval-cnf acc a)))
  :hints (("Goal" :induct (cross-prod2 lst1 lst2 acc)
           :in-theory (enable cross-prod2 cnf-dnf-eval-cnf))))

(defthm cnf-dnf-eval-dnf-of-cross-prod
  (equal (cnf-dnf-eval-dnf (cross-prod lst1 lst2) a)
         (and (cnf-dnf-eval-dnf lst1 a)
              (cnf-dnf-eval-dnf lst2 a)))
  :hints (("Goal" :in-theory (enable cross-prod cnf-dnf-eval-dnf))))

(defthm cnf-dnf-eval-cnf-of-cross-prod
  (equal (cnf-dnf-eval-cnf (cross-prod lst1 lst2) a)
         (or (cnf-dnf-eval-cnf lst1 a)
             (cnf-dnf-eval-cnf lst2 a)))
  :hints (("Goal" :in-theory (enable cross-prod cnf-dnf-eval-cnf))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; CNF-DNF is wrong when TERM is a call of NOT: it calls itself on the argument
;; of the NOT with CNFP negated, so the result for the argument is read in the
;; wrong normal form.  See cnf-dnf-incorrect-for-not and
;; split-on-conjoined-disjunctions-incorrect-for-not in cnf-dnf-tests.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The fix: in the NOT case, pass CNFP unchanged.  This is CNF-DNF from
;; tau.lisp with just that change.
(defun cnf-dnf-fixed (sign term cnfp)
  (cond
   ((variablep term)
    (list (list (if sign term (list 'NOT term)))))
   ((fquotep term)
    (let ((val (if (eq (cadr term) nil) (not sign) sign)))
      (if val
          (if cnfp
              nil               ; (AND) = T
              '(nil))           ; (OR (AND)) = T
          (if cnfp
              '(nil)            ; (AND (OR)) = NIL
              nil))))           ; (OR) = NIL
   ((eq (ffn-symb term) 'NOT)
    (cnf-dnf-fixed (not sign) (fargn term 1) cnfp)) ; was (not cnfp)
   ((eq (ffn-symb term) 'IF)
    (let ((x (fargn term 1))
          (y (fargn term 2))
          (z (fargn term 3))
          (cnfp1 (if sign cnfp (not cnfp))))
      (cond ((equal z *nil*) ; (AND x y)
             (if cnfp1
                 (append (cnf-dnf-fixed sign x cnfp)
                         (cnf-dnf-fixed sign y cnfp))
                 (cross-prod (cnf-dnf-fixed sign x cnfp)
                             (cnf-dnf-fixed sign y cnfp))))
            ((equal y *nil*) ; (AND (NOT x) z)
             (if cnfp1
                 (append (cnf-dnf-fixed (not sign) x cnfp)
                         (cnf-dnf-fixed sign z cnfp))
                 (cross-prod (cnf-dnf-fixed (not sign) x cnfp)
                             (cnf-dnf-fixed sign z cnfp))))
            ((equal z *t*) ; (OR (NOT x) y)
             (if cnfp1
                 (cross-prod (cnf-dnf-fixed (not sign) x cnfp)
                             (cnf-dnf-fixed sign y cnfp))
                 (append (cnf-dnf-fixed (not sign) x cnfp)
                         (cnf-dnf-fixed sign y cnfp))))
            ((or (equal x y)    ; (OR x z)
                 (equal y *t*))
             (if cnfp1
                 (cross-prod (cnf-dnf-fixed sign x cnfp)
                             (cnf-dnf-fixed sign z cnfp))
                 (append (cnf-dnf-fixed sign x cnfp)
                         (cnf-dnf-fixed sign z cnfp))))
            (t (list (list (if sign term (list 'NOT term))))))))
   (t (list (list (if sign term (list 'NOT term)))))))

(local
 (defthm cnf-dnf-eval-cnf-of-singleton-singleton
   (equal (cnf-dnf-eval-cnf (list (list lit)) a)
          (if (cnf-dnf-eval lit a) t nil))
   :hints (("Goal" :in-theory (enable cnf-dnf-eval-cnf cnf-dnf-eval-disjunction)))))

(local
 (defthm cnf-dnf-eval-dnf-of-singleton-singleton
   (equal (cnf-dnf-eval-dnf (list (list lit)) a)
          (if (cnf-dnf-eval lit a) t nil))
   :hints (("Goal" :in-theory (enable cnf-dnf-eval-dnf cnf-dnf-eval-conjunction)))))

;; The fixed version is correct: its result, read as a CNF if CNFP and as a
;; DNF otherwise, is equivalent to TERM if SIGN, and to its negation
;; otherwise.
(defthm cnf-dnf-fixed-correct
  (iff (if cnfp
           (cnf-dnf-eval-cnf (cnf-dnf-fixed sign term cnfp) a)
         (cnf-dnf-eval-dnf (cnf-dnf-fixed sign term cnfp) a))
       (if sign
           (cnf-dnf-eval term a)
         (not (cnf-dnf-eval term a))))
  :hints (("Goal" :induct (cnf-dnf-fixed sign term cnfp)
           :in-theory (e/d (cnf-dnf-eval-cnf cnf-dnf-eval-dnf
                                cnf-dnf-eval-disjunction cnf-dnf-eval-conjunction
                                cnf-dnf-eval-of-fncall-args)
                           (cnf-dnf-eval-of-fncall-args-back)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; SPLIT-ON-CONJOINED-DISJUNCTIONS and
;; SPLIT-ON-CONJOINED-DISJUNCTIONS-IN-HYPS-OF-PAIRS are correct provided
;; CNF-DNF is correct on the hypotheses (as it would be with the fix above).

;; CNF-DNF gives a correct DNF for each of the TERMS.
(defund cnf-dnf-correct-on-termsp (terms a)
  (if (endp terms)
      t
    (and (iff (cnf-dnf-eval-dnf (cnf-dnf t (car terms) nil) a)
              (cnf-dnf-eval (car terms) a))
         (cnf-dnf-correct-on-termsp (cdr terms) a))))

;; The (implicitly conjoined) list of hypotheses becomes a list of lists of
;; hypotheses whose disjunction is equivalent to it.  (An empty list of
;; hypotheses gives NIL, which split-on-conjoined-disjunctions-in-hyps-of-pairs
;; checks for.)
(defthm split-on-conjoined-disjunctions-correct
  (implies (and (cnf-dnf-correct-on-termsp lst a)
                (consp lst))
           (iff (cnf-dnf-eval-dnf (split-on-conjoined-disjunctions lst) a)
                (cnf-dnf-eval-conjunction lst a)))
  :hints (("Goal" :in-theory (enable split-on-conjoined-disjunctions
                                     cnf-dnf-correct-on-termsp
                                     cnf-dnf-eval-conjunction))))

;; The meaning of a list of (hyps . concl) pairs: each conjunction of
;; hypotheses implies its conclusion.
(defund cnf-dnf-eval-pairs (pairs a)
  (if (endp pairs)
      t
    (and (implies (cnf-dnf-eval-conjunction (car (car pairs)) a)
                  (cnf-dnf-eval (cdr (car pairs)) a))
         (cnf-dnf-eval-pairs (cdr pairs) a))))

(defthm cnf-dnf-eval-pairs-of-append
  (equal (cnf-dnf-eval-pairs (append x y) a)
         (and (cnf-dnf-eval-pairs x a)
              (cnf-dnf-eval-pairs y a)))
  :hints (("Goal" :in-theory (enable cnf-dnf-eval-pairs append))))

(local
 (defthm cnf-dnf-eval-pairs-of-pairlis-x2
   (implies (implies (cnf-dnf-eval-dnf hyps-lst a)
                     (cnf-dnf-eval concl a))
            (cnf-dnf-eval-pairs (pairlis-x2 hyps-lst concl) a))
   :hints (("Goal" :in-theory (enable cnf-dnf-eval-pairs pairlis-x2 cnf-dnf-eval-dnf)))))

(local
 (defthm consp-when-consp-of-split-on-conjoined-disjunctions
   (implies (consp (split-on-conjoined-disjunctions lst))
            (consp lst))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable split-on-conjoined-disjunctions)))))

;; CNF-DNF gives a correct DNF for the hypotheses of each pair.
(defund cnf-dnf-correct-on-hyps-of-pairsp (pairs a)
  (if (endp pairs)
      t
    (and (cnf-dnf-correct-on-termsp (car (car pairs)) a)
         (cnf-dnf-correct-on-hyps-of-pairsp (cdr pairs) a))))

;; Splitting the hypotheses of the pairs preserves their truth.  (So, since a
;; theorem's pairs are true for every alist, so are the pairs from which tau
;; rules are made.)
(defthm split-on-conjoined-disjunctions-in-hyps-of-pairs-correct
  (implies (and (cnf-dnf-eval-pairs pairs a)
                (cnf-dnf-correct-on-hyps-of-pairsp pairs a))
           (cnf-dnf-eval-pairs (split-on-conjoined-disjunctions-in-hyps-of-pairs pairs) a))
  :hints (("Goal" :in-theory (enable split-on-conjoined-disjunctions-in-hyps-of-pairs
                                     cnf-dnf-eval-pairs
                                     cnf-dnf-correct-on-hyps-of-pairsp))))
