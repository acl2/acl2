; Correctness of the ACL2 system functions that check whether a clause is
; subsumed by a built-in clause
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; ACL2 stores :BUILT-IN-CLAUSE rules, and some initial built-in clauses, as
;; records in the world, grouped by the top function symbol of each clause.
;; Before simplifying a goal, and when relieving hypotheses, ACL2 checks with
;; BUILT-IN-CLAUSEP1 and BUILT-IN-CLAUSEP2 (in simplify.lisp) whether some
;; enabled built-in clause, whose function symbols all occur in the goal,
;; subsumes the goal.  If so, the goal is proved.  This book proves that this
;; is right: if the stored clauses are valid, then any clause they subsume is
;; true.
;;
;; The results are stated with SUBSUMES-EVAL (see subsumes.lisp), which knows
;; only the functions that one-way-unify1 treats specially.  The built-in
;; clauses mention other functions (such as O< and ACL2-COUNT), so to apply
;; these results to particular built-in clauses, one would functionally
;; instantiate them with an evaluator that also knows those functions.

; cert_param: (non-acl2r)

(include-book "subsumes")
(local (include-book "kestrel/terms-light/termp" :dir :system))

;; These functions are in :program mode in the sources.  We put them in
;; :logic mode here.  They test for the end of a list with NULL, so they can
;; recur once on a non-NIL atom; the measures make NIL smaller than any other
;; atom.
(verify-termination
  (built-in-clausep2 (declare (xargs :measure (if (null bic-lst) 0 (+ 1 (acl2-count bic-lst)))))))
(verify-termination
  (built-in-clausep1 (declare (xargs :measure (if (null bic-alist) 0 (+ 1 (acl2-count bic-alist)))))))

;; A list of built-in clause records whose clauses are valid terms.
(defund valid-built-in-clause-listp (bic-lst w)
  (if (atom bic-lst)
      t
    (and (subsumes-eval-valid-clausep (access built-in-clause (car bic-lst) :clause))
         (term-listp (access built-in-clause (car bic-lst) :clause) w)
         (valid-built-in-clause-listp (cdr bic-lst) w))))

;; An alist whose values are such lists, like the 'built-in-clauses world
;; global.
(defund valid-built-in-clause-alistp (bic-alist w)
  (if (atom bic-alist)
      t
    (and (valid-built-in-clause-listp (cdr (car bic-alist)) w)
         (valid-built-in-clause-alistp (cdr bic-alist) w))))

;; If built-in-clausep2 returns a rune, then CL is true.
(defthm built-in-clausep2-correct
  (implies (and (built-in-clausep2 bic-lst cl fns ens)
                (valid-built-in-clause-listp bic-lst w)
                (term-listp cl w)
                (equal (arity 'equal w) 2)
                (equal (arity 'cons w) 2)
                (equal (arity 'intern-in-package-of-symbol w) 2))
           (subsumes-eval (disjoin cl) a))
  :hints (("Goal" :in-theory (e/d (built-in-clausep2 valid-built-in-clause-listp)
                                  (subsumes subsumes-eval-of-disjoin)))))

(local
 (defthm built-in-clausep2-of-nil
   (equal (built-in-clausep2 nil cl fns ens)
          nil)
   :hints (("Goal" :in-theory (enable built-in-clausep2)))))

;; If built-in-clausep1 returns a rune, then CL is true.
(defthm built-in-clausep1-correct
  (implies (and (built-in-clausep1 bic-alist cl fns ens)
                (valid-built-in-clause-alistp bic-alist w)
                (term-listp cl w)
                (equal (arity 'equal w) 2)
                (equal (arity 'cons w) 2)
                (equal (arity 'intern-in-package-of-symbol w) 2))
           (subsumes-eval (disjoin cl) a))
  :hints (("Goal" :in-theory (e/d (built-in-clausep1 valid-built-in-clause-alistp)
                                  (built-in-clausep2 subsumes-eval-of-disjoin)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The initial built-in clauses

;; ACL2 starts with the built-in clauses in *INITIAL-BUILT-IN-CLAUSES*, which
;; say that ACL2-COUNT is an ordinal and that it decreases under CAR, CDR,
;; subtracting 1, REALPART, and IMAGPART in suitable cases.  ACL2 uses them to
;; prove the measure conjectures of most recursive definitions.  Here we prove
;; that they are valid, so (by functionally instantiating the result above)
;; any clause that built-in-clausep2 finds to be subsumed by one of them is
;; true.

;; An evaluator that knows the functions in the initial built-in clauses and
;; the functions that one-way-unify1 treats specially:
(defevaluator+ bic-eval
  binary-+ binary-* unary-- unary-/ intern-in-package-of-symbol coerce cons
  equal if not extra-info
  acl2-count car cdr o< o-p atom consp endp true-listp eq null integerp < = zp
  realpart imagpart complex-rationalp)

(defun-sk bic-eval-valid-clausep (cl)
  (forall (a) (bic-eval (disjoin cl) a)))

(defund bic-eval-valid-built-in-clause-listp (bic-lst w)
  (if (atom bic-lst)
      t
    (and (bic-eval-valid-clausep (access built-in-clause (car bic-lst) :clause))
         (term-listp (access built-in-clause (car bic-lst) :clause) w)
         (bic-eval-valid-built-in-clause-listp (cdr bic-lst) w))))

;; The result above, for this evaluator:
(defthm built-in-clausep2-correct-for-bic-eval
  (implies (and (built-in-clausep2 bic-lst cl fns ens)
                (bic-eval-valid-built-in-clause-listp bic-lst w)
                (term-listp cl w)
                (equal (arity 'equal w) 2)
                (equal (arity 'cons w) 2)
                (equal (arity 'intern-in-package-of-symbol w) 2))
           (bic-eval (disjoin cl) a))
  :hints (("Goal" :in-theory (e/d (bic-eval-of-fncall-args
                                   bic-eval-valid-built-in-clause-listp)
                                  (bic-eval-of-fncall-args-back
                                   bic-eval-of-disjoin))
           :use (:functional-instance built-in-clausep2-correct
                                      (subsumes-eval bic-eval)
                                      (subsumes-eval-list bic-eval-list)
                                      (subsumes-eval-valid-clausep bic-eval-valid-clausep)
                                      (subsumes-eval-valid-clausep-witness bic-eval-valid-clausep-witness)
                                      (valid-built-in-clause-listp bic-eval-valid-built-in-clause-listp)))
          (and stable-under-simplificationp
               '(:use (:instance bic-eval-valid-clausep-necc
                                 (cl cl)
                                 (a (subsumes-eval-valid-clausep-witness cl)))))))

;; The functions in the initial built-in clauses, and those that
;; one-way-unify1 treats specially, have their usual arities:
(defund initial-built-in-clauses-arities-okp (w)
  (and (equal (arity 'cons w) 2)
       (equal (arity 'intern-in-package-of-symbol w) 2)
       (equal (arity 'acl2-count w) 1)
       (equal (arity 'car w) 1)
       (equal (arity 'cdr w) 1)
       (equal (arity 'o< w) 2)
       (equal (arity 'o-p w) 1)
       (equal (arity 'atom w) 1)
       (equal (arity 'consp w) 1)
       (equal (arity 'not w) 1)
       (equal (arity 'endp w) 1)
       (equal (arity 'true-listp w) 1)
       (equal (arity 'eq w) 2)
       (equal (arity 'equal w) 2)
       (equal (arity 'null w) 1)
       (equal (arity 'integerp w) 1)
       (equal (arity '< w) 2)
       (equal (arity '= w) 2)
       (equal (arity 'zp w) 1)
       (equal (arity 'binary-+ w) 2)
       (equal (arity 'realpart w) 1)
       (equal (arity 'imagpart w) 1)
       (equal (arity 'complex-rationalp w) 1)))

;; The facts about ACL2-COUNT that the initial built-in clauses state:
(local
 (defthm acl2-count-decreases
   (and (implies (consp x)
                 (and (< (acl2-count (car x)) (acl2-count x))
                      (< (acl2-count (cdr x)) (acl2-count x))))
        (implies (and (integerp x)
                      (< 0 x))
                 (< (acl2-count (+ -1 x)) (acl2-count x)))
        (implies (complex-rationalp x)
                 (and (< (acl2-count (realpart x)) (acl2-count x))
                      (< (acl2-count (imagpart x)) (acl2-count x)))))
   :rule-classes :linear
   :hints (("Goal" :expand ((acl2-count x))))))

;; The initial built-in clauses are valid.
(defthm bic-eval-valid-built-in-clause-listp-of-initial-built-in-clauses
  (implies (initial-built-in-clauses-arities-okp w)
           (bic-eval-valid-built-in-clause-listp *initial-built-in-clauses* w))
  :hints (("Goal" :in-theory (e/d (bic-eval-valid-built-in-clause-listp
                                   initial-built-in-clauses-arities-okp
                                   o< o-p o-finp termp term-listp)
                                  (acl2-count)))))

;; So any clause that built-in-clausep2 finds to be subsumed by an initial
;; built-in clause is true.
(defthm built-in-clausep2-of-initial-built-in-clauses-correct
  (implies (and (built-in-clausep2 *initial-built-in-clauses* cl fns ens)
                (term-listp cl w)
                (initial-built-in-clauses-arities-okp w))
           (bic-eval (disjoin cl) a))
  :hints (("Goal" :use (:instance built-in-clausep2-correct-for-bic-eval
                                  (bic-lst *initial-built-in-clauses*))
           :in-theory (e/d (initial-built-in-clauses-arities-okp)
                           (bic-eval-of-disjoin
                            built-in-clausep2-correct-for-bic-eval
                            built-in-clausep2
                            (:e built-in-clausep2))))))
