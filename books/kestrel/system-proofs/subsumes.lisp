; Correctness of the ACL2 system functions for clause subsumption
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Clause CL1 subsumes clause CL2 if some instance of CL1 is a subset of CL2.
;; Then if CL1 is a theorem, so is CL2.  SUBSUMES (in simplify.lisp) checks
;; this, using one-way-unify1 to find the instance, and with two extensions: a
;; literal (EQUAL x 'c1) of CL1 is also absorbed by a literal (NOT (EQUAL a
;; 'c2)) of CL2 when x matches a and 'c1 and 'c2 are different constants, and
;; "extra-info" literals are ignored.  ACL2 uses subsumption for :BY hints, to
;; prove goals that are instances of built-in clauses, to check :EQUIVALENCE
;; rules, and to discard goals in the induction pool that are subsumed by other
;; goals.  The search can be limited by a count of the calls of
;; one-way-unify1, in which case SUBSUMES may return '? ("don't know").
;;
;; This book proves that when SUBSUMES returns T and CL1 is valid (true under
;; all alists), CL2 is true, and similarly for the functions that check
;; subsumption between sets of clauses.  For CLAUSE-SET-SUBSUMES, which
;; checks that every clause of one set is subsumed by some clause of another,
;; this holds only without a limit (as for :BY hints).  With a limit, it can
;; return T after giving up on a clause: see the counterexample in
;; subsumes-tests.lisp.  A copy of it with a one-line fix is correct.  When the
;; fix is made in the sources, that counterexample theorem will fail; the
;; theorems about the fixed copy should then hold for clause-set-subsumes
;; itself.

; cert_param: (non-acl2r)

(include-book "kestrel/evaluators/defevaluator-plus" :dir :system)
(include-book "kestrel/alists-light/alists-equiv-on" :dir :system)
(local (include-book "one-way-unify"))
(local (include-book "helpers"))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/terms-light/termp" :dir :system))
(local (include-book "tools/flag" :dir :system))

;; These functions are in :program mode in the sources.  We put them in
;; :logic mode here.  The measures are ordinals of the form w*m+n, where m
;; measures CL1 (for the -rec functions) or TL1 and n measures TL2: each call
;; either shortens CL1/TL1 or keeps it and shortens TL2.  (The functions test
;; for the end of a list with NULL, so they can recur once on a non-NIL atom;
;; the measures make NIL smaller than any other atom.)  The measures ignore
;; COUNT.  Since the bodies of the count-limited functions are wrapped in THE,
;; we need :RULER-EXTENDERS :ALL for the tests in the bodies to govern the
;; recursive calls.  We do not verify guards, which involve fixnum
;; declarations.
(verify-termination extra-info-lit-p)

(verify-termination
  (subsumes!-rec (declare (xargs :measure (make-ord 1 (+ 1 (if (null cl1) 0 (+ 1 (acl2-count cl1)))) 0))))
  (subsumes!1-equality-with-const (declare (xargs :measure (make-ord 1
                                                                     (+ 1 (if (null tl1) 0 (+ 1 (acl2-count tl1))))
                                                                     (+ 1 (if (null tl2) 0 (+ 1 (acl2-count tl2))))))))
  (subsumes!1 (declare (xargs :measure (make-ord 1
                                                 (+ 1 (if (null tl1) 0 (+ 1 (acl2-count tl1))))
                                                 (+ 1 (if (null tl2) 0 (+ 1 (acl2-count tl2)))))))))

(verify-termination
  (subsumes-rec (declare (xargs :measure (make-ord 1 (+ 1 (if (null cl1) 0 (+ 1 (acl2-count cl1)))) 0)
                                :ruler-extenders :all
                                :verify-guards nil)))
  (subsumes1-equality-with-const (declare (xargs :measure (make-ord 1
                                                                    (+ 1 (if (null tl1) 0 (+ 1 (acl2-count tl1))))
                                                                    (+ 1 (if (null tl2) 0 (+ 1 (acl2-count tl2)))))
                                                 :ruler-extenders :all
                                                 :verify-guards nil)))
  (subsumes1 (declare (xargs :measure (make-ord 1
                                                (+ 1 (if (null tl1) 0 (+ 1 (acl2-count tl1))))
                                                (+ 1 (if (null tl2) 0 (+ 1 (acl2-count tl2)))))
                             :ruler-extenders :all
                             :verify-guards nil))))

(verify-termination subsumes (declare (xargs :verify-guards nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The count-limited search succeeds only if the unlimited search does

(local (make-flag subsumes-rec :ruler-extenders :all))

(local (in-theory (disable one-way-unify1 one-way-unify1-lst one-way-unify1-equal
                            one-way-unify1-equal1)))

(local
 (defthm-flag-subsumes-rec
   (defthm integerp-of-subsumes-rec
     (implies (integerp count)
              (integerp (subsumes-rec count cl1 cl2 alist)))
     :rule-classes (:rewrite :type-prescription)
     :flag subsumes-rec)
   (defthm integerp-of-subsumes1-equality-with-const
     (implies (integerp count)
              (integerp (subsumes1-equality-with-const count lit x const1 tl1 tl2 cl2 alist)))
     :rule-classes (:rewrite :type-prescription)
     :flag subsumes1-equality-with-const)
   (defthm integerp-of-subsumes1
     (implies (integerp count)
              (integerp (subsumes1 count lit tl1 tl2 cl2 alist)))
     :rule-classes (:rewrite :type-prescription)
     :flag subsumes1)
   :hints (("Goal" :in-theory (enable subsumes-rec subsumes1-equality-with-const subsumes1)))))

;; The COUNT passed in by callers is a natural number.
(local
 (defthm-flag-subsumes-rec
   (defthm subsumes!-rec-when-subsumes-rec
     (implies (and (< 0 (subsumes-rec count cl1 cl2 alist))
                   (natp count))
              (subsumes!-rec cl1 cl2 alist))
     :flag subsumes-rec)
   (defthm subsumes!1-equality-with-const-when-subsumes1-equality-with-const
     (implies (and (< 0 (subsumes1-equality-with-const count lit x const1 tl1 tl2 cl2 alist))
                   (natp count))
              (subsumes!1-equality-with-const lit x const1 tl1 tl2 cl2 alist))
     :flag subsumes1-equality-with-const)
   (defthm subsumes!1-when-subsumes1
     (implies (and (< 0 (subsumes1 count lit tl1 tl2 cl2 alist))
                   (natp count))
              (subsumes!1 lit tl1 tl2 cl2 alist))
     :flag subsumes1)
   :hints (("Goal" :in-theory (enable subsumes-rec subsumes1-equality-with-const subsumes1
                                      subsumes!-rec subsumes!1-equality-with-const subsumes!1)))))

;; If SUBSUMES returns T, then the unlimited search succeeds.
(defthm subsumes!-rec-when-subsumes
  (implies (and (equal (subsumes count cl1 cl2 alist) t)
                (or (natp count)
                    (null count)))
           (subsumes!-rec cl1 cl2 alist))
  :hints (("Goal" :in-theory (enable subsumes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; An evaluator

;; An evaluator that knows the functions that one-way-unify1 treats specially,
;; plus IF (for disjunctions), NOT, and EXTRA-INFO (an "extra-info" literal is
;; (NOT (EXTRA-INFO ...)), which is always false).
(defevaluator+ subsumes-eval
  binary-+ binary-* unary-- unary-/ intern-in-package-of-symbol coerce cons equal
  if not extra-info)

;; Evaluate the terms in the range of ALIST.
(defund subsumes-eval-alist (alist a)
  (if (endp alist)
      nil
    (cons (cons (caar alist) (subsumes-eval (cdar alist) a))
          (subsumes-eval-alist (cdr alist) a))))

(defthm assoc-equal-of-subsumes-eval-alist
  (implies (alistp alist)
           (equal (assoc-equal key (subsumes-eval-alist alist a))
                  (let ((pair (assoc-equal key alist)))
                    (and pair
                         (cons key (subsumes-eval (cdr pair) a))))))
  :hints (("Goal" :in-theory (enable subsumes-eval-alist assoc-equal alistp))))

(local (in-theory (enable subsumes-eval-of-disjoin)))

(local
 (defthm extra-info-lit-is-false
   (implies (extra-info-lit-p lit)
            (not (subsumes-eval lit a)))
   :hints (("Goal" :in-theory (enable extra-info-lit-p extra-info)))))

;; The correctness of one-way-unify1, for this evaluator:
(local
 (defthm one-way-unify1-correct-for-subsumes-eval
   (implies (and (mv-nth 0 (one-way-unify1 pat term alist))
                 (alists-equiv-on (strip-cars (mv-nth 1 (one-way-unify1 pat term alist)))
                                  b
                                  (subsumes-eval-alist (mv-nth 1 (one-way-unify1 pat term alist)) a))
                 (alistp alist)
                 (termp pat w)
                 (termp term w)
                 (equal (arity 'equal w) 2)
                 (equal (arity 'cons w) 2)
                 (equal (arity 'intern-in-package-of-symbol w) 2))
            (equal (subsumes-eval pat b)
                   (subsumes-eval term a)))
   :hints (("Goal" :in-theory (e/d (subsumes-eval-of-fncall-args subsumes-eval-alist)
                                   (subsumes-eval-of-fncall-args-back))
            :use (:functional-instance one-way-unify1-correct
                                       (one-way-unify-eval subsumes-eval)
                                       (one-way-unify-eval-list subsumes-eval-list)
                                       (one-way-unify-eval-alist subsumes-eval-alist))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The substitution found by the unlimited search

;; Like the subsumes!-rec nest, but also returns the substitution that
;; instantiates CL1 into (a subset of, modulo the extensions) CL2.
(mutual-recursion
 (defun subsumes!-rec-alist (cl1 cl2 alist)
   (declare (xargs :measure (make-ord 1 (+ 1 (if (null cl1) 0 (+ 1 (acl2-count cl1)))) 0)
                   :verify-guards nil))
   (cond ((null cl1) (mv t alist))
         ((extra-info-lit-p (car cl1))
          (subsumes!-rec-alist (cdr cl1) cl2 alist))
         ((ffn-symb-p (car cl1) 'equal)
          (cond ((quotep (fargn (car cl1) 1))
                 (subsumes!1-equality-with-const-alist (car cl1)
                                                       (fargn (car cl1) 2)
                                                       (fargn (car cl1) 1)
                                                       (cdr cl1) cl2 cl2 alist))
                ((quotep (fargn (car cl1) 2))
                 (subsumes!1-equality-with-const-alist (car cl1)
                                                       (fargn (car cl1) 1)
                                                       (fargn (car cl1) 2)
                                                       (cdr cl1) cl2 cl2 alist))
                (t (subsumes!1-alist (car cl1) (cdr cl1) cl2 cl2 alist))))
         (t (subsumes!1-alist (car cl1) (cdr cl1) cl2 cl2 alist))))

 (defun subsumes!1-equality-with-const-alist (lit x const1 tl1 tl2 cl2 alist)
   (declare (xargs :measure (make-ord 1
                                      (+ 1 (if (null tl1) 0 (+ 1 (acl2-count tl1))))
                                      (+ 1 (if (null tl2) 0 (+ 1 (acl2-count tl2)))))))
   (cond ((null tl2) (mv nil nil))
         ((extra-info-lit-p (car tl2))
          (subsumes!1-equality-with-const-alist lit x const1 tl1 (cdr tl2) cl2 alist))
         ((and (ffn-symb-p (car tl2) 'not)
               (ffn-symb-p (fargn (car tl2) 1) 'equal))
          (let ((arg1 (fargn (fargn (car tl2) 1) 1))
                (arg2 (fargn (fargn (car tl2) 1) 2)))
            (cond ((and (quotep arg1)
                        (not (equal arg1 const1)))
                   (mv-let (wonp alist1)
                     (one-way-unify1 x arg2 alist)
                     (mv-let (flg final)
                       (if wonp (subsumes!-rec-alist tl1 cl2 alist1) (mv nil nil))
                       (if flg
                           (mv t final)
                         (subsumes!1-equality-with-const-alist lit x const1 tl1 (cdr tl2) cl2 alist)))))
                  ((and (quotep arg2)
                        (not (equal arg2 const1)))
                   (mv-let (wonp alist1)
                     (one-way-unify1 x arg1 alist)
                     (mv-let (flg final)
                       (if wonp (subsumes!-rec-alist tl1 cl2 alist1) (mv nil nil))
                       (if flg
                           (mv t final)
                         (subsumes!1-equality-with-const-alist lit x const1 tl1 (cdr tl2) cl2 alist)))))
                  (t (subsumes!1-equality-with-const-alist lit x const1 tl1 (cdr tl2) cl2 alist)))))
         (t (mv-let (wonp alist1)
              (one-way-unify1 lit (car tl2) alist)
              (mv-let (flg final)
                (if wonp (subsumes!-rec-alist tl1 cl2 alist1) (mv nil nil))
                (if flg
                    (mv t final)
                  (subsumes!1-equality-with-const-alist lit x const1 tl1 (cdr tl2) cl2 alist)))))))

 (defun subsumes!1-alist (lit tl1 tl2 cl2 alist)
   (declare (xargs :measure (make-ord 1
                                      (+ 1 (if (null tl1) 0 (+ 1 (acl2-count tl1))))
                                      (+ 1 (if (null tl2) 0 (+ 1 (acl2-count tl2)))))))
   (cond ((null tl2) (mv nil nil))
         ((extra-info-lit-p (car tl2))
          (subsumes!1-alist lit tl1 (cdr tl2) cl2 alist))
         (t (mv-let (wonp alist1)
              (one-way-unify1 lit (car tl2) alist)
              (mv-let (flg final)
                (if wonp (subsumes!-rec-alist tl1 cl2 alist1) (mv nil nil))
                (if flg
                    (mv t final)
                  (subsumes!1-alist lit tl1 (cdr tl2) cl2 alist))))))))

(local (make-flag subsumes!-rec-alist))

(local (include-book "tools/mv-nth" :dir :system))
(local (in-theory (disable mv-nth)))

;; The search succeeds exactly when the unlimited search in the sources does.
(local
 (defthm-flag-subsumes!-rec-alist
   (defthm mv-nth-0-of-subsumes!-rec-alist
     (equal (mv-nth 0 (subsumes!-rec-alist cl1 cl2 alist))
            (subsumes!-rec cl1 cl2 alist))
     :flag subsumes!-rec-alist)
   (defthm mv-nth-0-of-subsumes!1-equality-with-const-alist
     (equal (mv-nth 0 (subsumes!1-equality-with-const-alist lit x const1 tl1 tl2 cl2 alist))
            (subsumes!1-equality-with-const lit x const1 tl1 tl2 cl2 alist))
     :flag subsumes!1-equality-with-const-alist)
   (defthm mv-nth-0-of-subsumes!1-alist
     (equal (mv-nth 0 (subsumes!1-alist lit tl1 tl2 cl2 alist))
            (subsumes!1 lit tl1 tl2 cl2 alist))
     :flag subsumes!1-alist)
   :hints (("Goal" :in-theory (enable subsumes!-rec subsumes!1-equality-with-const subsumes!1)))))

(local
 (defthm-flag-subsumes!-rec-alist
   (defthm alistp-of-mv-nth-1-of-subsumes!-rec-alist
     (implies (alistp alist)
              (alistp (mv-nth 1 (subsumes!-rec-alist cl1 cl2 alist))))
     :flag subsumes!-rec-alist)
   (defthm alistp-of-mv-nth-1-of-subsumes!1-equality-with-const-alist
     (implies (alistp alist)
              (alistp (mv-nth 1 (subsumes!1-equality-with-const-alist lit x const1 tl1 tl2 cl2 alist))))
     :flag subsumes!1-equality-with-const-alist)
   (defthm alistp-of-mv-nth-1-of-subsumes!1-alist
     (implies (alistp alist)
              (alistp (mv-nth 1 (subsumes!1-alist lit tl1 tl2 cl2 alist))))
     :flag subsumes!1-alist)
   :hints (("Goal" :expand ((subsumes!-rec-alist cl1 cl2 alist)
                            (subsumes!1-equality-with-const-alist lit x const1 tl1 tl2 cl2 alist)
                            (subsumes!1-alist lit tl1 tl2 cl2 alist))))))

;; The substitution found extends ALIST.
(local
 (defthm-flag-subsumes!-rec-alist
   (defthm assoc-equal-of-mv-nth-1-of-subsumes!-rec-alist
     (implies (and (mv-nth 0 (subsumes!-rec-alist cl1 cl2 alist))
                   (assoc-equal key alist))
              (equal (assoc-equal key (mv-nth 1 (subsumes!-rec-alist cl1 cl2 alist)))
                     (assoc-equal key alist)))
     :flag subsumes!-rec-alist)
   (defthm assoc-equal-of-mv-nth-1-of-subsumes!1-equality-with-const-alist
     (implies (and (mv-nth 0 (subsumes!1-equality-with-const-alist lit x const1 tl1 tl2 cl2 alist))
                   (assoc-equal key alist))
              (equal (assoc-equal key (mv-nth 1 (subsumes!1-equality-with-const-alist lit x const1 tl1 tl2 cl2 alist)))
                     (assoc-equal key alist)))
     :flag subsumes!1-equality-with-const-alist)
   (defthm assoc-equal-of-mv-nth-1-of-subsumes!1-alist
     (implies (and (mv-nth 0 (subsumes!1-alist lit tl1 tl2 cl2 alist))
                   (assoc-equal key alist))
              (equal (assoc-equal key (mv-nth 1 (subsumes!1-alist lit tl1 tl2 cl2 alist)))
                     (assoc-equal key alist)))
     :flag subsumes!1-alist)
   :hints (("Goal" :expand ((subsumes!-rec-alist cl1 cl2 alist)
                            (subsumes!1-equality-with-const-alist lit x const1 tl1 tl2 cl2 alist)
                            (subsumes!1-alist lit tl1 tl2 cl2 alist))))))

;; Whether S and ALIST bind each of the KEYS in the same way.
(local
 (defun agree-on-keys (keys s alist)
   (if (endp keys)
       t
     (and (equal (assoc-equal (car keys) s)
                 (assoc-equal (car keys) alist))
          (agree-on-keys (cdr keys) s alist)))))

(local
 (defthm assoc-equal-of-mv-nth-1-of-subsumes!-rec-alist-when-member-equal
   (implies (and (mv-nth 0 (subsumes!-rec-alist cl1 cl2 alist))
                 (member-equal key (strip-cars alist))
                 (alistp alist))
            (equal (assoc-equal key (mv-nth 1 (subsumes!-rec-alist cl1 cl2 alist)))
                   (assoc-equal key alist)))
   :hints (("Goal" :use (assoc-equal-of-mv-nth-1-of-subsumes!-rec-alist
                         assoc-equal-iff-member-equal-of-strip-cars)
            :in-theory (disable assoc-equal-of-mv-nth-1-of-subsumes!-rec-alist
                                mv-nth-0-of-subsumes!-rec-alist
                                subsumes!-rec-alist)))))

(local
 (defthm agree-on-keys-of-mv-nth-1-of-subsumes!-rec-alist
   (implies (and (mv-nth 0 (subsumes!-rec-alist cl1 cl2 alist))
                 (subsetp-equal keys (strip-cars alist))
                 (alistp alist))
            (agree-on-keys keys (mv-nth 1 (subsumes!-rec-alist cl1 cl2 alist)) alist))
   :hints (("Goal" :in-theory (e/d (subsetp-equal)
                                   (mv-nth-0-of-subsumes!-rec-alist
                                    subsumes!-rec-alist))))))

(local
 (defthm alists-equiv-on-of-subsumes-eval-alist-and-subsumes-eval-alist-when-agree-on-keys
   (implies (and (agree-on-keys keys s alist)
                 (alistp s)
                 (alistp alist))
            (alists-equiv-on keys (subsumes-eval-alist s a) (subsumes-eval-alist alist a)))
   :hints (("Goal" :in-theory (enable alists-equiv-on)))))

;; The evaluated substitution found agrees with the evaluated input ALIST on
;; the keys of ALIST.
(local
 (defthm alists-equiv-on-of-subsumes-eval-alist-of-mv-nth-1-of-subsumes!-rec-alist
   (implies (and (mv-nth 0 (subsumes!-rec-alist cl1 cl2 alist))
                 (alistp alist))
            (alists-equiv-on (strip-cars alist)
                             (subsumes-eval-alist (mv-nth 1 (subsumes!-rec-alist cl1 cl2 alist)) a)
                             (subsumes-eval-alist alist a)))
   :hints (("Goal" :in-theory (disable subsumes!-rec-alist)))))

;; Facts about terms:

(local
 (defthm termp-of-args-of-equal
   (implies (and (termp lit w)
                 (consp lit)
                 (equal (car lit) 'equal)
                 (equal (arity 'equal w) 2))
            (and (termp (cadr lit) w)
                 (termp (caddr lit) w)))
   :hints (("Goal" :expand ((termp lit w)
                            (term-listp (cdr lit) w)
                            (term-listp (cddr lit) w))))))

(local
 (defthm termp-of-args-of-equal-under-not
   (implies (and (termp lit w)
                 (consp lit)
                 (equal (car lit) 'not)
                 (consp (cadr lit))
                 (equal (car (cadr lit)) 'equal)
                 (equal (arity 'equal w) 2))
            (and (termp (cadr (cadr lit)) w)
                 (termp (caddr (cadr lit)) w)))
   :hints (("Goal" :use (:instance termp-of-args-of-equal (lit (cadr lit)))
            :expand ((termp lit w)
                     (term-listp (cdr lit) w))
            :in-theory (disable termp-of-args-of-equal)))))

(local
 (defthm termp-of-car-when-term-listp-local
   (implies (and (term-listp x w)
                 (consp x))
            (termp (car x) w))))

(local
 (defthm term-listp-of-cdr-when-term-listp-local
   (implies (term-listp x w)
            (term-listp (cdr x) w))))

(local
 (defthm consp-when-term-listp-local
   (implies (and (term-listp x w)
                 x)
            (consp x))))

(local
 (defthm not-subsumes-eval-of-car-when-all-eval-to-false-with-subsumes-eval
   (implies (and (all-eval-to-false-with-subsumes-eval x a)
                 (consp x))
            (not (subsumes-eval (car x) a)))
   :hints (("Goal" :in-theory (enable all-eval-to-false-with-subsumes-eval)))))

(local
 (defthm all-eval-to-false-with-subsumes-eval-of-cdr
   (implies (all-eval-to-false-with-subsumes-eval x a)
            (all-eval-to-false-with-subsumes-eval (cdr x) a))
   :hints (("Goal" :in-theory (enable all-eval-to-false-with-subsumes-eval)))))

;; Distinct quoted constants have distinct values.
(local
 (defthm not-equal-of-cadr-and-cadr-when-quoted-termps
   (implies (and (not (equal q1 q2))
                 (quotep q1)
                 (quotep q2)
                 (termp q1 w)
                 (termp q2 w))
            (not (equal (cadr q1) (cadr q2))))
   :hints (("Goal" :expand ((termp q1 w) (termp q2 w))))))

;; A literal matched by one-way-unify1 against a false literal is false under
;; the final substitution.
(local
 (defthm not-subsumes-eval-when-one-way-unify1-and-subsumes!-rec-alist
   (implies (and (mv-nth 0 (one-way-unify1 pat term alist))
                 (mv-nth 0 (subsumes!-rec-alist tl1 cl2 (mv-nth 1 (one-way-unify1 pat term alist))))
                 (not (subsumes-eval term a))
                 (alistp alist)
                 (termp pat w)
                 (termp term w)
                 (equal (arity 'equal w) 2)
                 (equal (arity 'cons w) 2)
                 (equal (arity 'intern-in-package-of-symbol w) 2))
            (not (subsumes-eval pat (subsumes-eval-alist
                                     (mv-nth 1 (subsumes!-rec-alist tl1 cl2 (mv-nth 1 (one-way-unify1 pat term alist))))
                                     a))))
   :hints (("Goal" :use (:instance one-way-unify1-correct-for-subsumes-eval
                                   (b (subsumes-eval-alist
                                       (mv-nth 1 (subsumes!-rec-alist tl1 cl2 (mv-nth 1 (one-way-unify1 pat term alist))))
                                       a)))
            :in-theory (disable one-way-unify1-correct-for-subsumes-eval
                                mv-nth-0-of-subsumes!-rec-alist
                                subsumes!-rec-alist)))))

;; Likewise, with the value of the term instead of its falsity:
(local
 (defthm subsumes-eval-when-one-way-unify1-and-subsumes!-rec-alist
   (implies (and (mv-nth 0 (one-way-unify1 pat term alist))
                 (mv-nth 0 (subsumes!-rec-alist tl1 cl2 (mv-nth 1 (one-way-unify1 pat term alist))))
                 (alistp alist)
                 (termp pat w)
                 (termp term w)
                 (equal (arity 'equal w) 2)
                 (equal (arity 'cons w) 2)
                 (equal (arity 'intern-in-package-of-symbol w) 2))
            (equal (subsumes-eval pat (subsumes-eval-alist
                                       (mv-nth 1 (subsumes!-rec-alist tl1 cl2 (mv-nth 1 (one-way-unify1 pat term alist))))
                                       a))
                   (subsumes-eval term a)))
   :hints (("Goal" :use (:instance one-way-unify1-correct-for-subsumes-eval
                                   (b (subsumes-eval-alist
                                       (mv-nth 1 (subsumes!-rec-alist tl1 cl2 (mv-nth 1 (one-way-unify1 pat term alist))))
                                       a)))
            :in-theory (disable one-way-unify1-correct-for-subsumes-eval
                                mv-nth-0-of-subsumes!-rec-alist
                                subsumes!-rec-alist)))))

;; The main lemma: If the search succeeds and CL2 is false (under A), then CL1
;; is false under the evaluated substitution found.
(local
 (defthm-flag-subsumes!-rec-alist
   (defthm all-eval-to-false-of-cl1-when-subsumes!-rec-alist
     (implies (and (mv-nth 0 (subsumes!-rec-alist cl1 cl2 alist))
                   (all-eval-to-false-with-subsumes-eval cl2 a)
                   (alistp alist)
                   (term-listp cl1 w)
                   (term-listp cl2 w)
                   (equal (arity 'equal w) 2)
                   (equal (arity 'cons w) 2)
                   (equal (arity 'intern-in-package-of-symbol w) 2))
              (all-eval-to-false-with-subsumes-eval
               cl1
               (subsumes-eval-alist (mv-nth 1 (subsumes!-rec-alist cl1 cl2 alist)) a)))
     :flag subsumes!-rec-alist)
   (defthm all-eval-to-false-of-cl1-when-subsumes!1-equality-with-const-alist
     (implies (and (mv-nth 0 (subsumes!1-equality-with-const-alist lit x const1 tl1 tl2 cl2 alist))
                   (all-eval-to-false-with-subsumes-eval cl2 a)
                   (all-eval-to-false-with-subsumes-eval tl2 a)
                   (alistp alist)
                   (consp lit)
                   (equal (car lit) 'equal)
                   (or (and (equal x (cadr lit))
                            (equal const1 (caddr lit)))
                       (and (equal x (caddr lit))
                            (equal const1 (cadr lit))))
                   (quotep const1)
                   (termp lit w)
                   (term-listp tl1 w)
                   (term-listp tl2 w)
                   (term-listp cl2 w)
                   (equal (arity 'equal w) 2)
                   (equal (arity 'cons w) 2)
                   (equal (arity 'intern-in-package-of-symbol w) 2))
              (let ((b (subsumes-eval-alist
                        (mv-nth 1 (subsumes!1-equality-with-const-alist lit x const1 tl1 tl2 cl2 alist))
                        a)))
                (and (not (subsumes-eval lit b))
                     (all-eval-to-false-with-subsumes-eval tl1 b))))
     :flag subsumes!1-equality-with-const-alist)
   (defthm all-eval-to-false-of-cl1-when-subsumes!1-alist
     (implies (and (mv-nth 0 (subsumes!1-alist lit tl1 tl2 cl2 alist))
                   (all-eval-to-false-with-subsumes-eval cl2 a)
                   (all-eval-to-false-with-subsumes-eval tl2 a)
                   (alistp alist)
                   (termp lit w)
                   (term-listp tl1 w)
                   (term-listp tl2 w)
                   (term-listp cl2 w)
                   (equal (arity 'equal w) 2)
                   (equal (arity 'cons w) 2)
                   (equal (arity 'intern-in-package-of-symbol w) 2))
              (let ((b (subsumes-eval-alist
                        (mv-nth 1 (subsumes!1-alist lit tl1 tl2 cl2 alist))
                        a)))
                (and (not (subsumes-eval lit b))
                     (all-eval-to-false-with-subsumes-eval tl1 b))))
     :flag subsumes!1-alist)
   :hints (("Goal" :expand ((subsumes!-rec-alist cl1 cl2 alist)
                            (subsumes!1-equality-with-const-alist lit x const1 tl1 tl2 cl2 alist)
                            (subsumes!1-alist lit tl1 tl2 cl2 alist))
            :in-theory (disable mv-nth-0-of-subsumes!-rec-alist
                                mv-nth-0-of-subsumes!1-equality-with-const-alist
                                mv-nth-0-of-subsumes!1-alist)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Correctness of SUBSUMES

;; If the unlimited search succeeds, then CL1, instantiated by the
;; substitution found (which extends ALIST), implies CL2.
(defthm subsumes!-rec-correct-with-substitution
  (implies (and (subsumes!-rec cl1 cl2 alist)
                (subsumes-eval (disjoin cl1)
                               (subsumes-eval-alist (mv-nth 1 (subsumes!-rec-alist cl1 cl2 alist)) a))
                (alistp alist)
                (term-listp cl1 w)
                (term-listp cl2 w)
                (equal (arity 'equal w) 2)
                (equal (arity 'cons w) 2)
                (equal (arity 'intern-in-package-of-symbol w) 2))
           (subsumes-eval (disjoin cl2) a))
  :hints (("Goal" :use all-eval-to-false-of-cl1-when-subsumes!-rec-alist
           :in-theory (disable all-eval-to-false-of-cl1-when-subsumes!-rec-alist
                               subsumes!-rec-alist))))

(defthm subsumes!-rec-alist-extends-alist
  (implies (and (subsumes!-rec cl1 cl2 alist)
                (assoc-equal key alist))
           (equal (assoc-equal key (mv-nth 1 (subsumes!-rec-alist cl1 cl2 alist)))
                  (assoc-equal key alist)))
  :hints (("Goal" :use assoc-equal-of-mv-nth-1-of-subsumes!-rec-alist
           :in-theory (disable assoc-equal-of-mv-nth-1-of-subsumes!-rec-alist
                               subsumes!-rec-alist))))

;; A clause is valid if it is true under every alist.
(defun-sk subsumes-eval-valid-clausep (cl)
  (forall (a) (subsumes-eval (disjoin cl) a)))

(local (in-theory (disable subsumes-eval-valid-clausep)))

;; If CL1 subsumes CL2 and CL1 is valid, then CL2 is true.
(defthm subsumes!-rec-correct
  (implies (and (subsumes!-rec cl1 cl2 alist)
                (subsumes-eval-valid-clausep cl1)
                (alistp alist)
                (term-listp cl1 w)
                (term-listp cl2 w)
                (equal (arity 'equal w) 2)
                (equal (arity 'cons w) 2)
                (equal (arity 'intern-in-package-of-symbol w) 2))
           (subsumes-eval (disjoin cl2) a))
  :hints (("Goal" :use (subsumes!-rec-correct-with-substitution
                        (:instance subsumes-eval-valid-clausep-necc
                                   (cl cl1)
                                   (a (subsumes-eval-alist (mv-nth 1 (subsumes!-rec-alist cl1 cl2 alist)) a))))
           :in-theory (disable subsumes!-rec-correct-with-substitution
                               subsumes-eval-valid-clausep-necc
                               subsumes!-rec-alist
                               subsumes!-rec
                               subsumes-eval-of-disjoin))))

;; The main theorem about SUBSUMES: If it returns T and CL1 is valid, then CL2
;; is true.  The usual arities are needed for one-way-unify1 (see
;; one-way-unify.lisp).
(defthm subsumes-correct
  (implies (and (equal (subsumes count cl1 cl2 alist) t)
                (or (natp count)
                    (null count))
                (subsumes-eval-valid-clausep cl1)
                (alistp alist)
                (term-listp cl1 w)
                (term-listp cl2 w)
                (equal (arity 'equal w) 2)
                (equal (arity 'cons w) 2)
                (equal (arity 'intern-in-package-of-symbol w) 2))
           (subsumes-eval (disjoin cl2) a))
  :hints (("Goal" :use subsumes!-rec-when-subsumes
           :in-theory (disable subsumes!-rec-when-subsumes subsumes subsumes!-rec
                               subsumes-eval-of-disjoin))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Subsumption by a set of clauses, and between sets of clauses

(verify-termination
  (some-member-subsumes (declare (xargs :measure (if (null cl-set) 0 (+ 1 (acl2-count cl-set)))
                                        :verify-guards nil))))

;; Every clause in the set is valid.
(defund subsumes-eval-valid-clausesp (cl-set)
  (if (endp cl-set)
      t
    (and (subsumes-eval-valid-clausep (car cl-set))
         (subsumes-eval-valid-clausesp (cdr cl-set)))))

;; If some-member-subsumes returns T (and ACC was not T), some member of
;; CL-SET subsumes CL, so CL is true if the members of CL-SET are valid.
(defthm some-member-subsumes-correct
  (implies (and (equal (some-member-subsumes count cl-set cl acc) t)
                (not (equal acc t))
                (or (natp count)
                    (null count))
                (subsumes-eval-valid-clausesp cl-set)
                (term-list-listp cl-set w)
                (term-listp cl w)
                (equal (arity 'equal w) 2)
                (equal (arity 'cons w) 2)
                (equal (arity 'intern-in-package-of-symbol w) 2))
           (subsumes-eval (disjoin cl) a))
  :hints (("Goal" :in-theory (e/d (some-member-subsumes subsumes-eval-valid-clausesp)
                                  (subsumes subsumes-eval-of-disjoin)))))

;; Without a limit, some-member-subsumes never returns '?.
(defthm some-member-subsumes-when-no-limit
  (implies (not (equal acc '?))
           (not (equal (some-member-subsumes nil cl-set cl acc) '?)))
  :hints (("Goal" :in-theory (enable some-member-subsumes subsumes))))

;;; CLAUSE-SET-SUBSUMES (in prove.lisp)

(verify-termination
  (clause-set-subsumes-1 (declare (xargs :measure (if (null cl-set2) 0 (+ 1 (acl2-count cl-set2)))
                                         :verify-guards nil))))
(verify-termination clause-set-subsumes (declare (xargs :verify-guards nil)))

;; All the clauses are true.
(defund subsumes-eval-clauses-true (cl-set a)
  (if (endp cl-set)
      t
    (and (subsumes-eval (disjoin (car cl-set)) a)
         (subsumes-eval-clauses-true (cdr cl-set) a))))

(defthm subsumes-eval-of-conjoin-clauses
  (iff (subsumes-eval (conjoin-clauses cl-set) a)
       (subsumes-eval-clauses-true cl-set a))
  :hints (("Goal" :in-theory (e/d (subsumes-eval-clauses-true conjoin-clauses disjoin-lst)
                                  (subsumes-eval-of-disjoin)))))

(local
 (defthm subsumes-eval-clauses-true-when-valid
   (implies (subsumes-eval-valid-clausesp cl-set)
            (subsumes-eval-clauses-true cl-set a))
   :hints (("Goal" :in-theory (e/d (subsumes-eval-clauses-true subsumes-eval-valid-clausesp)
                                   (subsumes-eval-of-disjoin))))))

(local
 (defthm not-all-eval-to-false-when-subsetp-equal
   (implies (and (subsetp-equal x y)
                 (not (all-eval-to-false-with-subsumes-eval x a)))
            (not (all-eval-to-false-with-subsumes-eval y a)))
   :hints (("Goal" :in-theory (enable subsetp-equal all-eval-to-false-with-subsumes-eval)))))

;; A copy of clause-set-subsumes-1 with the fix: ACC becomes '? once
;; some-member-subsumes returns '?, and stays that way.
(defun clause-set-subsumes-1-fixed (init-subsumes-count cl-set1 cl-set2 acc)
  (declare (xargs :measure (if (null cl-set2) 0 (+ 1 (acl2-count cl-set2)))
                  :verify-guards nil))
  (cond ((null cl-set2) acc)
        (t (let ((temp (some-member-subsumes init-subsumes-count
                                             cl-set1 (car cl-set2) nil)))
             (and temp
                  (clause-set-subsumes-1-fixed init-subsumes-count
                                               cl-set1 (cdr cl-set2)
                                               (if (eq temp t) acc temp)))))))

(defun clause-set-subsumes-fixed (init-subsumes-count cl-set1 cl-set2)
  (declare (xargs :verify-guards nil))
  (or (equal cl-set1 cl-set2)
      (and cl-set1
           cl-set2
           (null (cdr cl-set2))
           (subsetp-equal (car cl-set1) (car cl-set2)))
      (clause-set-subsumes-1-fixed init-subsumes-count cl-set1 cl-set2 t)))

(defthm clause-set-subsumes-1-fixed-correct
  (implies (and (equal (clause-set-subsumes-1-fixed count cl-set1 cl-set2 acc) t)
                (or (natp count)
                    (null count))
                (subsumes-eval-valid-clausesp cl-set1)
                (term-list-listp cl-set1 w)
                (term-list-listp cl-set2 w)
                (equal (arity 'equal w) 2)
                (equal (arity 'cons w) 2)
                (equal (arity 'intern-in-package-of-symbol w) 2))
           (subsumes-eval-clauses-true cl-set2 a))
  :hints (("Goal" :in-theory (e/d (clause-set-subsumes-1-fixed subsumes-eval-clauses-true)
                                  (some-member-subsumes subsumes-eval-of-disjoin)))))

(local
 (defthm not-all-eval-to-false-of-car-when-subsumes-eval-valid-clausesp
   (implies (and (subsumes-eval-valid-clausesp cl-set)
                 (consp cl-set))
            (not (all-eval-to-false-with-subsumes-eval (car cl-set) a)))
   :hints (("Goal" :use (:instance subsumes-eval-valid-clausep-necc (cl (car cl-set)))
            :in-theory (enable subsumes-eval-valid-clausesp)))))

(local
 (defthm consp-when-term-list-listp-local
   (implies (and (term-list-listp x w)
                 x)
            (consp x))))

(local
 (defthm clause-set-subsumes-fixed-correct-helper
   (implies (and (equal (clause-set-subsumes-fixed count cl-set1 cl-set2) t)
                 (or (natp count)
                     (null count))
                 (subsumes-eval-valid-clausesp cl-set1)
                 (term-list-listp cl-set1 w)
                 (term-list-listp cl-set2 w)
                 (equal (arity 'equal w) 2)
                 (equal (arity 'cons w) 2)
                 (equal (arity 'intern-in-package-of-symbol w) 2))
            (subsumes-eval-clauses-true cl-set2 a))
   :hints (("Goal" :use (:instance clause-set-subsumes-1-fixed-correct (acc t))
            :in-theory (e/d (clause-set-subsumes-fixed subsumes-eval-clauses-true)
                            (clause-set-subsumes-1-fixed
                             clause-set-subsumes-1-fixed-correct))))))

;; If the fixed CLAUSE-SET-SUBSUMES returns T, then every clause of CL-SET2 is
;; subsumed by some clause of CL-SET1, so the clauses of CL-SET2 are true if
;; those of CL-SET1 are valid.
(defthm clause-set-subsumes-fixed-correct
  (implies (and (equal (clause-set-subsumes-fixed count cl-set1 cl-set2) t)
                (or (natp count)
                    (null count))
                (subsumes-eval-valid-clausesp cl-set1)
                (term-list-listp cl-set1 w)
                (term-list-listp cl-set2 w)
                (equal (arity 'equal w) 2)
                (equal (arity 'cons w) 2)
                (equal (arity 'intern-in-package-of-symbol w) 2))
           (subsumes-eval (conjoin-clauses cl-set2) a))
  :hints (("Goal" :in-theory (disable conjoin-clauses clause-set-subsumes-fixed))))

;; Without a limit (as for :BY hints), the function in the sources is the same
;; as the fixed one, so it is correct.

(local
 (defthm-flag-subsumes!-rec-alist
   (defthm booleanp-of-mv-nth-0-of-subsumes!-rec-alist
     (booleanp (mv-nth 0 (subsumes!-rec-alist cl1 cl2 alist)))
     :flag subsumes!-rec-alist)
   (defthm booleanp-of-mv-nth-0-of-subsumes!1-equality-with-const-alist
     (booleanp (mv-nth 0 (subsumes!1-equality-with-const-alist lit x const1 tl1 tl2 cl2 alist)))
     :flag subsumes!1-equality-with-const-alist)
   (defthm booleanp-of-mv-nth-0-of-subsumes!1-alist
     (booleanp (mv-nth 0 (subsumes!1-alist lit tl1 tl2 cl2 alist)))
     :flag subsumes!1-alist)
   :hints (("Goal" :expand ((subsumes!-rec-alist cl1 cl2 alist)
                            (subsumes!1-equality-with-const-alist lit x const1 tl1 tl2 cl2 alist)
                            (subsumes!1-alist lit tl1 tl2 cl2 alist))
            :in-theory (disable mv-nth-0-of-subsumes!-rec-alist
                                mv-nth-0-of-subsumes!1-equality-with-const-alist
                                mv-nth-0-of-subsumes!1-alist)))))

(local
 (defthm booleanp-of-subsumes!-rec
   (booleanp (subsumes!-rec cl1 cl2 alist))
   :hints (("Goal" :use booleanp-of-mv-nth-0-of-subsumes!-rec-alist
            :in-theory (disable booleanp-of-mv-nth-0-of-subsumes!-rec-alist)))))

(local
 (defthm booleanp-of-some-member-subsumes-when-no-limit
   (implies (booleanp acc)
            (booleanp (some-member-subsumes nil cl-set cl acc)))
   :hints (("Goal" :in-theory (enable some-member-subsumes subsumes)))))

(local
 (defthm clause-set-subsumes-1-when-no-limit
   (equal (clause-set-subsumes-1 nil cl-set1 cl-set2 t)
          (clause-set-subsumes-1-fixed nil cl-set1 cl-set2 t))
   :hints (("Goal" :in-theory (e/d (clause-set-subsumes-1 clause-set-subsumes-1-fixed)
                                   (some-member-subsumes))
            :induct (clause-set-subsumes-1-fixed nil cl-set1 cl-set2 t))
           (and stable-under-simplificationp
                '(:use (:instance booleanp-of-some-member-subsumes-when-no-limit
                                  (cl-set cl-set1)
                                  (cl (car cl-set2))
                                  (acc nil)))))))

(defthm clause-set-subsumes-correct-when-no-limit
  (implies (and (equal (clause-set-subsumes nil cl-set1 cl-set2) t)
                (subsumes-eval-valid-clausesp cl-set1)
                (term-list-listp cl-set1 w)
                (term-list-listp cl-set2 w)
                (equal (arity 'equal w) 2)
                (equal (arity 'cons w) 2)
                (equal (arity 'intern-in-package-of-symbol w) 2))
           (subsumes-eval (conjoin-clauses cl-set2) a))
  :hints (("Goal" :use (:instance clause-set-subsumes-fixed-correct (count nil))
           :in-theory (e/d (clause-set-subsumes clause-set-subsumes-fixed)
                           (clause-set-subsumes-fixed-correct
                            clause-set-subsumes-fixed-correct-helper
                            conjoin-clauses)))))

;; But with a limit, CLAUSE-SET-SUBSUMES in the sources can return T when it
;; gave up on a clause, if it then succeeds on a later clause: see
;; clause-set-subsumes-can-give-up-and-return-t in subsumes-tests.lisp.
