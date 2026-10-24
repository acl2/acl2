; Correctness of the ACL2 system function one-way-unify
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; ONE-WAY-UNIFY (in translate.lisp) matches a pattern against a term,
;; returning a substitution (an alist from pattern variables to subterms of the
;; term) under which the pattern becomes the term.  It is soundness-critical:
;; the rewriter, type-set, and other parts of the prover use it to decide when
;; a rule applies.  As the source comments put it, "The key fact we use about
;; one-way-unify is just that when it reports (mv T s), pat/s is provably
;; term."  This book proves that fact, in terms of an evaluator.

;; One-way-unify is more than syntactic matching.  It treats binary-+,
;; binary-*, unary--, unary-/, intern-in-package-of-symbol, coerce, and cons as
;; "constructors" that can match constants (e.g., (binary-+ '1 x) matches '7
;; with x bound to '6), and it matches (equal x y) in both orders.  So we use
;; an evaluator that knows exactly those functions.

;; The correctness theorem requires that PAT and TERM satisfy TERMP (in the
;; same world) and that the world gives EQUAL, CONS, and
;; INTERN-IN-PACKAGE-OF-SYMBOL their usual arity of 2.  The guard (PSEUDO-TERMP)
;; is not enough: see the counterexamples in one-way-unify-tests.lisp, which
;; involve a pattern variable named T, a pattern variable named NIL, and a call
;; of CONS with one argument.  These don't indicate bugs, since ACL2 only
;; applies one-way-unify to patterns that are translated terms.

(include-book "kestrel/evaluators/defevaluator-plus" :dir :system)
(include-book "kestrel/alists-light/alists-equiv-on" :dir :system)
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/terms-light/termp" :dir :system))
(local (include-book "helpers"))
(local (include-book "system/legal-variablep" :dir :system))
(local (include-book "tools/mv-nth" :dir :system))
(local (include-book "tools/flag" :dir :system))

;; Done before the arithmetic library is included and mv-nth is disabled, so
;; that the measure proof for the flag function goes through:
(local (make-flag one-way-unify1))

(local (include-book "kestrel/arithmetic-light/top" :dir :system))

(local (in-theory (disable mv-nth)))

;; An evaluator that knows the functions one-way-unify gives special treatment to.
(defevaluator+ one-way-unify-eval
  binary-+ binary-* unary-- unary-/ intern-in-package-of-symbol coerce cons equal)

;; Evaluate the terms in the range of ALIST.
(defund one-way-unify-eval-alist (alist a)
  (if (endp alist)
      nil
    (cons (cons (caar alist) (one-way-unify-eval (cdar alist) a))
          (one-way-unify-eval-alist (cdr alist) a))))

(defthm one-way-unify-eval-alist-of-cons
  (equal (one-way-unify-eval-alist (cons pair alist) a)
         (cons (cons (car pair) (one-way-unify-eval (cdr pair) a))
               (one-way-unify-eval-alist alist a)))
  :hints (("Goal" :in-theory (enable one-way-unify-eval-alist))))

(defthm assoc-equal-of-one-way-unify-eval-alist
  (implies (alistp alist)
           (equal (assoc-equal key (one-way-unify-eval-alist alist a))
                  (let ((pair (assoc-equal key alist)))
                    (and pair
                         (cons key (one-way-unify-eval (cdr pair) a))))))
  :hints (("Goal" :in-theory (enable one-way-unify-eval-alist assoc-equal alistp))))

(defthm strip-cars-of-one-way-unify-eval-alist
  (equal (strip-cars (one-way-unify-eval-alist alist a))
         (strip-cars alist))
  :hints (("Goal" :in-theory (enable one-way-unify-eval-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Matching against constants

(local (in-theory (disable one-way-unify1-quotep-subproblems)))

(local
 (defthm car-of-mv-nth-1-of-one-way-unify1-quotep-subproblems
   (implies (and (mv-nth 0 (one-way-unify1-quotep-subproblems pat term))
                 (not (equal t (mv-nth 0 (one-way-unify1-quotep-subproblems pat term))))
                 (equal (car term) 'quote))
            (equal (car (mv-nth 1 (one-way-unify1-quotep-subproblems pat term)))
                   'quote))
   :hints (("Goal" :in-theory (enable one-way-unify1-quotep-subproblems)))))

(local
 (defthm car-of-mv-nth-3-of-one-way-unify1-quotep-subproblems
   (implies (and (mv-nth 2 (one-way-unify1-quotep-subproblems pat term))
                 (equal (car term) 'quote))
            (equal (car (mv-nth 3 (one-way-unify1-quotep-subproblems pat term)))
                   'quote))
   :hints (("Goal" :in-theory (enable one-way-unify1-quotep-subproblems)))))

(local
 (defthm termp-of-mv-nth-0-of-one-way-unify1-quotep-subproblems
   (implies (and (termp pat w)
                 (mv-nth 0 (one-way-unify1-quotep-subproblems pat term))
                 (not (equal t (mv-nth 0 (one-way-unify1-quotep-subproblems pat term))))
                 (consp pat)
                 (not (equal 'quote (car pat))))
            (termp (mv-nth 0 (one-way-unify1-quotep-subproblems pat term)) w))
   :hints (("Goal" :in-theory (enable one-way-unify1-quotep-subproblems termp)))))

(local
 (defthm termp-of-mv-nth-1-of-one-way-unify1-quotep-subproblems
   (implies (and (mv-nth 0 (one-way-unify1-quotep-subproblems pat term))
                 (not (equal t (mv-nth 0 (one-way-unify1-quotep-subproblems pat term))))
                 (termp term w)
                 (equal (car term) 'quote))
            (termp (mv-nth 1 (one-way-unify1-quotep-subproblems pat term)) w))
   :hints (("Goal" :in-theory (enable one-way-unify1-quotep-subproblems termp)))))

(local
 (defthm termp-of-mv-nth-2-of-one-way-unify1-quotep-subproblems
   (implies (and (termp pat w)
                 (mv-nth 2 (one-way-unify1-quotep-subproblems pat term))
                 (consp pat)
                 (not (equal 'quote (car pat))))
            (termp (mv-nth 2 (one-way-unify1-quotep-subproblems pat term)) w))
   :hints (("Goal" :in-theory (enable one-way-unify1-quotep-subproblems termp)))))

(local
 (defthm termp-of-mv-nth-3-of-one-way-unify1-quotep-subproblems
   (implies (and (mv-nth 2 (one-way-unify1-quotep-subproblems pat term))
                 (termp term w)
                 (equal (car term) 'quote))
            (termp (mv-nth 3 (one-way-unify1-quotep-subproblems pat term)) w))
   :hints (("Goal" :in-theory (enable one-way-unify1-quotep-subproblems termp)))))

;; Pat matches the constant term with no further requirements.
(local
 (defthm one-way-unify1-quotep-subproblems-correct-no-subproblems
   (implies (and (equal t (mv-nth 0 (one-way-unify1-quotep-subproblems pat term)))
                 (equal (car term) 'quote)
                 (consp pat)
                 (not (equal 'quote (car pat)))
                 (termp pat w))
            (equal (one-way-unify-eval pat b)
                   (unquote term)))
   :hints (("Goal" :in-theory (enable one-way-unify1-quotep-subproblems termp)))))

(local
 (defthm unary-/-when-equal-of-1-and-*
   (implies (and (equal 1 (* x y))
                 (acl2-numberp x))
            (equal (/ y) x))
   :hints (("Goal" :use ((:instance inverse-of-* (x y))
                         (:instance associativity-of-* (x x) (y y) (z (/ y))))
            :in-theory (disable inverse-of-* associativity-of-*)))))

;; Pat matches the constant term if one subproblem is solved.
(local
 (defthm one-way-unify1-quotep-subproblems-correct-one-subproblem
   (implies (and (mv-nth 0 (one-way-unify1-quotep-subproblems pat term))
                 (not (equal t (mv-nth 0 (one-way-unify1-quotep-subproblems pat term))))
                 (not (mv-nth 2 (one-way-unify1-quotep-subproblems pat term)))
                 (equal (one-way-unify-eval (mv-nth 0 (one-way-unify1-quotep-subproblems pat term)) b)
                        (one-way-unify-eval (mv-nth 1 (one-way-unify1-quotep-subproblems pat term)) a))
                 (equal (car term) 'quote)
                 (consp pat)
                 (not (equal 'quote (car pat)))
                 (termp pat w)
                 (equal (arity 'cons w) 2)
                 (equal (arity 'intern-in-package-of-symbol w) 2))
            (equal (one-way-unify-eval pat b)
                   (unquote term)))
   :hints (("Goal" :in-theory (enable one-way-unify1-quotep-subproblems termp)))))

;; Pat matches the constant term if two subproblems are solved.
(local
 (defthm one-way-unify1-quotep-subproblems-correct-two-subproblems
   (implies (and (mv-nth 2 (one-way-unify1-quotep-subproblems pat term))
                 (equal (one-way-unify-eval (mv-nth 0 (one-way-unify1-quotep-subproblems pat term)) b)
                        (one-way-unify-eval (mv-nth 1 (one-way-unify1-quotep-subproblems pat term)) a))
                 (equal (one-way-unify-eval (mv-nth 2 (one-way-unify1-quotep-subproblems pat term)) b)
                        (one-way-unify-eval (mv-nth 3 (one-way-unify1-quotep-subproblems pat term)) a))
                 (equal (car term) 'quote)
                 (consp pat)
                 (not (equal 'quote (car pat))))
            (equal (one-way-unify-eval pat b)
                   (unquote term)))
   :hints (("Goal" :in-theory (enable one-way-unify1-quotep-subproblems)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; One-way-unify1 extends the alist without changing existing bindings

(defthm-flag-one-way-unify1
  (defthm alistp-of-mv-nth-1-of-one-way-unify1
    (implies (alistp alist)
             (alistp (mv-nth 1 (one-way-unify1 pat term alist))))
    :flag one-way-unify1)
  (defthm alistp-of-mv-nth-1-of-one-way-unify1-lst
    (implies (alistp alist)
             (alistp (mv-nth 1 (one-way-unify1-lst pl tl alist))))
    :flag one-way-unify1-lst)
  (defthm alistp-of-mv-nth-1-of-one-way-unify1-equal1
    (implies (alistp alist)
             (alistp (mv-nth 1 (one-way-unify1-equal1 pat1 pat2 term1 term2 alist))))
    :flag one-way-unify1-equal1)
  (defthm alistp-of-mv-nth-1-of-one-way-unify1-equal
    (implies (alistp alist)
             (alistp (mv-nth 1 (one-way-unify1-equal pat1 pat2 term1 term2 alist))))
    :flag one-way-unify1-equal))

(defthm-flag-one-way-unify1
  (defthm assoc-equal-of-mv-nth-1-of-one-way-unify1
    (implies (assoc-equal key alist)
             (equal (assoc-equal key (mv-nth 1 (one-way-unify1 pat term alist)))
                    (assoc-equal key alist)))
    :flag one-way-unify1)
  (defthm assoc-equal-of-mv-nth-1-of-one-way-unify1-lst
    (implies (assoc-equal key alist)
             (equal (assoc-equal key (mv-nth 1 (one-way-unify1-lst pl tl alist)))
                    (assoc-equal key alist)))
    :flag one-way-unify1-lst)
  (defthm assoc-equal-of-mv-nth-1-of-one-way-unify1-equal1
    (implies (assoc-equal key alist)
             (equal (assoc-equal key (mv-nth 1 (one-way-unify1-equal1 pat1 pat2 term1 term2 alist)))
                    (assoc-equal key alist)))
    :flag one-way-unify1-equal1)
  (defthm assoc-equal-of-mv-nth-1-of-one-way-unify1-equal
    (implies (assoc-equal key alist)
             (equal (assoc-equal key (mv-nth 1 (one-way-unify1-equal pat1 pat2 term1 term2 alist)))
                    (assoc-equal key alist)))
    :flag one-way-unify1-equal))

(defthm-flag-one-way-unify1
  (defthm subsetp-equal-of-strip-cars-of-mv-nth-1-of-one-way-unify1
    (subsetp-equal (strip-cars alist) (strip-cars (mv-nth 1 (one-way-unify1 pat term alist))))
    :flag one-way-unify1)
  (defthm subsetp-equal-of-strip-cars-of-mv-nth-1-of-one-way-unify1-lst
    (subsetp-equal (strip-cars alist) (strip-cars (mv-nth 1 (one-way-unify1-lst pl tl alist))))
    :flag one-way-unify1-lst)
  (defthm subsetp-equal-of-strip-cars-of-mv-nth-1-of-one-way-unify1-equal1
    (subsetp-equal (strip-cars alist) (strip-cars (mv-nth 1 (one-way-unify1-equal1 pat1 pat2 term1 term2 alist))))
    :flag one-way-unify1-equal1)
  (defthm subsetp-equal-of-strip-cars-of-mv-nth-1-of-one-way-unify1-equal
    (subsetp-equal (strip-cars alist) (strip-cars (mv-nth 1 (one-way-unify1-equal pat1 pat2 term1 term2 alist))))
    :flag one-way-unify1-equal))

;; If B agrees with the evaluated result alist on its keys, it agrees with the
;; evaluated input alist on its keys.

(local
 (defthm alists-equiv-on-of-one-way-unify-eval-alist-of-one-way-unify1-helper
   (implies (and (alists-equiv-on keys b (one-way-unify-eval-alist (mv-nth 1 (one-way-unify1 pat term alist)) a))
                 (subsetp-equal keys (strip-cars alist))
                 (alistp alist))
            (alists-equiv-on keys b (one-way-unify-eval-alist alist a)))
   :hints (("Goal" :induct (alists-equiv-on keys b (one-way-unify-eval-alist alist a))
            :expand ((alists-equiv-on keys b (one-way-unify-eval-alist (mv-nth 1 (one-way-unify1 pat term alist)) a)))
            :in-theory (enable alists-equiv-on subsetp-equal assoc-equal-iff-member-equal-of-strip-cars)))))

(local
 (defthm alists-equiv-on-of-one-way-unify-eval-alist-of-one-way-unify1-lst-helper
   (implies (and (alists-equiv-on keys b (one-way-unify-eval-alist (mv-nth 1 (one-way-unify1-lst pl tl alist)) a))
                 (subsetp-equal keys (strip-cars alist))
                 (alistp alist))
            (alists-equiv-on keys b (one-way-unify-eval-alist alist a)))
   :hints (("Goal" :induct (alists-equiv-on keys b (one-way-unify-eval-alist alist a))
            :expand ((alists-equiv-on keys b (one-way-unify-eval-alist (mv-nth 1 (one-way-unify1-lst pl tl alist)) a)))
            :in-theory (enable alists-equiv-on subsetp-equal assoc-equal-iff-member-equal-of-strip-cars)))))

(local
 (defthm alists-equiv-on-of-one-way-unify-eval-alist-when-one-way-unify1
   (implies (and (alists-equiv-on (strip-cars (mv-nth 1 (one-way-unify1 pat term alist)))
                                  b
                                  (one-way-unify-eval-alist (mv-nth 1 (one-way-unify1 pat term alist)) a))
                 (alistp alist))
            (alists-equiv-on (strip-cars alist) b (one-way-unify-eval-alist alist a)))
   :hints (("Goal" :use (:instance alists-equiv-on-of-one-way-unify-eval-alist-of-one-way-unify1-helper
                                   (keys (strip-cars alist)))
            :in-theory (disable alists-equiv-on-of-one-way-unify-eval-alist-of-one-way-unify1-helper)))))

(local
 (defthm alists-equiv-on-of-one-way-unify-eval-alist-when-one-way-unify1-lst
   (implies (and (alists-equiv-on (strip-cars (mv-nth 1 (one-way-unify1-lst pl tl alist)))
                                  b
                                  (one-way-unify-eval-alist (mv-nth 1 (one-way-unify1-lst pl tl alist)) a))
                 (alistp alist))
            (alists-equiv-on (strip-cars alist) b (one-way-unify-eval-alist alist a)))
   :hints (("Goal" :use (:instance alists-equiv-on-of-one-way-unify-eval-alist-of-one-way-unify1-lst-helper
                                   (keys (strip-cars alist)))
            :in-theory (disable alists-equiv-on-of-one-way-unify-eval-alist-of-one-way-unify1-lst-helper)))))

(local
 (defthm cdr-of-assoc-equal-when-alists-equiv-on-of-one-way-unify-eval-alist
   (implies (and (alists-equiv-on keys b (one-way-unify-eval-alist alist a))
                 (member-equal key keys)
                 (assoc-equal key alist)
                 (alistp alist))
            (equal (cdr (assoc-equal key b))
                   (one-way-unify-eval (cdr (assoc-equal key alist)) a)))
   :hints (("Goal" :use (:instance equal-of-cdr-of-assoc-equal-and-cdr-of-assoc-equal-when-alists-equiv-on
                                   (alist1 b)
                                   (alist2 (one-way-unify-eval-alist alist a)))
            :in-theory (disable equal-of-cdr-of-assoc-equal-and-cdr-of-assoc-equal-when-alists-equiv-on)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The main theorems

;; If one-way-unify1 succeeds, then the pattern, evaluated in any alist B that
;; agrees with the (evaluated) result substitution on its keys, has the same
;; value as the term.
(defthm-flag-one-way-unify1
  (defthm one-way-unify1-correct
    (implies (and (mv-nth 0 (one-way-unify1 pat term alist))
                  (alists-equiv-on (strip-cars (mv-nth 1 (one-way-unify1 pat term alist)))
                                   b
                                   (one-way-unify-eval-alist (mv-nth 1 (one-way-unify1 pat term alist)) a))
                  (alistp alist)
                  (termp pat w)
                  (termp term w)
                  (equal (arity 'equal w) 2)
                  (equal (arity 'cons w) 2)
                  (equal (arity 'intern-in-package-of-symbol w) 2))
             (equal (one-way-unify-eval pat b)
                    (one-way-unify-eval term a)))
    :flag one-way-unify1)
  (defthm one-way-unify1-lst-correct
    (implies (and (mv-nth 0 (one-way-unify1-lst pl tl alist))
                  (alists-equiv-on (strip-cars (mv-nth 1 (one-way-unify1-lst pl tl alist)))
                                   b
                                   (one-way-unify-eval-alist (mv-nth 1 (one-way-unify1-lst pl tl alist)) a))
                  (alistp alist)
                  (term-listp pl w)
                  (term-listp tl w)
                  (equal (len pl) (len tl))
                  (equal (arity 'equal w) 2)
                  (equal (arity 'cons w) 2)
                  (equal (arity 'intern-in-package-of-symbol w) 2))
             (equal (one-way-unify-eval-list pl b)
                    (one-way-unify-eval-list tl a)))
    :flag one-way-unify1-lst)
  (defthm one-way-unify1-equal1-correct
    (implies (and (mv-nth 0 (one-way-unify1-equal1 pat1 pat2 term1 term2 alist))
                  (alists-equiv-on (strip-cars (mv-nth 1 (one-way-unify1-equal1 pat1 pat2 term1 term2 alist)))
                                   b
                                   (one-way-unify-eval-alist (mv-nth 1 (one-way-unify1-equal1 pat1 pat2 term1 term2 alist)) a))
                  (alistp alist)
                  (termp pat1 w)
                  (termp pat2 w)
                  (termp term1 w)
                  (termp term2 w)
                  (equal (arity 'equal w) 2)
                  (equal (arity 'cons w) 2)
                  (equal (arity 'intern-in-package-of-symbol w) 2))
             (and (equal (one-way-unify-eval pat1 b)
                         (one-way-unify-eval term1 a))
                  (equal (one-way-unify-eval pat2 b)
                         (one-way-unify-eval term2 a))))
    :flag one-way-unify1-equal1)
  (defthm one-way-unify1-equal-correct
    (implies (and (mv-nth 0 (one-way-unify1-equal pat1 pat2 term1 term2 alist))
                  (alists-equiv-on (strip-cars (mv-nth 1 (one-way-unify1-equal pat1 pat2 term1 term2 alist)))
                                   b
                                   (one-way-unify-eval-alist (mv-nth 1 (one-way-unify1-equal pat1 pat2 term1 term2 alist)) a))
                  (alistp alist)
                  (termp pat1 w)
                  (termp pat2 w)
                  (termp term1 w)
                  (termp term2 w)
                  (equal (arity 'equal w) 2)
                  (equal (arity 'cons w) 2)
                  (equal (arity 'intern-in-package-of-symbol w) 2))
             (equal (equal (one-way-unify-eval pat1 b)
                           (one-way-unify-eval pat2 b))
                    (equal (one-way-unify-eval term1 a)
                           (one-way-unify-eval term2 a))))
    :flag one-way-unify1-equal)
  :hints (("Goal" :in-theory (e/d (one-way-unify-eval-of-fncall-args
                                   termp
                                   assoc-equal-iff-member-equal-of-strip-cars)
                                  (one-way-unify-eval-of-fncall-args-back
                                   ;; slows down the proof a lot:
                                   term-listp-of-cdr-when-termp)))))

;; If one-way-unify succeeds, then the pattern, evaluated in the (evaluated)
;; substitution, has the same value as the term.
(defthm one-way-unify-correct
  (implies (and (mv-nth 0 (one-way-unify pat term))
                (termp pat w)
                (termp term w)
                (equal (arity 'equal w) 2)
                (equal (arity 'cons w) 2)
                (equal (arity 'intern-in-package-of-symbol w) 2))
           (equal (one-way-unify-eval pat (one-way-unify-eval-alist (mv-nth 1 (one-way-unify pat term)) a))
                  (one-way-unify-eval term a)))
  :hints (("Goal" :use (:instance one-way-unify1-correct
                                  (alist nil)
                                  (b (one-way-unify-eval-alist (mv-nth 1 (one-way-unify pat term)) a)))
           :in-theory (disable one-way-unify1-correct))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ONE-WAY-UNIFY-RESTRICTIONS (in rewrite.lisp) is used for :RESTRICT hints.
;; It tries to extend each of the RESTRICTIONS (alists from pattern variables
;; to terms) to a substitution under which PAT becomes TERM, or just calls
;; one-way-unify if there are no restrictions.

;; Like one-way-unify-correct but for any starting alist.
(local
 (defthm one-way-unify1-correct-simple
   (implies (and (mv-nth 0 (one-way-unify1 pat term alist))
                 (alistp alist)
                 (termp pat w)
                 (termp term w)
                 (equal (arity 'equal w) 2)
                 (equal (arity 'cons w) 2)
                 (equal (arity 'intern-in-package-of-symbol w) 2))
            (equal (one-way-unify-eval pat (one-way-unify-eval-alist (mv-nth 1 (one-way-unify1 pat term alist)) a))
                   (one-way-unify-eval term a)))
   :hints (("Goal" :use (:instance one-way-unify1-correct
                                   (b (one-way-unify-eval-alist (mv-nth 1 (one-way-unify1 pat term alist)) a)))
            :in-theory (disable one-way-unify1-correct)))))

(defthm one-way-unify-restrictions1-correct
  (implies (and (mv-nth 0 (one-way-unify-restrictions1 pat term restrictions))
                (alistp-listp restrictions)
                (termp pat w)
                (termp term w)
                (equal (arity 'equal w) 2)
                (equal (arity 'cons w) 2)
                (equal (arity 'intern-in-package-of-symbol w) 2))
           (equal (one-way-unify-eval pat (one-way-unify-eval-alist (mv-nth 1 (one-way-unify-restrictions1 pat term restrictions)) a))
                  (one-way-unify-eval term a)))
  :hints (("Goal" :in-theory (enable one-way-unify-restrictions1 alistp-listp))))

;; If one-way-unify-restrictions succeeds, then the pattern, evaluated in the
;; (evaluated) substitution, has the same value as the term.
(defthm one-way-unify-restrictions-correct
  (implies (and (mv-nth 0 (one-way-unify-restrictions pat term restrictions))
                (alistp-listp restrictions)
                (termp pat w)
                (termp term w)
                (equal (arity 'equal w) 2)
                (equal (arity 'cons w) 2)
                (equal (arity 'intern-in-package-of-symbol w) 2))
           (equal (one-way-unify-eval pat (one-way-unify-eval-alist (mv-nth 1 (one-way-unify-restrictions pat term restrictions)) a))
                  (one-way-unify-eval term a)))
  :hints (("Goal" :in-theory (enable one-way-unify-restrictions))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Counterexamples showing that pseudo-termp is not enough are in
;; one-way-unify-tests.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Other properties of one-way-unify

(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)
(include-book "kestrel/terms-light/lambdas-closed-in-termp" :dir :system)
(include-book "kestrel/terms-light/no-nils-in-termp" :dir :system)
(include-book "kestrel/terms-light/no-duplicate-lambda-formals-in-termp" :dir :system)

;; As its comments say, one-way-unify1 is a "No-Change Loser": if it fails, it
;; returns its input ALIST unchanged.  So are one-way-unify1-equal1 and
;; one-way-unify1-equal, but not one-way-unify1-lst, which can fail after
;; extending the alist (see one-way-unify1-lst-not-a-no-change-loser in
;; one-way-unify-tests.lisp).
(defthm-flag-one-way-unify1
  (defthm mv-nth-1-of-one-way-unify1-when-fails
    (implies (not (mv-nth 0 (one-way-unify1 pat term alist)))
             (equal (mv-nth 1 (one-way-unify1 pat term alist))
                    alist))
    :flag one-way-unify1)
  (defthm mv-nth-1-of-one-way-unify1-equal1-when-fails
    (implies (not (mv-nth 0 (one-way-unify1-equal1 pat1 pat2 term1 term2 alist)))
             (equal (mv-nth 1 (one-way-unify1-equal1 pat1 pat2 term1 term2 alist))
                    alist))
    :flag one-way-unify1-equal1)
  (defthm mv-nth-1-of-one-way-unify1-equal-when-fails
    (implies (not (mv-nth 0 (one-way-unify1-equal pat1 pat2 term1 term2 alist)))
             (equal (mv-nth 1 (one-way-unify1-equal pat1 pat2 term1 term2 alist))
                    alist))
    :flag one-way-unify1-equal)
  :skip-others t)

(defthm mv-nth-1-of-one-way-unify-when-fails
  (implies (not (mv-nth 0 (one-way-unify pat term)))
           (equal (mv-nth 1 (one-way-unify pat term))
                  nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The values in the substitution are subterms of TERM or quoted constants, so
;; they inherit the usual properties of TERM.

(local
 (defthm pseudo-termp-of-mv-nth-1-of-one-way-unify1-quotep-subproblems
   (implies (and (pseudo-termp term)
                 (equal (car term) 'quote))
            (pseudo-termp (mv-nth 1 (one-way-unify1-quotep-subproblems pat term))))
   :hints (("Goal" :in-theory (enable one-way-unify1-quotep-subproblems)))))

(local
 (defthm pseudo-termp-of-mv-nth-3-of-one-way-unify1-quotep-subproblems
   (implies (and (pseudo-termp term)
                 (equal (car term) 'quote))
            (pseudo-termp (mv-nth 3 (one-way-unify1-quotep-subproblems pat term))))
   :hints (("Goal" :in-theory (enable one-way-unify1-quotep-subproblems)))))

(local
 (defthm quotep-of-mv-nth-1-of-one-way-unify1-quotep-subproblems
   (implies (equal (car term) 'quote)
            (or (null (mv-nth 1 (one-way-unify1-quotep-subproblems pat term)))
                (and (equal (car (mv-nth 1 (one-way-unify1-quotep-subproblems pat term))) 'quote)
                     (consp (mv-nth 1 (one-way-unify1-quotep-subproblems pat term))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable one-way-unify1-quotep-subproblems)))))

(local
 (defthm quotep-of-mv-nth-3-of-one-way-unify1-quotep-subproblems
   (implies (equal (car term) 'quote)
            (or (null (mv-nth 3 (one-way-unify1-quotep-subproblems pat term)))
                (and (equal (car (mv-nth 3 (one-way-unify1-quotep-subproblems pat term))) 'quote)
                     (consp (mv-nth 3 (one-way-unify1-quotep-subproblems pat term))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable one-way-unify1-quotep-subproblems)))))

(local
 (defthm lambdas-closed-in-termp-of-mv-nth-1-of-one-way-unify1-quotep-subproblems
   (implies (equal (car term) 'quote)
            (lambdas-closed-in-termp (mv-nth 1 (one-way-unify1-quotep-subproblems pat term))))
   :hints (("Goal" :use quotep-of-mv-nth-1-of-one-way-unify1-quotep-subproblems
            :in-theory (enable lambdas-closed-in-termp)))))

(local
 (defthm lambdas-closed-in-termp-of-mv-nth-3-of-one-way-unify1-quotep-subproblems
   (implies (equal (car term) 'quote)
            (lambdas-closed-in-termp (mv-nth 3 (one-way-unify1-quotep-subproblems pat term))))
   :hints (("Goal" :use quotep-of-mv-nth-3-of-one-way-unify1-quotep-subproblems
            :in-theory (enable lambdas-closed-in-termp)))))

(local
 (defthm no-duplicate-lambda-formals-in-termp-of-mv-nth-1-of-one-way-unify1-quotep-subproblems
   (implies (equal (car term) 'quote)
            (no-duplicate-lambda-formals-in-termp (mv-nth 1 (one-way-unify1-quotep-subproblems pat term))))
   :hints (("Goal" :use quotep-of-mv-nth-1-of-one-way-unify1-quotep-subproblems
            :in-theory (enable no-duplicate-lambda-formals-in-termp)))))

(local
 (defthm no-duplicate-lambda-formals-in-termp-of-mv-nth-3-of-one-way-unify1-quotep-subproblems
   (implies (equal (car term) 'quote)
            (no-duplicate-lambda-formals-in-termp (mv-nth 3 (one-way-unify1-quotep-subproblems pat term))))
   :hints (("Goal" :use quotep-of-mv-nth-3-of-one-way-unify1-quotep-subproblems
            :in-theory (enable no-duplicate-lambda-formals-in-termp)))))

(defthm-flag-one-way-unify1
  (defthm pseudo-term-listp-of-strip-cdrs-of-mv-nth-1-of-one-way-unify1
    (implies (and (pseudo-termp term)
                  (pseudo-term-listp (strip-cdrs alist)))
             (pseudo-term-listp (strip-cdrs (mv-nth 1 (one-way-unify1 pat term alist)))))
    :flag one-way-unify1)
  (defthm pseudo-term-listp-of-strip-cdrs-of-mv-nth-1-of-one-way-unify1-lst
    (implies (and (pseudo-term-listp tl)
                  (pseudo-term-listp (strip-cdrs alist)))
             (pseudo-term-listp (strip-cdrs (mv-nth 1 (one-way-unify1-lst pl tl alist)))))
    :flag one-way-unify1-lst)
  (defthm pseudo-term-listp-of-strip-cdrs-of-mv-nth-1-of-one-way-unify1-equal1
    (implies (and (pseudo-termp term1)
                  (pseudo-termp term2)
                  (pseudo-term-listp (strip-cdrs alist)))
             (pseudo-term-listp (strip-cdrs (mv-nth 1 (one-way-unify1-equal1 pat1 pat2 term1 term2 alist)))))
    :flag one-way-unify1-equal1)
  (defthm pseudo-term-listp-of-strip-cdrs-of-mv-nth-1-of-one-way-unify1-equal
    (implies (and (pseudo-termp term1)
                  (pseudo-termp term2)
                  (pseudo-term-listp (strip-cdrs alist)))
             (pseudo-term-listp (strip-cdrs (mv-nth 1 (one-way-unify1-equal pat1 pat2 term1 term2 alist)))))
    :flag one-way-unify1-equal))

(defthm-flag-one-way-unify1
  (defthm term-listp-of-strip-cdrs-of-mv-nth-1-of-one-way-unify1
    (implies (and (termp pat w)
                  (termp term w)
                  (term-listp (strip-cdrs alist) w)
                  (equal (arity 'equal w) 2))
             (term-listp (strip-cdrs (mv-nth 1 (one-way-unify1 pat term alist))) w))
    :flag one-way-unify1)
  (defthm term-listp-of-strip-cdrs-of-mv-nth-1-of-one-way-unify1-lst
    (implies (and (term-listp pl w)
                  (term-listp tl w)
                  (equal (len pl) (len tl))
                  (term-listp (strip-cdrs alist) w)
                  (equal (arity 'equal w) 2))
             (term-listp (strip-cdrs (mv-nth 1 (one-way-unify1-lst pl tl alist))) w))
    :flag one-way-unify1-lst)
  (defthm term-listp-of-strip-cdrs-of-mv-nth-1-of-one-way-unify1-equal1
    (implies (and (termp pat1 w)
                  (termp pat2 w)
                  (termp term1 w)
                  (termp term2 w)
                  (term-listp (strip-cdrs alist) w)
                  (equal (arity 'equal w) 2))
             (term-listp (strip-cdrs (mv-nth 1 (one-way-unify1-equal1 pat1 pat2 term1 term2 alist))) w))
    :flag one-way-unify1-equal1)
  (defthm term-listp-of-strip-cdrs-of-mv-nth-1-of-one-way-unify1-equal
    (implies (and (termp pat1 w)
                  (termp pat2 w)
                  (termp term1 w)
                  (termp term2 w)
                  (term-listp (strip-cdrs alist) w)
                  (equal (arity 'equal w) 2))
             (term-listp (strip-cdrs (mv-nth 1 (one-way-unify1-equal pat1 pat2 term1 term2 alist))) w))
    :flag one-way-unify1-equal)
  :hints (("Goal" :in-theory (e/d (termp) (term-listp-of-cdr-when-termp)))))

(defthm-flag-one-way-unify1
  (defthm lambdas-closed-in-termsp-of-strip-cdrs-of-mv-nth-1-of-one-way-unify1
    (implies (and (lambdas-closed-in-termp term)
                  (lambdas-closed-in-termsp (strip-cdrs alist)))
             (lambdas-closed-in-termsp (strip-cdrs (mv-nth 1 (one-way-unify1 pat term alist)))))
    :flag one-way-unify1)
  (defthm lambdas-closed-in-termsp-of-strip-cdrs-of-mv-nth-1-of-one-way-unify1-lst
    (implies (and (lambdas-closed-in-termsp tl)
                  (lambdas-closed-in-termsp (strip-cdrs alist)))
             (lambdas-closed-in-termsp (strip-cdrs (mv-nth 1 (one-way-unify1-lst pl tl alist)))))
    :flag one-way-unify1-lst)
  (defthm lambdas-closed-in-termsp-of-strip-cdrs-of-mv-nth-1-of-one-way-unify1-equal1
    (implies (and (lambdas-closed-in-termp term1)
                  (lambdas-closed-in-termp term2)
                  (lambdas-closed-in-termsp (strip-cdrs alist)))
             (lambdas-closed-in-termsp (strip-cdrs (mv-nth 1 (one-way-unify1-equal1 pat1 pat2 term1 term2 alist)))))
    :flag one-way-unify1-equal1)
  (defthm lambdas-closed-in-termsp-of-strip-cdrs-of-mv-nth-1-of-one-way-unify1-equal
    (implies (and (lambdas-closed-in-termp term1)
                  (lambdas-closed-in-termp term2)
                  (lambdas-closed-in-termsp (strip-cdrs alist)))
             (lambdas-closed-in-termsp (strip-cdrs (mv-nth 1 (one-way-unify1-equal pat1 pat2 term1 term2 alist)))))
    :flag one-way-unify1-equal)
  :hints (("Goal" :in-theory (enable lambdas-closed-in-termp lambdas-closed-in-termsp))))

(defthm-flag-one-way-unify1
  (defthm no-duplicate-lambda-formals-in-termsp-of-strip-cdrs-of-mv-nth-1-of-one-way-unify1
    (implies (and (no-duplicate-lambda-formals-in-termp term)
                  (no-duplicate-lambda-formals-in-termsp (strip-cdrs alist)))
             (no-duplicate-lambda-formals-in-termsp (strip-cdrs (mv-nth 1 (one-way-unify1 pat term alist)))))
    :flag one-way-unify1)
  (defthm no-duplicate-lambda-formals-in-termsp-of-strip-cdrs-of-mv-nth-1-of-one-way-unify1-lst
    (implies (and (no-duplicate-lambda-formals-in-termsp tl)
                  (no-duplicate-lambda-formals-in-termsp (strip-cdrs alist)))
             (no-duplicate-lambda-formals-in-termsp (strip-cdrs (mv-nth 1 (one-way-unify1-lst pl tl alist)))))
    :flag one-way-unify1-lst)
  (defthm no-duplicate-lambda-formals-in-termsp-of-strip-cdrs-of-mv-nth-1-of-one-way-unify1-equal1
    (implies (and (no-duplicate-lambda-formals-in-termp term1)
                  (no-duplicate-lambda-formals-in-termp term2)
                  (no-duplicate-lambda-formals-in-termsp (strip-cdrs alist)))
             (no-duplicate-lambda-formals-in-termsp (strip-cdrs (mv-nth 1 (one-way-unify1-equal1 pat1 pat2 term1 term2 alist)))))
    :flag one-way-unify1-equal1)
  (defthm no-duplicate-lambda-formals-in-termsp-of-strip-cdrs-of-mv-nth-1-of-one-way-unify1-equal
    (implies (and (no-duplicate-lambda-formals-in-termp term1)
                  (no-duplicate-lambda-formals-in-termp term2)
                  (no-duplicate-lambda-formals-in-termsp (strip-cdrs alist)))
             (no-duplicate-lambda-formals-in-termsp (strip-cdrs (mv-nth 1 (one-way-unify1-equal pat1 pat2 term1 term2 alist)))))
    :flag one-way-unify1-equal)
  :hints (("Goal" :in-theory (enable no-duplicate-lambda-formals-in-termp no-duplicate-lambda-formals-in-termsp))))

;; Wrappers for one-way-unify:

(defthm pseudo-term-listp-of-strip-cdrs-of-mv-nth-1-of-one-way-unify
  (implies (pseudo-termp term)
           (pseudo-term-listp (strip-cdrs (mv-nth 1 (one-way-unify pat term))))))

(defthm term-listp-of-strip-cdrs-of-mv-nth-1-of-one-way-unify
  (implies (and (termp pat w)
                (termp term w)
                (equal (arity 'equal w) 2))
           (term-listp (strip-cdrs (mv-nth 1 (one-way-unify pat term))) w)))

;; Follows from the termp property.
(defthm no-nils-in-termsp-of-strip-cdrs-of-mv-nth-1-of-one-way-unify
  (implies (and (termp pat w)
                (termp term w)
                (equal (arity 'equal w) 2))
           (no-nils-in-termsp (strip-cdrs (mv-nth 1 (one-way-unify pat term)))))
  :hints (("Goal" :use (:instance no-nils-in-termsp-when-term-listp
                                  (terms (strip-cdrs (mv-nth 1 (one-way-unify pat term)))))
           :in-theory (disable no-nils-in-termsp-when-term-listp))))

(defthm lambdas-closed-in-termsp-of-strip-cdrs-of-mv-nth-1-of-one-way-unify
  (implies (lambdas-closed-in-termp term)
           (lambdas-closed-in-termsp (strip-cdrs (mv-nth 1 (one-way-unify pat term))))))

(defthm no-duplicate-lambda-formals-in-termsp-of-strip-cdrs-of-mv-nth-1-of-one-way-unify
  (implies (no-duplicate-lambda-formals-in-termp term)
           (no-duplicate-lambda-formals-in-termsp (strip-cdrs (mv-nth 1 (one-way-unify pat term))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The substitution binds only variables of PAT (outside of lambda bodies),
;; besides those already bound in ALIST.

(local (include-book "kestrel/lists-light/union-equal" :dir :system))

(local
 (defthm subsetp-equal-of-free-vars-in-term-of-mv-nth-0-of-one-way-unify1-quotep-subproblems
   (implies (and (mv-nth 0 (one-way-unify1-quotep-subproblems pat term))
                 (not (equal t (mv-nth 0 (one-way-unify1-quotep-subproblems pat term))))
                 (consp pat)
                 (not (equal 'quote (car pat))))
            (subsetp-equal (free-vars-in-term (mv-nth 0 (one-way-unify1-quotep-subproblems pat term)))
                           (free-vars-in-term pat)))
   :hints (("Goal" :expand ((free-vars-in-term pat)
                            (free-vars-in-terms (cdr pat))
                            (free-vars-in-terms (cddr pat)))
            :in-theory (enable one-way-unify1-quotep-subproblems)))))

(local
 (defthm subsetp-equal-of-free-vars-in-term-of-mv-nth-2-of-one-way-unify1-quotep-subproblems
   (implies (and (mv-nth 2 (one-way-unify1-quotep-subproblems pat term))
                 (consp pat)
                 (not (equal 'quote (car pat))))
            (subsetp-equal (free-vars-in-term (mv-nth 2 (one-way-unify1-quotep-subproblems pat term)))
                           (free-vars-in-term pat)))
   :hints (("Goal" :expand ((free-vars-in-term pat)
                            (free-vars-in-terms (cdr pat))
                            (free-vars-in-terms (cddr pat)))
            :in-theory (enable one-way-unify1-quotep-subproblems)))))

(defthm-flag-one-way-unify1
  (defthm subsetp-equal-of-strip-cars-of-mv-nth-1-of-one-way-unify1-and-free-vars-in-term
    (implies (and (termp pat w)
                  (equal (arity 'equal w) 2))
             (subsetp-equal (strip-cars (mv-nth 1 (one-way-unify1 pat term alist)))
                            (union-equal (strip-cars alist) (free-vars-in-term pat))))
    :flag one-way-unify1)
  (defthm subsetp-equal-of-strip-cars-of-mv-nth-1-of-one-way-unify1-lst-and-free-vars-in-terms
    (implies (and (term-listp pl w)
                  (equal (arity 'equal w) 2))
             (subsetp-equal (strip-cars (mv-nth 1 (one-way-unify1-lst pl tl alist)))
                            (union-equal (strip-cars alist) (free-vars-in-terms pl))))
    :flag one-way-unify1-lst)
  (defthm subsetp-equal-of-strip-cars-of-mv-nth-1-of-one-way-unify1-equal1-and-free-vars-in-term
    (implies (and (termp pat1 w)
                  (termp pat2 w)
                  (equal (arity 'equal w) 2))
             (subsetp-equal (strip-cars (mv-nth 1 (one-way-unify1-equal1 pat1 pat2 term1 term2 alist)))
                            (union-equal (strip-cars alist)
                                         (union-equal (free-vars-in-term pat1)
                                                      (free-vars-in-term pat2)))))
    :flag one-way-unify1-equal1)
  (defthm subsetp-equal-of-strip-cars-of-mv-nth-1-of-one-way-unify1-equal-and-free-vars-in-term
    (implies (and (termp pat1 w)
                  (termp pat2 w)
                  (equal (arity 'equal w) 2))
             (subsetp-equal (strip-cars (mv-nth 1 (one-way-unify1-equal pat1 pat2 term1 term2 alist)))
                            (union-equal (strip-cars alist)
                                         (union-equal (free-vars-in-term pat1)
                                                      (free-vars-in-term pat2)))))
    :flag one-way-unify1-equal)
  :hints (("Goal" :in-theory (e/d (termp free-vars-in-term free-vars-in-terms)
                                  (term-listp-of-cdr-when-termp)))))

(defthm subsetp-equal-of-strip-cars-of-mv-nth-1-of-one-way-unify
  (implies (and (termp pat w)
                (equal (arity 'equal w) 2))
           (subsetp-equal (strip-cars (mv-nth 1 (one-way-unify pat term)))
                          (free-vars-in-term pat)))
  :hints (("Goal" :use (:instance subsetp-equal-of-strip-cars-of-mv-nth-1-of-one-way-unify1-and-free-vars-in-term
                                  (alist nil))
           :in-theory (disable subsetp-equal-of-strip-cars-of-mv-nth-1-of-one-way-unify1-and-free-vars-in-term))))
