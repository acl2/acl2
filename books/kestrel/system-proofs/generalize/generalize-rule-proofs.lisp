; Soundness of generalize-rule-segment
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Generalize-rule-segment instantiates :generalize rules to get facts about
;; the terms being generalized, and returns the negations of those facts (to
;; be added as hypotheses to the clause).  We show that, if the formulas of
;; the :generalize rules are theorems, then these literals are all false, and
;; that they mention only variables of the terms being generalized (so that
;; the new variables do not occur in them).

(include-book "disjoin-clauses-proofs")
(include-book "one-way-unify-proofs")
(local (include-book "helpers"))

(local (in-theory (disable generalize-ev-of-fncall-args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The assumption about the :generalize rules
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun-sk generalize-ev-theoremp (formula)
  (forall a (generalize-ev formula a)))

(in-theory (disable generalize-ev-theoremp))

;; Checks that the formula of each :generalize rule in RULES is a theorem
;; (according to the evaluator).  This holds for the generalize-rules of a
;; valid world (assuming the evaluator's functions have their usual meanings).
(defund generalize-rules-okp (rules)
  (declare (xargs :measure (if rules (+ 1 (len rules)) 0)))
  (if (null rules)
      t
    (let ((formula (access generalize-rule (car rules) :formula)))
      (and (pseudo-termp formula)
           (not (member-equal nil (free-vars-in-term formula)))
           (generalize-ev-theoremp formula)
           (generalize-rules-okp (cdr rules))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Variables
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm free-vars-in-term-when-quotep
   (implies (quotep term)
            (equal (free-vars-in-term term)
                   nil))
   :hints (("Goal" :expand ((free-vars-in-term term))))))

(local
 (defthm not-intersectp-equal-of-free-vars-in-term-of-nil
   (implies (not (member-equal nil vars))
            (not (intersectp-equal vars (free-vars-in-term nil))))
   :hints (("Goal" :expand ((free-vars-in-term nil))))))

(local
 (defthm not-intersectp-equal-of-free-vars-in-term-of-cdr-of-assoc-equal
   (implies (and (not (intersectp-equal vars (free-vars-in-terms (strip-cdrs alist))))
                 (assoc-equal x alist))
            (not (intersectp-equal vars (free-vars-in-term (cdr (assoc-equal x alist))))))
   :hints (("Goal" :in-theory (enable assoc-equal free-vars-in-terms)))))

(local
 (defthm not-intersectp-equal-of-free-vars-in-term-of-cons-term
   (implies (and (not (intersectp-equal vars (free-vars-in-terms args)))
                 (not (member-equal nil vars)))
            (not (intersectp-equal vars (free-vars-in-term (cons-term fn args)))))
   :hints (("Goal" :in-theory (enable cons-term cons-term1)
            :expand ((free-vars-in-term (cons fn args)))))))

(local
 (defthm not-intersectp-equal-of-free-vars-in-term-of-mv-nth-1-of-cons-term1-mv2
   (implies (and (not (intersectp-equal vars (free-vars-in-term form)))
                 (not (member-equal nil vars)))
            (not (intersectp-equal vars (free-vars-in-term (mv-nth 1 (cons-term1-mv2 fn args form))))))
   :hints (("Goal" :in-theory (enable cons-term1-mv2)))))

;; If all the variables of X are bound, the result of substituting into X
;; mentions only variables of the bindings.
(defthm-term-subst-flg
  (defthm not-intersectp-equal-of-free-vars-in-term-of-sublis-var1
    (implies (and (not (free-varsp x alist))
                  (not (intersectp-equal vars (free-vars-in-terms (strip-cdrs alist))))
                  (not (member-equal nil vars)))
             (not (intersectp-equal vars (free-vars-in-term (mv-nth 1 (sublis-var1 alist x))))))
    :flag term)
  (defthm not-intersectp-equal-of-free-vars-in-terms-of-sublis-var1-lst
    (implies (and (not (free-varsp-lst x alist))
                  (not (intersectp-equal vars (free-vars-in-terms (strip-cdrs alist))))
                  (not (member-equal nil vars)))
             (not (intersectp-equal vars (free-vars-in-terms (mv-nth 1 (sublis-var1-lst alist x))))))
    :flag list)
  :hints (("Goal" :in-theory (enable sublis-var1 sublis-var1-lst free-varsp free-varsp-lst)
           :expand ((free-vars-in-term x)
                    (free-vars-in-terms x)))
          (and stable-under-simplificationp
               '(:use not-intersectp-equal-of-free-vars-in-term-of-cdr-of-assoc-equal))))

(defthm not-intersectp-equal-of-free-vars-in-term-of-sublis-var
  (implies (and (not (free-varsp x alist))
                (not (intersectp-equal vars (free-vars-in-terms (strip-cdrs alist))))
                (not (member-equal nil vars)))
           (not (intersectp-equal vars (free-vars-in-term (sublis-var alist x)))))
  :hints (("Goal" :in-theory (enable sublis-var))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Bindings of NIL do not matter when NIL is not a variable of the term
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Drops the bindings of NIL (and any non-pairs) from ALIST.
(defund drop-nil-bindings (alist)
  (cond ((atom alist) nil)
        ((and (consp (car alist))
              (caar alist))
         (cons (car alist) (drop-nil-bindings (cdr alist))))
        (t (drop-nil-bindings (cdr alist)))))

(defthm assoc-equal-of-drop-nil-bindings
  (implies x
           (equal (assoc-equal x (drop-nil-bindings alist))
                  (assoc-equal x alist)))
  :hints (("Goal" :in-theory (enable drop-nil-bindings))))

(defthm not-assoc-equal-of-nil-and-drop-nil-bindings
  (not (assoc-equal nil (drop-nil-bindings alist)))
  :hints (("Goal" :in-theory (enable drop-nil-bindings))))

(defthm pseudo-term-listp-of-strip-cdrs-of-drop-nil-bindings
  (implies (pseudo-term-listp (strip-cdrs alist))
           (pseudo-term-listp (strip-cdrs (drop-nil-bindings alist))))
  :hints (("Goal" :in-theory (enable drop-nil-bindings))))

(defthm-term-subst-flg
  (defthm sublis-var1-of-drop-nil-bindings
    (implies (not (member-equal nil (free-vars-in-term x)))
             (equal (sublis-var1 (drop-nil-bindings alist) x)
                    (sublis-var1 alist x)))
    :flag term)
  (defthm sublis-var1-lst-of-drop-nil-bindings
    (implies (not (member-equal nil (free-vars-in-terms x)))
             (equal (sublis-var1-lst (drop-nil-bindings alist) x)
                    (sublis-var1-lst alist x)))
    :flag list)
  :hints (("Goal" :in-theory (enable sublis-var1 sublis-var1-lst)
           :expand ((free-vars-in-term x)
                    (free-vars-in-terms x)))))

(defthm sublis-var-of-drop-nil-bindings
  (implies (not (member-equal nil (free-vars-in-term x)))
           (equal (sublis-var (drop-nil-bindings alist) x)
                  (sublis-var alist x)))
  :hints (("Goal" :in-theory (enable sublis-var))))

;; An instance of a theorem is true, if NIL is not a variable of the theorem.
(defthm generalize-ev-of-sublis-var-when-generalize-ev-theoremp
  (implies (and (generalize-ev-theoremp formula)
                (pseudo-termp formula)
                (not (member-equal nil (free-vars-in-term formula))))
           (generalize-ev (sublis-var alist formula) a))
  :hints (("Goal" :use ((:instance generalize-ev-of-sublis-var
                                   (x formula)
                                   (alist (drop-nil-bindings alist)))
                        (:instance generalize-ev-theoremp-necc
                                   (a (append (generalize-ev-alist (drop-nil-bindings alist) a) a))))
           :in-theory (disable generalize-ev-of-sublis-var
                               generalize-ev-theoremp-necc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; subterm-one-way-unify
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-flag subterm-one-way-unify)

(defthm-flag-subterm-one-way-unify
  (defthm subterm-one-way-unify-properties
    (let ((res (mv-nth 1 (subterm-one-way-unify pat term))))
      (and (implies (pseudo-termp term)
                    (pseudo-term-listp (strip-cdrs res)))
           (implies (and (not (intersectp-equal vars (free-vars-in-term term)))
                         (not (member-equal nil vars)))
                    (not (intersectp-equal vars (free-vars-in-terms (strip-cdrs res)))))))
    :flag subterm-one-way-unify)
  (defthm subterm-one-way-unify-lst-properties
    (let ((res (mv-nth 1 (subterm-one-way-unify-lst pat-lst term))))
      (and (implies (pseudo-termp term)
                    (pseudo-term-listp (strip-cdrs res)))
           (implies (and (not (intersectp-equal vars (free-vars-in-term term)))
                         (not (member-equal nil vars)))
                    (not (intersectp-equal vars (free-vars-in-terms (strip-cdrs res)))))))
    :flag subterm-one-way-unify-lst)
  :hints (("Goal" :in-theory (enable subterm-one-way-unify subterm-one-way-unify-lst
                                     one-way-unify))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; dumb-negate-lit
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm generalize-ev-of-dumb-negate-lit
  (implies (pseudo-termp term)
           (iff (generalize-ev (dumb-negate-lit term) a)
                (not (generalize-ev term a))))
  :hints (("Goal" :in-theory (e/d (dumb-negate-lit generalize-ev-of-fncall-args)
                                  (generalize-ev-of-fncall-args-back)))))

(defthm pseudo-termp-of-dumb-negate-lit
  (implies (pseudo-termp term)
           (pseudo-termp (dumb-negate-lit term)))
  :hints (("Goal" :in-theory (enable dumb-negate-lit))))

(defthm not-intersectp-equal-of-free-vars-in-term-of-dumb-negate-lit
  (implies (and (not (intersectp-equal vars (free-vars-in-term term)))
                (not (member-equal nil vars)))
           (not (intersectp-equal vars (free-vars-in-term (dumb-negate-lit term)))))
  :hints (("Goal" :in-theory (enable dumb-negate-lit)
           :expand ((free-vars-in-term term)
                    (free-vars-in-terms (cdr term))
                    (:free (x) (free-vars-in-term (cons 'not x)))
                    (:free (x) (free-vars-in-terms (cons x nil)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; add-literal and disjoin-clauses (syntactic properties)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm pseudo-term-listp-of-add-literal
  (implies (and (pseudo-termp lit)
                (pseudo-term-listp cl))
           (pseudo-term-listp (add-literal lit cl at-end-flg)))
  :hints (("Goal" :in-theory (enable add-literal))))

(defthm not-intersectp-equal-of-free-vars-in-terms-of-add-literal
  (implies (and (not (intersectp-equal vars (free-vars-in-term lit)))
                (not (intersectp-equal vars (free-vars-in-terms cl))))
           (not (intersectp-equal vars (free-vars-in-terms (add-literal lit cl at-end-flg)))))
  :hints (("Goal" :in-theory (enable add-literal))))

(defthm pseudo-term-listp-of-disjoin-clauses1
  (implies (and (pseudo-term-listp cl1)
                (pseudo-term-listp cl2))
           (pseudo-term-listp (disjoin-clauses1 cl1 cl2)))
  :hints (("Goal" :in-theory (e/d (disjoin-clauses1) (add-literal)))))

(defthm pseudo-term-listp-of-disjoin-clauses
  (implies (and (pseudo-term-listp cl1)
                (pseudo-term-listp cl2))
           (pseudo-term-listp (disjoin-clauses cl1 cl2)))
  :hints (("Goal" :in-theory (enable disjoin-clauses))))

(defthm not-intersectp-equal-of-free-vars-in-terms-of-disjoin-clauses1
  (implies (and (not (intersectp-equal vars (free-vars-in-terms cl1)))
                (not (intersectp-equal vars (free-vars-in-terms cl2))))
           (not (intersectp-equal vars (free-vars-in-terms (disjoin-clauses1 cl1 cl2)))))
  :hints (("Goal" :in-theory (e/d (disjoin-clauses1) (add-literal))
           :expand ((free-vars-in-terms cl2)))))

(defthm not-intersectp-equal-of-free-vars-in-terms-of-disjoin-clauses
  (implies (and (not (intersectp-equal vars (free-vars-in-terms cl1)))
                (not (intersectp-equal vars (free-vars-in-terms cl2))))
           (not (intersectp-equal vars (free-vars-in-terms (disjoin-clauses cl1 cl2)))))
  :hints (("Goal" :in-theory (enable disjoin-clauses))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; apply-generalize-rule
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm apply-generalize-rule-properties
  (implies (and (mv-nth 0 (apply-generalize-rule gen-rule term ens))
                (pseudo-termp (access generalize-rule gen-rule :formula))
                (pseudo-termp term))
           (and (pseudo-termp (mv-nth 1 (apply-generalize-rule gen-rule term ens)))
                (implies (and (not (intersectp-equal vars (free-vars-in-term term)))
                              (not (member-equal nil vars)))
                         (not (intersectp-equal vars (free-vars-in-term (mv-nth 1 (apply-generalize-rule gen-rule term ens))))))
                (implies (and (generalize-ev-theoremp (access generalize-rule gen-rule :formula))
                              (not (member-equal nil (free-vars-in-term (access generalize-rule gen-rule :formula)))))
                         (generalize-ev (mv-nth 1 (apply-generalize-rule gen-rule term ens)) a))))
  :hints (("Goal" :in-theory (e/d (apply-generalize-rule) (subterm-one-way-unify)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; generalize-rule-segment
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm generalize-rule-segment1-properties
  (implies (and (generalize-rules-okp generalize-rules)
                (pseudo-termp term))
           (let ((segment (mv-nth 0 (generalize-rule-segment1 generalize-rules term ens))))
             (and (pseudo-term-listp segment)
                  (all-eval-to-false-with-generalize-ev segment a)
                  (implies (and (not (intersectp-equal vars (free-vars-in-term term)))
                                (not (member-equal nil vars)))
                           (not (intersectp-equal vars (free-vars-in-terms segment)))))))
  :hints (("Goal" :in-theory (e/d (generalize-rule-segment1 generalize-rules-okp)
                                  (apply-generalize-rule add-literal dumb-negate-lit)))))

;; The main theorem of this book: The literals returned by
;; generalize-rule-segment are false, and they mention only variables of the
;; terms being generalized.
(defthm generalize-rule-segment-properties
  (implies (and (generalize-rules-okp (global-val 'generalize-rules wrld))
                (pseudo-term-listp terms))
           (let ((segment (mv-nth 0 (generalize-rule-segment terms vars ens wrld))))
             (and (pseudo-term-listp segment)
                  (all-eval-to-false-with-generalize-ev segment a)
                  (implies (and (not (intersectp-equal vars2 (free-vars-in-terms terms)))
                                (not (member-equal nil vars2)))
                           (not (intersectp-equal vars2 (free-vars-in-terms segment)))))))
  :hints (("Goal" :in-theory (e/d (generalize-rule-segment)
                                  (generalize-rule-segment1 disjoin-clauses))
           :expand ((free-vars-in-terms terms)))))
