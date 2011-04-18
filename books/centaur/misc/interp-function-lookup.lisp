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



(in-package "ACL2")

;; This book introduces a function INTERP-FUNCTION-LOOKUP, which is
;; intended to enable clause processors to soundly use arbitrary
;; function definitions extracted from the ACL2 world.  Effectively, a
;; clause processor may use in its reasoning an instance of a
;; definitional equation (or any other theorem) if it then returns as
;; part of its list of goal clauses the theorem in question.
;; INTERP-FUNCTION-LOOKUP takes as input an alist that collects these
;; definitional equations, and produces a new alist as output that
;; includes all the previous definitional equations along with the one
;; used to produce the function body.

;; This book uses a fairly generic evaluator IFL-EV to prove
;; correctness theorems about INTERP-FUNCTION-LOOKUP; it recognizes
;; the function symbols IF, NOT, EQUAL, and USE-BY-HINT.  The theorems
;; can be functionally instantiated for other evaluators that
;; recognize these four symbols.

;; To prove the correctness of a clause processor that uses these
;; functions, it is best (indeed probably necessary) to use a
;; "bad-guy" witness function as the alist under which the generated
;; goal clauses are evaluated.  We elaborate more below.

;; The clauses collected in the definition alist produced by
;; INTERP-FUNCTION-LOOKUP are designed to be proven quickly and
;; automatically by the computed hint (USE-BY-COMPUTED-HINT CLAUSE).
;; Users of clause processors that utilize INTERP-FUNCTION-LOOKUP
;; should ensure that this computed hint is in effect immediately
;; after such a clause processor is applied.


;; There are two major correctness theorems about
;; INTERP-FUNCTION-LOOKUP, and some less interesting but equally
;; important well-formedness theorems, which we list here.

;; Major correctness theorems:  Evaluating the body of the function in
;; a context where the formals are bound to the evaluations of some
;; actuals is the same as evaluating the function applied to those
;; actuals.

;; (defthm interp-function-lookup-correct
;;   (mv-let (erp body formals out-defs)
;;     (interp-function-lookup fn in-defs world)
;;     (implies (and (not erp)
;;                   (ifl-ev-theoremp
;;                    (conjoin-clauses
;;                     (interp-defs-alist-clauses out-defs)))
;;                   (interp-defs-alistp in-defs)
;;                   (equal (len formals) (len actuals))
;;                   (not (eq fn 'quote)))
;;              (equal (ifl-ev body (pairlis$ formals
;;                                            (ifl-ev-lst actuals a)))
;;                     (ifl-ev (cons fn actuals) a))))
;;   :hints(("goal" :in-theory (e/d* (ifl-ev-constraint-0))
;;           :do-not-induct t)))

;; This is a corollary of this more general theorem, which may also be
;; useful sometimes:
;; (defthm interp-function-lookup-correct-2
;;   (mv-let (erp body formals out-defs)
;;     (interp-function-lookup fn in-defs world)
;;     (implies (and (not erp)
;;                   (ifl-ev-theoremp
;;                    (conjoin-clauses
;;                     (interp-defs-alist-clauses out-defs)))
;;                   (interp-defs-alistp in-defs)
;;                   (equal (len formals) (len actuals))
;;                   (not (eq fn 'quote)))
;;              (equal (ifl-ev body (pairlis$ formals actuals))
;;                     (ifl-ev (cons fn (kwote-lst actuals)) nil)))))

;; This theorem shows that INTERP-FUNCTION-LOOKUP's collected
;; definitions extend the ones it was given, which is important for
;; correctness when using it repeatedly:
;; (defthm interp-function-lookup-theoremp-defs-history
;;   (b* (((mv erp & & out-defs)
;;         (interp-function-lookup fn in-defs world)))
;;     (implies (and (ifl-ev-theoremp
;;                         (conjoin-clauses
;;                          (interp-defs-alist-clauses out-defs)))
;;                   (not erp)
;;                   (interp-defs-alistp in-defs))
;;              (ifl-ev-theoremp
;;               (conjoin-clauses
;;                (interp-defs-alist-clauses in-defs))))))


;; The following theorems establish well-formedness properties of the
;; outputs:
;; (defthm interp-function-lookup-defs-alistp
;;   (b* (((mv erp & & out-defs)
;;         (interp-function-lookup fn in-defs world)))
;;     (implies (and (not erp) (symbolp fn))
;;              (iff (interp-defs-alistp out-defs)
;;                   (interp-defs-alistp in-defs))))
;;   :hints(("Goal" :in-theory (e/d (interp-defs-alistp)))))

;; (defthm interp-function-lookup-wfp
;;   (b* (((mv erp body formals &)
;;         (interp-function-lookup fn in-defs world)))
;;     (implies (and (not erp)
;;                   (interp-defs-alistp in-defs))
;;              (and (pseudo-termp body)
;;                   (nonnil-symbol-listp formals)
;;                   (no-duplicatesp-equal formals))))
;;   :hints(("Goal" :in-theory
;;           (enable
;;            hons-assoc-equal-interp-defs-alistp))))




;; To elaborate on the "bad guy" comment above, the following is the
;; correctness claim for a generic clause processor:
;; (implies (and (pseudo-term-listp clause)
;;               (alistp al)
;;               (ev (conjoin-clauses
;;                    (my-clause-processor clause hints))
;;                   an-arbitrary-alist))
;;          (ev (disjoin clause) al))

;; A powerful technique is to introduce a "bad-guy" function for your
;; evaluator as follows:
;; (defchoose falsifier-for-ev (a) (x)
;;   (not (ev x a)))
;; This introduces a function symbol falsifier-for-ev with the axiom
;; "If there exists an alist under which X evaluates to NIL, then X
;; also evaluates to nil under the alist (FALSIFIER-FOR-EV X)."
;; A consequence of this is that the assertion
;; (ev x (falsifier-for-ev x)) is effectively equivalent to "x is a
;; theorem in the language of EV."  As you might expect, it can be
;; shown that (ev (conjoin lst) (falsifier-for-ev (conjoin lst)))
;; implies, for each element x of lst, (ev x (falsifier-for-ev x)).

;; One may choose as the arbitrary alist in the clause-processor
;; correctness claim above the falsifier of the conjoined generated
;; clauses, like this:
;; (implies (and (pseudo-term-listp clause)
;;               (alistp al)
;;               (ev (conjoin-clauses
;;                    (my-clause-processor clause hints))
;;                   (falsifier-for-ev
;;                    (conjoin-clauses
;;                     (my-clause-processor clause hints)))))
;;          (ev (disjoin clause) al))
;; Then in proving this theorem, the user may assume each generated
;; clause to be true under a different alist, or more than one, by
;; applying as :use hints instances of the falsifier-for-ev axiom.


(include-book "hons-sets")
(include-book "tools/bstar" :dir :system)
(include-book "tools/mv-nth" :dir :system)
(include-book "clause-processors/use-by-hint" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "misc/untranslate-patterns" :dir :system)
(include-book "clause-processors/ev-theoremp" :dir :system)

(set-inhibit-warnings "theory")

;; We'll first produce a generic interpreter based on an evaluator
;; that understands only IF.  We'll use the prefix "GENINTERP-" for
;; this.  However, we introduce some evaluator-independent concepts
;; first.

(defun nonnil-symbol-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (symbolp (car x))
         (car x)
         (nonnil-symbol-listp (cdr x)))))

(defun no-dupsp (lst)
  (declare (xargs :guard t))
  (not (hons-dups-p lst)))

(defthm no-dupsp-is-no-duplicatesp-equal
  (equal (no-dupsp lst)
         (no-duplicatesp-equal lst)))

(in-theory (disable no-dupsp))

(defun interp-defs-alistp (defs)
  (declare (xargs :guard t))
  (or (atom defs)
      (and (let ((entry (car defs)))
             (case-match entry
               ((fn formals body . &)
                ;; the & is the rune equating the function call with
                ;; the body
                (and (symbolp fn)
                     (pseudo-termp body)
                     (nonnil-symbol-listp formals)
                     (no-dupsp formals)))))
           (interp-defs-alistp (cdr defs)))))


(defthmd hons-assoc-equal-interp-defs-alistp
  (implies (and (hons-assoc-equal x obligs)
                (interp-defs-alistp obligs))
           (let ((entry (hons-assoc-equal x obligs)))
             (case-match entry
               ((& formals body . &)
                (and (pseudo-termp body)
                     (nonnil-symbol-listp formals)
                     (no-duplicatesp-equal formals))))))
  :hints (("goal" :induct (hons-assoc-equal x obligs))))

(in-theory (disable interp-defs-alistp))


;; This returns three values: rune, formals, and body of
;; the named function.  Overrides are user-provided alternative
;; definitions; we return the flag so that error messages can be more
;; helpful.  We allow definitions to be overridden in the table
;; interp-def-overrides, as follows:
;; (table interp-def-overrides
;;        'foo '((:definition foo-alt-def) ;; rune
;;               (a b c)                   ;; formals
;;               . (bar a (baz b c)))))    ;; body
;; This should work properly provided ACL2 can prove the definitional
;; equation using a :BY hint of the rune, as follows:
;; (thm (equal (foo a b c)
;;             (bar a (baz b c)))
;;      :hints (("goal" :by (:definition foo-alt-def))))
;; This function doesn't handle errors; in particular, if the function
;; isn't found in the override table or the world, the formals and
;; body returned will be :NONE and NIL respectively.
;; (defun interp-function-from-world (fn world)
;;   (declare (xargs :guard (and (symbolp fn)
;;                               (plist-worldp world))))
;;   (b* ((alist (table-alist 'interp-def-overrides world))
;;        ;; We use hons-assoc-equal rather than assoc-equal
;;        ;; because it doesn't have an alistp guard.
;;        (look (hons-assoc-equal fn alist)))
;;     (if (eql (len look) 3)
;;         (mv t (cadr look) (caddr look) (cdddr look))
;;       (mv nil fn
;;           (fgetprop fn 'formals :none world)
;;           (fgetprop fn 'unnormalized-body nil world)))))

;; (in-theory (disable interp-function-from-world))


(defun interp-function-lookup (fn defs overrides world)
  (declare (xargs :guard (and (symbolp fn)
                              (interp-defs-alistp defs)
                              (interp-defs-alistp overrides)
                              (plist-worldp world))
                  :guard-hints
                  (("goal" :in-theory
                    (enable
                     hons-assoc-equal-interp-defs-alistp)))))
  (b* ((look (hons-get fn defs))
       ((when look)
        (mv nil
            (caddr look)
            (cadr look)
            defs))
       (ov-look (hons-get fn overrides))
       ((when ov-look)
        (mv nil
            (caddr ov-look)
            (cadr ov-look)
            (hons-acons fn (cdr ov-look) defs)))
       (formals (fgetprop fn 'formals :none world))
       (body (fgetprop fn 'unnormalized-body nil world))
       ((when (not body))
        (mv (msg
             "Function definition not found: ~x0"
             fn) nil nil nil))
       ((when (not (pseudo-termp body)))
        (mv (msg
             "Body of ~x0 found, but not a pseudo-term: ~x1"
             fn body) nil nil nil))
       ((when (eq formals :none))
        (mv (msg
             "Function formals not found: ~x0"
             fn) nil nil nil))
       ((when (not (and (nonnil-symbol-listp formals)
                        (no-dupsp formals))))
        (mv (msg
             "Formals of ~x0 found, but not well-formed: ~x1"
             fn formals) nil nil nil))
       (defs (hons-acons fn (list* formals body fn) defs)))
    (mv nil body formals defs)))





(defthm interp-function-lookup-defs-alistp
  (b* (((mv erp & & out-defs)
        (interp-function-lookup fn in-defs overrides world)))
    (implies (and (not erp) (symbolp fn)
                  (interp-defs-alistp overrides))
             (iff (interp-defs-alistp out-defs)
                  (interp-defs-alistp in-defs))))
  :hints(("Goal" :in-theory
          (e/d (interp-defs-alistp
                hons-assoc-equal-interp-defs-alistp)))))


(defthm interp-function-lookup-defs-alistp-means-in-defs-alistp
  (b* (((mv erp & & out-defs)
        (interp-function-lookup fn in-defs overrides world)))
    (implies (and (not (interp-defs-alistp in-defs))
                  (not erp))
             (not (interp-defs-alistp out-defs))))
  :hints(("Goal" :in-theory (enable interp-defs-alistp))))

(defthm interp-function-lookup-wfp
  (b* (((mv erp body formals &)
        (interp-function-lookup fn in-defs overrides world)))
    (implies (and (not erp)
                  (interp-defs-alistp in-defs)
                  (interp-defs-alistp overrides))
             (and (pseudo-termp body)
                  (nonnil-symbol-listp formals)
                  (no-duplicatesp-equal formals))))
  :hints(("Goal" :in-theory
          (enable
           hons-assoc-equal-interp-defs-alistp))))




(defun interp-defs-alist-clauses (defs)
  (declare (xargs
            :guard (interp-defs-alistp defs)
            :guard-hints(("Goal" :in-theory
                          (enable interp-defs-alistp)))))
  (if (atom defs)
      nil
    (cons `((not (use-by-hint ',(cdddar defs))) ;; rune
            (equal (,(caar defs) . ,(cadar defs)) ;;(fn . formals)
                   ,(caddar defs))) ;; body
          (interp-defs-alist-clauses (cdr defs)))))




(defevaluator ifl-ev ifl-ev-lst
  ((if a b c)
   (equal a b)
   (not x)
   (use-by-hint x)))

(local (def-ruleset! ifl-ev-constraints
         '(ifl-ev-constraint-0
           ifl-ev-constraint-1
           ifl-ev-constraint-2
           ifl-ev-constraint-3
           ifl-ev-constraint-4
           ifl-ev-constraint-5
           ifl-ev-constraint-6
           ifl-ev-constraint-7
           ifl-ev-constraint-8
           ifl-ev-constraint-9)))


(def-ev-theoremp ifl-ev)

(defthm ifl-ev-theoremp-conjuncts
  (iff (ifl-ev-theoremp (conjoin (cons a b)))
       (and (ifl-ev-theoremp a)
            (ifl-ev-theoremp (conjoin b))))
  :hints (("goal" :use
           ((:instance ifl-ev-falsify
                       (x (conjoin (cons a b)))
                       (a (ifl-ev-falsify a)))
            (:instance ifl-ev-falsify
                       (x a)
                       (a (ifl-ev-falsify (conjoin (cons a b)))))
            (:instance ifl-ev-falsify
                       (x (conjoin (cons a b)))
                       (a (ifl-ev-falsify (conjoin b))))
            (:instance ifl-ev-falsify
                       (x (conjoin b))
                       (a (ifl-ev-falsify (conjoin (cons a b)))))))))


(defthm ifl-ev-theoremp-remove-first-lit-when-false
  (implies (ifl-ev-theoremp (list 'not lit))
           (iff (ifl-ev-theoremp (disjoin (cons lit clause)))
                (ifl-ev-theoremp (disjoin clause))))
  :hints (("Goal" :use
           ((:instance ifl-ev-falsify
                       (x (disjoin clause))
                       (a (ifl-ev-falsify (disjoin (cons lit clause)))))
            (:instance ifl-ev-falsify
                       (x (list 'not lit))
                       (a (ifl-ev-falsify (disjoin clause))))
            (:instance ifl-ev-falsify
                       (x (disjoin (cons lit clause)))
                       (a (ifl-ev-falsify (disjoin clause)))))))
  :otf-flg t)


(defthm ifl-ev-of-disjoin-append
  (iff (ifl-ev (disjoin (append a b)) al)
       (or (ifl-ev (disjoin a) al)
           (ifl-ev (disjoin b) al))))

(defthm ifl-ev-theoremp-of-conjoin-clauses-cons
  (iff (ifl-ev-theoremp
        (conjoin-clauses (cons cl1 clrest)))
       (and (ifl-ev-theoremp (disjoin cl1))
            (ifl-ev-theoremp (conjoin-clauses clrest))))
  :hints(("Goal" :in-theory (enable conjoin-clauses disjoin-lst))))

(defthm ifl-ev-theoremp-of-conjoin-clauses-append
  (iff (ifl-ev-theoremp
        (conjoin-clauses (append cls1 cls2)))
       (and (ifl-ev-theoremp (conjoin-clauses cls1))
            (ifl-ev-theoremp (conjoin-clauses cls2))))
  :hints (("subgoal *1/1" :in-theory (enable conjoin-clauses))))








(defthm hons-assoc-equal-ifl-ev-defs-alist-equality
  (let ((entry (hons-assoc-equal fn defs)))
    (implies (and (ifl-ev-theoremp
                   (conjoin-clauses
                    (interp-defs-alist-clauses defs)))
                  (interp-defs-alistp defs)
                  entry)
             (equal
              (equal (ifl-ev (cons fn (cadr entry)) a)
                     (ifl-ev (caddr entry) a))
              t)))
  :hints(("goal" :in-theory
          (enable interp-defs-alistp use-by-hint))
         ("Subgoal *1/2"
          :use ((:instance
                 ifl-ev-falsify
                 (x (disjoin
                     `((equal (,fn . ,(cadar defs))
                              ,(caddar defs))))))))))




(defthm interp-function-lookup-theoremp-defs-history
  (b* (((mv erp & & out-defs)
        (interp-function-lookup fn in-defs overrides world)))
    (implies (and (ifl-ev-theoremp
                        (conjoin-clauses
                         (interp-defs-alist-clauses out-defs)))
                  (not erp))
             (ifl-ev-theoremp
              (conjoin-clauses
               (interp-defs-alist-clauses in-defs))))))



(defthm interp-function-lookup-correct-1
  (mv-let (erp body formals out-defs)
    (interp-function-lookup fn in-defs overrides world)
    (implies (and (not erp)
                  (ifl-ev-theoremp
                   (conjoin-clauses
                    (interp-defs-alist-clauses out-defs)))
                  (interp-defs-alistp in-defs)
                  (interp-defs-alistp overrides))
             (equal (ifl-ev body a)
                    (ifl-ev (cons fn formals) a))))
  :hints(("goal" :in-theory
          (e/d (hons-assoc-equal-interp-defs-alistp
                use-by-hint)
               (default-car default-cdr pseudo-termp len))
          :use
          ((:instance
            ifl-ev-falsify
            (x (b* (((mv & body formals &)
                     (interp-function-lookup
                      fn in-defs overrides world)))
                 (disjoin `((equal (,fn . ,formals) ,body)))))
            (a a))))))

(in-theory (disable interp-function-lookup))




(defthm ifl-ev-lst-acons-non-member
  (implies (and (nonnil-symbol-listp vars)
                (not (member-equal key vars)))
           (equal (ifl-ev-lst
                   vars (cons (cons key val) rest))
                  (ifl-ev-lst
                   vars rest))))


(defun list-fix (x)
  (declare (xargs :guard t))
  (if (consp x)
      (cons (car x) (list-fix (cdr x)))
    nil))



(defthm ifl-ev-lst-pairlis
  (implies (and (nonnil-symbol-listp vars)
                (no-duplicatesp-equal vars)
                (equal (len vars) (len vals)))
           (equal (ifl-ev-lst vars (pairlis$ vars vals))
                  (list-fix vals))))

(defthm kwote-list-list-fix
  (equal (kwote-lst (list-fix x))
         (kwote-lst x)))

(defthm ifl-ev-cons-pairlis
  (implies (and (nonnil-symbol-listp vars)
                (no-duplicatesp-equal vars)
                (equal (len vars) (len vals))
                (not (eq fn 'quote)))
           (equal (ifl-ev (cons fn vars) (pairlis$ vars vals))
                  (ifl-ev (cons fn (kwote-lst vals)) nil)))
  :hints (("goal" :use
           ((:instance ifl-ev-constraint-0
                       (x (cons fn vars))
                       (a (pairlis$ vars vals)))))))







(defthm interp-function-lookup-correct-2
  (mv-let (erp body formals out-defs)
    (interp-function-lookup fn in-defs overrides world)
    (implies (and (not erp)
                  (ifl-ev-theoremp
                   (conjoin-clauses
                    (interp-defs-alist-clauses out-defs)))
                  (interp-defs-alistp in-defs)
                  (interp-defs-alistp overrides)
                  (equal (len formals) (len actuals))
                  (not (eq fn 'quote)))
             (equal (ifl-ev body (pairlis$ formals actuals))
                    (ifl-ev (cons fn (kwote-lst actuals)) nil)))))


(defthm len-ifl-ev-lst
  (equal (len (ifl-ev-lst x a))
         (len x))
  :hints (("goal" :induct (len x))))

(defthm interp-function-lookup-correct
  (mv-let (erp body formals out-defs)
    (interp-function-lookup fn in-defs overrides world)
    (implies (and (not erp)
                  (ifl-ev-theoremp
                   (conjoin-clauses
                    (interp-defs-alist-clauses out-defs)))
                  (interp-defs-alistp in-defs)
                  (interp-defs-alistp overrides)
                  (equal (len formals) (len actuals))
                  (not (eq fn 'quote)))
             (equal (ifl-ev body (pairlis$ formals
                                           (ifl-ev-lst actuals a)))
                    (ifl-ev (cons fn actuals) a))))
  :hints(("goal" :in-theory (e/d* (ifl-ev-constraint-0))
          :do-not-induct t)))




(local
 (progn
   (include-book "tools/def-functional-instance" :dir :system)
   (defevaluator foo-ev foo-ev-lst
     ((if a b c)
      (equal a b)
      (not a)
      (use-by-hint x)
      (cons a b)
      (car a)
      (cdr b)
      (consp a)
      (binary-+ a b)
      (unary-- a)
      (len x)))

   (defchoose foo-ev-falsify (a) (x)
     (not (foo-ev x a)))

   (def-functional-instance
     interp-function-lookup-correct-for-foo-ev
     interp-function-lookup-correct
     ((ifl-ev foo-ev)
      (ifl-ev-lst foo-ev-lst)
      (ifl-ev-falsify foo-ev-falsify))
     :hints (("Subgoal 2" :use foo-ev-constraint-0)
             ("Subgoal 1" :use foo-ev-falsify)))

   (def-functional-instance
     interp-function-lookup-correct-2-for-foo-ev
     interp-function-lookup-correct-2
     ((ifl-ev foo-ev)
      (ifl-ev-lst foo-ev-lst)
      (ifl-ev-falsify foo-ev-falsify)))

   (def-functional-instance
     interp-function-lookup-theoremp-defs-history-for-foo-ev
     interp-function-lookup-theoremp-defs-history
     ((ifl-ev foo-ev)
      (ifl-ev-lst foo-ev-lst)
      (ifl-ev-falsify foo-ev-falsify)))

   (def-functional-instance
     foo-ev-theoremp-of-conjoin-clauses-cons
     ifl-ev-theoremp-of-conjoin-clauses-cons
     ((ifl-ev foo-ev)
      (ifl-ev-lst foo-ev-lst)
      (ifl-ev-falsify foo-ev-falsify)))

   (def-functional-instance
     foo-ev-theoremp-of-conjoin-clauses-append
     ifl-ev-theoremp-of-conjoin-clauses-append
     ((ifl-ev foo-ev)
      (ifl-ev-lst foo-ev-lst)
      (ifl-ev-falsify foo-ev-falsify)))))
