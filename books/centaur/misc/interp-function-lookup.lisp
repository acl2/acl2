; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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
(include-book "std/util/bstar" :dir :system)
(include-book "tools/mv-nth" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "misc/untranslate-patterns" :dir :system)
(include-book "clause-processors/ev-theoremp" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)

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

(defthm eqlable-listp-when-nonnil-symbol-listp
  (implies (nonnil-symbol-listp x)
           (eqlable-listp x))
  :rule-classes :forward-chaining)

(defun interp-defs-alistp (defs)
  (declare (xargs :guard t))
  (or (atom defs)
      (and (let ((entry (car defs)))
             (case-match entry
               ((fn formals body . &)
                ;; the & is the rune equating the function call with
                ;; the body
                (and (symbolp fn)
                     (not (eq fn 'quote))
                     (pseudo-termp body)
                     (nonnil-symbol-listp formals)
                     (no-duplicatesp formals)))))
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



(defevaluator ifl-ev ifl-ev-lst
  ((if a b c)
   (equal a b)
   (not x)
   (iff a b)
   (implies a b)
   (typespec-check ts x)
   (use-by-hint x)))

(def-meta-extract ifl-ev ifl-ev-lst)

(local (in-theory (disable w)))

(defund meta-extract-function-formals/body (fn world)
  (declare (xargs :guard (and (symbolp fn)
                              (plist-worldp world))))
  (b* ((formula (meta-extract-formula-w fn world)))
    (case-match formula
      (('equal (!fn . formals) body . &)
       (b* (((unless (and (nonnil-symbol-listp formals)
                          (no-duplicatesp formals)))
             (mv (msg "Function ~x0 has ill-formed formals in definitional formula ~x1"
                      fn formula)
                 nil nil))
            ((unless (pseudo-termp body))
             (mv (msg "Function ~x0 has non-pseudo-term body in formula: ~x1"
                      fn formula) nil nil)))
         (mv nil formals body)))
      (& (mv (if (equal formula *t*)
                 (msg "Function ~x0 has no associated formula" fn)
               (msg "The formula of function ~x0 is not a simple EQUAL-based ~
                     definition: ~x1" fn formula))
             nil nil)))))

(defthm ifl-ev-meta-extract-function-formals/body
  (b* (((mv err formals body)
        (meta-extract-function-formals/body fn (w state))))
    (implies (and (ifl-ev-meta-extract-global-facts)
                  (not err))
             (equal (ifl-ev (cons fn formals) a)
                    (ifl-ev body a))))
  :hints(("Goal" :in-theory (e/d (meta-extract-function-formals/body
                                  ifl-ev-constraint-0)
                                 (ifl-ev-meta-extract-formula))
          :use ((:instance ifl-ev-meta-extract-formula
                 (name fn) (st state)))
          :cases ((eq fn 'quote))))
  :otf-flg t)

(defthm meta-extract-function-formals/body-well-formed
  (b* (((mv err formals body)
        (meta-extract-function-formals/body fn world)))
    (implies (not err)
             (and (nonnil-symbol-listp formals)
                  (no-duplicatesp formals)
                  (pseudo-termp body))))
  :hints(("Goal" :in-theory (enable meta-extract-function-formals/body))))


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
       (ov-look (or look (hons-get fn overrides)))
       ((when ov-look)
        (b* (((list formals body) (cdr ov-look))
             (defs (if look defs (hons-acons fn (cdr ov-look) defs)))
             ((unless (mbt (and (nonnil-symbol-listp formals)
                                (no-duplicatesp-eq formals)
                                (pseudo-termp body))))
              (mv (msg "Override for ~x0 ill-formed~%" fn)
                  nil nil nil)))
          (mv nil body formals defs)))
       ((mv err formals body)
        (meta-extract-function-formals/body fn world))
       ((when err) (mv err nil nil nil)))
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
    (implies (not erp)
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
                       (a (ifl-ev-falsify (disjoin clause)))))
           :in-theory (enable ifl-ev-disjoin-cons)))
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
                  ;; (interp-defs-alistp defs)
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
    (interp-function-lookup fn in-defs overrides (w state))
    (implies (and (not erp)
                  (ifl-ev-theoremp
                   (conjoin-clauses
                    (interp-defs-alist-clauses out-defs)))
                  ;; (interp-defs-alistp in-defs)
                  ;; (interp-defs-alistp overrides)
                  (ifl-ev-meta-extract-global-facts))
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
    (interp-function-lookup fn in-defs overrides (w state))
    (implies (and (not erp)
                  (ifl-ev-theoremp
                   (conjoin-clauses
                    (interp-defs-alist-clauses out-defs)))
                  ;; (interp-defs-alistp in-defs)
                  ;; (interp-defs-alistp overrides)
                  (equal (len formals) (len actuals))
                  (not (eq fn 'quote))
                  (ifl-ev-meta-extract-global-facts))
             (equal (ifl-ev body (pairlis$ formals actuals))
                    (ifl-ev (cons fn (kwote-lst actuals)) nil))))
  :hints (("goal" :do-not-induct t)
          (and stable-under-simplificationp
               '(:in-theory (enable ifl-ev-constraint-0)))))


(defthm len-ifl-ev-lst
  (equal (len (ifl-ev-lst x a))
         (len x))
  :hints (("goal" :induct (len x))))

(defthm interp-function-lookup-correct
  (mv-let (erp body formals out-defs)
    (interp-function-lookup fn in-defs overrides (w state))
    (implies (and (not erp)
                  (ifl-ev-theoremp
                   (conjoin-clauses
                    (interp-defs-alist-clauses out-defs)))
                  ;; (interp-defs-alistp in-defs)
                  ;; (interp-defs-alistp overrides)
                  (equal (len formals) (len actuals))
                  (not (eq fn 'quote))
                  (ifl-ev-meta-extract-global-facts))
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
      (typespec-check ts x)
      (implies a b)
      (iff a b)
      (cons a b)
      (car a)
      (cdr b)
      (consp a)
      (binary-+ a b)
      (unary-- a)
      (len x)))

   (def-meta-extract foo-ev foo-ev-lst)

   (def-functional-instance
     interp-function-lookup-correct-for-foo-ev
     interp-function-lookup-correct
     ((ifl-ev foo-ev)
      (ifl-ev-lst foo-ev-lst)
      (ifl-ev-falsify foo-ev-falsify)
      (ifl-ev-meta-extract-global-badguy
       foo-ev-meta-extract-global-badguy))
     :hints ((and stable-under-simplificationp
                  '(:use (foo-ev-constraint-0
                          foo-ev-falsify
                          foo-ev-meta-extract-global-badguy)))))

   (def-functional-instance
     interp-function-lookup-correct-2-for-foo-ev
     interp-function-lookup-correct-2
     ((ifl-ev foo-ev)
      (ifl-ev-lst foo-ev-lst)
      (ifl-ev-falsify foo-ev-falsify)
      (ifl-ev-meta-extract-global-badguy
       foo-ev-meta-extract-global-badguy)))

   (def-functional-instance
     interp-function-lookup-theoremp-defs-history-for-foo-ev
     interp-function-lookup-theoremp-defs-history
     ((ifl-ev foo-ev)
      (ifl-ev-lst foo-ev-lst)
      (ifl-ev-falsify foo-ev-falsify)
      (ifl-ev-meta-extract-global-badguy
       foo-ev-meta-extract-global-badguy)))

   (def-functional-instance
     foo-ev-theoremp-of-conjoin-clauses-cons
     ifl-ev-theoremp-of-conjoin-clauses-cons
     ((ifl-ev foo-ev)
      (ifl-ev-lst foo-ev-lst)
      (ifl-ev-falsify foo-ev-falsify)
      (ifl-ev-meta-extract-global-badguy
       foo-ev-meta-extract-global-badguy)))

   (def-functional-instance
     foo-ev-theoremp-of-conjoin-clauses-append
     ifl-ev-theoremp-of-conjoin-clauses-append
     ((ifl-ev foo-ev)
      (ifl-ev-lst foo-ev-lst)
      (ifl-ev-falsify foo-ev-falsify)
      (ifl-ev-meta-extract-global-badguy
       foo-ev-meta-extract-global-badguy)))))

