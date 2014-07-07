; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "../logic/top")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; This file introduces the @context macro, which forms the basis for defun@,
;; defthm@, deftheorem, and defderiv.  Before looking at the implementation
;; here, you may wish to browse through some of our basic builders, to see
;; what this code is used to support.




;; Patterns to describe terms and formulas.
;;
;; We can use patterns to concisely describe the shapes of terms and formulas.
;; The patterns we understand are described by the following tables.
;;
;;   term pattern             matches                       bindings
;; ----------------------------------------------------------------------------
;;     (? sym)                  any term                      sym bound here
;;     t, nil                   ''t, ''nil                    none
;;     0, 1, 2, ...             ''0, ''1, ''2, ...            none
;;     a quoted constant        exactly that constant         none
;;     a variable               exactly that variable         none
;;     (f tpat1 ... tpatN)      a matching call of f          tpat bindings
;;
;;   formula pattern          matches                       bindings
;; ----------------------------------------------------------------------------
;;     symbol                   any formula                   sym bound here
;;     (= tpat1 tpat2)          matching equalities           tpat bindings
;;     (!= tpat1 tpat2)         matching inequalities         tpat bindings
;;     (! fpat)                 matching negations            fpat bindings
;;     (v fpat1 fpat2)          matching disjunctions         fpat bindings
;;
;; We can also describe sigmas with patterns, using lists of (var . tpat)
;; pairs.

(mutual-recursion
 (defun dd.term-patternp (x)
   (declare (xargs :mode :program))
   (or (equal x t)
       (equal x nil)
       (natp x)
       (logic.constantp x)
       (logic.variablep x)
       (and (consp x)
            (cond ((equal (first x) '?)
                   (and (tuplep 2 x)
                        (logic.variablep (second x))))
                  (t
                   (and (logic.function-namep (first x))
                        (true-listp (cdr x))
                        (dd.term-pattern-listp (cdr x))))))
       (ACL2::cw "Warning: invalid dd.term-patternp: ~x0~%" x)))
 (defun dd.term-pattern-listp (x)
   (declare (xargs :mode :program))
   (if (consp x)
       (and (dd.term-patternp (car x))
            (dd.term-pattern-listp (cdr x)))
     t)))

(defun dd.formula-patternp (x)
  (declare (xargs :mode :program))
  (or (logic.variablep x)
      (and (consp x)
           (cond ((equal (first x) '=)
                  (and (tuplep 3 x)
                       (dd.term-patternp (second x))
                       (dd.term-patternp (third x))))
                 ((equal (first x) '!=)
                  (and (tuplep 3 x)
                       (dd.term-patternp (second x))
                       (dd.term-patternp (third x))))
                 ((equal (first x) '!)
                  (and (tuplep 2 x)
                       (dd.formula-patternp (second x))))
                 ((equal (first x) 'v)
                  (and (tuplep 3 x)
                       (dd.formula-patternp (second x))
                       (dd.formula-patternp (third x))))
                 (t nil)))
      (ACL2::cw "Warning: invalid dd.formula-patternp: ~x0~%" x)))

(defun dd.formula-pattern-listp (x)
  (declare (xargs :mode :program))
  (if (consp x)
      (and (dd.formula-patternp (car x))
           (dd.formula-pattern-listp (cdr x)))
    t))

(defun dd.sigma-patternp (x)
  (declare (xargs :mode :program))
  (if (consp x)
      (or (and (consp (car x))
               (logic.variablep (car (car x)))
               (dd.term-patternp (cdr (car x)))
               (dd.sigma-patternp (cdr x)))
          (ACL2::cw "Warning: invalid dd.sigma-patternp entry: ~x0~%" (car x)))
    t))




;; Matching Lisp objects against patterns.
;;
;; When we write a Lisp function or an ACL2 theorem, we often want to know if
;; some Lisp object matches a pattern.  For example, perhaps we are writing a
;; function (foo x), and as a guard we want to say that x is a proof whose
;; conclusion has the form A v B.
;;
;; We are going to write some macros which can generate code to perform this
;; kind of matching.  To our macros, things like x and (logic.conclusion x) are
;; just s-expressions, i.e., fragments of Lisp syntax that have some semantic
;; meaning we are ignorant of.  We call these things "paths".  Continuing our
;; example, the path we are interested in is literally the s-expression
;; (logic.conclusion x).
;;
;; The first issue to address is deciding if our path has the proper structure
;; as far as its connectives, the names of any functions used within it, and
;; occurrences of any explicit constants.  Continuing our example, since our
;; pattern is A v B, we want to check that the fmtype of our path is por*.
;;
;; To handle complex patterns, we allow our path to "grow" as we make the
;; match.  For example, to test PATH against A v (B v C), we first check that
;; the fmtype of PATH is por*.  Then, for the recursive call, we change our
;; path to (logic.vrhs PATH), and try to match that against (B v C).

(mutual-recursion
 (defun dd.term-pattern-structure-tests (path pat)
   (declare (xargs :mode :program))
   (cond ((or (equal pat t)
              (equal pat nil)
              (natp pat))
          (list `(equal ,path '',pat)))
         ((logic.constantp pat)
          (list `(equal ,path ,pat)))
         ((logic.variablep pat)
          (list `(equal ,path ',pat)))
         ((equal (first pat) '?)
          nil)
         (t
          (app (list `(logic.functionp ,path)
                     `(equal (logic.function-name ,path) ',(first pat))
                     `(equal (len (logic.function-args ,path)) ,(len (cdr pat))))
               (dd.term-pattern-structure-tests-list `(logic.function-args ,path) (cdr pat))))))
 (defun dd.term-pattern-structure-tests-list (path pat)
   (declare (xargs :mode :program))
   (if (consp pat)
       (app (dd.term-pattern-structure-tests `(car ,path) (car pat))
            (dd.term-pattern-structure-tests-list `(cdr ,path) (cdr pat)))
     nil)))

(defun dd.formula-pattern-structure-tests (path pat)
   (declare (xargs :mode :program))
   (cond ((symbolp pat)
          nil)
         ((equal (first pat) '=)
          (cons `(equal (logic.fmtype ,path) 'pequal*)
                (app (dd.term-pattern-structure-tests `(logic.=lhs ,path) (second pat))
                     (dd.term-pattern-structure-tests `(logic.=rhs ,path) (third pat)))))
         ((equal (first pat) '!=)
          (cons `(equal (logic.fmtype ,path) 'pnot*)
                (cons `(equal (logic.fmtype (logic.~arg ,path)) 'pequal*)
                      (app (dd.term-pattern-structure-tests `(logic.=lhs (logic.~arg ,path)) (second pat))
                           (dd.term-pattern-structure-tests `(logic.=rhs (logic.~arg ,path)) (third pat))))))
         ((equal (first pat) '!)
          (cons `(equal (logic.fmtype ,path) 'pnot*)
                (dd.formula-pattern-structure-tests `(logic.~arg ,path) (second pat))))
         ((equal (first pat) 'v)
          (cons `(equal (logic.fmtype ,path) 'por*)
                (app (dd.formula-pattern-structure-tests `(logic.vlhs ,path) (second pat))
                     (dd.formula-pattern-structure-tests `(logic.vrhs ,path) (third pat)))))
         (t
          (ACL2::er hard 'dd.formula-pattern-structure-tests
                    "Bad formula pattern encountered: ~x0~%" pat))))




;; Context variables and bindings maps.
;;
;; Given a pattern like A v B, we say A and B are "context variables."  In
;; order to properly match patterns with repeated variables (e.g., A v A), we
;; need to keep track of which parts of the formula are bound to each variable.
;; To do this, we build a "bindings map" that associates each context variable
;; with the paths it is bound to.  For example, if PATH is (conclusion x) and
;; pattern is A v B, we will generate a map that contains these entries:
;;
;;    (A . (logic.vlhs (conclusion x)))
;;    (B . (logic.vrhs (conclusion x)))
;;
;; If a variable is used multiple times, it will show up repeatedly in the map,
;; e.g., matching (conclusion x) against A v A would yield:
;;
;;    (A . (logic.vlhs (conclusion x)))
;;    (A . (logic.vrhs (conclusion x)))
;;
;; We can look for duplicate occurrences in order to see which equality tests
;; we will need to generate, e.g., in the above example we would see that we
;; need to check:
;;
;;    (equal (logic.vlhs (conclusion x)) (logic.vrhs (conclusion x)))
;;
;; Since the same variable, A, is bound to each of these.  Since equality is
;; transitive, we only need n-1 checks for n occurrences of a context variable.

(mutual-recursion
 (defun dd.term-pattern-path-bindings (path pat)
   (declare (xargs :mode :program))
   (cond ((or (equal pat t)
              (equal pat nil)
              (natp pat)
              (logic.constantp pat)
              (logic.variablep pat))
          nil)
         ((equal (first pat) '?)
          (list (cons (second pat) path)))
         (t
          (dd.term-pattern-path-bindings-list `(logic.function-args ,path) (cdr pat)))))
 (defun dd.term-pattern-path-bindings-list (path pat)
   (declare (xargs :mode :program))
   (if (consp pat)
       (app (dd.term-pattern-path-bindings `(car ,path) (car pat))
            (dd.term-pattern-path-bindings-list `(cdr ,path) (cdr pat)))
     nil)))

(defun dd.formula-pattern-path-bindings (path pat)
  (declare (xargs :mode :program))
  (cond ((symbolp pat)
         (list (cons pat path)))
        ((equal (first pat) '=)
         (app (dd.term-pattern-path-bindings `(logic.=lhs ,path) (second pat))
              (dd.term-pattern-path-bindings `(logic.=rhs ,path) (third pat))))
        ((equal (first pat) '!=)
         (app (dd.term-pattern-path-bindings `(logic.=lhs (logic.~arg ,path)) (second pat))
              (dd.term-pattern-path-bindings `(logic.=rhs (logic.~arg ,path)) (third pat))))
        ((equal (first pat) '!)
         (dd.formula-pattern-path-bindings `(logic.~arg ,path) (second pat)))
        ((equal (first pat) 'v)
         (app (dd.formula-pattern-path-bindings `(logic.vlhs ,path) (second pat))
              (dd.formula-pattern-path-bindings `(logic.vrhs ,path) (third pat))))
        (t
         (ACL2::er hard 'dd.formula-pattern-path-bindings
                   "Bad formula pattern encountered: ~x0~%" pat))))

(defun dd.path-bindings-to-equalities (x)
  (declare (xargs :mode :program))
  (if (consp x)
      (let ((result (lookup (car (car x)) (cdr x))))
        (if result
            (cons `(equal ,(cdr (car x)) ,(cdr result))
                  (dd.path-bindings-to-equalities (cdr x)))
          (dd.path-bindings-to-equalities (cdr x))))
    nil))




;; Constructing objects using patterns.
;;
;; After you've matched an object against some pattern, it's quite convenient
;; to be able to refer to parts of that object via the context variables you
;; just used.  That is, if you match x against A v B, you'd like to be able to
;; talk about A and B instead of (logic.vlhs x) and (logic.vrhs x).
;;
;; Once we've built the binding map, we can easily choose a representative for
;; A and B.  In fact, we can do better than this: if you provide a new pattern
;; that describes an object you'd like to construct in terms of the context
;; variables you've already matched, we can write the constructor code to
;; reassemble the object.  E.g., now that you've matched x against A v B, you
;; can say B v A and we can fill in (logic.por (logic.vrhs x) (logic.vlhs x)).

(mutual-recursion
 (defun dd.term-from-path-bindings (pat bindings)
   (declare (xargs :mode :program))
   (cond ((equal pat t)
          '''t)
         ((equal pat nil)
          '''nil)
         ((natp pat)
          (list 'quote (list 'quote pat)))
         ((logic.constantp pat)
          (list 'quote pat))
         ((logic.variablep pat)
          (list 'quote pat))
         ((equal (first pat) '?)
          (let ((entry (lookup (second pat) bindings)))
            (if (consp entry)
                (cdr entry)
              (ACL2::er hard 'dd.term-from-path-bindings
                        "Pattern mentions ~x0, but this is not bound.~%" pat))))
         (t
          `(logic.function ',(car pat)
                  (list ,@(dd.term-from-path-bindings-list (cdr pat) bindings))))))
 (defun dd.term-from-path-bindings-list (pat bindings)
   (declare (xargs :mode :program))
   (if (consp pat)
       (cons (dd.term-from-path-bindings (car pat) bindings)
             (dd.term-from-path-bindings-list (cdr pat) bindings))
     nil)))

(defun dd.formula-from-path-bindings (pat bindings)
  (declare (xargs :mode :program))
  (cond ((symbolp pat)
         (let ((entry (lookup pat bindings)))
           (if (consp entry)
               (cdr entry)
             (ACL2::er hard 'dd.formula-from-path-bindings
                       "Pattern mentions ~x0, but this is not bound.~%" pat))))
        ((equal (first pat) '=)
         `(logic.pequal ,(dd.term-from-path-bindings (second pat) bindings)
                  ,(dd.term-from-path-bindings (third pat) bindings)))
        ((equal (first pat) '!=)
         `(logic.pnot (logic.pequal ,(dd.term-from-path-bindings (second pat) bindings)
                        ,(dd.term-from-path-bindings (third pat) bindings))))
        ((equal (first pat) '!)
         `(logic.pnot ,(dd.formula-from-path-bindings (second pat) bindings)))
        ((equal (first pat) 'v)
         `(logic.por ,(dd.formula-from-path-bindings (second pat) bindings)
               ,(dd.formula-from-path-bindings (third pat) bindings)))
        (t
         (ACL2::er hard 'dd.formula-from-path-bindings
                   "Bad formula pattern encountered: ~x0~%" pat))))

(defun dd.formula-from-path-bindings-list (pat bindings)
  (declare (xargs :mode :program))
  (if (consp pat)
      (cons (dd.formula-from-path-bindings (car pat) bindings)
            (dd.formula-from-path-bindings-list (cdr pat) bindings))
    nil))

(defun dd.sigma-from-path-bindings (x bindings)
  (declare (xargs :mode :program))
  (if (consp x)
      (cons `(cons ',(car (car x))
                   ,(dd.term-from-path-bindings (cdr (car x)) bindings))
            (dd.sigma-from-path-bindings (cdr x) bindings))
    nil))




;; Matching lots of patterns at once.
;;
;; It's often the case that we'll want to try to pattern match several objects,
;; and share their variables.  E.g., for modus ponens, we want to match x with
;; A and y with ~A v B, and we want these A's to relate to one another.
;;
;; We introduce "multi patterns" objects to describe a list of matches to be
;; made.  Each entry in the list is a 3-tuple of the form
;;
;;    (type path pattern)
;;
;; Where type is either term, formula, proof, or constant.
;;
;;   - If type is term or formula, we try to match path against pattern, which
;;     should be a term or formula pattern, respectively.
;;
;;   - If type is proof, we try to match (conclusion path) against the formula
;;     pattern.  This isn't really needed but it is very convenient.
;;
;;   - If type is constant, the path may only be a variable, i.e., (? a), and
;;     we will require (constantp path).

(defun dd.multi-patternsp (x)
  (declare (xargs :mode :program))
  (if (consp x)
      (and (tuplep 3 (car x))
           (let ((type (first (car x)))
                 ;; we ignore path
                 (pattern (third (car x))))
             (cond ((equal type 'term)
                    (dd.term-patternp pattern))
                   ((equal type 'formula)
                    (dd.formula-patternp pattern))
                   ((equal type 'proof)
                    (dd.formula-patternp pattern))
                   ((equal type 'constant)
                    (and (tuplep 2 pattern)
                         (equal (first pattern) '?)
                         (logic.variablep (second pattern))))
                   (t
                    (ACL2::cw "Warning: invalid type for dd.multi-patternsp: ~x0~%" x))))
           (dd.multi-patternsp (cdr x)))
    t))

(defun dd.multi-patterns-structure-tests (x)
  (declare (xargs :mode :program))
  (if (consp x)
      (let* ((entry (car x))
             (type  (first entry))
             (path  (second entry))
             (pattern (third entry)))
        (app (cond ((equal type 'term)
                    (dd.term-pattern-structure-tests path pattern))
                   ((equal type 'formula)
                    (dd.formula-pattern-structure-tests path pattern))
                   ((equal type 'proof)
                    (dd.formula-pattern-structure-tests `(logic.conclusion ,path) pattern))
                   ((equal type 'constant)
                    (list `(logic.constantp ,path)))
                   (t
                    (ACL2::er hard 'dd.multi-patterns-structure-tests
                              "Bad multipattern entry: ~x0.~%" entry)))
             (dd.multi-patterns-structure-tests (cdr x))))
    nil))

(defun dd.multi-patterns-path-bindings (x)
  (declare (xargs :mode :program))
  (if (consp x)
      (let ((type (first (car x)))
            (path (second (car x)))
            (pattern (third (car x))))
        (app (cond ((equal type 'term)
                    (dd.term-pattern-path-bindings path pattern))
                   ((equal type 'formula)
                    (dd.formula-pattern-path-bindings path pattern))
                   ((equal type 'proof)
                    (dd.formula-pattern-path-bindings `(logic.conclusion ,path) pattern))
                   ((equal type 'constant)
                    (let ((variable (second pattern)))
                      (list (cons variable path))))
                   (t
                    (ACL2::er hard 'dd.multi-patterns-path-bindings
                              "Bad multipattern entry: ~x0.~%" (car x))))
             (dd.multi-patterns-path-bindings (cdr x))))
    nil))




;; Pattern-based derivations.
;;
;; We also provide support for writing derivations with patterns.  Each line in
;; a derivation has the form:
;;
;;      (conclusion justification [name])
;;
;; Where:
;;
;;   - Each conclusion is a formula pattern which describes what this step
;;     concludes.  Typically this is only used for documentation purpoess.
;;
;;   - Each justification explains how to arrive at this conclusion.  It must
;;     have the form (foo ...), and our documentation tools will mention foo
;;     when describing this derivation.  As special conveniences,
;;        * (@given x) can be used to refer to an existing proof.  We write
;;          this instead of x so that our documentation tools know what is
;;          given.
;;        * @- may be used to refer to the proof on the previous line,
;;        * @-- may be used to refer to the proof on the two-previous line,
;;        * Previously defined named lines may also be used by writing their
;;          names.
;;
;;   - Names are optional but sometimes necessary so that you can refer back
;;     to something you proved earlier.  If omitted, a name such as __LINE3__
;;     will be generated.  I typically use *1, *2, ... for names.

(defun dd.deriv-linep (x)
  (declare (xargs :mode :program))
  (or (and (or (tuplep 2 x)
               (tuplep 3 x))
           (let ((conclusion    (first x))
                 (justification (second x))
                 (name          (third x)))
             (and (dd.formula-patternp conclusion)
                  (true-listp justification)
                  (consp justification)
                  (logic.function-namep (car justification))
                  (symbolp name))))
      (ACL2::cw "Warning: invalid deriv line: ~x0.~%" x)))

(defun dd.deriv-linesp (x)
  (declare (xargs :mode :program))
  (if (consp x)
      (and (dd.deriv-linep (car x))
           (dd.deriv-linesp (cdr x)))
    t))

(defun dd.deriv-assign-names (x n)
  ;; Fill in the names, wherever they have been omitted, with __LINE<N>__
  (declare (xargs :mode :program))
  (if (consp x)
      (let ((conclusion    (first (car x)))
            (justification (second (car x)))
            (name          (third (car x))))
        (if (not name)
            (cons (list conclusion justification
                        (ACL2::intern-in-package-of-symbol
                         (ACL2::concatenate 'ACL2::string "__LINE"
                                            (ACL2::coerce (ACL2::explode-atom n 10)
                                                          'ACL2::string) "__")
                         'proofp))
                  (dd.deriv-assign-names (cdr x) (+ n 1)))
          (cons (car x)
                (dd.deriv-assign-names (cdr x) n))))
    nil))

(defun dd.deriv-link-subst (just prev1 prev2)
  ;; "just" is a justification of some line.  We have no idea what it looks
  ;; like, so we walk throughout it as if it were a tree.  We replace any
  ;; occurrences of @- and @-- with the names given in prev1 and prev2,
  ;; respectively.
  (declare (xargs :mode :program))
  (cond ((equal just '@-)
         (or prev1
             (ACL2::er ACL2::hard 'dd.deriv-link-subst
                       "Attempting to substitute nil into @-.~%")))
        ((equal just '@--)
         (or prev2
             (ACL2::er ACL2::hard 'dd.deriv-link-subst
                       "Attempting to substitute nil into @--.~%")))
        ((not (consp just))
         just)
        (t
         (cons (dd.deriv-link-subst (car just) prev1 prev2)
               (dd.deriv-link-subst (cdr just) prev1 prev2)))))

(defun dd.deriv-link-relative (x prev1 prev2)
  ;; We change all occurrences of @- and @-- in each justification with the
  ;; names of the lines they refer to.
  (declare (xargs :mode :program))
  (if (consp x)
      (let ((conclusion    (first (car x)))
            (justification (second (car x)))
            (name          (third (car x))))
        (cons
         (list conclusion (dd.deriv-link-subst justification prev1 prev2) name)
         (dd.deriv-link-relative (cdr x) name prev1)))
    nil))

(defun dd.deriv-letify1 (x)
  ;; We change these post-linking lines into lines for a let* statement, and
  ;; eliminate any (@given x) with x.
  (declare (xargs :mode :program))
  (if (consp x)
      (let ((justification (second (car x)))
            (name          (third (car x))))
        (if (equal (car justification) '@given)
            (if (tuplep 2 justification)
                ;; replace (@given x) with x
                (cons `(,name ,(second justification))
                      (dd.deriv-letify1 (cdr x)))
              (ACL2::er ACL2::hard 'dd.deriv-letify "Invalid @given: ~x0 ~%" justification))
          ;; other justifications are not altered.
          (cons `(,name ,justification)
                (dd.deriv-letify1 (cdr x)))))
    nil))

(defun dd.deriv-letify (x)
  ;; Converts a list of derivation lines into a let* statement.  This bundles
  ;; the renaming, linking, and letification steps.
  (declare (xargs :mode :program))
  (if (not (dd.deriv-linesp x))
      (ACL2::er ACL2::hard 'dd.deriv-letify "Invalid derivation: ~x0.~%" x)
    (let* ((named    (dd.deriv-assign-names x 1))
           (linked   (dd.deriv-link-relative named nil nil))
           (letified (dd.deriv-letify1 linked))
           (lastname (car (car (ACL2::last letified)))))
      `(let* ,letified ,lastname))))





;; The @context macro.
;;
;; All of the tools we have developed so far are brought together with @context
;; which is a sophisticated macro.  When I first developed pattern matching
;; support, I had no notion of contexts.  Here's a typical example of using one
;; of my early match macros:
;;
;; (defthm forcing-conclusion-of-merge-implications-bldr
;;   (implies (force (and (appeal-structurep x)
;;                        (appeal-structurep y)
;;                        (@match (proof x (v (! A) C))
;;                                (proof y (v (! B) C)))))
;;            (equal (conclusion (merge-implications-bldr x y))
;;                   (por (pnot (por (~arg (vlhs (conclusion x)))
;;                                   (~arg (vlhs (conclusion y)))))
;;                        (vrhs x)))))
;;
;; Even this kind of matching was a big improvement from manually writing out
;; everything you had to test, but obviously we could benefit from being able
;; to use context variables in the conclusion of the theorem.  But merely
;; adding some kind of "body" parameter to the match* statement wouldn't be
;; sufficient: we want the matching statements to occur in the hyps of the
;; implication, but we want to refer to the context variables we matched much
;; later.  I introduced @context to address this.
;;
;; The @context macro establishes a scope for all the context variables matched
;; within it.  Within a @context, we can embed certain special forms:
;;
;;   (@match ...)    - introduce code for pattern matching some multipatterns
;;   (@extend ...)   - manually inject extra paths into the context
;;   (@expand ...)   - alias for @extend because I always forget its name
;;   (@term ...)     - construct a term based on a pattern
;;   (@formula ...)  - construct a formula based on a pattern
;;   (@formulas ...) - construct a list of formulas based on some patterns
;;   (@sigma ...)    - construct a sigma based on a pattern
;;   (@derive ...)   - build a proof using our derivation syntax
;;
;; We could now write our example theorem in the following style:
;;
;; (@context
;;   (defthm forcing-conclusion-of-merge-implications-bldr
;;     (implies (force (and (appeal-structurep x)
;;                          (appeal-structurep y)
;;                          (@match (proof x (v (! A) C))
;;                                  (proof y (v (! B) C)))))
;;              (equal (conclusion (merge-implications-bldr x y))
;;                     (@formula (v (! (v A B)) C))))))
;;
;; We process the argument to @context in two passes.
;;
;;  (1) Namespace building.  We consider all of the @match and @extend/expand
;;      operations which occur in the context, and create a binding map out of
;;      their variables.  Note that this namespace is shared throughout the
;;      entire context.
;;
;;  (2) Code generation.  We then replace each of our special forms with some
;;      regular Lisp code.
;;
;;        - (@match <multi-patterns>) forms are replaced by all the structural
;;          checks they induce, and also with equality checks for the whole
;;          binding.
;;
;;          NOTE: the bindings checks are strange; you should probably limit
;;          yourself to one @match per context.
;;            -- BOZO maybe we should enforce a limit?
;;            -- BOZO maybe only do local bindings checks instead?
;;
;;        - (@extend/expand <multi-patterns> body) forms are replaced by their
;;          bodies (which are recursively processed)
;;
;;        - @term, @formula, @formulas, and @sigma are replaced by expressions
;;          which will construct the object described by their pattern
;;
;;        - (@derive <lines>) is replaced with its "letified" equivalent.
;;
;; @context cannot be purposefully nested.  The outer @context will treat the
;; inner @context as just another function call, and steal all of its special
;; forms as if they were its own.  This eliminates all of the special forms
;; inside the inner @context, turning it into a no-op.

(defun dd.context-gather (x)
  (declare (xargs :mode :program))
  (cond ((not (consp x))
         nil)
        ;((memberp (first x) '(@match-term))
        ; (if (and (tuplep 3 x)
        ;          (dd.term-patternp (third x)))
        ;     (dd.term-pattern-path-bindings (second x) (third x))
        ;   (ACL2::er hard 'dd.context-gather "Invalid @match-term encountered: ~x0 ~%" x)))
        ;((memberp (first x) '(@match-formula))
        ; (if (and (tuplep 3 x)
        ;          (dd.formula-patternp (third x)))
        ;     (dd.formula-pattern-path-bindings  (second x) (third x))
        ;   (ACL2::er hard 'dd.context-gather "Invalid @match-formula encountered: ~x0 ~%" x)))
        ;((memberp (first x) '(@match-proof))
        ; (if (and (tuplep 3 x)
        ;          (dd.formula-patternp (third x)))
        ;     (dd.formula-pattern-path-bindings  `(logic.conclusion ,(second x)) (third x))
        ;   (ACL2::er hard 'dd.context-gather "Invalid @match-proof encountered: ~x0 ~%" x)))
        ((memberp (first x) '(@match))
         (if (dd.multi-patternsp (cdr x))
             (dd.multi-patterns-path-bindings (cdr x))
           (ACL2::er hard 'dd.context-gather "Invalid @match encountered: ~x0 ~%" x)))
        ((memberp (first x) '(@extend @expand))
         (if (dd.multi-patternsp (second x))
             (dd.multi-patterns-path-bindings (second x))
           (ACL2::er hard 'dd.context-gather "Invalid ~x0 encountered: ~x1 ~%" (first x) x)))
        (t
         (app (dd.context-gather (car x))
              (dd.context-gather (cdr x))))))

(defun dd.context-replace (x bindings)
  (declare (xargs :mode :program))
  (cond ((not (consp x))
         x)
        ;((equal (first x) '@match-term)
        ; ;; dd.context-gather handles the sanity checks
        ; `(and ,@(dd.term-pattern-structure-tests (second x) (third x))))
        ;((equal (first x) '@match-formula)
        ; ;; dd.context-gather handles the sanity checks
        ; `(and ,@(dd.formula-pattern-structure-tests (second x) (third x))))
        ;((equal (first x) '@match-proof)
        ; ;; dd.context-gather handles the sanity checks
        ; `(and ,@(dd.formula-pattern-structure-tests `(logic.conclusion ,(second x)) (third x))))
        ((equal (first x) '@match)
         ;; dd.context-gather handles the sanity checks
         `(and
           ;; @match has structural tests AND binding tests built in
           ,@(dd.multi-patterns-structure-tests (cdr x))
           ,@(dd.path-bindings-to-equalities bindings)))
        ((memberp (first x) '(@extend @expand))
         ;; @extend is just replaced by its body
         (dd.context-replace (third x) bindings))
        ;((equal (first x) '@check-bindings)
        ; (if (not (tuplep 1 x))
        ;     (ACL2::er ACL2::hard 'dd.context-replace "Invalid @check-bindings encountered: ~x0 ~%" x)
        ;   `(and ,@(dd.path-bindings-to-equalities bindings))))
        ((equal (first x) '@term)
         (if (or (not (tuplep 2 x))
                 (not (dd.term-patternp (second x))))
             (ACL2::er ACL2::hard 'dd.context-replace "Invalid @term encountered: ~x0 ~%" x)
           (dd.term-from-path-bindings (second x) bindings)))
        ((equal (first x) '@formula)
         (if (or (not (tuplep 2 x))
                 (not (dd.formula-patternp (second x))))
             (ACL2::er ACL2::hard 'dd.context-replace "Invalid @formula encountered: ~x0 ~%" x)
           (dd.formula-from-path-bindings (second x) bindings)))
        ((equal (first x) '@terms)
         (if (not (dd.term-pattern-listp (cdr x)))
             (ACL2::er ACL2::hard 'dd.context-replace "Invalid @terms encountered: ~x0 ~%" x)
           `(list ,@(dd.term-from-path-bindings-list (cdr x) bindings))))
        ((equal (first x) '@formulas)
         (if (not (dd.formula-pattern-listp (cdr x)))
             (ACL2::er ACL2::hard 'dd.context-replace "Invalid @formulas encountered: ~x0 ~%" x)
           `(list ,@(dd.formula-from-path-bindings-list (cdr x) bindings))))
        ((equal (first x) '@sigma)
         (if (not (dd.sigma-patternp (cdr x)))
             (ACL2::er ACL2::hard 'dd.context-replace "Invalid @sigma encountered: ~x0 ~%" x)
           `(list ,@(dd.sigma-from-path-bindings (cdr x) bindings))))
        (t
         (cons (dd.context-replace (car x) bindings)
               (dd.context-replace (cdr x) bindings)))))

;; To allow @formula and @term and such to be used transparently inside of
;; @derive, we process @context in two passes.  Our first step is to replace
;; any @derive expressions with their expansion.  We then hit the result with
;; the context gathering and replacement.

(defun dd.deriv-letify-all (x)
  (declare (xargs :mode :program))
  (cond ((not (consp x))
         x)
        ((equal (car x) '@derive)
         (dd.deriv-letify (cdr x)))
        (t
         (cons (dd.deriv-letify-all (car x))
               (dd.deriv-letify-all (cdr x))))))

(defun dd.context-fn (x)
  (declare (xargs :mode :program))
  (let ((expand-deriv (dd.deriv-letify-all x)))
    (dd.context-replace expand-deriv (dd.context-gather expand-deriv))))

(defmacro @context (x)
  (dd.context-fn x))


;; It is difficult to directly put multiple contexts in a single function
;; because "cond" is a macro and will not accept something like
;;
;; (cond (@context ((@match ...) ...)) ...)
;;
;; We introduce our own @cond which gives a new context to each branch in the
;; cond.  This way, you can use matching to determine your tests, etc.
;;
;; Note: @cond cannot be meaningfully nested inside some external @context.

;; (defun dd.context-list-fn (x)
;;   (declare (xargs :mode :program))
;;   (if (consp x)
;;       (cons (dd.context-fn (car x))
;;             (dd.context-list-fn (cdr x)))
;;     nil))

;; (defmacro @cond (&rest args)
;;   `(cond ,@(dd.context-list-fn args)))





;; Axiom and theorem tracking.
;;
;; We can also automatically extract a list of axioms and theorems which are
;; used in a derivation.  Some of these are "local", meaning that they are
;; directly used via (build.axiom ...).  Others are "inherited", meaning they
;; are required by some other builder we've called upon.  We store lists of
;; axioms and theorems used by our builders, so that we can infer the axioms
;; and theorems we have inherited.

(ACL2::table milawa 'builder-axioms nil)

(ACL2::table milawa 'builder-theorems nil)

(defun dd.get-builder-axioms (wrld)
  (declare (xargs :mode :program))
  (cdr (lookup 'builder-axioms (ACL2::table-alist 'milawa wrld))))

(defun dd.get-builder-theorems (wrld)
  (declare (xargs :mode :program))
  (cdr (lookup 'builder-theorems (ACL2::table-alist 'milawa wrld))))

(defun dd.deriv-local-axioms (x)
  ;; Extract all the local axioms for a list of derivation lines
  (declare (xargs :mode :program))
  (if (consp x)
      (let ((justification (second (car x))))
        (cond ((equal (first justification) 'build.axiom)
               ;; E.g., (build.axiom (axiom-blah))
               (cons (second justification)
                     (dd.deriv-local-axioms (cdr x))))
              (t
               (dd.deriv-local-axioms (cdr x)))))
    nil))

(defun dd.deriv-inherited-axioms (x wrld)
  ;; Infer all the inherited axioms for a list of derivation lines
  (declare (xargs :mode :program))
  (if (consp x)
      (let* ((justification (second (car x))))
        (app (cdr (lookup (first justification) (dd.get-builder-axioms wrld)))
             (dd.deriv-inherited-axioms (cdr x) wrld)))
    nil))

(defun dd.deriv-local-theorems (x)
  ;; Extract all the local theorems for a list of derivation lines
  (declare (xargs :mode :program))
  (if (consp x)
      (let ((justification (second (car x))))
        (cond ((equal (first justification) 'build.theorem)
               ;; E.g., (build.theorem (theorem-blah))
               (cons (second justification)
                     (dd.deriv-local-theorems (cdr x))))
              (t
               (dd.deriv-local-theorems (cdr x)))))
    nil))

(defun dd.deriv-inherited-theorems (x wrld)
  ;; Infer all the inherited theorems for a list of derivation lines
  (declare (xargs :mode :program))
  (if (consp x)
      (let* ((justification (second (car x))))
        (app (cdr (lookup (first justification) (dd.get-builder-theorems wrld)))
             (dd.deriv-inherited-theorems (cdr x) wrld)))
    nil))

(defun dd.make-members (x set)
  ;; Create a list of [(memberp (axiom1) <set>), ...]
  (declare (xargs :mode :program))
  (if (consp x)
      (cons `(memberp ,(car x) ,set)
            (dd.make-members (cdr x) set))
    nil))

(defun dd.manual-inherited-axioms (x wrld)
  ;; x is a list of builder names; collect all the axioms they need.
  (declare (xargs :mode :program))
  (if (consp x)
      (app (cdr (lookup (car x) (dd.get-builder-axioms wrld)))
           (dd.manual-inherited-axioms (cdr x) wrld))
    nil))

(defun dd.manual-inherited-theorems (x wrld)
  ;; x is a list of builder names; collect all the theorems they need.
  (declare (xargs :mode :program))
  (if (consp x)
      (app (cdr (lookup (car x) (dd.get-builder-theorems wrld)))
           (dd.manual-inherited-theorems (cdr x) wrld))
    nil))



;; Since @context does not take state, we need to introduce some wrappers if we want
;; to provide direct support for axiom and theorem inference.  Towards this end, we
;; provide defun@, defund@, defthm@, and defthmd@, which implicitly wrap their defun
;; or defthm with @context, and also replace any occurrences of
;;
;;    (@obligations bldr1 bldr2 ... bldrN)
;;
;; With membership checks for the inherited axioms and theorems of these builders,
;; i.e.,
;;
;;    (and (memberp (axiom1) axioms)
;;         ...
;;         (memberp (axiomN) axioms)
;;         (memberp (thm1) thms)
;;         ...
;;         (memberp (thmN) thms))

(defun dd.replace-obligations (x wrld)
  (declare (xargs :mode :program))
  (cond ((not (consp x))
         x)
        ((equal (first x) '@obligations)
         `(and ,@(dd.make-members (dd.manual-inherited-axioms (cdr x) wrld) 'axioms)
               ,@(dd.make-members (dd.manual-inherited-theorems (cdr x) wrld) 'thms)))
        (t
         (cons (dd.replace-obligations (car x) wrld)
               (dd.replace-obligations (cdr x) wrld)))))

(defmacro defun@ (&rest args)
  `(ACL2::progn
    (ACL2::make-event `(@context (defun ,@(dd.replace-obligations ',args (ACL2::w ACL2::state)))))))

(defmacro defund@ (&rest args)
  `(ACL2::progn
    (ACL2::make-event `(@context (defund ,@(dd.replace-obligations ',args (ACL2::w ACL2::state)))))))

(defmacro definline@ (&rest args)
  `(ACL2::progn
    (ACL2::make-event `(@context (defun ,@(dd.replace-obligations ',args (ACL2::w ACL2::state)))))
    (ACL2::table milawa 'functions-to-inline
                 (cons ',(second args)
                       (ACL2::get-functions-to-inline ACL2::world)))))

(defmacro definlined@ (&rest args)
  `(ACL2::progn
    (ACL2::make-event `(@context (defund ,@(dd.replace-obligations ',args (ACL2::w ACL2::state)))))
    (ACL2::table milawa 'functions-to-inline
                 (cons ',(second args)
                       (ACL2::get-functions-to-inline ACL2::world)))))

(defmacro defthm@ (&rest args)
  `(ACL2::progn
    (ACL2::make-event `(@context (defthm ,@(dd.replace-obligations ',args (ACL2::w ACL2::state)))))))

(defmacro defthmd@ (&rest args)
  `(ACL2::progn
    (ACL2::make-event `(@context (defthmd ,@(dd.replace-obligations ',args (ACL2::w ACL2::state)))))))


(defmacro defsection@ (&rest args)
  ;; This is the same as defsection, but it also provides a context.
  `(ACL2::progn
    (ACL2::make-event `(@context (defsection ,@(dd.replace-obligations ',args (ACL2::w ACL2::state)))))))



(defmacro defobligations (name builders &key extra-axioms extra-thms)
  ;; Name should refer to a new builder which we are introducing.  Builders should be
  ;; the list of all the builders used by name.  We look up all the theorem and axiom
  ;; obligations for all these builders, and give them to name.
  ;;
  ;; You can also optionally provide some :extra-axioms and :extra-theorems that the
  ;; builder is going to require, if it manually uses build.axiom or build.theorem.
  (declare (xargs :guard (and (symbolp name)
                              (symbol-listp builders)
                              (true-listp extra-axioms)
                              (true-listp extra-thms))))
  `(ACL2::progn
    (ACL2::table milawa 'builder-axioms
                 (update ',name
                         (remove-duplicates (app ',extra-axioms
                                                 (dd.manual-inherited-axioms ',builders ACL2::world)))
                         (dd.get-builder-axioms ACL2::world)))
    (ACL2::table milawa 'builder-theorems
                 (update ',name
                         (remove-duplicates (app ',extra-thms
                                                 (dd.manual-inherited-theorems ',builders ACL2::world)))
                         (dd.get-builder-theorems ACL2::world)))
    (ACL2::value-triple (cons ',name
                              (list (cons 'AXMS (cdr (lookup ',name (dd.get-builder-axioms (ACL2::w ACL2::state)))))
                                    (cons 'THMS (cdr (lookup ',name (dd.get-builder-theorems (ACL2::w ACL2::state))))))))))
