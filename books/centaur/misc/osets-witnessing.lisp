; Centaur Miscellaneous Books
; Copyright (C) 2008-2012 Centaur Technology
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

(in-package "SET")

;; This book uses the "witness-cp" book to set up a clause processor for set
;; reasoning based on the osets library.  We use a similar strategy to the one
;; used in equiv-sets.lisp for reasoning about ordinary member-equal on lists.

;; Basically, this book provides a hint that can aid in reasoning about set
;; equivalence, subset, intersection, or emptiness.  It reduces all of these
;; concepts to reasoning about IN, that is, set membership.  So if you define
;; new set constructors, you need only prove a theorem like
;;   (equal (in a (my-set-constructor x y z)) ...)
;; in order for this book to reason smoothly about it.

;; You may use this hint manually like this:
;; (defthm foo
;;    ...
;;   :hints ((set::osets-reasoning)))

;; or you may (locally) set up a default hint and a suitable theory for the
;; hint by doing:
;;  (set::use-osets-reasoning)

;; What does this strategy do?  We think of the set predicates subset,
;; intersectp, empty, and equal as involving quantifiers.  For example,
;; (subset x y) really means (forall a (implies (in a x) (in a y))).

;; We do two things with this quantifier-based interpretation of each
;; predicate, based on whether it occurs positively or negatively.  This
;; determination is based on two factors -- whether its implicit quantifier is
;; universal or existential, and whether it occurs as a negated or non-negated
;; literal in the goal clause.  Arbitrarily, let's call it a positive
;; occurrence if it is a universal quantifier that occurs negated in the
;; clause, that is, non-negated in a hypothesis.  E.g., we have a
;; (subset a b) hypothesis.  Conversely, it's a negative occurrence if a
;; universal quantifier occurs as a non-negated conclusion or negated
;; hypothesis, or if an existential quantifier occurs as a negated hypothesis
;; or non-negated conclusion.

;; First we look at negative occurrences -- think of a (not (subset x y))
;; hypothesis.  What this really says is there exists some object A for which
;; (not (implies (in a x) (in a y))).  So we replace this hypothesis with this
;; assumption, where a is a fresh variable.  We do the following such
;; replacements, where A is a fresh variable in each case --

;;    Hypothesis                 Replacement
;;  (not (subset x y))       (and (in a x) (not (in a y)))
;;  (intersectp x y)         (and (in a x) (in a y))
;;  (not (equal x y))        (implies (and (setp x) (setp y))
;;                                    (xor (in a x) (in a y)))
;;  (not (empty x))          (not (in a x)).

;; For a positive occurrence -- think of a (subset a b) hypothesis -- we may
;; instantiate the implicit quantified formula one or more times, depending
;; what we find in the term.  For (subset x y), we may insert one or more terms
;; (implies (in a x) (in a y)) for elements a.  How do we determine which A's
;; to instantiate these terms with?  We look for various patterns that indicate
;; that some term represents a possible set element of interest:

;;    Pattern                   Possible interesting element
;; (in a x)                     a
;; (insert a x)                 a
;; (delete a x)                 a
;; (head x)                     (head x)

;; Note that since we replace negative occurrences with their instantiations
;; before we collect these interesting terms, among these collected terms are
;; any fresh variables introduced by those replacements.

;; We collect all such possibly-interesting terms and instantiate each positive
;; occurrence with all of them.  That is, we replace the following hypotheses
;; with a conjunction of replacements, with A set using the various patterns
;; above:

;;   Hypothesis                  Replacement
;; (subset x y)               (implies (in a x) (in a y))
;; (not (intersectp x y))     (not (and (in a x) (in a y)))
;; (equal x y)                (iff (in a x) (in a y))
;; (empty x)                  (not (in a x))

;; After we do these replacements, we're done.  What does this get us?
;; Basically, we've reduced all our implicit quantifiers to a bunch of IN
;; queries.  Because we have nice reductive rules about applying IN to the
;; various set constructors (such as insert, delete, union, intersection,
;; and difference), much of this boils away to just a bunch of Boolean logic
;; about IN applied to various variables.

;; For example, take the following theorem
;; (thm (implies (and (subset x y)
;;                    (not (subset x (union z w))))
;;               (not (subset (intersect (union x (union z w)) y)
;;                            (intersect (union z w) y)))))

;; If submit this form after loading this book and doing
;; (set::use-osets-reasoning),  ACL2 does the following:

;; First, negative occurrences.
;; The only negative occurrence is (not (subset x (union z w))).  This is
;; therefore replaced by:

;; (and (in nsubw0 x) (not (in nsubw0 (union z w))))

;; (Here nsubw0 happens to be the fresh variable chosen for the instantiation.)

;; We then look for interesting terms.  The only ones we find are the ones
;; produced by our previous replacement, (in nsubw0 x) and (in nsubw0 (union z
;; w)) -- in both cases the possible interesting element is nsubw0.  So we
;; instantiate our two positive occurrences,
;; (subset x y)
;; and
;; (subset (intersect (union x (union z w)) y)
;;         (intersect (union z w) y))
;; with their application to nsubw0.  This results in the following goal:
;;
;; (implies (and (implies (in nsubw0 x) (in nsubw0 y))
;;               (and (in nsubw0 x) (not (in nsubw0 (union z w)))))
;;          (not (implies (in nsubw0 (intersect (union x (union z w)) y))
;;                        (in nsubw0 (intersect (union z w) y))))).
;;
;; Applying rewrite rules UNION-IN and INTERSECT-IN, this becomes:
;; (implies (and (implies (in nsubw0 x) (in nsubw0 y))
;;               (and (in nsubw0 x) (not (or (in nsubw0 z) (in nsubw0 w)))))
;;          (not (implies (and (or (in nsubw0 x) (in nsubw0 z) (in nsubw0 w))
;;                             (in nsubw0 y))
;;                        (and (or (in nsubw0 z) (in nsubw0 w))
;;                             (in nsubw0 y)))))
;; Notice that all we're left with is Boolean connectives and IN applied to
;; various variables.  At this point we might as well be proving:
;; (implies (and (implies x y)
;;               (and x (not (or z w))))
;;          (not (implies (and (or x z w) y)
;;                        (and (or z w) y))))
;; which is a simple enough tautology for ACL2's built-in Boolean reasoning to
;; prove.


(include-book "std/osets/top" :dir :system)
(include-book "witness-cp")
(include-book "tools/rulesets" :dir :system)

(local (in-theory (enable definitions)))

(defun nonsubset-witness (x y)
  (declare (xargs :guard (and (setp x) (setp y))))
  (if (empty x)
      nil
    (if (in (head x) y)
        (nonsubset-witness (tail x) y)
      (head x))))

(defthmd nonsubset-witness-correct
  (let ((a (nonsubset-witness x y)))
    (iff (subset x y)
         (implies (in a x) (in a y)))))

(defthmd nonsubset-witness-nonnil
  (implies (let ((a (nonsubset-witness x y)))
             (implies (in a x) (in a y)))
           (not (nonsubset-witness x y))))

(defun intersectp-witness (x y)
  (declare (xargs :guard (and (setp x) (setp y))))
  (if (empty x)
      nil
    (if (in (head x) y)
        (head x)
      (intersectp-witness (tail x) y))))

(defthmd intersectp-witness-correct
  (let ((a (intersectp-witness x y)))
    (iff (intersectp x y)
         (and (in a x) (in a y)))))

(defun osets-unequal-witness (x y)
  (declare (xargs :guard (and (setp x) (setp y))))
  (or (nonsubset-witness x y)
      (nonsubset-witness y x)))

(defthmd osets-unequal-witness-correct
  (let ((a (osets-unequal-witness x y)))
    (implies (and (setp x) (setp y))
             (iff (equal x y)
                  (iff (in a x)
                       (in a y)))))
  :otf-flg t
  :hints (("goal" :in-theory (e/d (nonsubset-witness-correct
                                   nonsubset-witness-nonnil)
                                  (double-containment
                                   in-tail-or-head
                                   in))
           :use (double-containment))))

(defun nonempty-witness (x)
  (declare (xargs :guard (setp x)))
  (if (empty x) nil (head x)))

(defthmd nonempty-witness-correct
  (iff (empty x)
       (not (in (nonempty-witness x) x))))


(acl2::defwitness subset-witnessing
  :predicate (not (subset x y))
  :expr (let ((a (nonsubset-witness x y)))
          (and (in a x)
               (not (in a y))))
  :hints ('(:in-theory (e/d (nonsubset-witness-correct)
                            (subset in nonsubset-witness))))
  :generalize (((nonsubset-witness x y) . nsubw)))


(acl2::defwitness intersectp-witnessing
  :predicate (intersectp x y)
  :expr (let ((a (intersectp-witness x y)))
          (and (in a x)
               (in a y)))
  :hints ('(:in-theory (e/d (intersectp-witness-correct)
                            (intersectp in intersectp-witness))))
  :generalize (((intersectp-witness x y) . intpw)))

(acl2::defwitness equal-witnessing
  :predicate (not (equal x y))
  :expr (let ((a (osets-unequal-witness x y)))
          (implies (and (setp x) (setp y))
                   (xor (in a x) (in a y))))
  :hints ('(:in-theory '(iff xor)
            :use osets-unequal-witness-correct))
  :generalize (((osets-unequal-witness x y) . uneqw)))

(acl2::defwitness empty-witnessing
  :predicate (not (empty x))
  :expr (in (nonempty-witness x) x)
  :hints ('(:in-theory '(nonempty-witness-correct)))
  :generalize (((nonempty-witness x) . nempw)))

(acl2::definstantiate subset-instancing
  :predicate (subset x y)
  :vars (a)
  :expr (implies (in a x)
                 (in a y))
  :hints ('(:in-theory '(subset-in))))

(acl2::definstantiate intersectp-instancing
  :predicate (not (intersectp x y))
  :vars (a)
  :expr (not (and (in a x)
                  (in a y)))
  :hints ('(:in-theory '(intersectp never-in-empty)
            :use intersect-in)))

(acl2::definstantiate equal-instancing
  :predicate (equal x y)
  :vars (a)
  :expr (iff (in a x)
             (in a y))
  :hints ('(:in-theory nil)))

(acl2::definstantiate empty-instancing
  :predicate (empty x)
  :vars (a)
  :expr (not (in a x))
  :hints ('(:in-theory '(never-in-empty))))

(acl2::defexample subset-in-example
  :pattern (in a x)
  :templates (a)
  :instance-rulename subset-instancing)

(acl2::defexample intersectp-in-example
  :pattern (in a x)
  :templates (a)
  :instance-rulename intersectp-instancing)

(acl2::defexample equal-in-example
  :pattern (in a x)
  :templates (a)
  :instance-rulename equal-instancing)

(acl2::defexample empty-in-example
  :pattern (in a x)
  :templates (a)
  :instance-rulename empty-instancing)

(acl2::defexample subset-insert-example
  :pattern (insert a x)
  :templates (a)
  :instance-rulename subset-instancing)

(acl2::defexample intersectp-insert-example
  :pattern (insert a x)
  :templates (a)
  :instance-rulename intersectp-instancing)

(acl2::defexample equal-insert-example
  :pattern (insert a x)
  :templates (a)
  :instance-rulename equal-instancing)

(acl2::defexample empty-insert-example
  :pattern (insert a x)
  :templates (a)
  :instance-rulename empty-instancing)

(acl2::defexample subset-delete-example
  :pattern (delete a x)
  :templates (a)
  :instance-rulename subset-instancing)

(acl2::defexample intersectp-delete-example
  :pattern (delete a x)
  :templates (a)
  :instance-rulename intersectp-instancing)

(acl2::defexample equal-delete-example
  :pattern (delete a x)
  :templates (a)
  :instance-rulename equal-instancing)

(acl2::defexample empty-delete-example
  :pattern (delete a x)
  :templates (a)
  :instance-rulename empty-instancing)

(acl2::defexample subset-head-example
  :pattern (head x)
  :templates ((head x))
  :instance-rulename subset-instancing)

(acl2::defexample intersectp-head-example
  :pattern (head x)
  :templates ((head x))
  :instance-rulename intersectp-instancing)

(acl2::defexample equal-head-example
  :pattern (head x)
  :templates ((head x))
  :instance-rulename equal-instancing)

(acl2::defexample empty-head-example
  :pattern (head x)
  :templates ((head x))
  :instance-rulename empty-instancing)


(acl2::def-witness-ruleset osets-reasoning-rules
  '(subset-witnessing
    intersectp-witnessing
    equal-witnessing
    empty-witnessing
    subset-instancing
    intersectp-instancing
    equal-instancing
    empty-instancing
    subset-in-example
    intersectp-in-example
    equal-in-example
    empty-in-example
    subset-insert-example
    intersectp-insert-example
    equal-insert-example
    empty-insert-example
    subset-delete-example
    intersectp-delete-example
    equal-delete-example
    empty-delete-example
    subset-head-example
    intersectp-head-example
    equal-head-example
    empty-head-example))

(defmacro osets-reasoning ()
  '(acl2::witness :ruleset osets-reasoning-rules))

(defthmd nonempty-when-in
  (implies (in a x)
           (not (empty x))))

(defthmd in-tail-to-in-x
  (equal (in a (tail x))
         (and (not (equal a (head x)))
              (in a x)))
  :hints (("goal" :expand ((in a x)))))

(theory-invariant (not (and (active-runep '(:rewrite in-tail-to-in-x))
                            (or (active-runep '(:definition in))
                                (active-runep '(:rewrite in-tail)))))
                  :key in-tail-rewrite-loop)

(defthmd in-of-cons
  (equal (in a (cons b y))
         (and (setp y)
              (or (empty y)
                  (<< b (head y)))
              (or (equal a b)
                  (in a y))))
  :hints(("Goal" :in-theory (enable setp head tail empty)
          :expand ((in a (cons b y)))
          :do-not-induct t)))

(acl2::def-ruleset! osets-fancy-rules
  '(pick-a-point-subset-strategy))

(acl2::def-ruleset! osets-specialized-rules
  '(insert-never-empty
    insert-head
    insert-head-tail
    repeated-insert
    insert-sfix-cancel
    head-when-empty
    insert-when-empty
    head-of-insert-a-nil
    tail-of-insert-a-nil
    sfix-when-empty
    subset-membership-tail
    in-tail-or-head
    insert-identity
    subset-transitive
    subset-insert-x
    subset-sfix-cancel-x
    subset-sfix-cancel-y
    subset-in
    subset-in-2
    empty-subset
    empty-subset-2
    subset-reflexive
    subset-insert
    subset-tail
    delete-delete
    delete-preserves-empty
    delete-sfix-cancel
    delete-nonmember-cancel
    repeated-delete
    delete-insert-cancel
    insert-delete-cancel
    subset-delete
    union-symmetric
    union-commutative
    union-insert-x
    union-insert-y
    union-delete-x
    union-delete-y
    union-sfix-cancel-x
    union-sfix-cancel-y
    union-empty-x
    union-empty-y
    union-empty
    union-subset-x
    union-subset-y
    union-self
    union-associative
    union-outer-cancel
    intersect-symmetric
    intersect-insert-x
    intersect-insert-y
    intersect-delete-x
    intersect-delete-y
    intersect-sfix-cancel-x
    intersect-sfix-cancel-y
    intersect-empty-x
    intersect-empty-y
    intersect-subset-x
    intersect-subset-y
    intersect-self
    intersect-associative
    union-over-intersect
    intersect-over-union
    intersect-commutative
    intersect-outer-cancel
    difference-sfix-x
    difference-sfix-y
    difference-empty-x
    difference-empty-y
    difference-subset-x
    subset-difference
    difference-over-union
    difference-over-intersect
    difference-insert-x
    difference-insert-y
    difference-delete-x
    difference-delete-y
    difference-preserves-subset
    insert-induction-case
    double-containment
    in-tail))

(acl2::def-ruleset! osets-defs
  '(setp in empty subset
         insert delete intersect union difference
         head tail))

(acl2::def-ruleset! osets-witnessing-rules
  '(difference-in
    union-in
    intersect-in
    in-insert
    delete-in
    union-set
    intersect-set
    difference-set
    insert-produces-set
    sfix-produces-set
    tail-produces-set
    delete-set
    in-set
    nonempty-when-in
    never-in-empty
    in-head
    in-of-cons
    in-tail-to-in-x
    in-sfix-cancel))


(defmacro use-osets-reasoning ()
  '(local (progn (set-default-hints '((osets-reasoning)))
                 (in-theory (acl2::e/d*
                             (osets-witnessing-rules)
                             (osets-fancy-rules
                              osets-defs
                              osets-specialized-rules))))))


;; (acl2::allow-real-oracle-eval)

;; some tests of the reasoning strategy:
(local
 (encapsulate nil
   (use-osets-reasoning)

   ;; some lemmas from VL books
   (defthmd lemma2
     (implies (and (subset newinsts modnames)
                   (not (subset newinsts (union curr prev))))
              (not (subset (intersect (union newinsts (union curr prev))
                                      modnames)
                           (intersect (union curr prev)
                                      modnames)))))
   (defthmd lemma1
     (implies (and (subset newinsts modnames)
                   (not (subset newinsts (union curr prev))))
              (subset (intersect (union curr prev) modnames)
                      (intersect (union newinsts (union curr prev))
                                 modnames))))

   (defthmd union-of-difference-of-self
     (equal (union a (difference b a))
            (union a b)))

   (defthmd union-of-union-of-difference-of-self
     (equal (union a (union b (difference c a)))
            (union a (union b c))))

   (defthmd union-of-intersect-and-union
     (equal (union (intersect a b)
                   (intersect a c))
            (intersect a (union b c))))

   ;; lemmas from sets.lisp
   (defthmd insert-never-empty-lemma
     (not (empty (insert a X))))

   (defthmd insert-head-lemma
     (implies (not (empty X))
              (equal (insert (head X) X)
                     X)))

   (defthmd insert-head-tail-lemma
     (implies (not (empty X))
              (equal (insert (head X) (tail X))
                     X)))

   (defthmd repeated-insert-lemma
     (equal (insert a (insert a X))
            (insert a X)))

   (defthmd insert-sfix-cancel-lemma
     (equal (insert a (sfix X))
            (insert a X)))

   ;; this one doesn't really fit with these -- it's more of an
   ;; implementation detail than a property of sets
   ;;(defthmd head-when-empty-lemma
   ;;  (implies (empty X)
   ;;           (equal (head X)
   ;;                  nil)))

   (defthmd insert-when-empty-lemma
     (implies (and (syntaxp (not (equal X ''nil)))
                   (empty X))
              (equal (insert a X)
                     (insert a nil))))

   ;; ;;here's a problem -- equal is used as something other than set-equiv
   ;;(defthmd head-of-insert-a-nil-lemma
   ;;  (equal (head (insert a nil))
   ;;         a))

   ;; ;;another problem -- (equal x nil) gets changed to (not x),
   ;; ;;so we don't catch it
   ;;(defthmd tail-of-insert-a-nil-lemma
   ;;  (equal (tail (insert a nil))
   ;;         nil))

   ;; ;;same thing here
   ;;(defthmd sfix-when-empty-lemma
   ;;  (implies (empty X)
   ;;           (equal (sfix X)
   ;;                  nil)))

         ;;;; same, after
   ;;(defthmd subset-membership-tail-lemma
   ;;  (implies (and (subset X Y)
   ;;                (in a (tail X)))
   ;;           (in a (tail Y))))

   (defthmd in-tail-or-head-lemma
     (implies (and (in a X)
                   (not (in a (tail X))))
              (equal (head X)
                     a)))

   (defthmd insert-identity-lemma
     (implies (in a X)
              (equal (insert a X)
                     X)))

   (defthmd in-insert-lemma
     (equal (in a (insert b X))
            (or (in a X)
                (equal a b))))

   (defthmd subset-transitive-lemma
     (and (implies (and (subset X Y)
                        (subset Y Z))
                   (subset X Z))
          (implies (and (subset Y Z)
                        (subset X Y))
                   (subset X Z))))


   (defthmd subset-insert-X-lemma
     (iff (subset (insert a X) Y)
          (and (subset X Y)
               (in a Y))))

   (defthmd subset-sfix-cancel-X-lemma
     (iff (subset (sfix X) Y)
          (subset X Y)))

   (defthmd subset-sfix-cancel-Y-lemma
     (iff (subset X (sfix Y))
          (subset X Y)))

   (defthmd subset-in-lemma
     (and (implies (and (subset X Y)
                        (in a X))
                   (in a Y))
          (implies (and (in a X)
                        (subset X Y))
                   (in a Y))))

   (defthmd subset-in-2-lemma
     (and (implies (and (subset X Y)
                        (not (in a Y)))
                   (not (in a X)))
          (implies (and (not (in a Y))
                        (subset X Y))
                   (not (in a X)))))

   (defthmd empty-subset-lemma
     (implies (empty X)
              (subset X Y)))

   (defthmd empty-subset-2-lemma
     (implies (empty Y)
              (iff (subset X Y)
                   (empty X))))

   (defthmd subset-reflexive-lemma
     (subset X X))

   (defthmd subset-insert-lemma
     (subset X (insert a X)))

   (defthmd subset-tail-lemma
     (subset (tail X) X)
     :rule-classes ((:rewrite)
                    (:forward-chaining :trigger-terms ((tail x)))))


   (defthmd delete-delete-lemma
     (equal (delete a (delete b X))
            (delete b (delete a X)))
     :rule-classes ((:rewrite :loop-stopper ((a b)))))

   (defthmd delete-preserves-empty-lemma
     (implies (empty X)
              (empty (delete a X))))

   (defthmd delete-in-lemma
     (equal (in a (delete b X))
            (and (in a X)
                 (not (equal a b)))))

   (defthmd delete-sfix-cancel-lemma
     (equal (delete a (sfix X))
            (delete a X)))

   (defthmd delete-nonmember-cancel-lemma
     (implies (not (in a X))
              (equal (delete a X) (sfix X))))

   (defthmd repeated-delete-lemma
     (equal (delete a (delete a X))
            (delete a X)))

   (defthmd delete-insert-cancel-lemma
     (equal (delete a (insert a X))
            (delete a X)))

   (defthmd insert-delete-cancel-lemma
     (equal (insert a (delete a X))
            (insert a X)))

   (defthmd subset-delete-lemma
     (subset (delete a X) X))

   (defthmd union-symmetric-lemma
     (equal (union X Y) (union Y X))
     :rule-classes ((:rewrite :loop-stopper ((X Y)))))

   (defthmd union-commutative-lemma
     (equal (union X (union Y Z))
            (union Y (union X Z)))
     :rule-classes ((:rewrite :loop-stopper ((X Y)))))

   (defthmd union-insert-X-lemma
     (equal (union (insert a X) Y)
            (insert a (union X Y))))

   (defthmd union-insert-Y-lemma
     (equal (union X (insert a Y))
            (insert a (union X Y))))

   (defthmd union-delete-X-lemma
     (equal (union (delete a X) Y)
            (if (in a Y)
                (union X Y)
              (delete a (union X Y)))))

   (defthmd union-delete-Y-lemma
     (equal (union X (delete a Y))
            (if (in a X)
                (union X Y)
              (delete a (union X Y)))))

   (defthmd union-sfix-cancel-X-lemma
     (equal (union (sfix X) Y) (union X Y)))

   (defthmd union-sfix-cancel-Y-lemma
     (equal (union X (sfix Y)) (union X Y)))

   (defthmd union-empty-X-lemma
     (implies (empty X)
              (equal (union X Y) (sfix Y))))

   (defthmd union-empty-Y-lemma
     (implies (empty Y)
              (equal (union X Y) (sfix X))))

   (defthmd union-empty-lemma
     (iff (empty (union X Y))
          (and (empty X) (empty Y))))

   (defthmd union-in-lemma
     (iff (in a (union X Y))
          (or (in a X) (in a Y))))

   (defthmd union-subset-X-lemma
     (subset X (union X Y)))

   (defthmd union-subset-Y-lemma
     (subset Y (union X Y)))

   (defthmd union-self-lemma
     (equal (union X X) (sfix X)))

   (defthmd union-associative-lemma
     (equal (union (union X Y) Z)
            (union X (union Y Z))))

   (defthmd union-outer-cancel-lemma
     (equal (union X (union X Z))
            (union X Z)))

   (defthmd intersect-symmetric-lemma
     (equal (intersect X Y) (intersect Y X))
     :rule-classes ((:rewrite :loop-stopper ((X Y)))))

   (defthmd intersect-insert-X-lemma
     (implies (not (in a Y))
              (equal (intersect (insert a X) Y)
                     (intersect X Y))))

   (defthmd intersect-insert-Y-lemma
     (implies (not (in a X))
              (equal (intersect X (insert a Y))
                     (intersect X Y))))

   (defthmd intersect-delete-X-lemma
     (equal (intersect (delete a X) Y)
            (delete a (intersect X Y))))

   (defthmd intersect-delete-Y-lemma
     (equal (intersect X (delete a Y))
            (delete a (intersect X Y))))

   (defthmd intersect-sfix-cancel-X-lemma
     (equal (intersect (sfix X) Y) (intersect X Y)))

   (defthmd intersect-sfix-cancel-Y-lemma
     (equal (intersect X (sfix Y)) (intersect X Y)))

   (defthmd intersect-empty-X-lemma
     (implies (empty X) (empty (intersect X Y))))

   (defthmd intersect-empty-Y-lemma
     (implies (empty Y) (empty (intersect X Y))))

   (defthmd intersect-in-lemma
     (equal (in a (intersect X Y))
            (and (in a Y) (in a X))))

   (defthmd intersect-subset-X-lemma
     (subset (intersect X Y) X))

   (defthmd intersect-subset-Y-lemma
     (subset (intersect X Y) Y))

   (defthmd intersect-self-lemma
     (equal (intersect X X) (sfix X)))

   (defthmd intersect-associative-lemma
     (equal (intersect (intersect X Y) Z)
            (intersect X (intersect Y Z))))

   (defthmd union-over-intersect-lemma
     (equal (union X (intersect Y Z))
            (intersect (union X Y) (union X Z))))

   (defthmd intersect-over-union-lemma
     (equal (intersect X (union Y Z))
            (union (intersect X Y) (intersect X Z))))

   (defthmd intersect-commutative-lemma
     (equal (intersect X (intersect Y Z))
            (intersect Y (intersect X Z)))
     :rule-classes ((:rewrite :loop-stopper ((X Y)))))

   (defthmd intersect-outer-cancel-lemma
     (equal (intersect X (intersect X Z))
            (intersect X Z)))

   (defthmd difference-sfix-X-lemma
     (equal (difference (sfix X) Y) (difference X Y)))

   (defthmd difference-sfix-Y-lemma
     (equal (difference X (sfix Y)) (difference X Y)))

   (defthmd difference-empty-X-lemma
     (implies (empty X)
              (equal (difference X Y) (sfix X))))

   (defthmd difference-empty-Y-lemma
     (implies (empty Y)
              (equal (difference X Y) (sfix X))))

   (defthmd difference-in-lemma
     (equal (in a (difference X Y))
            (and (in a X)
                 (not (in a Y)))))

   (defthmd difference-subset-X-lemma
     (subset (difference X Y) X))

   (defthmd subset-difference-lemma
     (iff (empty (difference X Y))
          (subset X Y)))

   (defthmd difference-over-union-lemma
     (equal (difference X (union Y Z))
            (intersect (difference X Y) (difference X Z))))

   (defthmd difference-over-intersect-lemma
     (equal (difference X (intersect Y Z))
            (union (difference X Y) (difference X Z))))

   (defthmd difference-insert-X-lemma
     (equal (difference (insert a X) Y)
            (if (in a Y)
                (difference X Y)
              (insert a (difference X Y)))))

   (defthmd difference-insert-Y-lemma
     (equal (difference X (insert a Y))
            (delete a (difference X Y))))

   (defthmd difference-delete-X-lemma
     (equal (difference (delete a X) Y)
            (delete a (difference X Y))))

   (defthmd difference-delete-Y-lemma
     (equal (difference X (delete a Y))
            (if (in a X)
                (insert a (difference X Y))
              (difference X Y))))

   (defthmd difference-preserves-subset-lemma
     (implies (subset X Y)
              (subset (difference X Z)
                      (difference Y Z))))

   (defthmd insert-induction-case-lemma
     (implies (and (not (<< a (head X)))
                   (not (equal a (head X)))
                   (not (empty X)))
              (equal (insert (head X) (insert a (tail X)))
                     (insert a X))))

   (defthmd double-containment-lemma
     (implies (and (setp X)
                   (setp Y))
              (iff (equal X Y)
                   (and (subset X Y)
                        (subset Y X)))))

   (defthmd in-tail-lemma
     (implies (in a (tail x))
              (in a x)))))

