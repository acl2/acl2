; OMP Library
; (Orthogonal Matching Pursuit)
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; cert_param: (uses-acl2r)

(in-package "OMP")

(include-book "workshops/2018/kwan-greenstreet/vectors" :dir :system)
(include-book "workshops/2018/kwan-greenstreet/norm"    :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dictionary
  :parents (omp)
  :short "Dictionaries of unit-norm atoms in a real Hilbert space."
  :long
  (xdoc::topstring
   (xdoc::p
    "This library is only available in "
    (xdoc::seetopic "acl2::real" "ACL2(r)") ".")
   (xdoc::p
    "This book contains a formalization of dictionaries, including
     notions of completeness, redundancy, and frames.")
   (xdoc::p
    "A dictionary is a finite indexed family of unit-norm vectors in
     @($\\mathcal{H} = \\mathbb{R}^d$).  We represent an atom as a
     @(see real-listp) of length @($d$) (matching the conventions of
     @('books/workshops/2018/kwan-greenstreet/')) and a dictionary as
     the list of its atoms in some fixed enumeration -- the column
     view of the matrix @($\\Phi \\in \\mathbb{R}^{d \\times N}$),
     where @($N = |I|$) is the index set's cardinality.")
   (xdoc::p
    "The definitions here track Section II (\"Background\") of:")
   (xdoc::p
    "J. A. Tropp, \"Greed is Good: Algorithmic Results for Sparse
     Approximation,\" IEEE Trans. Info. Theory 50(10), 2004.")
   (xdoc::p
    "The vector and norm infrastructure is inherited from
     @('books/workshops/2018/kwan-greenstreet/'):")
   (xdoc::ul
    (xdoc::li
     "@('vectors.lisp'): @('vec-+'), @('scalar-*'), @('vec--'),
      @('dot'), @('zvecp').")
    (xdoc::li
     "@('norm.lisp'): @('norm^2') (note that @('(norm^2 v) = 1') is
      equivalent to @($\\|v\\| = 1$))."))
   (xdoc::p
    "A dictionary is intentionally <b>not</b> required to be a basis,
     linearly independent, or orthonormal.  The matrix view stacking
     atoms as columns gives @($\\Phi \\in \\mathbb{R}^{d \\times N}$)
     where @($N = $) @(tsee n-atoms) and each column has unit
     @($\\ell_2$) norm.  When @($d \\le N$) (the overcomplete /
     redundant case) the dictionary can still be complete; this is
     the regime @('OMP') targets."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Vectors in H = R^d, and unit-norm atoms.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define vectorp ((v t) (dim natp))
  :returns (ok booleanp)
  :short "Recognize a vector of @($\\mathbb{R}^{\\mathit{dim}}$)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two conjuncts are exposed as rewrites in the @('///')
     section so callers (e.g. @(tsee unit-atom-p)) can discharge
     guards like @('(real-listp v)') from @('(vectorp v dim)')
     without enabling @('vectorp') by hand."))
  (and (real-listp v)
       (equal (len v) (nfix dim)))
  ///
  (defthm real-listp-when-vectorp
    (implies (vectorp v dim)
             (real-listp v))
    :rule-classes (:rewrite :forward-chaining))
  (defthm len-when-vectorp
    (implies (vectorp v dim)
             (equal (len v) (nfix dim)))))

(define unit-atom-p ((v t) (dim natp))
  :returns (ok booleanp)
  :short "Recognize a unit-norm vector of @($\\mathbb{R}^{\\mathit{dim}}$)."
  :long
  (xdoc::topstring
   (xdoc::p
    "@($\\|v\\| = 1$) iff @($\\|v\\|^2 = 1$) since the norm is
     nonnegative.  Squaring lets us avoid @(see sqrt)."))
  (and (vectorp v dim)
       (equal (norm^2 v) 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Dictionaries: a finite indexed family of atoms, all of the same dimension.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dictionaryp ((d t) (dim natp))
  :returns (ok booleanp)
  :short "Recognize a dictionary of @($\\mathbb{R}^{\\mathit{dim}}$):
          a true-list of @(tsee unit-atom-p)s of that dimension."
  (cond ((atom d) (null d))
        (t (and (unit-atom-p (car d) dim)
                (dictionaryp (cdr d) dim))))
  ///
  (defthm dictionaryp-of-cons
    (equal (dictionaryp (cons a d) dim)
           (and (unit-atom-p a dim)
                (dictionaryp d dim))))
  (defthm dictionaryp-forward-to-true-listp
    (implies (dictionaryp d dim)
             (true-listp d))
    :rule-classes :forward-chaining))

(define n-atoms ((d t))
  :enabled t
  :returns (n natp :rule-classes :type-prescription)
  :short "Number of atoms: the cardinality @($|I|$) of the index set."
  :long
  (xdoc::topstring
   (xdoc::p
    "Kept enabled because it is just an alias for @(see len) on a
     dictionary; downstream arithmetic and guards see the underlying
     @(see len) form directly."))
  (len d))

(define atom-at ((i natp) (d t))
  :guard (true-listp d)
  :returns (a t)
  :short "The @($i$)-th atom of a dictionary,
          using the list's zero-based enumeration."
  (nth (nfix i) d)
  ///
  (defthm unit-atom-p-of-atom-at
    (implies (and (dictionaryp d dim)
                  (natp i)
                  (< i (n-atoms d)))
             (unit-atom-p (atom-at i d) dim))
    :hints (("Goal" :in-theory (enable dictionaryp n-atoms))))
  (defthm vectorp-of-atom-at
    (implies (and (dictionaryp d dim)
                  (natp i)
                  (< i (n-atoms d)))
             (vectorp (atom-at i d) dim))
    :hints (("Goal"
             :do-not-induct t
             :use unit-atom-p-of-atom-at
             :in-theory (enable unit-atom-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Linear combinations and the span of a dictionary.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zero-vec ((dim natp))
  :returns (v real-listp)
  :short "The zero vector of @($\\mathbb{R}^{\\mathit{dim}}$)."
  (if (zp dim) nil
    (cons 0 (zero-vec (- dim 1))))
  ///
  (defthm len-of-zero-vec
    (equal (len (zero-vec dim)) (nfix dim)))
  (defthm vectorp-of-zero-vec
    (vectorp (zero-vec dim) dim)
    :hints (("Goal" :in-theory (enable vectorp)))))

;; Support lemmas for the closure theorems on linear-combo below.

(defthm len-of-scalar-*
  (implies (and (real-listp vec) (realp a))
           (equal (len (scalar-* a vec)) (len vec)))
  :hints (("Goal" :use (:instance acl2::scalar-*-closure
                                  (acl2::a a)
                                  (acl2::vec vec)))))

(defthm real-listp-of-car-when-dictionaryp
  (implies (and (dictionaryp d dim)
                (consp d))
           (real-listp (car d)))
  :hints (("Goal" :in-theory (enable dictionaryp unit-atom-p vectorp))))

(defthm len-of-car-when-dictionaryp
  (implies (and (dictionaryp d dim)
                (consp d))
           (equal (len (car d)) (nfix dim)))
  :hints (("Goal" :in-theory (enable dictionaryp unit-atom-p vectorp))))

(define linear-combo ((coeffs real-listp) (d t) (dim natp))
  :guard (and (real-listp coeffs)
              (dictionaryp d dim)
              (equal (len coeffs) (n-atoms d)))
  :verify-guards nil
  :returns (v real-listp)
  :short "Element-wise linear combination
          @($\\sum_i c_i \\, D(i)$)
          of the atoms of @($d$) with coefficient vector @($c$);
          the result lives in @($\\mathbb{R}^{\\mathit{dim}}$)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Guard verification needs @('len-of-linear-combo') below to
     discharge @('vec-+')'s @('(= (len vec1) (len vec2))') guard, so
     we define this with @(':verify-guards nil') and run
     @(tsee verify-guards) inside @('///') after the length lemma is
     established."))
  (cond ((or (atom coeffs) (atom d))
         (zero-vec dim))
        (t (vec-+ (scalar-* (car coeffs) (car d))
                  (linear-combo (cdr coeffs) (cdr d) dim))))
  ///
  (defthm len-of-linear-combo
    (implies (and (real-listp coeffs)
                  (dictionaryp d dim)
                  (equal (len coeffs) (n-atoms d)))
             (equal (len (linear-combo coeffs d dim))
                    (nfix dim)))
    :hints (("Goal"
             :induct (linear-combo coeffs d dim)
             :in-theory (enable linear-combo dictionaryp unit-atom-p vectorp))
            ("Subgoal *1/2"
             :use ((:instance acl2::vec-+-closure-2
                              (acl2::vec1 (scalar-* (car coeffs) (car d)))
                              (acl2::vec2 (linear-combo (cdr coeffs) (cdr d) dim)))))))
  (verify-guards linear-combo
    :hints (("Goal" :in-theory (enable dictionaryp unit-atom-p))))
  (defthm vectorp-of-linear-combo
    (implies (and (real-listp coeffs)
                  (dictionaryp d dim)
                  (equal (len coeffs) (n-atoms d)))
             (vectorp (linear-combo coeffs d dim) dim))
    :hints (("Goal" :in-theory (enable vectorp)))))

(define-sk in-spanp (v d dim)
  :guard (and (natp dim)
              (dictionaryp d dim))
  :returns (ok booleanp)
  :short "@($v \\in \\mathrm{span}(D)$):
          there exist coefficients realizing @($v$) as a linear
          combination of @($d$)'s atoms."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first two conjuncts inside the @('exists') establish the
     coefficient-vector shape that @(tsee linear-combo) needs from
     @('coeffs'), and the outer guard supplies the dictionary
     precondition; @(see and) short-circuits give the rest."))
  (exists coeffs
    (and (real-listp coeffs)
         (equal (len coeffs) (n-atoms d))
         (equal (linear-combo coeffs d dim) v))))

(define-sk complete-dictionary-p (d dim)
  :guard (and (natp dim)
              (dictionaryp d dim))
  :returns (ok booleanp)
  :short "A dictionary is complete (spans @($\\mathcal{H}$)) when every
          vector of dimension @($\\mathit{dim}$) lies in its span."
  (forall v
    (implies (vectorp v dim)
             (in-spanp v d dim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Redundant dictionaries.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define redundant-dictionary-p ((d t) (dim natp))
  :returns (ok booleanp)
  :short "A dictionary with strictly more atoms than the ambient dimension."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the matrix view, @($\\Phi \\in \\mathbb{R}^{d \\times N}$)
     with @($N > d$) -- @($\\Phi$) is \"fat\".  When such a dictionary
     is also complete, the representation map
     @($c \\mapsto \\sum_i c_i \\, D(i)$) is surjective onto
     @($\\mathcal{H}$) but not injective: every signal has infinitely
     many representations, and the kernel of the map has dimension
     @($N - d$).  This is the regime where one chooses a representation
     by a minimality criterion -- typically sparsity, as in @('OMP')."))
  (and (dictionaryp d dim)
       (> (n-atoms d) (nfix dim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Frames.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm nonneg-of-real-squared
   (implies (realp x)
            (<= 0 (* x x)))
   :rule-classes ((:rewrite) (:linear))))

(define sum-sq-inner-products ((x real-listp) (d t))
  :guard (dictionaryp d (len x))
  :returns (s realp :rule-classes :type-prescription)
  :short "@($\\sum_i \\langle x, D(i) \\rangle^2$),
          the sum of squared inner products of @($x$) with each atom."
  :long
  (xdoc::topstring
   (xdoc::p
    "The guard pins @($d$) to a dictionary of @($x$)'s dimension so
     each @('(dot x (car d))') call sees real-listp args of equal
     length."))
  (cond ((atom d) 0)
        (t (+ (let ((ip (dot x (car d))))
                (* ip ip))
              (sum-sq-inner-products x (cdr d)))))
  ///
  (defthm nonneg-of-sum-sq-inner-products
    (implies (and (real-listp x)
                  (dictionaryp d (len x)))
             (<= 0 (sum-sq-inner-products x d)))
    :rule-classes ((:rewrite) (:linear))
    :hints (("Goal"
             :induct (sum-sq-inner-products x d)
             :in-theory (enable sum-sq-inner-products dictionaryp)))))

(define-sk frame-inequality-p (d dim a b)
  :guard (and (natp dim)
              (realp a)
              (realp b)
              (dictionaryp d dim))
  :returns (ok booleanp)
  :short "The frame inequality for fixed bounds @($A$) and @($B$):
          @($\\forall x \\in \\mathcal{H},\\;
             A \\, \\|x\\|^2 \\le
             \\sum_i \\langle x, D(i) \\rangle^2 \\le
             B \\, \\|x\\|^2$)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Over the reals, @($|\\langle x, D(i) \\rangle|^2 = \\langle x,
     D(i) \\rangle^2$).  This predicate alone does not constrain @($A$)
     and @($B$) to be positive or ordered -- @(tsee framep) layers the
     @($0 < A \\le B$) requirement on top.")
   (xdoc::p
    "The @('implies') form is auto-translated to @('if') in the
     function body by @(see define-sk) (see @(see
     std::define-sk-implies-handling)), giving us guard verification
     under @('(vectorp x dim)') while preserving @('implies') in the
     @('-necc') theorem for a usable rewrite rule."))
  (forall x
    (implies (vectorp x dim)
             (and (<= (* a (norm^2 x))
                      (sum-sq-inner-products x d))
                  (<= (sum-sq-inner-products x d)
                      (* b (norm^2 x)))))))

(define framep ((d t) (dim natp) (a realp) (b realp))
  :returns (ok booleanp)
  :short "A frame with explicit bounds @($A$) and @($B$): a dictionary
          satisfying the @(see frame-inequality-p) with
          @($0 < A \\le B < \\infty$)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The standard mathematical definition does not require strict
     redundancy -- e.g. an orthonormal basis is a (tight) frame with
     @($A = B = 1$).  Use @(tsee redundant-dictionary-p) alongside
     @('framep') when the strictly redundant case is wanted."))
  (and (dictionaryp d dim)
       (< 0 a)
       (<= a b)
       (frame-inequality-p d dim a b)))

(define-sk frame-for-h-p (d dim)
  :guard (natp dim)
  :returns (ok booleanp)
  :short "Existential form of @(tsee framep): @($d$) is a frame for
          @($\\mathcal{H} = \\mathbb{R}^{\\mathit{dim}}$) for some pair
          of bounds."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @(see and) short-circuits on the witness type-checks before
     reaching @(tsee framep), so guard verification can discharge
     @('framep')'s @('(realp a)') and @('(realp b)') in the
     then-branch.  Semantically this matches the existential without
     the type-checks: @('framep') already returns @('nil') when @($a$)
     or @($b$) isn't real, since @('<') coerces non-numbers to @($0$)
     and the @('(< 0 a)') / @('(<= a b)') tests fail."))
  (exists (a b)
    (and (realp a)
         (realp b)
         (framep d dim a b))))

(define tight-framep ((d t) (dim natp) (a realp))
  :guard (dictionaryp d dim)
  :returns (ok booleanp)
  :short "Tight frame: @($A = B$)."
  :long
  (xdoc::topstring
   (xdoc::p
    "When additionally @($A = 1$), this is a Parseval frame: every
     @($x$) satisfies @($\\|x\\|^2 = \\sum_i \\langle x, D(i)
     \\rangle^2$).  See @(tsee parseval-framep)."))
  (framep d dim a a))

(define parseval-framep ((d t) (dim natp))
  :guard (dictionaryp d dim)
  :returns (ok booleanp)
  :short "Parseval frame: tight frame with @($A = B = 1$)."
  (tight-framep d dim 1))
