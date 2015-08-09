(in-package "ACL2")

(include-book "bdd-mgr")

#|

    bdd-spec.lisp
    ~~~~~~~~~~~~~

In this book we will develop the theory of the function ite-spec,
a much simpler version of the function ite-bdd given in the bdd-mgr
book. This book consists of 5 main parts:

1. prove robdds are propositionally equivalent iff they are
structurally equivalent.

2. prove that ite-spec is semantically equivalent to
propositional if-then-else.

3. prove 4 reductions of ite-spec which are used in ite-bdd
to short-circuit the evaluation of 4 input cases.

4. prove that when ite-spec is given robdds, it returns an robdd.

5. prove several important congruences about structural-equivalence.

|#

;;;; this book only contains definitions used for proving theorems
;;;; about the "executable" functions in bdd-mr.lisp. Thus, we do not
;;;; expect to execute the functions in this book and as such, we will
;;;; not go through the overhead of verifying their guards.

(set-verify-guards-eagerness 0)

;;;;; most of the recursive functions defined in this book will recur
;;;;; by traversing the the tree structure of bdds. so, we will recall
;;;;; a couple of simple theorems here and actually hide the definition
;;;;; of acl2-count.

(local
(defthm consp-<-acl2-count-bdd-else
  (implies (consp x)
	   (< (acl2-count (b-else x))
	      (acl2-count x)))
  :rule-classes :linear))

(local
(defthm consp-<-acl2-count-bdd-then
  (implies (consp x)
	   (< (acl2-count (b-then x))
	      (acl2-count x)))
  :rule-classes :linear))

(local
(defthm acl2-count-consp->0
  (implies (consp x)
	   (< 0 (acl2-count x)))
  :rule-classes :linear))

(in-theory (disable acl2-count))

#|----------------------------------------------------------------------------|#

;;;;;;;;;;;;;;;;;;; BEGIN PART 1. ;;;;;;;;;;;;;;;;;;;;;;;;

;;;; we now define structural equivalence for bdds. This function
;;;; is essentially 'equal except that it ignores the (car) of each
;;;; node (this is where we store the unique identifiers in the
;;;; stobj implementation) and compares atoms using iff.

(defun bdd= (x y)
  (cond ((and (atom x) (atom y)) (iff x y))
        ((or (atom x) (atom y)) nil)
        (t (and (equal (b-test x) (b-test y))
                (bdd= (b-then x) (b-then y))
                (bdd= (b-else x) (b-else y))))))

(local
(defthm bdd=-is-reflexive (bdd= x x)))

(local
(defthm bdd=-is-symmetric
  (implies (bdd= x y) (bdd= y x))))

(local
(defthm bdd=-is-transitive
  (implies (and (bdd= x y) (bdd= y z))
           (bdd= x z))))

(defequiv bdd=)

;;;; we will use the following wrapper function for (if) in order to
;;;; use the function in theorems and rewrite rules without having
;;;; ACL2 reducing it propositionally.

(defun prop-if (x y z) (if x y z))

;;;; we prove a few useful theorems about prop-if (and in fact (if)).

(defcong iff iff (prop-if x y z) 1)

(defthm prop-if-reduction-t
  (equal (prop-if t x y) x))

(defthm prop-if-reduction-nil
  (equal (prop-if nil x y) y))

(defthm prop-if-reduction-equal
  (implies (equal x y)
           (equal (prop-if f x y) y)))

;;;; (prop-look v a) is essentially (cdr (assoc v a))

(defmacro bool (x) `(if ,x t nil))

(defun prop-look (v a)
  (if (atom a) nil
    (if (equal v (caar a))
        (bool (cdar a))
      (prop-look v (cdr a)))))

;;;; (bdd-ev x a) evaluates the bdd x under the propositional assignment a

(defun bdd-ev (x a)
  (if (atom x) (bool x)
    (prop-if (prop-look (b-test x) a)
             (bdd-ev (b-then x) a)
             (bdd-ev (b-else x) a))))

;;;; (1) the following simple congruence assures that two bdds x and y such that
;;;; (bdd= x y), satisfy the relation (forall (a) (equal (bdd-ev x a) (bdd-ev y a)))

(defcong bdd= equal (bdd-ev x a) 1)

;;;; we now show that converse holds in the case where x and y are robdds (reduced
;;;; ordered binary decision diagrams). Thus ACL2 will agree with [Bryant86]. Actually,
;;;; we need to extend the notion of bdd-ev (which we do later in this book) to allow
;;;; for tests which are non-variables. We essentially use if-normalizing to show that
;;;; any if expression can be reduced to one where all tests are variables identifiers.

(defun bdd-test> (x y)
  (or (atom y)
      (> (b-test x)
         (b-test y))))

(defun robdd (x)
  (or (atom x)
      (and (bdd-test> x (b-then x))      ;;;; ORDERED
           (bdd-test> x (b-else x))
           (not (bdd= (b-then x)         ;;;; REDUCED
                      (b-else x)))
           (pnatp (b-test x))
           (robdd (b-then x))
           (robdd (b-else x)))))

;;;; in order to show the converse to (1), we need to construct a witness which satisfies
;;;; (not (equal (bdd-ev x witness) (bdd-ev y witness))) when (not (bdd= x y)) and x and y
;;;; are robdds. the following function builds this witness as a function of x and y.

(defun robdd-witness (x y)
  (declare (xargs :measure
                  (+ (acl2-count x) (acl2-count y))))
  (cond
   ((and (atom x) (atom y)) ())
   ((and (consp y)
         (or (atom x)
             (> (b-test y) (b-test x))))
    (if (bdd= x (b-then y))
        (cons (cons (b-test y) nil)
              (robdd-witness x (b-else y)))
      (cons (cons (b-test y) t)
            (robdd-witness x (b-then y)))))
   ((or (atom y)
        (> (b-test x) (b-test y)))
    (if (bdd= (b-then x) y)
        (cons (cons (b-test x) nil)
              (robdd-witness (b-else x) y))
      (cons (cons (b-test x) t)
            (robdd-witness (b-then x) y))))
   (t
    (if (bdd= (b-then x) (b-then y))
        (cons (cons (b-test x) nil)
              (robdd-witness (b-else x) (b-else y)))
      (cons (cons (b-test x) t)
            (robdd-witness (b-then x) (b-then y)))))))

;;;; the following predicate (independent-of v x) is true when
;;;; the bdd x is not dependent on the variable v

(defun independent-of (v x)
  (or (atom x)
      (and (not (equal (b-test x) v))
           (independent-of v (b-then x))
           (independent-of v (b-else x)))))

;;;; we now relate independence to robdd structures...

(local
(defthm robdd-natp-test-forward-chain
  (implies (and (robdd x) (consp x))
           (natp (b-test x)))
  :rule-classes :forward-chaining))


(local
(defthm robdd-independence-setup
  (implies (and (robdd x)
                (or (atom x)
                    (> v (b-test x))))
           (independent-of v x))
  :hints (("Goal" :induct (independent-of v x)))))

;;;; ...and wrap this notion into a decomposition at a given robdd node x

(local
(defthm robdd-independence
  (implies (and (robdd x) (consp x))
           (and (independent-of (b-test x) (b-then x))
                (independent-of (b-test x) (b-else x))))))

;;;; we also need to show that bdd-ev can "skip" over independent variables

(local
(defthm bdd-ev-independence
  (implies (independent-of v x)
           (equal (bdd-ev x (cons (cons v d) a))
                  (bdd-ev x a)))))

;;;; the above independence properties allow us to simplify bdd-ev's to not
;;;; only deconstruct the bdd x, but also drop the variable bound to the
;;;; test position in x. NOTE, a more general theorem could be used here where
;;;; the binding to (b-test x) is forgotten from the assignment. The following
;;;; is sufficient for our purposes since our witness function will construct
;;;; the assignment in a specific manner..

(local
(defthm bdd-ev-of-robdd
  (implies (and (robdd x) (consp x)
                (equal (b-test x) v))
           (equal (bdd-ev x (cons (cons v d) a))
                  (if d (bdd-ev (b-then x) a)
                    (bdd-ev (b-else x) a))))))

;;;; the following forward chaining is not necessary in order for our saturation
;;;; theorem to succeed, but it is useful in helping ACL2 avoid unnecessary forcing
;;;; induced by the implication:
;;;;      (implies (and (force (acl2-numberp x))
;;;;                    (force (acl2-numberp y))
;;;;                    (>= x y) (>= y x))
;;;;               (equal x y))


;;;; we now prove our saturation theorem. ACL2 does a wonderful job on this theorem
;;;; breaking it up into 18 subgoals and discharging each of them in an orderly fashion :)

(defthm robdd-bdd=-saturates-bdd-ev-=
  (implies (and (robdd x) (robdd y)
                (not (bdd= x y)))
           (not (equal (bdd-ev x (robdd-witness x y))
                       (bdd-ev y (robdd-witness x y))))))

;;;; so, now we have that for robdds x and y, that (bdd= x y) is the same
;;;; relation as (forall (a) (equal (bdd-ev x a) (bdd-ev y a)))


;;;;;;;;;;;;;;;;;;;; END PART 1. ;;;;;;;;;;;;;;;;;;;;;;;;;

#|----------------------------------------------------------------------------|#

;;;;;;;;;;;;;;;;;;; BEGIN PART 2. ;;;;;;;;;;;;;;;;;;;;;;;;

;;;; WE now move to the definition of our specification of ite, namely the function ite-spec.
;;;; We will show that this function preserves bdd-ev and given robdds, it returns robdds.
;;;; We will later show that under the right invariant that our stobj implementation of bdd-ite
;;;; returns a bdd which is bdd= to the bdd returned by ite-spec.

;;;; top-var, else-node, then-node, b-node are defined in bdd-mgr.lisp

(in-theory (enable top-var then-node else-node b-node))

(defun ite-spec (f g h)
  (declare (xargs :measure (+ (acl2-count f)
			      (acl2-count g)
			      (acl2-count h))))
  (if (atom f) (if f g h)
    (let ((v (top-var f g h)))
      (let ((then (ite-spec (then-node f v)
                            (then-node g v)
                            (then-node h v)))
            (else (ite-spec (else-node f v)
                            (else-node g v)
                            (else-node h v))))
        (if (bdd= then else) then
          (b-node 'if v then else))))))

(local
(defthm top-var->=-f-test
  (>= (top-var f g h) (b-test f))
  :rule-classes :linear))

(local
(defthm top-var->=-g-test
  (implies (consp g)
           (>= (top-var f g h) (b-test g)))
  :rule-classes :linear))

(local
(defthm top-var->=-h-test
  (implies (consp h)
           (>= (top-var f g h) (b-test h)))
  :rule-classes :linear))

(local
(defthm ite-main-lemma-setup
  (implies (and (>= v (b-test f))
                (or (>= v (b-test g))
                    (atom g))
                (or (>= v (b-test h))
                    (atom h)))
           (equal (prop-if (prop-look v a)
                           (prop-if (bdd-ev (then-node f v) a)
                                    (bdd-ev (then-node g v) a)
                                    (bdd-ev (then-node h v) a))
                           (prop-if (bdd-ev (else-node f v) a)
                                    (bdd-ev (else-node g v) a)
                                    (bdd-ev (else-node h v) a)))
                  (prop-if (bdd-ev f a)
                           (bdd-ev g a)
                           (bdd-ev h a))))
  :rule-classes nil))

(local
(defthm ite-main-lemma
  (let ((v (top-var f g h)))
    (equal (prop-if (prop-look v a)
                    (prop-if (bdd-ev (then-node f v) a)
                             (bdd-ev (then-node g v) a)
                             (bdd-ev (then-node h v) a))
                    (prop-if (bdd-ev (else-node f v) a)
                             (bdd-ev (else-node g v) a)
                             (bdd-ev (else-node h v) a)))
           (prop-if (bdd-ev f a)
                    (bdd-ev g a)
                    (bdd-ev h a))))
  :hints (("Goal"
           :use (:instance ite-main-lemma-setup
                           (v (top-var f g h)))
           :in-theory (disable top-var prop-if
                               then-node else-node)))))

(local
(defthm prop-if-equal-with-ite-main
  (let ((v (top-var f g h)))
    (implies (equal (prop-if (bdd-ev (then-node f v) a)
                             (bdd-ev (then-node g v) a)
                             (bdd-ev (then-node h v) a))
                    (prop-if (bdd-ev (else-node f v) a)
                             (bdd-ev (else-node g v) a)
                             (bdd-ev (else-node h v) a)))
             (equal (prop-if (bdd-ev (else-node f v) a)
                             (bdd-ev (else-node g v) a)
                             (bdd-ev (else-node h v) a))
                    (prop-if (bdd-ev f a)
                             (bdd-ev g a)
                             (bdd-ev h a)))))
  :hints (("Goal"
           :in-theory (disable ite-main-lemma
                               then-node else-node
                               prop-if top-var)
           :use (:instance ite-main-lemma)))))

(defthm ite-spec-preserves-bdd-ev
  (equal (bdd-ev (ite-spec f g h) a)
         (prop-if (bdd-ev f a)
                  (bdd-ev g a)
                  (bdd-ev h a)))
  :hints (("Goal"
           :induct (ite-spec f g h)
           :in-theory (disable then-node else-node
                               prop-if top-var))))

;;;;;;;;;;;;;;;;;;;; END PART 2. ;;;;;;;;;;;;;;;;;;;;;;;;;

#|----------------------------------------------------------------------------|#

;;;;;;;;;;;;;;;;;;; BEGIN PART 3. ;;;;;;;;;;;;;;;;;;;;;;;;

;;;; we now prove a few reductions which we make use of in the implementation
;;;; function ite-bdd in order to simplify ite calculations.

(local
(defthm ite-spec-reduction-1-free
  (implies (and (equal g (bdd-1))
                (equal h (bdd-0))
                (robdd f))
           (bdd= (ite-spec f g h) f))
  :hints (("Goal" :induct (ite-spec f g h)))
  :rule-classes nil))

(defthm ite-spec-reduction-1
  (implies (robdd f)
           (bdd= (ite-spec f (bdd-1) (bdd-0)) f))
  :hints (("Goal" :use (:instance
                        ite-spec-reduction-1-free
                        (g (bdd-1)) (h (bdd-0))))))
(local
(defthm then-node-atom
  (implies (atom x) (equal (then-node x v) x))))

(local
(defthm else-node-atom
  (implies (atom x) (equal (else-node x v) x))))

(defcong bdd= bdd= (then-node x v) 1)

(defcong bdd= bdd= (else-node x v) 1)

(local
(defthm bdd=-forward-chain-b-test
  (implies (bdd= x y) (equal (b-test x) (b-test y)))
  :rule-classes :forward-chaining))

(defthm robdd-then-node
  (implies (robdd x) (robdd (then-node x u))))

(defthm robdd-else-node
  (implies (robdd x) (robdd (else-node x u))))

(local
(defthm bdd=-back-chain
  (implies (and (consp x) (consp y)
                (bdd= (b-then x) (b-then y))
                (bdd= (b-else x) (b-else y)))
           (equal (bdd= x y)
                  (equal (b-test x) (b-test y))))))

(local
(defthm bdd=top-var-equal-1
  (implies (and (robdd f) (robdd g) (bdd= f g))
           (equal (top-var f g h)
                  (top-var f t h)))))

(defthm ite-spec-reduction-2
  (implies (and (robdd f) (robdd g) (robdd h)
                (bdd= f g))
           (bdd= (ite-spec f g h)
                 (ite-spec f (bdd-1) h)))
  :hints (("Goal" :induct (ite-spec f g h)
           :in-theory (disable top-var then-node else-node bdd=))
          ("Subgoal *1/1" :in-theory (enable bdd=)))
  :rule-classes nil)

(local
(defthm bdd=top-var-equal-2
  (implies (and (robdd f) (robdd h) (bdd= f h))
           (equal (top-var f g h)
                  (top-var f g nil)))))

(defthm ite-spec-reduction-3
  (implies (and (robdd f) (robdd h)
                (bdd= f h))
           (bdd= (ite-spec f g h)
                 (ite-spec f g (bdd-0))))
  :hints (("Goal"
           :induct (ite-spec f g h)
           :in-theory (disable top-var then-node else-node bdd=))
          ("Subgoal *1/1"
           :in-theory (enable bdd=))))

(local
(defthm then-node-match
  (implies (consp g)
           (equal (then-node g (b-test g)) (b-then g)))))

(local
(defthm else-node-match
  (implies (consp g)
           (equal (else-node g (b-test g)) (b-else g)))))

(local
(defthm then-node-mismatch-non-atom
  (implies (and (consp g) (not (equal v (b-test g))))
           (equal (then-node g v) g))))

(local
(defthm else-node-mismatch-non-atom
  (implies (and (consp g) (not (equal v (b-test g))))
           (equal (else-node g v) g))))

(defthm ite-spec-reduction-4
  (implies (and (robdd g) (robdd h) (bdd= g h))
           (bdd= (ite-spec f g h) g))
  :hints (("Goal"
           :induct (ite-spec f g h)
           :in-theory (disable top-var then-node else-node bdd=))
          ("Subgoal *1/4"
           :cases ((atom g)
                   (and (consp g)
                        (equal (top-var f g h) (b-test g)))))
          ("Subgoal *1/3"
           :cases ((atom g)
                   (and (consp g)
                        (equal (top-var f g h) (b-test g)))))))

;;;;;;;;;;;;;;;;;;;; END PART 3. ;;;;;;;;;;;;;;;;;;;;;;;;;

#|----------------------------------------------------------------------------|#

;;;;;;;;;;;;;;;;;;; BEGIN PART 4. ;;;;;;;;;;;;;;;;;;;;;;;;

;;;; we now want to (finally) show that if ite-spec is given robdds then it will return
;;;; robdds. this is important since we want to ensure that the relation bdd=
;;;; is always equivalent to propositional equivalence.

(local
(defthm top-var-is-pnatp
  (implies (and (robdd f) (robdd g) (robdd h)
                (consp f))
           (pnatp (top-var f g h)))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((top-var f g h)))
                 :rewrite)))

(local
(defthm top-var-is-bounded
  (implies (and (> v (b-test f))
                (> v (b-test g))
                (> v (b-test h)))
           (> v (top-var f g h)))
  :rule-classes :linear))

(local
(defthm robdd-bounded-then-node
  (implies (and (robdd f) (pnatp v)
                (>= v (b-test f)))
           (> v (b-test (then-node f v))))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((then-node f v)))
                 :linear)))

(local
(defthm robdd-bounded-else-node
  (implies (and (robdd f) (pnatp v)
                (>= v (b-test f)))
           (> v (b-test (else-node f v))))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((else-node f v)))
                 :linear)))

(local
(defthm robdd-constrained-then-node
  (implies (robdd f)
           (>= (b-test f)
               (b-test (then-node f v))))
  :rule-classes :linear))

(local
(defthm robdd-constrained-else-node
  (implies (robdd f)
           (>= (b-test f)
               (b-test (else-node f v))))
  :rule-classes :linear))

(local
(defthm ite-spec-is-bounded-then
  (implies (and (> v (b-test f))
                (> v (b-test g))
                (> v (b-test h))
                (pnatp v)
                (robdd f) (robdd g) (robdd h))
           (> v (b-test (ite-spec f g h))))
  :hints (("Goal"
           :induct (ite-spec f g h)
           :in-theory (disable then-node else-node top-var)))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((ite-spec f g h)))
                 :linear)))

(local
(defthm top-var-bounds-b-test-f
  (implies (and (consp f) (robdd f))
           (and (>= (top-var f g h)
                    (b-test f))
                (>= (top-var f g h)
                    (b-test g))
                (>= (top-var f g h)
                    (b-test h))))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((top-var f g h)))
                 :linear)))

(local
(defthm ite-spec-then-node
  (let ((v (top-var f g h)))
    (implies (and (consp f) (robdd f)
                  (robdd g) (robdd h))
             (> v (b-test (ite-spec (then-node f v)
                                    (then-node g v)
                                    (then-node h v))))))))

(local
(defthm ite-spec-else-node
  (let ((v (top-var f g h)))
    (implies (and (consp f) (robdd f)
                  (robdd g) (robdd h))
             (> v (b-test (ite-spec (else-node f v)
                                    (else-node g v)
                                    (else-node h v))))))))

(defthm ite-spec-returns-robdds
  (implies (and (robdd f) (robdd g) (robdd h))
           (robdd (ite-spec f g h)))
  :hints (("Goal" :in-theory (disable top-var then-node else-node))))


;;;;;;;;;;;;;;;;;;;; END PART 4. ;;;;;;;;;;;;;;;;;;;;;;;;;

#|----------------------------------------------------------------------------|#

;;;;;;;;;;;;;;;;;;; BEGIN PART 5. ;;;;;;;;;;;;;;;;;;;;;;;;

;;;; we finish this book with some congruence relations which let us
;;;; replace bdd= items in answering the question if something
;;;; is an robdd, in the context of ite-spec, etc..

; The following are commented out because of the mod to ACL2 v2-8 that does
; better matching for calls of equivalence relations against the current
; context, since they were causing rewriting loops during the proof of
; bdd=-robdd-cong-implies.  An alternate fix would be to add (syntaxp (not
; (term-order y x)) hypotheses, in order to mimic the behavior before this ACL2
; mod.

#|

(local
(defthm bdd=-bdd-test>-rewrite
  (implies (bdd= x y)
           (equal (bdd-test> z x)
                  (bdd-test> z y)))))

(local
(defthm bdd=-atom-implies
  (implies (and (bdd= x y) (atom x))
           (atom y))))

(local
(defthm bdd=-implies-equal-b-test
  (implies (bdd= x y)
           (equal (b-test x) (b-test y)))))

(local
(defthm bdd=-implies-bdd=-b-then
  (implies (bdd= x y)
           (bdd= (b-then x) (b-then y)))))

(local
(defthm bdd=-implies-bdd=-b-else
  (implies (bdd= x y)
           (bdd= (b-else x) (b-else y)))))

|#

(local
(defthm bdd=-robdd-cong-implies
  (implies (and (bdd= x y) (robdd x))
           (robdd y))
  :hints (("Goal" :induct (bdd= x y)))
  :rule-classes nil))

(defcong bdd= equal (robdd x) 1
  :hints (("Goal"
           :in-theory (disable robdd bdd=)
           :use ((:instance bdd=-robdd-cong-implies
                            (x x) (y x-equiv))
                 (:instance bdd=-robdd-cong-implies
                            (x x-equiv) (y x))))))

(defcong bdd= equal (top-var f g h) 1)

(defcong bdd= equal (top-var f g h) 2)

(defcong bdd= equal (top-var f g h) 3)

(local (defcong bdd= equal (consp x) 1))

(defun ite-f-induct (f fe g h)
  (declare (xargs :measure (+ (acl2-count f)
			      (acl2-count g)
			      (acl2-count h))))
  (if (atom f) fe
    (let ((v (top-var f g h)))
      (+ (ite-f-induct (then-node f v)
                       (then-node fe v)
                       (then-node g v)
                       (then-node h v))
         (ite-f-induct (else-node f v)
                       (else-node fe v)
                       (else-node g v)
                       (else-node h v))))))

(defun ite-g-induct (f g ge h)
  (declare (xargs :measure (+ (acl2-count f)
			      (acl2-count g)
			      (acl2-count h))))
  (if (atom f) ge
    (let ((v (top-var f g h)))
      (+ (ite-g-induct (then-node f v)
                       (then-node g v)
                       (then-node ge v)
                       (then-node h v))
         (ite-g-induct (else-node f v)
                       (else-node g v)
                       (else-node ge v)
                       (else-node h v))))))

(defun ite-h-induct (f g h he)
  (declare (xargs :measure (+ (acl2-count f)
			      (acl2-count g)
			      (acl2-count h))))
  (if (atom f) he
    (let ((v (top-var f g h)))
      (+ (ite-h-induct (then-node f v)
                       (then-node g v)
                       (then-node h v)
                       (then-node he v))
         (ite-h-induct (else-node f v)
                       (else-node g v)
                       (else-node h v)
                       (else-node he v))))))

(in-theory (disable top-var then-node else-node
                    bdd= b-node))

(local (in-theory (disable bdd=-is-symmetric
                           bdd=-is-transitive
                           bdd=-is-reflexive)))

(defcong bdd= bdd= (ite-spec f g h) 1
  :hints (("Goal" :induct (ite-f-induct f f-equiv g h)
           :in-theory (enable b-node))
          ("Subgoal *1/1" :in-theory (enable bdd=))))

(defcong bdd= bdd= (ite-spec f g h) 2
  :hints (("Goal" :induct (ite-g-induct f g g-equiv h)
           :in-theory (enable b-node))
          ("Subgoal *1/1" :in-theory (enable bdd=))))

(defcong bdd= bdd= (ite-spec f g h) 3
  :hints (("Goal" :induct (ite-h-induct f g h h-equiv)
           :in-theory (enable b-node))
          ("Subgoal *1/1" :in-theory (enable bdd=))))

(in-theory (disable ite-spec robdd bdd-ev prop-if))

(in-theory (enable acl2-count))

;;;;;;;;;;;;;;;;;;;; END PART 5. ;;;;;;;;;;;;;;;;;;;;;;;;;

#|----------------------------------------------------------------------------|#

