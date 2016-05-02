; Written by John Cowles
; Copyright/License: See the LICENSE file in this directory.

#| This is the .lisp file for the Abelian Group book.

   John Cowles, University of Wyoming, Summer 1993
     Last modified 29 July 1994.

   Modified A. Flatau  2-Nov-1994
     Added a :verify-guards t hint to PRED for Acl2 1.8.

   Modified by Jared Davis, January 2014, to convert comments to XDOC
|#

(in-package "ACL2-AGP")
(include-book "acl2-asg")

(defsection abelian-groups
  :parents (algebra)
  :short "Axiomatization of an associative and commutative binary operation
with an identity and an unary inverse operation, developed by John Cowles."

  :long "<h3>Theory of Abelian Groups</h3>

<p>@('ACL2-AGP::op') is an associative and commutative binary operation on the
set (of equivalence classes formed by the equivalence relation,
@('ACL2-AGP::equiv'), on the set)</p>

@({
     GP = { x | (ACL2-AGP::pred x) != nil }
})

<p>@('ACL2-AGP::id') is a constant in the set GP which acts as an unit for
@('ACL2-AGP::op') in GP.</p>

<p>@('ACL2-AGP::inv') is an unary operation on the set (of equivalence classes
formed by the equivalence relation, @('ACL2-AGP::equiv'), on the set) GP which
acts as an @('ACL2-AGP::op-inverse') for @('ACL2-AGP:: id').</p>

<p>For example, let</p>

<ul>
<li>@('ACL2-AGP::pred') = Booleanp, </li>
<li>@('ACL2-AGP::op')   = exclusive-or, </li>
<li>@('ACL2-AGP::id')   = nil, and </li>
<li>@('ACL2-AGP::inv')  = identity function. </li>
</ul>

<h3>Axioms of the theory of Abelian Groups</h3>

<p>Using @(see encapsulate), we introduce constrained functions:</p>

<ul>
<li>@(call equiv)</li>
<li>@(call pred)</li>
<li>@(call op)</li>
<li>@(call id)</li>
<li>@(call inv)</li>
</ul>

<p>with the following, constraining axioms:</p>

@(def Equiv-is-an-equivalence)
@(def Equiv-implies-iff-pred-1)
@(def Equiv-implies-equiv-op-1)
@(def Equiv-implies-equiv-op-2)
@(def Equiv-implies-equiv-inv-1)
@(def Closure-of-op-for-pred)
@(def Closure-of-id-for-pred)
@(def Closure-of-inv-for-pred)
@(def Commutativity-of-op)
@(def Associativity-of-op)
@(def Left-unicity-of-id-for-op)
@(def Right-inverse-of-inv-for-op)

<h3>Theorems of the theory of Abelian Groups</h3>"
  ;; It looks like this doc ends abruptly, but see below; we extend it.
  :autodoc nil

  (encapsulate
    ((equiv (x y) t)
     (pred (x) t)
     (op (x y) t)
     (id () t)
     (inv (x) t))

    (local (defun equiv (x y)
             (equal x y)))

    (local (defun pred (x)
             (declare (xargs :verify-guards t))
             (or (equal x t)
                 (equal x nil))))

    (local (defun op (x y)
             (declare (xargs :guard (and (pred x)
                                         (pred y))))
             (and (or x y)
                  (not (and x y)))))

    (local (defun id ()
             nil))

    (local (defun inv (x)
             (declare (xargs :guard (pred x)))
             x))

    (defequiv equiv
      :rule-classes (:equivalence
                     (:type-prescription
                      :corollary
                      (or (equal (equiv x y) t)
                          (equal (equiv x y) nil)))))

    (defcong equiv iff (pred x) 1)

    (defcong equiv equiv (op x y) 1)

    (defcong equiv equiv (op x y) 2)

    (defcong equiv equiv (inv x) 1)

    (defthm Closure-of-op-for-pred
      (implies (and (pred x)
                    (pred y))
               (pred (op x y))))

    (defthm Closure-of-id-for-pred
      (pred (id)))

    (defthm Closure-of-inv-for-pred
      (implies (pred x)
               (pred (inv x))))

    (defthm Commutativity-of-op
      (implies (and (pred x)
                    (pred y))
               (equiv (op x y)
                      (op y x))))

    (defthm Associativity-of-op
      (implies (and (pred x)
                    (pred y)
                    (pred z))
               (equiv (op (op x y) z)
                      (op x (op y z)))))

    (defthm Left-unicity-of-id-for-op
      (implies (pred x)
               (equiv (op (id) x)
                      x)))

    (defthm Right-inverse-of-inv-for-op
      (implies (pred x)
               (equiv (op x (inv x))
                      (id))))))


(defsection abelian-groups-thms
  :extension abelian-groups

  (acl2-asg::add-commutativity-2 equiv
                                 pred
                                 op
                                 commutativity-of-op
                                 commutativity-2-of-op)

  (defthm Right-unicity-of-id-for-op
    (implies (pred x)
             (equiv (op x (id))
                    x)))

  (defthm Left-inverse-of-inv-for-op
    (implies (pred x)
             (equiv (op (inv x) x)
                    (id))))

  (local (defthm Right-cancellation-for-op-iff
           (implies (and (pred x)
                         (pred y)
                         (pred z))
                    (iff (equiv (op x z) (op y z))
                         (equiv x y)))
           :rule-classes nil
           :hints (("Subgoal 1"
                    :in-theory (disable Equiv-implies-equiv-op-1)
                    :use (:instance Equiv-implies-equiv-op-1
                                    (x (op x z))
                                    (x-equiv (op y z))
                                    (y  (inv z)))))))

  (defthm Right-cancellation-for-op
    (implies (and (pred x)
                  (pred y)
                  (pred z))
             (equal (equiv (op x z) (op y z))
                    (equiv x y)))
    :rule-classes nil
    :hints (("Goal" :use Right-cancellation-for-op-iff)))

  (local (defthm Left-cancellation-for-op-iff
           (implies (and (pred x)
                         (pred y)
                         (pred z))
                    (iff (equiv (op x y) (op x z))
                         (equiv z y)))
           :rule-classes nil
           :hints (("Goal" :use ((:instance Right-cancellation-for-op
                                            (x z)
                                            (z x)))))))

  (defthm Left-cancellation-for-op
    (implies (and (pred x)
                  (pred y)
                  (pred z))
             (equal (equiv (op x y) (op x z))
                    (equiv y z)))
    :hints (("Goal" :use Left-cancellation-for-op-iff)))

  (defthm Uniqueness-of-id-as-op-idempotent
    (implies (and (pred x)
                  (equiv (op x x) x))
             (equiv x (id)))
    :rule-classes nil
    :hints (("Goal"
             :use (:instance Right-cancellation-for-op
                             (y (id))
                             (z x)))))

  (defthm Uniqueness-of-op-inverses
    (implies (and (pred x)
                  (pred y)
                  (equiv (op x y) (id)))
             (equiv y (inv x)))
    :rule-classes nil
    :hints (("Goal"
             :use (:instance Right-cancellation-for-op
                             (x y)
                             (y (inv x))
                             (z x)))))

  (defthm Involution-of-inv
    (implies (pred x)
             (equiv (inv (inv x))
                    x))
    :hints (("Goal" :use (:instance Uniqueness-of-op-inverses
                                    (x (inv x))
                                    (y x)))))

  (defthm Uniqueness-of-op-inverses-1
    (implies (and (pred x)
                  (pred y)
                  (equiv (op x (inv y)) (id)))
             (equiv x y))
    :rule-classes nil
  :hints (("Goal" :use (:instance Uniqueness-of-op-inverses
                                  (y x)
                                  (x (inv y))))))

  (defthm Distributivity-of-inv-over-op
    (implies (and (pred x)
                  (pred y))
             (equiv (inv (op x y))
                    (op (inv x)
                        (inv y))))
    :hints (("Goal" :use (:instance Uniqueness-of-op-inverses
                                    (x (op x y))
                                    (y (op (inv x)(inv y)))))))

  (defthm id-is-its-own-invese
    (equiv (inv (id))
           (id))
    :hints (("Goal" :use (:instance Uniqueness-of-op-inverses
                                    (x (id))
                                    (y (id))))))

  (local (defthm obvious-inv-cancellation
           (implies (and (pred x)
                         (pred y))
                    (equiv (op (op x (inv x)) y) y))
           :rule-classes nil))

  (defthm inv-cancellation-on-right
    (implies (and (pred x)
                  (pred y))
             (equiv (op x (op y (inv x)))
                    y))
    :hints (("Goal"
             :use obvious-inv-cancellation
             :in-theory (disable right-inverse-of-inv-for-op))))

  (defthm inv-cancellation-on-left
    (implies (and (pred x)
                  (pred y))
             (equiv (op x (op (inv x) y))
                    y))))
