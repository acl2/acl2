; Written by John Cowles
; Copyright/License: See the LICENSE file in this directory.

#| This is the .lisp file for the Commutative Ring book.

   John Cowles, University of Wyoming, Summer 1993

   Modified A. Flatau  2-Nov-1994
     Added a :verify-guards t hint to PRED for Acl2 1.8.

   Modified by Jared Davis, January 2004, to convert comments to XDOC.
|#

(in-package "ACL2-CRG")
(include-book "acl2-agp")

(defsection commutative-rings
  :parents (algebra)
  :short "Axiomatization of two associative and commutative operations, one
distributes over the other, while the other has an identity and an unary
inverse operation, developed by John Cowles."

  :long "<h3>Theory of Commutative Rings</h3>

<p>@('ACL2-CRG::plus') and @('ACL2-CRG::times') are associative and commutative
binary operations on the set (of equivalence classes formed by the equivalence
relation, @('ACL2-CRG::equiv'), on the set)</p>

@({
      RG = { x | (ACL2-CRG::pred x) != nil }
})

<p>with @('ACL2-CRG::times') distributing over @('ACL2-CRG::plus').</p>

<p>@('ACL2-CRG::zero') is a constant in the set RG which acts as an unit for
@('ACL2-CRG::plus').</p>

<p>@('ACL2-CRG::minus') is an unary operation on the set (of equivalence
classes formed by the equivalence relation, @('ACL2-CRG::equiv'), on the set)
RG which acts as an @('ACL2-CRG::plus-inverse') for @('ACL2-CRG::zero').</p>

<p>For example, let</p>
<ul>
<li> @('ACL2-CRG::pred')  = Booleanp, </li>
<li> @('ACL2-CRG::plus')  = exclusive-or, </li>
<li> @('ACL2-CRG::times') = and, </li>
<li> @('ACL2-CRG::zero')  = nil, and </li>
<li> @('ACL2-CRG::minus') = identity function. </li>
</ul>

<h3>Axioms of the theory of Commutative Rings</h3>

<p>Using @(see encapsulate), we introduce constrained functions:</p>

<ul>
<li>@(call equiv)</li>
<li>@(call pred)</li>
<li>@(call plus)</li>
<li>@(call times)</li>
<li>@(call zero)</li>
<li>@(call minus)</li>
</ul>

<p>with the following, constraining axioms:</p>

@(def Equiv-is-an-equivalence)
@(def Equiv-implies-iff-pred-1)
@(def Equiv-implies-equiv-plus-1)
@(def Equiv-implies-equiv-plus-2)
@(def Equiv-implies-equiv-times-1)
@(def Equiv-implies-equiv-times-2)
@(def Equiv-implies-equiv-minus-1)

@(def Closure-of-plus-for-pred)
@(def Closure-of-times-for-pred)
@(def Closure-of-zero-for-pred)
@(def Closure-of-minus-for-pred)

@(def Commutativity-of-plus)
@(def Commutativity-of-times)

@(def Associativity-of-plus)
@(def Associativity-of-times)

@(def Left-distributivity-of-times-over-plus)

@(def Left-unicity-of-zero-for-plus)
@(def Right-inverse-for-plus)


<h3>Theorems of the theory of Commutative Rings</h3>

<p>Given the above constraints, we prove the following generic theorems.</p>

<p>Besides the theorems below, note that @('<RG, ACL2-CRG::plus>') and @('<RG,
ACL2-CRG::times>') are both semigroups, and @('<RG, ACL2-CRG::plus,
ACL2-CRG::minus, ACL2-CRG::zero>') is an Abelian Group. Thus, additional
theorems of the theory of Commutative Rings may be obtained as instances of the
theorems of the theories of @(see acl2-asg::abelian-semigroups) and @(see
acl2-agp::abelian-groups).</p>"
  ;; It looks like this doc ends abruptly, but see below; we extend it.
  :autodoc nil

  (encapsulate
    ((equiv (x y) t)
     (pred (x) t)
     (plus (x y) t)
     (times (x y) t)
     (zero () t)
     (minus (x) t))

    (local (defun equiv (x y)
       (equal x y)))

    (local (defun pred (x)
             (declare (xargs :verify-guards t))
             (or (equal x t)
                 (equal x nil))))

    (local (defun plus (x y)
             (declare (xargs :guard (and (pred x)
                                         (pred y))))
             (and (or x y)
                  (not (and x y)))))

    (local (defun times (x y)
             (declare (xargs :guard (and (pred x)
                                         (pred y))))
             (and x y)))

    (local (defun zero () nil))

    (local (defun minus (x)
             (declare (xargs :guard (pred x)))
             x))

    (defequiv equiv
      :rule-classes (:equivalence
                     (:type-prescription
                      :corollary
                      (or (equal (equiv x y) t)
                          (equal (equiv x y) nil)))))

    (defcong equiv iff (pred x) 1)

    (defcong equiv equiv (plus x y) 1)

    (defcong equiv equiv (plus x y) 2)

    (defcong equiv equiv (times x y) 1)

    (defcong equiv equiv (times x y) 2)

    (defcong equiv equiv (minus x) 1)

    (defthm Closure-of-plus-for-pred
      (implies (and (pred x)
                    (pred y))
               (pred (plus x y))))

    (defthm Closure-of-times-for-pred
      (implies (and (pred x)
                    (pred y))
               (pred (times x y))))

    (defthm Closure-of-zero-for-pred
      (pred (zero)))

    (defthm Closure-of-minus-for-pred
      (implies (pred x)
               (pred (minus x))))

    (defthm Commutativity-of-plus
      (implies (and (pred x)
                    (pred y))
               (equiv (plus x y)
                      (plus y x))))

    (defthm Commutativity-of-times
      (implies (and (pred x)
                    (pred y))
               (equiv (times x y)
                      (times y x))))

    (defthm Associativity-of-plus
      (implies (and (pred x)
                    (pred y)
                    (pred z))
               (equiv (plus (plus x y) z)
                      (plus x (plus y z)))))

    (defthm Associativity-of-times
      (implies (and (pred x)
                    (pred y)
                    (pred z))
               (equiv (times (times x y) z)
                      (times x (times y z)))))

    (defthm Left-distributivity-of-times-over-plus
      (implies (and (pred x)
                    (pred y)
                    (pred z))
               (equiv (times  x (plus y z))
                      (plus (times x y)
                            (times x z)))))

    (defthm Left-unicity-of-zero-for-plus
      (implies (pred x)
               (equiv (plus (zero) x)
                      x)))

    (defthm Right-inverse-for-plus
      (implies (pred x)
               (equiv (plus x (minus x))
                      (zero))))))

(defsection commutative-rings-thms
  :extension commutative-rings

  (defthm Right-distributivity-of-times-over-plus
    (implies (and (pred x)
                  (pred y)
                  (pred z))
             (equiv (times (plus x y) z)
                    (plus (times x z)
                          (times y z)))))

  (defthm Left-nullity-of-zero-for-times
    (implies (pred x)
             (equiv (times (zero) x)
                    (zero)))
    :hints (("Goal"
             :use ((:instance
                    (:functional-instance
                     acl2-agp::Uniqueness-of-id-as-op-idempotent
                     (acl2-agp::equiv equiv)
                     (acl2-agp::pred pred)
                     (acl2-agp::op plus)
                     (acl2-agp::id zero)
                     (acl2-agp::inv minus))
                    (x (times (zero) x)))
                   (:instance Left-distributivity-of-times-over-plus
                              (y (zero))
                              (z (zero)))))))

  (defthm Right-nullity-of-zero-for-times
    (implies (pred x)
             (equiv (times x (zero))
                    (zero))))

  (defthm Functional-commutativity-of-minus-times-right
    (implies (and (pred x)
                  (pred y))
             (equiv (times x (minus y))
                    (minus (times x y))))
    :hints (("Goal"
             :use ((:instance
                    (:functional-instance
                     acl2-agp::Uniqueness-of-op-inverses
                     (acl2-agp::equiv equiv)
                     (acl2-agp::pred pred)
                     (acl2-agp::op plus)
                     (acl2-agp::id zero)
                     (acl2-agp::inv minus))
                    (x (times x y))
                    (y (times x (minus y))))
                   (:instance
                    Left-distributivity-of-times-over-plus
                    (z (minus y)))))))

  (defthm Functional-commutativity-of-minus-times-left
    (implies (and (pred x)
                  (pred y))
             (equiv (times (minus x) y)
                    (minus (times x y))))))
