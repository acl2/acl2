; Written by John Cowles
; Copyright/License: See the LICENSE file in this directory.

#| This is the .lisp file for the Abelian SemiGroup book.

   John Cowles, University of Wyoming, Summer 1993
     Last modified 29 July 1994.

   Modified A. Flatau  2-Nov-1994
     Added a :verify-guards t hint to PRED for Acl2 1.8.

   Modified by Jared Davis, January 2014, to convert comments to XDOC
|#

(in-package "ACL2-ASG")
(include-book "xdoc/top" :dir :system)

(defsection abelian-semigroups
  :parents (algebra)
  :short "Axiomatization of an associative and commutative binary operation, developed by John Cowles."
  :autodoc nil
  :long "<h3>Theory of Abelian SemiGroups</h3>

<p>@('ACL2-ASG::op') is an associative and commutative binary operation on the
set (of equivalence classes formed by the equivalence relation,
@('ACL2-ASG::equiv'), on the set)</p>

@({
     { x | (ACL2-ASG::pred x) != nil }
})

<p>Exclusive-or on the set of Boolean values with the equivalence relation,
EQUAL, is an example.</p>

<p>Note, it is recommended that a second version of commutativity, called
Commutativity-2, be added as a :@(see rewrite) rule for any operation which has
both Associative and Commutative :@(see rewrite) rules. The macro
@(see ACL2-ASG::Add-Commutativity-2) may be used to add such a rule.</p>

<h3>Axioms of Abelian Semigroups</h3>

<p>Using @(see encapsulate), we introduce constrained functions:</p>

<ul>
<li>@(call equiv)</li>
<li>@(call pred)</li>
<li>@(call op)</li>
</ul>

<p>with the following, constraining axioms:</p>

@(def Equiv-is-an-equivalence)
@(def Equiv-implies-iff-pred-1)
@(def Equiv-implies-equiv-op-1)
@(def Equiv-implies-equiv-op-2)
@(def Closure-of-op-for-pred)
@(def Associativity-of-op)
@(def Commutativity-of-op)

<h3>Theorem of the theory of Abelian Groups</h3>

<p>Given the above constraints, we prove the following generic theorems.</p>

@(def Commutativity-2-of-op)"

  (encapsulate
    ((equiv (x y) t)
     (pred (x) t)
     (op (x y) t))

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

    (defequiv equiv)

    (defcong equiv iff (pred x) 1)

    (defcong equiv equiv (op x y) 1)

    (defcong equiv equiv (op x y) 2)

    (defthm Closure-of-op-for-pred
      (implies (and (pred x)
                    (pred y))
               (pred (op x y))))

    (defthm Associativity-of-op
      (implies (and (pred x)
                    (pred y)
                    (pred z))
               (equiv (op (op x y) z)
                      (op x (op y z)))))

    (defthm Commutativity-of-op
      (implies (and (pred x)
                    (pred y))
               (equiv (op x y)
                      (op y x))))))


(defsection add-commutativity-2
  :parents (abelian-semigroups)
  :short "Macro for adding a second version of commutativity."
  :autodoc nil
  :long "<p>Examples:</p>
@({
    (acl2-asg::add-commutativity-2 equal
                                   rationalp
                                   *
                                   commutativity-of-*
                                   commutativity-2-of-*)

   (acl2-asg::add-commutativity-2 acl2-bag::bag-equal
                                  true-listp
                                  acl2-bag::bag-union
                                  acl2-bag::commutativity-of-bag-union
                                  commutativity-2-of-bag-union)
})

<p>General form:</p>

@({
   (acl2-asg::add-commutativity-2 equiv-name
                                  pred-name
                                  op-name
                                  commutativity-thm-name
                                  commutativity-2-thm-name)
})

<p>where all the arguments are names.</p>

<ul>
<li><b>Equiv-name</b> is the name of an equivalence relation, @('equiv');</li>

<li><b>pred-name</b> is the name of a unary function, @('pred');</li>

<li><b>op-name</b> is the name of a binary function, @('op');</li>

<li><b>commutativity-thm-name</b> is the name of theorem which added a :@(see
rewrite) rule to the data base saying that the operation @('op') is commutative
on the set (of equivalence classes formed by the equivalence relation,
@('equiv'), on the set)

@({
    SG = { x | (pred x) != nil }
})

There must be rules in the data base for the closure of SG under @('op') and
the associativity with respect to @('equiv') of @('op') on SG.</li>
</ul>

<p>The macro adds a rewrite rule for a second version of the commutativity with
respect to equiv of op on SG.  This is done by proving a theorem named
<b>commutativity-2-thm-name</b>.</p>

<p>Here is the form of the rule added by the macro:</p>

@({
    (defthm commutativity-2-thm-name
      (implies (and (pred x)
                    (pred y)
                    (pred z))
               (equiv (op x (op y z))
                      (op y (op x z))))) .
})

<p>Here is what is meant by \"closure of SG under op\":</p>

@({
    (implies (and (pred x)
                  (pred y))
             (pred (op x y)))
})

<p>Here is what is meant by \"associativity with respect to equiv of
op on SG\":</p>

@({
    (implies (and (pred x)
                  (pred y)
                  (pred z))
             (equiv (op (op x y) z)
                    (op x (op y z))))
})

<p>Here is the form of the commutativity rule:</p>

@({
    (defthm commutativity-thm-name
      (implies (and (pred x)
                    (pred y))
               (equiv (op x y)
                      (op y x))))
})"

  (local (defthm commutativity-2-of-op-lemma
           (implies (and (pred x)
                         (pred y)
                         (pred z))
                    (equiv (op (op x y) z)
                           (op (op y x) z)))
           :rule-classes nil))

  (defthm Commutativity-2-of-op
    (implies (and (pred x)
                  (pred y)
                  (pred z))
             (equiv (op x (op y z))
                    (op y (op x z))))
    :hints (("Goal"
             :in-theory (acl2::disable commutativity-of-op)
             :use commutativity-2-of-op-lemma)))

  (defmacro add-commutativity-2 (equiv-name
                                 pred-name
                                 op-name
                                 commutativity-thm-name
                                 commutativity-2-thm-name)
    (declare (xargs :guard (and (symbolp equiv-name)
                                (symbolp pred-name)
                                (symbolp op-name)
                                (symbolp commutativity-thm-name)
                                (symbolp commutativity-2-thm-name))))
    `(encapsulate
       nil
       (local
        (defthm Associativity-of-op-name
          ;; Temporarily ensure that the associativity rewrite rule comes after
          ;; the commutativity rewrite rule.
          (IMPLIES (AND (,pred-name X)
                        (,pred-name Y)
                        (,pred-name Z))
                   (,equiv-name (,op-name (,op-name X Y) Z)
                                (,op-name X (,op-name Y Z))))
          :hints (("Goal" :in-theory (acl2::disable ,commutativity-thm-name)))))

       (defthm ,commutativity-2-thm-name
         (implies (and (,pred-name x)
                       (,pred-name y)
                       (,pred-name z))
                  (,equiv-name (,op-name x (,op-name y z))
                               (,op-name y (,op-name x z))))
         :hints (("Goal"
                  :use (:functional-instance
                        Commutativity-2-of-op
                        (equiv (lambda (x y) (,equiv-name x y)))
                        (pred  (lambda (x)   (,pred-name x)))
                        (op    (lambda (x y) (,op-name x y))))))))))
