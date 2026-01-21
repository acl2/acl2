; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2019 Centaur Technology
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

(in-package "FGL")
(include-book "fgl-object")
(include-book "bfr")
(include-book "centaur/meta/term-vars" :dir :system)
(include-book "std/util/defenum" :dir :system)
(local (std::add-default-post-define-hook :fix))


;; CGRAPH type -- see ctrex-utils.lisp

(defenum ctrex-ruletype-p (:elim :property :fixup :implicit nil))

(defconst *ctrex-order-first* 0)
(defconst *ctrex-order-mid* 5)
(defconst *ctrex-order-last* 10)

(defconst *ctrex-eval-default-priority* 10)
(defconst *ctrex-elim-default-priority* 10)
(defconst *ctrex-property-default-priority* 8)
(defconst *ctrex-fixup-default-priority* 10)
(defconst *ctrex-other-default-priority* 5)


(defprod ctrex-rule
  :parents (cgraph)
  :short "Internal structure of a counterexample generation rule"
  :long "<p>As discussed in @(see cgraph), this is the format in which a rule is stored. This rule has one match pattern, determining the objects on which the rule triggers.
 A rule definition form may create more than one ctrex-rule (of the same name)
 to accomodate different patterns that might match.</p>"
  ((name symbolp :rule-classes :type-prescription)
   (match pseudo-termp "Pattern to be matched in order to trigger this rule")
   ;; (match-var pseudo-var-p "Variable name denoting the whole matched object")
   (unify-subst fgl-object-bindings-p "Initial substitution for unifying with match -- usually nil")
   (target pseudo-termp "Term representing the object that will be assigned a value based on this rule")
   (deps pseudo-term-subst-p "Substitution giving the dependencies of the rule")
   (dep-success-vars pseudo-term-subst-p "Pairs such as @('(a-success . a)') where @('a') is one of the keys of deps. Vars such as @('a-success') may then be used in the success/priority/value formulas.")
   (success pseudo-termp "Term evaluated to determine whether the formula was successful")
   (priority pseudo-termp "Term evaluated to determine the priority of the formula application")
   (value pseudo-termp "Term evaluated to compute the value of the target")
   (order natp "Relative ordering, for determining which formulas to evaluate first/last -- use constants @('*ctrex-order-first*'), @('*ctrex-order-mid*'), @('*ctrex-order-last*').")
   (ruletype ctrex-ruletype-p))
  :layout :alist)


(defprod cgraph-formula
  ;; The cgraph will be a map from target objects to lists of cgraph-formulas, so
  ;; the target object is not represented in the formula since it is implicit.
  ((deps fgl-object-bindings-p "Mapping from variable names (used in the success/priority/value terms) to dependency objects")
   ;; The rest is typically, but not always, copied from the ctrex-rule that gave rise to the formula:
   (name symbolp :rule-classes :type-prescription "Rule name that gave rise to this formula")
   (dep-success-vars pseudo-term-subst-p "Pairs such as @('(a-success . a)') where @('a') is one of the keys of deps. Vars such as @('a-success') may then be used in the success/priority/value formulas.")
   (success pseudo-termp "Term evaluated to determine whether the formula was successful")
   (priority pseudo-termp "Term evaluated to determine the priority of the formula application")
   (value pseudo-termp "Term evaluated to compute the value of the target")
   (order natp "Relative ordering, for determining which formulas to evaluate first/last -- use constants @('*ctrex-order-first*'), @('*ctrex-order-mid*'), @('*ctrex-order-last*').")
   (ruletype ctrex-ruletype-p))
  :layout :alist)

(fty::deflist cgraph-formulalist :elt-type cgraph-formula :true-listp t)

(defprod cgraph-equivnode
  ((equivalence fgl-object-p "The object signifying the equivalence between the target and other")
   (other fgl-object-p "The potentially equivalent other object"))
  :layout :alist)

(fty::deflist cgraph-equivlist :elt-type cgraph-equivnode :true-listp t)

(define cgraph-formula-order< ((x cgraph-formula-p) (y cgraph-formula-p))
  (< (cgraph-formula->order x) (cgraph-formula->order y))
  ///
  (acl2::defsort cgraph-formula-sort
    :prefix cgraph-formula
    :compare< cgraph-formula-order<
    :comparablep cgraph-formula-p
    :comparable-listp cgraph-formulalist-p
    :true-listp t))

(defprod cgraph-outedges
  ((formulas cgraph-formulalist-p)
   (equivs cgraph-equivlist-p))
  :layout :alist)
  

(fty::defmap cgraph :key-type fgl-object :val-type cgraph-outedges :true-listp t
  :parents (fgl-counterexample-implementation-details)
  :short "FGL counterexample generator graph"
  :long "
<p>A counterexample generation graph (cgraph) is akin to a bipartite directed
graph. That is, there are two types of nodes, and edges only go between
opposite node types. The first type of node is an <em>object node</em>, which
is some FGL symbolic object for which we want to derive a concrete value. The
other type of node is divided into two subtypes: formula nodes and equivalence
nodes. Both subtypes signify relations betwee object nodes.</p>

<ul>

<li><em>Object nodes</em> are each associated with some FGL symbolic object. At
the start of counterexample generation, we have an assignment of values to
certain objects (those associated with Boolean variables in the Boolean
variable database), and we want to get an assignment of values to other
objects (namely, the top level variables of the theorem).</li>

<li><em>Formula nodes</em> each offer a formula for deciding on a value of (or,
sometimes, updating the value of) some particular object (its target).  Each
formula node has exactly one in-edge, coming from its target object node. It
may have several out-edges, pointing to objects (dependencies) whose derived
values could be used in the formula to help compute the target object's
value.</li>

<li><em>Equivalence nodes</em> each describe a potential equivalence between
object nodes. An equivalence node has one in-edge (from one of the two
potentially equivalent objects), an out-edge to the equivalence term (an object
signifying the equivalence itself, which if assigned the value T means the two
equivalent objects are the same), and another out-edge to the other potentially
equivalent object; there will be another corresponding equivalence node with
the edges between the two potentially equivalent objects reversed.</li>

</ul>

<p>The representation of the graph is a map from FGL objects (target object
nodes) to lists of formula nodes and equivalence nodes to which it has
out-edges.  Each formula node and equivalence node contains the objects to
which it has out-edges, as well as other info about the formula.</p>

<h3>Deriving Object Values from a Cgraph</h3>

<p>To derive a value for an object given a counterexample generation graph, we
traverse the graph depth-first starting at that object. We check the following
two \"short-circuit\" cases:</p>

<ul>

<li>If the object corresponds to a Boolean variable from the database, the
counterexample assignment from SAT determines its value.</li>

<li>If the object is variable-free (has no @(':g-var') sub-objects) and its
value can be computed, that determines its value.</li>

</ul>

<p>If neither of these two cases holds, we proceed to look at the object's
equivalence nodes. For each equivalence node, we recursively try to determine a
value for the equivalence object. If this is successful and the value is true,
then we collect the equivalent object into a set with the original object, add
its formula nodes to the original object's formula nodes, and continue to
explore both the original object's equivalences and the equivalent
object's. When done, this results in an equivalence class of objects and a set
of formula edges. However, it is also possible that some equivalent object
satisfies one of the short-circuit cases: if this is found to be true, then all
the equivalent objects are assigned that value.</p>

<p>If no short-circuit case was found, then we try each formula node collected
from the equivalence classes. For each formula, we recursively try to derive
the values for each of its dependencies (objects connected by object edges from
the formula node). After visiting all these edges (successfully determining
values for the objects or not), the formula node computes some results:</p>

<ul>
<li>a decision of whether the formula was computed successfully or not, based
on the success/failure and values of the dependencies</li>
<li>if successful, the computed value for the object</li>
<li>if successful, a priority value to compare to other potential formula nodes
for the object.</li>
</ul>

<p>If the formula was successful, then the equivalence class of objects has a
candidate value, but other formulas may also offer their own values. These may
even use the value computed from other formulas. The priority values produced
by successful formulas decide which one wins.</p>

<h3>Building a Cgraph</h3>

<p>A cgraph is generated via rules that trigger on object nodes that are added
to the graph.  If a new object node matches such a rule, the rule adds a new
formula node for some object (which may also be new, potentially triggering
more rules).  The object edges of the new formula again potentially add new
objects and trigger more rules.</p>

<h3>Kinds of Cgraph Rules/Formulas</h3>

<ul>

<li>Elim rules say how to compute the value of some aggregate/product once we
have computed values for their fields. Typically, an elim rule is triggered by
an object that is a field accessor call -- say @('(field1 (foo x))'). It
provides a value for the argument to the accessor (here @('(foo x)')) and it
has object edges to all of the accessors. Once we have derived the values for
all the accessor calls (or failed at some of them), the formula says how to
construct the object, perhaps giving default values for any accessors for which
we've failed to derive a value. The appearance of other accessor calls of the
same target object doesn't add new formula nodes; elim rules create one formula
node per target.</li>

<li>Property rules contribute updates to some object such as an alist or
map. Like elim rules, they are typically triggered by a call of a lookup of
some sort, e.g. @('(assoc key (foo x))'). This will add a formula node
targeting @('(foo x)') and depending on @('(assoc key (foo x))') and
@('key'). The formula describes how to update the target based on the value of
the lookup and the key; e.g., @('(cons (cons key lookup) target)'). It is
expected that several property rule formula nodes may update their mutual
target, and it shouldn't matter the order in which the updates happen.</li>

<li>Fixup rules create formulas that are supposed to run after all non-fixup
formulas for the target object, and fix up the existing value of the object to
meet some desired condition.</li>

<li>Implicitly, for any object that is a function call, that object's value can
be computed by computing values for the arguments of the call and then applying
the function to those arguments. This method should usually have lower priority
than other formulas, if there are any: typically, we are trying to compute
values for \"small\" terms (variables) starting with values for \"large\"
terms (Boolean variable database entries), and this sort of rule goes the other
way--trying to derive the value of a larger term from its smaller
components.</li>

</ul>

<p>These behaviors can be generally expressed with a few rule parameters:</p>

<ul>

<li>Match conditions -- what objects induce the application of the rule to
update the graph. Typical rules trigger on one or more term patterns with
leading function symbols, and match if a new object node unifies with the
pattern.</li>

<li>Target object -- typically formulated in terms of the matching object's
unifying substitution</li>

<li>Dependencies -- often overlap with matching triggers but may include others</li>

<li>Order -- e.g., fixup formulae should run last, equivalence formulas should
run first</li>

<li>Value formula</li>
<li>Success formula</li>
<li>Priority formula</li>
</ul>

<p>These last formulas can use various variables in them: the values and
success flags of the dependencies, and the the previous value, success flag,
and priority of the target. These are initialized and updated according to
these rules:</p>

<ul>

<li>If the formula's success flag is NIL, then there are no updates to the
target success, priority, and value. The rest of these rules assume that the
formula succeeded.</li>

<li>The target success flag is initially NIL and is updated to T when a formula
succeeds.</li>

<li>The target priority is updated to the formula priority if the target
success flag was NIL or if the formula priority was greater than the target
priority.</li>

<li>The target value is updated to the formula value if the target success flag
was NIL or if the formula priority was greater than the target priority.</li>

<li>If the target success flag was T, the target priority equals the formula
priority, and the formula value differs from the target value, then a
conflicting assignment warning is stored.</li>

</ul>

")


(fty::defmap cgraph-memo :key-type fgl-object :true-listp t)

(defprod cgraph-value
  ((val)
   (priority natp :rule-classes :type-prescription)
   (rule symbolp :rule-classes :type-prescription))
  :layout :alist)
    

(fty::defmap cgraph-alist :key-type fgl-object :val-type cgraph-value :true-listp t)
            
   

   


(define cgraph-formula-bfrlist ((x cgraph-formula-p))
  (fgl-object-bindings-bfrlist (cgraph-formula->deps x))
  ///
  (defthm bfrlist-of-cgraph-formula->deps
    (implies (not (member v (cgraph-formula-bfrlist x)))
             (not (member v (fgl-object-bindings-bfrlist (cgraph-formula->deps x))))))

  (defthm bfrlist-of-cgraph-formula
    (equal (cgraph-formula-bfrlist (cgraph-formula deps name succvars success priority value order ruletype))
           (fgl-object-bindings-bfrlist deps))))

(define cgraph-formulalist-bfrlist ((x cgraph-formulalist-p))
  (if (atom x)
      nil
    (append (cgraph-formula-bfrlist (car x))
            (cgraph-formulalist-bfrlist (cdr x))))
  ///
  (defthm cgraph-formula-bfrlist-of-car-cdr
    (implies (not (member v (cgraph-formulalist-bfrlist x)))
             (and (not (member v (cgraph-formula-bfrlist (car x))))
                  (not (member v (cgraph-formulalist-bfrlist (cdr x)))))))
  (defthm cgraph-formulalist-bfrlist-of-cons
    (equal (cgraph-formulalist-bfrlist (cons a b))
           (append (cgraph-formula-bfrlist a)
                   (cgraph-formulalist-bfrlist b))))
  (defthm cgraph-formulalist-bfrlist-of-append
    (equal (cgraph-formulalist-bfrlist (append a b))
           (append (cgraph-formulalist-bfrlist a)
                   (cgraph-formulalist-bfrlist b)))))

(define cgraph-equivnode-bfrlist ((x cgraph-equivnode-p))
  (append (fgl-object-bfrlist (cgraph-equivnode->equivalence x))
          (fgl-object-bfrlist (cgraph-equivnode->other x)))
  ///
  (defthm bfrlist-of-cgraph-equivnode-accessors
    (implies (not (member v (cgraph-equivnode-bfrlist x)))
             (and (not (member v (fgl-object-bfrlist (cgraph-equivnode->equivalence x))))
                  (not (member v (fgl-object-bfrlist (cgraph-equivnode->other x)))))))

  (defthm cgraph-equivnode-bfrlist-of-cgraph-equivnode
    (equal (cgraph-equivnode-bfrlist (cgraph-equivnode equivalence other))
           (append (fgl-object-bfrlist equivalence)
                   (fgl-object-bfrlist other)))))

(define cgraph-equivlist-bfrlist ((x cgraph-equivlist-p))
  (if (atom x)
      nil
    (append (cgraph-equivnode-bfrlist (car x))
            (cgraph-equivlist-bfrlist (cdr x))))
  ///
  (defthm cgraph-equivnode-bfrlist-of-car-cdr
    (implies (not (member v (cgraph-equivlist-bfrlist x)))
             (and (not (member v (cgraph-equivnode-bfrlist (car x))))
                  (not (member v (cgraph-equivlist-bfrlist (cdr x)))))))

  (defthm cgraph-equivlist-bfrlist-of-cons
    (equal (cgraph-equivlist-bfrlist (cons a x))
           (append (cgraph-equivnode-bfrlist a)
                   (cgraph-equivlist-bfrlist x)))))

(define cgraph-outedges-bfrlist ((x cgraph-outedges-p))
  (append (cgraph-formulalist-bfrlist (cgraph-outedges->formulas x))
          (cgraph-equivlist-bfrlist (cgraph-outedges->equivs x)))
  ///
  (defthm bfrlist-of-cgraph-outedges-accessors
    (implies (not (member v (cgraph-outedges-bfrlist x)))
             (and (not (member v (cgraph-formulalist-bfrlist (cgraph-outedges->formulas x))))
                  (not (member v (cgraph-equivlist-bfrlist (cgraph-outedges->equivs x)))))))

  (defthm cgraph-outedges-bfrlist-of-cgraph-outedges
    (equal (cgraph-outedges-bfrlist (cgraph-outedges formulas equivs))
           (append (cgraph-formulalist-bfrlist formulas)
                   (cgraph-equivlist-bfrlist equivs)))))

(define cgraph-bfrlist ((x cgraph-p))
  (if (atom x)
      nil
    (append (and (mbt (And (consp (car x))
                           (fgl-object-p (caar x))))
                 (cgraph-outedges-bfrlist (cdar x)))
            (cgraph-bfrlist (cdr x))))
  ///
  (defthm lookup-in-cgraph-bfrlist
    (implies (and (not (member v (cgraph-bfrlist x)))
                  (fgl-object-p k))
             (not (member v (cgraph-outedges-bfrlist (cdr (hons-assoc-equal k x))))))
    :hints(("Goal" :in-theory (enable hons-assoc-equal))))

  (defthm cgraph-bfrlist-of-fast-alist-fork
    (implies (and (not (member v (cgraph-bfrlist x)))
                  (not (member v (cgraph-bfrlist y))))
             (not (member v (cgraph-bfrlist (fast-alist-fork x y))))))

  (defthm cgraph-bfrlist-of-cons
    (equal (cgraph-bfrlist (cons a x))
           (append (and (consp a) (fgl-object-p (car a))
                        (cgraph-outedges-bfrlist (cdr a)))
                   (cgraph-bfrlist x))))
  
  (local (defthm cgraph-fix-of-bad-car
           (implies (not (And (consp (car x))
                              (fgl-object-p (caar x))))
                    (equal (cgraph-fix x)
                           (cgraph-fix (cdr x))))
           :hints(("Goal" :in-theory (enable cgraph-fix))))))






(define cgraph-formula-bfrs-ok ((x cgraph-formula-p)
                                &optional ((bfrstate bfrstate-p) 'bfrstate))
  :returns (ok)
  (fgl-object-bindings-bfrs-ok (cgraph-formula->deps x))
  ///
  (defret <fn>-in-terms-of-bfrlist
    (equal ok
           (bfr-listp (cgraph-formula-bfrlist x)))
    :hints(("Goal" :in-theory (enable cgraph-formula-bfrlist)))))

(define cgraph-formulalist-bfrs-ok ((x cgraph-formulalist-p)
                                    &optional ((bfrstate bfrstate-p) 'bfrstate))
  :returns (ok)
  (if (atom x)
      t
    (and (cgraph-formula-bfrs-ok (car x))
         (cgraph-formulalist-bfrs-ok (cdr x))))
  ///
  (defret <fn>-in-terms-of-bfrlist
    (equal ok
           (bfr-listp (cgraph-formulalist-bfrlist x)))
    :hints(("Goal" :in-theory (enable cgraph-formulalist-bfrlist)))))


(define cgraph-equivnode-bfrs-ok ((x cgraph-equivnode-p)
                                  &optional ((bfrstate bfrstate-p) 'bfrstate))
  :returns (ok)
  (and (fgl-object-bfrs-ok (cgraph-equivnode->equivalence x))
       (fgl-object-bfrs-ok (cgraph-equivnode->other x)))
  ///
  (defret <fn>-in-terms-of-bfrlist
    (equal ok
           (bfr-listp (cgraph-equivnode-bfrlist x)))
    :hints(("Goal" :in-theory (enable cgraph-equivnode-bfrlist)))))

(define cgraph-equivlist-bfrs-ok ((x cgraph-equivlist-p)
                                  &optional ((bfrstate bfrstate-p) 'bfrstate))
  :returns (ok)
  (if (atom x)
      t
    (and (cgraph-equivnode-bfrs-ok (car x))
            (cgraph-equivlist-bfrs-ok (cdr x))))
  ///
  (defret <fn>-in-terms-of-bfrlist
    (equal ok
           (bfr-listp (cgraph-equivlist-bfrlist x)))
    :hints(("Goal" :in-theory (enable cgraph-equivlist-bfrlist)))))

(define cgraph-outedges-bfrs-ok ((x cgraph-outedges-p)
                                 &optional ((bfrstate bfrstate-p) 'bfrstate))
  :returns (ok)
  (and (cgraph-formulalist-bfrs-ok (cgraph-outedges->formulas x))
       (cgraph-equivlist-bfrs-ok (cgraph-outedges->equivs x)))
  ///
  (defret <fn>-in-terms-of-bfrlist
    (equal ok
           (bfr-listp (cgraph-outedges-bfrlist x)))
    :hints(("Goal" :in-theory (enable cgraph-outedges-bfrlist)))))

(define cgraph-bfrs-ok ((x cgraph-p)
                        &optional ((bfrstate bfrstate-p) 'bfrstate))
  :returns (ok)
  (if (atom x)
      t
    (and (or (not (mbt (And (consp (car x))
                            (fgl-object-p (caar x)))))
             (cgraph-outedges-bfrs-ok (cdar x)))
         (cgraph-bfrs-ok (cdr x))))
  ///
  (defret <fn>-in-terms-of-bfrlist
    (equal ok
           (bfr-listp (cgraph-bfrlist x)))
    :hints(("Goal" :in-theory (enable cgraph-bfrlist)))))


