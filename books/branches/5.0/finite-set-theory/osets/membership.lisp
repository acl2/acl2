; Fully Ordered Finite Sets
; Copyright (C) 2003-2012 by Jared Davis <jared@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public Lic-
; ense along with this program; if not, write to the Free Soft- ware
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.


; membership.lisp
;
; This file introduces the notions of set membership and subset.  We also go
; into an abstract argument which will form the basis for quantification, and
; especially for pick-a-point and double containment proofs.
;
; At the end of this file, we will disable all of the theorems that pertain to
; the order of elements, providing an entirely membership-based reasoning
; environment for the outer level.

(in-package "SETS")
(include-book "primitives")
(include-book "computed-hints")
(set-verify-guards-eagerness 2)


(defsection in
  :parents (osets)
  :short "@(call in) determines if <tt>a</tt> is a member of the set
<tt>X</tt>."

  :long "<p>The logical definition of <tt>in</tt> makes no mention of the set
order, except implicitly by the use of the set @(see primitives) like @(see
head) and @(see tail).</p>

<p>The :exec version just inlines the set primitives and does one level of loop
unrolling.  On CCL, it seems to run about 2.6x faster on the following
loop:</p>

<code>
 ;; 4.703 sec logic, 1.811 sec exec
 (let ((big-set (loop for i from 1 to 100000 collect i)))
   (gc$)
   (time (loop for i fixnum from 1 to 30000 do (sets::in i big-set))))
</code>

<p>There are other ways we could optimize <tt>in</tt>.  Since the set is
ordered, we could try to use the set order @(see <<) to stop early when we ran
into an element that is larger than the one we are looking for.  For instance,
when looking for 1 in the set '(2 3 4), we know that since <tt>1 &lt;&lt;
2</tt> that <tt>1</tt> cannot be a member of this set.</p>

<p>The simplest way to do this is to use <tt>&lt;&lt;</tt> at every element.
But set order comparisons can be very expensive, especially when sets contain
large cons structures.  So while it is easy to contrive situations where
exploiting the order would be advantageous, like</p>

<code>
 (in 1 '(2 3 4 .... 100000))
</code>

<p>where we could return instantly, there are also times where it would be
slower.  For instance, on</p>

<code>
 (in 100001 '(1 2 3 4 ... 100000))
</code>

<p>we would incur the extra cost of 100,000 calls to <tt>&lt;&lt;</tt>.</p>

<p>For this reason, we do not currently implement any short-circuiting.  The
reasoning is:</p>

<ul>

<li>it is not clear which would be faster in all cases,</li>

<li>it is not clear what the typical usage behavior of <tt>in</tt> is, so even
if we wanted to benchmark alternate implementations, it may be hard to come up
with the right benchmarking suite</li>

<li>both solutions are O(n) anyway, and <tt>in</tt> isn't a function that
should probably be used in any kind of loop so its performance shouldn't be
especially critical to anything</li>

<li>the current method is arguably no less efficient than an unordered
implementation.</li>

</ul>

<p>Future note.  In principle membership in an ordered list might be done in
<tt>O(log_2 n)</tt>.  We are considering using a <i>galloping</i> membership
check in the future to obtain something along these lines.</p>"

  (defun in (a X)
    (declare (xargs :guard (setp X)
                    :verify-guards nil))
    (mbe :logic
         (and (not (empty X))
              (or (equal a (head X))
                  (in a (tail X))))
         :exec
         (and x
              (or (equal a (car x))
                  (and (cdr x)
                       (or (equal a (cadr x))
                           (in a (cddr x))))))))

  (verify-guards in
    :hints(("Goal" :in-theory (enable (:ruleset primitive-rules)))))

  (defthm in-type
    (or (equal (in a X) t)
        (equal (in a X) nil))
    :rule-classes :type-prescription)

  (encapsulate ()

    (local (defthm head-not-whole
             (implies (not (empty X))
                      (not (equal (head X) X)))
             :hints(("Goal" :in-theory (enable (:ruleset primitive-rules))))))

    (local (defthm lemma
             (implies (> (acl2-count x) (acl2-count y))
                      (not (in x y)))))

    (defthm not-in-self
      (not (in x x))))

  (defthm in-sfix-cancel
    (equal (in a (sfix X))
           (in a X)))

  (defthm never-in-empty
    (implies (empty X)
             (not (in a X))))

  (defthm in-set
    (implies (in a X)
             (setp X)))

  (defthm in-tail
    (implies (in a (tail X))
             (in a X)))

  (defthm in-tail-or-head
    (implies (and (in a X)
                  (not (in a (tail X))))
             (equal (head X) a)))

  (defthm in-head
    ;; BOZO seems redundant with never-in-empty
    (equal (in (head X) X)
           (not (empty X)))))


; We now begin to move away from set order.

(defsection head-unique
  :extension head

  (local (defthm lemma
	   (implies (and (not (empty X))
			 (not (equal a (head X)))
			 (not (<< a (head (tail X))))
			 (<< a (head X)))
		    (not (in a X)))
	   :hints(("Goal"
		   :in-theory (enable (:ruleset order-rules))
		   :cases ((empty (tail X)))))))

  (defthm head-minimal
    (implies (<< a (head X))
	     (not (in a X)))
    :hints(("Goal"
	    :in-theory (enable (:ruleset order-rules)))))

  (defthm head-minimal-2
    (implies (in a X)
	     (not (<< a (head X)))))

  (add-to-ruleset order-rules '(head-minimal head-minimal-2))


  (local (defthm lemma2
	   (implies (empty (tail X))
		    (not (in (head X) (tail X))))))

  (local (defthm lemma3
	   (implies (not (empty (tail X)))
		    (not (in (head X) (tail X))))
	   :hints(("Goal" :in-theory (enable (:ruleset order-rules))))))

  ;; This is an interesting theorem, which gives us a concept of uniqueness
  ;; without using the set order to state it!

  (defthm head-unique
    (not (in (head X) (tail X)))
    :hints(("Goal"
	    :use ((:instance lemma2)
		  (:instance lemma3))))))



(defsection in-insert
  :extension insert

  (defthm insert-identity
    (implies (in a X)
             (equal (insert a X) X))
    :hints(("Goal"
            :in-theory (enable head-tail-same
                               (:ruleset order-rules)))))

  (defthm in-insert
    (equal (in a (insert b X))
           (or (in a X)
               (equal a b)))
    :hints(("Goal"
            :in-theory (enable (:ruleset order-rules))
            :induct (insert b X)))))



(defsection weak-insert-induction
  :parents (insert)
  :short "Inducting over insert without exposing the set order."

  :long "<p>When we want to insert an element into an ordered set, the set
order obviously has to be involved so that we can decide where to put the new
element.  Accordingly, the set order plays a role in the induction scheme that
we get from @(see insert)'s definition.  This makes insert somewhat different
than other set operations (membership, union, cardinality, etc.) that just use
a simple @(see tail)-based induction, where the set order is already hidden by
<tt>tail</tt>.</p>

<p>When we are proving theorems about sets, we generally want to avoid thinking
about the set order, but we sometimes need to induct over <tt>insert</tt>.  So,
here we introduce a new induction scheme that allows us to induct over insert
but hides the set order.  We disable the ordinary induction scheme that insert
uses, and set up an induction hint so that <tt>weak-insert-induction</tt> will
automatically be used instead.</p>"

  (defthm weak-insert-induction-helper-1
    (implies (and (not (in a X))
                  (not (equal (head (insert a X)) a)))
             (equal (head (insert a X))
                    (head X)))
    :hints(("Goal" :in-theory (enable (:ruleset order-rules)))))

  (defthm weak-insert-induction-helper-2
    (implies (and (not (in a X))
                  (not (equal (head (insert a X)) a)))
             (equal (tail (insert a X))
                    (insert a (tail X))))
    :hints(("Goal" :in-theory (enable (:ruleset order-rules)))))

  (defthm weak-insert-induction-helper-3
    (implies (and (not (in a X))
                  (equal (head (insert a X)) a))
             (equal (tail (insert a X))
                    (sfix X)))
    :hints(("Goal" :in-theory (enable (:ruleset order-rules)))))

  (defun weak-insert-induction (a X)
    (declare (xargs :guard (setp X)))
    (cond ((empty X) nil)
          ((in a X) nil)
          ((equal (head (insert a X)) a) nil)
          (t (list (weak-insert-induction a (tail X))))))

  (in-theory (disable (:induction insert)))

  (defthm use-weak-insert-induction t
    :rule-classes ((:induction
                    :pattern (insert a X)
                    :scheme (weak-insert-induction a X)))))



(defsection subset
  :parents (osets)
  :short "@(call subset) determines if <tt>X</tt> is a subset of <tt>Y</tt>."

  :long "<p>We use a logically simple definition, but using MBE we exploit the
set order to implement a tail-recursive, linear subset check.</p>

<p>The :exec version of fast-subset just inlines the set primitives and tweaks
the way the order check is done.  It is about 3x faster than the :logic version
of fast-subset on the following loop:</p>

<code>
 ;; 3.83 sec logic, 1.24 seconds exec
 (let ((x (loop for i from 1 to 1000 collect i)))
   (gc$)
   (time$ (loop for i fixnum from 1 to 100000 do (sets::subset x x))))
</code>

<p>In the future we may investigate developing a faster subset check based on
galloping.</p>"

  (defun fast-subset (X Y)
    (declare (xargs :guard (and (setp X) (setp Y))
                    :guard-hints(("Goal" :in-theory (enable (:ruleset primitive-rules) <<)))))
    (mbe :logic
         (cond ((empty X) t)
               ((empty Y) nil)
               ((<< (head X) (head Y)) nil)
               ((equal (head X) (head Y)) (fast-subset (tail X) (tail Y)))
               (t (fast-subset X (tail Y))))
         :exec
         (cond ((null X) t)
               ((null Y) nil)
               ((fast-lexorder (car X) (car Y))
                (and (equal (car X) (car Y))
                     (fast-subset (cdr X) (cdr Y))))
               (t
                (fast-subset X (cdr Y))))))

  (defun subset (X Y)
    (declare (xargs :guard (and (setp X) (setp Y))
                    :verify-guards nil))
    (mbe :logic
         (if (empty X)
                    t
                  (and (in (head X) Y)
                       (subset (tail X) Y)))
         :exec (fast-subset X Y)))

  (defthm subset-type
    (or (equal (subset X Y) t)
        (equal (subset X Y) nil))
    :rule-classes :type-prescription)

  (encapsulate ()

    (local (defthmd lemma
             (implies (not (in (head Y) X))
                      (equal (subset X Y)
                             (subset X (tail Y))))))

    (local (defthm case-1
             (implies (and (not (empty X))
                           (not (empty Y))
                           (not (<< (head X) (head Y)))
                           (not (equal (head X) (head Y)))
                           (implies (and (setp X) (setp (tail Y)))
                                    (equal (fast-subset X (tail Y))
                                           (subset X (tail Y)))))
                      (implies (and (setp X) (setp Y))
                               (equal (fast-subset X Y)
                                      (subset X Y))))
             :hints(("Goal" :in-theory (enable (:ruleset order-rules))
                     :use (:instance lemma)))))

    (local (defthm case-2
             (implies (and (not (empty x))
                           (not (empty y))
                           (not (<< (head x) (head y)))
                           (equal (head x) (head y))
                           (implies (and (setp (tail x)) (setp (tail y)))
                                    (equal (fast-subset (tail x) (tail y))
                                           (subset (tail x) (tail y)))))
                      (implies (and (setp x) (setp y))
                               (equal (fast-subset x y)
                                      (subset x y))))
             :hints(("Goal" :in-theory (enable (:ruleset order-rules))
                     :use (:instance lemma (X (tail X)))))))

    (local (defthm fast-subset-equivalence
             (implies (and (setp X) (setp Y))
                      (equal (fast-subset X Y)
                             (subset X Y)))
             :hints(("Goal" :in-theory (enable (:ruleset order-rules))
                     :induct (fast-subset X Y)))))

    (verify-guards subset)))



(defsection all-by-membership
  :parents (osets)
  :short "A way to quantify over sets."

  :long "<p><tt>all-by-membership</tt> is a generic theorem that can be used to
prove that a property holds of a set by showing that a related property holds
of the set elements.</p>

<p>The most important role of <tt>all-by-membership</tt> is to allow for
pick-a-point proofs of @(see subset).  That is, it allows us to show that
<tt>(subset X Y)</tt> holds by showing that every element of X satisfies
<tt>(in a Y)</tt>.</p>

<p>More generally, we could show that a set satisfies a predicate like
<tt>integer-setp</tt> because each of its elements satisfies
<tt>integerp</tt>.</p>


<h3>Pick-a-Point Proofs in ACL2</h3>

<p>We begin by explaining how pick-a-point proofs of subset can be carried out.
In traditional mathematics, @(see subset) is defined using quantification over
members, e.g., as follows:</p>

<code>
  (equal (subset X Y)
         (forall a (implies (in a X) (in a Y))))
</code>

<p>This definition is very useful for <b>pick-a-point</b> proofs that some set
<tt>X</tt> is a subset of <tt>Y</tt>.  Such a proof begins by picking an
arbitrary point <tt>a</tt> that is a member of <tt>X</tt>.  Then, if we can
show that <tt>a</tt> must be a member of <tt>Y</tt>, we have established
<tt>(subset X Y)</tt>.</p>

<p>These kinds of arguments are extremely useful, and we would like to be able
to carry them out in ACL2 about osets.  But since ACL2 does not have explicit
quantifiers, we cannot even write a theorem like this:</p>

<code>
 (implies (forall a (implies (in a X) (in a Y)))
          (subset X Y))
</code>

<p>But consider the contrapositive of this theorem:</p>

<code>
 (implies (not (subset X Y))
          (exists a (and (in a X) (not (in a Y)))))
</code>

<p>We <i>can</i> prove something like this, by writing an explicit function to
search for an element of <tt>X</tt> that is not an element of <tt>Y</tt>.  That
is, we can prove:</p>

<code>
 (implies (not (subset X Y))
          (let ((a (find-witness X Y)))
            (and (in a X)
                 (not (in a Y)))))
</code>

<p>Once we prove the above, we still need to be able to \"reduce\" a proof of
<tt>(subset X Y)</tt> to a proof of <tt>(implies (in a X) (in a Y))</tt>.
While we can't do this with a direct rewrite rule, we can sort of fake it using
functional instantiation.  As groundwork:</p>

<ul>

<li>Using @(see encapsulate), we introduce functions <tt>sub</tt> and
<tt>super</tt> with the constraint that
<code>
 (implies (in a (sub))
          (in a (super)))
</code></li>

<li>Using this constraint, we prove the generic theorem:
<code>
 (subset (sub) (super))
</code></li>

</ul>

<p>Then, when we want to prove <tt>(subset X Y)</tt> for some particular
<tt>X</tt> and <tt>Y</tt>, we can functionally instantiate the generic theorem
with</p>

<code>
   sub   &lt;-- (lambda () X)
   super &lt;-- (lambda () Y)
</code>

<p>And this allows us to prove <tt>(subset X Y)</tt> as long as we can relieve
the constraint, i.e., <tt>(implies (in a X) (in a Y))</tt>.</p>


<h3>Generalizing Pick-a-Point Proofs</h3>

<p>In earlier versions of the osets library, we used an explicit argument to
reduce subset proofs to pick-a-point style membership arguments.  But we later
generalized the approach to arbitrary predicates instead.</p>

<p>First, notice that if you let the predicate <tt>(P a)</tt> be defined as
<tt>(in a Y)</tt>, then <tt>(subset X Y)</tt> is just</p>

<code>
 (forall a, (implies (in a X) (P a)))
</code>

<p>Our generalization basically lets you reduce a proof of <tt>(P-setp X)</tt>
to a proof of <tt>(implies (in a X) (P a))</tt>, for an arbitrary predicate
<tt>P</tt>.  This can be used to prove subset by just chooisng <tt>P</tt> as
described above, but it can also be used for many other ideas by just changing
the meaning of <tt>P</tt>.  For instance, if <tt>P</tt> is @(see integerp),
then we can show that <tt>X</tt> is an <tt>integer-setp</tt> or similar.</p>

<p>The mechanism is just an adaptation of that described in the previous
section.</p>

<ul>

<li>We begin by introducing a completely arbitrary <tt>predicate</tt>.</li>

<li>Based on <tt>predicate</tt>, we introduce a new function, <tt>all</tt>,
which checks to see if every member in a set satisfies <tt>predicate</tt>.</li>

<li>We set up an encapsulate which allows us to assume that some hypotheses are
true and that any member of some set satisfies <tt>predicate</tt>.</li>

</ul>

<p>Finally, we prove <tt>all-by-membership</tt>, which shows that under these
assumptions, the set satisfies <tt>all</tt>.  This theorem can be functionally
instantiated to reduce a proof of <tt>(all X)</tt> to a proof of</p>

<code>
  (implies (in a X) (P a))
</code>"

  (encapsulate
    (((predicate *) => *))
    (local (defun predicate (x) x)))

  (defun all (set-for-all-reduction)
    (declare (xargs :guard (setp set-for-all-reduction)))
    (if (empty set-for-all-reduction)
        t
      (and (predicate (head set-for-all-reduction))
           (all (tail set-for-all-reduction)))))

  (encapsulate
    (((all-hyps) => *)
     ((all-set) => *))

    (local (defun all-hyps () nil))
    (local (defun all-set () nil))

    (defthmd membership-constraint
      (implies (all-hyps)
               (implies (in arbitrary-element (all-set))
                        (predicate arbitrary-element)))))

  (local (defun find-not (X)
           (declare (xargs :guard (setp X)))
           (cond ((empty X) nil)
                 ((not (predicate (head X))) (head X))
                 (t (find-not (tail X))))))

  (local (defthm lemma-find-not-is-a-witness
           (implies (not (all x))
                    (and (in (find-not x) x)
                         (not (predicate (find-not x)))))))

  (defthmd all-by-membership
    (implies (all-hyps)
             (all (all-set)))
    :hints(("Goal"
            :use (:instance membership-constraint
                            (arbitrary-element (find-not (all-set))))))))



(defsection pick-a-point-subset-strategy
  :parents (osets)
  :short "Automatic pick-a-point proofs of @(see subset)."

  :long "<p>The rewrite rule <tt>pick-a-point-subset-strategy</tt> tries to
automatically reduce proof goals such as:</p>

<code>
 (implies hyps
          (subset X Y))
</code>

<p>To proofs of:</p>

<code>
 (implies (and hyps (in a X))
          (in a Y))
</code>

<p>The mechanism for doing this is somewhat elaborate: the rewrite rule
replaces the <tt>(subset X Y)</tt> with <tt>(subset-trigger X Y)</tt>.  This
trigger is recognized by a computed hint, which then suggest proving the
theorem via functional instantiation of @(see all-by-membership).</p>

<p>The pick-a-point method is often a good way to prove subset relations.  On
the other hand, this rule is very heavy-handed, and you may need to disable it
if you do not want to use the pick-a-point method to solve your goal.</p>"

  (defun subset-trigger (X Y)
    (declare (xargs :guard (and (setp X) (setp Y))))
    (subset X Y))

  (defthm pick-a-point-subset-strategy
    (implies (and (syntaxp (rewriting-goal-lit mfc state))
                  (syntaxp (rewriting-conc-lit `(subset ,X ,Y) mfc state)))
             (equal (subset X Y)
                    (subset-trigger X Y))))

  (in-theory (disable subset-trigger))

  ;; BOZO replace all this stuff with witness-cp?
  (COMPUTED-HINTS::automate-instantiation
   :new-hint-name pick-a-point-subset-hint
   :generic-theorem all-by-membership
   :generic-predicate predicate
   :generic-hyps all-hyps
   :generic-collection all-set
   :generic-collection-predicate all
   :actual-collection-predicate subset
   :actual-trigger subset-trigger
   :predicate-rewrite (((predicate ?x ?y) (in ?x ?y)))
   :tagging-theorem pick-a-point-subset-strategy))




(defsection subset-theorems
  :extension subset

  (defthm subset-sfix-cancel-X
    (equal (subset (sfix X) Y)
           (subset X Y)))

  (defthm subset-sfix-cancel-Y
    (equal (subset X (sfix Y))
           (subset X Y)))

  (defthm empty-subset
    (implies (empty X)
             (subset X Y)))

  (defthm empty-subset-2
    (implies (empty Y)
             (equal (subset X Y)
                    (empty X))))

  (defthm subset-in
    (and (implies (and (subset X Y)
                       (in a X))
                  (in a Y))
         (implies (and (in a X)
                       (subset X Y))
                  (in a Y))))

  (defthm subset-in-2
    (and (implies (and (subset X Y)
                       (not (in a Y)))
                  (not (in a X)))
         (implies (and (not (in a Y))
                       (subset X Y))
                  (not (in a X)))))

  (encapsulate
    ()
    (local (defthm l0
             (equal (subset (insert a nil) Y)
                    (in a Y))
             :hints(("Goal" :in-theory (enable (:ruleset primitive-rules))))))

    (defthm subset-insert-X
      (equal (subset (insert a X) Y)
             (and (subset X Y)
                  (in a Y)))
      :hints(("Goal" :induct (insert a X)))))

  (defthm subset-reflexive
    (subset X X))

  (defthm subset-transitive
    (and (implies (and (subset X Y)
                       (subset Y Z))
                  (subset X Z))
         (implies (and (subset Y Z)
                       (subset X Y))
                  (subset X Z))))

  (defthm subset-membership-tail
    (implies (and (subset X Y)
                  (in a (tail X)))
             (in a (tail Y)))
    :hints(("Goal" :in-theory (enable (:ruleset order-rules)))))

  (defthm subset-membership-tail-2
    (implies (and (subset X Y)
                  (not (in a (tail Y))))
             (not (in a (tail X))))
    :hints(("Goal" :in-theory (disable subset-membership-tail)
            :use (:instance subset-membership-tail))))

  (defthm subset-insert
    (subset X (insert a X)))

  (defthm subset-tail
    (subset (tail X) X)
    :rule-classes ((:rewrite)
                   (:forward-chaining :trigger-terms ((tail x))))))




(defsection double-containment
  :parents (osets)
  :short "A strategy for proving sets are equal because they are subsets
of one another."

  :long "<p>Double containment can be a good way to prove that two sets are
equal to one another.</p>

<p>Unfortunately, because this rule targets <tt>equal</tt> it can get quite
expensive.  You may sometimes wish to disable it to speed up your proofs, as
directed by @(see accumulated-persistence).</p>"

; The general argument is the following:
;
; Suppose that we have two sets which are subsets of one another, i.e. (subset
; X Y) and (subset Y X) are true.  First, we will show that (head X) = (head
; Y).  Next we will show that (in a (tail X)) implies that (in a (tail Y)).
; This fact is then used for a sub- set by membership argument to show that
; (tail X) = (tail Y).  Now, (head X) = (head Y) and (tail X) = (tail Y) can be
; used together to show that X = Y (see primitives.lisp, head-tail-same) so we
; are done.

; Here are the details.  First we show that the heads are the same:

  (local (defthmd double-containment-lemma-head
	   (implies (and (subset X Y)
			 (subset Y X))
		    (equal (head X) (head Y)))
	   :hints(("Goal" :in-theory (enable (:ruleset order-rules))))))


; Next we show that (tail X) is a subset of (tail Y), using a subset by
; membership argument:

  (local (defthmd in-tail-expand
	   (equal (in a (tail X))
		  (and (in a X)
		       (not (equal a (head X)))))))

  (local (defthmd double-containment-lemma-in-tail
	   (implies (and (subset X Y)
			 (subset Y X))
		    (implies (in a (tail X))   ; could be "equal" instead,
			     (in a (tail Y)))) ; but that makes loops.
	   :hints(("Goal"
		   :in-theory (enable (:ruleset order-rules))
		   :use ((:instance in-tail-expand (a a) (X X))
			 (:instance in-tail-expand (a a) (X Y)))))))

  (local (defthmd double-containment-lemma-tail
	   (implies (and (subset X Y)
			 (subset Y X))
		    (subset (tail X) (tail Y)))
	   :hints(("Goal" :in-theory (enable double-containment-lemma-in-tail)))))

; Finally, we are ready to show that double containment is equality.  To do
; this, we need to induct in such a way that we consider the tails of X and Y.
; Then, we will use our fact that about the tails being subsets of one another
; in the inductive case.

  (local (defun double-tail-induction (X Y)
	   (declare (xargs :guard (and (setp X) (setp Y))))
	   (if (or (empty X) (empty Y))
	       (list X Y)
	     (double-tail-induction (tail X) (tail Y)))))

  (local (defthm double-containment-is-equality-lemma
	   (IMPLIES (AND (NOT (OR (EMPTY X) (EMPTY Y)))
			 (IMPLIES (AND (SUBSET (TAIL X) (TAIL Y))
				       (SUBSET (TAIL Y) (TAIL X)))
				  (EQUAL (EQUAL (TAIL X) (TAIL Y)) T))
			 (SETP X)
			 (SETP Y)
			 (SUBSET X Y)
			 (SUBSET Y X))
		    (EQUAL (EQUAL X Y) T))
	   :hints(("Goal"
                   :in-theory (enable head-tail-same)
		   :use ((:instance double-containment-lemma-tail
				    (X X) (Y Y))
			 (:instance double-containment-lemma-tail
				    (X Y) (Y X))
			 (:instance double-containment-lemma-head
				    (X X) (Y Y)))))))

  (local (defthmd double-containment-is-equality
	   (implies (and (setp X)
			 (setp Y)
			 (subset X Y)
			 (subset Y X))
		    (equal (equal X Y) t))
	   :hints(("Goal"
                   :in-theory (enable head-tail-same)
                   :induct (double-tail-induction X Y)))))

  (defthm double-containment
    ;; I added backchain limits to this because targetting equal is so expensive.
    ;; Even so it is possibly very expensive.
    (implies (and (setp X)
		  (setp Y))
	     (equal (equal X Y)
		    (and (subset X Y)
			 (subset Y X))))
    :rule-classes ((:rewrite :backchain-limit-lst 1))
    :hints(("Goal" :use (:instance double-containment-is-equality)))))


; We are now done with the membership level.  We disable all of the order based
; reasoning that we introduced here.

(in-theory (disable head-minimal head-minimal-2))






;; [Jared] I moved a few things here from what used to be fast.lisp, so they can
;; be shared across the new union/intersection/difference files

; I've tried various approaches to exposing the set order.  My current strategy
; is to open all primitives, convert IN to MEMBER, and convert SUBSET to
; SUBSETP (list subset).  BOZO discuss the other, lifting approach.

(encapsulate
  ()
  (local (in-theory (enable (:ruleset primitive-rules)
                            (:ruleset order-rules))))

  (defthm setp-of-cons
    (equal (setp (cons a X))
           (and (setp X)
                (or (<< a (head X))
                    (empty X)))))

  (defthm in-to-member
    (implies (setp X)
             (equal (in a X)
                    (if (member a x)
                        t
                      nil))))

  (defthm not-member-when-smaller
    (implies (and (<< a (car x))
                  (setp x))
             (not (member a x))))

  (defthm subset-to-subsetp
    (implies (and (setp x)
                  (setp y))
             (equal (subset x y)
                    (subsetp x y))))

  (defthm lexorder-<<-equiv
    ;; This lets us optimize << into just lexorder when we've already
    ;; checked equality.
    (implies (not (equal a b))
             (equal (equal (<< a b) (lexorder a b))
                    t))
    :hints(("Goal" :in-theory (enable <<)))))

(def-ruleset low-level-rules
  '(setp-of-cons
    in-to-member
    not-member-when-smaller
    subset-to-subsetp
    lexorder-<<-equiv
    (:ruleset primitive-rules)
    (:ruleset order-rules)))

(in-theory (disable (:ruleset low-level-rules)))



; These fast versions recur on one or both of their arguments, but not always
; the same argument.  Hence, we need to introduce a more flexible measure to
; prove that they terminate.  Fortunately, this is still relatively simple:

(defun fast-measure (X Y)
  (+ (acl2-count X) (acl2-count Y)))
