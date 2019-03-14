; Copyright (C) 2017 Centaur Technology
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

(in-package "STOBJS")

(include-book "centaur/misc/prev-stobj-binding" :dir :system)
;; (include-book "tools/rulesets" :dir :system)
(include-book "centaur/fty/fixequiv" :dir :system)
(include-book "std/basic/defs" :dir :system)
(include-book "std/basic/arith-equiv-defs" :dir :system)
(include-book "tools/templates" :dir :system)
(local (include-book "std/basic/arith-equivs" :dir :system))


(defxdoc stobj-updater-independence
  :parents (std/stobjs)
  :short "Discussion of the accessor/updater independence or <i>frame problem</i>,
          especially as it relates to the @(see def-updater-independence-thm) utility."
  :long "<p>Note: This is related to what is known as the frame problem in
philosophy/artificial intelligence/logic; for a broader discussion see <a
href=\"https://plato.stanford.edu/entries/frame-problem/\">this
article</a>.</p>

<p>When reasoning about structured data in ACL2, especially stobjs, one
commonly needs to know that a given updater has no effect on a given accessor.
During the development of any large program involving such a structured object,
the number and complexity of accessor and updater functions tends to grow until
the ad-hoc approach to the problem (proving each such theorem as it is needed)
becomes unworkable.</p>

<p>In the ad hoc approach, a given data structure might require a number of
theorems close to the product of the structure's accessor and updater count.
For many programs this isn't so large that it is impossible to generate and
prove all such theorems, but we propose a much more scalable approach here.</p>

<h3>Proposed Approach</h3>

<p>Broadly speaking, the approach requires the following two sorts of theorems:</p>

<p>The approach described here (and implemented by @(see
def-updater-independence-thm) relies on indexed accesses and updates of the
structure.  That is, there should be a single accessor and a single updater
function in terms of which all primitive accesses and updates can be logically
described, such as @('nth')/@('update-nth'), @('assoc')/@('acons'), or
@('g')/@('s').  If the data structure in question doesn't have such a single
accessor/updater, it is easy (though perhaps tedious) to define them.</p>

<p>The main idea is to prove two kinds of theorems that work together:</p>

<ul>
<li>For each accessor, a theorem stating sufficient conditions under which the
accessor applied to two different structures produces equal results.</li>

<li>For each updater, one or more theorems stating that the updater does not
change certain fields or accessor applications.</li>
</ul>

<h4>Example 1</h4>
<p>The following theorem states that as long as element 3 of
two objects are equal, the @('access-3rd') of those two stobjs is equal:</p>
@({
 (implies (equal (nth 3 new) (nth 3 old))
          (equal (access-3rd new) (access-3rd old)))
 })

<p>Note that if we interpret this as a rewrite rule, the variable @('old') is
free, which would greatly limit is usefulness.  We use a @(see bind-free)
hypothesis to strategically bind @('old') to a good candidate; see below.</p>

<p>The following theorem states that for any element other than number 4,
@('update-4th') of an object preserves that element:</p>
@({
 (implies (not (equal (nfix n) 4))
          (equal (nth n (update-4th val x))
                 (nth n x)))
 })

<p>These two rules can be used with the bind-free strategy below to prove:</p>
 @({
  (equal (access-3rd (update-4th val x)) (access-3rd x))
  })

<h4>Example 2</h4>
<p>The following theorem states that as long as the first @('k') elements of
field 2 of two objects are equal, the non-primitive accessor @('sum-range-of-field2') of the two
objects is preserved:</p>
@({
  (implies (range-equal 0 k (nth 2 new) (nth 2 old))
           (equal (sum-range-of-field2 k new)
                  (sum-range-of-field2 k old)))
 })

<p>The following theorem states that the non-primitive updater @('clear-field2-from') only
affects elements k and above of field 2:</p>
@({
 (implies (< (nfix i) (nfix k))
          (equal (nth i (nth 2 (clear-field2-from k x)))
                 (nth i (nth 2 x))))
 })

<p>Given an appropriate reasoning strategy about @('range-equal') and the
bind-free strategy below, these two rules are sufficient to prove:</p>
 @({
 (implies (<= (nfix j) (nfix k))
          (equal (sum-range-of-field2 j (clear-field2-from k x))
                 (sum-range-of-field2 j x)))
 })

<h3>Free Variable Binding Strategy</h3>

<p>Accessor theorems of the form above contain a free variable @('old').  Our
approaches use two strategies to bind this variable:</p>

<ul>

<li>When trying to prove another such accessor rule, we bind @('old') to
@('old') whenever @('new') is bound to @('new') (and do not apply the rule
otherwise).  This strategy is effective as long as all such accessor rules are
phrased in terms of the same two variables.</li>

<li>In other contexts, we only apply the rule when @('new') is a function call.
In that case, we use the @('prev-stobj-binding') utility to bind @('old') to
one of the actuals of that function call, depending on the formals and
stobjs-out of the function in question.  For example, suppose @('foo') takes
formals @('(x val st$)') and has stobjs-out @('(nil st$)').  That is,
it (perhaps) modifies @('st$') and returns it as its second value.  Then if
@('new') is bound to @('(mv-nth 1 (foo k q bar))'), we will find @('(nth 1
stobjs-out) = st$'), find that @('st$') is the 3rd formal, and thus bind the
third actual, @('bar'), to @('old').</li>

</ul>")

(defun bind-updater-independence-prev-stobj (arg mfc state)
  (declare (xargs :stobjs state :mode :program))
  (if (eq arg 'new)
      '((old . old))
    (acl2::prev-stobj-binding arg 'old mfc state)))

(defmacro bind-stobj-updater-returnval (arg)
  `(and (syntaxp (or (consp ,arg) (eq ,arg 'new)))
        (bind-free (bind-updater-independence-prev-stobj ,arg mfc state))))

;; (def-ruleset! special-updater-independence-thms nil)

(defmacro def-updater-independence-thm (name body &rest args)
  ;; (b* ((special-name (intern-in-package-of-symbol
  ;;                     (concatenate 'string (symbol-name name) "-SPECIAL")
  ;;                     name)))
  `(defthm ,name
     (implies (bind-stobj-updater-returnval new)
              ,body)
     . ,args))

(defxdoc def-updater-independence-thm
  :parents (stobj-updater-independence)
  :short "Prove an updater independence theorem, as discussed in @(see stobj-updater-independence)."
  :long "<p>This just adds the appropriate @('bind-free') form to your theorem,
which should use the variables @('new') and @('old') (from the ACL2 package).  For example:</p>
@({
 (def-updater-independence-thm access-3rd-updater-independence
   (implies (equal (nth 3 new) (nth 3 old))
            (equal (access-3rd new) (access-3rd old)))
   :hints((\"Goal\" :in-theory (enable access-3rd))))
 })
<p>Note @('new') should appear in the LHS and @('old') should not.</p>")


;; Range-equal and range-equal-badguy provide an effective way to reason about
;; accessors that are preserved by updates outside of a particular range of
;; indices.  NTH-WHEN-RANGE-EQUAL should be enabled to make them useful.

(define range-equal ((start natp) (num natp) (x true-listp) (y true-listp))
  :measure (nfix num)
  :parents (stobj-updater-independence)
  :short "Check that a range of entries from two lists are equal."
  :long "<p>This is useful for stobj updater independence theorems, e.g.,</p>
@({
 (def-stobj-updater-independence sum-range-of-field2-updater-independence
   (implies (range-equal 0 k (nth 2 new) (nth 2 old))
            (equal (sum-range-of-field2 k new)
                   (sum-range-of-field2 k old))))
 })

<p>Also see @('range-nat-equiv'), which is similar but checks @('nat-equiv') of
corresponding elements instead of @('equal').</p>
"
  (if (zp num)
      t
    (and (equal (nth start x) (nth start y))
         (range-equal (1+ (lnfix start)) (1- num) x y)))
  ///
  (defthmd range-equal-open
    (implies (not (zp num))
             (equal (range-equal start num x y)
                    (and (equal (nth start x) (nth start y))
                         (range-equal (1+ (lnfix start)) (1- num) x y)))))

  (local (defthm nth-of-list-fix
           (equal (nth n (acl2::list-fix x))
                  (nth n x))
           :hints(("Goal" :in-theory (enable nth acl2::list-fix)))))

  (fty::deffixequiv range-equal)

  ;; (local (defthm range-equal-when-greater-num-lemma
  ;;          (implies (range-equal start (+ (nfix num2) (nfix n)) x y)
  ;;                   (range-equal start num2 x y))
  ;;          :rule-classes nil))

  ;; (defthm range-equal-when-greater-num
  ;;   (implies (and (range-equal start num x y)
  ;;                 (syntaxp (not (equal num num2)))
  ;;                 (<= (nfix num2) (nfix num)))
  ;;            (range-equal start num2 x y))
  ;;   :hints (("goal" :use ((:instance range-equal-when-greater-num-lemma
  ;;                          (num2 num2) (n (- (nfix num) (nfix num2))))))))

  ;; (defthm range-equal-when-superrange
  ;;   (implies (and (range-equal start num x y)
  ;;                 (syntaxp (not (and (equal start start2)
  ;;                                    (equal num num2))))
  ;;                 (<= (nfix start) (nfix start2))
  ;;                 (<= (+ (nfix num2) (nfix start2)) (+ (nfix num) (nfix start))))
  ;;            (range-equal start2 num2 x y))
  ;;   :hints (("goal" :induct (range-equal start num x y)
  ;;            :in-theory (enable* acl2::arith-equiv-forwarding))
  ;;           (and stable-under-simplificationp
  ;;                '(:expand ((range-equal start num2 x y))))))

  (defthmd nth-when-range-equal
    (implies (and (range-equal start num x y)
                  (<= (nfix start) (nfix n))
                  (< (nfix n) (+ (nfix start) (nfix num))))
             (equal (nth n x) (nth n y)))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defthm range-equal-self
    (range-equal start num x x))


  (defthm range-equal-of-update-out-of-range-1
    (implies (not (and (<= (nfix start) (nfix n))
                       (< (nfix n) (+ (nfix start) (nfix num)))))
             (equal (range-equal start num (update-nth n v x) y)
                    (range-equal start num x y))))

  (defthm range-equal-of-update-out-of-range-2
    (implies (not (and (<= (nfix start) (nfix n))
                       (< (nfix n) (+ (nfix start) (nfix num)))))
             (equal (range-equal start num x (update-nth n v y))
                    (range-equal start num x y))))

  (defthm range-equal-of-empty
    (range-equal start 0 x y)))


(define range-equal-badguy ((start natp) (num natp) (x true-listp) (y true-listp))
  :measure (nfix num)
  :returns (badguy natp :rule-classes :type-prescription)
  (if (or (zp num) (eql num 1))
      (nfix start)
    (if (equal (nth start x) (nth start y))
        (range-equal-badguy (1+ (lnfix start)) (1- num) x y)
      (nfix start)))
  ///
  (local (in-theory (enable range-equal)))
  (defret range-equal-badguy-lower-bound
    (<= (nfix start) badguy)
    :rule-classes :linear)

  (defret range-equal-badguy-lower-bound-rewrite
    (implies (<= start1 (nfix start))
             (<= start1 badguy)))

  (defret range-equal-badguy-lower-bound-not-equal
    (implies (< start1 (nfix start))
             (not (equal start1 badguy))))

  (defret range-equal-badguy-upper-bound
    (implies (posp num)
             (< badguy (+ (nfix start) (nfix num))))
    :rule-classes :linear)

  (defret range-equal-badguy-upper-bound-when-not-equal
    (implies (not (range-equal start num x y))
             (< badguy (+ (nfix start) (nfix num))))
    :rule-classes ((:linear :backchain-limit-lst 0)))

  (defret range-equal-badguy-upper-bound-when-not-equal-rewrite
    (implies (and (not (range-equal start num x y))
                  (<= (+ (nfix start) (nfix num)) foo))
             (< badguy foo))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defret range-equal-badguy-not-equal-past-upper-bound
    (implies (and (not (range-equal start num x y))
                  (<= (+ (nfix start) (nfix num)) foo))
             (not (equal badguy foo)))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defret range-equal-by-badguy
    (implies (equal (nth badguy x) (nth badguy y))
             (range-equal start num x y)))

  (defret range-equal-by-badguy-literal
    (implies (acl2::rewriting-positive-literal `(range-equal ,start ,num ,x ,y))
             (iff (range-equal start num x y)
                  (or (zp num) ;; (not (< badguy (+ (nfix start) (nfix num)))) ;; 
                      (equal (nth badguy x) (nth badguy y))))))

  (defthm range-equal-by-superrange
    (implies (and (range-equal min1 max1 x y)
                  (<= (nfix min1) (nfix min))
                  (<= (+ (nfix min) (nfix max))
                      (+ (nfix min1) (nfix max1))))
             (range-equal min max x y))
    :hints(("Goal" :in-theory (e/d (nth-when-range-equal)
                                   (range-equal-open))))))



(defthm range-equal-when-range-equal
  ;; Note!  This rule may look nonsensical but it can allow the rule
  ;; range-equal-badguy-upper-bound-when-not-equal, below, to fire when it otherwise couldn't.
  ;; An example below shows how this can happen.
  
  ;; To prove sum-range-of-update we want to apply trigger-range-equal,
  ;; and to prove that we need to relieve its hyp
  ;;    (range-equal (+ (nfix n) (nfix start)) num x y)
  ;; which when applied in this example becomes:
  ;;    (range-equal (+ (nfix 12) (nfix 5)) n (update-nth (+ 17 (nfix n)) 4 x) x)
  ;; When trying to relieve this hyp we first reduce the first argument to 17,
  ;; then try to prove range-equal using range-equal-by-badguy.
  ;; In the course of relieving its hyp
  ;;    (equal (nth badguy x) (nth badguy y))
  ;; (where badguy = (range-equal-badguy 17 n ...)
  ;; we need to show that badguy != (+ 17 (nfix n)).  So we try to apply
  ;; range-equal-badguy-not-equal-past-upper-bound, and thus have to relieve the hyp
  ;; (not (range-equal c num x y)) -- which is the negation of what we are
  ;; actually trying to prove.  So we should just be able to assume that.  But
  ;; ACL2's mechanism for assuming a hyp you're already trying to relieve
  ;; is the ancestor stack, and the relevant term
  ;; that is actually on the ancestor stack is not (range-equal 17 n ...)
  ;; but rather the original (range-equal (+ (nfix 12) (nfix 5)) n ...)

  ;; This rule solves that problem by triggering on the original hyp we are
  ;; trying to relive, effectively inserting the normalized form of the
  ;; range-equal hyp into the ancestor stack.

  ;; The rewrite failure cache can mess this up if this rule triggers after we
  ;; already try range-equal-by-badguy, so we situate this rule after that so
  ;; that it will be tried first.

  ;; One additional tweak we considered was to add a hyp
  ;;  (not (range-equal start num x y))

  ;; to range-equal-by-badguy, with backchain-limit 0.  That would have the
  ;; effect of preventing range-equal-by-badguy from being attempted when the
  ;; appropriate range-equal term was not in the ancestors stack.  Effectively,
  ;; we think that if range-equal-when-range-equal is tried first and the
  ;; application of range-equal-by-badguy fails, this would prevent trying the
  ;; same range-equal-by-badguy application again when it is even less likely
  ;; to work, because the appropriate ancestor isn't in the stack.  But we
  ;; don't think this is necessary because the rewrite failure cache will
  ;; presumably cause it to fail anyway.

  ;; An alternative to using this rule is to ensure that all range-equal hyps
  ;; only use variables as arguments.
  (implies (range-equal start num x y)
           (range-equal start num x y)))


(define range-equal-min-max ((min natp) (max natp) (x true-listp) (y true-listp))
  :guard (<= min max)
  (range-equal min (+ 1 (- (lnfix max) (lnfix min))) x y)
  ///
  (fty::deffixequiv range-equal-min-max)
  (local (defthm range-equal-when-zp
           (implies (zp num)
                    (range-equal start num x y))
           :hints(("Goal" :in-theory (enable range-equal)))))

  (defthm range-equal-min-max-when-superrange
    (implies (and (range-equal-min-max min1 max1 x y)
                  (<= (nfix min1) (nfix min))
                  (<= (nfix max) (nfix max1)))
             (range-equal-min-max min max x y))
    :hints(("Goal" :in-theory (disable range-equal-by-badguy-literal)
            :cases ((<= (nfix min) (nfix max))))))
  
  (defthmd nth-when-range-equal-min-max
    (implies (and (range-equal-min-max min max x y)
                  (<= (nfix min) (nfix n))
                  (<= (nfix n) (nfix max)))
             (equal (nth n x) (nth n y)))
    :hints(("Goal" :in-theory (enable nth-when-range-equal))))

  (defthm range-equal-min-max-self
    (range-equal-min-max min max x x))

  (defthm range-equal-min-max-of-update-out-of-range-1
    (implies (not (and (<= (nfix min) (nfix n))
                       (<= (nfix n) (nfix max))))
             (equal (range-equal-min-max min max (update-nth n v x) y)
                    (range-equal-min-max min max x y)))
    :hints(("Goal" :in-theory (disable range-equal-by-badguy-literal)
            :cases ((<= (nfix min) (nfix max))))))

  (defthm range-equal-min-max-of-update-out-of-range-2
    (implies (not (and (<= (nfix min) (nfix n))
                       (<= (nfix n) (nfix max))))
             (equal (range-equal-min-max min max x (update-nth n v y))
                    (range-equal-min-max min max x y)))
    :hints(("Goal" :in-theory (disable range-equal-by-badguy-literal)
            :cases ((<= (nfix min) (nfix max)))))))

(define range-equal-min-max-badguy ((min natp) (max natp) (x true-listp) (y true-listp))
  :guard (<= min max)
  :returns (badguy natp :rule-classes :type-prescription)
  (range-equal-badguy min (+ 1 (- (lnfix max) (lnfix min))) x y)
  ///
  (local (in-theory (enable range-equal-min-max)))

  (defret range-equal-min-max-badguy-lower-bound
    (<= (nfix min) badguy)
    :rule-classes :linear)

  (defret range-equal-min-max-badguy-lower-bound-rewrite
    (implies (<= min1 (nfix min))
             (<= min1 badguy)))

  (defret range-equal-min-max-badguy-lower-bound-not-equal
    (implies (< min1 (nfix min))
             (not (equal min1 badguy))))

  (defret range-equal-min-max-badguy-upper-bound
    (implies (<= (nfix min) (nfix max))
             (<= badguy (nfix max)))
    :rule-classes :linear)

  (defret range-equal-min-max-badguy-upper-bound-when-not-equal
    (implies (not (range-equal-min-max min max x y))
             (<= badguy (nfix max)))
    :rule-classes ((:linear :backchain-limit-lst 0)))

  (defret range-equal-min-max-badguy-upper-bound-when-not-equal-rewrite-lte
    (implies (and (not (range-equal-min-max min max x y))
                  (<= (nfix max) max1))
             (<= badguy max1))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defret range-equal-min-max-badguy-upper-bound-when-not-equal-rewrite-less
    (implies (and (not (range-equal-min-max min max x y))
                  (< (nfix max) max1))
             (< badguy max1))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defret range-equal-min-max-badguy-not-equal-past-upper-bound
    (implies (and (not (range-equal-min-max min max x y))
                  (< (nfix max) max1))
             (not (equal badguy max1)))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defret range-equal-min-max-by-badguy
    (implies (equal (nth badguy x) (nth badguy y))
             (range-equal-min-max min max x y)))
    
  (defret range-equal-min-max-by-badguy-literal
    (implies (acl2::rewriting-positive-literal `(range-equal-min-max ,min ,max ,x ,y))
             (iff (range-equal-min-max min max x y)
                  (or (< (nfix max) (nfix min)) ;; (< (nfix max) badguy)
                      (equal (nth badguy x) (nth badguy y)))))
    :hints(("Goal" :in-theory (enable nth-when-range-equal)))))

(defthm range-equal-min-max-when-range-equal-min-max
  ;; See comment about range-equal-when-range-equal.
    (implies (range-equal-min-max min max x y)
             (range-equal-min-max min max x y)))

  
                    

;; ;; We disable this rule because it provides a shortcut to proving
;; ;; sum-range-of-update that we don't want to take for this illustration.
;; (in-theory (disable range-equal-of-update-out-of-range-1))

;; (defun sum-range (start num x)
;;   (if (zp num)
;;       0
;;     (+ (nth start x)
;;        (sum-range (+ 1 (lnfix start)) (+ -1 num) x))))

;; (local (defthm nth-of-nthcdr
;;          (equal (nth n (nthcdr m x))
;;                 (nth (+ (nfix n) (nfix m)) x))))

;; (defthm trigger-range-equal
;;   (implies (range-equal (+ (nfix n) (nfix start)) num x y)
;;            (equal (equal (sum-range start num (nthcdr n x))
;;                          (sum-range start num (nthcdr n y)))
;;                   t))
;;   :hints(("Goal" :in-theory (e/d (range-equal)
;;                                  (range-equal-by-badguy-literal)))))

;; ;; This rule proves when range-equal-when-range-equal is enabled, but not if disabled
;; ;; (unless range-equal-of-update-out-of-range-1 is enabled.)

;; (defthm sum-range-of-update
;;   (equal (sum-range 5 n (nthcdr 12 (update-nth (+ 17 (nfix n)) 4 x)))
;;          (sum-range 5 n (nthcdr 12 x)))
;;   :hints(("Goal" :in-theory (disable sum-range))))





;; Same as range-equal/range-equal-badguy but compares corresponding elements
;; with nat-equiv.
(define range-nat-equiv ((start natp) (num natp) (x true-listp) (y true-listp))
  :measure (nfix num)
  (if (zp num)
      t
    (and (ec-call (nat-equiv (nth start x) (nth start y)))
         (range-nat-equiv (1+ (lnfix start)) (1- num) x y)))
  ///
  (defthmd range-nat-equiv-open
    (implies (not (zp num))
             (equal (range-nat-equiv start num x y)
                    (and (nat-equiv (nth start x) (nth start y))
                         (range-nat-equiv (1+ (lnfix start)) (1- num) x y)))))

  (local (defthm nth-of-list-fix
           (equal (nth n (acl2::list-fix x))
                  (nth n x))
           :hints(("Goal" :in-theory (enable nth acl2::list-fix)))))

  (fty::deffixequiv range-nat-equiv)

  ;; (local (defthm range-nat-equiv-when-greater-num-lemma
  ;;          (implies (range-nat-equiv start (+ (nfix num2) (nfix n)) x y)
  ;;                   (range-nat-equiv start num2 x y))
  ;;          :rule-classes nil))

  ;; (defthm range-nat-equiv-when-greater-num
  ;;   (implies (and (range-nat-equiv start num x y)
  ;;                 (syntaxp (not (equal num num2)))
  ;;                 (<= (nfix num2) (nfix num)))
  ;;            (range-nat-equiv start num2 x y))
  ;;   :hints (("goal" :use ((:instance range-nat-equiv-when-greater-num-lemma
  ;;                          (num2 num2) (n (- (nfix num) (nfix num2))))))))

  ;; (defthm range-nat-equiv-when-superrange
  ;;   (implies (and (range-nat-equiv start num x y)
  ;;                 (syntaxp (not (and (equal start start2)
  ;;                                    (equal num num2))))
  ;;                 (<= (nfix start) (nfix start2))
  ;;                 (<= (+ (nfix num2) (nfix start2)) (+ (nfix num) (nfix start))))
  ;;            (range-nat-equiv start2 num2 x y))
  ;;   :hints (("goal" :induct (range-nat-equiv start num x y)
  ;;            :in-theory (enable* acl2::arith-equiv-forwarding))
  ;;           (and stable-under-simplificationp
  ;;                '(:expand ((range-nat-equiv start num2 x y))))))

  (defthmd nth-when-range-nat-equiv
    (implies (and (range-nat-equiv start num x y)
                  (<= (nfix start) (nfix n))
                  (< (nfix n) (+ (nfix start) (nfix num))))
             (nat-equiv (nth n x) (nth n y)))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defthm range-nat-equiv-self
    (range-nat-equiv start num x x))


  (defthm range-nat-equiv-of-update-out-of-range-1
    (implies (not (and (<= (nfix start) (nfix n))
                       (< (nfix n) (+ (nfix start) (nfix num)))))
             (equal (range-nat-equiv start num (update-nth n v x) y)
                    (range-nat-equiv start num x y))))

  (defthm range-nat-equiv-of-update-out-of-range-2
    (implies (not (and (<= (nfix start) (nfix n))
                       (< (nfix n) (+ (nfix start) (nfix num)))))
             (equal (range-nat-equiv start num x (update-nth n v y))
                    (range-nat-equiv start num x y))))

  (defthm range-nat-equiv-of-empty
    (range-nat-equiv start 0 x y)))


(define range-nat-equiv-badguy ((start natp) (num natp) (x true-listp) (y true-listp))
  :measure (nfix num)
  :returns (badguy natp :rule-classes :type-prescription)
  (if (or (zp num) (eql num 1))
      (nfix start)
    (if (ec-call (nat-equiv (nth start x) (nth start y)))
        (range-nat-equiv-badguy (1+ (lnfix start)) (1- num) x y)
      (nfix start)))
  ///
  (local (in-theory (enable range-nat-equiv)))
  (defret range-nat-equiv-badguy-lower-bound
    (<= (nfix start) badguy)
    :rule-classes :linear)

  (defret range-nat-equiv-badguy-lower-bound-rewrite
    (implies (<= start1 (nfix start))
             (<= start1 badguy)))

  (defret range-nat-equiv-badguy-lower-bound-not-equal
    (implies (< start1 (nfix start))
             (not (equal start1 badguy))))

  (defret range-nat-equiv-badguy-upper-bound
    (implies (posp num)
             (< badguy (+ (nfix start) (nfix num))))
    :rule-classes :linear)

  (defret range-nat-equiv-badguy-upper-bound-when-not-equal
    (implies (not (range-nat-equiv start num x y))
             (< badguy (+ (nfix start) (nfix num))))
    :rule-classes ((:linear :backchain-limit-lst 0)))

  (defret range-nat-equiv-badguy-upper-bound-when-not-equal-rewrite
    (implies (and (not (range-nat-equiv start num x y))
                  (<= (+ (nfix start) (nfix num)) foo))
             (< badguy foo))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defret range-nat-equiv-badguy-not-equal-past-upper-bound
    (implies (and (not (range-nat-equiv start num x y))
                  (<= (+ (nfix start) (nfix num)) foo))
             (not (equal badguy foo)))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defret range-nat-equiv-by-badguy
    (implies (nat-equiv (nth badguy x) (nth badguy y))
             (range-nat-equiv start num x y)))

  (defret range-nat-equiv-by-badguy-literal
    (implies (acl2::rewriting-positive-literal `(range-nat-equiv ,start ,num ,x ,y))
             (iff (range-nat-equiv start num x y)
                  (or (zp num) ;; (not (< badguy (+ (nfix start) (nfix num)))) ;; 
                      (nat-equiv (nth badguy x) (nth badguy y))))))

  (defthm range-nat-equiv-by-superrange
    (implies (and (range-nat-equiv min1 max1 x y)
                  (<= (nfix min1) (nfix min))
                  (<= (+ (nfix min) (nfix max))
                      (+ (nfix min1) (nfix max1))))
             (range-nat-equiv min max x y))
    :hints(("Goal" :in-theory (e/d (nth-when-range-nat-equiv)
                                   (range-nat-equiv-open))))))



(defthm range-nat-equiv-when-range-nat-equiv
  (implies (range-nat-equiv start num x y)
           (range-nat-equiv start num x y)))


(define range-nat-equiv-min-max ((min natp) (max natp) (x true-listp) (y true-listp))
  :guard (<= min max)
  (range-nat-equiv min (+ 1 (- (lnfix max) (lnfix min))) x y)
  ///
  (fty::deffixequiv range-nat-equiv-min-max)
  (local (defthm range-nat-equiv-when-zp
           (implies (zp num)
                    (range-nat-equiv start num x y))
           :hints(("Goal" :in-theory (enable range-nat-equiv)))))

  (defthm range-nat-equiv-min-max-when-superrange
    (implies (and (range-nat-equiv-min-max min1 max1 x y)
                  (<= (nfix min1) (nfix min))
                  (<= (nfix max) (nfix max1)))
             (range-nat-equiv-min-max min max x y))
    :hints(("Goal" :in-theory (disable range-nat-equiv-by-badguy-literal)
            :cases ((<= (nfix min) (nfix max))))))
  
  (defthmd nth-when-range-nat-equiv-min-max
    (implies (and (range-nat-equiv-min-max min max x y)
                  (<= (nfix min) (nfix n))
                  (<= (nfix n) (nfix max)))
             (nat-equiv (nth n x) (nth n y)))
    :hints(("Goal" :in-theory (enable nth-when-range-nat-equiv))))

  (defthm range-nat-equiv-min-max-self
    (range-nat-equiv-min-max min max x x))

  (defthm range-nat-equiv-min-max-of-update-out-of-range-1
    (implies (not (and (<= (nfix min) (nfix n))
                       (<= (nfix n) (nfix max))))
             (equal (range-nat-equiv-min-max min max (update-nth n v x) y)
                    (range-nat-equiv-min-max min max x y)))
    :hints(("Goal" :in-theory (disable range-nat-equiv-by-badguy-literal)
            :cases ((<= (nfix min) (nfix max))))))

  (defthm range-nat-equiv-min-max-of-update-out-of-range-2
    (implies (not (and (<= (nfix min) (nfix n))
                       (<= (nfix n) (nfix max))))
             (equal (range-nat-equiv-min-max min max x (update-nth n v y))
                    (range-nat-equiv-min-max min max x y)))
    :hints(("Goal" :in-theory (disable range-nat-equiv-by-badguy-literal)
            :cases ((<= (nfix min) (nfix max)))))))

(define range-nat-equiv-min-max-badguy ((min natp) (max natp) (x true-listp) (y true-listp))
  :guard (<= min max)
  :returns (badguy natp :rule-classes :type-prescription)
  (range-nat-equiv-badguy min (+ 1 (- (lnfix max) (lnfix min))) x y)
  ///
  (local (in-theory (enable range-nat-equiv-min-max)))

  (defret range-nat-equiv-min-max-badguy-lower-bound
    (<= (nfix min) badguy)
    :rule-classes :linear)

  (defret range-nat-equiv-min-max-badguy-lower-bound-rewrite
    (implies (<= min1 (nfix min))
             (<= min1 badguy)))

  (defret range-nat-equiv-min-max-badguy-lower-bound-not-equal
    (implies (< min1 (nfix min))
             (not (equal min1 badguy))))

  (defret range-nat-equiv-min-max-badguy-upper-bound
    (implies (<= (nfix min) (nfix max))
             (<= badguy (nfix max)))
    :rule-classes :linear)

  (defret range-nat-equiv-min-max-badguy-upper-bound-when-not-equal
    (implies (not (range-nat-equiv-min-max min max x y))
             (<= badguy (nfix max)))
    :rule-classes ((:linear :backchain-limit-lst 0)))

  (defret range-nat-equiv-min-max-badguy-upper-bound-when-not-equal-rewrite-lte
    (implies (and (not (range-nat-equiv-min-max min max x y))
                  (<= (nfix max) max1))
             (<= badguy max1))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defret range-nat-equiv-min-max-badguy-upper-bound-when-not-equal-rewrite-less
    (implies (and (not (range-nat-equiv-min-max min max x y))
                  (< (nfix max) max1))
             (< badguy max1))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defret range-nat-equiv-min-max-badguy-not-equal-past-upper-bound
    (implies (and (not (range-nat-equiv-min-max min max x y))
                  (< (nfix max) max1))
             (not (equal badguy max1)))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defret range-nat-equiv-min-max-by-badguy
    (implies (nat-equiv (nth badguy x) (nth badguy y))
             (range-nat-equiv-min-max min max x y)))
    
  (defret range-nat-equiv-min-max-by-badguy-literal
    (implies (acl2::rewriting-positive-literal `(range-nat-equiv-min-max ,min ,max ,x ,y))
             (iff (range-nat-equiv-min-max min max x y)
                  (or (< (nfix max) (nfix min)) ;; (< (nfix max) badguy)
                      (nat-equiv (nth badguy x) (nth badguy y)))))
    :hints(("Goal" :in-theory (enable nth-when-range-nat-equiv)))))

(defthm range-nat-equiv-min-max-when-range-nat-equiv-min-max
  ;; See comment about range-nat-equiv-when-range-nat-equiv.
    (implies (range-nat-equiv-min-max min max x y)
             (range-nat-equiv-min-max min max x y)))








(defconst *def-range-equiv-template*
  '(encapsulate nil
     (local (include-book "std/basic/arith-equivs" :dir :system))
     (local (fty::deffixcong <idx-equiv> equal (<nth> n x) n :thm-suffix "-<NAME>-<IDX-EQUIV>-FOR-RANGE-EQUIV"))
     ;; Same as range-equal/range-equal-badguy but compares corresponding elements
     ;; with <equiv>.
     (define <name> ((start <idxtype>) (num natp) x y)
       :measure (nfix num)
       :verify-guards nil
       (if (zp num)
           t
         (and (<equiv> (<nth> start x) (<nth> start y))
              (<name> (1+ (<lidxfix> start)) (1- num) x y)))
       ///
       (defthmd <name>-open
         (implies (not (zp num))
                  (equal (<name> start num x y)
                         (and (<equiv> (<nth> start x) (<nth> start y))
                              (<name> (1+ (<lidxfix> start)) (1- num) x y)))))

       (fty::deffixequiv <name>)

       (local (defthm <name>-when-greater-num-lemma
                (implies (<name> start (+ (nfix num2) (nfix n)) x y)
                         (<name> start num2 x y))
                :rule-classes nil))

       (defthm <name>-when-greater-num
         (implies (and (<name> start num x y)
                       (syntaxp (not (equal num num2)))
                       (<= (nfix num2) (nfix num)))
                  (<name> start num2 x y))
         :hints (("goal" :use ((:instance <name>-when-greater-num-lemma
                                (num2 num2) (n (- (nfix num) (nfix num2))))))))

       (defthm <name>-when-superrange
         (implies (and (<name> start num x y)
                       (syntaxp (not (and (equal start start2)
                                          (equal num num2))))
                       (<= (<idxfix> start) (<idxfix> start2))
                       (<= (+ (nfix num2) (<idxfix> start2)) (+ (nfix num) (<idxfix> start))))
                  (<name> start2 num2 x y))
         :hints (("goal" :induct (<name> start num x y)
                  :in-theory (enable* acl2::arith-equiv-forwarding))
                 (and stable-under-simplificationp
                      '(:expand ((<name> start num2 x y))))))

       (defthmd <nth>-when-<name>
         (implies (and (<name> start num x y)
                       (<= (<idxfix> start) (<idxfix> n))
                       (< (<idxfix> n) (+ (<idxfix> start) (nfix num))))
                  (<equiv> (<nth> n x) (<nth> n y)))
         :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

       (defthm <name>-self
         (<name> start num x x))


       (defthm <name>-of-update-out-of-range-1
         (implies (not (and (<= (<idxfix> start) (<idxfix> n))
                            (< (<idxfix> n) (+ (<idxfix> start) (nfix num)))))
                  (equal (<name> start num (<update> n v x) y)
                         (<name> start num x y))))

       (defthm <name>-of-update-out-of-range-2
         (implies (not (and (<= (<idxfix> start) (<idxfix> n))
                            (< (<idxfix> n) (+ (<idxfix> start) (nfix num)))))
                  (equal (<name> start num x (<update> n v y))
                         (<name> start num x y))))

       (defthm <name>-of-empty
         (<name> start 0 x y)))


     (define <name>-badguy ((start <idxtype>) (num natp) x y)
       :measure (nfix num)
       :verify-guards nil
       :returns (badguy <idxtype> :rule-classes :type-prescription)
       (if (or (zp num) (eql num 1))
           (<lidxfix> start)
         (if (<equiv> (<nth> start x) (<nth> start y))
             (<name>-badguy (1+ (<lidxfix> start)) (1- num) x y)
           (<idxfix> start)))
       ///
       (local (in-theory (enable <name>)))
       (defret <name>-badguy-lower-bound
         (<= (<idxfix> start) badguy)
         :rule-classes :linear)

       (defret <name>-badguy-lower-bound-rewrite
         (implies (<= start1 (<idxfix> start))
                  (<= start1 badguy)))

       (defret <name>-badguy-lower-bound-not-equal
         (implies (< start1 (<idxfix> start))
                  (not (equal start1 badguy))))

       (defret <name>-badguy-upper-bound
         (implies (posp num)
                  (< badguy (+ (<idxfix> start) (nfix num))))
         :rule-classes :linear)

       (defret <name>-badguy-upper-bound-when-not-equal
         (implies (not (<name> start num x y))
                  (< badguy (+ (<idxfix> start) (nfix num))))
         :rule-classes ((:linear :backchain-limit-lst 0)))

       (defret <name>-badguy-upper-bound-when-not-equal-rewrite
         (implies (and (not (<name> start num x y))
                       (<= (+ (<idxfix> start) (nfix num)) foo))
                  (< badguy foo))
         :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

       (defret <name>-badguy-not-equal-past-upper-bound
         (implies (and (not (<name> start num x y))
                       (<= (+ (<idxfix> start) (nfix num)) foo))
                  (not (equal badguy foo)))
         :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

       (defret <name>-by-badguy
         (implies (<equiv> (<nth> badguy x) (<nth> badguy y))
                  (<name> start num x y)))

       (defret <name>-by-badguy-literal
         (implies (acl2::rewriting-positive-literal `(<name> ,start ,num ,x ,y))
                  (iff (<name> start num x y)
                       (or (not (< badguy (+ (<idxfix> start) (nfix num))))
                           (<equiv> (<nth> badguy x) (<nth> badguy y))))))

       (defthm <name>-by-superrange
         (implies (and (<name> min1 max1 x y)
                       (<= (<idxfix> min1) (<idxfix> min))
                       (<= (+ (<idxfix> min) (nfix max))
                           (+ (<idxfix> min1) (nfix max1))))
                  (<name> min max x y))
         :hints(("Goal" :in-theory (e/d (<nth>-when-<name>)
                                        (<name>-open))))))



     (defthm <name>-when-<name>
       (implies (<name> start num x y)
                (<name> start num x y)))

     (define <name>-min-max ((min <idxtype>) (max <idxtype>) x y)
       :guard (<= min max)
       :verify-guards nil
       (<name> min (+ 1 (- (<lidxfix> max) (<lidxfix> min))) x y)
       ///
       (fty::deffixequiv <name>-min-max)
       (local (defthm <name>-when-zp
                (implies (zp num)
                         (<name> start num x y))
                :hints(("Goal" :in-theory (enable <name>)))))

       (defthm <name>-min-max-when-superrange
         (implies (and (<name>-min-max min1 max1 x y)
                       (<= (<idxfix> min1) (<idxfix> min))
                       (<= (<idxfix> max) (<idxfix> max1)))
                  (<name>-min-max min max x y))
         :hints(("Goal" :in-theory (disable <name>-by-badguy-literal)
                 :cases ((<= (<idxfix> min) (<idxfix> max))))))
       
       (defthmd <nth>-when-<name>-min-max
         (implies (and (<name>-min-max min max x y)
                       (<= (<idxfix> min) (<idxfix> n))
                       (<= (<idxfix> n) (<idxfix> max)))
                  (<equiv> (<nth> n x) (<nth> n y)))
         :hints(("Goal" :in-theory (enable <nth>-when-<name>))))

       (defthm <name>-min-max-self
         (<name>-min-max min max x x))

       (defthm <name>-min-max-of-update-out-of-range-1
         (implies (not (and (<= (<idxfix> min) (<idxfix> n))
                            (<= (<idxfix> n) (<idxfix> max))))
                  (equal (<name>-min-max min max (<update> n v x) y)
                         (<name>-min-max min max x y)))
         :hints(("Goal" :in-theory (disable <name>-by-badguy-literal)
                 :cases ((<= (<idxfix> min) (<idxfix> max))))))

       (defthm <name>-min-max-of-update-out-of-range-2
         (implies (not (and (<= (<idxfix> min) (<idxfix> n))
                            (<= (<idxfix> n) (<idxfix> max))))
                  (equal (<name>-min-max min max x (<update> n v y))
                         (<name>-min-max min max x y)))
         :hints(("Goal" :in-theory (disable <name>-by-badguy-literal)
                 :cases ((<= (<idxfix> min) (<idxfix> max)))))))

     (define <name>-min-max-badguy ((min <idxtype>) (max <idxtype>) x y)
       :guard (<= min max)
       :verify-guards nil
       :returns (badguy <idxtype> :rule-classes :type-prescription)
       (<name>-badguy min (+ 1 (- (<lidxfix> max) (<lidxfix> min))) x y)
       ///
       (local (in-theory (enable <name>-min-max)))

       (defret <name>-min-max-badguy-lower-bound
         (<= (<idxfix> min) badguy)
         :rule-classes :linear)

       (defret <name>-min-max-badguy-lower-bound-rewrite
         (implies (<= min1 (<idxfix> min))
                  (<= min1 badguy)))

       (defret <name>-min-max-badguy-lower-bound-not-equal
         (implies (< min1 (<idxfix> min))
                  (not (equal min1 badguy))))

       (defret <name>-min-max-badguy-upper-bound
         (implies (<= (<idxfix> min) (<idxfix> max))
                  (<= badguy (<idxfix> max)))
         :rule-classes :linear)

       (defret <name>-min-max-badguy-upper-bound-when-not-equal
         (implies (not (<name>-min-max min max x y))
                  (<= badguy (<idxfix> max)))
         :rule-classes ((:linear :backchain-limit-lst 0)))

       (defret <name>-min-max-badguy-upper-bound-when-not-equal-rewrite-lte
         (implies (and (not (<name>-min-max min max x y))
                       (<= (<idxfix> max) max1))
                  (<= badguy max1))
         :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

       (defret <name>-min-max-badguy-upper-bound-when-not-equal-rewrite-less
         (implies (and (not (<name>-min-max min max x y))
                       (< (<idxfix> max) max1))
                  (< badguy max1))
         :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

       (defret <name>-min-max-badguy-not-equal-past-upper-bound
         (implies (and (not (<name>-min-max min max x y))
                       (< (<idxfix> max) max1))
                  (not (equal badguy max1)))
         :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

       (defret <name>-min-max-by-badguy
         (implies (<equiv> (<nth> badguy x) (<nth> badguy y))
                  (<name>-min-max min max x y)))
       
       (defret <name>-min-max-by-badguy-literal
         (implies (acl2::rewriting-positive-literal `(<name>-min-max ,min ,max ,x ,y))
                  (iff (<name>-min-max min max x y)
                       (or (< (<idxfix> max) (<idxfix> min)) ;; (< (nfix max) badguy)
                           (<equiv> (<nth> badguy x) (<nth> badguy y)))))
         :hints(("Goal" :in-theory (enable <nth>-when-<name>)))))

     (defthm <name>-min-max-when-<name>-min-max
       ;; See comment about <name>-when-<name>.
       (implies (<name>-min-max min max x y)
                (<name>-min-max min max x y)))))


(defun pair-symbol-names (x)
  (declare (xargs :mode :program))
  (if (atom x)
      nil
    (if (and (consp (car x))
             (symbolp (caar x))
             (symbolp (cdar x)))
        (cons (cons (symbol-name (caar x))
                    (symbol-name (cdar x)))
              (pair-symbol-names (cdr x)))
      (pair-symbol-names (cdr x)))))

(defmacro def-range-equiv (name &key (equiv 'equal)
                                (nth 'nth)
                                (update 'update-nth)
                                (pkg 'nil)
                                (index-type 'natp))
  (b* (((unless (member-eq index-type '(natp integerp)))
        (er hard? 'def-range-equiv "Index type must be natp or integerp"))
       ((mv idxtype idxfix lidxfix idx-equiv)
        (if (eq index-type 'natp)
            (mv 'natp 'nfix 'lnfix 'nat-equiv)
          (mv 'integerp 'ifix 'lifix 'int-equiv)))
       (atom-alist `((<name> . ,name)
                     (<nth> . ,nth)
                     (<update> . ,update)
                     (<equiv> . ,equiv)
                     (<idxtype> . ,idxtype)
                     (<idxfix> . ,idxfix)
                     (<lidxfix> . ,lidxfix)
                     (<idx-equiv> . ,idx-equiv)))
       (str-alist (pair-symbol-names atom-alist)))
    (acl2::template-subst
     *def-range-equiv-template*
     :atom-alist atom-alist
     :str-alist str-alist
     :string-str-alist str-alist
     :pkg-sym (or pkg name))))
                                
