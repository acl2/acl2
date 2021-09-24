; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "BITSETS")
(include-book "bits-between")
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/misc/equal-sets" :dir :system))
(local (include-book "std/lists/revappend" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

(local (in-theory (acl2::enable* set::definitions set::expensive-rules
                                 bitops::ash-1-removal)))

(defxdoc sbitsets
  :parents (std/bitsets)
  :short "Sparse bitsets library: an alternative to @(see bitsets) for
representing finite sets of natural numbers."

  :long "<h3>Introduction</h3>

<p>In the ordinary @(see bitsets) library, sets of natural numbers are encoded
as bignums.  This is perfectly fine when the set elements are relatively small,
but it is not an efficient way to deal with sets of large numbers.  For
instance, trying to insert a number like 2^30 into an ordinary bitset will
probably kill your Lisp.</p>

<p>Sparse bitsets are a more forgiving alternative.  They can handle very large
set elements, but still achieve bitset-like efficiencies in many cases.</p>

<p>Sparse bitsets are represented as ordered lists of @('(offset . block)')
pairs.  Loosely speaking, each such pair in the set @('X') means that:</p>

@({
  offset*blocksize + 0             \\in X  iff  (logbitp 0 block)
  offset*blocksize + 1             \\in X  iff  (logbitp 1 block)
    ...
  offset*blocksize + (blocksize-1) \\in X  iff  (logbitp (blocksize-1) block)
})

<p>The @('blocksize') is a some constant determined by @(see
*sbitset-block-size*).  We'll assume it is 60 (which makes each @('block') a
fixnum on 64-bit CCL).</p>

<h4>Efficiency Considerations</h4>

<p>Sparse bitsets are essentially a hybrid of ordered sets and bitsets, and
their efficiency characteristics are very data dependent.</p>

<p>Sparse bitsets perform best on sets that have \"clusters\" of nearby
members, perhaps separated by wide gaps.  Here, sparse bitsets give you some of
the same benefits of bitsets, viz. word-at-a-time operations like union and the
space efficiency of using bit masks to represent the set members.</p>

<p>For completely dense sets, e.g., all integers in @('[0, 1000]'), sparse
bitsets are:</p>

<ul>

<li>Better than ordered sets, because they get to compress nearby elements into
 bitmasks and use word-at-a-time operations.</li>

<li>Somewhat worse than ordinary bitsets.  They are less space efficient due to
 the conses and offset numbers.  They are also more expensive for membership
 testing: regular bitsets can basically use O(1) array indexing via @(see
 logbitp), while sparse bitsets must use an O(n) search for the right
 pair.</li>

</ul>

<p>For \"cluster-free\" sets where the elements are so far apart that they
never fall into the same block, sparse bitsets are:</p>

<ul>

<li>Better than bitsets, which perform badly here since they can have large
segments of 0 bits that waste space and take time to process during set
operations.</li>

<li>Somewhat worse than ordered sets.  For instance, a set like {0, 60, 120}
would be encoded as @('((0 . 1) (1 . 1) (2 . 1))'), which is similar to its
ordered set representation except for the additional overhead of using @('(1
. 1)') to represent 60, etc.</li>

</ul>


<h3>Sparse Bitset Operations</h3>

<p>Convention:</p>

<ul>
<li>@('a, b, ...') denote set elements</li>
<li>@('X, Y, ...') denote sets.</li>
</ul>

<p>Valid sparse bitsets are recognized by @(see sbitsetp), and there is a
standard fixing function, @(see sbitset-fix).</p>

<p>We intend to eventually implement sparse analogues for all of the functions
in the @(see bitsets) library, and analogues for the bitset @(see reasoning)
techniques.  For now we have only finished a few of these operations:</p>

<h5>Sparse Bitset Construtors</h5>

<dl>

<dt>@('(sbitset-singleton a)')</dt>
<dd>Constructs the set @('{a}')</dd>

<dt>@('(sbitset-union X Y ...)')</dt>
<dd>Constructs the set @('X U Y U ...')</dd>

<dt>@('(sbitset-intersect X Y ...)')</dt>
<dd>Constructs the set @('X \\intersect Y \\intersect ...')</dd>

<dt>@('(sbitset-difference X Y)')</dt>
<dd>Constructs the set @('X - Y')</dd>

</dl>

<h5>Inspecting Sparse Bitsets</h5>

<dl>
<dt>Todo</dt>
</dl>

<h5>Enumerating Sparse Bitset Members</h5>

<dl>
<dt>@('(sbitset-members X)')</dt>
<dd>Constructs an ordinary ordered set with the elements of X.</dd>
<dd>Important in @(see reasoning) about sparse bitsets.</dd>
</dl>")

(defsection *sbitset-block-size*
  :parents (sbitset-pairp)
  :short "Size of each block in an sparse bitset."

  :long "<p>The block size can be any positive number, but for good performance
you probably want to use the maximal number such that:</p>

@({
 (fixnump (1- (expt 2 *sbitset-block-size*))) = T
})

<p>On CCL and SBCL, 60 is the right number.  For other Lisps, 60 is logically
fine, but other numbers may give you better performance.</p>

<p>Note: if you change this, you may wish to also write a corresponding,
optimized version of @(see sbitset-pair-members).</p>"

  (defconst *sbitset-block-size* 60))

(local (defthm floor-is-nonnegative-integer-quotient
         (implies (and (natp a) (posp b))
                  (equal (floor a b)
                         (nonnegative-integer-quotient a b)))))

(local (in-theory (disable truncate)))

(local (defthm truncate-is-nonnegative-integer-quotient
         (implies (and (natp a) (posp b))
                  (equal (truncate a b)
                         (nonnegative-integer-quotient a b)))))


(local
 (encapsulate
   ()
   (local (defun niq-ind (a b c)
            (declare (xargs :measure (nonnegative-integer-quotient c a)))
            (if (or (= (nfix a) 0) (< (ifix c) a))
                b
              (niq-ind a (- b 1) (- c a)))))

   (defthm niq-lemma
     (implies (and (posp a)
                   (natp b)
                   (natp c))
              (equal (equal (nonnegative-integer-quotient c a)
                            b)
                     (and (<= (* a b) c)
                          (< c (+ a (* a b))))))
     :hints (("goal" :induct (niq-ind a b c))
             (and stable-under-simplificationp
                  '(:nonlinearp t))))

   (local (include-book "arithmetic-3/bind-free/top" :dir :system))
   (local (in-theory (disable acl2::cancel-mod-+-basic)))

   (local (defthm l0
            (implies (and (integerp a)
                          (natp size)
                          (<= (* size offset) a)
                          (< a (+ size (* size offset)))
                          (natp offset))
                     (equal (+ a (* (- size) offset))
                            (mod a size)))
            :hints(("Goal" :in-theory (enable mod)
                    :do-not-induct t))))

   (make-event
    `(defthm mod-blocksize-nonsense
       (implies (and (integerp a)
                     (<= (* ,*sbitset-block-size* offset) a)
                     (< a (+ ,*sbitset-block-size* (* ,*sbitset-block-size* offset)))
                     (natp offset))
                (equal (+ a (* ,(- *sbitset-block-size*) offset))
                       (mod a ,*sbitset-block-size*)))))))



(local (in-theory (disable bitops::logbitp-when-too-small
                           ;expt-between-one-and-two
                           ;; arith-3 acl2::expt-is-increasing-for-base->-1
                           bitops::expt-2-monotonic
                           acl2::associativity-of-append)))

(local (defthm integer-listp-of-append
         (implies (and (integer-listp x)
                       (integer-listp y))
                  (integer-listp (append x y)))))

(local (defthm rassoc-append
         (equal (append x (append y z))
                (append (append x y) z))))

(local (defun dec-induct (n)
         (if (zp n)
             n
           (dec-induct (1- n)))))

(local (defthm integerp-of-car-when-integer-listp
         (implies (integer-listp x)
                  (equal (integerp (car x))
                         (consp x)))))

(local (defthmd member-equal-is-in
         (implies (set::setp x)
                  (iff (member-equal a x)
                       (set::in a x)))
         :hints(("Goal" :in-theory (enable set::in-to-member)))))

(local
 (make-event
  `(defthm expt-2-monotonic-specialized-for-block-size
     (implies (and (< a ,*sbitset-block-size*)
                   (natp a))
              (< (expt 2 a) ,(expt 2 *sbitset-block-size*)))
     :hints(("Goal" :use ((:instance bitops::expt-2-monotonic
                                     (a a)
                                     (b ,*sbitset-block-size*))))))))


(local
 (defsection add-to-each

   (defthm consp-of-add-to-each
     (equal (consp (add-to-each offset x))
            (consp x))
     :hints(("Goal" :in-theory (enable add-to-each))))

   (defthm integer-listp-of-add-to-each
     (implies (and (integerp offset)
                   (integer-listp x))
              (integer-listp (add-to-each offset x)))
     :hints(("Goal" :in-theory (enable add-to-each))))

   (local (defthm l0
            (implies (and (member-equal a (add-to-each offset x))
                          (integerp offset)
                          (integer-listp x))
                     (integerp a))))

   (defthm member-equal-add-to-each
     (implies (and (force (integerp offset))
                   (force (integer-listp x)))
              (iff (member-equal a (add-to-each offset x))
                   (and (integerp a)
                        (member-equal (- a offset) x)))))

   (defthm no-duplicatesp-equal-of-add-to-each
     (implies (and (no-duplicatesp-equal x)
                   (force (integer-listp x))
                   (force (integerp offset)))
              (no-duplicatesp-equal (add-to-each offset x))))

   (local (defthm l1
            (implies (and (integerp a)
                          (integerp b))
                     (equal (set::<< a b)
                            (< a b)))
            :hints(("Goal" :in-theory (enable set::<< lexorder alphorder)))))

   (defthm setp-of-add-to-each
     (implies (and (integerp offset)
                   (integer-listp x)
                   (set::setp x))
              (set::setp (add-to-each offset x)))
     :hints(("Goal" :in-theory (enable* (:ruleset set::primitive-rules)
                                        add-to-each))))))



(local
 (defsection no-duplicatesp-equal-when-setp

   (local (defthm l0
            (implies (and (member-equal a x)
                          (set::<< a (car x)))
                     (not (set::setp x)))
            :hints(("Goal"
                    :induct (len x)
                    :in-theory (enable* (:ruleset set::primitive-rules)
                                        (:ruleset set::order-rules))))))

   (defthm no-duplicatesp-equal-when-setp
     (implies (set::setp x)
              (no-duplicatesp-equal x))
     :hints(("Goal" :in-theory (enable* (:ruleset set::primitive-rules)))))))


(local
 (defsection append-is-union

   (defun max-int (x)
     (cond ((atom x)
            nil)
           ((atom (cdr x))
            (car x))
           (t
            (max (car x)
                 (max-int (cdr x))))))

   (defun min-int (x)
     (cond ((atom x)
            nil)
           ((atom (cdr x))
            (car x))
           (t
            (min (car x)
                 (min-int (cdr x))))))

   (local (defthm l1
            (implies (and (case-split (integerp a))
                          (case-split (integerp b)))
                     (equal (set::<< a b)
                            (< a b)))
            :hints(("Goal" :in-theory (enable set::<< lexorder alphorder)))))

   (local (defthm l2
            (implies (and (integer-listp x)
                          (set::setp x))
                     (equal (min-int x)
                            (if (consp x)
                                (car x)
                              nil)))
            :hints(("Goal" :in-theory (enable* (:ruleset set::primitive-rules))))))

   (defthmd setp-of-append
     (implies (and (force (or (< (max-int x) (min-int y))
                              (atom x)
                              (atom y)))
                   (force (integer-listp x))
                   (force (integer-listp y))
                   (force (set::setp x))
                   (force (set::setp y)))
              (set::setp (append x y)))
     :hints(("Goal" :in-theory (enable* (:ruleset set::primitive-rules)))))

   (local (in-theory (enable setp-of-append)))

   (local (defthm in-of-append
            (implies (and (force (or (< (max-int x) (min-int y))
                                     (atom x)
                                     (atom y)))
                          (force (integer-listp x))
                          (force (integer-listp y))
                          (force (set::setp x))
                          (force (set::setp y)))
                     (equal (set::in a (append x y))
                            (or (set::in a x)
                                (set::in a y))))
            :hints(("goal"
                    :use ((:instance member-equal-is-in (x (append x y)))
                          (:instance member-equal-is-in (x x))
                          (:instance member-equal-is-in (x y)))))))

   (defthmd append-is-union
     (implies (and (force (or (< (max-int x) (min-int y))
                              (atom x)
                              (atom y)))
                   (force (integer-listp x))
                   (force (integer-listp y))
                   (force (set::setp x))
                   (force (set::setp y)))
              (equal (append x y)
                     (set::union x y))))))



(local
 (defsection consp-of-bits-between

   (local (defthm l1
            (implies (posp x)
                     (logbitp (logbitp-mismatch x 0) x))
            :hints(("Goal"
                    :in-theory (disable acl2::logbitp-mismatch-correct)
                    :use ((:instance acl2::logbitp-mismatch-correct
                                     (a x)
                                     (b 0)))))))

   (local (defthm l2
            (implies (posp x)
                     (< (logbitp-mismatch x 0) (integer-length x)))
            :rule-classes ((:rewrite) (:linear))))

   (local (defthm l3
            (implies (and (< x (expt 2 n))
                          (posp x)
                          (natp n))
                     (<= (logbitp-mismatch x 0)
                         n))
            :rule-classes ((:rewrite) (:linear))
            :hints(("Goal"
                    :in-theory (disable bitops::integer-length-bounded-by-expt)
                    :use ((:instance bitops::integer-length-bounded-by-expt (a x)))))))

   (local (defthm l4
            (implies (posp x)
                     (natp (logbitp-mismatch x 0)))
            :hints(("Goal" :in-theory (enable natp)))
            :rule-classes ((:rewrite) (:type-prescription))))

   (defthm consp-of-bits-between
     (implies (and (< block (expt 2 n))
                   (posp block)
                   (natp n))
              (consp (bits-between 0 n block)))
     :hints(("Goal"
             :in-theory (disable member-equal-of-bits-between)
             :use ((:instance member-equal-of-bits-between
                              (a (logbitp-mismatch block 0))
                              (n 0)
                              (x block)
                              (m n))))))))



(defmacro the-sbitset-block (x)
  `(the (unsigned-byte ,*sbitset-block-size*) ,x))

(make-event
 `(define sbitset-blockp (x)
    :returns (bool booleanp :rule-classes :type-prescription)
    :parents (sbitset-pairp)
    :short "@(call sbitset-blockp) recognizes numbers that are valid as the
<i>block</i> component of an @(see sbitset-pairp)."

    :long "<p>To ensure that sparse bitsets are canonical, we don't allow 0 as
a valid block.  The idea is that any block whose value is 0 should just be
omitted from the set.</p>"
    :inline t
    (mbe :logic (and (posp x)
                     (< x (expt 2 *sbitset-block-size*)))
         :exec (and (integerp x)
                    (<= 1 x)
                    (<= x ,(1- (expt 2 *sbitset-block-size*)))))
    ///
    (defthm sbitset-block-type
      (implies (sbitset-blockp x)
               (posp x))
      :rule-classes :compound-recognizer)

    (defthm sbitset-block-upper-bound
      ;; BOZO should this be linear, too?
      (implies (sbitset-blockp x)
               (< x (expt 2 *sbitset-block-size*))))))


(define sbitset-pairp (x)
  :parents (sbitsets)
  :returns (pairp booleanp :rule-classes :type-prescription)
  :short "@(call sbitset-pairp) recognizes a valid @('(offset . block)') pair
for sparse bitsets."
  :inline t
  (and (consp x)
       (natp (car x))
       (sbitset-blockp (cdr x)))
  ///
  (defthm consp-when-sbitset-pairp
    (implies (sbitset-pairp x)
             (consp x))
    :rule-classes :compound-recognizer))

(define sbitset-pair ((offset natp :type unsigned-byte)
                      (block sbitset-blockp))
  :returns pair
  :parents (sbitset-pairp)
  :short "@(call sbitset-pair) constructs a @('(offset . block)') pair."
  :inline t
  (cons offset block))

(define sbitset-pair-offset ((x sbitset-pairp))
  :parents (sbitset-pairp)
  :returns offset
  :short "@(call sbitset-pair-offset) gets the @('offset') from an @('(offset
  . block)') pair."
  :inline t
  (car x))

(define sbitset-pair-block ((x sbitset-pairp))
  :parents (sbitset-pairp)
  :returns block
  :short "@(call sbitset-pair-block) gets the @('block') from an @('(offset
  . block)') pair."
  :inline t
  (cdr x))

(defsection sbitset-pairp-basics
  :extension sbitset-pairp
  (local (in-theory (enable sbitset-pairp
                            sbitset-pair
                            sbitset-pair-offset
                            sbitset-pair-block)))

  (defthm sbitset-pair-offset-of-sbitset-pair
    (equal (sbitset-pair-offset (sbitset-pair offset block))
           offset))

  (defthm sbitset-pair-block-of-sbitset-pair
    (equal (sbitset-pair-block (sbitset-pair offset block))
           block))

  (defthm sbitset-pair-offset-type
    (implies (force (sbitset-pairp x))
             (natp (sbitset-pair-offset x)))
    :rule-classes :type-prescription)

  (defthm sbitset-pair-block-type
    (implies (force (sbitset-pairp x))
             (and (integerp (sbitset-pair-block x))
                  (< 0 (sbitset-pair-block x))))
    :rule-classes :type-prescription)

  (defthm sbitset-pair-block-upper-bound
    (implies (force (sbitset-pairp x))
             (< (sbitset-pair-block x) (expt 2 *sbitset-block-size*)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :use ((:instance sbitset-block-upper-bound
                                    (x (cdr x)))))))

  (defthm sbitset-pairp-of-sbitset-pair
    (implies (and (force (natp offset))
                  (force (sbitset-blockp block)))
             (sbitset-pairp (sbitset-pair offset block))))

  (defthm sbitset-blockp-of-sbitset-pair-block
    (implies (force (sbitset-pairp x))
             (sbitset-blockp (sbitset-pair-block x)))))



(define sbitset-pair-members ((x sbitset-pairp))
  :returns set
  :parents (sbitset-members sbitset-pairp)
  :short "@(call sbitset-pair-members) extracts the members of a single @(see
sbitset-pairp)."

  :long "<p>For instance, if the pair is @('(0 . 7)'), we produce the set
@('{0, 1, 2}'); if the set is @('(1 . 7)'), we produce @('{60, 61, 62}').</p>

<p>This serves as the logical definition we use to reason about member
extraction.</p>

<p>Normally this function isn't executed.  When the block size is 32 or 60, we
can instead use the optimized @(see bits-0-31) or @(see 60bits-0-59) routines
instead.  But, if you change the block size to something else, this function
<b>will</b> be executed and its performance will probably be bad.  In this
case, you might want to write a custom @('bits-0-32') style routine for your
block size.</p>"

  (add-to-each (* (sbitset-pair-offset x) *sbitset-block-size*)
               (bits-between 0 *sbitset-block-size* (sbitset-pair-block x)))

  ///

  (defthm sbitset-pair-members-of-nil
    (equal (sbitset-pair-members nil)
           nil))

  (defthm true-listp-of-sbitset-pair-members
    ;; Under the guard it always produces a consp as well, but it seems nice to
    ;; prove this unconditionally, separately.
    (true-listp (sbitset-pair-members x))
    :rule-classes :type-prescription)

  (defthm integer-listp-of-sbitset-pair-members
    (implies (force (sbitset-pairp x))
             (integer-listp (sbitset-pair-members x))))

  (local (include-book "arithmetic-3/bind-free/top" :dir :system))

  (defthm member-equal-sbitset-pair-members
    (implies (force (sbitset-pairp x))
             (iff (member-equal a (sbitset-pair-members x))
                  (and (natp a)
                       (equal (floor a *sbitset-block-size*)
                              (sbitset-pair-offset x))
                       (logbitp (mod a *sbitset-block-size*)
                                (sbitset-pair-block x))))))

  (defthm no-duplicatesp-equal-of-sbitset-pair-members
    (implies (force (sbitset-pairp x))
             (no-duplicatesp-equal (sbitset-pair-members x))))

  (defthm offsets-must-agree-when-sbitset-pair-members-intersect
    (implies (and (force (sbitset-pairp x))
                  (force (sbitset-pairp y))
                  (intersectp-equal (sbitset-pair-members x)
                                    (sbitset-pair-members y))
                  (syntaxp (term-order y x)))
             (equal (sbitset-pair-offset x)
                    (sbitset-pair-offset y)))
    :hints((acl2::set-reasoning)))

  (defthm consp-of-sbitset-pair-members
    (implies (force (sbitset-pairp x))
             (and (true-listp (sbitset-pair-members x))
                  (consp (sbitset-pair-members x))))
    :rule-classes :type-prescription)

  (defthm setp-of-sbitset-pair-members
    (implies (force (sbitset-pairp a))
             (set::setp (sbitset-pair-members a))))

  (defthm in-of-sbitset-pair-members
    (implies (force (sbitset-pairp x))
             (equal (set::in a (sbitset-pair-members x))
                    (and (natp a)
                         (equal (floor a *sbitset-block-size*)
                                (sbitset-pair-offset x))
                         (logbitp (mod a *sbitset-block-size*)
                                  (sbitset-pair-block x)))))
    :hints(("Goal" :use ((:instance member-equal-is-in
                                    (x (sbitset-pair-members x)))))))

  (defthm empty-of-sbitset-pair-members
    (implies (force (sbitset-pairp x))
             (not (set::empty (sbitset-pair-members x))))
    :hints(("Goal" :in-theory (e/d* ((:ruleset set::primitive-rules))
                                    (sbitset-pair-members))))))


(local
 (defsection sbitset-pair-members-bounds

  (local (in-theory (enable sbitset-pair-members)))

  (local (defthm max-int-of-add-to-each
           (implies (and (force (integerp offset))
                         (force (integer-listp x)))
                    (equal (max-int (add-to-each offset x))
                           (if (consp x)
                               (+ offset (max-int x))
                             nil)))
           :hints(("Goal"
                   :induct (add-to-each offset x)
                   :in-theory (enable add-to-each max-int)))))

  (local (defthm min-int-of-add-to-each
           (implies (and (force (integerp offset))
                         (force (integer-listp x)))
                    (equal (min-int (add-to-each offset x))
                           (if (consp x)
                               (+ offset (min-int x))
                             nil)))
           :hints(("Goal"
                   :induct (add-to-each offset x)
                   :in-theory (enable add-to-each min-int)))))

  (local (defthm max-int-of-bits-between
           (implies (and (consp (bits-between n m x))
                         (force (natp n))
                         (force (natp m))
                         (force (<= n m)))
                    (< (max-int (bits-between n m x))
                       m))
           :rule-classes ((:rewrite) (:linear))
           :hints(("Goal"
                   :induct (bits-between n m x)
                   :in-theory (enable bits-between)))))

  (local (defthm min-int-of-bits-between
           (implies (and (consp (bits-between n m x))
                         (force (natp n))
                         (force (natp m))
                         (force (<= n m)))
                    (<= n (min-int (bits-between n m x))))
           :rule-classes ((:rewrite) (:linear))
           :hints(("Goal"
                   :induct (bits-between n m x)
                   :in-theory (enable bits-between)))))

  (defthm sbitset-pair-members-upper-bound
    (implies (force (sbitset-pairp x))
             (< (max-int (sbitset-pair-members x))
                (* *sbitset-block-size* (+ (sbitset-pair-offset x) 1))))
    :rule-classes ((:rewrite) (:linear)))

  (defthm sbitset-pair-members-lower-bound
    (implies (force (sbitset-pairp x))
             (<= (* *sbitset-block-size* (sbitset-pair-offset x))
                 (min-int (sbitset-pair-members x))))
    :rule-classes ((:rewrite) (:linear)))))


(define sbitsetp (x)
  :returns bool
  :parents (sbitsets)
  :short "@(call sbitsetp) determines whether @('X') is a well-formed sparse
bitset."

  (if (atom x)
      (not x)
    (and (sbitset-pairp (first x))
         (if (atom (cdr x))
             (not (cdr x))
           (and (sbitset-pairp (second x))
                (< (sbitset-pair-offset (first x))
                   (sbitset-pair-offset (second x)))))
         (sbitsetp (cdr x))))
  ///

  (defthm true-listp-when-sbitsetp
    (implies (sbitsetp x)
             (true-listp x))
    :rule-classes :compound-recognizer)

  (defthm sbitsetp-when-atom
    (implies (atom x)
             (equal (sbitsetp x)
                    (not x))))

  (defthm sbitsetp-of-cons
    (equal (sbitsetp (cons a x))
           (and (sbitset-pairp a)
                (sbitsetp x)
                (or (atom x)
                    (< (sbitset-pair-offset a)
                       (sbitset-pair-offset (first x)))))))

  (defthm sbitset-pairp-of-car
    (implies (sbitsetp x)
             (equal (sbitset-pairp (car x))
                    (consp x))))

  (defthm sbitsetp-of-cdr
    (implies (sbitsetp x)
             (sbitsetp (cdr x))))

  (defthm sbitset-pairp-when-member-equal-of-sbitsetp
    (implies (and (member-equal a x)
                  (sbitsetp x))
             (sbitset-pairp a))
    :rule-classes ((:rewrite)
                   (:rewrite :corollary
                             (implies (and (sbitsetp x)
                                           (member-equal a x))
                                      (sbitset-pairp a))))))


(define sbitset-fix ((x sbitsetp))
  :parents (sbitsets)
  :short "@(call sbitset-fix) is a basic fixing function for sparse bitsets."
  :inline t
  (mbe :logic (if (sbitsetp x) x nil)
       :exec x)
  ///
  (defthm true-listp-of-sbitset-fix
    (true-listp (sbitset-fix x))
    :rule-classes :type-prescription)

  (defthm sbitsetp-of-sbitset-fix
    (sbitsetp (sbitset-fix x)))

  (defthm sbitset-fix-when-sbitsetp
    (implies (sbitsetp x)
             (equal (sbitset-fix x)
                    x))))



; We optimize the definition of sbitset-members if the block-size is 60 or 32
; bits.

(defsection sbitset-members
  :parents (sbitsets)
  :short "@(call sbitset-members) converts a bitset into an ordinary, ordered
set."

  :long "<p>In the logic, we just call @(see sbitset-pair-members) on each
block to get the members.</p>

<p>However, this function should typically be left disabled and you should not
reason about the underlying representation of sparse bitsets.</p>

<p>For faster execution, when the block size is 32 or 60 we use a partially
unrolled inner loop for extracting the bits from each block.  This optimization
is not performed for other block sizes.</p>"

  (make-event
   (b* ((fn (case *sbitset-block-size*
              (60 '60bits-0-59)
              (32 'bits-0-31)
              (otherwise nil)))
        (exec-def
         (if fn
             `(defun sbitset-members-exec (x acc)
                (declare (xargs :guard (sbitsetp x)))
                (if (atom x)
                    acc
                  (let* ((pair1   (car x))
                         (offset1 (sbitset-pair-offset pair1))
                         (block1  (sbitset-pair-block pair1)))
                    ;; BOZO should probably use ash 5 for 32-bit case
                    (,fn (* offset1 ,*sbitset-block-size*)
                         block1
                         (sbitset-members-exec (cdr x) acc)))))
           `(value-triple :invisible)))
        (logic-body
         `(if (not (sbitsetp x))
              nil
            (if (atom x)
                nil
              (append (sbitset-pair-members (car x))
                      (sbitset-members-aux (cdr x))))))
        (real-body
         (if fn
             `(mbe :logic ,logic-body
                   :exec (sbitset-members-exec x nil))
           logic-body))
        (remove-thm
         (if fn
             `(defthm sbitset-members-exec-removal
                (implies (force (sbitsetp x))
                         (equal (sbitset-members-exec x acc)
                                (append (sbitset-members-aux x) acc)))
                :hints(("Goal" :in-theory (enable sbitset-pair-members))))
           `(value-triple :invisible))))
     `(encapsulate
        ()
        ,exec-def
        (acl2::defund-inline sbitset-members-aux (x)
          (declare (xargs :guard (sbitsetp x)
                          :verify-guards nil))
          ,real-body)
        (local (in-theory (enable sbitset-members-aux)))
        ,remove-thm
        (verify-guards sbitset-members-aux$inline))))

  (define sbitset-members ((x sbitsetp))
    :inline t
    :verify-guards nil
    (mbe :logic (if (or (not (sbitsetp x))
                        (atom x))
                    nil
                  (set::union (sbitset-pair-members (car x))
                               (sbitset-members (cdr x))))
         :exec (sbitset-members-exec x nil)))

  (local (in-theory (enable sbitset-members sbitset-members-aux)))

  (defsection guard-verification

    (local (defthm l0
             (integer-listp (sbitset-members-aux x))))

    (local (defthm l1
             (equal (consp (sbitset-members-aux x))
                    (and (sbitsetp x)
                         (consp x)))))

    (local (defthm l2
             (implies (set::setp (append x y))
                      (and (set::setp (acl2::list-fix x))
                           (set::setp y)))
             :hints(("Goal" :in-theory (enable* (:ruleset set::primitive-rules))))))

    (local (defthm l3
             (equal (min-int (append x y))
                    (if (consp x)
                        (if (consp y)
                            (min (min-int x) (min-int y))
                          (min-int x))
                      (if (consp y)
                          (min-int y)
                        nil)))
             :hints(("Goal" :in-theory (enable min-int append)))))

    (local (defthm l4
             (set::setp (sbitset-members-aux x))
             :hints(("Goal" :in-theory (enable setp-of-append)))))

    (local (defthm l5
             (equal (sbitset-members-aux x)
                    (if (or (atom x)
                            (not (sbitsetp x)))
                        nil
                      (set::union (sbitset-pair-members (car x))
                                   (sbitset-members-aux (cdr x)))))
             :rule-classes :definition
             :hints(("Goal" :in-theory (e/d (append-is-union)
                                            (set::double-containment))))))

    (defthm sbitset-members-aux-removal
      (equal (sbitset-members-aux x)
             (sbitset-members x)))

    (verify-guards+ sbitset-members))


  (defthm sbitset-members-default
    (implies (not (sbitsetp a))
             (equal (sbitset-members a)
                    nil)))

  (defthm sbitset-members-when-atom
    (implies (atom x)
             (equal (sbitset-members x)
                    nil)))

  (local (defthm l0
           (implies (atom x)
                    (equal (set::setp x)
                           (not x)))
           :hints(("Goal" :in-theory (enable set::setp)))))

  (local (defthm union-under-iff
           (iff (set::union x y)
                (or (not (set::empty x))
                    (not (set::empty y))))
           :hints(("Goal" :in-theory (enable* (:ruleset set::primitive-rules))))))

  (defthm sbitset-members-of-cons
    (implies (force (sbitsetp (cons a x)))
             (equal (sbitset-members (cons a x))
                    (set::union (sbitset-pair-members a)
                                 (sbitset-members x)))))

  (defthm sbitset-members-of-sbitset-fix
    (equal (sbitset-members (sbitset-fix b))
           (sbitset-members b))
    :hints(("Goal" :in-theory (enable sbitset-fix))))

  (defthm true-listp-of-sbitset-members
    (true-listp (sbitset-members x))
    :rule-classes :type-prescription)

  (defthm setp-of-sbitset-members
    (set::setp (sbitset-members x)))

  (defthm no-duplicatesp-equal-of-sbitset-members
    (no-duplicatesp-equal (sbitset-members x))))



(define sbitset-find ((offset natp)
                      (x      sbitsetp))
  :parents (in-of-sbitset-members)
  :short "Helper definition; shouldn't be needed by users."
  (cond ((atom x)
         nil)
        ((equal (sbitset-pair-offset (car x)) offset)
         (car x))
        (t
         (sbitset-find offset (cdr x))))
  ///
  (defthm sbitset-find-when-atom
    (implies (atom x)
             (equal (sbitset-find offset x)
                    nil)))

  (defthm sbitset-find-of-cons
    (equal (sbitset-find offset (cons a x))
           (if (equal (sbitset-pair-offset a) offset)
               a
             (sbitset-find offset x))))

  (defthm member-equal-of-sbitset-find
    (implies (sbitset-find offset x)
             (member-equal (sbitset-find offset x) x)))

  (defthm sbitset-pairp-of-sbitset-find
    (implies (force (sbitsetp x))
             (equal (sbitset-pairp (sbitset-find offset x))
                    (if (sbitset-find offset x)
                        t
                      nil))))

  (defthm sbitset-pair-offset-of-sbitset-find
    (implies (sbitsetp x)
             (equal (sbitset-pair-offset (sbitset-find offset x))
                    (if (sbitset-find offset x)
                        offset
                      nil))))

  (defthm natp-when-sbitset-find
    (implies (and (sbitset-find offset x)
                  (sbitsetp x))
             (natp offset))
    :rule-classes (:forward-chaining)))



(defsection in-of-sbitset-members
  :parents (sbitset-members)
  :short "Low-level lemma to rewrite @('(in a (sbitset-members x))') into a
more structural form."

  :long "<p>This theorem is disabled by default and most users shouldn't enable
it.  It's only needed to prove properties about the basic sbitset
constructors.</p>

<p>This is a little more complicated than in the basic bitset library, because
we have to go to the proper pair.</p>"

  (local (defthm l0
           (implies (and (sbitsetp x)
                         (set::in a (sbitset-members x)))
                    (sbitset-find (floor a *sbitset-block-size*) x))
           :hints(("Goal"
                   :in-theory (disable mod-blocksize-nonsense)
                   :induct (len x)
                   :expand ((sbitset-members x))))))

  (local (defthm l1
           (implies (and (sbitsetp x)
                         (< offset (sbitset-pair-offset (car x))))
                    (not (sbitset-find offset x)))
           :hints(("Goal" :in-theory (enable sbitset-find)))))

  (local (defthm l2
           (implies (and (sbitset-pairp x)
                         (set::in a (sbitset-pair-members x)))
                    (equal (sbitset-pair-offset x)
                           (floor a *sbitset-block-size*)))))

  (local (defthm l3
           (implies (sbitsetp x)
                    (equal (set::in a (sbitset-members x))
                           (let ((pair (sbitset-find (floor a *sbitset-block-size*) x)))
                             (and pair
                                  (set::in a (sbitset-pair-members pair))))))
           :hints(("Goal"
                   :induct (len x)
                   :expand ((sbitset-members x)
                            (:free (n) (sbitset-find n x)))
                   :in-theory (disable in-of-sbitset-pair-members)
                   :do-not '(generalize fertilize)))))

  (defthmd in-of-sbitset-members
    (equal (set::in a (sbitset-members x))
           (and (sbitsetp x)
                (let ((pair (sbitset-find (floor a *sbitset-block-size*) x)))
                  (and pair
                       (set::in a (sbitset-pair-members pair))))))
    :hints(("Goal" :use ((:instance l3))))))


(local (in-theory (enable in-of-sbitset-members)))



; -----------------------------------------------------------------------------
;
;                           BASIC SBITSET OPERATIONS
;
; -----------------------------------------------------------------------------

(make-event
 `(define sbitset-singleton-pair ((a natp :type unsigned-byte))
    :returns (pair sbitset-pairp)
    :parents (sbitset-singleton)
    :short "@(call sbitset-singleton-pair) creates a @(see sbitset-pairp) whose
only member is @('a')."
    :guard-hints(("Goal" :in-theory (enable sbitset-blockp)))
    :split-types t
    :prepwork ((local (in-theory (enable sbitset-blockp)))
               (local (include-book "arithmetic-3/bind-free/top" :dir :system)))
    :inline t
    (mbe :logic
         (let ((a (nfix a)))
           (sbitset-pair (floor a *sbitset-block-size*)
                         (expt 2 (mod a *sbitset-block-size*))))
         :exec
         (sbitset-pair (truncate a ,*sbitset-block-size*)
                       (ash 1 (rem a ,*sbitset-block-size*))))
    ///
    (defthm sbitset-pair-offset-of-sbitset-singleton-pair
      (equal (sbitset-pair-offset (sbitset-singleton-pair a))
             (floor (nfix a) *sbitset-block-size*)))

    (defthm sbiset-pair-block-of-sbitset-singleton-pair
      (equal (sbitset-pair-block (sbitset-singleton-pair a))
             (expt 2 (mod (nfix a) *sbitset-block-size*))))))

(define sbitset-singleton ((a natp :type unsigned-byte))
  :parents (sbitsets)
  :short "@(call sbitset-singleton) constructs the singleton set @('{a}')."
  :split-types t
  :inline t
  :returns (sbitset sbitsetp)
  (list (sbitset-singleton-pair a))
  ///
  (local (include-book "arithmetic-3/bind-free/top" :dir :system))

  (local (defthm l0
           (equal (set::in a (sbitset-members (sbitset-singleton b)))
                  (equal a (nfix b)))
           :hints (("goal" :use ((:instance niq-lemma
                                  (c (nfix b)) (a 60) (b a)))
                    :in-theory (e/d (mod) (niq-lemma mod-blocksize-nonsense))))))

  (defthm sbitset-members-of-sbitset-singleton
    (equal (sbitset-members (sbitset-singleton a))
           (set::insert (nfix a) nil))
    :hints(("Goal" :in-theory (disable sbitset-singleton)))))


(local (defthm sbitset-blockp-of-logior
         (implies (and (force (sbitset-blockp x))
                       (force (sbitset-blockp y)))
                  (sbitset-blockp (logior x y)))
         :hints(("Goal"
                 :in-theory (e/d (sbitset-blockp)
                                 (bitops::upper-bound-of-logior-for-naturals))
                 :use ((:instance bitops::upper-bound-of-logior-for-naturals
                                  (x x)
                                  (y y)
                                  (n *sbitset-block-size*)))))))

(local (defthm equal-of-sbitset-pair
         (implies (force (sbitset-pairp x))
                  (equal (equal (sbitset-pair offset block) x)
                         (and (equal offset (sbitset-pair-offset x))
                              (equal block (sbitset-pair-block x)))))
         :hints(("Goal" :in-theory (enable sbitset-pair
                                           sbitset-pairp
                                           sbitset-pair-offset
                                           sbitset-pair-block)))))

(local (defthm lower-bound-of-first-offset-of-sbitset-find
         (implies (and (sbitset-find b x)
                       (<= b a)
                       (sbitsetp x))
                  (<= (sbitset-pair-offset (car x)) a))
         :rule-classes ((:rewrite) (:linear))
         :hints(("goal"
                 :in-theory (enable sbitset-find)
                 :do-not '(generalize fertilize)))))


(defsection sbitset-union
  :parents (sbitsets)
  :short "@('(sbitset-union X Y ...)') constructs the set @('X U Y U ...')."
  :long "@(def sbitset-union)"

  (define sbitset-union-exec ((x sbitsetp)
                              (y sbitsetp))
    :measure (+ (len x) (len y))
    (b* (((when (atom x)) y)
         ((when (atom y)) x)
         (x1 (car x))
         (y1 (car y))
         ((the unsigned-byte x1.offset) (sbitset-pair-offset x1))
         ((the unsigned-byte y1.offset) (sbitset-pair-offset y1))
         ((when (< x1.offset y1.offset))
          (cons x1 (sbitset-union-exec (cdr x) y)))
         ((unless (eql x1.offset y1.offset))
          (cons y1 (sbitset-union-exec x (cdr y))))
         (x1.block (sbitset-pair-block x1))
         (y1.block (sbitset-pair-block y1))
         (new-block (the-sbitset-block
                     (logior (the-sbitset-block x1.block)
                             (the-sbitset-block y1.block))))
         (new-pair (sbitset-pair x1.offset new-block)))
      (cons new-pair (sbitset-union-exec (cdr x) (cdr y)))))

  (define sbitset-binary-union ((x sbitsetp)
                                (y sbitsetp))
    :inline t
    (mbe :logic (sbitset-union-exec (sbitset-fix x)
                                    (sbitset-fix y))
         :exec (sbitset-union-exec x y)))

  (defmacro sbitset-union (&rest args)
    (cond ((atom args)
           nil)
          ((atom (cdr args))
           (car args))
          (t
           (xxxjoin 'sbitset-binary-union args))))

  (add-macro-alias sbitset-union sbitset-binary-union$inline)
  (add-macro-fn    sbitset-union sbitset-binary-union$inline t)

  (local (in-theory (enable sbitset-union-exec
                            sbitset-union)))

  (local (defthm c0
           (implies (and (< a (sbitset-pair-offset x1))
                         (< a (sbitset-pair-offset (car y2)))
                         (sbitset-pairp x1)
                         (sbitsetp y2))
                    (< a (sbitset-pair-offset (car (sbitset-union-exec (cons x1 x2) y2)))))
           :rule-classes ((:rewrite) (:linear))))

  (local (defthm c1
           (implies (and (< a (sbitset-pair-offset y1))
                         (< a (sbitset-pair-offset (car x2)))
                         (sbitsetp x2)
                         (sbitset-pairp y1))
                    (< a (sbitset-pair-offset (car (sbitset-union-exec x2 (cons y1 y2))))))
           :rule-classes ((:rewrite) (:linear))))

  (local (defthm c2
           (implies (and (< a (sbitset-pair-offset (car x2)))
                         (< a (sbitset-pair-offset (car y2)))
                         (sbitset-pairp x1)
                         (sbitsetp y2))
                    (< a (sbitset-pair-offset (car (sbitset-union-exec x2 y2)))))
           :rule-classes ((:rewrite) (:linear))))

  (defthm sbitsetp-of-sbitset-union-exec
    (implies (and (sbitsetp x)
                  (sbitsetp y))
             (sbitsetp (sbitset-union-exec x y)))
    :hints(("Goal"
            :induct (sbitset-union-exec x y)
            :do-not '(generalize fertilize))))

  (local (defthm l0
           (implies (and (sbitsetp x)
                         (sbitsetp y))
                    (iff (sbitset-find offset (sbitset-union-exec x y))
                         (or (sbitset-find offset x)
                             (sbitset-find offset y))))
           :hints(("Goal"
                   :induct (sbitset-union-exec x y)
                   :in-theory (enable sbitset-union-exec)))))

  (local (defthm m0
           (implies (and (sbitsetp x)
                         (sbitsetp y))
                    (equal (sbitset-find offset (sbitset-union-exec x y))
                           (let* ((x[offset] (sbitset-find offset x))
                                  (y[offset] (sbitset-find offset y)))
                             (cond ((and x[offset] y[offset])
                                    (sbitset-pair offset
                                                  (logior (sbitset-pair-block x[offset])
                                                          (sbitset-pair-block y[offset]))))
                                   (x[offset])
                                   (y[offset])
                                   (t
                                    nil)))))
           :hints(("Goal"
                   :induct (sbitset-union-exec x y)
                   :in-theory (enable sbitset-union-exec sbitset-find)
                   :do-not '(generalize fertilize)))))

  (in-theory (disable sbitset-union-exec))

  (local (defthm m1
           (implies (and (sbitsetp x)
                         (sbitsetp y))
                    (equal (set::in a (sbitset-members (sbitset-union-exec x y)))
                           (or (set::in a (sbitset-members x))
                               (set::in a (sbitset-members y)))))))

  (local (defthm sbitset-members-of-sbitset-union-exec
           ;; Just by double-containment.
           (implies (and (sbitsetp x)
                         (sbitsetp y))
                    (equal (sbitset-members (sbitset-union-exec x y))
                           (set::union (sbitset-members x)
                                        (sbitset-members y))))))

  ;; And now we just get rid of the hyps, with the fixing function.

  (local (in-theory (enable sbitset-union)))

  (defthm sbitset-of-sbitset-union
    (sbitsetp (sbitset-union x y)))

  (defthm sbitset-members-of-sbitset-union
    (equal (sbitset-members (sbitset-union x y))
           (set::union (sbitset-members x)
                        (sbitset-members y)))))


(local (defthm sbitset-blockp-of-logand
         (implies (and (force (sbitset-blockp x))
                       (force (sbitset-blockp y)))
                  (equal (sbitset-blockp (logand x y))
                         (not (zp (logand x y)))))
         :hints(("Goal"
                 :in-theory (e/d (sbitset-blockp)
                                 (bitops::unsigned-byte-p-of-logand-1
                                  bitops::unsigned-byte-p-of-logand-2
                                  ))
                 :use ((:instance bitops::unsigned-byte-p-of-logand-1
                                  (x x)
                                  (y y)
                                  (n *sbitset-block-size*)))))))

(defsection sbitset-intersect
  :parents (sbitsets)
  :short "@('(sbitset-intersect X Y ...)') constructs the set @('X \\intersect Y
\\intersect ...')."
  :long "@(def sbitset-intersect)"

  (define sbitset-intersect-exec ((x sbitsetp)
                                  (y sbitsetp))
    :measure (+ (len x) (len y))
    (b* (((when (atom x)) nil)
         ((when (atom y)) nil)
         (x1 (car x))
         (y1 (car y))
         ((the unsigned-byte x1.offset) (sbitset-pair-offset x1))
         ((the unsigned-byte y1.offset) (sbitset-pair-offset y1))
         ((when (< x1.offset y1.offset))
          (sbitset-intersect-exec (cdr x) y))
         ((unless (eql x1.offset y1.offset))
          (sbitset-intersect-exec x (cdr y)))
         (x1.block (sbitset-pair-block x1))
         (y1.block (sbitset-pair-block y1))
         (new-block (the-sbitset-block
                     (logand (the-sbitset-block x1.block)
                             (the-sbitset-block y1.block))))
         ((when (eql 0 (the-sbitset-block new-block)))
          (sbitset-intersect-exec (cdr x) (cdr y)))
         (new-pair (sbitset-pair x1.offset new-block)))
      (cons new-pair (sbitset-intersect-exec (cdr x) (cdr y)))))

  (define sbitset-binary-intersect ((x sbitsetp)
                                    (y sbitsetp))
    :inline t
    (mbe :logic (sbitset-intersect-exec (sbitset-fix x)
                                        (sbitset-fix y))
         :exec (sbitset-intersect-exec x y)))

  (defmacro sbitset-intersect (&rest args)
    (cond ((atom args)
           nil)
          ((atom (cdr args))
           (car args))
          (t
           (xxxjoin 'sbitset-binary-intersect args))))

  (add-macro-alias sbitset-intersect sbitset-binary-intersect$inline)
  (add-macro-fn    sbitset-intersect sbitset-binary-intersect$inline t)

  (local (in-theory (enable sbitset-intersect-exec
                            sbitset-intersect)))

  (local (defthm c0
           (implies (and (sbitset-intersect-exec x2 y2)
                         (< (sbitset-pair-offset x1)
                            (sbitset-pair-offset (car y2)))
                         (sbitset-pairp x1)
                         (sbitsetp x2)
                         (sbitset-pairp y1)
                         (sbitsetp y2))
                    (< (sbitset-pair-offset x1)
                       (sbitset-pair-offset (car (sbitset-intersect-exec x2 y2)))))))

  (defthm sbitsetp-of-sbitset-intersect-exec
    (implies (and (sbitsetp x)
                  (sbitsetp y))
             (sbitsetp (sbitset-intersect-exec x y)))
    :hints(("Goal"
            :induct (sbitset-intersect-exec x y)
            :do-not '(generalize fertilize))))

  (local (defthm l0
           (implies (and (sbitsetp x)
                         (sbitsetp y))
                    (iff (sbitset-find offset (sbitset-intersect-exec x y))
                         (let ((a (sbitset-find offset x))
                               (b (sbitset-find offset y)))
                           (and a
                                b
                                (not (zp (logand (sbitset-pair-block a)
                                                 (sbitset-pair-block b))))))))
           :hints(("Goal"
                   :induct (sbitset-intersect-exec x y)
                   :in-theory (enable sbitset-intersect-exec)))))

  (local (defthm m0
           (implies (and (sbitsetp x)
                         (sbitsetp y))
                    (equal (sbitset-find offset (sbitset-intersect-exec x y))
                           (let* ((a         (sbitset-find offset x))
                                  (b         (sbitset-find offset y))
                                  (new-block (logand (sbitset-pair-block a)
                                                     (sbitset-pair-block b))))
                             (and a
                                  b
                                  (not (zp new-block))
                                  (sbitset-pair offset new-block)))))
           :hints(("Goal"
                   :induct (sbitset-intersect-exec x y)
                   :in-theory (enable sbitset-intersect-exec sbitset-find)
                   :do-not '(generalize fertilize)))))

  (in-theory (disable sbitset-intersect-exec))

  (local (defthm n0
           (implies (and (logbitp a x)
                         (equal (logand x y) 0))
                    (not (logbitp a y)))
           :hints(("Goal"
                   :in-theory (disable bitops::logbitp-of-logand)
                   :use ((:instance bitops::logbitp-of-logand
                                    (a a)
                                    (x x)
                                    (y y)))))))

  (local (defthm m1
           (implies (and (sbitsetp x)
                         (sbitsetp y))
                    (equal (set::in a (sbitset-members (sbitset-intersect-exec x y)))
                           (and (set::in a (sbitset-members x))
                                (set::in a (sbitset-members y)))))))

  (local (defthm sbitset-members-of-sbitset-intersect-exec
           ;; Just by double-containment.
           (implies (and (sbitsetp x)
                         (sbitsetp y))
                    (equal (sbitset-members (sbitset-intersect-exec x y))
                           (set::intersect (sbitset-members x)
                                            (sbitset-members y))))
           :hints(("Goal" :in-theory (disable (force))))))

  ;; And now we just get rid of the hyps, with the fixing function.

  (local (in-theory (enable sbitset-intersect)))

  (defthm sbitset-of-sbitset-intersect
    (sbitsetp (sbitset-intersect x y)))

  (defthm sbitset-members-of-sbitset-intersect
    (equal (sbitset-members (sbitset-intersect x y))
           (set::intersect (sbitset-members x)
                            (sbitset-members y)))))




(local (defthm sbitset-blockp-of-logandc2
         (implies (and (force (sbitset-blockp x))
                       (force (sbitset-blockp y)))
                  (equal (sbitset-blockp (logand x (lognot y)))
                         (not (zp (logand x (lognot y))))))
         :hints(("Goal"
                 :in-theory (e/d (sbitset-blockp)
                                 (bitops::unsigned-byte-p-of-logand-1
                                  bitops::unsigned-byte-p-of-logand-2
                                  ))
                 :use ((:instance bitops::unsigned-byte-p-of-logand-1
                                  (x x)
                                  (y (lognot y))
                                  (n *sbitset-block-size*)))))))


(define sbitset-difference ((x sbitsetp)
                            (y sbitsetp))
  :returns sbitset
  :parents (sbitsets)
  :short "@('(sbitset-difference X Y)') constructs the set @('X - Y')."

  :prepwork
  ((define sbitset-difference-exec ((x sbitsetp)
                                    (y sbitsetp))
     :measure (+ (len x) (len y))
     (b* (((when (atom x)) nil)
          ((when (atom y)) x)
          (x1 (car x))
          (y1 (car y))
          ((the unsigned-byte x1.offset) (sbitset-pair-offset x1))
          ((the unsigned-byte y1.offset) (sbitset-pair-offset y1))
          ((when (< x1.offset y1.offset))
           (cons (car x) (sbitset-difference-exec (cdr x) y)))
          ((unless (eql x1.offset y1.offset))
           (sbitset-difference-exec x (cdr y)))
          (x1.block (sbitset-pair-block x1))
          (y1.block (sbitset-pair-block y1))
          (new-block (the-sbitset-block
                      (logandc2 (the-sbitset-block x1.block)
                                (the-sbitset-block y1.block))))
          ((when (eql 0 (the-sbitset-block new-block)))
           (sbitset-difference-exec (cdr x) (cdr y)))
          (new-pair (sbitset-pair x1.offset new-block)))
       (cons new-pair (sbitset-difference-exec (cdr x) (cdr y))))))

  :inline t
  (mbe :logic (sbitset-difference-exec (sbitset-fix x)
                                       (sbitset-fix y))
       :exec (sbitset-difference-exec x y))
  ///
  (local (in-theory (enable sbitset-difference-exec)))

  (local (defthm c1
           (IMPLIES (AND (< a (SBITSET-PAIR-OFFSET (CAR X2)))
                         (< a (SBITSET-PAIR-OFFSET (CAR Y2)))
                         (SBITSET-DIFFERENCE-EXEC X2 Y2)
                         (SBITSETP X2)
                         (SBITSETP Y2))
                    (< a (SBITSET-PAIR-OFFSET (CAR (SBITSET-DIFFERENCE-EXEC X2 Y2)))))))

  (defthm sbitsetp-of-sbitset-difference-exec
    (implies (and (sbitsetp x)
                  (sbitsetp y))
             (sbitsetp (sbitset-difference-exec x y)))
    :hints(("Goal"
            :induct (sbitset-difference-exec x y)
            :do-not '(generalize fertilize))))

  (local (defthm l0
           (implies (and (sbitsetp x)
                         (sbitsetp y))
                    (iff (sbitset-find offset (sbitset-difference-exec x y))
                         (let* ((a (sbitset-find offset x))
                                (b (sbitset-find offset y))
                                (new-block (logandc2 (sbitset-pair-block a)
                                                     (sbitset-pair-block b))))
                           (and a
                                (or (not b)
                                    (not (zp new-block)))))))
           :hints(("Goal"
                   :induct (sbitset-difference-exec x y)
                   :in-theory (enable sbitset-difference-exec)))))

  (local (defthm m0
           (implies (and (sbitsetp x)
                         (sbitsetp y))
                    (equal (sbitset-find offset (sbitset-difference-exec x y))
                           (let* ((a         (sbitset-find offset x))
                                  (b         (sbitset-find offset y))
                                  (new-block (logandc2 (sbitset-pair-block a)
                                                       (sbitset-pair-block b))))
                             (and a
                                  (if (not b)
                                      a
                                    (and (not (zp new-block))
                                         (sbitset-pair offset new-block)))))))
           :hints(("Goal"
                   :induct (sbitset-difference-exec x y)
                   :in-theory (enable sbitset-difference-exec sbitset-find)
                   :do-not '(generalize fertilize)))))

  (in-theory (disable sbitset-difference-exec))

  (local (defthm n0
           (implies (and (equal (logand x (lognot y)) 0)
                         (logbitp a x))
                    (logbitp a y))
           :hints(("Goal"
                   :in-theory (disable bitops::logbitp-of-logand)
                   :use ((:instance bitops::logbitp-of-logand
                                    (a a)
                                    (x x)
                                    (y (lognot y))))))))

  (local (defthm m1
           (implies (and (sbitsetp x)
                         (sbitsetp y))
                    (equal (set::in a (sbitset-members (sbitset-difference-exec x y)))
                           (and (set::in a (sbitset-members x))
                                (not (set::in a (sbitset-members y))))))))

  (local (defthm sbitset-members-of-sbitset-difference-exec
           ;; Just by double-containment.
           (implies (and (sbitsetp x)
                         (sbitsetp y))
                    (equal (sbitset-members (sbitset-difference-exec x y))
                           (set::difference (sbitset-members x)
                                             (sbitset-members y))))
           :hints(("Goal" :in-theory (disable (force))))))

  ;; And now we just get rid of the hyps, with the fixing function.

  (local (in-theory (enable sbitset-difference)))

  (defthm sbitset-of-sbitset-difference
    (sbitsetp (sbitset-difference x y)))

  (defthm sbitset-members-of-sbitset-difference
    (equal (sbitset-members (sbitset-difference x y))
           (set::difference (sbitset-members x)
                             (sbitset-members y)))))


#||


; -----------------------------------------------------------------------------
;
;                         WITNESS STYLE REASONING
;
; -----------------------------------------------------------------------------

; In ordinary bitsets, we could just use equal-by-logbitp to quickly prove
; equal-bitsets-by-membership.  Here we don't have a badguy already ready
; already, so we have to make one.

;; (local
;;  (define sbitset-badguy (x y)
;;    ;; Returns the offset for the first difference, or nil if they're identical.
;;    :verify-guards nil
;;    (b* (((when (atom x))
;;          (if (atom y)
;;              nil
;;            (sbitset-pair-offset (car y))))
;;         ((when (atom y))
;;          (sbitset-pair-offset (car x)))
;;         (x-off (sbitset-pair-offset (car x)))
;;         (y-off (sbitset-pair-offset (car y)))
;;         ((when (< x-off y-off)) x-off)
;;         ((when (< y-off x-off)) y-off)
;;         ((unless (equal (sbitset-pair-block (car x))
;;                         (sbitset-pair-block (car y))))
;;          x-off))
;;      (sbitset-badguy (cdr x) (cdr y)))
;;    ///
;;    (local (defthm equal-of-sbitset-pairs
;;             (implies (and (sbitset-pairp x)
;;                           (sbitset-pairp y))
;;                      (equal (equal x y)
;;                             (and (equal (sbitset-pair-offset x)
;;                                         (sbitset-pair-offset y))
;;                                  (equal (sbitset-pair-block x)
;;                                         (sbitset-pair-block y)))))
;;             :hints(("Goal" :in-theory (enable sbitset-pairp
;;                                               sbitset-pair-offset
;;                                               sbitset-pair-block)))))

;;    (defthm sbitset-badguy-under-iff
;;      (implies (and (sbitsetp x)
;;                    (sbitsetp y))
;;               (iff (sbitset-badguy x y)
;;                    (not (equal x y))))
;;      :hints(("Goal" :in-theory (enable sbitsetp))))

;;    (local (defthm l0
;;             (IMPLIES (AND (EQUAL (SBITSET-BADGUY X2 Y2) offset)
;;                           (< offset (SBITSET-PAIR-OFFSET (CAR X2)))
;;                           offset
;;                           (SBITSETP X2)
;;                           (SBITSETP Y2))
;;                      (<= (SBITSET-PAIR-OFFSET (CAR Y2))
;;                          offset))))

;;    (local (defthm l1
;;             (IMPLIES (AND (EQUAL (SBITSET-BADGUY X2 Y2) 0)
;;                           (< 0 (SBITSET-PAIR-OFFSET (CAR X2)))
;;                           (SBITSETP X2)
;;                           (SBITSETP Y2))
;;                      (equal (SBITSET-PAIR-OFFSET (CAR Y2))
;;                             0))))

;;    (defthm sbitset-badguy-correct
;;      (let ((offset (sbitset-badguy x y)))
;;        (implies (and (sbitsetp x)
;;                      (sbitsetp y)
;;                      offset)
;;                 (not (equal (sbitset-find offset x)
;;                             (sbitset-find offset y))))))))


; if we've found some block that's in one but not the other, then we have a member.

(define sbitset-pair-badguy (x y)
  :verify-guards nil
  (b* (((when (equal x y))
        nil)
       (x-off   (sbitset-pair-offset x))
       (y-off   (sbitset-pair-offset y))
       (x-block (sbitset-pair-block x))
       (y-block (sbitset-pair-block y))
       ((when (equal x-off y-off))
        (+ (* x-off *sbitset-block-size*)
           (logbitp-mismatch x-block y-block))))
    (car (sbitset-pair-members x))))

(define sbitset-badguy (x y)
  :verify-guards nil
  (b* (((when (atom x))
        (if (atom y)
            nil
          (car (sbitset-pair-members (car y)))))
       ((when (atom y))
        (car (sbitset-pair-members (car x))))
       ((when (equal (car x) (car y)))
        (sbitset-badguy (cdr x) (cdr y))))
    (sbitset-pair-badguy (car x) (car y)))))

(local (in-theory (enable sbitset-pair-badguy)))

(local (defthm l1
           (implies (nat-listp x)
                    (iff (car x)
                         (consp x)))))

(local (defthm l2
           (implies (and (nat-listp x)
                         (natp offset))
                    (nat-listp (add-to-each offset x)))))

(local (defthm l3
           (implies (sbitset-pairp x)
                    (nat-listp (sbitset-pair-members x)))
           :hints(("Goal" :in-theory (enable sbitset-pair-members)))))

(defthm sbitset-pair-badguy-under-iff
    (implies (and (sbitset-pairp x)
                  (sbitset-pairp y))
             (iff (sbitset-pair-badguy x y)
                  (not (equal x y))))
    :hints(("Goal" :in-theory (enable sbitset-pair-members))))


(local (defthm c0
           (iff (member (car x) x)
                (consp x))))

(local (defthm c1-upper
           (implies (and (member elem (sbitset-pair-members x))
                         (sbitset-pairp x))
                    (< elem (+ *sbitset-block-size*
                               (* *sbitset-block-size* (sbitset-pair-offset x)))))))

(local (defthm c1-lower
           (implies (and (member elem (sbitset-pair-members x))
                         (sbitset-pairp x))
                    (<= (* *sbitset-block-size* (sbitset-pair-offset x))
                        elem))))

(local (defthm c1-upper-special
           (implies (sbitset-pairp x)
                    (< (car (sbitset-pair-members x))
                       (+ *sbitset-block-size*
                          (* *sbitset-block-size* (sbitset-pair-offset x)))))
           :rule-classes ((:rewrite) (:linear))))

(local (defthm c1-lower-special
           (implies (sbitset-pairp x)
                    (<= (* *sbitset-block-size* (sbitset-pair-offset x))
                        (car (sbitset-pair-members x))))
           :rule-classes ((:rewrite) (:linear))))

(local (defthm c2
           (implies (sbitset-pairp x)
                    (not (empty (sbitset-pair-members x))))))

(local (defthm equal-of-sbitset-pairs
           (implies (and (sbitset-pairp x)
                         (sbitset-pairp y))
                    (equal (equal x y)
                           (and (equal (sbitset-pair-offset x)
                                       (sbitset-pair-offset y))
                                (equal (sbitset-pair-block x)
                                       (sbitset-pair-block y)))))
           :hints(("Goal" :in-theory (enable sbitset-pairp
                                             sbitset-pair-offset
                                             sbitset-pair-block)))))

(local (defthm correct-when-offsets-differ
           (let ((elem (sbitset-pair-badguy x y)))
             (implies (and (not (equal (sbitset-pair-offset x)
                                       (sbitset-pair-offset y)))
                           (sbitset-pairp x)
                           (sbitset-pairp y))
                      (not (iff (member elem (sbitset-pair-members x))
                                (member elem (sbitset-pair-members y))))))))

(local (include-book "arithmetic-3/bind-free/top" :dir :system))

(local (defthm d0
           (iff (natp (logbitp-mismatch x y))
                (logbitp-mismatch x y))))

(local (defthm d0b
           (iff (rationalp (logbitp-mismatch x y))
                (logbitp-mismatch x y))))

(local (defthm d1
           (implies (and (natp x)
                         (syntaxp (not (quotep x))))
                    (equal (< (+ 0 x) y)
                           (< x y)))))

(local (defthm d2-help1
           (equal (logbitp-mismatch x x)
                  nil)))

(local (defthm d2-help2
           (implies (sbitset-pairp x)
                    (<= (integer-length (sbitset-pair-block x))
                        60))
           :rule-classes ((:rewrite) (:linear))
           :hints(("goal"
                   :in-theory (disable acl2::integer-length-monotonic)
                   :use ((:instance acl2::integer-length-monotonic
                                    (i (sbitset-pair-block x))
                                    (j (1- (expt 2 *sbitset-block-size*)))))))))

(local (defthm d2
           (implies (and (sbitset-pairp x)
                         (sbitset-pairp y))
                    (< (logbitp-mismatch (sbitset-pair-block x)
                                         (sbitset-pair-block y))
                       60))
           :hints(("Goal"
                   :in-theory (disable acl2::logbitp-mismatch-upper-bound)
                   :use ((:instance acl2::logbitp-mismatch-upper-bound
                                    (a (sbitset-pair-block x))
                                    (b (sbitset-pair-block y))))))))

(local (defthm d3
           (implies (and (not (logbitp (logbitp-mismatch x y) x))
                         (not (equal x y))
                         (natp x)
                         (natp y))
                    (logbitp (logbitp-mismatch x y) y))
           :hints(("goal" :use ((:instance acl2::logbitp-mismatch-correct
                                           (a x) (b y)))))))

(local (defthm d4
           (implies (and (logbitp (logbitp-mismatch x y) x)
                         (not (equal x y))
                         (natp x)
                         (natp y))
                    (not (logbitp (logbitp-mismatch x y) y)))
           :hints(("goal" :use ((:instance acl2::logbitp-mismatch-correct
                                           (a x) (b y)))))))

(local (defthm correct-when-offsets-same
           (let ((elem (sbitset-pair-badguy x y)))
             (implies (and (equal (sbitset-pair-offset x)
                                  (sbitset-pair-offset y))
                           (not (equal x y))
                           (sbitset-pairp x)
                           (sbitset-pairp y))
                      (not (iff (member elem (sbitset-pair-members x))
                                (member elem (sbitset-pair-members y))))))))

(defthm sbitset-pair-badguy-correct
    (let ((elem (sbitset-pair-badguy x y)))
      (implies (and (not (equal x y))
                    (sbitset-pairp x)
                    (sbitset-pairp y))
               (not (iff (member elem (sbitset-pair-members x))
                         (member elem (sbitset-pair-members y))))))
    :hints(("Goal"
            :in-theory (disable sbitset-pair-badguy
                                sbitset-pair-members
                                member-equal-sbitset-pair-members
                                correct-when-offsets-same
                                correct-when-offsets-differ)
            :use ((:instance correct-when-offsets-same)
                  (:instance correct-when-offsets-differ)))))

(local (in-theory (disable sbitset-pair-badguy)))
(local (in-theory (enable sbitset-badguy)))

(defthm sbitset-badguy-under-iff
  (implies (and (sbitsetp x)
                (sbitsetp y))
           (iff (sbitset-badguy x y)
                (not (equal x y))))
  :hints(("Goal" :in-theory (enable sbitsetp))))


(local (defthm m0
         (implies (and (sbitset-pairp x)
                       (sbitset-pairp y))
                  (iff (natp (sbitset-pair-badguy x y))
                       (sbitset-pair-badguy x y)))
         :hints(("Goal" :in-theory (enable sbitset-pair-badguy)))))

(local (defthm m1
         (let ((elem (sbitset-pair-badguy x y)))
           (implies (and (not (equal x y))
                         (sbitset-pairp x)
                         (sbitset-pairp y)
                         (member elem (sbitset-pair-members x)))
                    (not (member elem (sbitset-pair-members y)))))
         :hints(("Goal"
                 :in-theory (disable sbitset-pair-badguy-correct
                                     member-equal-sbitset-pair-members
                                     equal-of-sbitset-pairs)
                 :use ((:instance sbitset-pair-badguy-correct))))))

(local (defthm m2
         (let ((elem (sbitset-pair-badguy x y)))
           (implies (and (not (equal x y))
                         (sbitset-pairp x)
                         (sbitset-pairp y)
                         (not (member elem (sbitset-pair-members x))))
                    (member elem (sbitset-pair-members y))))
         :hints(("Goal"
                 :in-theory (disable sbitset-pair-badguy-correct
                                     member-equal-sbitset-pair-members
                                     equal-of-sbitset-pairs)
                 :use ((:instance sbitset-pair-badguy-correct))))))

(local (defthm m4
         (implies (and (< (sbitset-pair-offset a) (sbitset-pair-offset (car x)))
                       (member elem (sbitset-pair-members a))
                       (sbitsetp x)
                       (sbitset-pairp a))
                  (not (member elem (sbitset-members x))))
         :hints(("Goal" :in-theory (enable sbitset-members)))))

(local (defthm m5
         (IMPLIES (AND (< (sbitset-pair-offset a) (sbitset-pair-offset (car x)))
                       (not (member elem (sbitset-pair-members a)))
                       (sbitsetp x)
                       (sbitset-pairp a))
                  (not (member elem (sbitset-members x))))
         :hints(("Goal" :in-theory (enable sbitset-members)))))

(defthm m6
  (implies (and (member elem (sbitset-pair-members a))
                (member a x)
                (sbitset-pairp a)
                (sbitsetp x))
           (member elem (sbitset-members x)))
  :hints(("Goal" :in-theory (e/d (sbitset-members)
                                 (sbitset-pair-members
                                  in-of-sbitset-pair-members
                                  MEMBER-EQUAL-SBITSET-PAIR-MEMBERS
                                  car-cdr-elim
                                  )))))

(defthm m7
  (IMPLIES (AND (< (SBITSET-PAIR-OFFSET X1)
                   (SBITSET-PAIR-OFFSET (CAR X2)))
                (NOT (EQUAL X1 Y1))
                (SBITSET-PAIRP X1)
                (SBITSETP X2)
                (SBITSET-PAIRP Y1))
           (not (MEMBER-EQUAL (SBITSET-PAIR-BADGUY X1 Y1)
                              (SBITSET-MEMBERS X2))))
  :hints(("Goal"
          :use ((:instance m4
                           (elem (SBITSET-PAIR-BADGUY X1 Y1))
                           (a x1)
                           (x x2)))
          :in-theory (e/d (;sbitset-members
                                  )
                                 (;sbitset-pair-members
                                  m4
                                  in-of-sbitset-pair-members
                                  equal-of-sbitset-pairs
                                  MEMBER-EQUAL-SBITSET-PAIR-MEMBERS
                                  car-cdr-elim
                                  )))))



Subgoal *1/5.1.3'5'
(IMPLIES (AND (SBITSET-PAIRP A)
              (SBITSET-PAIRP B)
              (SBITSETP X)
              (NOT (EQUAL A B))
              (< (SBITSET-PAIR-OFFSET A)
                 (SBITSET-PAIR-OFFSET (CAR X)))
              (MEMBER-EQUAL (SBITSET-PAIR-BADGUY A B)
                            (SBITSET-MEMBERS X)))
         (NOT (MEMBER-EQUAL (SBITSET-PAIR-BADGUY A B)
                            (SBITSET-PAIR-MEMBERS B))))

Subgoal *1/5.1.2.3''
(IMPLIES (AND (NOT (EQUAL X1 Y1))
              (SBITSET-PAIRP X1)
              (SBITSET-PAIRP Y1)
              (SBITSETP Y2)
              (< (SBITSET-PAIR-OFFSET Y1)
                 (SBITSET-PAIR-OFFSET (CAR Y2)))
              (MEMBER-EQUAL (SBITSET-PAIR-BADGUY X1 Y1)
                            (SBITSET-PAIR-MEMBERS X1)))
         (NOT (MEMBER-EQUAL (SBITSET-PAIR-BADGUY X1 Y1)
                            (SBITSET-MEMBERS Y2))))

Subgoal *1/5.1.2.2
(IMPLIES (AND (NOT (EQUAL X1 Y1))
              (SBITSET-PAIRP X1)
              (SBITSETP X2)
              (< (SBITSET-PAIR-OFFSET X1)
                 (SBITSET-PAIR-OFFSET (CAR X2)))
              (SBITSET-PAIRP Y1)
              (SBITSETP Y2)
              (< (SBITSET-PAIR-OFFSET Y1)
                 (SBITSET-PAIR-OFFSET (CAR Y2)))
              (MEMBER-EQUAL (SBITSET-PAIR-BADGUY X1 Y1)
                            (SBITSET-MEMBERS X2)))
         (NOT (MEMBER-EQUAL (SBITSET-PAIR-BADGUY X1 Y1)
                            (SBITSET-MEMBERS Y2))))

(defthm sbitset-badguy-correct
  (let ((elem (sbitset-badguy x y)))
    (implies (and (sbitsetp x)
                  (sbitsetp y)
                  elem)
             (not (iff (member elem (sbitset-members x))
                       (member elem (sbitset-members y))))))
  :hints(("goal"
          :induct (sbitset-badguy x y)
          :in-theory (disable member-equal-sbitset-pair-members
                              equal-of-sbitset-pairs)
          :do-not '(generalize fertilize)
          :do-not-induct t))
  :otf-flg t)



(defund sbitset-

(local (in-theory (disable double-containment)))

(defthm c0
  (IMPLIES (AND (NOT (EQUAL (SBITSET-FIND offset X)
                            (SBITSET-FIND offset Y)))
                (SBITSETP X)
                (SBITSETP Y)
                (NOT (EQUAL X Y)))
           (not (equal (sbitset-members x)
                       (sbitset-members y))))
  :hints(("Goal" :in-theory (enable sbitset-members))))

(defthm crux
  (implies (and (sbitsetp x)
                (sbitsetp y)
                (not (equal x y)))
           (not (equal (sbitset-members x)
                       (sbitset-members y))))
  :hints(("Goal"
          :in-theory (disable sbitset-badguy-correct)
          :use ((:instance sbitset-badguy-correct)))))
           in-of-sbitset-members

(defthmd equal-sbitsets-by-membership
  (implies (and (sbitsetp x)
                (sbitsetp y))
           (equal (equal x y)
                  (equal (sbitset-members x)
                         (sbitset-members y))))
  :hints(("Goal"
          :in-theory (disable set::double-containment))))
          :use ((:instance sbitset-badguy-correct
                           (x x) (y y)))
                 equal-by-logbitp
                 (logbitp-hyp (lambda ()
                                (and (natp x)
                                     (natp y)
                                     (equal (sbitset-members x)
                                            (sbitset-members y)))))
                 (logbitp-lhs (lambda () x))
                 (logbitp-rhs (lambda () y))))))))


||#
