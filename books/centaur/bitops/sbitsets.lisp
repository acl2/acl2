; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "bits-between")
(include-book "misc/definline" :dir :system)
(local (include-book "equal-by-logbitp"))
(local (include-book "ihs-extensions"))
(local (include-book "../misc/equal-sets"))
(local (include-book "unicode/revappend" :dir :system))
(local (include-book "unicode/rev" :dir :system))
(local (include-book "unicode/append" :dir :system))
(local (include-book "arithmetic-3/extra/top-ext" :dir :system))

(local (in-theory (disable cancel-mod-+)))


(defxdoc sbitsets
  :parents (bitops)
  :short "Sparse bitsets library: an alternative to @(see bitsets) for
representing finite sets of natural numbers."

  :long "<h3>Introduction</h3>

<p>In the ordinary @(see bitset) library, sets of natural numbers are encoded
as bignums.  This is perfectly fine when the set elements are relatively small,
but it is not an efficient way to deal with sets of large numbers.  For
instance, trying to insert a number like 2^30 into an ordinary bitset will
probably kill your Lisp.</p>

<p>Sparse bitsets are a more forgiving alternative.  They can handle very large
set elements, but still achieve bitset-like efficiencies in many cases.</p>

<p>Sparse bitsets are represented as ordered lists of <tt>(offset . block)</tt>
pairs.  Loosely speaking, each such pair in the set <tt>X</tt> means that:</p>

<code>
  offset*blocksize + 0             \\in X  iff  (logbitp 0 block)
  offset*blocksize + 1             \\in X  iff  (logbitp 1 block)
    ...
  offset*blocksize + (blocksize-1) \\in X  iff  (logbitp (blocksize-1) block)
</code>

<p>The <tt>blocksize</tt> is a some constant determined by @(see
*sbitset-block-size*).  We'll assume it is 60 (which makes each <tt>block</tt>
a fixnum on 64-bit CCL).</p>

<h4>Efficiency Considerations</h4>

<p>Sparse bitsets are essentially a hybrid of ordered sets and bitsets, and
their efficiency characteristics are very data dependent.</p>

<p>Sparse bitsets perform best on sets that have \"clusters\" of nearby
members, perhaps separated by wide gaps.  Here, sparse bitsets give you some of
the same benefits of bitsets, viz. word-at-a-time operations like union and the
space efficiency of using bit masks to represent the set members.</p>

<p>For completely dense sets, e.g., all integers in <tt>[0, 1000]</tt>, sparse
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
would be encoded as <tt>((0 . 1) (1 . 1) (2 . 1))</tt>, which is similar to its
ordered set representation except for the additional overhead of using <tt>(1
. 1)</tt> to represent 60, etc.</li>

</ul>


<h3>Using Sparse Bitsets</h3>

<p>The sbitsets library can be loaded with:</p>

<code>
  (include-book \"bitops/sbitsets\" :dir :cbooks)
</code>

<p>Valid sparse bitsets are recognized by @(see sbitsetp), and there is a
standard fixing function, @(see sbitset-fix).</p>

<p>We intend to implement sparse analogues for all of the functions in the
@(see bitsets) library, but at the moment only @(see sbitset-members), @(see
sbitset-singleton), and @(see sbitset-union) are finished.</p>

<p>The reasoning strategy is also the same as with bitsets: we cast everything
in terms of @(see sbitset-members) instead of reasoning about the actual set
representation.</p>")


(defsection *sbitset-block-size*
  :parents (sbitsets)
  :short "Size of each block in an sparse bitset."

  :long "<p>The block size can be any positive number, but for good performance
you probably want to use the maximal number such that:</p>

<code>
 (fixnump (1- (expt 2 *sbitset-block-size*))) = T
</code>

<p>On CCL and SBCL, 60 is the right number.  For other Lisps, 60 is logically
fine, but other numbers may give you better performance.</p>

<p>Note: if you change this, you may wish to also write a corresponding,
optimized version of @(see sbitset-pair-members).</p>"

  (defconst *sbitset-block-size* 60))


(local
 (encapsulate
   ()
   (local (defthm l0
            (implies (and (integerp a)
                          (natp size)
                          (<= (* size offset) a)
                          (< a (+ size (* size offset)))
                          (natp offset))
                     (equal (+ a (* (- size) offset))
                            (mod a size)))))

   (make-event
    `(defthm mod-blocksize-nonsense
       (implies (and (integerp a)
                     (<= (* ,*sbitset-block-size* offset) a)
                     (< a (+ ,*sbitset-block-size* (* ,*sbitset-block-size* offset)))
                     (natp offset))
                (equal (+ a (* ,(- *sbitset-block-size*) offset))
                       (mod a ,*sbitset-block-size*)))))))



(local (in-theory (disable logbitp-when-too-small
                           expt-between-one-and-two
                           expt-is-increasing-for-base->-1
                           expt-2-monotonic)))

(local (in-theory (disable assoc-append)))

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
         (implies (sets::setp x)
                  (iff (member-equal a x)
                       (sets::in a x)))
         :hints(("Goal" :in-theory (enable sets::in-to-member)))))

(local
 (make-event
  `(defthm expt-2-monotonic-specialized-for-block-size
     (implies (and (< a ,*sbitset-block-size*)
                   (natp a))
              (< (expt 2 a) ,(expt 2 *sbitset-block-size*)))
     :hints(("Goal" :use ((:instance expt-2-monotonic
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
                     (equal (sets::<< a b)
                            (< a b)))
            :hints(("Goal" :in-theory (enable sets::<< lexorder alphorder)))))

   (defthm setp-of-add-to-each
     (implies (and (integerp offset)
                   (integer-listp x)
                   (sets::setp x))
              (sets::setp (add-to-each offset x)))
     :hints(("Goal" :in-theory (enable* (:ruleset sets::primitive-rules)
                                        add-to-each))))))



(local
 (defsection no-duplicatesp-equal-when-setp

   (local (defthm l0
            (implies (and (member-equal a x)
                          (sets::<< a (car x)))
                     (not (sets::setp x)))
            :hints(("Goal"
                    :induct (len x)
                    :in-theory (enable* (:ruleset sets::primitive-rules)
                                        (:ruleset sets::order-rules))))))

   (defthm no-duplicatesp-equal-when-setp
     (implies (sets::setp x)
              (no-duplicatesp-equal x))
     :hints(("Goal" :in-theory (enable* (:ruleset sets::primitive-rules)))))))


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
                     (equal (sets::<< a b)
                            (< a b)))
            :hints(("Goal" :in-theory (enable sets::<< lexorder alphorder)))))

   (local (defthm l2
            (implies (and (integer-listp x)
                          (sets::setp x))
                     (equal (min-int x)
                            (if (consp x)
                                (car x)
                              nil)))
            :hints(("Goal" :in-theory (enable* (:ruleset sets::primitive-rules))))))

   (defthmd setp-of-append
     (implies (and (force (or (< (max-int x) (min-int y))
                              (atom x)
                              (atom y)))
                   (force (integer-listp x))
                   (force (integer-listp y))
                   (force (sets::setp x))
                   (force (sets::setp y)))
              (sets::setp (append x y)))
     :hints(("Goal" :in-theory (enable* (:ruleset sets::primitive-rules)))))

   (local (in-theory (enable setp-of-append)))

   (local (defthm in-of-append
            (implies (and (force (or (< (max-int x) (min-int y))
                                     (atom x)
                                     (atom y)))
                          (force (integer-listp x))
                          (force (integer-listp y))
                          (force (sets::setp x))
                          (force (sets::setp y)))
                     (equal (sets::in a (append x y))
                            (or (sets::in a x)
                                (sets::in a y))))
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
                   (force (sets::setp x))
                   (force (sets::setp y)))
              (equal (append x y)
                     (sets::union x y))))))



(local
 (defsection consp-of-bits-between

   (local (defthm l1
            (implies (posp x)
                     (logbitp (logbitp-mismatch x 0) x))
            :hints(("Goal"
                    :in-theory (disable logbitp-mismatch-correct)
                    :use ((:instance logbitp-mismatch-correct
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
                    :in-theory (disable integer-length-bounded-by-expt)
                    :use ((:instance integer-length-bounded-by-expt (a x)))))))

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



(defsection sbitset-blockp
  :parents (sbitsets)
  :short "@(call sbitset-blockp) recognizes numbers that are valid as the
<i>block</i> component of an @(see sbitset-pairp)."

  :long "<p>To ensure that sparse bitsets are canonical, we don't allow 0 as a
valid block.  The idea is that any block whose value is 0 should just be
omitted from the set.</p>"

  (defmacro the-sbitset-block (x)
    `(the (unsigned-byte ,*sbitset-block-size*) ,x))

  (make-event
   `(definlined sbitset-blockp (x)
      (declare (xargs :guard t))
      (mbe :logic (and (posp x)
                       (< x (expt 2 *sbitset-block-size*)))
           :exec (and (integerp x)
                      (<= 1 x)
                      (<= x ,(1- (expt 2 *sbitset-block-size*)))))))

  (local (in-theory (enable sbitset-blockp)))

  (defthm sbitset-block-type
    (implies (sbitset-blockp x)
             (posp x))
    :rule-classes :compound-recognizer)

  (defthm sbitset-block-upper-bound
    (implies (sbitset-blockp x)
             (< x (expt 2 *sbitset-block-size*)))))



(defsection sbitset-pairp
  :parents (sbitsets)
  :short "@(call sbitset-pairp) recognizes a valid <tt>(offset . block)</tt>
pair for sparse bitsets."

  (definline sbitset-pairp (x)
    (declare (xargs :guard t))
    (and (consp x)
         (natp (car x))
         (sbitset-blockp (cdr x))))

  (definline sbitset-pair (offset block)
    (declare (xargs :guard (and (natp offset)
                                (sbitset-blockp block))))
    (cons offset block))

  (definline sbitset-pair-offset (x)
    (declare (xargs :guard (sbitset-pairp x)))
    (car x))

  (definline sbitset-pair-block (x)
    (declare (xargs :guard (sbitset-pairp x)))
    (cdr x))

  (defthm sbitset-pair-offset-of-sbitset-pair
    (equal (sbitset-pair-offset (sbitset-pair offset block))
           offset))

  (defthm sbitset-pair-block-of-sbitset-pair
    (equal (sbitset-pair-block (sbitset-pair offset block))
           block))

  (defthm consp-when-sbitset-pairp
    (implies (sbitset-pairp x)
             (consp x))
    :rule-classes :compound-recognizer)

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

  (defthm sbitset-blockp-of-sbitset-pair-block
    (implies (force (sbitset-pairp x))
             (sbitset-blockp (sbitset-pair-block x))))

  (defthm sbitset-pairp-of-sbitset-pair
    (implies (and (force (natp offset))
                  (force (sbitset-blockp block)))
             (sbitset-pairp (sbitset-pair offset block))))

  (in-theory (disable sbitset-pair
                      sbitset-pairp
                      sbitset-pair-offset
                      sbitset-pair-block)))



(defsection sbitset-pair-members
  :parents (sbitset-members)
  :short "@(call sbitset-pair-members) extracts the members of a single @(see
sbitset-pair)."

  :long "<p>For instance, if the pair is <tt>(0 . 7)</tt>, we produce the set
<tt>{0, 1, 2}</tt>; if the set is <tt>(1 . 7)</tt>, we produce <tt>{60, 61,
62}</tt>.</p>

<p>This serves as the logical definition we use to reason about member
extraction.</p>

<p>Normally this function isn't executed.  When the block size is 32 or 60, we
can instead use the optimized @(see bits-0-31) or @(see 60bits-0-59) routines
instead.  But, if you change the block size to something else, this function
<b>will</b> be executed and its performance will probably be bad.  In this
case, you might want to write a custom <tt>bits-0-32</tt> style routine for
your block size.</p>"

  (defund sbitset-pair-members (x)
    (declare (xargs :guard (sbitset-pairp x)))
    (add-to-each (* (sbitset-pair-offset x) *sbitset-block-size*)
                 (bits-between 0 *sbitset-block-size* (sbitset-pair-block x))))

  (local (in-theory (enable sbitset-pair-members)))

  (local (in-theory (disable cancel-mod-+))) ;; loops

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
    :hints((witness)))

  (defthm consp-of-sbitset-pair-members
    (implies (force (sbitset-pairp x))
             (and (true-listp (sbitset-pair-members x))
                  (consp (sbitset-pair-members x))))
    :rule-classes :type-prescription)

  (defthm setp-of-sbitset-pair-members
    (implies (force (sbitset-pairp a))
             (sets::setp (sbitset-pair-members a))))

  (defthm in-of-sbitset-pair-members
    (implies (force (sbitset-pairp x))
             (equal (sets::in a (sbitset-pair-members x))
                    (and (natp a)
                         (equal (floor a *sbitset-block-size*)
                                (sbitset-pair-offset x))
                         (logbitp (mod a *sbitset-block-size*)
                                  (sbitset-pair-block x)))))
    :hints(("Goal" :use ((:instance member-equal-is-in
                                    (x (sbitset-pair-members x)))))))

  (defthm empty-of-sbitset-pair-members
    (implies (force (sbitset-pairp x))
             (not (sets::empty (sbitset-pair-members x))))
    :hints(("Goal" :in-theory (e/d* ((:ruleset sets::primitive-rules))
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



(defsection sbitsetp
  :parents (sbitsets)
  :short "@(call sbitsetp) determines whether <tt>X</tt> is a well-formed
sparse bitset."

  (defund sbitsetp (x)
    (declare (xargs :guard t))
    (if (atom x)
        (not x)
      (and (sbitset-pairp (first x))
           (if (atom (cdr x))
               (not (cdr x))
             (and (sbitset-pairp (second x))
                  (< (sbitset-pair-offset (first x))
                     (sbitset-pair-offset (second x)))))
           (sbitsetp (cdr x)))))

  (local (in-theory (enable sbitsetp)))

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



(defsection sbitset-fix
  :parents (sbitsets)
  :short "@(call sbitset-fix) is a basic fixing function for sparse bitsets."

  (definlined sbitset-fix (x)
    (declare (xargs :guard (sbitsetp x)))
    (mbe :logic (if (sbitsetp x) x nil)
         :exec x))

  (local (in-theory (enable sbitset-fix)))

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
        (,(if fn 'definlined 'defund) sbitset-members-aux (x)
         (declare (xargs :guard (sbitsetp x)
                         :verify-guards nil))
         ,real-body)
        (local (in-theory (enable sbitset-members-aux)))
        ,remove-thm
        (verify-guards sbitset-members-aux))))

  (definlined sbitset-members (x)
    (declare (xargs :guard (sbitsetp x)
                    :verify-guards nil))
    (mbe :logic (if (or (not (sbitsetp x))
                        (atom x))
                    nil
                  (sets::union (sbitset-pair-members (car x))
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
             (implies (sets::setp (append x y))
                      (and (sets::setp (list-fix x))
                           (sets::setp y)))
             :hints(("Goal" :in-theory (enable* (:ruleset sets::primitive-rules))))))

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
             (sets::setp (sbitset-members-aux x))
             :hints(("Goal" :in-theory (enable setp-of-append)))))

    (local (defthm l5
             (equal (sbitset-members-aux x)
                    (if (or (atom x)
                            (not (sbitsetp x)))
                        nil
                      (sets::union (sbitset-pair-members (car x))
                                   (sbitset-members-aux (cdr x)))))
             :rule-classes :definition
             :hints(("Goal" :in-theory (e/d (append-is-union)
                                            (sets::double-containment))))))

    (defthm sbitset-members-aux-removal
      (equal (sbitset-members-aux x)
             (sbitset-members x)))

    (verify-guards sbitset-members))


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
                    (equal (sets::setp x)
                           (not x)))
           :hints(("Goal" :in-theory (enable sets::setp)))))

  (local (defthm union-under-iff
           (iff (sets::union x y)
                (or (not (sets::empty x))
                    (not (sets::empty y))))
           :hints(("Goal" :in-theory (enable* (:ruleset sets::primitive-rules))))))

  (defthm sbitset-members-of-cons
    (implies (force (sbitsetp (cons a x)))
             (equal (sbitset-members (cons a x))
                    (sets::union (sbitset-pair-members a)
                                 (sbitset-members x)))))

  (defthm sbitset-members-of-sbitset-fix
    (equal (sbitset-members (sbitset-fix b))
           (sbitset-members b))
    :hints(("Goal" :in-theory (enable sbitset-fix))))

  (defthm true-listp-of-sbitset-members
    (true-listp (sbitset-members x))
    :rule-classes :type-prescription)

  (defthm setp-of-sbitset-members
    (sets::setp (sbitset-members x)))

  (defthm no-duplicatesp-equal-of-sbitset-members
    (no-duplicatesp-equal (sbitset-members x))))



(defsection sbitset-find

; Helper for in-of-sbitset-members; shouldn't be needed by users.

  (defund sbitset-find (offset x)
    (declare (xargs :guard (and (natp offset)
                                (sbitsetp x))))
    (cond ((atom x)
           nil)
          ((equal (sbitset-pair-offset (car x)) offset)
           (car x))
          (t
           (sbitset-find offset (cdr x)))))

  (local (in-theory (enable sbitset-find)))

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

; Analogue of "in-of-bitset-members."
;
; This is a little more complicated than in the basic bitset library, because
; we have to go to the proper pair.
;
; This theorem is disabled by default and most users shouldn't enable it.  It's
; only needed to prove properties about the basic sbitset constructors.

  (local (defthm l0
           (implies (and (sbitsetp x)
                         (sets::in a (sbitset-members x)))
                    (sbitset-find (floor a *sbitset-block-size*) x))
           :hints(("Goal"
                   :in-theory (disable mod-blocksize-nonsense)
                   :induct (len x)))))

  (local (defthm l1
           (implies (and (sbitsetp x)
                         (< offset (sbitset-pair-offset (car x))))
                    (not (sbitset-find offset x)))
           :hints(("Goal" :in-theory (enable sbitset-find)))))

  (local (defthm l2
           (implies (and (sbitset-pairp x)
                         (sets::in a (sbitset-pair-members x)))
                    (equal (sbitset-pair-offset x)
                           (floor a *sbitset-block-size*)))))

  (local (defthm l3
           (implies (sbitsetp x)
                    (equal (sets::in a (sbitset-members x))
                           (let ((pair (sbitset-find (floor a *sbitset-block-size*) x)))
                             (and pair
                                  (sets::in a (sbitset-pair-members pair))))))
           :hints(("Goal"
                   :induct (len x)
                   :in-theory (disable in-of-sbitset-pair-members)
                   :do-not '(generalize fertilize)))))

  (defthmd in-of-sbitset-members
    (equal (sets::in a (sbitset-members x))
           (and (sbitsetp x)
                (let ((pair (sbitset-find (floor a *sbitset-block-size*) x)))
                  (and pair
                       (sets::in a (sbitset-pair-members pair))))))
    :hints(("Goal" :use ((:instance l3))))))


(local (in-theory (enable in-of-sbitset-members)))



; -----------------------------------------------------------------------------
;
;                           BASIC SBITSET OPERATIONS
;
; -----------------------------------------------------------------------------

(defsection sbitset-singleton-pair
  :parents (sbitset-singleton)
  :short "@(call sbitset-singleton-pair) creates a @(see sbitset-pairp) whose
only member is <tt>a</tt>."

  (local (in-theory (enable sbitset-blockp)))

  (make-event
   `(definlined sbitset-singleton-pair (a)
      (declare (xargs :guard (natp a)
                      :guard-hints(("Goal" :in-theory (enable sbitset-blockp)))))
      (mbe :logic
           (let ((a (nfix a)))
             (sbitset-pair (floor a *sbitset-block-size*)
                           (expt 2 (mod a *sbitset-block-size*))))
           :exec
           (sbitset-pair (truncate a ,*sbitset-block-size*)
                         (ash 1 (rem a ,*sbitset-block-size*))))))

  (local (in-theory (enable sbitset-singleton-pair)))

  (defthm sbitset-pairp-of-sbitset-singleton-pair
    (sbitset-pairp (sbitset-singleton-pair a)))

  (defthm sbitset-pair-offset-of-sbitset-singleton-pair
    (equal (sbitset-pair-offset (sbitset-singleton-pair a))
           (floor (nfix a) *sbitset-block-size*)))

  (defthm sbiset-pair-block-of-sbitset-singleton-pair
    (equal (sbitset-pair-block (sbitset-singleton-pair a))
           (expt 2 (mod (nfix a) *sbitset-block-size*)))))


(defsection sbitset-singleton
  :parents (sbitsets)
  :short "@(call sbitset-singleton) constructs the singleton set <tt>{a}</tt>."

  (definlined sbitset-singleton (a)
    (declare (xargs :guard (natp a)))
    (list (sbitset-singleton-pair a)))

  (local (in-theory (enable sbitset-singleton)))

  (defthm sbitsetp-of-sbitset-singleton
    (sbitsetp (sbitset-singleton a)))

  (local (defthm l0
           (equal (sets::in a (sbitset-members (sbitset-singleton b)))
                  (equal a (nfix b)))))

  (defthm sbitset-members-of-sbitset-singleton
    (equal (sbitset-members (sbitset-singleton a))
           (sets::insert (nfix a) nil))
    :hints(("Goal" :in-theory (disable sbitset-singleton)))))



(defsection sbitset-union
  :parents (sbitsets)
  :short "@(call sbitset-union) constructs the set <tt>X U Y</tt>."

  (defthm sbitset-blockp-of-logior
    (implies (and (force (sbitset-blockp x))
                  (force (sbitset-blockp y)))
             (sbitset-blockp (logior x y)))
    :hints(("Goal"
            :in-theory (e/d (sbitset-blockp)
                            (upper-bound-of-logior-for-naturals))
            :use ((:instance upper-bound-of-logior-for-naturals
                             (x x)
                             (y y)
                             (n *sbitset-block-size*))))))

  (defund sbitset-union-exec (x y)
    (declare (xargs :guard (and (sbitsetp x)
                                (sbitsetp y))
                    :measure (+ (len x) (len y))))
    (b* (((when (atom x)) y)
         ((when (atom y)) x)
         (x1 (car x))
         (y1 (car y))
         (x1.offset (sbitset-pair-offset x1))
         (y1.offset (sbitset-pair-offset y1))
         ((when (= x1.offset y1.offset))
          (b* ((x1.block (sbitset-pair-block x1))
               (y1.block (sbitset-pair-block y1))
               (new-block (the-sbitset-block
                           (logior (the-sbitset-block x1.block)
                                   (the-sbitset-block y1.block))))
               (new-pair (sbitset-pair x1.offset new-block)))
            (cons new-pair (sbitset-union-exec (cdr x) (cdr y)))))
         ((when (< x1.offset y1.offset))
          (cons x1 (sbitset-union-exec (cdr x) y))))
      (cons y1 (sbitset-union-exec x (cdr y)))))

  (definlined sbitset-union (x y)
    (declare (xargs :guard (and (sbitsetp x)
                                (sbitsetp y))))
    (mbe :logic (sbitset-union-exec (sbitset-fix x)
                                    (sbitset-fix y))
         :exec (sbitset-union-exec x y)))

  (local (in-theory (enable sbitset-union-exec)))

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


  (local (defthm equal-of-sbitset-pair
           (implies (force (sbitset-pairp x))
                    (equal (equal (sbitset-pair offset block) x)
                           (and (equal offset (sbitset-pair-offset x))
                                (equal block (sbitset-pair-block x)))))
           :hints(("Goal" :in-theory (enable sbitset-pair
                                             sbitset-pairp
                                             sbitset-pair-offset
                                             sbitset-pair-block)))))

  (local (defthm l0
           (implies (and (sbitsetp x)
                         (sbitsetp y))
                    (iff (sbitset-find offset (sbitset-union-exec x y))
                         (or (sbitset-find offset x)
                             (sbitset-find offset y))))
           :hints(("Goal"
                   :induct (sbitset-union-exec x y)
                   :in-theory (enable sbitset-union-exec)))))

  (local (defthm l1
           (implies (and (sbitset-find b x)
                         (<= b a)
                         (sbitsetp x))
                    (<= (sbitset-pair-offset (car x)) a))
           :rule-classes ((:rewrite) (:linear))
           :hints(("goal"
                   :in-theory (enable sbitset-find)
                   :do-not '(generalize fertilize)))))

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
                    (equal (sets::in a (sbitset-members (sbitset-union-exec x y)))
                           (or (sets::in a (sbitset-members x))
                               (sets::in a (sbitset-members y)))))))

  (defthm sbitset-members-of-sbitset-union-exec
    ;; Just by double-containment.
    (implies (and (sbitsetp x)
                  (sbitsetp y))
             (equal (sbitset-members (sbitset-union-exec x y))
                    (sets::union (sbitset-members x)
                                 (sbitset-members y)))))

  ;; And now we just get rid of the hyps, with the fixing function.

  (local (in-theory (enable sbitset-union)))

  (defthm sbitset-of-sbitset-union
    (sbitsetp (sbitset-union x y)))

  (defthm sbitset-members-of-sbitset-union
    (equal (sbitset-members (sbitset-union x y))
           (sets::union (sbitset-members x)
                        (sbitset-members y)))))



