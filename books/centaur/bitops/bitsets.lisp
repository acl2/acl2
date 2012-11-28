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
(include-book "equal-by-logbitp")   ;; for logbitp-mismatch for witness stuff
(include-book "misc/definline" :dir :system)
(include-book "../misc/witness-cp")
(local (include-book "ihs-extensions"))
(local (include-book "arithmetic-3/top" :dir :system))


(defxdoc bitsets
  :parents (bitops)
  :short "Bitsets library: uses bitmasks to represent finite sets of (small)
natural numbers."

  :long "<h3>Introduction</h3>

<p>In this library, sets of natural numbers are represented as natural numbers
by saying @('a') is a member of the set @('X') when @('(@(see logbitp) a X)').
For instance, the set {1, 2, 4} would be represented as the number 22.  In
binary, this number is 10110, and you can see that bits 1, 2, and 4 are each
\"true\".</p>

<p>This representation enjoys certain efficiencies.  In particular, operations
like union, intersection, difference, and subset testing can be carried out in
a \"word at a time\" fashion with bit operations.</p>

<p>But bitsets are only appropriate for sets whose elements are reasonably
small numbers since the space needed to represent a bitset is determined by its
maximal element.  If your sets contain extremely small numbers---less than
28-60, depending on the Lisp---then they can be represented as fixnums and the
bitset operations will be remarkably efficient.</p>

<p>Beyond this, bignums are necessary.  Even though bignum operations are
generally involve memory allocation and are much slower than fixnum operations,
using bignums to represent sets can still be very efficient.  For instance, on
64-bit CCL, bignums are represented as a header/data pair where the data is an
array of 32-bit words; operations like @(see logand) can smash together the two
data arrays a word at a time.</p>

<p>Let's define the <i>density</i> of a set as its cardinality divided by its
maximal element plus one (to account for zero-indexing).  Under this
definition, the set {1, 2, 4} has a density of 60%, whereas {96, 97, 98} has a
density of 3%.</p>

<p>Without destructive updates, you probably can't do much better than bitsets
for dense sets.  But bitsets are not good at representing sparse sets.  For
instance, you would need 8 KB of memory just to represent the singleton set
{65536}.</p>

<p>The <see topic=\"@(url sbitsets)\">sparse bitsets</see> library is an
alternative to bitsets that uses lists of @('(offset . data)') pairs instead of
ordinary natural numbers as the set representation.  This representation is
perhaps somewhat less efficient for dense sets, but is far more efficient for
sparse sets (e.g., {65536} can be represented with a single cons of fixnums
instead of an 8 KB bignum.) and still provides word-at-a-time operations in
many cases.</p>


<h3>Loading the Library</h3>

<p>The basic bitsets library can be loaded with:</p>

@({
 (include-book \"bitops/bitsets\" :dir :cbooks)
})

<p>An optimized version (that requires additional ttags) can be loaded with:</p>

@({
 (include-book \"bitops/bitsets-opt\" :dir :cbooks)
})


<h3>Using the Library</h3>

<p>Convention:</p>

<ul>

<li>@('a, b, ...') denote set elements</li>

<li>@('X, Y, ...') denote sets.</li>

</ul>

<p>There is no such explicit @('bitsetp') recognizer; instead we just use
@('natp').  Similarly there is no separate bitset-fixing function because we
just use @('nfix').</p>

<h5>Bitset Constructors</h5>

<dl> <dt>@('(@(see bitset-singleton) a)')</dt> <dd>Constructs the set @('{ a
}')</dd> <dd>Execution: @('(ash 1 a)')</dd>

<dt>@('(@(see bitset-insert) a X)')</dt>
<dd>Constructs the set @('X U {a}')</dd>
<dd>Execution: @('(logior (ash 1 a) x)')</dd>

<dt>@('(@(see bitset-list) a b ...)')</dt>
<dd>Constructs the set @('{a, b, ...}')</dd>
<dd>Execution: repeated @('bitset-insert')s</dd>

<dt>@('(@(see bitset-list*) a b ... X)')</dt>
<dd>Constructs the set @('X U {a, b, ...}')</dd>
<dd>Execution: repeated @('bitset-insert')s</dd>

<dt>@('(@(see bitset-delete) a X)')</dt>
<dd>Constructs the set @('X - {a}')</dd>
<dd>Execution: @('(logandc1 (ash 1 a) x)')</dd>

<dt>@('(@(see bitset-union) X Y)')</dt>
<dd>Constructs the set @('X U Y')</dd>
<dd>Execution: @('(logior x y)')</dd>

<dt>@('(@(see bitset-intersect) X Y)')</dt>
<dd>Constructs the set @('X \\intersect Y')</dd>
<dd>Execution: @('(logand x y)')</dd>

<dt>@('(@(see bitset-difference) X Y)')</dt>
<dd>Constructs the set @('X - Y')</dd>
<dd>Execution: @('(logandc1 y x)')</dd>
</dl>

<h5>Inspecting Bitsets</h5>

<dl>
<dt>@('(@(see bitset-memberp) a X)')</dt>
<dd>Determine whether @('a') is a member of the set @('X')</dd>
<dd>Execution: @('(logbitp a x)')</dd>

<dt>@('(@(see bitset-intersectp) X Y)')</dt>
<dd>Determines whether @('X') and @('Y') have any common members</dd>
<dd>Execution: @('(logtest x y)')</dd>

<dt>@('(@(see bitset-subsetp) X Y)')</dt>
<dd>Determines whether @('X') is a subset of @('Y')</dd>
<dd>Execution: @('(= 0 (logandc2 y x))')</dd>

<dt>@('(@(see bitset-cardinality) X)')</dt>
<dd>Determines the cardinality of @('X')</dd>
<dd>Execution: @('(logcount x)')</dd>

</dl>

<h5>Enumerating Bitset Members</h5>

<dl>
<dt>@('(@(see bitset-members) X)')</dt>
<dd>Constructs an ordinary ordered set with the elements of X.</dd>
<dd>Expensive: must cons together all of the set elements.</dd>
</dl>


<h3>Reasoning about Bitsets</h3>

<p>The library tries to shield you from ever having to reason about bitwise
arithmetic operations.  Instead, you should be able to carry out all of your
reasoning on the level of sets.  To achieve this, we try to cast everything in
terms of @(see bitset-members).</p>


<h4>Basic Approach</h4>

<p>If you want to reason about some bitset-producing function @('foo'), then
you should typically try to write your theorems about:</p>

@({
 (bitset-members (foo ...))
})

<p>instead of directly proving something about:</p>

@({
 (foo ...)
})

<p>For example, to reason about @(see bitset-union) we prove:</p>

@(thm natp-of-bitset-union)
@(thm bitset-members-of-bitset-union)

<p>In most cases, the above theorems are sufficient for reasoning about the
behavior of @('bitset-union').</p>

<p>Note that once you have defined a bitset-producing function, you may wish to
add it to the table @('bitset-fns') so that the witnessing hints (below) will
understand that they produce bitsets.</p>


<h4>Equivalence Proofs</h4>

<p>The @('bitset-members') approach is good most of the time, but in some cases
you may wish to show that two bitset-producing functions literally create the
same bitset.  That is, instead of showing:</p>

@({
 (bitset-members (foo ...)) = (bitset-members (bar ...))
})

<p>it is perhaps better to prove:</p>

@({
 (foo ...) = (bar ...)
})

<p>It should be automatic to prove this stronger form (after first proving the
weaker form) by adding the hint:</p>

@({
 :hints ((bitset-witnessing))
})

<p>which ties into the witnessing stuff from @('centaur/misc/witness-cp') to
show that bitsets are equal when they have the same members.</p>")



(defsection bitset-members
  :parents (bitsets)
  :short "@(call bitset-members) converts a bitset into an ordinary, ordered
set."

  :long "<p>Reasoning note: @('bitset-members') is fundamental to reasoning
about bitsets; see <i>Reasoning with Bitsets</i> in @(see bitsets).  Its
definition and the theorem @('in-of-bitset-members') should generally be left
disabled since they expose the underlying representation of bitsets.</p>

<p>Performance note: @('bitset-members') is <b>inherently expensive</b>: no
matter how it is implemented, it must create at least @('|X|') conses.  You may
sometimes be able to avoid this cost using functions like @(see
bitset-memberp), @(see bitset-intersectp), or @(see bitset-subsetp)
instead.</p>

<p>It is simple enough to convert a bitset into an ordered set: since the @(see
integer-length) of @('x') gives us an upper bound on its elements, we just need
to walk up to this bound and collect all @('i') such that @('(@(see logbitp) i
x)').</p>

<p>The definition below uses @(see bits-between) to do just this.  However,
note that when the @('bitsets-opt') book is loaded (which requires a ttag), a
more efficient implementation is used; see @(see ttag-bitset-members) for
details.</p>"

  (defund bitset-members (x)
    (declare (xargs :guard (natp x)))
    (mbe :logic
         (let ((x (nfix x)))
           (bits-between 0 (integer-length x) x))
         :exec
         (bits-between 0 (integer-length x) x)))

  (local (in-theory (enable bitset-members)))

  (defthm bitset-members-default
    (implies (not (natp a))
             (equal (bitset-members a)
                    nil)))

  (defthm bitset-members-of-nfix
    (equal (bitset-members (nfix b))
           (bitset-members b)))

  (defthm true-listp-of-bitset-members
    (true-listp (bitset-members x))
    :rule-classes :type-prescription)

  (defthm no-duplicatesp-equal-of-bitset-members
    (no-duplicatesp-equal (bitset-members x)))

  (defthm setp-of-bitset-members
    (sets::setp (bitset-members x)))

  (defthmd in-of-bitset-members
    ;; CAREFUL!  This theorem should typically be left disabled because it
    ;; exposes the underlying representation of the set.  On the other hand,
    ;; it's the main theorem that we use when introducing new "primitive
    ;; functions" for building bitsets (i.e., which build bitsets by exploiting
    ;; the underlying representation).
    (equal (sets::in a (bitset-members x))
           (and (natp a)
                (logbitp a (nfix x)))))

  (encapsulate
    ()
    (local (in-theory (disable bitset-members)))

    (local (defthm l0
             (implies (posp x)
                      (logbitp-mismatch x 0))))

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
                      (bitset-members x))
             :hints(("Goal"
                     :in-theory (enable natp)
                     :use ((:instance in-of-bitset-members
                                      (a (logbitp-mismatch x 0))))))))

    (local (defthm l3
             (implies (not (posp x))
                      (not (bitset-members x)))
             :hints(("Goal" :cases ((equal x 0))))))

    (defthm bitset-members-under-iff
      ;; BOZO proving this is silghtly questionable...
      (iff (bitset-members x)
           (posp x)))))



(defsection bignum-extract
  :parents (ttag-bitset-members)
  :short "Extract a particular 32-bit slice of an integer."

  :long "<p>Logically, @(call bignum-extract) is essentially:</p>

@({
   (logand (ash x (* -32 slice)) (1- (expt 2 32)))
})

<p>What does this do?  Imagine partitioning the integer @('x') into a list of
32-bit slices.  Say that the least-significant 32 bits are the 0th slice, and
so on.  The @('bignum-extract') function is just extracting the @('slice')th
slice of @('x').</p>

<p>The logical definition of @('bignum-extract') is not very efficient; when
@('x') is a bignum, the @('(ash x (* -32 slice))') term will generally require
us to create a new bignum.  In the @('bitsets-opt') book, we develop an
under-the-hood replacement for 64-bit CCL that takes advantage of the
underlying representation of bignums, and essentially implements this function
into an array access.</p>"

  (defund bignum-extract (x slice)
    (declare (xargs :guard (and (integerp x)
                                (natp slice))
                    :verify-guards nil))
    (mbe :logic (let ((x     (ifix x))
                      (slice (nfix slice)))
                  (logand (1- (expt 2 32))
                          (ash x (* -32 slice))))
         :exec (the (unsigned-byte 32)
                    (logand (the (unsigned-byte 32) (1- (expt 2 32)))
                            (ash x (* -32 slice))))))

  (local (in-theory (enable bignum-extract)))

  (defthm natp-of-bignum-extract
    (natp (bignum-extract x slice))
    :rule-classes :type-prescription)

  (defthm unsigned-byte-p-of-bignum-extract
    (unsigned-byte-p 32 (bignum-extract x slice))
    :hints(("Goal"
            :in-theory (disable unsigned-byte-p-of-logand-1)
            :use ((:instance unsigned-byte-p-of-logand-1
                   (n 32)
                   (x (1- (expt 2 32)))
                   (y (ash (ifix x) (* -32 (nfix slice)))))))))

  (make-event
   `(defthm upper-bound-of-bignum-extract
      (< (bignum-extract x slice) ,(expt 2 32))
      :rule-classes :linear
      :hints(("Goal" :use ((:instance unsigned-byte-p-of-bignum-extract))))))

  (verify-guards bignum-extract)

  (local (defthm l0
           (implies (and (natp slice)
                         (integerp x))
                    (equal (bits-between 0 32 (ash x (* -32 slice)))
                           (add-to-each (* -32 slice)
                                        (bits-between (* 32 slice)
                                                      (* 32 (+ 1 slice))
                                                      x))))
           :hints(("Goal"
                   :use ((:instance bits-between-of-right-shift
                                    (n 0)
                                    (m 32)
                                    (k (* -32 slice))))
                   :in-theory (disable bits-between-of-right-shift)))))

  (defthm bits-between-of-bignum-extract
    (implies (and (posp slice)
                  (integerp x))
             (equal (bits-between 0 32 (bignum-extract x slice))
                    (add-to-each (* -32 slice)
                                 (bits-between (* 32 slice)
                                               (* 32 (+ 1 slice))
                                               x))))
    :hints(("Goal"
            :in-theory (e/d (loghead)
                            (bits-between-of-increment-right-index
                             right-shift-to-logtail))))))



(defsection ttag-bitset-members
  :parents (bitset-members)
  :short "Notes about the optimization of @(see bitset-members)."

  :long "<p>The basic version of @('bitset-members') calls @(see bits-between),
which repeatedly indexes into the bitset using @(see logbitp).</p>

<p>We found this wasn't very efficient in 64-bit CCL, and have developed an
alternate implementation that uses:</p>

<ol>

<li>@(see bits-0-31), a partially unrolled version of @(see bits-between) that
is specialized for 32-bit numbers, and</li>

<li>@(see bignum-extract), a function for extracting a 32-bit chunk from a
bignum in a particularly efficient way on 64-bit CCL.</li>

</ol>

<p>Basic performance testing suggests that @('ttag-bitset-members') is almost
5x faster than a regular version.  Here's the testing code I used:</p>

@({
 (include-book \"bitsets\")
 (include-book \"../aig/random-sim\")
 (include-book \"../misc/memory-mgmt-raw\")
 (include-book \"tools/defconsts\" :dir :system)

 (set-max-mem ;; newline to fool dependency scanner
   (* 30 (expt 2 30)))

 (defconsts (*random-data* state)
   (random-list 100000 (ash 1 5000) state))

 (defund bitset-members-list (x)
   (if (atom x)
       nil
     (cons (bitset-members (car x))
           (bitset-members-list (cdr x)))))

 (defund ttag-bitset-members-list (x)
   (if (atom x)
       nil
     (cons (ttag-bitset-members (car x))
           (ttag-bitset-members-list (cdr x)))))

 (progn$
  (gc$)
  (time$ (bitset-members-list *random-data*)
         :msg \"Unoptimized Original: ~st sec, ~sa bytes~%\")
  (gc$)
  (time$ (ttag-bitset-members-list *random-data*)
         :msg \"Unoptimized TTAG: ~st sec, ~sa bytes~%\")
  nil)

 (include-book \"bitsets-opt\")

 (progn$
  (gc$)
  (time$ (bitset-members-list *random-data*)
         :msg \"Optimized Original: ~st sec, ~sa bytes~%\")
  (gc$)
  (time$ (ttag-bitset-members-list *random-data*)
         :msg \"Optimized TTAG: ~st sec, ~sa bytes~%\")
  nil)
})

<p>And the results (on fv-1):</p>

@({
 Unoptimized Original: 17.11 sec, 4,001,845,424 bytes
 Unoptimized TTAG: 14.20 sec, 9,118,513,584 bytes
 Optimized Original: 3.57 sec, 4,001,845,424 bytes
 Optimized TTAG: 3.57 sec, 4,001,845,424 bytes
})"

  (local (in-theory (disable assoc-append)))

  (local (defthm rassoc-append
           (equal (append x (append y z))
                  (append (append x y) z))))

  (local (defthm ash-5-to-times
           (implies (natp x)
                    (equal (ash x 5)
                           (* x 32)))
           :hints(("Goal" :in-theory (enable ash)))))

  (local (defthm ash-minus-5-to-floor
           (implies (natp x)
                    (equal (ash x -5)
                           (floor x 32)))
           :hints(("Goal" :in-theory (enable ash)))))

  (defund ttag-bitset-members-aux (slice x acc)
    ;; Main loop.  We collect the set corresponding to x[0:32*(slice+1)], by
    ;; using our 32-bit collection function on each slice extracted by
    ;; bignum-extract.
    (declare (xargs :guard (and (natp slice)
                                (integerp x))))
    (if (mbe :logic (zp slice)
             :exec (= slice 0))
        (bits-0-31 (ash slice 5)
                   (bignum-extract x slice)
                   acc)
      (ttag-bitset-members-aux (- (lnfix slice) 1)
                               x
                               (bits-0-31 (ash slice 5)
                                          (bignum-extract x slice)
                                          acc))))

  (local (in-theory (enable loghead)))
  (defthm ttag-bitset-members-aux-redef
    (implies (and (natp slice)
                  (integerp x))
             (equal (ttag-bitset-members-aux slice x acc)
                    (append (bits-between 0
                                          (* (+ 1 slice) 32)
                                          x)
                            acc)))
    :hints(("Goal" :in-theory (e/d (ttag-bitset-members-aux bignum-extract)
                                   (right-shift-to-logtail)))))

  (defund ttag-bitset-members (x)
    (declare (xargs :guard (natp x)
                    :guard-hints (("Goal" :in-theory (enable bitset-members)))))
    (mbe :logic (bitset-members x)
         :exec (ttag-bitset-members-aux (ash (integer-length x) -5)
                                        x
                                        nil))))



(defsection bitset-memberp
  :parents (bitsets)
  :short "@(call bitset-memberp) tests whether @('a') is a member of the set
@('X')."

  :long "<p>This is reasonably efficient: it executes as @(see logbitp) and
does not need to use @(see bitset-members).</p>

<p>We prefer to reason about @('(sets::in a (bitset-members X))').  We could
have used this as the @(':logic') definition, but the @(see logbitp)-based
definition should be better for symbolic simulation with @(see GL).</p>"

  (definlined bitset-memberp (a x)
    (declare (xargs :guard (and (natp a)
                                (natp x))))
    (logbitp a (lnfix x)))

  (defthm bitset-memberp-removal
    (equal (bitset-memberp a x)
           (sets::in (nfix a) (bitset-members x)))
    :hints(("Goal" :in-theory (enable bitset-memberp in-of-bitset-members)))))



(defsection bitset-singleton
  :parents (bitsets)
  :short "@(call bitset-singleton) constructs the singleton set @('{a}')."

  :long "<p>This is perhaps slightly more efficient than the equivalent,
 @('(@(see bitset-insert) A 0)').</p>"

  (definlined bitset-singleton (a)
    (declare (xargs :guard (natp a)))
    (ash 1 (lnfix a)))

  (local (in-theory (enable bitset-singleton)))

  (defthm natp-of-bitset-singleton
    (natp (bitset-singleton a))
    :rule-classes :type-prescription)

  (defthm bitset-singleton-when-not-natp
    (implies (not (natp a))
             (equal (bitset-singleton a)
                    (bitset-singleton 0))))

  (defthm bitset-singleton-of-nfix
    (equal (bitset-singleton (nfix a))
           (bitset-singleton a)))

  (encapsulate
    ()
    (local (defthm l0
             (equal (sets::in a (bitset-members (bitset-singleton b)))
                    (equal a (nfix b)))
             ;; Ugh, really bad expt matching...
             :hints(("Goal" :in-theory (e/d (in-of-bitset-members)
                                            ((expt) |(expt x 0)|)))
                    (and stable-under-simplificationp
                         '(:in-theory (enable expt))))))

    (defthm bitset-members-of-bitset-singleton
      (equal (bitset-members (bitset-singleton a))
             (sets::insert (nfix a) nil))
      :hints(("Goal" :in-theory (disable bitset-singleton))))))



(defsection bitset-insert
  :parents (bitsets)
  :short "@(call bitset-insert) constructs the set @('X U {a}')."

  :long "<p>This looks pretty efficient, but keep in mind that it still has to
construct a new set and hence is linear in the size of the set.  You should
probably avoid calling this in a loop if possible; instead consider functions
like @(see bitset-union).</p>"

  (definlined bitset-insert (a x)
    (declare (xargs :guard (and (natp a)
                                (natp x))))
    (logior (ash 1 (lnfix a)) (lnfix x)))

  (local (in-theory (enable bitset-insert)))

  (defthm natp-of-bitset-insert
    (natp (bitset-insert a x))
    :rule-classes :type-prescription)

  (defthm bitset-insert-when-not-natp-left
    (implies (not (natp a))
             (equal (bitset-insert a x)
                    (bitset-insert 0 x))))

  (defthm bitset-insert-when-not-natp-right
    (implies (not (natp x))
             (equal (bitset-insert a x)
                    (bitset-singleton a)))
  :hints(("Goal" :in-theory (enable bitset-singleton))))

  (defthm bitset-insert-of-nfix-left
    (equal (bitset-insert (nfix a) x)
           (bitset-insert a x)))

  (defthm bitset-insert-of-nfix-right
    (equal (bitset-insert a (nfix x))
           (bitset-insert a x)))

  (encapsulate
    ()
    (local (defthm l0
             (equal (sets::in a (bitset-members (bitset-insert b x)))
                    (or (equal a (nfix b))
                        (sets::in a (bitset-members x))))
             :hints(("Goal"
                     :in-theory (e/d (in-of-bitset-members)
                                     ;; Ugh, lousy expt matching
                                     (|(expt x 0)|
                                      |(expt x (if a b c))|))))))

    (defthmd sets::bitset-members-of-bitset-insert
      (equal (bitset-members (bitset-insert a x))
             (sets::insert (nfix a) (bitset-members x)))
      :hints(("Goal" :in-theory (disable bitset-insert))))))



(defsection bitset-delete
  :parents (bitsets)
  :short "@(call bitset-delete) constructs the set @('X - {a}')."

  :long "<p>This looks pretty efficient, but keep in mind that it still has to
construct a new set and hence is linear in the size of the set.  You should
probably avoid calling this in a loop if possible; instead, consider functions
like @(see bitset-intersect) and @(see bitset-difference).</p>"

  (definlined bitset-delete (a x)
    (declare (xargs :guard (and (natp a)
                                (natp x))))
    (logandc1 (ash 1 (lnfix a)) (lnfix x)))

  (local (in-theory (enable bitset-delete)))

  (defthm natp-of-bitset-delete
    (natp (bitset-delete a x))
    :rule-classes :type-prescription)

  (defthm bitset-delete-when-not-natp-left
    (implies (not (natp a))
             (equal (bitset-delete a x)
                    (bitset-delete 0 x))))

  (defthm bitset-delete-when-not-natp-right
    (implies (not (natp x))
             (equal (bitset-delete a x)
                    0)))

  (defthm bitset-delete-of-nfix-left
    (equal (bitset-delete (nfix a) x)
           (bitset-delete a x)))

  (defthm bitset-delete-of-nfix-right
    (equal (bitset-delete a (nfix x))
           (bitset-delete a x)))

  (encapsulate
    ()
    (local (defthm l0
             (equal (sets::in a (bitset-members (bitset-delete b x)))
                    (and (sets::in a (bitset-members x))
                         (not (equal a (nfix b)))))
             :hints(("Goal" :in-theory (e/d (in-of-bitset-members)
                                            (|(expt x 0)|
                                             |(expt x (if a b c))|))))))


    (defthm bitset-members-of-bitset-delete
      (equal (bitset-members (bitset-delete a x))
             (sets::delete (nfix a) (bitset-members x)))
      :hints(("Goal" :in-theory (disable bitset-delete))))))



(defsection bitset-union
  :parents (bitsets)
  :short "@(call bitset-union) constructs the set @('X U Y')."

  (definlined bitset-union (x y)
    (declare (xargs :guard (and (natp x)
                                (natp y))))
    (logior (lnfix x) (lnfix y)))

  (local (in-theory (enable bitset-union)))

  (defthm natp-of-bitset-union
    (natp (bitset-union x y))
    :rule-classes :type-prescription)

  (defthm bitset-union-when-not-natp-left
    (implies (not (natp x))
             (equal (bitset-union x y)
                    (nfix y))))

  (defthm bitset-union-when-not-natp-right
    (implies (not (natp y))
             (equal (bitset-union x y)
                    (nfix x))))

  (defthm bitset-union-of-nfix-left
    (equal (bitset-union (nfix x) y)
           (bitset-union x y)))

  (defthm bitset-union-of-nfix-right
    (equal (bitset-union x (nfix y))
           (bitset-union x y)))

  (encapsulate
    ()
    (local (defthm l0
             (equal (sets::in a (bitset-members (bitset-union x y)))
                    (or (sets::in a (bitset-members x))
                        (sets::in a (bitset-members y))))
             :hints(("Goal" :in-theory (enable in-of-bitset-members)))))

    (defthm bitset-members-of-bitset-union
      (equal (bitset-members (bitset-union x y))
             (sets::union (bitset-members x)
                          (bitset-members y)))
      :hints(("Goal" :in-theory (disable bitset-union))))))



(defsection bitset-intersect
  :parents (bitsets)
  :short "@(call bitset-intersect) constructs the set @('X \\intersect Y')."

  :long "<p>Note: if you only want to know whether or not two sets intersect,
@(see bitset-intersectp) is probably more efficient.</p>"

  (definlined bitset-intersect (x y)
    (declare (xargs :guard (and (natp x)
                                (natp y))))
    (logand (lnfix x) (lnfix y)))

  (local (in-theory (enable bitset-intersect)))

  (defthm natp-of-bitset-intersect
    (natp (bitset-intersect x y))
    :rule-classes :type-prescription)

  (defthm bitset-intersect-when-not-natp-left
    (implies (not (natp x))
             (equal (bitset-intersect x y)
                    0)))

  (defthm bitset-intersect-when-not-natp-right
    (implies (not (natp y))
             (equal (bitset-intersect x y)
                    0)))

  (defthm bitset-intersect-of-nfix-left
    (equal (bitset-intersect (nfix x) y)
           (bitset-intersect x y)))

  (defthm bitset-intersect-of-nfix-right
    (equal (bitset-intersect x (nfix y))
           (bitset-intersect x y)))

  (encapsulate
    ()
    (local (defthm l0
             (equal (sets::in a (bitset-members (bitset-intersect x y)))
                    (and (sets::in a (bitset-members x))
                         (sets::in a (bitset-members y))))
             :hints(("Goal" :in-theory (enable in-of-bitset-members)))))

    (defthm bitset-members-of-bitset-intersect
      (equal (bitset-members (bitset-intersect x y))
             (sets::intersect (bitset-members x)
                              (bitset-members y)))
      :hints(("Goal" :in-theory (disable bitset-intersect))))))



(defsection bitset-difference
  :parents (bitsets)
  :short "@(call bitset-difference) constructs the set @('X - Y')."

  (definlined bitset-difference (x y)
    (declare (xargs :guard (and (natp x)
                                (natp y))))
    (logandc1 (lnfix y) (lnfix x)))

  (local (in-theory (enable bitset-difference)))

  (defthm natp-of-bitset-difference
    (natp (bitset-difference x y)))

  (defthm bitset-difference-when-not-natp-left
    (implies (not (natp x))
             (equal (bitset-difference x y)
                    0)))

  (defthm bitset-difference-when-not-natp-right
    (implies (not (natp y))
             (equal (bitset-difference x y)
                    (nfix x))))

  (defthm bitset-difference-of-nfix-left
    (equal (bitset-difference (nfix x) y)
           (bitset-difference x y)))

  (defthm bitset-difference-of-nfix-right
    (equal (bitset-difference x (nfix y))
           (bitset-difference x y)))

  (encapsulate
    ()
    (local (defthm l0
             (iff (sets::in a (bitset-members (bitset-difference x y)))
                  (and (sets::in a (bitset-members x))
                       (not (sets::in a (bitset-members y)))))
             :hints(("Goal" :in-theory (enable in-of-bitset-members)))))

    (defthm bitset-members-of-bitset-difference
      (equal (bitset-members (bitset-difference x y))
             (sets::difference (bitset-members x)
                               (bitset-members y)))
      :hints(("Goal" :in-theory (disable bitset-difference))))))




; -----------------------------------------------------------------------------
;
;                         WITNESS STYLE REASONING
;
; -----------------------------------------------------------------------------

; BOZO document this stuff.

(encapsulate
  ()
  (local
   (defthm l0
     (implies (and (equal (bitset-members x) (bitset-members y))
                   (natp x)
                   (natp y)
                   (natp a))
              (equal (equal (logbitp a x) (logbitp a y))
                     t))
     :hints(("Goal"
             :in-theory (disable in-of-bitset-members)
             :use ((:instance in-of-bitset-members (x x))
                   (:instance in-of-bitset-members (x y)))))))

  (defthmd equal-bitsets-by-membership
    (implies (and (natp x)
                  (natp y))
             (equal (equal x y)
                    (equal (bitset-members x)
                           (bitset-members y))))
    :hints(("Goal"
            :in-theory (disable sets::double-containment)
            :use ((:functional-instance
                   equal-by-logbitp
                   (logbitp-hyp (lambda ()
                                  (and (natp x)
                                       (natp y)
                                       (equal (bitset-members x)
                                              (bitset-members y)))))
                   (logbitp-lhs (lambda () x))
                   (logbitp-rhs (lambda () y))))))))

(table bitset-fns nil

; Table that lists functions that produce bitsets.  You can add to this table
; if you develop your own bitset-producing functions.

       '((bitset-singleton$inline . t)
         (bitset-insert$inline . t)
         (bitset-delete$inline . t)
         (bitset-intersect$inline . t)
         (bitset-union$inline . t)
         (bitset-difference$inline . t))

       :clear)

(defthm bitset-equal-witnessing-lemma
  (implies (not (equal a b))
           (let ((k (logbitp-mismatch (nfix a) (nfix b))))
             (implies (and (natp a) (natp b))
                      (not (iff (sets::in k (bitset-members a))
                                (sets::in k (bitset-members b)))))))
  :hints (("goal" :use ((:instance equal-bitsets-by-membership
                                   (x (nfix a))
                                   (y (nfix b)))
                        (:instance logbitp-mismatch-correct
                                   (a (nfix a))
                                   (b (nfix b))))
           :in-theory (e/d (in-of-bitset-members natp)
                           (sets::double-containment
                            logbitp-mismatch-correct))))
  :rule-classes nil)

(defwitness bitset-equal-witnessing
  :predicate (not (equal a b))
  :expr (let ((k (logbitp-mismatch (nfix a) (nfix b))))
          (implies (and (natp a) (natp b))
                   (not (iff (sets::in k (bitset-members a))
                             (sets::in k (bitset-members b))))))
  :restriction (let ((bitset-fns (table-alist 'bitset-fns (w state))))
                 (or (and (consp a)
                          (assoc (car a) bitset-fns))
                     (and (consp b)
                          (assoc (car b) bitset-fns))))
  :generalize (((logbitp-mismatch (nfix a) (nfix b)) . badbit))
  :hints ('(:use bitset-equal-witnessing-lemma :in-theory nil)))

(definstantiate bitset-equal-instancing
  :predicate (equal a b)
  :expr (iff (sets::in k (bitset-members a))
             (sets::in k (bitset-members b)))
  :vars (k)
  :restriction (let ((bitset-fns (table-alist 'bitset-fns (w state))))
                 (or (and (consp a)
                          (assoc (car a) bitset-fns))
                     (and (consp b)
                          (assoc (car b) bitset-fns))))
  :hints ('(:in-theory nil)))

(defexample bitset-equal-example
  :pattern (sets::in k (bitset-members x))
  :templates (k)
  :instance-rulename bitset-equal-instancing)

(defmacro bitset-witnessing ()
  ;; Typical use:  (defthm ... :hints ((bitset-witnessing)))
  `(witness :ruleset (bitset-equal-witnessing
                      bitset-equal-instancing
                      bitset-equal-example)))

(local
 (encapsulate
   ()
   (local (allow-real-oracle-eval))
   (local (defthm test1
            (implies (equal (bitset-union (bitset-union a d) b)
                            (bitset-intersect b c))
                     (equal (bitset-union b (bitset-union a d)) (nfix b)))
            :hints ((bitset-witnessing))))

   (local (defthm test2
            (equal (bitset-union a (bitset-intersect b c))
                   (bitset-intersect (bitset-union a b)
                                     (bitset-union a c)))
            :hints ((bitset-witnessing))))))




; -----------------------------------------------------------------------------
;
;                         ADDITIONAL OPERATIONS
;
; -----------------------------------------------------------------------------

(defsection bitset-subsetp
  :parents (bitsets)
  :short "@(call bitset-subsetp) efficiently determines if @('X') is a subset
of @('Y')."

  (definlined bitset-subsetp (x y)
    (declare (xargs :guard (and (natp x)
                                (natp y))))
    (= 0 (bitset-difference x y)))

  (local (in-theory (enable bitset-subsetp)))

  (defthm booleanp-of-bitset-subsetp
    (booleanp (bitset-subsetp x y))
    :rule-classes :type-prescription)

  (defthm bitset-subsetp-when-not-natp-left
    (implies (not (natp x))
             (equal (bitset-subsetp x y)
                    t)))

  (defthm bitset-subsetp-when-not-natp-right
    (implies (not (natp y))
             (equal (bitset-subsetp x y)
                    (zp x))))

  (defthm bitset-subsetp-of-nfix-left
    (equal (bitset-subsetp (nfix x) y)
           (bitset-subsetp x y)))

  (defthm bitset-subsetp-of-nfix-right
    (equal (bitset-subsetp x (nfix y))
           (bitset-subsetp x y)))

  (encapsulate
    ()
    (local (allow-real-oracle-eval))
    (local (defthm l0
             (implies (and (bitset-subsetp x y)
                           (sets::in a (bitset-members x)))
                      (sets::in a (bitset-members y)))
             :hints((bitset-witnessing))))

    (local (defthm l1
             (implies (bitset-subsetp x y)
                      (sets::subset (bitset-members x)
                                    (bitset-members y)))
             :hints(("Goal" :in-theory (disable bitset-subsetp)))))

    (local (defthm l2
             (implies (sets::subset (bitset-members x)
                                    (bitset-members y))
                      (bitset-subsetp x y))
             :hints((bitset-witnessing))))

    (defthm bitset-subsetp-removal
      (equal (bitset-subsetp x y)
             (sets::subset (bitset-members x)
                           (bitset-members y)))
      :hints(("Goal"
              :in-theory (disable bitset-subsetp)
              :cases ((bitset-subsetp x y)))))))



(defsection bitset-intersectp
  :parents (bitsets)
  :short "@(call bitset-intersectp) efficiently determines if @('X') and @('Y')
have any common members."

  :long "<p>This is efficient because, unlike @(see bitset-intersect), we don't
actually construct the intersection.</p>"

  (definlined bitset-intersectp (x y)
    (declare (xargs :guard (and (natp x)
                                (natp y))))
    (logtest (lnfix x) (lnfix y)))

  (local (in-theory (enable bitset-intersectp)))

  (defthm booleanp-of-bitset-intersectp
    (booleanp (bitset-intersectp x y))
    :rule-classes :type-prescription)

  (defthm bitset-intersectp-when-not-natp-left
    (implies (not (natp x))
             (equal (bitset-intersectp x y)
                    nil)))

  (defthm bitset-intersectp-when-not-natp-right
    (implies (not (natp y))
             (equal (bitset-intersectp x y)
                    nil)))

  (defthm bitset-intersectp-of-nfix-left
    (equal (bitset-intersectp (nfix x) y)
           (bitset-intersectp x y)))

  (defthm bitset-intersectp-of-nfix-right
    (equal (bitset-intersectp x (nfix y))
           (bitset-intersectp x y)))

  (encapsulate
    ()
    (local (defthm l0
             (implies (bitset-intersectp x y)
                      (not (equal 0 (bitset-intersect x y))))
             :hints(("Goal"
                     :in-theory (enable bitset-intersectp
                                        bitset-intersect)))))

    (defthm bitset-intersectp-removal
      (implies (bitset-intersectp x y)
               (sets::intersect (bitset-members x)
                                (bitset-members y)))
      :hints(("Goal"
              :in-theory (disable bitset-intersectp
                                  bitset-members-of-bitset-intersect
                                  sets::double-containment)
              :use ((:instance bitset-members-of-bitset-intersect)
                    (:instance l0)))))))



(defsection bitset-cardinality
  :parents (bitsets)
  :short "@(call bitset-cardinality) determines the cardinality of the set
@('X')."

  :long "<p>We prefer to reason about @('(sets::cardinality (bitset-members
X))').  We could have used this as the @(':logic') definition, but the @(see
logcount)-based definition should be better for symbolic simulation with @(see
GL).</p>"

  (defund bitset-cardinality (x)
    (declare (xargs :guard (natp x)))
    (logcount (lnfix x)))

; The correctness proof is tricky because logcount is effectively is defined in
; a logcar/logcdr style, while bitset-members is defined in a logbitp
; upward-counting style.  To bridge the gap, our strategy is to redefine logcar
; as the length of (LSB-BITS N X).  We show that (LSB-BITS 0 X) computes an
; ordered set that contains all of the positions of 1-bits in X.  This is the
; same set computed by BITSET-MEMBERS, hence its length is the same.

  ;; (local (defthm c0
  ;;          (implies (natp x)
  ;;                   (equal (nonnegative-integer-quotient x 2)
  ;;                          (logcdr x)))
  ;;          :hints(("Goal" :in-theory (enable logcdr)))))

  ;; (local (defthm c1
  ;;          (implies (natp x)
  ;;                   (equal (evenp x)
  ;;                          (= (logcar x) 0)))
  ;;          :hints(("Goal" :in-theory (enable logcar evenp)))))

  ;; (local (defthm logcount-when-positive
  ;;          (implies (natp x)
  ;;                   (equal (logcount x)
  ;;                          (cond ((zp x)
  ;;                                 0)
  ;;                                ((= (logcar x) 1)
  ;;                                 (+ 1 (logcount (logcdr x))))
  ;;                                (t
  ;;                                 (logcount (logcdr x))))))
  ;;          :rule-classes ((:definition :clique (logcount) :controller-alist ((logcount t))))
  ;;          :hints(("Goal"
  ;;                  :induct (logcount x)
  ;;                  :in-theory (enable logcar logcount logcar)))))

  ;; (local (in-theory (disable logcount)))

  (local (defund lsb-bits (n x)
           (if (zp x)
               nil
             (if (= (logcar x) 1)
                 (cons (nfix n) (lsb-bits (+ 1 (nfix n)) (logcdr x)))
               (lsb-bits (+ 1 (nfix n)) (logcdr x))))))

  (local (defthmd logcount-is-len-lsb-bits
           ;; This is just a simple induction.  Note that N is free!
           (implies (natp x)
                    (equal (logcount x)
                           (len (lsb-bits n x))))
           :hints(("Goal" :in-theory (enable lsb-bits logcount**)))))

  (local (defthm member-equal-lsb-bits
           (iff (member-equal a (lsb-bits n x))
                (and (natp a)
                     (<= (nfix n) a)
                     (logbitp (- a (nfix n)) (nfix x))))
           :hints(("Goal"
                   :do-not '(generalize fertilize)
                   :in-theory (enable lsb-bits logbitp**)
                   :induct (lsb-bits n x)))))

  (local (defthm l0
           (implies (and (force (natp a))
                         (force (natp b)))
                    (equal (sets::<< a b)
                           (< a b)))
           :hints(("Goal" :in-theory (enable sets::<< lexorder alphorder)))))

  (local (defthm l1
           (equal (natp (car (lsb-bits n x)))
                  (if (lsb-bits n x)
                      t
                    nil))
           :hints(("Goal" :in-theory (enable lsb-bits)))))

  (local (defthm l2
           (implies (lsb-bits n x)
                    (<= (nfix n) (car (lsb-bits n x))))
           :rule-classes ((:rewrite) (:linear))
           :hints(("Goal" :in-theory (enable lsb-bits)))))

  (local (defthm setp-of-lsb-bits
           (sets::setp (lsb-bits n x))
           :hints(("Goal" :in-theory (enable* lsb-bits
                                              (:ruleset sets::primitive-rules))))))

  (local (in-theory (disable l0 l1 l2)))

  (local (defthmd sets-membership-hack
           (implies (and (sets::setp x)
                         (syntaxp (not (quotep x))))
                    (iff (member-equal a x)
                         (sets::in a x)))
           :hints(("Goal"
                   :in-theory (enable* (:ruleset sets::primitive-rules))))))

  (local (defthm in-lsb-bits
           (equal (sets::in a (lsb-bits n x))
                  (and (natp a)
                       (<= (nfix n) a)
                       (logbitp (- a (nfix n)) (nfix x))))
           :hints(("Goal" :use ((:instance sets-membership-hack
                                           (a a)
                                           (x (lsb-bits n x))))))))

  (local (defthm lsb-bits-is-bitset-members
           (equal (lsb-bits 0 x)
                  (bitset-members x))
           :hints(("goal"
                   :in-theory (e/d (in-of-bitset-members)
                                   (lsb-bits))))))

  (local (defthm logcount-is-len-of-bitset-members
           (implies (natp x)
                    (equal (logcount x)
                           (len (bitset-members x))))
           :hints(("Goal"
                   :in-theory (enable bitset-members)
                   :use ((:instance logcount-is-len-lsb-bits (n 0)))))))

  (local (defthm cardinality-is-len
           (implies (sets::setp x)
                    (equal (sets::cardinality x)
                           (len x)))
           :hints(("Goal" :in-theory (enable* (:ruleset sets::primitive-rules))))))

  (local (defthm logcount-is-cardinality-of-bitset-members
           (implies (natp x)
                    (equal (logcount x)
                           (sets::cardinality (bitset-members x))))))

  (defthm bitset-cardinality-removal
    (equal (bitset-cardinality x)
           (sets::cardinality (bitset-members x)))
    :hints(("Goal" :in-theory (enable bitset-cardinality)))))



(defsection bitset-list*
  :parents (bitsets)
  :short "Macro to repeatedly insert into a bitset."
  :long "<p>Example: @('(bitset-list* a b c X)') expands to:</p>

@({
 (bitset-insert a
  (bitset-insert b
   (bitset-insert c X)))
})

<p>This is much like the @(see list*) macro for constructing lists.  See also
@(see bitset-list) for a @(see list)-like version.</p>

<p><b>NOTE:</b> This is not very efficient.  Inserting N elements into a set
will require N calls of @(see bitset-insert).</p>"

  (defun bitset-list*-macro (lst)
    (declare (xargs :guard (and (true-listp lst)
                                (consp lst))))
    (if (atom (cdr lst))
        (car lst)
      (list 'bitset-insert
            (car lst)
            (bitset-list*-macro (cdr lst)))))

  (defmacro bitset-list* (&rest args)
    (bitset-list*-macro args)))


(defsection bitset-list
  :parents (bitsets)
  :short "Macro to construct a bitset from particular members."
  :long "<p>Example: @('(bitset-list 1 2 4)') constructs the set @('{1, 2,
  4}').</p>

<p>In general, @('(bitset-list x1 x2 ... xn)') expands to</p>

@({
 (bitset-insert x1
  (bitset-insert x2
   (bitset-insert ...
     (bitset-insert xn 0))))
})

<p>This is much like the @(see list) macro for constructing lists.  See also
@(see bitset-list*) for a @(see list*)-like version.</p>

<p><b>NOTE:</b> This is not very efficient.  Constructing a set with N elements
will require N calls of @(see bitset-insert).</p>"

  (defun bitset-list-macro (lst)
    (declare (xargs :guard t))
    (if (atom lst)
        0
      (list 'bitset-insert
            (car lst)
            (bitset-list-macro (cdr lst)))))

  (defmacro bitset-list (&rest args)
    (bitset-list-macro args)))

