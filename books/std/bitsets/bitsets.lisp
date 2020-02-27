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
(include-book "bignum-extract")
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/misc/witness-cp" :dir :system))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "arithmetic-3/bind-free/top" :dir :system))

(local (in-theory (acl2::enable* set::definitions set::expensive-rules
                                 bitops::ash-1-removal)))

(defxdoc bitsets
  :parents (std/bitsets)
  :short "Bitsets library: uses bitmasks to represent finite sets of (small)
natural numbers."

  :long "<h3>Introduction</h3>

<p>In this library, sets of natural numbers are represented as natural numbers
by saying @('a') is a member of the set @('X') when @('(logbitp a X)').  For
instance, the set {1, 2, 4} would be represented as the number 22.  In binary,
this number is 10110, and you can see that bits 1, 2, and 4 are each
\"true\".</p>

<p>This representation enjoys certain efficiencies.  In particular, operations
like union, intersection, difference, and subset testing can be carried out in
a \"word at a time\" fashion with bit operations.</p>

<p>But bitsets are only appropriate for sets whose elements are reasonably
small numbers since the space needed to represent a bitset is determined by its
maximal element.  If your sets contain extremely small numbers---less than
28-60, depending on the Lisp---then they can be represented as fixnums and the
bitset operations will be remarkably efficient.</p>

<p>Beyond this, bignums are necessary.  Even though bignum operations generally
involve memory allocation and are much slower than fixnum operations, using
bignums to represent sets can still be very efficient.  For instance, on 64-bit
CCL, bignums are represented as a header/data pair where the data is an array
of 32-bit words; operations like @(see logand) can smash together the two data
arrays a word at a time.</p>

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


<h3>Bitset Operations</h3>

<p>Convention:</p>

<ul>
<li>@('a, b, ...') denote set elements</li>
<li>@('X, Y, ...') denote sets.</li>
</ul>

<p>There is no such explicit @('bitsetp') recognizer; instead we just use
@('natp').  Similarly there is no separate bitset-fixing function because we
just use @('nfix').</p>

<p>See @(see reasoning) for some notes about how to prove theorems about bitset
functions.</p>

<h5>Bitset Constructors</h5>

<dl>

<dt>@('(bitset-singleton a)')</dt>
<dd>Constructs the set @('{a}')</dd>
<dd>Execution: @('(ash 1 a)')</dd>

<dt>@('(bitset-insert a X)')</dt>
<dd>Constructs the set @('X U {a}')</dd>
<dd>Execution: @('(logior (ash 1 a) x)')</dd>

<dt>@('(bitset-list a b ...)')</dt>
<dd>Constructs the set @('{a, b, ...}')</dd>
<dd>Execution: repeated @('bitset-insert')s</dd>

<dt>@('(bitset-list* a b ... X)')</dt>
<dd>Constructs the set @('X U {a, b, ...}')</dd>
<dd>Execution: repeated @('bitset-insert')s</dd>

<dt>@('(bitset-delete a X)')</dt>
<dd>Constructs the set @('X - {a}')</dd>
<dd>Execution: @('(logandc1 (ash 1 a) x)')</dd>

<dt>@('(bitset-union X Y ...)')</dt>
<dd>Constructs the set @('X U Y U ...')</dd>
<dd>Execution: @('(logior x (logior y ...))')</dd>

<dt>@('(bitset-intersect X Y ...)')</dt>
<dd>Constructs the set @('X \\intersect Y \\intersect ...')</dd>
<dd>Execution: @('(logand x (logand y ...))')</dd>

<dt>@('(bitset-difference X Y)')</dt>
<dd>Constructs the set @('X - Y')</dd>
<dd>Execution: @('(logandc1 y x)')</dd>
</dl>

<h5>Inspecting Bitsets</h5>

<dl>
<dt>@('(bitset-memberp a X)')</dt>
<dd>Determine whether @('a') is a member of the set @('X')</dd>
<dd>Execution: @('(logbitp a x)')</dd>

<dt>@('(bitset-intersectp X Y)')</dt>
<dd>Determines whether @('X') and @('Y') have any common members</dd>
<dd>Execution: @('(logtest x y)')</dd>

<dt>@('(bitset-subsetp X Y)')</dt>
<dd>Determines whether @('X') is a subset of @('Y')</dd>
<dd>Execution: @('(= 0 (logandc2 y x))')</dd>

<dt>@('(bitset-cardinality X)')</dt>
<dd>Determines the cardinality of @('X')</dd>
<dd>Execution: @('(logcount x)')</dd>

</dl>

<h5>Enumerating Bitset Members</h5>

<dl>
<dt>@('(bitset-members X)')</dt>
<dd>Constructs an ordinary ordered set with the elements of X.</dd>
<dd>Expensive: must cons together all of the set elements.</dd>
<dd>Important in @(see reasoning) about bitsets.</dd>
</dl>")

(local (xdoc::set-default-parents bitsets))

(define bitset-members ((x natp))
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
to walk up to this bound and collect all @('i') such that @('(logbitp i
x)').</p>

<p>The definition below uses @(see bits-between) to do just this.  However,
note that when the @('bignum-extract-opt') book is loaded (which requires a
ttag), a more efficient implementation is used; see @(see ttag-bitset-members)
and @(see bignum-extract) for details.</p>"

  (mbe :logic
       (let ((x (nfix x)))
         (bits-between 0 (integer-length x) x))
       :exec
       (bits-between 0 (integer-length x) x))
  ///

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

  (defthm nat-listp-of-bitset-members
    (nat-listp (bitset-members x)))

  (defthm no-duplicatesp-equal-of-bitset-members
    (no-duplicatesp-equal (bitset-members x)))

  (defthm setp-of-bitset-members
    (set::setp (bitset-members x)))

  (defthmd in-of-bitset-members
    ;; CAREFUL!  This theorem should typically be left disabled because it
    ;; exposes the underlying representation of the set.  On the other hand,
    ;; it's the main theorem that we use when introducing new "primitive
    ;; functions" for building bitsets (i.e., which build bitsets by exploiting
    ;; the underlying representation).
    (equal (set::in a (bitset-members x))
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
                     :in-theory (disable acl2::logbitp-mismatch-correct)
                     :use ((:instance acl2::logbitp-mismatch-correct
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


(defsection bits-between-of-bignum-extract
  (local (in-theory (enable bignum-extract)))

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
            :in-theory (e/d (acl2::loghead)
                            (bits-between-of-increment-right-index
                             acl2::right-shift-to-logtail))))))

(define ttag-bitset-members ((x natp))
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
 (include-book \"centaur/aig/random-sim\" :dir :system)
 (include-book \"centaur/misc/memory-mgmt\" :dir :system)
 (include-book \"std/util/defconsts\" :dir :system)

  (acl2::set-max-mem ;; newline to fool dependency scanner
    (* 30 (expt 2 30)))

  (acl2::defconsts (*random-data* state)
    (acl2::random-list 100000 (ash 1 5000) state))

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

<p>And the results (on compute-1-3):</p>

@({
     Unoptimized Original: 12.80 sec, 4,001,843,488 bytes
     Unoptimized TTAG: 8.27 sec, 9,118,511,648 bytes
     Optimized Original: 4.05 sec, 4,001,843,488 bytes
     Optimized TTAG: 4.01 sec, 4,001,843,488 bytes
})"

  :prepwork
  ((local (in-theory (disable acl2::associativity-of-append)))

   (local (defthm rassoc-append
            (equal (append x (append y z))
                   (append (append x y) z))))

   (local (defthm ash-5-to-times
            (implies (natp x)
                     (equal (ash x 5)
                            (* x 32)))
            :hints(("Goal" :in-theory (enable ash floor)))))

   (local (defthm ash-minus-5-to-floor
            (implies (natp x)
                     (equal (ash x -5)
                            (floor x 32)))
            :hints(("Goal" :in-theory (enable ash floor)))))

   (defund ttag-bitset-members-aux (slice x acc)
     ;; Main loop.  We collect the set corresponding to x[0:32*(slice+1)], by
     ;; using our 32-bit collection function on each slice extracted by
     ;; bignum-extract.
     (declare (xargs :guard (and (natp slice)
                                 (integerp x))))
     (if (zp slice)
         (bits-0-31 (ash slice 5)
                    (bignum-extract x slice)
                    acc)
       (ttag-bitset-members-aux (the (integer 0 *) (- (lnfix slice) 1))
                                x
                                (bits-0-31 (the (integer 0 *) (ash slice 5))
                                           (bignum-extract x slice)
                                           acc))))

   (local (in-theory (enable acl2::loghead)))

   (defthm ttag-bitset-members-aux-redef
     (implies (and (natp slice)
                   (integerp x))
              (equal (ttag-bitset-members-aux slice x acc)
                     (append (bits-between 0
                                           (* (+ 1 slice) 32)
                                           x)
                             acc)))
     :hints(("Goal" :in-theory (e/d (ttag-bitset-members-aux bignum-extract)
                                    (acl2::right-shift-to-logtail))))))


  :guard-hints (("Goal" :in-theory (e/d (bitset-members))))

  (mbe :logic (bitset-members x)
       :exec (ttag-bitset-members-aux
              (the (integer 0 *) (ash (integer-length x) -5))
              x
              nil)))



(define bitset-memberp ((a natp :type unsigned-byte)
                        (x natp :type unsigned-byte))
  :returns (bool booleanp :rule-classes :type-prescription)
  :short "@(call bitset-memberp) tests whether @('a') is a member of the set
@('X')."
  :long "<p>This is reasonably efficient: it executes as @(see logbitp) and
does not need to use @(see bitset-members).</p>

<p>We prefer to reason about @('(set::in a (bitset-members X))').  We could
have used this as the @(':logic') definition, but the @(see logbitp)-based
definition should be better for symbolic simulation with @(see gl::gl).</p>"
  :inline t
  :split-types t
  (logbitp a (the unsigned-byte (lnfix x)))
  ///
  (defthm bitset-memberp-removal
    (equal (bitset-memberp a x)
           (set::in (nfix a) (bitset-members x)))
    :hints(("Goal" :in-theory (enable bitset-memberp in-of-bitset-members)))))


(define bitset-singleton ((a natp :type unsigned-byte))
  :returns (bitset natp :rule-classes :type-prescription)
  :short "@(call bitset-singleton) constructs the singleton set @('{a}')."
  :long "<p>This is perhaps slightly more efficient than the equivalent,
 @('(bitset-insert A 0)').</p>"
  :inline t
  :split-types t
  (the unsigned-byte
       (ash 1 (the unsigned-byte (lnfix a))))
  ///
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
             (equal (set::in a (bitset-members (bitset-singleton b)))
                    (equal a (nfix b)))
             ;; Ugh, really bad expt matching...
             :hints(("Goal" :in-theory (e/d (in-of-bitset-members)
                                            ((expt)
                                             acl2::|(expt x 0)|)))
                    (and stable-under-simplificationp
                         '(:in-theory (enable expt))))))

    (defthm bitset-members-of-bitset-singleton
      (equal (bitset-members (bitset-singleton a))
             (set::insert (nfix a) nil))
      :hints(("Goal" :in-theory (disable bitset-singleton))))))


(define bitset-insert ((a natp :type unsigned-byte)
                       (x natp :type unsigned-byte))
  :returns (bitset natp :rule-classes :type-prescription)
  :parents (bitsets)
  :short "@(call bitset-insert) constructs the set @('X U {a}')."

  :long "<p>This looks pretty efficient, but keep in mind that it still has to
construct a new set and hence is linear in the size of the set.  You should
probably avoid calling this in a loop if possible; instead consider functions
like @(see bitset-union).</p>"
  :inline t
  :split-types t
  (the unsigned-byte
       (logior (the unsigned-byte (ash 1 (lnfix a)))
               (the unsigned-byte (lnfix x))))
  ///
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
             (equal (set::in a (bitset-members (bitset-insert b x)))
                    (or (equal a (nfix b))
                        (set::in a (bitset-members x))))
             :hints(("Goal"
                     :in-theory (e/d (in-of-bitset-members)
                                     ;; Ugh, lousy expt matching
                                     (acl2::|(expt x 0)|
                                            acl2::|(expt x (if a b c))|))))))

    (defthmd set::bitset-members-of-bitset-insert
      (equal (bitset-members (bitset-insert a x))
             (set::insert (nfix a) (bitset-members x)))
      :hints(("Goal" :in-theory (disable bitset-insert))))))



(define bitset-delete ((a natp :type unsigned-byte)
                       (x natp :type unsigned-byte))
  :returns (bitset natp :rule-classes :type-prescription)
  :parents (bitsets)
  :short "@(call bitset-delete) constructs the set @('X - {a}')."
  :long "<p>This looks pretty efficient, but keep in mind that it still has to
construct a new set and hence is linear in the size of the set.  You should
probably avoid calling this in a loop if possible; instead, consider functions
like @(see bitset-intersect) and @(see bitset-difference).</p>"
  :inline t
  :split-types t
  (the unsigned-byte
       (logandc1 (the unsigned-byte (ash 1 (the unsigned-byte (lnfix a))))
                 (the unsigned-byte (lnfix x))))
  ///
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
             (equal (set::in a (bitset-members (bitset-delete b x)))
                    (and (set::in a (bitset-members x))
                         (not (equal a (nfix b)))))
             :hints(("Goal" :in-theory (e/d (in-of-bitset-members)
                                            (acl2::|(expt x 0)|
                                             acl2::|(expt x (if a b c))|))))))


    (defthm bitset-members-of-bitset-delete
      (equal (bitset-members (bitset-delete a x))
             (set::delete (nfix a) (bitset-members x)))
      :hints(("Goal" :in-theory (disable bitset-delete))))))





(defsection bitset-union
  :parents (bitsets)
  :short "@('(bitset-union X Y ...)') constructs the set @('X U Y U ...')."

  (define bitset-binary-union ((x natp :type unsigned-byte)
                               (y natp :type unsigned-byte))
    :returns (bitset natp :rule-classes :type-prescription)
    :parents (bitset-union)
    :inline t
    :split-types t
    (the unsigned-byte
         (logior (the unsigned-byte (lnfix x))
                 (the unsigned-byte (lnfix y)))))

  (defmacro bitset-union (&rest args)
    (cond ((atom args)
           0)
          ((atom (cdr args))
           (car args))
          (t
           (xxxjoin 'bitset-binary-union args))))

  (add-macro-alias bitset-union bitset-binary-union$inline)
  (add-macro-fn    bitset-union bitset-binary-union$inline t)

  (local (in-theory (enable bitset-union)))

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
             (equal (set::in a (bitset-members (bitset-union x y)))
                    (or (set::in a (bitset-members x))
                        (set::in a (bitset-members y))))
             :hints(("Goal" :in-theory (enable in-of-bitset-members)))))

    (defthm bitset-members-of-bitset-union
      (equal (bitset-members (bitset-union x y))
             (set::union (bitset-members x)
                          (bitset-members y)))
      :hints(("Goal" :in-theory (disable bitset-union))))))



(defsection bitset-intersect
  :parents (bitsets)
  :short "@('(bitset-intersect X Y ...)') constructs the set @('X \\intersect Y
  \\intersect ...')."

  :long "<p>Note: if you only want to know whether or not two sets intersect,
@(see bitset-intersectp) is probably more efficient.</p>"

  (define bitset-binary-intersect ((x natp :type unsigned-byte)
                                   (y natp :type unsigned-byte))
    :returns (bitset natp :rule-classes :type-prescription)
    :parents (bitset-intersect)
    :inline t
    :split-types t
    (the unsigned-byte
         (logand (the unsigned-byte (lnfix x))
                 (the unsigned-byte (lnfix y)))))

  (defmacro bitset-intersect (&rest args)
    (cond ((atom args)
           0)
          ((atom (cdr args))
           (car args))
          (t
           (xxxjoin 'bitset-binary-intersect args))))

  (add-macro-alias bitset-intersect bitset-binary-intersect$inline)
  (add-macro-fn    bitset-intersect bitset-binary-intersect$inline t)

  (local (in-theory (enable bitset-intersect)))

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
             (equal (set::in a (bitset-members (bitset-intersect x y)))
                    (and (set::in a (bitset-members x))
                         (set::in a (bitset-members y))))
             :hints(("Goal" :in-theory (enable in-of-bitset-members)))))

    (defthm bitset-members-of-bitset-intersect
      (equal (bitset-members (bitset-intersect x y))
             (set::intersect (bitset-members x)
                              (bitset-members y)))
      :hints(("Goal" :in-theory (disable bitset-intersect))))))



(define bitset-difference ((x natp :type unsigned-byte)
                           (y natp :type unsigned-byte))
  :returns (bitset natp :rule-classes :type-prescription)
  :parents (bitsets)
  :short "@(call bitset-difference) constructs the set @('X - Y')."
  :inline t
  :split-types t
  (the unsigned-byte
       (logandc1 (the unsigned-byte (lnfix y))
                 (the unsigned-byte (lnfix x))))
  ///
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
             (iff (set::in a (bitset-members (bitset-difference x y)))
                  (and (set::in a (bitset-members x))
                       (not (set::in a (bitset-members y)))))
             :hints(("Goal" :in-theory (enable in-of-bitset-members)))))

    (defthm bitset-members-of-bitset-difference
      (equal (bitset-members (bitset-difference x y))
             (set::difference (bitset-members x)
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
            :in-theory (disable set::double-containment)
            :use ((:functional-instance
                   equal-by-logbitp
                   (logbitp-hyp (lambda ()
                                  (and (natp x)
                                       (natp y)
                                       (equal (bitset-members x)
                                              (bitset-members y)))))
                   (logbitp-lhs (lambda () x))
                   (logbitp-rhs (lambda () y))))))))



;; BOZO why did we make this local?
(local
 (progn

   (table bitset-fns nil

; Table that lists functions that produce bitsets.  You can add to this table
; if you develop your own bitset-producing functions.

          '((acl2::bitset-singleton$inline . t) ;; gross that we can't use macro aliases
            (acl2::bitset-insert$inline . t)
            (acl2::bitset-delete$inline . t)
            (bitset-binary-intersect$inline . t)
            (bitset-binary-union$inline . t)
            (acl2::bitset-difference$inline . t))

          :clear)

   (defthm bitset-equal-witnessing-lemma
     (implies (not (equal a b))
              (let ((k (logbitp-mismatch (nfix a) (nfix b))))
                (implies (and (natp a) (natp b))
                         (not (iff (set::in k (bitset-members a))
                                   (set::in k (bitset-members b)))))))
     :hints (("goal" :use ((:instance equal-bitsets-by-membership
                                      (x (nfix a))
                                      (y (nfix b)))
                           (:instance acl2::logbitp-mismatch-correct
                                      (a (nfix a))
                                      (b (nfix b))))
              :in-theory (e/d (in-of-bitset-members natp)
                              (set::double-containment
                               acl2::logbitp-mismatch-correct))))
     :rule-classes nil)

   (defwitness bitset-equal-witnessing
     :predicate (not (equal a b))
     :expr (let ((k (logbitp-mismatch (nfix a) (nfix b))))
             (implies (and (natp a) (natp b))
                      (not (iff (set::in k (bitset-members a))
                                (set::in k (bitset-members b))))))
     :restriction
     (let ((bitset-fns (table-alist 'bitset-fns world)))
                    (or (and (consp a)
                             (assoc (car a) bitset-fns))
                        (and (consp b)
                             (assoc (car b) bitset-fns))))
     :generalize (((logbitp-mismatch (nfix a) (nfix b)) . badbit))
     :hints ('(:use bitset-equal-witnessing-lemma :in-theory nil)))

   (definstantiate bitset-equal-instancing
     :predicate (equal a b)
     :expr (iff (set::in k (bitset-members a))
                (set::in k (bitset-members b)))
     :vars (k)
     :restriction
     (let ((bitset-fns (table-alist 'bitset-fns world)))
                    (or (and (consp a)
                             (assoc (car a) bitset-fns))
                        (and (consp b)
                             (assoc (car b) bitset-fns))))
     :hints ('(:in-theory nil)))

   (defexample bitset-equal-example
     :pattern (set::in k (bitset-members x))
     :templates (k)
     :instance-rulename bitset-equal-instancing)

   (defmacro bitset-witnessing ()
     ;; Typical use:  (defthm ... :hints ((bitset-witnessing)))
     `(acl2::witness :ruleset (bitset-equal-witnessing
                               bitset-equal-instancing
                               bitset-equal-example)))))

(local
 (encapsulate
   ()
   ;;(local (allow-real-oracle-eval))
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

(define bitset-subsetp ((x natp :type unsigned-byte)
                        (y natp :type unsigned-byte))
  :parents (bitsets)
  :returns (subsetp booleanp :rule-classes :type-prescription)
  :short "@(call bitset-subsetp) efficiently determines if @('X') is a subset
of @('Y')."
  :inline t
  :split-types t
  (eql 0 (the unsigned-byte (bitset-difference x y)))
  ///
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
;    (local (allow-real-oracle-eval))
    (local (defthm l0
             (implies (and (bitset-subsetp x y)
                           (set::in a (bitset-members x)))
                      (set::in a (bitset-members y)))
             :hints((bitset-witnessing))))

    (local (defthm l1
             (implies (bitset-subsetp x y)
                      (set::subset (bitset-members x)
                                    (bitset-members y)))
             :hints(("Goal" :in-theory (disable bitset-subsetp)))))

    (local (defthm l2
             (implies (set::subset (bitset-members x)
                                    (bitset-members y))
                      (bitset-subsetp x y))
             :hints((bitset-witnessing))))

    (defthm bitset-subsetp-removal
      (equal (bitset-subsetp x y)
             (set::subset (bitset-members x)
                           (bitset-members y)))
      :hints(("Goal"
              :in-theory (disable bitset-subsetp)
              :cases ((bitset-subsetp x y)))))))



(define bitset-intersectp ((x natp :type unsigned-byte)
                           (y natp :type unsigned-byte))
  :returns (intersectp booleanp :rule-classes :type-prescription)
  :parents (bitsets)
  :short "@(call bitset-intersectp) efficiently determines if @('X') and @('Y')
have any common members."
  :long "<p>This is efficient because, unlike @(see bitset-intersect), we don't
actually construct the intersection.</p>"
  :inline t
  :split-types t
  (logtest (the unsigned-byte (lnfix x))
           (the unsigned-byte (lnfix y)))
  ///
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
               (set::intersect (bitset-members x)
                                (bitset-members y)))
      :hints(("Goal"
              :in-theory (disable bitset-intersectp
                                  bitset-members-of-bitset-intersect
                                  set::double-containment)
              :use ((:instance bitset-members-of-bitset-intersect)
                    (:instance l0)))))))



(define bitset-cardinality ((x natp :type unsigned-byte))
  :parents (bitsets)
  :short "@(call bitset-cardinality) determines the cardinality of the set
@('X')."
  :long "<p>We prefer to reason about @('(set::cardinality (bitset-members
X))').  We could have used this as the @(':logic') definition, but the @(see
logcount)-based definition should be better for symbolic simulation with @(see
gl::gl).</p>"
  :inline t
  :split-types t
  (the unsigned-byte
       (logcount (the unsigned-byte (lnfix x))))
  ///

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
             (if (eql (acl2::logcar x) 1)
                 (cons (nfix n) (lsb-bits (+ 1 (nfix n)) (acl2::logcdr x)))
               (lsb-bits (+ 1 (nfix n)) (acl2::logcdr x))))))

  (local (defthmd logcount-is-len-lsb-bits
           ;; This is just a simple induction.  Note that N is free!
           (implies (natp x)
                    (equal (logcount x)
                           (len (lsb-bits n x))))
           :hints(("Goal" :in-theory (enable lsb-bits acl2::logcount**)))))

  (local (defthm member-equal-lsb-bits
           (iff (member-equal a (lsb-bits n x))
                (and (natp a)
                     (<= (nfix n) a)
                     (logbitp (- a (nfix n)) (nfix x))))
           :hints(("Goal"
                   :do-not '(generalize fertilize)
                   :in-theory (enable lsb-bits acl2::logbitp**)
                   :induct (lsb-bits n x)))))

  (local (defthm l0
           (implies (and (force (natp a))
                         (force (natp b)))
                    (equal (set::<< a b)
                           (< a b)))
           :hints(("Goal" :in-theory (enable set::<< lexorder alphorder)))))

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
           (set::setp (lsb-bits n x))
           :hints(("Goal" :in-theory (enable* lsb-bits
                                              (:ruleset set::primitive-rules))))))

  (local (in-theory (disable l0 l1 l2)))

  (local (defthmd sets-membership-hack
           (implies (and (set::setp x)
                         (syntaxp (not (quotep x))))
                    (iff (member-equal a x)
                         (set::in a x)))
           :hints(("Goal"
                   :in-theory (enable* (:ruleset set::primitive-rules))))))

  (local (defthm in-lsb-bits
           (equal (set::in a (lsb-bits n x))
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
           (implies (set::setp x)
                    (equal (set::cardinality x)
                           (len x)))
           :hints(("Goal" :in-theory (enable* (:ruleset set::primitive-rules))))))

  (local (defthm logcount-is-cardinality-of-bitset-members
           (implies (natp x)
                    (equal (logcount x)
                           (set::cardinality (bitset-members x))))))

  (defthm bitset-cardinality-removal
    (equal (bitset-cardinality x)
           (set::cardinality (bitset-members x)))
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
