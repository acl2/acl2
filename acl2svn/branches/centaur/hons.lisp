; ACL2 Version 4.3 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2011  University of Texas at Austin

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic
; NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78701 U.S.A.

; hons.lisp -- Logical definitions for hash cons and fast alists.  Note that
; the memoization and watch functionality previously provided by this file have
; been moved into "memoize.lisp".  A closely related file is "hons-raw.lisp"
; that provides the Common Lisp implementation of many of the concepts
; introduced below.

; The original version of this file was contributed by Bob Boyer and Warren
; A. Hunt, Jr.  The design of this system of hash cons, function memoization,
; and fast association lists (applicative hash tables) was initially
; implemented by Boyer and Hunt.  The code has since been improved by Boyer and
; Hunt, and also by Sol Swords, Jared Davis, and Matt Kaufmann.

(in-package "ACL2")

(defdoc normed
  ":Doc-Section Hons-and-Memoization

Normed objects are ACL2 Objects that are \"canonical\" or \"unique\" in a
certain sense.~/

This ~il[documentation] topic relates to the experimental extension of ACL2
supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

In Common Lisp, we can tell whether an ACL2 object is ~st[normed] or not, but
there is no way for an ordinary ACL2 function to see whether an object is
normed.  Hence, whether or not an object is normed is an implementation-level
concept.

The fundamental property of normed objects is that if A and B are both normed,
then ~c[(equal A B)] holds if and only if ~c[(eql A B)] holds.  For strings and
conses, ~c[(eql A B)] holds only when ~c[(eq A B)], so any normed conses or
strings are ~ilc[equal] precisely when they are ~ilc[eq].  The potential
benefits of having normed objects include:  constant-time equality comparisons,
reduced memory usage, fast association lists, and function memoization.

Note that in our implementation, all symbols, characters, and numbers are
automatically normed, and whenever a cons is normed its car and cdr must
also be normed.~/


The Meaning of Normed in Common Lisp.

Recall that the ACL2 Objects are certain \"good\" Common Lisp symbols,
characters, strings, and numbers, and the conses which can be recursively
formed from these good atoms.

Not all properties of these objects are visible in the ACL2 logic.  An example
of an invisible property is the pointer identity of an object.  For example,
suppose we write the following.

~bv[]
 (defconst *x* (cons 1 2))
 (defconst *y* (cons 1 2))
~ev[]

In Common Lisp, ~ilc[cons] is guaranteed to provide a new pair that is distinct
from any previously created pair, so we know that *x* and *y* will be distinct
objects and we will be able to tell them apart from one another using ~c[eq].
But this difference is not visible in the ACL2 logic, and no ACL2 function can
tell *x* apart from *y*.

The normed-ness of an object is a similarly invisible property.  In Common
Lisp, invisible to ACL2, we maintain a data structure called a \"Hons Space\"
that records which objects are normed.  So, being normed is not an intrinsic
property of an object, but instead is determined by whether the object is
mentioned in this Hons Space.


Notes about Garbage Collection.

The Hons Space includes tables with pointers to every normed cons and
string.  One consequence of this is that normed objects cannot be reclaimed by
Lisp's ordinary garbage collector, even after they have become unreachable from
the perspective of an ACL2 program.

For CCL users only, ~ilc[hons-wash] is a special kind of garbage collection
that allows normed conses to be reclaimed.  For other Lisps, the only option is
to occasionally, manually clear out these Hons Space tables with
~ilc[hons-clear].")

#+(or acl2-loop-only (not hons))
(defn hons-copy (x)
  ":Doc-Section Hons-and-Memoization

~c[(hons-copy x)] returns a ~il[normed] object that is equal to X.~/

This ~il[documentation] topic relates to the experimental extension of ACL2
supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

In the logic, ~c[hons-copy] is just the identity function; we leave it enabled
and would think it odd to ever prove a theorem about it.

Under the hood, ~c[hons-copy] does whatever is necessary to produce a normed
version of X.~/

What might this involve?

If X is a symbol, character, or number, then it is already normed and nothing
is done.

If X is a string, we check if any normed version of X already exists.  If so,
we return the already-normed version; otherwise, we install X as the normed 
version for all strings that are ~ilc[equal] to X.

If X is a cons, we must determine if there is a normed version of X, or
recursively construct and install one.  Norming large cons trees can become
expensive, but there are a couple of cheap cases.  In particular, if X is
already normed, or if large subtrees of X are already normed, then not much
needs to be done.  The slowest case is norming some large ACL2 cons structure
that has no subtrees which are already normed.

Note that running ~c[hons-copy] on an object that was created with ~ilc[cons]
is often slower than just using ~ilc[hons] directly when constructing the
object.~/"

  ;; Has an under-the-hood implementation
  (declare (xargs :mode :logic)) ; for attaching early to acl2x-expansion-alist
  x)

#+(or acl2-loop-only (not hons))
(defn hons-copy-persistent (x)
  ":Doc-Section Hons-and-Memoization

~c[(hons-copy-persistent x)] returns a ~il[normed] object that is equal to X
and which will be re-normed after any calls to ~ilc[hons-clear].~/

This ~il[documentation] topic relates to the experimental extension of ACL2
supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

Logically ~c[hons-copy-persistent] is the identity; we leave it enabled and
would think it odd to ever prove a theorem about it.

Under the hood, ~c[hons-copy-persistent] is virtually identical to
~ilc[hons-copy].

The only difference is that when ~ilc[hons-clear] is used, any persistently
normed conses are automatically re-normed, and this re-norming can be carried
out more efficiently than, say, an ordinary ~ilc[hons-copy].~/~/"

  ;; Has an under-the-hood implementation
  x)

#+(or acl2-loop-only (not hons))
(defn hons (x y)
  ":Doc-Section Hons-and-Memoization

~c[(hons x y)] returns a ~il[normed] object equal to ~c[(cons x y)].~/

This ~il[documentation] topic relates to the experimental extension of ACL2
supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

In the logic, ~c[hons] is just ~ilc[cons]; we leave it enabled and would think
it odd to ever prove a theorem about it.

Under the hood, ~c[hons] does whatever is necessary to ensure that its result
is normed.~/

What might this involve?

Since the car and cdr of any normed cons must be normed, we need to
~ilc[hons-copy] x and y.  This requires little work if x and y are already
normed, but can be expensive if x or y contain large, un-normed cons
structures.

After that, we need to check whether any normed cons equal to ~c[(x . y)]
already exists.  If so, we return it; otherwise, we need to construct a new
cons for ~c[(x . y)] and install it as the normed version of ~c[(x . y)].

Generally speaking, these extra operations make ~c[hons] much slower than
~c[cons], even when given normed arguments."

  ;; Has an under-the-hood implementation
  (cons x y))

#+(or acl2-loop-only (not hons))
(defn hons-equal (x y)
  ":Doc-Section Hons-and-Memoization

~c[(hons-equal x y)] is a recursive equality check that optimizes when parts of
its arguments are ~il[normed].~/

This ~il[documentation] topic relates to the experimental extension of ACL2
supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

In the logic, ~c[hons-equal] is just ~ilc[equal]; we leave it enabled and would
think it odd to ever prove a theorem about it.

Under the hood, when ~c[hons-equal] encounters two arguments that are both
normed, it becomes a mere ~ilc[eql] check, and hence avoids the overhead of
recursively checking large cons structures for equality.~/

Note.  If ~c[hons-equal] is given arguments that do not contain many normed
objects, it can actually be much slower than ~ilc[equal]!  This is because it
checks to see whether its arguments are normed at each recursive step, and so
you are repeatedly paying the price of such checks.  See also
~ilc[hons-equal-lite], which only checks at the top level whether its arguments
are normed."

  ;; Has an under-the-hood implementation
  (equal x y))

#+(or acl2-loop-only (not hons))
(defn hons-equal-lite (x y)
  ":Doc-Section Hons-and-Memoization

~c[(hons-equal-lite x y)] is a non-recursive equality check that optimizes if
its arguments are ~il[normed].~/

This ~il[documentation] topic relates to the experimental extension of ACL2
supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

In the logic, ~c[hons-equal-lite] is just ~ilc[equal]; we leave it enabled and
would think it odd to ever prove a theorem about it.

Under the hood, ~c[hons-equal-lite] checks whether its arguments are normed,
and if so it effectively becomes a ~ilc[eql] check.  Otherwise, it immediately
calls ~ilc[equal] to determine if its arguments are equal.~/

The idea here is to strike a useful balance between ~c[equal] and
~ilc[hons-equal].  If both arguments happen to be normed, we get to use a very
fast equality comparison.  Otherwise, we just get out of the way and let
~c[equal] do its work, without the extra overhead of recursively checking
whether the subtrees of x and y are normed."

  ;; Has an under-the-hood implementation
  (equal x y))

#+(or acl2-loop-only (not hons))
(defn hons-clear (gc)
  ":Doc-Section Hons-and-Memoization

~c[(hons-clear gc)] is a drastic garbage collection mechanism that clears out
the underlying Hons Space.~/

This ~il[documentation] topic relates to the experimental extension of ACL2
supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

Logically, ~c[hons-clear] just returns nil; we leave it enabled and would think
it odd to ever prove a theorem about it.

Under the hood, ~c[hons-clear] brutally (1) clears all the tables that govern
which conses are ~il[normed], then (2) optionally garbage collects, per the
~c[gc] argument, then finally (3) re-norms the keys of ~ilc[fast-alists] and
persistently normed conses; see ~ilc[hons-copy-persistent].~/

Note.  The hash tables making up the Hons Space retain their sizes after being
cleared.  If you want to shrink them, see ~ilc[hons-resize].

Note.  CCL users might prefer ~ilc[hons-wash], which is relatively efficient
and allows for the garbage collection of normed conses without impacting their
normed status.

Note.  It is not recommended to interrupt this function.  Doing so may cause
persistently normed conses and fast alist keys to become un-normed, which might
lead to less efficient re-norming and/or violations of the fast-alist
discipline."

  ;; Has an under-the-hood implementation
  (declare (ignore gc))
  nil)

#+(or acl2-loop-only (not hons))
(defn hons-wash ()
  ":Doc-Section Hons-and-Memoization

~c[(hons-wash)] is like ~ilc[gc$] but can also garbage collect ~il[normed]
objects (CCL Only).~/

This ~il[documentation] topic relates to the experimental extension of ACL2
supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

Logically, ~c[hons-wash] just returns nil; we leave it enabled and would think
it odd to ever prove a theorem about it.

Under the hood, in CCL, ~c[hons-wash] runs a garbage collection after taking
special measures to allow normed conses to be collected.  In Lisps other than
CCL, ~c[hons-wash] does nothing.  This is because the efficient implementation
of ~c[hons-wash] is specific to the \"static honsing\" scheme which requires
CCL-specific features.~/

Why is this function needed?  Ordinarily, it is not possible to garbage collect
any normed conses.  This is because the Hons Space includes pointers to any
normed conses, and hence Lisp's garbage collector thinks these objects are
live.  To correct for this, ~c[hons-wash] (1) clears out these pointers, (2)
runs a garbage collection, then (3) re-norms any previously-normed conses which
have survived the garbage collection.

Note.  It is not recommended to interrupt this function.  Doing so may cause
persistently normed conses and fast alist keys to become un-normed, which might
lead to less efficient re-norming and/or violations of the fast-alist
discipline."

  ;; Has an under-the-hood implementation
  nil)

#+(or acl2-loop-only (not hons))
(defn hons-summary ()
  ":Doc-Section Hons-and-Memoization

~c[(hons-summary)] prints basic information about the sizes of the tables in
the current Hons Space.~/

This ~il[documentation] topic relates to the experimental extension of ACL2
supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

Logically, ~c[hons-summary] just returns nil; we leave it enabled and would
think it odd to ever prove a theorem about it.

Under the hood, this function gathers and prints some basic information about
the sizes of the tables in the Hons Space.~/

This information may be useful for deciding if you want to garbage collect
using functions such as ~ilc[hons-clear] or ~ilc[hons-wash].  It may also be
useful for determining good initial sizes for the Hons Space hash tables for
your particular computation; see ~ilc[hons-resize]."

  ;; Has an under-the-hood implementation
  nil)

(defmacro hons-resize (&key str-ht nil-ht cdr-ht cdr-ht-eql
                            addr-ht other-ht sbits
                            fal-ht persist-ht)
  ":Doc-Section Hons-and-Memoization

~c[(hons-resize ...)] can be used to manually adjust the sizes of the hash
tables that govern which ACL2 Objects are considered ~il[normed].~/

This ~il[documentation] topic relates to the experimental extension of ACL2
supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

General form:
~bv[]
 (hons-resize [:str-ht size]
              [:nil-ht size]
              [:cdr-ht size]
              [:cdr-ht-eql size]
              [:addr-ht size]
              [:other-ht size]
              [:sbits size]
              [:fal-ht size]
              [:persist-ht size])
~ev[]

Example:
~bv[]
 (hons-resize :str-ht 100000
              :addr-ht (expt 2 27))
~ev[]

Logically, ~c[hons-resize] just returns nil; we leave it enabled and would
think it odd to ever prove a theorem about it.

Under the hood, ~c[hons-resize] can be used to change the sizes of certain hash
tables in the Hons Space.

All arguments are optional.  The size given to each argument should either be
nil (the default) or a natural number.  A natural number indicates the newly
desired size for the hash table, whereas nil means \"don't resize this table.\"
Any non-natural argument is regarded as nil.~/

You may wish to call this function for two reasons.

1.  Improving Performance by Resizing Up

Since the hash tables in the Hons Space automatically grow as new objects are
normed, ~c[hons-resize] is unnecessary.  But automatic growth can be slow
because it is incremental: a particular hash table might be grown dozens of
times over the course of your application.  Using ~c[hons-resize] to pick a
more appropriate initial size may help to reduce this overhead.

2.  Reducing Memory Usage by Resizing Down

Resizing can also be used to shrink the hash tables.  This might possibly be
useful immediately after a ~c[hons-clear] to free up memory taken by the hash
tables themselves.  (Of course, the tables will grow again as you create new
normed objects.)

Advice for using ~c[hons-resize].

Note that hash tables that are already close to the desired size, or which have
too many elements to fit into the desired size, will not actually be resized.
This makes resizing relatively \"safe.\"

Note that the ~ilc[hons-summary] function can be used to see how large and how
full your hash tables are.  This may be useful in deciding what sizes you want
to give to ~c[hons-resize].

Note that ~c[hons-resize] operates by (1) allocating new hash tables, then (2)
copying everything from the old hash table into the new table.  Because of
this, for best performance you should ideally call it when the hash tables
involved are minimally populated, i.e., at the start of your application, or
soon after a ~ilc[hons-clear]."

  `(hons-resize-fn ,str-ht ,nil-ht ,cdr-ht ,cdr-ht-eql
                   ,addr-ht ,other-ht ,sbits
                   ,fal-ht ,persist-ht))

#+(or acl2-loop-only (not hons))
(defn hons-resize-fn (str-ht nil-ht cdr-ht cdr-ht-eql
                                 addr-ht other-ht sbits
                                 fal-ht persist-ht)
  (declare (ignore str-ht nil-ht cdr-ht cdr-ht-eql
                   addr-ht other-ht sbits
                   fal-ht persist-ht))
  ;; Has an under-the-hood implementation
  nil)

(defdoc fast-alists
  ":Doc-Section Hons-and-Memoization

alists with hidden hash tables for faster execution~/

This ~il[documentation] topic relates to the experimental extension of ACL2
supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

The implementation of fast alists is, in many ways, similar to that of ACL2
arrays.  Logically, ~ilc[hons-acons] is just like ~c[acons], and
~ilc[hons-get] is similar to ~ilc[assoc-equal].  But under the hood, hash
tables are associated with these alists, and, when a certain ~st[discipline] is
followed, these functions execute with hash table speeds.

What is this discipline?  Each ~c[hons-acons] operation \"steals\" the hash
table associated with the alist that is being extended.  Because of this, one
must be very conscious of which object is the most recent extension of an alist
and use that extension exclusively.

The only penalty for a failure to keep track of the most recent extension is
a loss of execution speed, not of correctness, and perhaps the annoyance of
some ~ilc[slow-alist-warning]s.

Maintaining discipline may require careful passing of a fast alist up and down
through function calls, as with any single threaded object in an applicative
setting, but there is ~st[no syntactic enforcement] that insists you only use
the most recent extension of an alist as there is for single threaded
objects (~ilc[stobj]s).  Also, even with perfectly proper code, discipline can
sometimes be lost due to user interrupts and aborts.~/

Performance Notes

The keys of fast alists are always ~il[normed].  Why?  In Common Lisp,
equal-based hashing is relatively slow, so to allow the use of eql-based hash
tables, ~ilc[hons-acons] and ~ilc[hons-get] always ~ilc[hons-copy] the keys
involved.

Since alist keys are frequently atoms, this norming activity may often be so
fast that you do not need to think about it.  But if you are going to use large
structures as the keys for your fast alist, this overhead can be significant,
and you may want to ensure that your keys are normed ahead of time.

There is ~b[no automatic mechanism] for reclaiming the hash tables that are
associated with alists.  Because of this, to avoid memory leaks, you should
call ~ilc[fast-alist-free] to remove the hash table associated with alists
that will no longer be used.")

(defn hons-assoc-equal (key alist)
  ":Doc-Section Hons-and-Memoization

~c[(hons-assoc-equal key alist)] is ~st[not fast]; it serves as the logical
definition for ~ilc[hons-get].~/

This ~il[documentation] topic relates to the experimental extension of ACL2
supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

The definition of ~c[hons-assoc-equal] is similar to that of ~ilc[assoc-equal],
except that (1) it does not require ~ilc[alistp] as a guard, and (2) it \"skips
over\" any non-conses when its alist argument is malformed.~/

We typically leave ~c[hons-get] enabled and reason about ~c[hons-assoc-equal]
instead.  One benefit of this approach is that it avoids certain \"false\"
discipline warnings that might arise from execution during theorem proving."

  (cond ((atom alist)
         nil)
        ((and (consp (car alist))
              (hons-equal key (caar alist)))
         (car alist))
        (t
         (hons-assoc-equal key (cdr alist)))))

(defdoc slow-alist-warning
  ":Doc-Section Hons-and-Memoization

warnings issued when ~ilc[fast-alists] are used inefficiently~/

This ~il[documentation] topic relates to the experimental extension of ACL2
supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

Obtaining hash-table performance from ~ilc[hons-get] requires one to follow
a certain discipline.  If this discipline is violated, you may see a \"slow
alist warning\".  This warning means that the alist you are extending or
accessing does not have a valid hash table associated with it, and hence any
accesses must be carried out with ~ilc[hons-assoc-equal] instead of
~c[gethash].~/

You can control whether or not you get a warning and, if so, whether or not a
break (an error from which you can continue) ensues.  For instance:

~bv[]
 (set-slow-alist-action :warning)  ; warn on slow access (default)
 (set-slow-alist-action :break)    ; warn and also call break$
 (set-slow-alist-action nil)       ; do not warn or break
~ev[]

The above forms expand to table events, so they can be embedded in encapsulates
and books, wrapped in ~ilc[local], and so on.")

(table hons 'slow-alist-warning :warning)

(defmacro set-slow-alist-action (action)
  (declare (xargs :guard (or (eq action :warning)
                             (eq action :break)
                             (not action))))
  `(table hons 'slow-alist-warning ,action))

(defn get-slow-alist-action (state)
  (declare (xargs :stobjs state))
  (let* ((alist   (table-alist 'hons (w state)))
         (warning (hons-assoc-equal 'slow-alist-warning alist)))
    (and (consp warning)
         (cdr warning))))

#+(or acl2-loop-only (not hons))
(defn hons-get (key alist)
  ":Doc-Section Hons-and-Memoization

~c[(hons-get key alist)] is the efficient lookup operation for
~il[fast-alists].~/

This ~il[documentation] topic relates to the experimental extension of ACL2
supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

Logically, ~c[hons-get] is just an alias for ~ilc[hons-assoc-equal]; we
typically leave it enabled and prefer to reason about ~c[hons-assoc-equal]
instead.  One benefit of this approach is that it helps to avoids \"false\"
discipline warnings that might arise from execution during theorem proving.

Under the hood, when ~c[alist] is a fast alist that is associated with a valid
hash table, ~c[hons-get] first norms ~c[key] using ~ilc[hons-copy], then
becomes a ~c[gethash] operation on the hidden hash table.~/~/"

  ;; Has an under-the-hood implementation
  (hons-assoc-equal key alist))

#+(or acl2-loop-only (not hons))
(defn hons-acons (key val alist)
  ":Doc-Section Hons-and-Memoization

~c[(hons-acons key val alist)] is the main way to create or extend
~il[fast-alists].~/

This ~il[documentation] topic relates to the experimental extension of ACL2
supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

Logically, ~c[hons-acons] is like ~ilc[acons] except that its guard does not
require ~ilc[alistp]; we leave it enabled and would think it odd to ever prove
a theorem about it.

Under the hood, two things are done differently.  First, the key is copied with
~ilc[hons-copy]; this lets us use EQL-based hash tables instead of
EQUAL-based hash tables for better performance.  Second, assuming there is a
valid hash table associated with this alist, we destructively update the hash
table by binding key to val.  The hash table will no longer be associated with
alist, but will instead be associated with the new alist returned by
~c[hons-acons].~/

Hash Table Creation

A new hash table is created by ~c[hons-acons] whenever alist is an atom.
Unlike ordinary ~c[acons], we do not require that alist be nil, and in fact you
may wish to use a non-nil value for one of two reasons.

1.  As a size hint

By default, the new hash table will be given a quite modest default capacity of
60 elements.  As more elements are added, the table may need to be resized to
accommodate them, and this resizing has some runtime cost.

When a natural number is used as a fast alist's name, we interpret it as a size
hint.  For example, ~c[(hons-acons 'foo 'bar 1000)] instructs us to use 1000 as
the initial size for this hash table and binds 'foo to 'bar.  The resulting
table should not need to be resized until more than 1000 elements are added.
We ignore size hints that request fewer than 60 elements.

Because of hash collisions, hash tables typically need to have a larger size
than the actual number of elements they contain.  The hash tables for fast
alists are told to grow when they reach 70% full.  So, an easy rule of thumb
might be: multiply the expected number of elements you need by 1.5 to keep your
hash tables about 2/3 full.

2.  As an alist name

We also frequently use a symbol for alist, and think of this symbol as the name
of the new alist.  We have found that naming alists can be valuable for two
reasons:

First, the name can be helpful in identifying fast alists that should have been
freed, see ~ilc[fast-alist-summary].

Second, names can sometimes be used to avoid a subtle and insidious
table-stealing phenomenon that occurs when using fast-alists that are
themselves normed; see ~ilc[hons-acons!].

At the moment, there is no way to simultaneously name a fast alist and also
give it a size hint.  We may eventually allow strings to include embedded name
and size components, but for now we have not implemented this capability."

  ;; Has an under-the-hood implementation
  (cons (cons key val) alist))

#+(or acl2-loop-only (not hons))
(defn hons-acons! (key val alist)
  ":Doc-Section Hons-and-Memoization

~c[(hons-acons! key val alist)] is an alternative to ~ilc[hons-acons] that
produces ~il[normed], fast alists.~/

This ~il[documentation] topic relates to the experimental extension of ACL2
supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

Logically, ~c[hons-acons!] is like ~ilc[acons] except that its guard does not
require ~ilc[alistp]; we leave it enabled and would think it odd to ever prove
a theorem about it.

Ordinarily, ~il[fast-alists] are constructed with ~ilc[hons-acons] instead of
~c[hons-acons!].  In such alists, the keys are honsed, but the conses that make
up the \"spine\" of the alist itself are ordinary conses.  In other words, it
is basically correct to say:

~bv[]
 (hons-acons key val alist) == (cons (cons (hons-copy key) val) alist)
~ev[]

In contrast, when ~c[hons-acons!] is used, the conses making up the alist
itself are also normed.  That is,

~bv[]
 (hons-acons! key val alist) == (hons (hons key val) alist)
~ev[]~/

Generally, you ~st[should not use] ~c[hons-acons!] unless you really know what
you're doing.

Drawback 1.  ~c[hons-acons!] requires you to ~ilc[hons-copy] all of the values
that are being stored in the fast alist.  If you are storing large values, this
may be expensive.

Drawback 2.  It can be more difficult to maintain the proper discipline when
using ~c[hons-acons!].  For instance, consider the following:

~bv[]
  (let ((al1 (hons-acons 1 'one (hons-acons 2 'two nil)))
        (al2 (hons-acons 1 'one (hons-acons 2 'two nil))))
     ...)
~ev[]

Here, both al1 and al2 are valid fast alists and they can be extended
independently without any trouble.  But if these alists had instead been
constructed with ~c[hons-acons!], then since both al1 and al2 are equal, normed
conses, they will literally be ~ilc[eq] and hence will refer to precisely the
same hash table.  In other words, ~c[hons-acons!] makes it relatively easy to
~st[inadvertently] steal the hash table associated with some other fast alist.
This problem can be alleviated somewhat by uniquely naming alists; see the
discussion in ~ilc[hons-acons] for details.

Despite these drawbacks, ~c[hons-acons!] is the only way besides
~ilc[hons-shrink-alist!] to generate a fast alist that is normed.  It is not
adequate to ~ilc[hons-copy] a fast alist that was generated by ordinary
~ilc[hons-acons] calls, because this would produce an EQUAL-but-not-EQ object,
and this new object would not be associated with the fast alist's hash table."

  ;; Has an under-the-hood implementation
  (cons (cons key val) alist))

#+(or acl2-loop-only (not hons))
(defn hons-shrink-alist (alist ans)
  ":Doc-Section Hons-and-Memoization

~c[(hons-shrink-alist alist ans)] can be used to eliminate \"shadowed pairs\"
from an alist or to copy ~il[fast-alists].~/

This ~il[documentation] topic relates to the experimental extension of ACL2
supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

Logically, ~c[hons-shrink-alist] is defined as follows:

~bv[]
 (cond ((atom alist)
        ans)
       ((atom (car alist))
        (hons-shrink-alist (cdr alist) ans))
       ((hons-assoc-equal (car (car alist)) ans)
        (hons-shrink-alist (cdr alist) ans))
       (t
        (hons-shrink-alist (cdr alist) (cons (car alist) ans))))
~ev[]

The alist argument need not be a fast alist, and it is not modified by the
shrink.

Typically ans is set to nil or some other atom.  In this case, shrinking
produces a new, fast alist which is like alist except that (1) any
\"malformed,\" atomic entries have been removed, (2) all \"shadowed pairs\"
have been removed, and (3) incidentally, the surviving elements have been
reversed.  This can be useful as a way to clean up any unnecessary bindings in
alist, or as a way to obtain a \"deep copy\" of a fast alist that can extended
independently from the original while maintaining discipline.

When ans is not an atom, good discipline requires that it is a fast alist.  In
this case, ~c[hons-shrink-alist] steals the hash table for ans and extends it
with all of the bindings in alist that are not in ans.  From the perspective of
~ilc[hons-assoc-equal], you can think of the resulting alist as being basically
similar to ~c[(append ans alist)], but in a different order.~/~/"

  ;; Has an under-the-hood implementation
  (cond ((atom alist)
         ans)
        ((atom (car alist))
         (hons-shrink-alist (cdr alist) ans))
        ((hons-assoc-equal (car (car alist)) ans)
         (hons-shrink-alist (cdr alist) ans))
        (t
         (hons-shrink-alist (cdr alist) (cons (car alist) ans)))))

#+(or acl2-loop-only (not hons))
(defn hons-shrink-alist! (alist ans)
  ":Doc-Section Hons-and-Memoization

~c[(hons-shrink-alist! alist ans)] is an alternative to ~ilc[hons-shrink-alist]
that produces a ~il[normed] result.~/

This ~il[documentation] topic relates to the experimental extension of ACL2
supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

Logically this function is just ~c[hons-shrink-alist]; we leave it enabled and
would think it odd to ever prove a theorem about it.

Under the hood, this is the same as ~c[hons-shrink-alist] except that it uses
something like ~ilc[hons-acons!] instead of ~ilc[hons-acons].  You generally
~st[should not use] this function unless you really know what you're doing and
understand the drawbacks discussed in ~ilc[hons-acons!].~/~/"

  ;; Has an under-the-hood implementation
  (hons-shrink-alist alist ans))

#+(or acl2-loop-only (not hons))
(defn fast-alist-len (alist)
  ":Doc-Section Hons-and-Memoization

~c[(fast-alist-len alist)] counts the number of unique keys in a fast alist.~/

This ~il[documentation] topic relates to the experimental extension of ACL2
supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

Logically this function counts how many elements would remain in the alist were
we to shrink it with ~ilc[hons-shrink-alist].

Good discipline requires that the alist is a fast alist.  Under the hood, when
the alist is a fast alist we can simply call the underlying Common Lisp
function ~c[hash-table-count] on the associated hash table, which is very fast
and doesn't require us to actually shrink the alist.~/~/"

  ;; Has an under-the-hood implementation
  (len (hons-shrink-alist alist nil)))

#+(or acl2-loop-only (not hons))
(defn fast-alist-free (alist)
  ":Doc-Section Hons-and-Memoization

~c[(fast-alist-free alist)] throws away the hash table associated with a fast
alist.~/

This ~il[documentation] topic relates to the experimental extension of ACL2
supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

Logically, this function is the identity; we leave it enabled and would think
it odd to ever prove a theorem about it.

Under the hood, ~c[fast-alist-free] removes the hash table associated with this
alist, if one exists.  This effectively converts the alist into an ordinary
alist.~/

Because there is no automatic mechanism for freeing the hash tables used in
fast alists, to avoid memory leaks you should manually free any alists that
will no longer be used.  You may find ~ilc[fast-alist-summary] useful in
tracking down alists that were not properly freed.

It is safe to call ~c[fast-alist-free] on any argument, including fast alists
that have already been freed and objects which are not alists at all."

  ;; Has an under-the-hood implementation
  alist)

#+(or acl2-loop-only (not hons))
(defn fast-alist-summary ()
  ":Doc-Section Hons-and-Memoization

~c[(fast-alist-summary)] prints some basic statistics about any current fast
alists.~/

This ~il[documentation] topic relates to the experimental extension of ACL2
supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

Logically, ~c[fast-alist-summary] just returns nil; we leave it enabled and
would think it odd to ever prove a theorem about it.

Under the hood, this function gathers and prints some basic statistics about
the current fast alists.  It may be useful for identifying fast alists that
should have been freed with ~ilc[fast-alist-free]~/~/"

  ;; Has an under-the-hood implementation
  nil)

(defn cons-subtrees (x al)
  ":Doc-Section Hons-and-Memoization

~c[(cons-subtrees x nil)] builds a fast alist that associates each subtree
of X with T, without duplication.~/

This ~il[documentation] topic relates to the experimental extension of ACL2
supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].
~/~/"

  (cond ((atom x)
         al)
        ((hons-get x al)
         al)
        (t
         (cons-subtrees
          (car x)
          (cons-subtrees (cdr x) (hons-acons x t al))))))

#+(or acl2-loop-only (not hons))
(defn number-subtrees (x)
  ":Doc-Section Hons-and-Memoization

~c[(number-subtrees x)] returns the number of distinct subtrees of X, in the
sense of ~ilc[equal]~/

This ~il[documentation] topic relates to the experimental extension of ACL2
supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

In the logic, ~c[number-subtrees] is defined as the length of
~ilc[cons-subtrees].

Under the hood, we first ~ilc[hons-copy] X to obtain a normed version, then
count the number of unique conses in X using an EQ hash table.~/~/"

  ;; Has an under-the-hood implementation
  (len (cons-subtrees x 'number-subtrees)))

#+(or acl2-loop-only (not hons))
(defn clear-hash-tables ()
  ":Doc-Section Hons-and-Memoization

deprecated feature~/

This ~il[documentation] topic relates to the experimental extension of ACL2
supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

Deprecated.  Calls ~ilc[clear-memoize-tables] and then ~ilc[hons-clear] or
~ilc[hons-wash], whichever makes sense for the underlying Common Lisp.~/~/"

  ;; Has an under-the-hood implementation
  nil)

(defn flush-hons-get-hash-table-link (alist)
  ":Doc-Section Hons-and-Memoization

deprecated feature~/

This ~il[documentation] topic relates to the experimental extension of ACL2
supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

Deprecated.  Alias for ~ilc[fast-alist-free]~/~/"

  (fast-alist-free alist))

(in-theory (disable

; The execution of honsing and fast alist functions during theorem proving
; could be very subtle.  It is easy to imagine discipline failures, inadvertent
; norming, inadvertent clearing of hash tables, etc.  We try to prevent this at
; least somewhat by disabling the executable counterparts of many of the above
; functions.  This is not a total solution, but seems like a good idea anyway.

            ;; These would probably be pretty harmless
            (:executable-counterpart hons)
            (:executable-counterpart hons-copy)
            (:executable-counterpart hons-copy-persistent)
            (:executable-counterpart hons-summary)
            (:executable-counterpart fast-alist-summary)

            ;; These could be particularly bad to call by mistake
            (:executable-counterpart hons-clear)
            (:executable-counterpart hons-wash)
            (:executable-counterpart hons-resize-fn)

            ;; These could lead to discipline failures
            (:executable-counterpart hons-get)
            (:executable-counterpart hons-acons)
            (:executable-counterpart hons-acons!)
            (:executable-counterpart hons-shrink-alist)
            (:executable-counterpart hons-shrink-alist!)
            (:executable-counterpart fast-alist-len)
            (:executable-counterpart fast-alist-free)
            (:executable-counterpart flush-hons-get-hash-table-link)
            ))

; For some additional helper functions and lemmas, see the files
; books/misc/hons-help.lisp and books/misc/hons-help2.lisp.
