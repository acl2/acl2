; NREV - A "safe" implementation of something like nreverse
; Copyright (C) 2014 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "NREV")
(include-book "std/stobjs/absstobjs" :dir :system)
(include-book "std/stobjs/clone" :dir :system)
(include-book "std/lists/list-defuns" :dir :system)
(local (include-book "std/lists/rcons" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(local (in-theory (enable rcons)))

(defxdoc nrev
  :parents (reverse)
  :short "A safe mechanism for implementing something like @('nreverse'), for
writing tail-recursive functions that use less memory by avoiding the final
@(see reverse) step."

  :long "<h3>Motivation</h3>

<p>To avoid stack overflows, you sometimes need tail-recursive executable
versions of your functions.  These tail-recursive functions often produce their
elements in the reverse of the desired order.  For instance, here is a basic,
tail-recursive <a
href='https://en.wikipedia.org/wiki/Map_(higher-order_function)'>map</a>:</p>

@({
    (defun map-exec (x acc)
      (if (atom x)
          acc
        (map-exec (cdr x) (cons (f (car x)) acc))))
})

<p>But this produces elements in the wrong order.  To correct for this, you
might explicitly reverse the elements, e.g.,:</p>

@({
    (defun map (x)
      (mbe :logic (if (atom x)
                      nil
                    (cons (f (car x)) (map (cdr x))))
           :exec (reverse (map-exec x nil))))
})

<p>This successfully avoids stack overflows, but since @(see reverse) is
applicative, this approach allocates twice as many conses as the naive, non
tail-recursive version.</p>

<p>In Common Lisp, we could avoid this overhead using @('nreverse'), a
destructive routine that can reverse a list in-place by swapping pointers.  But
since @('nreverse') is destructive, it wouldn't be sound to just make it
generally available in ACL2.</p>

<p>Even so, we would like to have something like @('nreverse') that would allow
us to write tail-recursive versions of @('map') without having to allocate
double the conses.  In principle, it is okay to use @('nreverse') here because
we are only tampering with fresh conses that are not reachable from anywhere
else in the program.  (Well, that's almost true; if @('map-exec') were @(see
memoize)d, then we could get into trouble.)</p>

<h3>Solution</h3>

<p>@('nrev') is, we believe, a safe mechanism for writing tail-recursive
functions that can (at your option) avoid this double consing by using
destructive, under-the-hood operations.</p>

<p>Without trust tags, @('nrev') is roughly on par with the ordinary
@('reverse') based solution:</p>

<ul>

<li>Memory &mdash; same as @('reverse'), i.e., still twice as many as the non
tail-recursive version.</li>

<li>Runtime &mdash; perhaps around 1.3x worse than @('reverse') due to the
@(see acl2::stobj) overhead.</li>

</ul>

<p>With a trust tag, @('nrev') is roughly on par with the @('nreverse')
solution:</p>

<ul>

<li>Memory &mdash; same as @('nreverse'), i.e., avoids the double consing
problem.</li>

<li>Runtime &mdash; perhaps around 1.25x worse than @('nreverse') due to the
@(see acl2::stobj) overhead, but still faster than a traditional @('reverse')
based solution.</li>

</ul>

<h3>Loading @('nrev')</h3>

<p>For the pure ACL2 (no trust tags) version, you can use:</p>

@({
    (include-book \"centaur/nrev/pure\" :dir :system)
})

<p>For the optimized (trust tags) version, you can instead load:</p>

@({
    (include-book \"centaur/nrev/fast\" :dir :system)
})

<p>Note that it's perfectly fine to start with the pure book and then load the
fast version later.  Loading the fast version will \"retroactively\" optimize
all functions that are based on @('nrev').</p>

<h3>Using @('nrev')</h3>

<p>These books implement an abstract stobj called @('nrev').  The logical story
is that @('nrev') is just a list.  The fundamental operation on @('nrev') is
@(see nrev-push), which logically conses \"onto the right,\" like @(see rcons).
Once you have pushed the desired elements, you can get them back out in queue
order using @(see nrev-finish).</p>

<p>See @(see nrev-demo) for a basic example.</p>")

(defsection nrev$c
  :parents (nrev)
  :short "The concrete @('nrev') stobj."
  :long "@(def nrev$c)"
  :autodoc nil

  (defstobj nrev$c
    (nrev$c-acc :type (satisfies true-listp)
                :initially nil)
    (nrev$c-hint :type t :initially nil)))


(defsection nrev-fix
  :parents (nrev)
  :short "Identity function for @('nrev')."
  :long "<box><p><b>Signature:</b> @('(nrev-fix nrev)') &rarr; @('nrev'')</p></box>

<p>In the logic, this simply sets:</p>

@({
     nrev' := (list-fix nrev)
})

<p>In both the pure and optimized implementations, this is a no-op that just
returns @('nrev') unchanged.</p>

<p>This is a fast operation.  It is generally useful to call @('(nrev-fix
nrev)') in your function's base case, to avoid needing @(see true-listp)
hypotheses.</p>"

  (defun nrev$a-fix (nrev$a)
    (declare (xargs :guard t))
    (list-fix nrev$a))

  (defun-inline nrev$c-fix (nrev$c)
    (declare (xargs :stobjs nrev$c))
    nrev$c))


(defsection nrev-push
  :parents (nrev)
  :short "Fundamental operation to extend @('nrev') with a new element."

  :long "<box><p><b>Signature:</b> @('(nrev-push a nrev)') &rarr;
@('nrev'')</p></box>

<p>In the logic, this sets:</p>

@({
    nrev' := (rcons a nrev)
})

<p>In the pure ACL2 implementation, the underlying representation of @('nrev')
keeps the elements in reverse order, so @('nrev-push') takes just a single
cons.</p>

<p>In the optimized implementation, this operation creates a cons and then
destructively extends the rightmost cons cell, like a Common Lisp @('rplacd')
operation.</p>"

  (defun nrev$a-push (a nrev$a)
    (declare (xargs :guard t))
    (rcons a nrev$a))

  (defun nrev$c-push (a nrev$c)
    (declare (xargs :stobjs nrev$c))
    (let* ((acc    (nrev$c-acc nrev$c))
           (acc    (cons a acc)))
      (update-nrev$c-acc acc nrev$c))))


(defsection nrev-copy
  :parents (nrev)
  :short "Slow operation to copy the current contents of @('nrev'), without
destroying it."

  :long "<box><p><b>Signature:</b> @('(nrev-copy nrev)') &rarr;
@('list')</p></box>

<p>This is an unusual, expensive operation.  It may occasionally be useful as a
way to inspect the contents of @('nrev') without modifying @('nrev').</p>

<p>In the logic, this just returns @('(list-fix nrev)').</p>

<p>In the pure ACL2 implementation, the underlying representation of @('nrev')
keeps the elements in reverse order, so @('nrev-copy') just calls @(see
reverse) to reverse these elements and give you a list in the proper order.
This, of course, takes O(n) conses.</p>

<p>In the optimized implementation, we similarly need to create a copy of the
current contents of @('nrev'), so this again takes O(n) conses.</p>"

  (defun nrev$a-copy (nrev$a)
    (declare (xargs :guard t))
    (list-fix nrev$a))

  (defun nrev$c-copy (nrev$c)
    (declare (xargs :stobjs nrev$c))
    (reverse (nrev$c-acc nrev$c))))


(defsection nrev-set-hint
  :parents (nrev)
  :short "Set a candidate list to try and preserve existing conses when finishing an nrev."
  :long
  "<box><p><b>Signature:</b> @('(nrev-set-hint a nrev)') &rarr;
@('nrev'')</p></box>

<p>In the common use case where an nrev is accumulating a transformed list (as
in a @(see std::defprojection)), sometimes it may be the case that few of the
list elements are actually transformed.  In these cases it may be desirable to
return a list that has as many conses shared with the original list as
possible.  This way, fewer total conses are in your working footprint.</p>

<p>To support this, nrev allows setting a hint, which in such a case should
just be the original, untransformed list.</p>

<p>In the logical story, this doesn't do anything but return the unchanged
nrev.  In the pure ACL2 implementation, it just sets an extra stobj field to
the hint.  However, in the optimized implementation, when there is a hint set,
then before returning the final list, we check to see if it has a suffix in
common with the hint, and if so, replace that suffix with the one from the
hint.  Therefore, we return something equal to the list we've accumulated, but
with as many of the conses from the hint as possible.</p>"

  (defun nrev$a-set-hint (a nrev$a)
    (declare (xargs :guard t)
             (ignore a))
    (list-fix nrev$a))

  (defun nrev$c-set-hint (a nrev$c)
    (declare (xargs :stobjs nrev$c))
    (update-nrev$c-hint a nrev$c)))


(defsection nrev-finish
  :parents (nrev)
  :short "Final step to extract the elements from an @('nrev')."

  :long "<box><p><b>Signature:</b> @('(nrev-finish nrev)') &rarr; @('(mv list
nrev')')</p></box>

<p>In the logic, this returns @('(list-fix nrev)') as @('list'), and also
updates @('nrev' := nil').</p>

<p>In the pure ACL2 implementation, this function is very much like @(see
nrev-copy).  The underlying representation of @('nrev') keeps the elements in
reverse order, so @('nrev-finish') has to reverse them, e.g., via @(see
reverse), which of course is O(n).</p>

<p>In the optimized implementation, we have already constructed the list in
reverse order, so we can simply return it, saving all that consing.  For this
to be sound, we must simultaneously clear out @('nrev')&mdash;otherwise, a
subsequent @(see nrev-push) would be destructively modifying conses that are
visible elsewhere in the program.</p>"

  (defun nrev$a-finish (nrev$a)
    (declare (xargs :guard t))
    (let* ((elems (list-fix nrev$a)))
      (mv elems nil)))

  (defun nrev$c-finish (nrev$c)
    (declare (xargs :stobjs nrev$c))
    (let* ((elems  (reverse (nrev$c-acc nrev$c)))
           (nrev$c (update-nrev$c-acc nil nrev$c)))
      (mv elems nrev$c))))


(defsection nrev-stobj
  :parents (nrev)
  :short "Definition of the @('nrev') abstract stobj."
  :long "@(def nrev)"

  (defun create-nrev$a ()
    (declare (xargs :guard t))
    nil)

  (defun nrev-corr (nrev$c nrev$a)
    (declare (xargs :stobjs nrev$c))
    (equal (nrev$c-copy nrev$c)
           (nrev$a-copy nrev$a))))

(defabsstobj-events nrev
  :foundation nrev$c
  :recognizer (nrev$p :logic true-listp
                      :exec nrev$cp)
  :creator (acl2::create-nrev :logic create-nrev$a
                              :exec create-nrev$c)
  :corr-fn nrev-corr
  :exports ((nrev-fix :logic nrev$a-fix
                      :exec nrev$c-fix$inline)
            (nrev-copy :logic nrev$a-copy
                       :exec nrev$c-copy)
            (nrev-push :logic nrev$a-push
                       :exec nrev$c-push)
            (nrev-set-hint :logic nrev$a-set-hint
                           :exec nrev$c-set-hint)
            (nrev-finish :logic nrev$a-finish
                         :exec nrev$c-finish)))

; Critical: prohibit any further use of the raw concrete accessors, since in
; the fast book we may smash their definitions.

(push-untouchable nrev$c-acc t)
(push-untouchable update-nrev$c-acc t)


(defsection with-local-nrev
  :parents (nrev)
  :short "Wrapper for @(see with-local-stobj) for common cases of using @(see
nrev)."

  (defmacro with-local-nrev (form)
    `(with-local-stobj nrev
       (mv-let (elems nrev)
         (let ((nrev ,form))
           (nrev-finish nrev))
         elems))))

(defsection nrev2
  :parents (nrev)
  :short "An extra @(see nrev) created with @(see acl2::defstobj-clone)."
  :long "<p>This may be useful if you need two @(see nrev) stobjs at once.</p>
@(def nrev2)"

  :autodoc nil
  (acl2::defstobj-clone nrev2 nrev :suffix "2"))


(defsection nrev-append
  :parents (nrev)
  :short "Add several elements into @('nrev') at once."
  :long "<p>We just leave this enabled.</p>"

  (defun nrev-append (x nrev)
    (declare (xargs :guard t :stobjs nrev))
    (mbe :logic
         (non-exec (append nrev (list-fix x)))
         :exec
         (if (atom x)
             (nrev-fix nrev)
           (let ((nrev (nrev-push (car x) nrev)))
             (nrev-append (cdr x) nrev))))))
