; seed-random -- create and save random seeds
; Copyright (C) 2008-2010 Centaur Technology
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

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(include-book "tools/include-raw" :dir :system)

(defxdoc seed-random$
  :parents (random$)
  :short "Influence the random numbers produced by @(see random$)."
  :long "<p>General form:</p>

@({
     (include-book \"centaur/misc/seed-random\" :dir :system)
     (seed-random name
                  [:freshp t/nil]  ;; default t
                  )
})

<p>Hypothetical example:</p>

@({
   (seed-random 'foo) ;; randomly seed the generator, name this seed 'foo
   (random$ 50 state) --> (mv 31 state)
   (random$ 50 state) --> (mv 49 state)
   (random$ 50 state) --> (mv 2 state)
   (random$ 50 state) --> (mv 23 state)
   (random$ 50 state) --> (mv 15 state)

   (seed-random 'foo) ;; return to the seed named 'foo
   (random$ 50 state) --> (mv 31 state)
   (random$ 50 state) --> (mv 49 state)
   (random$ 50 state) --> (mv 2 state)

   (seed-random 'bar :freshp nil) ;; copy current seed, name it 'bar
   (random$ 50 state) --> (mv 23 state)
   (random$ 50 state) --> (mv 15 state)

   (seed-random 'foo) ;; return to 'foo
   (random$ 50 state) --> (mv 31 state)

   (seed-random 'bar) ;; return to 'bar
   (random$ 50 state) --> (mv 23 state)
   (random$ 50 state) --> (mv 15 state)
})

<p>Logically, @('seed-random$') ignores its arguments and just returns
@('nil').  We leave it enabled and would think it odd to ever prove a theorem
about it.</p>

<p>Under the hood, @('seed-random$') influences the behavior of @(see random$).
Note that in its implementation, the ACL2 function @('(random$ limit state)')
basically just calls @('(random limit)') to produce its result.  To understand
@('seed-random$'), it is useful to recall some features of Common Lisp:</p>

<ul>

<li>A @('random-state') is an implementation-defined data type that is used by
the @('random') function to produce random numbers.</li>

<li>In particular, @('(random limit &optional random-state)') can use some
particular @('random-state') or, by default, uses whatever @('random-state') is
currently bound to the special variable @('*random-state*').</li>

<li>A fresh, \"randomly initialized\" @('random-state') can be produced with
@('(make-random-state t)').</li>

<li>The current @('*random-state*') can be copied with @('(make-random-state
nil)').</li>

</ul>

<p>So, what does @('seed-random$') do?</p>

<p>We maintain a hidden association list that maps names to random-states.
These names can be any ACL2 objects, but we typically use symbols.</p>

<p>When @('seed-random$') is called with a name that is already bound to some
state, we just restore @('*random-state*') to this state.  This effectively
resets the random number generator so that it produces the same random numbers
as before.</p>

<p>When @('seed-random$') is called with a name that has not been bound yet,
its behavior depends on the optional @('freshp') keyword-argument.</p>

<p>When @('freshp') is @('t') (the default), we construct a \"randomly
initialized\" @('random-state'), bind @('name') to it, and install it as
@('*random-state*').  In other words, when @('foo') has never been used as a
name before, @('(seed-random$ 'foo)') effectively initializes the random number
generator to a truly random state.</p>

<p>On the other hand, when @('freshp') is @('nil') we simply copy and name the
current @('*random-state*').  It appears that, at least on CCL, the
@('*random-state*') starts the same upon every invocation of ACL2.  Hence, if
you launch ACL2 and then immediately invoke</p>

@({
    (seed-random 'seed :freshp nil)
})

<p>you can obtain a sequence of random numbers that you can return to even
after restarting ACL2, and which can be returned to at any time during the
session by just calling @('(seed-random 'seed)').</p>")

(defun seed-random$-fn (name freshp)
  (declare (xargs :guard t)
           (ignore name freshp))
  nil)

(defmacro seed-random$ (name &key (freshp 't))
  `(seed-random$-fn ,name ,freshp))

(defttag seed-random$)

(include-raw "seed-random-raw.lsp")


;; Basic tests to make sure it works

(local
 (progn

   (include-book "std/util/defconsts" :dir :system)
   (include-book "std/util/bstar" :dir :system)
   (include-book "std/testing/assert-bang" :dir :system)

; Matt K. mod: Replace random-list with the tail-recursive version from
; system/random.lisp, to avoid a stack overflow in LispWorks.

   (local (include-book "system/random" :dir :system)) ; for random-list

   (defund random-list (n limit state)
     (declare (xargs :guard (and (natp n)
                                 (posp limit))))
     (random-list-aux n limit nil state))

   (defund random-list-aux (n limit acc state)
     (declare (xargs :guard (and (natp n)
                                 (posp limit)
                                 (true-listp acc))))
     (if (zp n)
         (mv (reverse acc) state)
       (b* (((mv x1 state) (random$ limit state)))
         (random-list-aux (- n 1) limit (cons x1 acc) state))))

   (value-triple (seed-random$ 'foo))
   (defconsts (*test1-a* state) (random-list 1000 100000 state))

   (value-triple (seed-random$ 'bar :freshp nil))
   (defconsts (*test1-b* state) (random-list 1000 100000 state))

   (value-triple (seed-random$ 'foo))
   (defconsts (*test2-ab* state) (random-list 2000 100000 state))

   (assert! (equal (append *test1-a* *test1-b*) *test2-ab*))

   (value-triple (seed-random$ 'bar))
   (defconsts (*test2-b* state) (random-list 1000 100000 state))

   (assert! (equal *test1-b* *test2-b*))))
