; seed-random -- create and save random seeds
; Copyright (C) 2008-2010 Centaur Technology
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

(defun seed-random$-fn (name freshp)
  (declare (xargs :guard t)
           (ignore name freshp))
  nil)

(defmacro seed-random$ (name &key (freshp 't))
  ":Doc-Section random$
Influence the random numbers produced by ~ilc[random$]~/

General form:
~bv[]
 (seed-random name
              [:freshp t/nil]  ;; default t
              )
~ev[]

Hypothetical example:
~bv[]
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
~ev[]

Logically, ~c[seed-random$] ignores its arguments and just returns ~c[nil]; we
leave it enabled and would think it odd to ever prove a theorem about it.

Under the hood, ~c[seed-random$] influences the behavior of ~ilc[random$].
Note that in its implementation, the ACL2 function ~c[(random$ limit state)]
basically just calls ~c[(random limit)] to produce its result.

To understand ~c[seed-random$], it is useful to recall some features of Common
Lisp:

 - A ~c[random-state] is an implementation-defined data type that is used by
   the ~c[random] function to produce random numbers.

 - In particular, ~c[(random limit &optional random-state)] can use some
   particular ~c[random-state] or, by default, uses whatever ~c[random-state]
   is currently bound to the special variable ~c[*random-state*].

 - A fresh, \"randomly initialized\" ~c[random-state] can be produced with
   ~c[(make-random-state t)].

 - The current ~c[*random-state*] can be copied with
   ~c[(make-random-state nil)].

So, what does ~c[seed-random$] do?

We maintain a hidden association list that maps names to random-states.  These
names can be any ACL2 objects, but we typically use symbols.

When ~c[seed-random$] is called with a name that is already bound to some
state, we just restore ~c[*random-state*] to this state.  This effectively
resets the random number generator so that it produces the same random numbers
as before.

When ~c[seed-random$] is called with a name that has not been bound yet, its
behavior depends on the optional ~c[freshp] keyword-argument.

When ~c[freshp] is ~c[t] (the default), we construct a \"randomly initialized\"
~c[random-state], bind ~c[name] to it, and install it as ~c[*random-state*].
In other words, when ~c[foo] has never been used as a name before,
~c[(seed-random$ 'foo)] effectively initializes the random number generator to
a truly random state.

On the other hand, when ~c[freshp] is ~c[nil] we simply copy and name the
current ~c[*random-state*].  It appears that, at least on CCL, the
~c[*random-state*] starts the same upon every invocation of ACL2.  Hence, if
you launch ACL2 and then immediately invoke
~bv[]
 (seed-random 'seed :freshp nil)
~ev[]
you can obtain a sequence of random numbers that you can return to even
after restarting ACL2, and which can be returned to at any time during the
session by just calling ~c[(seed-random 'seed)].~/~/"

  `(seed-random$-fn ,name ,freshp))

(defttag seed-random$)

(progn!
 (set-raw-mode t)

 (defparameter *random-seeds* nil)

 (defun seed-random$-fn (name freshp)
   (let ((look (assoc-equal name *random-seeds*)))
     (cond (look
            ;(format t "Restoring *random-state* to ~a.~%" (cdr look))
            (setq *random-state* (make-random-state (cdr look))))
           (freshp
            (let* ((new-st (make-random-state t)))
              ;(format t "Fresh seed ~a: ~a.~%" name new-st)
              (setq *random-seeds* (acons name new-st *random-seeds*))
              (setq *random-state* (make-random-state new-st))))
           (t
            (let ((new-st (make-random-state nil)))
              ;(format t "Copy seed to ~a: ~a.~%" name new-st)
              (setq *random-seeds* (acons name new-st *random-seeds*))))))
   nil))


;; Basic tests to make sure it works

(local
 (progn

   (include-book "tools/defconsts" :dir :system)
   (include-book "tools/bstar" :dir :system)
   (include-book "misc/assert" :dir :system)

   (defund random-list (len limit state)
     (declare (xargs :guard (and (natp len)
                                 (posp limit))
                     :stobjs state))
     (if (zp len)
         (mv nil state)
       (b* (((mv r1 state) (random$ limit state))
            ((mv rest state) (random-list (- len 1) limit state)))
         (mv (cons r1 rest) state))))

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

