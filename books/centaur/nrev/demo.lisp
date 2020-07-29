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
(include-book "pure")
(include-book "std/util/define" :dir :system)
(local (include-book "std/lists/top" :dir :system))

(defsection nrev-demo
  :parents (nrev)
  :short "Short demonstration of using nrev for a basic map function.")

(local (xdoc::set-default-parents nrev-demo))

(define f (x)
  :short "The function we'll project."
  (let ((x (ifix x)))
    (+ x x)))

(define map-spec (x)
  :short "Naive, ordinary implementation of mapping @(see f)."
  (if (atom x)
      nil
    (cons (f (car x))
          (map-spec (cdr x)))))

(define map-tr (x acc)
  :short "Conventional tail-recursive core for mapping @(see f)."
  :long "<p>This returns the elements in backwards order.</p>"
  (if (atom x)
      acc
    (map-tr (cdr x) (cons (f (car x)) acc)))
  ///
  (defthm map-tr-correct
    (equal (map-tr x acc)
           (revappend (map-spec x) acc))
    :hints(("Goal" :in-theory (enable map-spec)))))

(define map-traditional (x)
  :short "Conventional @(see reverse)-based @(see mbe) of @(see map-spec) and
  @(see map-tr)."
  (mbe :logic (map-spec x)
       :exec (reverse (map-tr x nil))))


(define map-impl (x nrev)
  :short "@(see nrev)-based tail-recursive core for mapping @(see f)."
  :long "<p>This is essentially similar to @(see map-tr).</p>

<p>The most interesting part of this is the correctness theorem:</p>

<ul>

<li>Thanks to abstract stobjs, we can just write our theorem as if @('nrev') is
an ordinary list.</li>

<li>Thanks to the @(see rcons)-based logical story for @('nrev'), our theorem
doesn't have to be in terms of @(see revappend) as it does in @(see map-tr).
Instead, we can just use ordinary @(see append).</li>

</ul>"
  (b* (((when (atom x))
        (nrev-fix nrev))
       (nrev (nrev-push (f (car x)) nrev)))
    (map-impl (cdr x) nrev))
  ///
  (defthm map-impl-correct
    (equal (map-impl x nrev)
           (append nrev (map-spec x)))
    :hints(("Goal" :in-theory (enable map-spec)))))

(define my-map (x)
  :short "@(see nrev)-based @(see mbe) of @(see map-spec) and @(see map-impl)."

  :long "<p>This is a bit more involved than @(see map-traditional) because we
need to use @(see with-local-stobj) to create our temporary accumulator, run
our implementation, and then extract the results with @(see nrev-finish).
Fortunately that can all be wrapped up into @(see with-local-nrev).</p>"

  (mbe :logic (map-spec x)
       :exec (with-local-nrev (map-impl x nrev))))

; Performance comparisons

#||
(include-book
 "centaur/misc/memory-mgmt" :dir :system)

(acl2::set-max-mem (* 10 (expt 2 30)))

:q

(in-package "NREV")

(defconst *ins*
  (loop for i fixnum from 1 to 100000000 collect i))

(progn
; Unprincipled use of loop, for comparison.
; 1.56 seconds realtime, 1.56 seconds runtime
; (1,600,000,144 bytes allocated).
  (acl2::hl-system-gc)
  (len (time$ (loop for e in *ins* collect (f e)))))

(progn
; Unprincipled use of nreverse, for comparison.
; 2.15 seconds realtime, 2.15 seconds runtime
; (1,600,000,128 bytes allocated).
  (defun map-nreverse (x)
    (declare (xargs :guard t))
    (mbe :logic (map-spec x)
         :exec (nreverse (map-tr x nil))))
  (acl2::hl-system-gc)
  (len (time$ (map-nreverse *ins*))))

(progn
; Naive version.  You may need, e.g., "acl2 -Z 4096M", to avoid stack overflow
; 3.39 seconds realtime, 3.39 seconds runtime
; (1,600,000,128 bytes allocated).
  (acl2::hl-system-gc)
  (len (time$ (map-spec *ins*))))

(progn
; Traditional, pure ACL2 solution using tail-recursion and reverse.
; 2.88 seconds realtime, 2.88 seconds runtime
; (3,200,000,128 bytes allocated).
  (acl2::hl-system-gc)
  (len (time$ (map-traditional *ins*))))

(progn
; Pure ACL2 nrev solution (no ttags)
; (MY-MAP *INS*) took
; 3.81 seconds realtime, 3.81 seconds runtime
; (3,200,000,160 bytes allocated).
  (acl2::hl-system-gc)
  (len (time$ (my-map *ins*))))

; (/ 3.81 2.88) = 1.3x slower

(lp)
(include-book "fast")
:q

(progn
; Optimized ACL2 nrev solution (ttags)
; (MY-MAP *INS*) took
; 2.71 seconds realtime, 2.70 seconds runtime
; (1,600,000,176 bytes allocated).
  (acl2::hl-system-gc)
  (len (time$ (my-map *ins*))))

; (/ 2.71 2.15) = 1.26x slower than unprincipled nreverse
; (/ 2.71 1.56) = 1.73x slower than unprincipled loop

(lp)

||#


(include-book "fast")
(include-book "std/testing/assert-bang" :dir :system)

; Some basic sanity checks.

(defun foo (nrev)
  (declare (xargs :stobjs nrev))
  (nrev-copy nrev))

(memoize 'foo)

(make-event
 ;; Check that we're properly clearing foo's memo tables in nrev-push
 ;; and nrev-finish.
 (b* (((mv & nrev) (nrev-finish nrev))
      (nrev (nrev-push 1 nrev))
      (elems1 (foo nrev))
      (nrev (nrev-push 2 nrev))
      (elems2 (foo nrev))
      ((mv & nrev) (nrev-finish nrev))
      (elems3 (foo nrev)))
   (or (and (equal elems1 '(1))
            (equal elems2 '(1 2))
            (not elems3))
       (er hard? "memo test failed: ~x0 ~x1 ~x2" elems1 elems2 elems3))
   (mv nil '(value-triple :success) state nrev)))

;; basic sanity checks
(assert! (equal (my-map '(1 2 3))
                (map-spec '(1 2 3))))

(assert! (equal (my-map '(1 2 3 . 4))
                (map-spec '(1 2 3 . 4))))

(assert! (equal (my-map nil)
                (map-spec nil)))

(assert! (equal (my-map 5)
                (map-spec 5)))
