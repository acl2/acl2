; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "GL")
(include-book "gl-util")
(include-book "std/util/define" :dir :system)

;; This is turning into a dumping ground for logically-simple functions that
;; have a special meaning under symbolic execution.  Maybe we should rename
;; this file.

(define acl2::always-equal (x y)
  :parents (reference)
  :short "Alias for @(see equal) that has a special meaning in @(see
gl-bdd-mode)."

  :long "<p>Logically this is just @(see equal), but @(see GL) treats
@('always-equal') in a special way.</p>

<p>Suppose GL is asked to prove @('(equal spec impl)') when this does not
actually hold.  Sometimes, the symbolic objects for spec and impl can be
created, but the BDD representing their equality is too large to fit in memory.
This stops you from seeing any counterexamples, even though GL knows that the
two objects aren't equal.</p>

<p>To work around this, you may restate your theorem using @('always-equal')
instead of @('equal') as the final comparison.  @('always-equal') has a custom
symbolic counterpart that returns @('t') when its arguments are equivalent, or
else produces a symbolic object that captures just one counterexample and is
indeterminate in all other cases.</p>

<p>Note that there is not really any reason to use @('always-equal') if you are
using an AIG-based GL mode, such as @(see gl-satlink-mode).</p>"
  :enabled t
  ;; BOZO could inline this (but will probably need to adjust its special
  ;; handling if we do that)
  (equal x y))


(defsection gl-assert
  :parents (reference)
  :short "During GL symbolic execution, check that a condition holds, causing
an error if it does not."

  :long "<p>@('(gl-assert x)'), logically speaking, just returns @('(if x t
nil)').  In concrete execution, it causes an error if @('x') is false, and in
symbolic execution, it forces a check that @('x') is true and produces a
counterexample if not.</p>"

  (defun-inline gl-assert-fn (x msg gmsg)
    (declare (xargs :guard t)
             (ignore gmsg))
    (mbe :logic (and x t)
         :exec (if x
                   t
                 (er hard? 'gl-assert "~@0" msg))))

  (defmacro gl-assert (x &key
                         (msg 'nil msgp)
                         (gmsg 'nil gmsgp))
    (let* ((msg (if msgp
                    msg
                  (list 'quote (acl2::msg "GL-ASSERT failure: ~x0" x))))
           (gmsg (cond (gmsgp gmsg)
                       (msgp msg)
                       (t (list 'quote (acl2::msg "GL-ASSERT failure: ~x0" x))))))
      `(gl-assert-fn ,x ,msg ,gmsg))))


(define gl-concretize (x)
  :parents (reference)
  :short "During GL symbolic execution, try to reduce a symbolic object to a
concrete one."
  :long "<p>@('(gl-concretize x)'), logically speaking, just returns @('x').
However, during symbolic simulation (in AIG mode), it tries to reduce @('x') to
a concrete object by finding one object it could represent and trying to prove
that it is always equal to that object.</p>"
  :inline t
  :enabled t
  x)


(defsection gl-mbe
  :parents (reference)
  :short "Assert that a particular symbolic object is equivalent to a second
form, and use the second in place of the first."

  :long "<p>@(call gl-mbe) is defined to simply check whether its two arguments
@('spec') and @('impl') are equal, throwing an error if not, and return
@('spec').</p>

<p>However, when @('gl-mbe') is symbolically executed, the equality of the two
arguments is checked symbolically.  If it can be proved (e.g., via a BDD
equality or SAT check) that they are always equal, then @('impl') is returned
instead of @('spec'), otherwise an error is produced.</p>

<p>This is most useful when symbolically executing in AIG mode.  For example,
suppose that through a series of shifting operations, the symbolic
representation of some numeric operand X is expanded to thousands of bits.
However, the user knows that only the bottom 25 bits may be non-zero.  Then the
following form may speed up the rest of the computation involving X by cutting
off all the upper bits, which are known to be zero:</p>

@({
 (let ((x-chop (gl-mbe x (logand (1- (ash 1 25)) x))))
    ...)
})

<p>When GL symbolically executes this, it tries to prove that @('x') and the
@(see logand) expression are equivalent, that is, their symbolic
representations evaluate to the same concrete values under all environments.
If this can be proved, @('x-chop') is bound to the @(see logand) result, which
cuts off the upper bits of @('x'), which may improve symbolic execution
performance.  However, logically @('gl-mbe') just binds @('x-chop') to @('x'),
so this @('logand') term does not complicate reasoning about the
specification.</p>

<p>See also @(see gl-mbe-fast).</p>"

  (defun gl-mbe-fn (spec impl spec-form impl-form)
    (declare (xargs :guard t))
    (mbe :logic spec
         :exec (prog2$
                (or (equal spec impl)
                    (er hard? 'gl-mbe
                               "GL-MBE failure: ~x0 and ~x1 unequal.~% ~
                                Values: ~x2 versus ~x3."
                        spec-form impl-form spec impl))
                spec)))

  (defthm gl-mbe-gl-def
    (equal (gl-mbe-fn spec impl spec-form impl-form)
           (if (gl-assert (acl2::always-equal spec impl)
                          :msg (msg "GL-MBE failure: ~x0 and ~x1 unequal." spec-form impl-form))
               impl
             spec))
    :rule-classes ((:definition :install-body nil)))

  (set-preferred-def gl-mbe-fn gl-mbe-gl-def)

  (defmacro gl-mbe (spec impl)
    `(gl-mbe-fn ,spec ,impl ',spec ',impl)))


(defsection gl-mbe-fast
  :parents (gl-mbe)
  :short "Like @(see gl-mbe), but faster and without error checking during
execution."
  :long "<p>See @(see gl-mbe) for background.  @('(gl-mbe-fast spec exec)') is
logically identical to @('gl-mbe') and should have exactly the same effect
during symbolic execution.  However, @('gl-mbe-fast') may run more quickly
during concrete execution, at the cost of some error checking.</p>

<p>In particular, for ordinary, concrete execution, a @('(gl-mbe spec impl)')
form requires both the @('spec') and @('impl') forms to be evaluated and
checked for equality.  In contrast, @('gl-mbe-fast') is essentially a macro
that expands to:</p>

@({
     (mbe :logic (gl-mbe spec exec)
          :exec spec)
})

<p>The guard proof you will incur should be trivial because @('gl-mbe') always
just logically returns @('spec').</p>

<p>Aside from performance, this <b>behaves differently</b> than @(see gl-mbe)
in the degenerate case where your @('spec') and @('exec') forms produce
different results.  For example:</p>

@({
     (defun test1 (x y) (declare (xargs :guard t)) (gl-mbe x y))
     (defun test2 (x y) (declare (xargs :guard t)) (gl-mbe-fast x y))

     (test1 3 7)   --> causes a hard error
     (test2 3 7)   --> no error, returns 3
})"

  (defmacro gl-mbe-fast (spec impl)
    `(let ((spec ,spec))
       (mbe :logic (gl-mbe spec ,impl)
            :exec spec))))


;; BOZO document these

(defun gl-force-check-fn (x strong direction)
  (declare (xargs :guard t)
           (ignore strong direction))
  x)

(defmacro gl-force-check (x &key strong (direction ':both))
  `(gl-force-check-fn ,x ,strong ,direction))

(defmacro gl-force-check-strong (x)
  `(gl-force-check-fn ,x t :both))

(defxdoc gl-force-check
  :parents (reference)
  :short "When found in an @('if') test, forces GL to check satisfiability of the test."
  :long "<p>When using GL's AIG-based modes, it is sometimes important to force
GL to check whether an IF test is constant-true or constant-false.  For
example, if the @('if') guards a recursive call, then symbolic
interpretation of the function may diverge if the test isn't checked.</p>

<p>Usage:</p>
@({
 (gl-force-check test :strong nil :dir :both)
 })

<p>Here @(':strong') governs whether the path condition is considered; by
default it is not, because it is potentially much more expensive to do the
check when considering the path condition.  @(':dir') may be @('t'), @('nil'),
or @(':both') (the default).  If @('t'), then we only try to show that
@('test') is constant-true; if @('nil'), we only try to show it constant-false;
if @(':both'), then we try both directions.</p> ")


(defmacro gl-force-true (x &key strong)
  `(gl-force-check-fn ,x ,strong t))

(defmacro gl-force-true-strong (x)
  `(gl-force-check-fn ,x t t))

(defmacro gl-force-false (x &key strong)
  `(gl-force-check-fn ,x ,strong nil))

(defmacro gl-force-false-strong (x)
  `(gl-force-check-fn ,x t nil))

(table gl-uninterpreted-functions 'gl-force-check-fn t)



(define gl-aside (form)
  :parents (reference)
  :short "A debugging facility that is typically used for printing messages
during GL symbolic execution."

  :long #{"""<p>In the logic and during ordinary execution, @(call gl-aside) is
just an ordinary function that ignores its argument and returns @('nil').
However, during GL symbolic execution it has a special meaning which is useful
for printing debugging messages and doing other kinds of low-level hacking.</p>

<p><b>Note:</b> @('gl-aside') is fairly flexible but it can be <b>tricky to
use</b> correctly.  You should probably read this documentation carefully and
also see the ``Tricks and Pitfalls'' section below!</p>


<h3>Basic Example</h3>

<p>Here is a typical usage of gl-aside:</p>

@({
    (defun spec1 (x y)
      (b* ((sum (+ x y))
           (?msg (gl-aside (cw "Note: X is ~x0 and Y is ~x1.~%" x y))))
        sum))
})

<p>During the normal execution of @('spec1'), this Note will (of course) be
printed: @('gl-aside') is just an ordinary function, so ACL2 will (eagerly)
evaluate the @('cw') call before even invoking @('gl-aside').</p>

<p>What happens during symbolic execution?  If we try to prove the following,
simple GL theorem, e.g.,:</p>

@({
    (def-gl-thm spec1-correct
      :hyp (and (unsigned-byte-p 3 x)
                (unsigned-byte-p 3 y))
      :concl (equal (spec1 x y)
                    (+ x y))
      :g-bindings
      (auto-bindings (:nat x 3) (:nat y 3)))
})

<p>then our Note will still be printed <b>even though X and Y are @(see
symbolic-objects)</b> when @('spec1') is being executed!  In particular, we
will see, in @(see gl-satlink-mode):</p>

@({
     Note: X is (:G-INTEGER 0 1 2 NIL) and Y is
     (:G-NUMBER 4 5 6 NIL).
})

<p>The numbers 0-6 here are AIG variables.  If we were instead in @(see
gl-bdd-mode), we would see large BDD variables (trees of T and NIL) here
instead of these numbers.</p>

<p>The technical explanation of how this works is: when GL's symbolic
interpreter encounters a call of @('(gl-aside form')), it executes @('form')
inside a @(see wormhole), with the variables bound to their symbolic
versions.</p>


<h3>Why do we even need this?</h3>

<p>Couldn't we just write our spec without @('gl-aside')?  If we just
wrote:</p>

@({
    (defun spec2 (x y)
      (b* ((sum (+ x y))
           (?msg (cw "Note: X is ~x0 and Y is ~x1.~%" x y)))
        sum))
})

<p>Then our Note would still get printed during normal execution.  It would
also get printed during <i>some</i> symbolic executions.  In particular, if
we know that X and Y are particular concrete values, then we will still see
our note.  For example, if we heavily constrain @('X') and @('Y') so to be
constants:</p>

@({
    (def-gl-thm spec2-correct-for-3-and-4
      :hyp (and (equal x 3)
                (equal y 4))
      :concl (equal (spec2 x y)
                    (+ x y))
      :g-bindings
      (auto-bindings (:nat x 3) (:nat y 3)))
})

<p>then we will indeed see our Note printed:</p>

@({
     Note: X is 3 and Y is 4.
})

<p>here, the @(see cw) form is being applied to all-constant arguments, so GL
can simply evaluate it, causing the message to be printed.  However, if we
instead submit something more like our original theorem:</p>

@({
    (def-gl-thm spec2-correct
      :hyp (and (unsigned-byte-p 3 x)
                (unsigned-byte-p 3 y))
      :concl (equal (spec2 x y)
                    (+ x y))
      :g-bindings
      (auto-bindings (:nat x 3) (:nat y 3)))
})

<p>then the Note is not printed.  Why not?  In this case, when GL's interpreter
reaches the @('cw') form, @('x') and @('y') are still symbolic objects, so it
cannot simply concretely execute @('cw').  Instead, GL symbolically executes
the logical definition of @('cw')&mdash;really @(see fmt-to-comment-window).
But in the logic, this function (of course) does not print anything, but
instead just returns @('nil').  At any rate, GL ends up binding @('msg') to
@('nil') and nothing gets printed.</p>


<h3>Tricks and Pitfalls</h3>

<h5>Pitfall: @(see progn$) and its ilk</h5>

<p>You probably <b>never</b> want to use @(see prog2$) or @(see progn$) to
invoke a @('gl-aside').  For instance, you do NOT want to do this:</p>

@({
      (progn$ (gl-aside ...)      ;; WRONG
              sum)
})

<p>Why not?  During symbolic execution, GL just completely skips directly to
the last form in the @('progn$'), so it will never even see your
@('gl-aside')!</p>

<p>For similar reasons, you should also generally not use @(see b*) binders
like @('-'), @('&'), and @('?!'), or the implicit @('progn$') forms that @('b*')
permits.  For example:</p>

@({
      (b* ((ans   (f x y ...))
           (?msg  (gl-aside ...))  ;; GOOD, bind to an ignored variable
           (?!msg (gl-aside ...))  ;; BAD, won't get evaluated
           (-     (gl-aside ...))  ;; BAD, won't get evaluated

           ((when condition)
            ;; implicit b* progn$:
            (gl-aside ...)         ;; BAD, won't get evaluated
            ans))

         ;; implicit b* progn$:
         (gl-aside ...)            ;; BAD, won't get evaluated
         ans)
})

<h5>Trick: print only during symbolic execution</h5>

<p>The above @('spec1') function will print its Note during <b>both</b> regular
execution and symbolic execution.  It is also possible to use @(see mbe) to get
a message that only prints during symbolic execution.</p>

@({
    (defmacro gl-aside-symbolic (form)
      `(mbe :logic (gl-aside ,form)
            :exec nil))

    (defun spec3 (x y)
      (declare (xargs :guard (and (natp x) (natp y))))
      (b* ((sum (+ x y))
           (?msg (gl-aside-symbolic (cw "Note: X is ~x0 and Y is ~x1.~%" x y))))
        sum))

    (spec3 3 4)      ;; No Note is printed
    7

    (def-gl-thm spec3-correct ...) ;; Note is printed
})

<p>Of course, this only works for guard-verified functions.</p>"""}

  :enabled t
  (declare (ignore form))
  nil)

(defsection gl-aside-symbolic
  :parents (gl-aside)
  :short "Alternative to @(see gl-aside) that is only evaluated during GL
symbolic execution."
  :long "@(def gl-aside-symbolic)"

  (defmacro gl-aside-symbolic (form)
    `(mbe :logic (gl-aside ,form)
          :exec nil)))



(defun gl-ignore (x)
  (declare (xargs :guard t)
           (ignore x))
  nil)

(defund gl-error (x)
  (declare (xargs :guard t)
           (ignore x))
  (prog2$ (er hard? 'gl-error "GL-ERROR call encountered; quitting~%")
          nil))

(defthm gl-error-is-nil
  (equal (gl-error x) nil)
  :hints(("Goal" :in-theory (enable gl-error))))



(defun gl-hide (x)
  (declare (xargs :guard t))
  x)
