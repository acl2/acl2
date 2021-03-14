; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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

(in-package "SV")
(include-book "eval")


(defines svex-xeval
  :parents (evaluation)
  :short "Cheaply detect always-constant bits in an @(see svex) by
approximately evaluating it under the empty (i.e., all X) environment."

  :long "<p>This is a lightweight way to tell that certain bits of an @(see
svex) expression are actually particular constants, no matter how you bind its
variables.  It returns an @(see 4vec) which tells us that certain bits of
@('expr') are ``obviously'' constant, and that other bits are not known to be
constant.  In particular:</p>

<ul>

<li>Xes indicate that this bit of @('expr') is not obviously constant,</li>

<li>0/1/Z bits indicate that this bit of @('expr') is obviously always
0/1/Z.</li>

</ul>


<h3>Example</h3>

<p>Consider the following expression:</p>

@({
     (bitand (bitor a b) (bitand c #b1000))
})

<p>What values can this expression return?  You can see that, regardless of the
values of @('a'), @('b'), and @('c'), the resulting @(see 4vec) will always
have 0 on its lower 3 bits.  It will also always have 0s on bits 5 and above.
But bit 4 will depend on the values of @('a'), @('b'), and @('c').</p>

<p>When we use @('svex-xeval'), we get:</p>

@({
     (svex-xeval '(bitand (bitor a b) (bitand c #b1000))) == (8 . 0)
})

<p>Here is the interpretation of the resulting @(see 4vec), @('(8 . 0)'):</p>

@({
     bits of upper (8) are: 0...01000
     bits of lower (0) are: 0...00000
     ---------------------------------
     01ZX interpretation:   0...0X000
})

<p>So @('svex-xeval') is telling us that:</p>

<ul>
<li>Bit 4 is not known to be always constant.</li>
<li>All the other bits are known to be always constant 0.</li>
</ul>


<h3>Implementation</h3>

<p>@('(svex-xeval expr)') is almost identical to @('(svex-eval expr nil)').
Recall that, when @(see svex-eval) encounters a variable that isn't bound in
the environment, it returns the all Xes vector.  So, when we evaluate @('expr')
in the @('nil') environment, it's as if we've bound all of its variables to all
Xes.</p>

<p>If all of our @(see expressions) were ``properly monotonic'' and truly
treated @('x') bits as unknowns, then the result of @('(svex-eval expr nil)')
would clearly be a conservative approximation of @('(svex-eval expr env)') for
any environment.</p>

<p>This almost works.  However, the case-equality operator @('===') is
problematic, because it has a non-monotonic semantics that does not treat X
bits as unknown.  As a result, evaluation in the @('nil') environment doesn't
really work for what we're trying to do here.  For example:</p>

@({
     (svex-eval '(=== a b) nil)     -->  -1  (all bits true)
})

<p>But obviously this expression isn't always true, for instance:</p>

@({
    (let ((env '((a . 1) (b . 0))))
      (svex-eval '(=== a b) env))    -->  0  (all bits false)
})

<p>To correct for this, @('svex-xeval') simply interprets @('===') as @('==')
instead.  Since @('==') is an ordinary, properly monotonic function, and
since it conservatively approximates @('==='), this works out quite well
and we get, for instance:</p>

@({
     (svex-xeval '(=== a b))  --> all Xes
     (svex-xeval '(=== a a))  --> all Xes
     (svex-xeval '(=== 0 0))  --> all true
})"

  (define svex-xeval ((expr svex-p "Expression to evaluate."))
    :returns (val 4vec-p "Indication of always-constant bits (see below).")
    :measure (svex-count expr)
    :verify-guards nil
    (svex-case expr
      :quote expr.val
      :var (4vec-x)
      :call
      (let ((expr.fn (case expr.fn
                       (=== '==)
                       (==? 'safer-==?)
                       (bit?! 'bit?)
                       (?!    '?*)
                       (otherwise expr.fn))))
        (mbe :logic
             (svex-apply expr.fn (svexlist-xeval expr.args))
             :exec
             ;; Shortcuts for ?, bit?, bitand, bitor
             (case expr.fn
               ((? ?*)
                     (b* (((unless (eql (len expr.args) 3))
                           (svex-apply expr.fn (svexlist-xeval expr.args)))
                          (test (3vec-fix (svex-xeval (first expr.args))))
                          ((4vec test))
                          ((when (eql test.upper 0))
                           (svex-xeval (third expr.args)))
                          ((when (not (eql test.lower 0)))
                           (svex-xeval (second expr.args)))
                          (then (svex-xeval (second expr.args)))
                          (else (svex-xeval (third expr.args))))
                       (case expr.fn
                         (? (4vec-? test then else))
                         (?* (4vec-?* test then else)))))
               (bit?
                (b* (((unless (eql (len expr.args) 3))
                      (svex-apply expr.fn (svexlist-xeval expr.args)))
                     (test (svex-xeval (first expr.args)))
                     ((when (eql test 0))
                      (svex-xeval (third expr.args)))
                     ((when (eql test -1))
                      (svex-xeval (second expr.args))))
                  (4vec-bit? test
                             (svex-xeval (second expr.args))
                             (svex-xeval (third expr.args)))))
               (bitand
                (b* (((unless (eql (len expr.args) 2))
                      (svex-apply expr.fn (svexlist-xeval expr.args)))
                     (test (svex-xeval (first expr.args)))
                     ((when (eql test 0)) 0))
                  (4vec-bitand test
                               (svex-xeval (second expr.args)))))
               (bitor
                (b* (((unless (eql (len expr.args) 2))
                      (svex-apply expr.fn (svexlist-xeval expr.args)))
                     (test (svex-xeval (first expr.args)))
                     ((when (eql test -1)) -1))
                  (4vec-bitor test
                              (svex-xeval (second expr.args)))))
               (otherwise
                (svex-apply expr.fn (svexlist-xeval expr.args))))))))

  (define svexlist-xeval ((x svexlist-p))
    :measure (svexlist-count x)
    :returns (val 4veclist-p)
    :short "Maps @(see svex-xeval) over an @(see svex) list."
    (if (atom x)
        nil
      (cons (svex-xeval (car x))
            (svexlist-xeval (cdr x)))))
  ///


  (local (defthm consp-of-svexlist-xeval
           (equal (consp (svexlist-xeval x))
                  (consp x))
           :hints (("goal" :expand ((svexlist-xeval x))))))

  (local (defthm upper-lower-of-3vec-fix
           (implies (and (3vec-p x)
                         (not (equal (4vec->lower x) 0)))
                    (not (equal (4vec->upper x) 0)))
           :hints(("Goal" :in-theory (enable 3vec-p)))))

  (local (defthm 4vec-?-cases
           (and (implies (equal (4vec->upper (3vec-fix test)) 0)
                         (equal (4vec-? test then else)
                                (4vec-fix else)))
                (implies (not (equal (4vec->lower (3vec-fix test)) 0))
                         (equal (4vec-? test then else)
                                (4vec-fix then))))
           :hints(("Goal" :in-theory (enable 4vec-? 3vec-?)))))

  (local (defthm 4vec-?*-cases
           (and (implies (equal (4vec->upper (3vec-fix test)) 0)
                         (equal (4vec-?* test then else)
                                (4vec-fix else)))
                (implies (not (equal (4vec->lower (3vec-fix test)) 0))
                         (equal (4vec-?* test then else)
                                (4vec-fix then))))
           :hints(("Goal" :in-theory (enable 4vec-?* 3vec-?*)))))

  (local (defthm 4vec-bit?-cases
           (and (implies (equal test 0)
                         (equal (4vec-bit? test then else)
                                (4vec-fix else)))
                (implies (equal test -1)
                         (equal (4vec-bit? test then else)
                                (4vec-fix then))))
           :hints(("Goal" :in-theory (enable 4vec-bit? 3vec-bit?)))))

  (local (defthm 4vec-bitand-case
           (implies (equal test 0)
                    (equal (4vec-bitand test x)
                           0))
           :hints(("Goal" :in-theory (enable 4vec-bitand 3vec-bitand)))))

  (local (defthm 4vec-bitor-case
           (implies (equal test -1)
                    (equal (4vec-bitor test x)
                           -1))
           :hints(("Goal" :in-theory (enable 4vec-bitor 3vec-bitor)))))

  (verify-guards svex-xeval
    :hints((and stable-under-simplificationp
                '(:in-theory (e/d (svex-apply len 4veclist-nth-safe nth 4vec-?!)
                                  (svex-xeval))
                  :expand ((svexlist-xeval (svex-call->args expr))
                           (svexlist-xeval (cdr (svex-call->args expr)))
                           (svexlist-xeval (cddr (svex-call->args expr))))))))

  (memoize 'svex-xeval :condition '(eq (svex-kind expr) :call))

  (deffixequiv-mutual svex-xeval
    :hints (("goal" :expand ((svexlist-fix x)))))

  (defthm svexlist-xeval-nil
    (equal (svexlist-xeval nil) nil))

  (defthm car-of-svexlist-xeval
    (4vec-equiv (car (svexlist-xeval x))
                (svex-xeval (car x))))

  (defthm cdr-of-svexlist-xeval
    (4veclist-equiv (cdr (svexlist-xeval x))
                    (svexlist-xeval (cdr x))))

  (defthm len-of-svexlist-xeval
    (equal (len (svexlist-xeval x))
           (len x)))

  (defthm svexlist-xeval-of-append
    (equal (svexlist-xeval (append a b))
           (append (svexlist-xeval a)
                   (svexlist-xeval b)))
    :hints(("Goal" :in-theory (enable append)))))
