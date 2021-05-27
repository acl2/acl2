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
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "tools/templates" :dir :system)

(local (defthm svex-count-gt-1
         (implies (svex-case x :call)
                  (< 1 (svex-count x)))
         :hints(("Goal" :expand ((svex-count x))))
         :rule-classes :linear))

(defconst *svex-fn/args-mono-eval-body-template*
  '(case (fnsym-fix fn)
     (=== (b* (((unless (eql (len args) 2))
                (<apply> '== (svexlist-<ev> args <env>)))
               ((list first second) args)
               ((when (svex-case second :quote))
                (<fnprefix>-===* (svex-<ev> first <env>) (<quote-val> second)))
               ((when (svex-case first :quote))
                (<fnprefix>-===* (svex-<ev> second <env>) (<quote-val> first))))
            (<fnprefix>-== (svex-<ev> first <env>) (svex-<ev> second <env>))))
     (===* (b* (((unless (eql (len args) 2))
                 (<apply> '== (svexlist-<ev> args <env>)))
                ((list first second) args)
                ((when (svex-case second :quote))
                 (<fnprefix>-===* (svex-<ev> first <env>) (<quote-val> second))))
             (<fnprefix>-== (svex-<ev> first <env>) (svex-<ev> second <env>))))
     (==? (b* (((unless (and (eql (len args) 2)
                             (svex-case (second args) :quote)))
                (<apply> 'safer-==? (svexlist-<ev> args <env>))))
            (<fnprefix>-wildeq (svex-<ev> (first args) <env>)
                         (svex-<ev> (second args) <env>))))
     ;; BOZO add lazy case
     (?! (b* (((unless (and (eql (len args) 3)
                            (svex-case (first args) :quote)))
               (<apply> '?* (svexlist-<ev> args <env>))))
           (<fnprefix>-?! (<quote-val> (first args))
                    (svex-<ev> (second args) <env>)
                    (svex-<ev> (third args) <env>))))
     ;; BOZO add lazy case
     (bit?! (b* (((unless (and (eql (len args) 3)
                               (svex-case (first args) :quote)))
                  (<apply> 'bit? (svexlist-<ev> args <env>))))
              (<fnprefix>-bit?! (<quote-val> (first args))
                          (svex-<ev> (second args) <env>)
                          (svex-<ev> (third args) <env>))))
     ((? ?*)
      (<mbe-or-exec> :logic (<apply> fn (svexlist-<ev> args <env>))
           :exec (b* (((unless (eql (len args) 3))
                       (<apply> fn (svexlist-<ev> args <env>)))
                      (test (<3vec-fix> (svex-<ev> (first args) <env>)))
                      ((<4vec> test))
                      ((when (<vec-eql> test.upper 0))
                       (svex-<ev> (third args) <env>))
                      ((when (not (<vec-eql> test.lower 0)))
                       (svex-<ev> (second args) <env>))
                      (then (svex-<ev> (second args) <env>))
                      (else (svex-<ev> (third args) <env>)))
                   (case (fnsym-fix fn)
                     (? (<fnprefix>-? test then else))
                     (?* (<fnprefix>-?* test then else))))))
     (bit?
      (<mbe-or-exec> :logic (<apply> fn (svexlist-<ev> args <env>))
           :exec (b* (((unless (eql (len args) 3))
                       (<apply> fn (svexlist-<ev> args <env>)))
                      (test (svex-<ev> (first args) <env>))
                      ((when (<4vec-eql> test 0))
                       (svex-<ev> (third args) <env>))
                      ((when (<4vec-eql> test -1))
                       (svex-<ev> (second args) <env>)))
                   (<fnprefix>-bit? test
                              (svex-<ev> (second args) <env>)
                              (svex-<ev> (third args) <env>)))))
     (bitand
      (<mbe-or-exec> :logic (<apply> fn (svexlist-<ev> args <env>))
           :exec (b* (((unless (eql (len args) 2))
                       (<apply> fn (svexlist-<ev> args <env>)))
                      (test (svex-<ev> (first args) <env>))
                      ((when (<4vec-eql> test 0)) 0))
                   (<fnprefix>-bitand test
                                (svex-<ev> (second args) <env>)))))
     (bitor
      (<mbe-or-exec> :logic (<apply> fn (svexlist-<ev> args <env>))
           :exec (b* (((unless (eql (len args) 2))
                       (<apply> fn (svexlist-<ev> args <env>)))
                      (test (svex-<ev> (first args) <env>))
                      ((when (<4vec-eql> test -1)) -1))
                   (<fnprefix>-bitor test
                               (svex-<ev> (second args) <env>)))))
     (otherwise
      (<apply> fn (svexlist-<ev> args <env>)))))

(defconst *svex-mono-eval-template*
  '(defines svex-<ev>
     :parents (evaluation)
     :short <short>
     :long <long>
     :flag-local nil
     (define svex-<ev> ((x svex-p "Expression to evaluate.")
                        <env-formal>)
       :returns (val <rettype>)
       :measure (two-nats-measure (svex-count x) 1)
       :verify-guards nil
       (svex-case x
         :quote x.val
         :var <env-lookup>
         :call (svex-call-<ev> x <env>)))

     (define svex-call-<ev> ((x svex-p)
                             <env-formal>)
       :guard (svex-case x :call)
       :measure (two-nats-measure (svex-count x) 0)
       :returns (val <rettype>)
       (b* (((unless (mbt (svex-case x :call))) (4vec-x))
            ((svex-call x)))
         (mbe :logic (svex-fn/args-<ev> x.fn x.args <env>)
              :exec (let* ((fn x.fn)
                           (args x.args))
                      <body>))))

     (define svex-fn/args-<ev> ((fn fnsym-p)
                                (args svexlist-p)
                                <env-formal>)
       :measure (two-nats-measure (svexlist-count args) 1)
       :returns (val <rettype>)
       <body>)

     (define svexlist-<ev> ((x svexlist-p)
                            <env-formal>)
       :measure (two-nats-measure (svexlist-count x) 0)
       :returns (val 4veclist-p)
       :short "Maps @(see svex-<ev>) over an @(see svex) list."
       (if (atom x)
           nil
         (cons (svex-<ev> (car x) <env>)
               (svexlist-<ev> (cdr x) <env>))))
     ///
     (local (in-theory (disable svex-<ev>
                                svex-call-<ev>
                                svexlist-<ev>)))

     (local (defthm consp-of-svexlist-<ev>
              (equal (consp (svexlist-<ev> x <env>))
                     (consp x))
              :hints (("goal" :expand ((svexlist-<ev> x <env>))))))

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

     (defthmd svex-<ev>-of-quote
       (implies (svex-case x :quote)
                (equal (svex-<ev> x <env>) (<quote-val> x)))
       :hints(("Goal" :in-theory (enable svex-<ev>))))

     (verify-guards svex-<ev>
       :hints((and stable-under-simplificationp
                   '(:in-theory (e/d (<apply> len 4veclist-nth-safe nth 4vec-?!
                                                 svex-<ev>-of-quote)
                                     (svex-<ev>))
                     :expand ((svexlist-<ev> (svex-call->args x) <env>)
                              (svexlist-<ev> (cdr (svex-call->args x)) <env>)
                              (svexlist-<ev> (cddr (svex-call->args x)) <env>)
                              (svexlist-<ev> args <env>)
                              (svexlist-<ev> (cdr args) <env>)
                              (svexlist-<ev> (cddr args) <env>))))))

     (memoize 'svex-call-<ev>)

     (deffixequiv-mutual svex-<ev>)
     ;; :hints (("goal" :expand ((svexlist-xev
     ;;                          (svex-call-<ev> x)
     ;;                          (svex-call-<ev> (svex-fix x))))))

     (defthm svexlist-<ev>-nil
       (equal (svexlist-<ev> nil <env>) nil)
       :hints(("Goal" :in-theory (enable svexlist-<ev>))))

     (defthm car-of-svexlist-<ev>
       (4vec-equiv (car (svexlist-<ev> x <env>))
                   (svex-<ev> (car x) <env>))
       :hints(("Goal" :expand ((svexlist-<ev> x <env>))
               :in-theory (enable svex-<ev>-of-quote))))

     (defthm cdr-of-svexlist-<ev>
       (4veclist-equiv (cdr (svexlist-<ev> x <env>))
                       (svexlist-<ev> (cdr x) <env>))
       :hints(("Goal" :in-theory (enable svexlist-<ev>))))

     (defthm len-of-svexlist-<ev>
       (equal (len (svexlist-<ev> x <env>))
              (len x))
       :hints(("Goal" :in-theory (enable svexlist-<ev>))))

     (defthm svexlist-<ev>-of-append
       (equal (svexlist-<ev> (append a b) <env>)
              (append (svexlist-<ev> a <env>)
                      (svexlist-<ev> b <env>)))
       :hints(("Goal" :in-theory (enable append svexlist-<ev>))))))


#||
;; The following make-event defines these functions:
(defines
  (define svex-mono-eval ...)
  (define svex-call-mono-eval ...)
  (define svex-fn/args-mono-eval ...)
  (define svexlist-mono-eval ...)
  ...)
||#
(make-event
 (b* ((body (acl2::template-subst *svex-fn/args-mono-eval-body-template*
                                  :str-alist '(("<EV>" "MONO-EVAL" . svex-package)
                                               ("<FNPREFIX>" "4VEC" . svex-package))
                                  :string-str-alist '(("<EV>" "MONO-EVAL" . svex-package)
                                                      ("<ev>" "mono-eval" . svex-package)
                                                      ("<FNPREFIX>" "4VEC" . svex-package))
                                  :atom-alist '((<env> . env)
                                                (<apply> . svex-apply)
                                                (<quote-val> . svex-quote->val)
                                                (<vec-eql> . eql)
                                                (<3vec-fix> . 3vec-fix)
                                                (<4vec> . 4vec)
                                                (<4vec-eql> . equal)
                                                (<mbe-or-exec> . mbe))))
      (event (acl2::template-subst *svex-mono-eval-template*
                                   :str-alist '(("<EV>" "MONO-EVAL" . svex-package)
                                                ("<FNPREFIX>" "4VEC" . svex-package))
                                  :string-str-alist '(("<EV>" "MONO-EVAL" . svex-package)
                                                      ("<ev>" "mono-eval" . svex-package)
                                                      ("<FNPREFIX>" "4VEC" . svex-package))
                                   :atom-alist `((<body> . ,body)
                                                 (<env> . env)
                                                 (<short> . "Evaluate an X-monotonic approximation of an svex")
                                                 (<long> . nil)
                                                 (<rettype> . 4vec-p)
                                                 (<apply> . svex-apply)
                                                 (<quote-val> . svex-quote->val)
                                                 (<env-formal> . (env svex-env-p))
                                                 (<env-lookup> . (svex-env-lookup x.name env))))))
   event))

#||
;; The following make-event defines these functions:
(defines
  (define svex-xeval ...)
  (define svex-call-xeval ...)
  (define svex-fn/args-xeval ...)
  (define svexlist-xeval ...)
  ...)
||#
(make-event
 (b* ((short "Cheaply detect always-constant bits in an @(see svex) by
approximately evaluating it under the empty (i.e., all X) environment.")
      (long "<p>This is a lightweight way to tell that certain bits of an @(see
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
})")
      (body (acl2::template-subst *svex-fn/args-mono-eval-body-template*
                                  :str-alist '(("<EV>" "XEVAL" . svex-package)
                                               ("<FNPREFIX>" "4VEC" . svex-package))
                                  :string-str-alist '(("<EV>" "XEVAL" . svex-package)
                                                      ("<ev>" "xeval" . svex-package)
                                                      ("<FNPREFIX>" "4VEC" . svex-package))
                                  :splice-alist '((<env> . nil))
                                  :atom-alist '((<apply> . svex-apply)
                                                (<quote-val> . svex-quote->val)
                                                (<vec-eql> . eql)
                                                (<3vec-fix> . 3vec-fix)
                                                (<4vec> . 4vec)
                                                (<4vec-eql> . equal)
                                                (<mbe-or-exec> . mbe))))
      (event (acl2::template-subst *svex-mono-eval-template*
                                   :str-alist '(("<EV>" "XEVAL" . svex-package)
                                                ("<FNPREFIX>" "4VEC" . svex-package))
                                  :string-str-alist '(("<EV>" "XEVAL" . svex-package)
                                                      ("<ev>" "xeval" . svex-package)
                                                      ("<FNPREFIX>" "4VEC" . svex-package))
                                   :atom-alist `((<body> . ,body)
                                                 (<short> . ,short)
                                                 (<long> . ,long)
                                                 (<rettype> . 4vec-p)
                                                 (<apply> . svex-apply)
                                                 (<quote-val> . svex-quote->val)
                                                 (<env-lookup> . (4vec-x)))
                                   :splice-alist '((<env> . nil)
                                                   (<env-formal> . nil)))))
   event))


(std::defret-mutual svex-xeval-is-mono-eval
  :mutual-recursion svex-xeval
  (defretd svex-xeval-is-mono-eval
    (equal val
           (svex-mono-eval x nil))
    :hints ('(:expand (<call>
                       (svex-mono-eval x nil))))
    :fn svex-xeval)
  (defretd svex-call-xeval-is-mono-eval
    (equal val
           (svex-call-mono-eval x nil))
    :hints ('(:expand (<call>
                       (svex-call-mono-eval x nil))))
    :fn svex-call-xeval)
  (defretd svex-fn/args-xeval-is-mono-eval
    (equal val
           (svex-fn/args-mono-eval fn args nil))
    :hints ('(:expand ((:free (fn) <call>)
                       (:free (fn) (svex-fn/args-mono-eval fn args nil)))))
    :fn svex-fn/args-xeval)
  (defretd svexlist-xeval-is-mono-eval
    (equal val
           (svexlist-mono-eval x nil))
    :hints ('(:expand (<call>
                       (svexlist-mono-eval x nil))))
    :fn svexlist-xeval))
