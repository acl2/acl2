 ; S-Expressions for 4-Valued Logic
; Copyright (C) 2010-2012 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

; sexpr-eval.lisp
;   - defines our s-expression language for 4-valued logic expressions
;   - proves that sexpr evaluation is monotonic
;   - defines extended sexpr evaluation operations
;   - defines sexpr composition and restriction operations

(in-package "ACL2")
(include-book "4v-logic")
(include-book "centaur/misc/fast-alists" :dir :system)
(include-book "centaur/misc/hons-extra" :dir :system)
(local (include-book "std/lists/nth" :dir :system))

(defsection 4v-sexpr-ind
  :parents (4v-sexprs)
  :short "Basic structural induction scheme for s-expressions."

  (mutual-recursion
   (defun 4v-sexpr-ind (x)
     (declare (xargs :guard t))
     (if (atom x)
         x
       (cons (car x) (4v-sexpr-ind-list (cdr x)))))
   (defun 4v-sexpr-ind-list (x)
     (declare (xargs :guard t))
     (if (atom x)
         nil
       (cons (4v-sexpr-ind (car x))
             (4v-sexpr-ind-list (cdr x))))))

  (flag::make-flag 4v-sexpr-flag 4v-sexpr-ind
                   :flag-mapping ((4v-sexpr-ind sexpr)
                                  (4v-sexpr-ind-list sexpr-list))))



; These are just (X), (Z), (T), and (F), i.e., our constant sexpr functions.

(defconst *4vx-sexpr* (hist (4vx)))
(defconst *4vz-sexpr* (hist (4vz)))
(defconst *4vt-sexpr* (hist (4vt)))
(defconst *4vf-sexpr* (hist (4vf)))

(defmacro 4vt-sexpr-p (a) `(eq (car ,a) (4vt)))
(defmacro 4vf-sexpr-p (a) `(eq (car ,a) (4vf)))
(defmacro 4vx-sexpr-p (a) `(eq (car ,a) (4vx)))
(defmacro 4vz-sexpr-p (a) `(eq (car ,a) (4vz)))


(defmacro 4v-first (x)
  `(mbe :logic (nth 0 ,x)
        :exec (first ,x)))

(defmacro 4v-second (x)
  `(mbe :logic (nth 1 ,x)
        :exec (second ,x)))

(defmacro 4v-third (x)
  `(mbe :logic (nth 2 ,x)
        :exec (third ,x)))

(local (defthmd nth-open-quotep
         (implies (syntaxp (quotep n))
                  (equal (nth n x)
                         (if (zp n)
                             (car x)
                           (nth (1- n) (cdr x)))))))


(defsection 4v-sexpr-eval
  :parents (4v-sexprs)
  :short "Evaluate a sexpr under an environment."

  :long "<p>@(call 4v-sexpr-eval) evaluates the <see topic='@(url
4v-sexprs)'>4v-sexpr</see> @('x') under the environment @('env'), producing a
@(see 4vp).</p>

<p>This environment is an alist binding the variables of @('x') to four-valued
logic constants.  It must be a fast alist.</p>

<ul>
 <li>Unbound variables evaluate to X.</li>
 <li>Variables bound to non-@(see 4vp) values evaluate to X.</li>
 <li>Ill-formed sexprs evaluate to X.</li>
</ul>

<p>This is an especially simple evaluator, and together with the @(see
4v-operations) it invokes it defines the semantics of our s-expressions.
Moreover, the main theorems about other 4v-sexpr operations are usually stated
in terms of the evaluations of their results.</p>

<p>We @(see memoize) evaluation to avoid having to recompute shared
subexpressions.  Note that we do not memoize with @(':forget t') because you
frequently want to evaluate several related expressions under the same
environment, as in @(see 4v-sexpr-eval-alist).  As a consequence, you'll
generally need to manage its memo table yourself.</p>

<p>This evaluator performs well enough to be practically useful for single-bit
evaluations under a fixed environment.  However, it is almost certainly too
slow to use this function when doing any significant amount of evaluation,
e.g., vector simulations of the same sexpr under random environments.  For that
sort of thing, it should be possible to develop a much faster simulator, e.g.,
by compiling the sexpr into a bytecode program and using a @(see stobj) array
of fixnums to hold the values, or similar.</p>"

  (defxdoc 4v-sexpr-eval-list
    :parents (4v-sexpr-eval)
    :short "Evaluate a list of sexprs under an environment."

    :long "<p>See @(see 4v-sexpr-eval); this is just its mutually recursive
counterpart.</p>")

  (defund 4v-sexpr-apply (fn args)
    (declare (xargs :guard (true-listp args)))
    (b* (((when (or (eq fn (4vt))
                    (eq fn (4vf))
                    (eq fn (4vx))
                    (eq fn (4vz))))
          fn)
         (arg1 (4v-first args))
         (arg2 (4v-second args))
         (arg3 (4v-third args)))
      (case fn
        (not       (4v-not      arg1))
        (and       (4v-and      arg1 arg2))
        (xor       (4v-xor      arg1 arg2))
        (iff       (4v-iff      arg1 arg2))
        (or        (4v-or       arg1 arg2))
        (ite*      (4v-ite*     arg1 arg2 arg3))
        (zif       (4v-zif      arg1 arg2 arg3))
        (buf       (4v-unfloat  arg1))
        (xdet      (4v-xdet     arg1))
        (res       (4v-res      arg1 arg2))
        (tristate  (4v-tristate arg1 arg2))
        (ite       (4v-ite      arg1 arg2 arg3))
        (pullup    (4v-pullup   arg1))
        (id        (4v-fix      arg1))
        ;; (wand     (4v-wand  arg1 arg2))
        ;; (wor      (4v-wor   arg1 arg2))
        (otherwise (4vx)))))

  (local (in-theory (enable 4v-sexpr-apply)))
; [Jared] I was tempted to make a 4v-sexpr-eval1 function in the style of
; 4v-sexpr-eval-alist1, but this seems troublesome because it would mean
; changing all of our clear-memoize-table call functions.  I'm just going to
; leave this as requiring a fast alist, and similarly for 4v-sexpr-restrict,
; 4v-sexpr-compose, etc.

  (mutual-recursion
   (defun 4v-sexpr-eval (x env)
     (declare (xargs :guard t :verify-guards nil))
     (b* (((when (atom x))
           ;; NIL is regarded as X, which is important in 4v-sexpr-compose and
           ;; perhaps other places.  Any other atom is a variable and we look
           ;; up its value in env.
           (if x
               (4v-lookup x env)
             (4vx)))
          (fn   (car x))
          ((when (or (eq fn (4vt))
                     (eq fn (4vf))
                     (eq fn (4vx))
                     (eq fn (4vz))))
           fn)
          (args (4v-sexpr-eval-list (cdr x) env))
          (arg1 (4v-first args))
          (arg2 (4v-second args))
          (arg3 (4v-third args)))
       (case fn
          (not       (4v-not      arg1))
          (and       (4v-and      arg1 arg2))
          (xor       (4v-xor      arg1 arg2))
          (iff       (4v-iff      arg1 arg2))
          (or        (4v-or       arg1 arg2))
          (ite*      (4v-ite*     arg1 arg2 arg3))
          (zif       (4v-zif      arg1 arg2 arg3))
          (buf       (4v-unfloat  arg1))
          (xdet      (4v-xdet     arg1))
          (res       (4v-res      arg1 arg2))
          (tristate  (4v-tristate arg1 arg2))
          (ite       (4v-ite      arg1 arg2 arg3))
          (pullup    (4v-pullup   arg1))
          (id        (4v-fix      arg1))
          ;; (wand     (4v-wand  arg1 arg2))
          ;; (wor      (4v-wor   arg1 arg2))
          (otherwise (4vx)))))

   (defun 4v-sexpr-eval-list (x env)
     (declare (xargs :guard t))
     (if (atom x)
         nil
       (cons (4v-sexpr-eval (car x) env)
             (4v-sexpr-eval-list (cdr x) env)))))

  (defthmd 4v-sexpr-eval-redef
    (equal (4v-sexpr-eval x env)
           (b* (((when (atom x))
                 (if x (4v-lookup x env) (4vx)))
                (args (4v-sexpr-eval-list (cdr x) env)))
             (4v-sexpr-apply (car x) args)))
    :rule-classes ((:definition
                    :clique (4v-sexpr-eval 4v-sexpr-eval-list)
                    :controller-alist
                    ((4v-sexpr-eval t nil)
                     (4v-sexpr-eval-list t nil)))))

  (verify-guards 4v-sexpr-eval
    :hints (("goal" :in-theory (enable nth-open-quotep))))

  (memoize '4v-sexpr-eval
           :condition '(and (consp x) (consp (cdr x))))

  (defthm 4v-sexpr-eval-possibilities
    (implies (and (not (equal (4v-sexpr-eval x env) (4vt)))
                  (not (equal (4v-sexpr-eval x env) (4vf)))
                  (not (equal (4v-sexpr-eval x env) (4vz))))
             (equal (equal (4v-sexpr-eval x env) (4vx)) t))
    :hints (("goal" :expand ((4v-sexpr-eval x env)))))

  (defthm 4v-sexpr-eval-nil
    (equal (4v-sexpr-eval nil env)
           (4vx)))

  (defthm 4v-sexpr-eval-4vx-sexpr
    (equal (4v-sexpr-eval *4vx-sexpr* env)
           (4vx)))

  (defthm 4v-fix-4v-sexpr-eval
    (equal (4v-fix (4v-sexpr-eval x env))
           (4v-sexpr-eval x env)))

  (defthm-4v-sexpr-flag
    (defthm 4v-sexpr-eval-monotonicp
      (implies (4v-alist-<= env env1)
               (4v-<= (4v-sexpr-eval x env)
                      (4v-sexpr-eval x env1)))
      :flag sexpr)
    (defthm 4v-sexpr-eval-list-monotonicp
      (implies (4v-alist-<= env env1)
               (4v-list-<= (4v-sexpr-eval-list x env)
                           (4v-sexpr-eval-list x env1)))
      :flag sexpr-list)
    :hints (("goal"
             :in-theory (disable* (:ruleset 4v-op-defs) 4v-<= 4v-lookup
                                  default-car default-cdr nth-when-zp nth-add1 nth
                                  ))
            (and stable-under-simplificationp
                 '(:use ((:instance 4v-alist-<=-necc
                                    (k x)
                                    (x env)
                                    (y env1)))))))

  (defthm nth-of-4v-sexpr-eval-list
    (4v-equiv (nth n (4v-sexpr-eval-list x env))
              (4v-sexpr-eval (nth n x) env))))


(defsection 4v-sexpr-eval-alist
  :parents (4v-sexpr-eval)
  :short "Extension of @(see 4v-sexpr-eval) to alists."

  :long "<p>@(call 4v-sexpr-eval-alist) is given an alist @('x') that should
bind names to sexprs.  It evaluates the sexprs under @('env') and returns a new
alist that binds the same names to the resulting four-valued constants.  The
new alist is an ordinary, non-fast alist.</p>

<p>It is beneficial for @('env') to be a fast alist; if it is not fast, we
temporarily make it fast.</p>"

  (defund 4v-sexpr-eval-alist1 (x env)
    "Assumes ENV is fast"
    (declare (xargs :guard t))
    (cond ((atom x)
           nil)
          ((atom (car x))
           (4v-sexpr-eval-alist1 (cdr x) env))
          (t
           (cons (cons (caar x) (4v-sexpr-eval (cdar x) env))
                 (4v-sexpr-eval-alist1 (cdr x) env)))))

  (defun 4v-sexpr-eval-alist (x env)
    "Makes ENV fast if necessary"
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic
         (cond ((atom x)
                nil)
               ((atom (car x))
                (4v-sexpr-eval-alist (cdr x) env))
               (t
                (cons (cons (caar x) (4v-sexpr-eval (cdar x) env))
                      (4v-sexpr-eval-alist (cdr x) env))))
         :exec
         (with-fast-alist env (4v-sexpr-eval-alist1 x env))))

  (defthm 4v-sexpr-eval-alist1-removal
    (equal (4v-sexpr-eval-alist1 x env)
           (4v-sexpr-eval-alist x env))
    :hints(("Goal" :in-theory (enable 4v-sexpr-eval-alist1))))

  (verify-guards 4v-sexpr-eval-alist)

  (defthm lookup-sexpr-eval-alist
    (equal (hons-assoc-equal x (4v-sexpr-eval-alist al env))
           (and (hons-assoc-equal x al)
                (cons x (4v-sexpr-eval (cdr (hons-assoc-equal x al)) env))))
    :hints(("Goal" :in-theory (disable 4v-sexpr-eval))))

  (defthm 4v-sexpr-eval-alist-append
    (equal (4v-sexpr-eval-alist (append a b) env)
           (append (4v-sexpr-eval-alist a env)
                   (4v-sexpr-eval-alist b env))))

  (defthm alist-keys-4v-sexpr-eval-alist
    (equal (alist-keys (4v-sexpr-eval-alist a env))
           (alist-keys a)))

  (defthm 4v-alist-<=-sexpr-eval-alist-monotonic-env
    (implies (4v-alist-<= a b)
             (4v-alist-<= (4v-sexpr-eval-alist x a)
                          (4v-sexpr-eval-alist x b)))))


(defsection 4v-sexpr-eval-alists
  :parents (4v-sexpr-eval)

  (defund 4v-sexpr-eval-alists1 (x env)
    "Assumes ENV is fast"
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (cons (4v-sexpr-eval-alist1 (car x) env)
            (4v-sexpr-eval-alists1 (cdr x) env))))

  (defun 4v-sexpr-eval-alists (x env)
    "Makes ENV fast if necessary"
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic
         (if (atom x)
             nil
           (cons (4v-sexpr-eval-alist (car x) env)
                 (4v-sexpr-eval-alists (cdr x) env)))
         :exec
         (with-fast-alist env
           (4v-sexpr-eval-alists1 x env))))

  (defthm 4v-sexpr-eval-alists1-removal
    (equal (4v-sexpr-eval-alists1 x env)
           (4v-sexpr-eval-alists x env))
    :hints(("Goal" :in-theory (enable 4v-sexpr-eval-alists1))))

  (verify-guards 4v-sexpr-eval-alists))


(defsection 4v-sexpr-eval-list-list
  :parents (4v-sexpr-eval)

  (defund 4v-sexpr-eval-list-list1 (x env)
    "Assumes ENV is fast"
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (cons (4v-sexpr-eval-list (car x) env)
            (4v-sexpr-eval-list-list1 (cdr x) env))))

  (defun 4v-sexpr-eval-list-list (x env)
    "Makes ENV fast if necessary"
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic
         (if (atom x)
             nil
           (cons (4v-sexpr-eval-list (car x) env)
                 (4v-sexpr-eval-list-list (cdr x) env)))
         :exec
         (with-fast-alist env
           (4v-sexpr-eval-list-list1 x env))))

  (defthm 4v-sexpr-eval-list-list1-removal
    (equal (4v-sexpr-eval-list-list1 x env)
           (4v-sexpr-eval-list-list x env))
    :hints(("Goal" :in-theory (enable 4v-sexpr-eval-list-list1))))

  (verify-guards 4v-sexpr-eval-list-list))


(defsection 4v-sexpr-restrict
  :parents (4v-sexprs)
  :short "Basic substitution operation for @(see 4v-sexprs)."

  :long "<p>@(call 4v-sexpr-restrict) takes a sexpr, @('x'), and a fast alist,
@('al') that should bind variables to sexprs.  It constructs a new sexpr that
is just a copy of @('x') where any variables bound in @('al') have been
replaced with their bound values.</p>

<p>We @(see memoize) this function to avoid repeatedly restricting shared
subexpressions, but this only helps when you are restricting with the same
alist.  We don't use @(':forget t') because you frequently want to restrict
several related expressions under the same alist, as in @(see
4v-sexpr-restrict-alist).  So, you'll generally need to manage clearing the
memoization table yourself.</p>

<p>Note that this function is \"dumb\" and does not try in any way to simplify
the resulting expressions.  The function @(see 4v-sexpr-restrict-with-rw) is a
\"smarter\" alternative that is generally slower but can produce simpler sexprs
as output.</p>"

  (defxdoc 4v-sexpr-restrict-list
    :parents (4v-sexpr-restrict)
    :short "Substitute into a list of sexprs."

    :long "<p>See @(see 4v-sexpr-restrict); this is just its mutually recursive
counterpart.</p>")

  (mutual-recursion
   (defun 4v-sexpr-restrict (x al)
     (declare (xargs :guard t))
     (if (atom x)
         (and x (let ((look (hons-get x al)))
                  (if look (cdr look) x)))
       (hons (car x)
             (4v-sexpr-restrict-list (cdr x) al))))

   (defun 4v-sexpr-restrict-list (x al)
     (declare (xargs :guard t))
     (if (atom x)
         x
       (hons (4v-sexpr-restrict (car x) al)
             (4v-sexpr-restrict-list (cdr x) al)))))

  (memoize '4v-sexpr-restrict
           :condition '(and (consp x) (consp (cdr x))))

  (defthm-4v-sexpr-flag
    (defthm 4v-sexpr-eval-4v-sexpr-restrict
      (equal (4v-sexpr-eval (4v-sexpr-restrict x al1) al2)
             (4v-sexpr-eval x (append (4v-sexpr-eval-alist al1 al2)
                                      al2)))
      :flag sexpr)
    (defthm 4v-sexpr-eval-list-sexpr-4v-sexpr-restrict-list
      (equal (4v-sexpr-eval-list (4v-sexpr-restrict-list x al1) al2)
             (4v-sexpr-eval-list x (append (4v-sexpr-eval-alist al1 al2)
                                           al2)))
      :flag sexpr-list)
    :hints (("goal"
             :in-theory (disable 4v-sexpr-eval 4v-fix)
             :expand ((:free (al) (4v-sexpr-eval x al))
                      (:free (al) (4v-sexpr-eval nil al))
                      (:free (al x y) (4v-sexpr-eval (cons x y) al)))
             :do-not-induct t))))


(defsection 4v-sexpr-restrict-alist
  :parents (4v-sexpr-restrict)
  :short "Extension of @(see 4v-sexpr-restrict) to alists."

  :long "<p>@(call 4v-sexpr-restrict-alist) is given an alist @('x') that
typically binds names to sexprs.  It restricts each of these sexprs using
@('al'), and returns a new alist that binds the same names to the resulting
sexprs.  The resulting alist is an ordinary, non-fast alist.</p>

<p>It is beneficial for @('env') to be a fast alist; if it is not fast, we we
temporarily make it fast.</p>"

  (defund 4v-sexpr-restrict-alist1 (x al)
    "Assumes AL is fast"
    (declare (xargs :guard t))
    (cond ((atom x)
           nil)
          ((atom (car x))
           (4v-sexpr-restrict-alist1 (cdr x) al))
          (t
           (cons (cons (caar x) (4v-sexpr-restrict (cdar x) al))
                 (4v-sexpr-restrict-alist1 (cdr x) al)))))

  (defun 4v-sexpr-restrict-alist (x al)
    "Makes AL fast if necessary"
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic
         (cond ((atom x)
                nil)
               ((atom (car x))
                (4v-sexpr-restrict-alist (cdr x) al))
               (t
                (cons (cons (caar x) (4v-sexpr-restrict (cdar x) al))
                      (4v-sexpr-restrict-alist (cdr x) al))))
         :exec
         (with-fast-alist al
           (4v-sexpr-restrict-alist1 x al))))

  (defthm 4v-sexpr-restrict-alist1-removal
    (equal (4v-sexpr-restrict-alist1 x al)
           (4v-sexpr-restrict-alist x al))
    :hints(("Goal" :in-theory (enable 4v-sexpr-restrict-alist1))))

  (verify-guards 4v-sexpr-restrict-alist)

  (defthm 4v-sexpr-eval-alist-4v-sexpr-restrict-alist
    (equal (4v-sexpr-eval-alist (4v-sexpr-restrict-alist x al) env)
           (4v-sexpr-eval-alist x (append (4v-sexpr-eval-alist al env)
                                          env)))
    :hints (("goal" :induct t)))

  (defthm hons-assoc-equal-4v-sexpr-restrict-alist
    (equal (hons-assoc-equal x (4v-sexpr-restrict-alist al env))
           (and (hons-assoc-equal x al)
                (cons x (4v-sexpr-restrict (cdr (hons-assoc-equal x al))
                                        env))))
    :hints (("goal" :induct t)))

  (defthm alist-keys-4v-sexpr-restrict-alist
    (equal (alist-keys (4v-sexpr-restrict-alist al env))
           (alist-keys al)))

  (defcong alist-equiv alist-equiv (4v-sexpr-restrict-alist a b) 1
    :hints ((witness :ruleset (alist-equiv-witnessing)))))


(defsection 4v-sexpr-compose
  :parents (4v-sexprs)
  :short "Alternate substitution operation for @(see 4v-sexprs)."

  :long "<p>@(call 4v-sexpr-compose) is takes a sexpr, @('x'), and a fast alist
@('al') that binds variables to sexprs.</p>

<p>We construct a new sexpr by copying @('x'), except that we
<b>unconditionally</b> replace every variable in @('x') with its binding in
@('al'), regardless of whether such a binding actually exists.  Any unbound
variables are just replaced by NIL, which in our semantics always evaluates to
X.</p>

<p>We @(see memoize) this function, but this only helps when you are composing
with the same alist.  We don't use @(':forget t') because you frequently want
to compose several related expressions under the same alist, as in @(see
4v-sexpr-restrict-alist).  So, you'll generally need to manage clearing the
memoization table yourself.</p>"

  (mutual-recursion
   (defun 4v-sexpr-compose (x al)
     (declare (xargs :guard t))
     (if (atom x)
         (and x (let ((look (hons-get x al)))
                  (and look (cdr look))))
       (hons (car x) (4v-sexpr-compose-list (cdr x) al))))

   (defun 4v-sexpr-compose-list (x al)
     (declare (xargs :guard t))
     (if (atom x)
         x
       (hons (4v-sexpr-compose (car x) al)
             (4v-sexpr-compose-list (cdr x) al)))))

  (memoize '4v-sexpr-compose
           :condition '(and (consp x) (consp (cdr x))))

  (defthm-4v-sexpr-flag
    (defthm 4v-sexpr-eval-4v-sexpr-compose
      (equal (4v-sexpr-eval (4v-sexpr-compose x al) env)
             (4v-sexpr-eval x (4v-sexpr-eval-alist al env)))
      :flag sexpr)
    (defthm 4v-sexpr-eval-list-4v-sexpr-compose-list
      (equal (4v-sexpr-eval-list (4v-sexpr-compose-list x al) env)
             (4v-sexpr-eval-list x (4v-sexpr-eval-alist al env)))
      :flag sexpr-list)
    :hints (("goal" :in-theory (disable* (:ruleset 4v-op-defs)
                                         4v-sexpr-eval-alist)))))



(defsection 4v-sexpr-compose-alist
  :parents (4v-sexpr-compose)
  :short "Extension of @(see 4v-sexpr-compose) to alists."

  :long "<p>@(call 4v-sexpr-compose-alist) is given an alist @('x') that
typically binds names to sexprs.  It composes each of these sexprs with
@('al'), and returns a new alist that binds the same names to the resulting
sexprs.  The resulting alist is an ordinary, non-fast alist.</p>

<p>It is beneficial for @('env') to be a fast alist; if it is not fast, we we
temporarily make it fast.</p>"

  (defund 4v-sexpr-compose-alist1 (x al)
    "Assumes AL is fast"
    (declare (xargs :guard t))
    (cond ((atom x)
           nil)
          ((atom (car x))
           (4v-sexpr-compose-alist1 (cdr x) al))
          (t
           (cons (cons (caar x) (4v-sexpr-compose (cdar x) al))
                 (4v-sexpr-compose-alist1 (cdr x) al)))))

  (defun 4v-sexpr-compose-alist (x al)
    "Makes AL fast if necessary"
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic
         (cond ((atom x)
                nil)
               ((atom (car x))
                (4v-sexpr-compose-alist (cdr x) al))
               (t
                (cons (cons (caar x) (4v-sexpr-compose (cdar x) al))
                      (4v-sexpr-compose-alist (cdr x) al))))
         :exec
         (with-fast-alist al
           (4v-sexpr-compose-alist1 x al))))

  (defthm 4v-sexpr-compose-alist1-removal
    (equal (4v-sexpr-compose-alist1 x al)
           (4v-sexpr-compose-alist x al))
    :hints(("Goal" :in-theory (enable 4v-sexpr-compose-alist1))))

  (verify-guards 4v-sexpr-compose-alist)

  (defthm hons-assoc-equal-4v-sexpr-compose-alist
    (equal (hons-assoc-equal k (4v-sexpr-compose-alist x al))
           (and (hons-assoc-equal k x)
                (cons k (4v-sexpr-compose (cdr (hons-assoc-equal k x)) al)))))

  (defthm 4v-sexpr-eval-alist-4v-sexpr-compose-alist
    (equal (4v-sexpr-eval-alist (4v-sexpr-compose-alist x al) env)
           (4v-sexpr-eval-alist x (4v-sexpr-eval-alist al env)))
    :hints(("Goal" :in-theory (disable 4v-sexpr-eval))))

  (defthm alist-keys-4v-sexpr-compose-alist
    (equal (alist-keys (4v-sexpr-compose-alist al env))
           (alist-keys al)))

  (defthm 4v-sexpr-compose-alist-append
    (equal (4v-sexpr-compose-alist (append al1 al2) env)
           (append (4v-sexpr-compose-alist al1 env)
                   (4v-sexpr-compose-alist al2 env)))))



(defsection 4v-sexpr-alist-extract
  :parents (4v-sexprs)
  :short "Extract a portion of a <see topic='@(url 4v-sexprs)'>4v-sexpr</see> alist."
  :long "<p>@(call 4v-sexpr-alist-extract) is given:</p>

<ul> <li>@('keys'), a list of names, and</li> <li>@('al'), a fast alist binding
 names to sexprs.</li> </ul>

<p>It produces a new alist that binds all of the names in @('keys') to their
corresponding sexprs in @('al').  The result is an ordinary, non-fast
alist.</p>

<p>More precisely, the new alist binds each @('k') in @('keys') to:</p>

<ul>
 <li>@('al[k]') when @('k') is bound in @('al'), or</li>
 <li>@('NIL') (which just evaluates to X) otherwise.</li>
</ul>

<p>This is just slightly different than @(see fal-extract): whereas fal-extract
omits missing keys, this binds them to nil.</p>

<p>This function can be a useful for removing any \"extraneous\" bindings from
an the sexpr-alist @('al').  Some equivalence relations like @(see
4v-sexpr-alist-equiv) check whether alists have the same bindings because this
allows for powerful composition theorems.  For instance, the following rule
would not hold if @('a-equiv') were allowed to contain bind variables not bound
by @('a'):</p>

@(thm 4v-sexpr-alist-equiv-implies-4v-sexpr-alist-equiv-append-1)"

  (defund 4v-sexpr-alist-extract1 (keys al)
    "Assumes AL is fast"
    (declare (xargs :guard t))
    (if (atom keys)
        nil
      (cons (cons (car keys) (cdr (hons-get (car keys) al)))
            (4v-sexpr-alist-extract1 (cdr keys) al))))

  (defun 4v-sexpr-alist-extract (keys al)
    "Makes AL fast if necessary"
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic
         (if (atom keys)
             nil
           (cons (cons (car keys) (cdr (hons-get (car keys) al)))
                 (4v-sexpr-alist-extract (cdr keys) al)))
         :exec
         (with-fast-alist al
           (4v-sexpr-alist-extract1 keys al))))

  (defthm 4v-sexpr-alist-extract1-removal
    (equal (4v-sexpr-alist-extract1 keys al)
           (4v-sexpr-alist-extract keys al))
    :hints(("Goal" :in-theory (enable 4v-sexpr-alist-extract1))))

  (verify-guards 4v-sexpr-alist-extract)

  (defcong alist-equiv equal (4v-sexpr-alist-extract keys al) 2))





(defsection 4v-sexpr-eval-default
  (defsection 4v-lookup-default

    (defun 4v-lookup-default (k env default)
      (declare (xargs :guard t))
      (let ((look (hons-get k env)))
        (prog2$ (and (not look) (4v-lookup-not-found k))
                (4v-fix (if look (cdr look) default)))))

    (defthm 4vp-of-4v-lookup-default
      (4vp (4v-lookup-default k env default)))

    (defthm 4v-fix-4v-lookup-default
      (equal (4v-fix (4v-lookup-default k env default))
             (4v-lookup-default k env default))))


  (mutual-recursion
   (defun 4v-sexpr-eval-default (x env default)
     (declare (xargs :guard t))
     (b* (((when (atom x))
           ;; NIL is regarded as X, which is important in 4v-sexpr-compose and
           ;; perhaps other places.  Any other atom is a variable and we look
           ;; up its value in env.
           (if x
               (4v-lookup-default x env default)
             (4vx)))
          (fn   (car x))
          (args (4v-sexpr-eval-default-list (cdr x) env default)))
       (4v-sexpr-apply fn args)))

   (defun 4v-sexpr-eval-default-list (x env default)
     (declare (xargs :guard t))
     (if (atom x)
         nil
       (cons (4v-sexpr-eval-default (car x) env default)
             (4v-sexpr-eval-default-list (cdr x) env default)))))

  (memoize '4v-sexpr-eval-default :condition '(and (consp x) (consp (cdr x))))

  (in-theory (disable 4v-sexpr-eval-default)))


(defsection 4v-sexpr-eval-default-alist

  (defund 4v-sexpr-eval-default-alist1 (x env default)
    "Assumes ENV is fast"
    (declare (xargs :guard t))
    (cond ((atom x)
           nil)
          ((atom (car x))
           (4v-sexpr-eval-default-alist1 (cdr x) env default))
          (t
           (cons (cons (caar x) (4v-sexpr-eval-default (cdar x) env default))
                 (4v-sexpr-eval-default-alist1 (cdr x) env default)))))

  (defund 4v-sexpr-eval-default-alist (x env default)
    "Makes ENV fast if necessary"
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic
         (cond ((atom x)
                nil)
               ((atom (car x))
                (4v-sexpr-eval-default-alist (cdr x) env default))
               (t
                (cons (cons (caar x) (4v-sexpr-eval-default (cdar x) env default))
                      (4v-sexpr-eval-default-alist (cdr x) env default))))
         :exec
         (with-fast-alist env (4v-sexpr-eval-default-alist1 x env default))))

  (local (in-theory (enable 4v-sexpr-eval-default-alist
                            4v-sexpr-eval-default-alist1)))


  (defund 4v-sexpr-eval-default-alists1 (x env default)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (cons (4v-sexpr-eval-default-alist1 (car x) env default)
            (4v-sexpr-eval-default-alists1 (cdr x) env default))))

  (defund 4v-sexpr-eval-default-alists (x env default)
    "Makes ENV fast if necessary"
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic
         (if (atom x)
             nil
           (cons (4v-sexpr-eval-default-alist (car x) env default)
                 (4v-sexpr-eval-default-alists (cdr x) env default)))
         :exec
         (with-fast-alist env (4v-sexpr-eval-default-alists1 x env default))))

  (local (in-theory (enable 4v-sexpr-eval-default-alists
                            4v-sexpr-eval-default-alists1)))


  (defthm 4v-sexpr-eval-default-alist1-removal
    (equal (4v-sexpr-eval-default-alist1 x env default)
           (4v-sexpr-eval-default-alist x env default)))

  (defthm 4v-sexpr-eval-default-alists1-removal
    (equal (4v-sexpr-eval-default-alists1 x env default)
           (4v-sexpr-eval-default-alists x env default))
    :hints(("Goal" :in-theory (e/d ()
                                   (4v-sexpr-eval-default)))))

  (verify-guards 4v-sexpr-eval-default-alist)
  (verify-guards 4v-sexpr-eval-default-alists)

  (defthm lookup-sexpr-eval-default-alist
    (equal (hons-assoc-equal x (4v-sexpr-eval-default-alist al env default))
           (and (hons-assoc-equal x al)
                (cons x (4v-sexpr-eval-default (cdr (hons-assoc-equal x al)) env default)))))

  (defthm 4v-sexpr-eval-default-alist-append
    (equal (4v-sexpr-eval-default-alist (append a b) env default)
           (append (4v-sexpr-eval-default-alist a env default)
                   (4v-sexpr-eval-default-alist b env default))))

  (defthm alist-keys-4v-sexpr-eval-default-alist
    (equal (alist-keys (4v-sexpr-eval-default-alist a env default))
           (alist-keys a))))
