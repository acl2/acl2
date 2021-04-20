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
(include-book "a4vec")
(include-book "aig-arith")
(include-book "4vmask")
(include-book "std/util/defrule" :dir :system)
(include-book "centaur/bitops/limited-shifts" :dir :system)
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (std::add-default-post-define-hook :fix))


(defsection a4vec-operations
  :parents (bit-blasting)
  :short "Symbolic versions of the SV @(see functions) that operate on @(see
a4vec)s instead of @(see 4vec)s."

  :long "<p>These operations form the core of our support for @(see
bit-blasting) SV @(see expressions).</p>

<p>Our basic goal here is to provide efficient @(see acl2::aig)-based
implementations of all of the SV @(see functions).  It is generally important
for these functions to produce small AIGs so that we will produce simpler,
smaller problems for back-end tools like SAT solvers and BDD packages to
process.</p>

<p>These are many functions to implement, but most of this is straightforward
and we can substantially reuse our functions for @(see
aig-symbolic-arithmetic), extending them as appropriate to deal with our
four-valued logic.</p>

<p>A few functions with fancier implementations include @(see a4vec-concat),
which is reused in @(see a4vec-zero-ext) and @(see a4vec-sign-ext), and also
the shifting operations @(see a4vec-rsh) and @(see a4vec-lsh).  Each of these
take some special measures to try to avoid creating catastrophically large
vectors.</p>")

(local (xdoc::set-default-parents a4vec-operations))

(local (defthm true-listp-of-scdr
         (implies (true-listp x)
                  (true-listp (gl::scdr x)))
         :hints(("Goal" :in-theory (enable gl::scdr)))
         :rule-classes :type-prescription))

(local (in-theory (disable aig-list->s)))

(local (defthm aig-list->u-when-aig-list->s-nonneg
         (implies (<= 0 (aig-list->s x env))
                  (equal (aig-list->u x env)
                         (aig-list->s x env)))
         :hints(("Goal" :in-theory (enable aig-list->u
                                           aig-list->s
                                           gl::scdr
                                           gl::s-endp)))))

(local (defthm aig-list->s-open-quote
         (implies (syntaxp (quotep x))
                  (equal (aig-list->s x env)
                         (B* (((MV FIRST REST GL::END)
                               (GL::FIRST/REST/END X)))
                           (IF GL::END
                               (GL::BOOL->SIGN (AIG-EVAL FIRST ENV))
                               (BITOPS::LOGCONS (BOOL->BIT (AIG-EVAL FIRST ENV))
                                                (AIG-LIST->S REST ENV))))))
         :hints(("Goal" :in-theory (enable aig-list->s)))))

(local (defthm aig-list->s-of-bfr-snorm
         (equal (aig-list->s (gl::bfr-snorm x) env)
                (aig-list->s x env))
         :hints(("Goal" :in-theory (enable aig-list->s gl::bfr-snorm)))))

(local (defthm aig-list->s-of-bfr-scons
         (equal (aig-list->s (gl::bfr-scons a b) env)
                (bitops::logcons (bool->bit (aig-eval a env))
                                 (aig-list->s b env)))
         :hints(("Goal" :expand ((aig-list->s (gl::bfr-scons a b) env)
                                 (aig-list->s b env))
                 :in-theory (enable gl::s-endp-of-bfr-scons)
                 :do-not-induct t))))

(local (defthm aig-list->s-of-bfr-sterm
         (equal (aig-list->s (gl::bfr-sterm x) env)
                (bool->vec (aig-eval x env)))
         :hints(("Goal" :in-theory (enable aig-list->s)))))


(defsection a4vec-x
  :short "@(call a4vec-x) return an @(see a4vec) that evaluates to @(see
4vec-x) under every environment."
  :long "@(def a4vec-x)"

  (defmacro a4vec-x ()
    (list 'quote (a4vec (aig-sterm t)
                        (aig-sterm nil))))

  (defthm a4vec-x-correct
    (equal (a4vec-eval (a4vec-x) env)
           (4vec-x))))


(defsection a4vec-0
  :short "@(call a4vec-0) return an @(see a4vec) that evaluates to 0 under
every environment."
  :long "@(def a4vec-0)"

  (defmacro a4vec-0 ()
    (list 'quote (a4vec (aig-sterm nil)
                        (aig-sterm nil))))

  (defthm a4vec-0-correct
    (equal (a4vec-eval (a4vec-0) env)
           (4vec 0 0))))


(defsection a4vec-1x
  :short "@(call a4vec-1x) returns an @(see a4vec) that evaluates to @(see
4vec-1x) under every environment."
  :long "@(def a4vec-1x)"

  (defmacro a4vec-1x ()
    (list 'quote (a4vec (aig-scons t (aig-sterm nil))
                        (aig-sterm nil))))

  (defthm a4vec-1x-correct
    (equal (a4vec-eval (a4vec-1x) env)
           (4vec-1x))))


(define 4vec->a4vec ((x 4vec-p))
  :short "Convert a plain @(see 4vec) into a symbolic @(see a4vec)."
  :returns (res a4vec-p)
  :long "<p>This is used, e.g., to create the initial @(see a4vec)s for any
quoted constants in the svex we are bit-blasting.</p>"
  (b* (((4vec x)))
    (a4vec (aig-i2v x.upper)
           (aig-i2v x.lower)))
  ///
  (defthm 4vec->a4vec-correct
    (equal (a4vec-eval (4vec->a4vec x) env)
           (4vec-fix x))))


(define a2vec-p ((x a4vec-p))
  :returns (aig)
  :short "Construct an AIG that captures: when does an @(see a4vec) evaluate to
a @(see 2vec-p)?"

  :long "<p>This is a supporting function that is widely used by many of our
@(see a4vec-operations).  For instance, operations like @(see 4vec-plus) return
all Xes when there are any X/Z bits.</p>"

  (b* (((a4vec x)))
    ;; The laziness of aig-and means that this properly short-circuits.
    (aig-=-ss x.upper x.lower))
  ///
  (defthm a2vec-p-correct
    (equal (aig-eval (a2vec-p x) env)
           (2vec-p (a4vec-eval x env)))))


(define a4vec-ite-fn ((test "Test AIG (not a 4vec!).")
                      (then a4vec-p)
                      (else a4vec-p))
  :parents (a4vec-ite)
  :returns (res a4vec-p)
  :short "Basic if-then-else for symbolic 4vecs."
  (cond ((eq test t)   (a4vec-fix then))
        ((eq test nil) (a4vec-fix else))
        (t (b* (((a4vec then))
                ((a4vec else)))
             ;; BOZO It looks like this is going to call aig-ite on each pair
             ;; of bits, which is going to be checking over and over again
             ;; whether the test is known to be T or NIL.  That probably isn't
             ;; worth worrying about.  It might be that we could optimize
             ;; aig-ite-bss-fn itself to avoid this, using an aux function.
             (a4vec (aig-ite-bss-fn test then.upper else.upper)
                    (aig-ite-bss-fn test then.lower else.lower)))))
  ///
  (defthm a4vec-ite-fn-correct
    (equal (a4vec-eval (a4vec-ite-fn test then else) env)
           (if (aig-eval test env)
               (a4vec-eval then env)
             (a4vec-eval else env))))

  (defthm a4vec-ite-fn-of-const-tests
    (and (equal (a4vec-ite-fn t then else) (a4vec-fix then))
         (equal (a4vec-ite-fn nil then else) (a4vec-fix else)))))


(defsection a4vec-ite
  :short "Lazy macro for if-then-else of symbolic 4vecs."
  :long "@({ (a4vec-ite test then else) --> ans })

<ul>
<li>@('test') is a single AIG, not an @(see a4vec).</li>
<li>@('then') and @('else') are @(see a4vec)s.</li>
<li>@('ans') is also an @(see a4vec).</li>
</ul>

<p>This is widely used in the implementation of our @(see a4vec-operations).
It is similar in spirit to @(see acl2::q-ite); we try to avoid evaluating
@('then') or @('else') if we can resolve @('test').</p>"

  (defmacro a4vec-ite (test then else)
    (cond ((and (or (symbolp then) (quotep then))
                (or (symbolp else) (quotep else)))
           ;; THEN and ELSE are constants or variables, so there's no point in
           ;; trying to lazily avoid computing them, because they are already
           ;; computed.
           `(a4vec-ite-fn ,test ,then ,else))
          (t
           `(mbe :logic (a4vec-ite-fn ,test ,then ,else)
                 :exec (let ((a4vec-ite-test ,test))
                         ;; BOZO this duplicates ,else, which could lead to
                         ;; code blowup.  We can probably avoid that...

                         ;; BOZO should also check-vars-not-free here.  See
                         ;; aig-ite and similar
                         (if a4vec-ite-test
                             (let ((a4vec-ite-then ,then))
                               (if (eq a4vec-ite-test t)
                                   a4vec-ite-then
                                 (a4vec-ite-fn a4vec-ite-test a4vec-ite-then ,else)))
                           ,else)))))))


(define a4vec-bit-extract ((n a4vec-p) (x a4vec-p))
  :short "Symbolic version of @(see 4vec-bit-extract)."
  :returns (res a4vec-p)
  (b* (((a4vec x))
       ((a4vec n)))
    (a4vec-ite (aig-andc2 (a2vec-p n)            ;; Is N properly two-valued?
                          (aig-sign-s n.upper)   ;; Is N non-negative?
                          )
               ;; N is properly two-valued and natural, so extract
               ;; the Nth bit of X and return it as a one-bit a4vec.
               (b* ((ubit (aig-logbitp-n2v 1 n.upper x.upper))
                    (lbit (aig-logbitp-n2v 1 n.upper x.lower)))
                 (a4vec (aig-scons ubit (aig-sterm nil))
                        (aig-scons lbit (aig-sterm nil))))
               ;; N is bad, so just return a single X bit.
               (a4vec-1x)))
  ///
  (defthm a4vec-bit-extract-correct
    (equal (a4vec-eval (a4vec-bit-extract n x) env)
           (4vec-bit-extract (a4vec-eval n env)
                             (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 4vec-bit-extract
                                      4vec-bit-index)))))


(define a4vec-syntactic-3vec-p-rec ((x true-listp) (y true-listp))
  :short "Make sure there is no pair of bits with Xi == 0 while Yi == 1."
  :returns bool
  :parents (a4vec-syntactic-3vec-p)
  :measure (+ (len x) (len y))
  (b* (((mv xf xr xe) (gl::first/rest/end x))
       ((mv yf yr ye) (gl::first/rest/end y)))
    (and (or (eq xf t)          ;; Xf is obviously non-0
             (eq yf nil)        ;; Yf is obviously non-1
             (hons-equal xf yf) ;; Same bits rules out Xf == 0 while Yf == 1.
             )
         (if (and xe ye)
             ;; End of both vectors, so we're done.
             t
           ;; More bits to check, so keep going.
           (a4vec-syntactic-3vec-p-rec xr yr))))
  ///
  (defthm a4vec-syntactic-3vec-p-rec-correct
    (implies (a4vec-syntactic-3vec-p-rec x y)
             (equal (logand (aig-list->s y env) (lognot (aig-list->s x env)))
                    0))
    :hints (("goal"
             :induct (a4vec-syntactic-3vec-p-rec x y)
             :expand ((aig-list->s y env)
                      (aig-list->s x env))))))

(define a4vec-syntactic-3vec-p ((x a4vec-p))
  :short "Try to cheaply, statically determine whether an @(see a4vec) always
evaluates to a @(see 3vec), i.e., whether it has no Z bits."

  :long "<p>This is used mainly in @(see a3vec-fix): when we know that there
are no Z bits, we can avoid building AIGs to do unfloating.</p>"
  (b* (((a4vec x)))
    (a4vec-syntactic-3vec-p-rec x.upper x.lower))
  ///
  (defthm a4vec-syntactic-3vec-p-correct
    (implies (a4vec-syntactic-3vec-p x)
             (3vec-p (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 3vec-p)))))


(define a3vec-fix ((x a4vec-p))
  :short "Symbolic version of @(see 3vec-fix)."
  :returns (x-fix a4vec-p)
  (b* (((when (a4vec-syntactic-3vec-p x))
        ;; We don't have to do anything because we can determine, cheaply and
        ;; statically, that there are no Z bits at all.
        (a4vec-fix x))
       ((a4vec x)))
    (a4vec (aig-logior-ss x.upper x.lower)
           (aig-logand-ss x.upper x.lower)))
  ///
  (defthm a3vec-fix-correct
    (equal (a4vec-eval (a3vec-fix x) env)
           (3vec-fix (a4vec-eval x env)))
    :hints (("goal" :in-theory (disable a4vec-eval-of-var))
            (and stable-under-simplificationp
                 '(:in-theory (enable 3vec-fix a4vec-eval-of-var))))))


(define a3vec-bitnot ((x a4vec-p))
  :short "Symbolic version of @(see 3vec-bitnot)."
  :returns (res a4vec-p)
  (b* (((a4vec x)))
    (a4vec (aig-lognot-s x.lower)
           (aig-lognot-s x.upper)))
  ///
  (defthm a3vec-bitnot-correct
    (equal (a4vec-eval (a3vec-bitnot x) env)
           (3vec-bitnot (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 3vec-bitnot)))))


(define a4vec-onset ((x a4vec-p))
  :short "Symbolic version of @(see 4vec-onset)."
  :returns (res a4vec-p)
  (b* (((a4vec x)))
    (a4vec x.upper (aig-logand-ss x.upper x.lower)))
  ///
  (defthm a4vec-onset-correct
    (equal (a4vec-eval (a4vec-onset x) env)
           (4vec-onset (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 4vec-onset)))))


(define a4vec-offset ((x a4vec-p))
  :short "Symbolic version of @(see 4vec-offset)."
  :returns (res a4vec-p)
  (b* (((a4vec x)))
    (a4vec (aig-lognot-s x.lower)
           (aig-lognor-ss x.upper x.lower)))
  ///
  (defthm a4vec-offset-correct
    (equal (a4vec-eval (a4vec-offset x) env)
           (4vec-offset (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 4vec-offset)))))


(define a3vec-bitand ((x a4vec-p) (y a4vec-p))
  :short "Symbolic version of @(see 3vec-bitand)."
  :returns (res a4vec-p)
  (b* (((a4vec x))
       ((a4vec y)))
    (a4vec (aig-logand-ss x.upper y.upper)
           (aig-logand-ss x.lower y.lower)))
  ///
  (defthm a3vec-bitand-correct
    (equal (a4vec-eval (a3vec-bitand x y) env)
           (3vec-bitand (a4vec-eval x env)
                        (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 3vec-bitand)))))


(define a3vec-bitor ((x a4vec-p) (y a4vec-p))
  :short "Symbolic version of @(see 3vec-bitor)."
  :returns (res a4vec-p)
  (b* (((a4vec x))
       ((a4vec y)))
    (a4vec (aig-logior-ss x.upper y.upper)
           (aig-logior-ss x.lower y.lower)))
  ///
  (defthm a3vec-bitor-correct
    (equal (a4vec-eval (a3vec-bitor x y) env)
           (3vec-bitor (a4vec-eval x env)
                       (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 3vec-bitor)))))


(define a3vec-bitxor ((x a4vec-p) (y a4vec-p))
  :short "Symbolic version of @(see 3vec-bitxor)."
  :returns (res a4vec-p)
  (b* (((a4vec x))
       ((a4vec y))
       (xmask (aig-logior-ss (aig-logandc2-ss x.upper x.lower)
                             (aig-logandc2-ss y.upper y.lower))))
    (a4vec (aig-logior-ss xmask (aig-logxor-ss x.upper y.upper))
           (aig-logandc1-ss xmask (aig-logxor-ss x.lower y.lower))))
  ///
  (defthm a3vec-bitxor-correct
    (equal (a4vec-eval (a3vec-bitxor x y) env)
           (3vec-bitxor (a4vec-eval x env)
                        (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 3vec-bitxor)))))


(define a4vec-res ((a a4vec-p) (b a4vec-p))
  :short "Symbolic version of @(see 4vec-res)."
  :returns (res a4vec-p)
  (b* (((a4vec a))
       ((a4vec b)))
    (a4vec (aig-logior-ss a.upper b.upper)
           (aig-logand-ss a.lower b.lower)))
  ///
  (defthm a4vec-res-correct
    (equal (a4vec-eval (a4vec-res x y) env)
           (4vec-res (a4vec-eval x env)
                     (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 4vec-res)))))


(define a4vec-resand ((a a4vec-p) (b a4vec-p))
  :short "Symbolic version of @(see 4vec-resand)."
  :returns (res a4vec-p)
  (b* (((a4vec a))
       ((a4vec b)))
    (a4vec (aig-logand-sss (aig-logior-ss a.upper a.lower)  ;; a not 0
                           (aig-logior-ss b.upper b.lower)  ;; b not 0
                           (aig-logior-ss a.upper b.upper))
           (aig-logand-ss a.lower b.lower)))
  ///
  (defthm a4vec-resand-correct
    (equal (a4vec-eval (a4vec-resand x y) env)
           (4vec-resand (a4vec-eval x env)
                        (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 4vec-resand)))))


(define a4vec-resor ((a a4vec-p) (b a4vec-p))
  :short "Symbolic version of @(see 4vec-resor)."
  :returns (res a4vec-p)
  (b* (((a4vec a))
       ((a4vec b)))
    (a4vec (aig-logior-ss a.upper b.upper)
           (aig-logior-sss (aig-logand-ss a.upper a.lower)  ;; a not 0
                           (aig-logand-ss b.upper b.lower)  ;; b not 0
                           (aig-logand-ss a.lower b.lower))))
  ///
  (defthm a4vec-resor-correct
    (equal (a4vec-eval (a4vec-resor x y) env)
           (4vec-resor (a4vec-eval x env)
                       (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 4vec-resor)))))


(define a4vec-override ((stronger a4vec-p)
                        (weaker a4vec-p))
  :short "Symbolic version of @(see 4vec-override)."
  :returns (res a4vec-p)
  (b* (((a4vec stronger))
       ((a4vec weaker)))
    (a4vec (aig-logior-ss (aig-logand-ss stronger.lower weaker.upper) stronger.upper)
           (aig-logand-ss (aig-logior-ss stronger.upper weaker.lower) stronger.lower)))
  ///
  (defthm a4vec-override-correct
    (equal (a4vec-eval (a4vec-override x y) env)
           (4vec-override (a4vec-eval x env)
                          (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 4vec-override))
           (bitops::logbitp-reasoning))))


(define a3vec-reduction-and ((x a4vec-p))
  :short "Symbolic version of @(see 3vec-reduction-and)."
  :returns (res a4vec-p)
  (b* (((a4vec x)))
    (a4vec (aig-sterm (aig-=-ss x.upper (aig-sterm t)))
           (aig-sterm (aig-=-ss x.lower (aig-sterm t)))))
  ///
  (defthm a3vec-reduction-and-correct
    (equal (a4vec-eval (a3vec-reduction-and x) env)
           (3vec-reduction-and (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 3vec-reduction-and)))))


(define a3vec-reduction-or ((x a4vec-p))
  :short "Symbolic version of @(see 3vec-reduction-or)."
  :returns (res a4vec-p)
  (b* (((a4vec x)))
    (a4vec (aig-sterm (aig-not (aig-=-ss x.upper (aig-sterm nil))))
           (aig-sterm (aig-not (aig-=-ss x.lower (aig-sterm nil))))))
  ///
  (defthm a3vec-reduction-or-correct
    (equal (a4vec-eval (a3vec-reduction-or x) env)
           (3vec-reduction-or (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 3vec-reduction-or)))))


(define a4vec-xdet ((x a4vec-p))
  :short "Symbolic version of @(see 4vec-xdet)."
  :returns (res a4vec-p)
  (a4vec-ite (a2vec-p x)
             ;; No X/Z bits, so return the input unchanged (modulo fixing)
             (a4vec-fix x)
             ;; X/Z bit somewhere, so just return all Xes.
             (a4vec-x))
  ///
  (defthm a4vec-xdet-correct
    (equal (a4vec-eval (a4vec-xdet x) env)
           (4vec-xdet (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 4vec-xdet lognot)))))


(define aig-countones-aux ((x true-listp))
  :returns (res true-listp)
  (if (atom x)
      nil
    (b* ((rest (aig-countones-aux (cdr x))))
      (aig-+-ss (car x) nil rest)))
  ///
  (defret aig-countones-aux-correct
    (equal (aig-list->s (aig-countones-aux x) env)
           (logcount (aig-list->u x env)))
    :hints(("Goal" :in-theory (enable logcount**)))))


(define aig-onehot-aux ((x true-listp))
  :returns (mv (zero) (one))
  (b* (((when (atom x)) (mv t nil))
       ((mv zero one) (aig-onehot-aux (cdr x))))
    (mv (aig-and zero (aig-not (car x)))
        (aig-ite (car x) zero one)))
  ///
  (defret aig-onehot-aux-zero-correct
    (equal (aig-eval zero env)
           (equal (logcount (aig-list->u x env)) 0))
    :hints(("Goal" :in-theory (enable logcount**))))

  (defret aig-onehot-aux-one-correct
    (equal (aig-eval one env)
           (equal (logcount (aig-list->u x env)) 1))
    :hints(("Goal" :in-theory (enable logcount**)))))
       



(define a4vec-countones ((x a4vec-p))
  :short "Symbolic version of @(see 4vec-countones)."
  :returns (res a4vec-p)
  (a4vec-ite (aig-and (a2vec-p x)
                      (aig-not (aig-sign-s (a4vec->upper x))))
             (b* ((val (aig-countones-aux (a4vec->upper x))))
               (a4vec val val))
             ;; X/Z bit somewhere, so just return all Xes.
             (a4vec-x))
  ///
  (defthm a4vec-countones-correct
    (equal (a4vec-eval (a4vec-countones x) env)
           (4vec-countones (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 4vec-countones)))))


(define a4vec-onehot ((x a4vec-p))
  :short "Symbolic version of @(see 4vec-onehot)."
  :returns (res a4vec-p)
  (a4vec-ite (aig-and (a2vec-p x)
                      (aig-not (aig-sign-s (a4vec->upper x))))
             (b* (((mv ?zero one) (aig-onehot-aux (a4vec->upper x)))
                  (val (aig-scons one nil)))
               (a4vec val val))
             ;; X/Z bit somewhere, so just return all Xes.
             (a4vec-x))
  ///
  (defthm a4vec-onehot-correct
    (equal (a4vec-eval (a4vec-onehot x) env)
           (4vec-onehot (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 4vec-onehot)))))

(define a4vec-onehot0 ((x a4vec-p))
  :short "Symbolic version of @(see 4vec-onehot0)."
  :returns (res a4vec-p)
  (a4vec-ite (aig-and (a2vec-p x)
                      (aig-not (aig-sign-s (a4vec->upper x))))
             (b* (((mv zero one) (aig-onehot-aux (a4vec->upper x)))
                  (ok (aig-or zero one))
                  (val (aig-scons ok nil)))
               (a4vec val val))
             ;; X/Z bit somewhere, so just return all Xes.
             (a4vec-x))
  ///
  (defthm a4vec-onehot0-correct
    (equal (a4vec-eval (a4vec-onehot0 x) env)
           (4vec-onehot0 (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 4vec-onehot0)))))

(define a4vec-mask-check ((mask 4vmask-p)
                          (idx natp)
                          (vec true-listp "aig list")
                          (upperp booleanp))
  :returns (already-maskedp booleanp)
  :measure (len vec)
  :prepwork ((local (defthmd logbitp-past-integer-length-iff-logtail-minus1
                      (iff (equal (logtail idx mask) -1)
                           (and (<= (integer-length mask) (nfix idx))
                                (logbitp idx mask)))
                      :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs
                                                         ihsext-inductions))))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable logbitp-past-integer-length-iff-logtail-minus1))))
  (b* ((idx (lnfix idx))
       (mask (4vmask-fix mask))
       ((mv first rest endp) (gl::first/rest/end vec))
       ((when endp)
        (or (mbe :logic (equal (logtail idx (sparseint-val mask)) -1)
                 :exec (and (<= (sparseint-length mask) idx)
                            (eql 1 (sparseint-bit idx mask))))  ;; (equal (4vmask-fix mask) -1)
            (equal first (mbe :logic (acl2::bool-fix upperp) :exec upperp)))))
    (and (or (eql 1 (sparseint-bit idx (4vmask-fix mask)))
             (equal first (mbe :logic (acl2::bool-fix upperp) :exec upperp)))
         (a4vec-mask-check mask (1+ (lnfix idx)) rest upperp)))
  ///
  (local (in-theory (disable bitops::logcdr-natp acl2::logtail-identity
                             bitops::logbitp-when-bitmaskp
                             bitops::logand-with-negated-bitmask
                             bitops::logtail-natp)))

  (local (defthmd logtail-in-terms-of-logbitp
           (equal (logtail idx x)
                  (logcons (bool->bit (logbitp idx x)) (logtail idx (logcdr x))))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))
           :rule-classes ((:definition :controller-alist ((acl2::logtail$inline t t))
                           :clique acl2::logtail$inline))))
  (local
   (defthm a4vec-mask-check-correct-lemma
     (implies (a4vec-mask-check mask idx vec upperp)
              (and (implies upperp
                            (equal (logior (lognot (logtail idx (sparseint-val (4vmask-fix mask))))
                                           (aig-list->s vec env))
                                   (aig-list->s vec env)))
                   (implies (not upperp)
                            (equal (logand (logtail idx (sparseint-val (4vmask-fix mask)))
                                           (aig-list->s vec env))
                                   (aig-list->s vec env)))))
     :hints(("Goal" :in-theory (enable* aig-list->s aig-logior-ss aig-i2v
                                        bitops::ihsext-recursive-redefs)
             :induct (a4vec-mask-check mask idx vec upperp)
             :expand ((:with logtail-in-terms-of-logbitp
                       (LOGTAIL IDX (sparseint-val (4VMASK-FIX mask)))))
             ))
     :rule-classes nil))

  (defthmd a4vec-mask-check-correct
    (and (implies (a4vec-mask-check mask 0 vec t)
                  (equal (logior (lognot (sparseint-val (4vmask-fix mask))) (aig-list->s vec env))
                         (aig-list->s vec env)))
         (implies (a4vec-mask-check mask 0 vec nil)
                  (equal (logand (sparseint-val (4vmask-fix mask)) (aig-list->s vec env))
                         (aig-list->s vec env))))
    :hints (("goal" :use ((:instance a4vec-mask-check-correct-lemma
                           (idx 0) (upperp t))
                          (:instance a4vec-mask-check-correct-lemma
                           (idx 0) (upperp nil))))))

  ;; helpful for deffixequiv:
  (local (in-theory (disable (:d a4vec-mask-check)
                             acl2::equal-of-booleans-rewrite))))


(define aig-scons-with-hint (b
                             (v true-listp)
                             (hint true-listp))
  :returns (ans (equal ans (aig-scons b v))
                :hints(("Goal" :in-theory (enable gl::bfr-scons))))
  :inline t
  (if (atom v)
      (if b
          (cons-with-hint b
                          (let ((ans '(nil)))
                            (mbe :logic ans
                                 :exec (if (equal ans (cdr hint)) (cdr hint) ans)))
                          hint)
        (let ((ans '(nil)))
          (mbe :logic ans
               :exec (if (equal hint ans) hint ans))))
    (if (and (atom (cdr v))
             (hons-equal (car v) b))
        (llist-fix v)
      (cons-with-hint b (llist-fix v) hint))))

(define aig-sterm-with-hint (b hint)
  :returns (ans (equal ans (aig-sterm b))
                :hints(("Goal" :in-theory (enable gl::bfr-sterm))))
  :inline t
  (cons-with-hint b nil hint))


(define a4vec-mask ((mask 4vmask-p)
                    (x a4vec-p))
  :short "Symbolic version of @(see 4vec-mask)."
  :returns (masked-a4vec a4vec-p)
  ;; We need to set any irrelevant bits to X (upper=1, lower=0).
  (b* (((a4vec x))
       (mask     (4vmask-fix mask))
       ((when (and (a4vec-mask-check mask 0 x.upper t)
                   (a4vec-mask-check mask 0 x.lower nil)))
        (a4vec-fix x))
       (dontcare (sparseint-val (sparseint-bitnot mask)))
       (dc-aigs  (aig-i2v dontcare))
       (ans (a4vec (aig-logior-ss dc-aigs x.upper)
                   (aig-logandc1-ss dc-aigs x.lower)))
       ;; (- (if (equal ans x)
       ;;        (acl2::sneaky-incf 'same 1)
       ;;      (acl2::sneaky-incf 'diff 1)))
       )
    ans)
  ///
  (defthm a4vec-mask-correct
    (equal (a4vec-eval (a4vec-mask mask x) env)
           (4vec-mask mask (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 4vec-mask a4vec-mask-check-correct)))))

(define a4vec-uminus ((x a4vec-p))
  :short "Symbolic version of @(see 4vec-uminus)."
  :returns (res a4vec-p)
  (a4vec-ite (a2vec-p x)
             ;; The input is properly two-valued, so we can negate it.
             (b* (((a4vec x))
                  (res (aig-+-ss t nil (aig-lognot-s x.upper))))
               (a4vec res res))
             ;; Some X/Z bit somewhere, so just return all Xes.
             (a4vec-x))
  ///
  (defthm a4vec-uminus-correct
    (equal (a4vec-eval (a4vec-uminus x) env)
           (4vec-uminus (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 4vec-uminus lognot)))))


(define a4vec-minus ((x a4vec-p) (y a4vec-p))
  :short "Symbolic version of @(see 4vec-minus)."
  :returns (res a4vec-p)
  (a4vec-ite (aig-and (a2vec-p x) (a2vec-p y))
             ;; Both inputs are properly two-valued, so we can do the subtract:
             (b* (((a4vec x))
                  ((a4vec y))
                  (res (aig-+-ss t x.upper (aig-lognot-s y.upper))))
               (a4vec res res))
             ;; Some X/Z bit somewhere, so just return all Xes.
             (a4vec-x))
  ///
  (defthm a4vec-minus-correct
    (equal (a4vec-eval (a4vec-minus x y) env)
           (4vec-minus (a4vec-eval x env)
                       (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 4vec-minus lognot)))))


(define a4vec-plus ((x a4vec-p) (y a4vec-p))
  :short "Symbolic version of @(see 4vec-plus)."
  :returns (res a4vec-p)
  (a4vec-ite (aig-and (a2vec-p x) (a2vec-p y))
             ;; Both inputs are properly two-valued, so we can do the sum:
             (b* (((a4vec x))
                  ((a4vec y))
                  (res (aig-+-ss nil x.upper y.upper)))
               (a4vec res res))
             ;; Some X/Z bit somewhere, so just return all Xes.
             (a4vec-x))
  ///
  (defthm a4vec-plus-correct
    (equal (a4vec-eval (a4vec-plus x y) env)
           (4vec-plus (a4vec-eval x env)
                      (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 4vec-plus)))))


(define a4vec-times ((x a4vec-p) (y a4vec-p))
  :short "Symbolic version of @(see 4vec-times)."
  :returns (res a4vec-p)
  (a4vec-ite (aig-and (a2vec-p x) (a2vec-p y))
             ;; Both inputs are properly two-valued, so we can do the multiply:
             (b* (((a4vec x))
                  ((a4vec y))
                  (res (aig-*-ss x.upper y.upper)))
               (a4vec res res))
             ;; Some X/Z bit somewhere, so just return all Xes.
             (a4vec-x))
  ///
  (defthm a4vec-times-correct
    (equal (a4vec-eval (a4vec-times x y) env)
           (4vec-times (a4vec-eval x env)
                       (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 4vec-times lognot)))))


(define a4vec-quotient ((x a4vec-p) (y a4vec-p))
  :short "Symbolic version of @(see 4vec-quotient)."
  :returns (res a4vec-p)
  (a4vec-ite (aig-and (a2vec-p x)  ;; Is X properly two-valued?
                      (a2vec-p y)  ;; Is Y properly two-valued?
                      (aig-not (aig-=-ss (a4vec->upper y) (aig-sterm nil))) ;; Is Y nonzero?
                      )
             ;; Good inputs, do the divide
             (b* (((a4vec x))
                  ((a4vec y))
                  (res (aig-truncate-ss x.upper y.upper)))
               (a4vec res res))
             ;; Some X/Z bit somewhere or divide by zero, so just return all Xes.
             (a4vec-x))
  ///
  (defthm a4vec-quotient-correct
    (equal (a4vec-eval (a4vec-quotient x y) env)
           (4vec-quotient (a4vec-eval x env)
                          (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 4vec-quotient lognot)))))


(define a4vec-remainder ((x a4vec-p) (y a4vec-p))
  :short "Symbolic version of @(see 4vec-remainder)."
  :returns (res a4vec-p)
  (a4vec-ite (aig-and (a2vec-p x) ;; Is X properly two-valued?
                      (a2vec-p y) ;; Is Y properly two-valued?
                      (aig-not (aig-=-ss (a4vec->upper y) (aig-sterm nil))) ;; Is Y nonzero?
                      )
             ;; Good inputs, do the remainder.
             (b* (((a4vec x))
                  ((a4vec y))
                  (res (aig-rem-ss x.upper y.upper)))
               (a4vec res res))
             ;; Some X/Z bit somewhere or divide by zero, so just return all Xes.
             (a4vec-x))
  ///
  (defthm a4vec-remainder-correct
    (equal (a4vec-eval (a4vec-remainder x y) env)
           (4vec-remainder (a4vec-eval x env)
                           (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 4vec-remainder lognot)))))


(define a4vec-< ((x a4vec-p) (y a4vec-p))
  :short "Symbolic version of @(see 4vec-<)."
  :returns (res a4vec-p)
  (a4vec-ite (aig-and (a2vec-p x) (a2vec-p y))
             ;; Both inputs are properly two-valued, so we can do the comparison
             (b* (((a4vec x))
                  ((a4vec y))
                  (res (aig-sterm (aig-<-ss x.upper y.upper))))
               (a4vec res res))
             ;; Some X/Z bit somewhere, so just return all Xes.
             (a4vec-x))
  ///
  (defthm a4vec-<-correct
    (equal (a4vec-eval (a4vec-< x y) env)
           (4vec-< (a4vec-eval x env)
                   (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 4vec-< lognot)))))


(define a4vec-clog2 ((x a4vec-p))
  :short "Symbolic version of @(see 4vec-clog2)."
  :returns (res a4vec-p)
  (b* (((a4vec x)))
    (a4vec-ite (aig-and (a2vec-p x)                    ;; Is X properly two-valued?
                        (aig-not (aig-sign-s x.upper)) ;; Is X positive?
                        )
               ;; Proper input, compute ceiling log2.
               (b* ((res (aig-integer-length-s (aig-+-ss nil '(t) x.upper))))
                 (a4vec res res))
               ;; Some X/Z bit somewhere or negative, so just return all Xes.
               (a4vec-x)))
  ///
  (defthm a4vec-clog2-correct
    (equal (a4vec-eval (a4vec-clog2 x) env)
           (4vec-clog2 (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 4vec-clog2)))))


(define a4vec-pow ((base a4vec-p)
                   (exp a4vec-p))
  :short "Symbolic version of @(see 4vec-pow)."
  :returns (res a4vec-p)
  (a4vec-ite (aig-and (a2vec-p base)
                      (a2vec-p exp))
             (b* ((base (a4vec->lower base))
                  (exp  (a4vec->lower exp)))
               (a4vec-ite (aig-or (aig-not (aig-<-ss exp nil))     ;; exp >= 0
                                  (aig-or (aig-=-ss base '(t nil)) ;; base == 1
                                          (aig-=-ss base '(t))))   ;; base == -1
                          (b* ((pow (aig-expt-su base exp)))
                            (a4vec pow pow))
                          (a4vec-ite (aig-=-ss base nil)
                                     (a4vec-x)
                                     (a4vec nil nil))))
             (a4vec-x))
  ///
  (local (defthm expt-b-0
           (equal (expt b 0) 1)
           :hints(("Goal" :in-theory (enable expt)))))

  (local (defthm expt-neg1-n
           (equal (expt -1 n)
                  (- 1 (* 2 (logcar n))))
           :hints(("Goal" :in-theory (enable expt)))))

  (local (defthm logcar-of-aig-list->s
           (equal (logcar (aig-list->s x env))
                  (bool->bit (aig-eval (car x) env)))
           :hints(("Goal" :in-theory (enable aig-list->s)))))

  (local (defthm logcar-of-aig-list->u
           (equal (logcar (aig-list->u x env))
                  (bool->bit (aig-eval (car x) env)))
           :hints(("Goal" :in-theory (enable aig-list->u)))))

  (defthm a4vec-pow-correct
    (equal (a4vec-eval (a4vec-pow base exp) env)
           (4vec-pow (a4vec-eval base env)
                     (a4vec-eval exp env)))
    :hints(("Goal" :in-theory (enable 4vec-pow)))))
                  


(define a3vec-== ((x a4vec-p) (y a4vec-p))
  :short "Symbolic version of @(see 3vec-==)."
  :returns (res a4vec-p)
  ;; Could probably do this in one pass and lazily
  (a3vec-reduction-and (a3vec-bitnot (a3vec-bitxor x y)))
  ///
  (defthm a3vec-==-correct
    (equal (a4vec-eval (a3vec-== x y) env)
           (3vec-== (a4vec-eval x env)
                    (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 4vec-== 3vec-==)))))


(define a4vec-=== ((x a4vec-p) (y a4vec-p))
  :short "Symbolic version of @(see 4vec-===)."
  :returns (res a4vec-p)
  (b* (((a4vec x))
       ((a4vec y))
       ;; The laziness of aig-and means that this is as lazy as possible.
       (val (aig-sterm (aig-and (aig-=-ss x.upper y.upper)
                                (aig-=-ss x.lower y.lower)))))
    (a4vec val val))
  ///
  (defthm a4vec-===-correct
    (equal (a4vec-eval (a4vec-=== x y) env)
           (4vec-=== (a4vec-eval x env)
                     (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 4vec-=== bool->vec)))))


(define and4 (a b c d)
  (and a b c d)
  ///
  (defthm and4-forward
    (implies (and4 a b c d)
             (and a b c d))
    :rule-classes :forward-chaining))



(define a4vec-wildeq-safe-bit ((au "aig")
                          (al)
                          (bu)
                          (bl))
  :returns (mv (wildeq-safe-p-upper "aig")
               (wildeq-safe-p-lower "aig"))
  (b* ((bz (aig-and (aig-not bu) bl))
       ((when (eq bz t))
        ;; If B is definitely Z then we return true.
        (mv t t))
       (bx (aig-and bu (aig-not bl)))
       ((when (eq bx t))
        ;; If B is definitely X, then we return X (and that means B is not Z,
        ;; so we don't need to consider that.)
        (mv t nil))
       (axz (aig-xor au al))
       ((when (eq axz t))
        ;; If A is definitely X or Z:
        ;;  if B is Z, then we still return true
        ;;  otherwise we return X.
        (mv t bz))
       (a=b (aig-iff au bu)))
    (mv (aig-or
         ;; We're taking care of the cases where A or B are X or Z
         ;; elsewhere, so it suffices to just compare the uppers.
         a=b

         (aig-or bz  ;; Ans is T, so upper set.
                 bx  ;; Ans it X, so upper set
                 )
         axz ;; Ans is X, so upper set
         )
        (aig-or
         (aig-and
          ;; We're taking care of the cases where A or B are X or Z
          ;; elsewhere, so it suffices to just compare the uppers.
          a=b
          (aig-not bx)  ;; Don't set lower if Ans X.
          (aig-not axz) ;; Don't set lower if Ans X.
          )
         bz ;; Ans is T, so lower set
         )))
  ///
  (defthmd a4vec-wildeq-safe-bit-eval
    (b* (((mv upper lower) (a4vec-wildeq-safe-bit a.upper a.lower b.upper b.lower)))
      (and (equal (aig-eval upper env)
                  (or (iff (aig-eval a.upper env)
                           (aig-eval b.upper env))
                      (and (not (aig-eval b.upper env))
                           (aig-eval b.lower env))
                      (and (aig-eval b.upper env)
                           (not (aig-eval b.lower env)))
                      (xor (aig-eval a.upper env)
                           (aig-eval a.lower env))))
           (equal (aig-eval lower env)
                  (or (and (iff (aig-eval a.upper env)
                                (aig-eval b.upper env))
                           (not (and (aig-eval b.upper env)
                                     (not (aig-eval b.lower env))))
                           (iff (aig-eval a.upper env)
                                (aig-eval a.lower env)))
                      (and (not (aig-eval b.upper env))
                           (aig-eval b.lower env))))))
    :hints ((and stable-under-simplificationp
                 '(:use ((:instance acl2::aig-eval-and
                           (x (aig-not b.upper))
                           (y b.lower) (env env))
                         (:instance acl2::aig-eval-and
                           (x b.upper)
                           (y (aig-not b.lower)) (env env))
                         (:instance acl2::aig-eval-xor
                          (x a.upper) (y a.lower) (env env)))
                   :in-theory (disable acl2::aig-eval-and
                                       acl2::aig-eval-xor))))))


(define a4vec-wildeq-safe-aux ((a.upper true-listp "aig list")
                               (a.lower true-listp "aig list")
                               (b.upper true-listp "aig list")
                               (b.lower true-listp "aig list"))
  :measure (+ (len b.upper) (len b.lower) (len a.upper) (len a.lower))
  :returns (mv (wildeq-safe-p-upper "aig")
               (wildeq-safe-p-lower "aig"))
  :hints(("Goal" :in-theory (enable and4)))
  :guard-hints (("goal" :in-theory (enable and4)))
  (b* (((mv buf bur buend) (gl::first/rest/end b.upper))
       ((mv blf blr blend) (gl::first/rest/end b.lower))
       ;; ((when (and buend blend (eq buf nil) (eq blf t)))
       ;;  ;; Ends in Zs out to infinity.
       ;;  (mv t t))
       ((mv auf aur auend) (gl::first/rest/end a.upper))
       ((mv alf alr alend) (gl::first/rest/end a.lower))

       ((mv upper1 lower1) (a4vec-wildeq-safe-bit auf alf buf blf))
       ((when (mbe :logic (and4 buend blend auend alend)
                   :exec (and buend blend auend alend)))
        (mv upper1 lower1)))
    (mbe :logic
         (b* (((mv upper-rest lower-rest)
               (a4vec-wildeq-safe-aux aur alr bur blr)))
           (mv (aig-and upper1 upper-rest)
               (aig-and lower1 lower-rest)))
         :exec
         (b* (((when (and (eq upper1 nil) (eq lower1 nil)))
               ;; short circuit
               (mv nil nil))
              ((mv upper-rest lower-rest)
               (a4vec-wildeq-safe-aux aur alr bur blr)))
           (mv (aig-and upper1 upper-rest)
               (aig-and lower1 lower-rest)))))

  ///
  ;; (local (defthm 4vec-wildeq-safe-expand
  ;;          (equal (4vec-wildeq-safe (4vec (aig-list->s a.upper env)
  ;;                                    (aig-list->s a.lower env))
  ;;                              (4vec (aig-list->s b.upper env)
  ;;                                    (aig-list->s b.lower env)))
  ;;                 (

  (local (defthm aig-list->s-when-endp
           (implies (gl::s-endp x)
                    (equal (aig-list->s x env)
                           (bool->vec (aig-eval (car x) env))))
           :hints(("Goal" :in-theory (enable aig-list->s)))))

  (local (defthm s-endp-when-singleton
           (gl::s-endp (list x))
           :hints(("Goal" :in-theory (enable gl::s-endp)))))

  (local (defthm a4vec-wildeq-safe-bit-correct
           (b* (((mv upper lower) (a4vec-wildeq-safe-bit a b c d)))
             (and (iff (aig-eval upper env)
                       (equal -1 (4vec->upper
                                  (4vec-wildeq-safe (4vec (bool->vec (aig-eval a env))
                                                          (bool->vec (aig-eval b env)))
                                                    (4vec (bool->vec (aig-eval c env))
                                                          (bool->vec (aig-eval d env)))))))
                  (iff (aig-eval lower env)
                       (equal -1 (4vec->lower
                                  (4vec-wildeq-safe (4vec (bool->vec (aig-eval a env))
                                                          (bool->vec (aig-eval b env)))
                                                    (4vec (bool->vec (aig-eval c env))
                                                          (bool->vec (aig-eval d env)))))))))
           :hints(("Goal" :in-theory (e/d (4vec-wildeq-safe
                                           4vec-bitxor 3vec-bitnot
                                           3vec-bitor 3vec-reduction-and
                                           a4vec-wildeq-safe-bit-eval bool->vec)
                                          (not xor iff))))))




  (local (defthmd 4vec-wildeq-safe-expand
           (equal (4vec-wildeq-safe (4vec a b) (4vec c d))
                  (4vec (bool->vec
                         (and (equal -1 (4vec->upper (4vec-wildeq-safe (4vec (bool->vec (logbitp 0 a))
                                                                             (bool->vec (logbitp 0 b)))
                                                                       (4vec (bool->vec (logbitp 0 c))
                                                                             (bool->vec (logbitp 0 d))))))
                              (equal -1 (4vec->upper (4vec-wildeq-safe (4vec (logcdr a)
                                                                             (logcdr b))
                                                                       (4vec (logcdr c)
                                                                             (logcdr d)))))))
                        (bool->vec
                         (and (equal -1 (4vec->lower (4vec-wildeq-safe (4vec (bool->vec (logbitp 0 a))
                                                                             (bool->vec (logbitp 0 b)))
                                                                       (4vec (bool->vec (logbitp 0 c))
                                                                             (bool->vec (logbitp 0 d))))))
                              (equal -1 (4vec->lower (4vec-wildeq-safe (4vec (logcdr a)
                                                                             (logcdr b))
                                                                       (4vec (logcdr c)
                                                                             (logcdr d)))))))))
           :hints(("Goal" :in-theory (enable 4vec-wildeq-safe 3vec-bitnot 4vec-bitxor
                                             3vec-bitor 3vec-reduction-and bool->vec
                                             bitops::logand**
                                             bitops::logxor**
                                             bitops::logior**
                                             bitops::lognot**
                                             bitops::logbitp**)))))

  (local (defthm logbitp-0-of-aig-list->s
           (equal (logbitp 0 (aig-list->s x env))
                  (aig-eval (car x) env))
           :hints(("Goal" :in-theory (enable aig-list->s)))))

  (local (defthm logcdr-of-aig-list->s
           (equal (logcdr (aig-list->s x env))
                  (aig-list->s (gl::scdr x) env))
           :hints(("Goal" :in-theory (enable aig-list->s)))))

  (local (defcong iff equal (bool->vec x) 1))

  (local (defthm bool->vec-equal-neg-1
           (iff (equal -1 (bool->vec a))
                a)))

  (defthm a4vec-wildeq-safe-aux-correct
    (b* (((mv ans.upper ans.lower) (a4vec-wildeq-safe-aux a.upper a.lower b.upper b.lower)))
      (equal (a4vec-eval (a4vec (list ans.upper) (list ans.lower)) env)
             (4vec-wildeq-safe (4vec (aig-list->s a.upper env)
                                     (aig-list->s a.lower env))
                               (4vec (aig-list->s b.upper env)
                                     (aig-list->s b.lower env)))))
    :hints (("Goal" :induct (a4vec-wildeq-safe-aux a.upper a.lower b.upper b.lower)
             :do-not '(generalize fertilize eliminate-destructors))
            (and stable-under-simplificationp
                 '(:use ((:instance 4vec-wildeq-safe-expand
                          (a (aig-list->s a.upper env))
                          (b (aig-list->s a.lower env))
                          (c (aig-list->s b.upper env))
                          (d (aig-list->s b.lower env)))))))))


(define a4vec-wildeq-safe ((a a4vec-p) (b a4vec-p))
  :short "Symbolic version of @(see 4vec-wildeq-safe)."
  :returns (res a4vec-p)
  ;; BOZO we could probably benefit from a fused version of this that could
  ;; better exploit laziness.
  (b* (((a4vec a))
       ((a4vec b))
       ((mv ans.upper ans.lower)
        (a4vec-wildeq-safe-aux a.upper a.lower b.upper b.lower)))
    (a4vec (list ans.upper) (list ans.lower)))
  ///
  (defthm a4vec-wildeq-safe-correct
    (equal (a4vec-eval (a4vec-wildeq-safe a b) env)
           (4vec-wildeq-safe (a4vec-eval a env)
                        (a4vec-eval b env)))
    :hints(("Goal" :in-theory (enable 4vec-wildeq-safe 4vec-bitxor-redef 2vec)))))



(define a4vec-wildeq-bit ((au "aig")
                          (al)
                          (bu)
                          (bl))
  :returns (mv (wildeq-p-upper "aig")
               (wildeq-p-lower "aig"))
  (b* ((bxz (aig-xor bl bu))
       ((when (eq bxz t))
        ;; If B is definitely X or Z then we return true.
        (mv t t))
       (axz (aig-xor au al))
       ((when (eq axz t))
        ;; If A is definitely X or Z:
        ;;  if B is X or Z, then we still return true
        ;;  otherwise we return X.
        (mv t bxz))
       (a=b (aig-iff au bu)))
    (mv (aig-or
         ;; We're taking care of the cases where A or B are X or Z
         ;; elsewhere, so it suffices to just compare the uppers.
         a=b

         bxz ;; Ans is T, so upper set.
         axz ;; Ans is X, so upper set
         )
        (aig-or
         ;; Lower is true iff answer is 1, which is the case if B is x or z, or if a=b.
         bxz
         (aig-and a=b
                  (aig-not axz)))))
  ///
  (defthmd a4vec-wildeq-bit-eval
    (b* (((mv ?upper ?lower) (a4vec-wildeq-bit a.upper a.lower b.upper b.lower)))
      (and (equal (aig-eval upper env)
                  (or (iff (aig-eval a.upper env)
                           (aig-eval b.upper env))
                      (xor (aig-eval b.upper env)
                           (aig-eval b.lower env))
                      (xor (aig-eval a.upper env)
                           (aig-eval a.lower env))))
           (equal (aig-eval lower env)
                  (or (xor (aig-eval b.upper env)
                           (aig-eval b.lower env))
                      (and (iff (aig-eval a.upper env)
                                (aig-eval b.upper env))
                           (iff (aig-eval a.lower env)
                                (aig-eval b.lower env)))))
           ))
    :hints ((and stable-under-simplificationp
                 '(:use ((:instance acl2::aig-eval-xor
                           (x b.lower)
                           (y b.upper) (env env))
                         (:instance acl2::aig-eval-xor
                          (x a.upper) (y a.lower) (env env)))
                   :in-theory (disable ;; acl2::aig-eval-and
                                       acl2::aig-eval-xor))))))


(define a4vec-wildeq-aux ((a.upper true-listp "aig list")
                          (a.lower true-listp "aig list")
                          (b.upper true-listp "aig list")
                          (b.lower true-listp "aig list"))
  :measure (+ (len b.upper) (len b.lower) (len a.upper) (len a.lower))
  :returns (mv (wildeq-p-upper "aig")
               (wildeq-p-lower "aig"))
  :hints(("Goal" :in-theory (enable and4)))
  :guard-hints (("goal" :in-theory (enable and4)))
  (b* (((mv buf bur buend) (gl::first/rest/end b.upper))
       ((mv blf blr blend) (gl::first/rest/end b.lower))
       ;; ((when (and buend blend (eq buf nil) (eq blf t)))
       ;;  ;; Ends in Zs out to infinity.
       ;;  (mv t t))
       ((mv auf aur auend) (gl::first/rest/end a.upper))
       ((mv alf alr alend) (gl::first/rest/end a.lower))

       ((mv upper1 lower1) (a4vec-wildeq-bit auf alf buf blf))
       ((when (mbe :logic (and4 buend blend auend alend)
                   :exec (and buend blend auend alend)))
        (mv upper1 lower1)))
    (mbe :logic
         (b* (((mv upper-rest lower-rest)
               (a4vec-wildeq-aux aur alr bur blr)))
           (mv (aig-and upper1 upper-rest)
               (aig-and lower1 lower-rest)))
         :exec
         (b* (((when (and (eq upper1 nil) (eq lower1 nil)))
               ;; short circuit
               (mv nil nil))
              ((mv upper-rest lower-rest)
               (a4vec-wildeq-aux aur alr bur blr)))
           (mv (aig-and upper1 upper-rest)
               (aig-and lower1 lower-rest)))))

  ///
  ;; (local (defthm 4vec-wildeq-expand
  ;;          (equal (4vec-wildeq (4vec (aig-list->s a.upper env)
  ;;                                    (aig-list->s a.lower env))
  ;;                              (4vec (aig-list->s b.upper env)
  ;;                                    (aig-list->s b.lower env)))
  ;;                 (

  (local (defthm aig-list->s-when-endp
           (implies (gl::s-endp x)
                    (equal (aig-list->s x env)
                           (bool->vec (aig-eval (car x) env))))
           :hints(("Goal" :in-theory (enable aig-list->s)))))

  (local (defthm s-endp-when-singleton
           (gl::s-endp (list x))
           :hints(("Goal" :in-theory (enable gl::s-endp)))))

  (local (defthm a4vec-wildeq-bit-correct
           (b* (((mv upper lower) (a4vec-wildeq-bit a b c d)))
             (and (iff (aig-eval upper env)
                       (equal -1 (4vec->upper
                                  (4vec-wildeq (4vec (bool->vec (aig-eval a env))
                                                     (bool->vec (aig-eval b env)))
                                               (4vec (bool->vec (aig-eval c env))
                                                     (bool->vec (aig-eval d env)))))))
                  (iff (aig-eval lower env)
                       (equal -1 (4vec->lower
                                  (4vec-wildeq (4vec (bool->vec (aig-eval a env))
                                                     (bool->vec (aig-eval b env)))
                                               (4vec (bool->vec (aig-eval c env))
                                                     (bool->vec (aig-eval d env)))))))))
           :hints(("Goal" :in-theory (e/d (4vec-wildeq
                                           4vec-bitxor 3vec-bitnot
                                           3vec-bitor 3vec-reduction-and
                                           a4vec-wildeq-bit-eval bool->vec)
                                          (not xor iff))))))




  (local (defthmd 4vec-wildeq-expand
           (equal (4vec-wildeq (4vec a b) (4vec c d))
                  (4vec (bool->vec
                         (and (equal -1 (4vec->upper (4vec-wildeq (4vec (bool->vec (logbitp 0 a))
                                                                        (bool->vec (logbitp 0 b)))
                                                                  (4vec (bool->vec (logbitp 0 c))
                                                                        (bool->vec (logbitp 0 d))))))
                              (equal -1 (4vec->upper (4vec-wildeq (4vec (logcdr a)
                                                                        (logcdr b))
                                                                  (4vec (logcdr c)
                                                                        (logcdr d)))))))
                        (bool->vec
                         (and (equal -1 (4vec->lower (4vec-wildeq (4vec (bool->vec (logbitp 0 a))
                                                                        (bool->vec (logbitp 0 b)))
                                                                  (4vec (bool->vec (logbitp 0 c))
                                                                        (bool->vec (logbitp 0 d))))))
                              (equal -1 (4vec->lower (4vec-wildeq (4vec (logcdr a)
                                                                        (logcdr b))
                                                                  (4vec (logcdr c)
                                                                        (logcdr d)))))))))
           :hints(("Goal" :in-theory (enable 4vec-wildeq 3vec-bitnot 4vec-bitxor
                                             3vec-bitor 3vec-reduction-and bool->vec
                                             bitops::logand**
                                             bitops::logxor**
                                             bitops::logior**
                                             bitops::lognot**
                                             bitops::logbitp**)))))

  (local (defthm logbitp-0-of-aig-list->s
           (equal (logbitp 0 (aig-list->s x env))
                  (aig-eval (car x) env))
           :hints(("Goal" :in-theory (enable aig-list->s)))))

  (local (defthm logcdr-of-aig-list->s
           (equal (logcdr (aig-list->s x env))
                  (aig-list->s (gl::scdr x) env))
           :hints(("Goal" :in-theory (enable aig-list->s)))))

  (local (defcong iff equal (bool->vec x) 1))

  (local (defthm bool->vec-equal-neg-1
           (iff (equal -1 (bool->vec a))
                a)))

  (defthm a4vec-wildeq-aux-correct
    (b* (((mv ans.upper ans.lower) (a4vec-wildeq-aux a.upper a.lower b.upper b.lower)))
      (equal (a4vec-eval (a4vec (list ans.upper) (list ans.lower)) env)
             (4vec-wildeq (4vec (aig-list->s a.upper env)
                                (aig-list->s a.lower env))
                          (4vec (aig-list->s b.upper env)
                                (aig-list->s b.lower env)))))
    :hints (("Goal" :induct (a4vec-wildeq-aux a.upper a.lower b.upper b.lower)
             :do-not '(generalize fertilize eliminate-destructors))
            (and stable-under-simplificationp
                 '(:use ((:instance 4vec-wildeq-expand
                          (a (aig-list->s a.upper env))
                          (b (aig-list->s a.lower env))
                          (c (aig-list->s b.upper env))
                          (d (aig-list->s b.lower env)))))))))


(define a4vec-wildeq ((a a4vec-p) (b a4vec-p))
  :short "Symbolic version of @(see 4vec-wildeq)."
  :returns (res a4vec-p)
  ;; BOZO we could probably benefit from a fused version of this that could
  ;; better exploit laziness.
  (b* (((a4vec a))
       ((a4vec b))
       ((mv ans.upper ans.lower)
        (a4vec-wildeq-aux a.upper a.lower b.upper b.lower)))
    (a4vec (list ans.upper) (list ans.lower)))
  ///
  (defthm a4vec-wildeq-correct
    (equal (a4vec-eval (a4vec-wildeq a b) env)
           (4vec-wildeq (a4vec-eval a env)
                        (a4vec-eval b env)))
    :hints(("Goal" :in-theory (enable 4vec-wildeq 4vec-bitxor-redef 2vec)))))




(define a4vec-symwildeq ((a a4vec-p) (b a4vec-p))
  :short "Symbolic version of @(see 4vec-symwildeq)."
  :returns (res a4vec-p)
  ;; BOZO we could probably benefit from a fused version of this that could
  ;; better exploit laziness.
  (b* (((a4vec a))
       ((a4vec b))
       (eq (a3vec-bitnot (a3vec-bitxor (a3vec-fix a) (a3vec-fix b))))
       (zmask (aig-logior-ss (aig-logandc1-ss b.upper b.lower)
                             (aig-logandc1-ss a.upper a.lower))))
    (a3vec-reduction-and (a3vec-bitor eq (a4vec zmask zmask))))
  ///
  (defthm a4vec-symwildeq-correct
    (equal (a4vec-eval (a4vec-symwildeq a b) env)
           (4vec-symwildeq (a4vec-eval a env)
                           (a4vec-eval b env)))
    :hints(("Goal" :in-theory (enable 4vec-symwildeq 4vec-bitxor-redef 2vec)))))


(define aig-parity-s ((x true-listp))
  :parents (a4vec-parity)
  (b* (((mv xf xr xe) (gl::first/rest/end x)))
    (if xe
        nil
      (aig-xor xf (aig-parity-s xr))))
  ///
  (local (defthm logxor-of-bits
           (implies (and (bitp a) (bitp b))
                    (equal (logxor a b)
                           (bitops::b-xor a b)))))

  (defthm aig-parity-s-correct
    (let ((xv (aig-list->s x env)))
      (implies (<= 0 xv)
               (equal (aig-eval (aig-parity-s x) env)
                      (bitops::bit->bool (parity (+ 1 (integer-length xv)) xv)))))
    :hints(("Goal" :in-theory (enable parity
                                      bitops::loghead** bitops::logtail**)
            :induct (aig-parity-s x)
            :expand ((aig-list->s x env)
                     (:free (n x) (parity (+ 2 n) x))
                     (:free (a b) (integer-length (bitops::logcons a b))))))))

(define a4vec-parity ((x a4vec-p))
  :short "Symbolic version of @(see 4vec-parity)."
  :returns (res a4vec-p)
  (b* (((a4vec x)))
    (a4vec-ite (aig-and (a2vec-p x)                    ;; Is X properly two-valued?
                        (aig-not (aig-sign-s x.upper)) ;; Is it non-negative?
                        )
               ;; Legitimate input, compute the parity
               (let* ((bit (aig-parity-s x.upper))
                      (vec (aig-sterm bit)))
                 (a4vec vec vec))
               ;; Bad input, just return all Xes.
               (a4vec-x)))
  ///
  (defthm a4vec-parity-correct
    (equal (a4vec-eval (a4vec-parity x) env)
           (4vec-parity (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 4vec-parity bool->vec)))))

(define aig-iszero-s ((a true-listp))
  :short "Determines whether a signed vector of AIGs is equal to 0."
  :returns (res "aig")
  (b* (((mv first rest end) (gl::first/rest/end a))
       ((when end) (aig-not first)))
    (aig-and (aig-not first)
             (aig-iszero-s rest)))
  ///
  (defthm aig-iszero-s-correct
    (equal (aig-eval (aig-iszero-s a) env)
           (equal (aig-list->s a env) 0))
    :hints(("Goal" :in-theory (enable aig-list->s)))))


(define a3vec-? ((x a4vec-p)
                 (y a4vec-p)
                 y3p
                 (z a4vec-p)
                 z3p)
  :short "Symbolic version of @(see 3vec-?)."
  :returns (res a4vec-p)

  ;; ~test.upper --> false
  ;; test.lower --> true
  ;; otherwise x.
  ;;
  ;; ans upper:
  ;; ( ( testfalse & elses.upper)       ;; test is false --> else
  ;;   | ( testtrue & thens.upper) )    ;; test is true --> then
  ;; | ( (~testfalse & ~testtrue)
  ;;      & (elses.upper | thens.upper | elses.lower | thens.lower)
  ;;      )
  ;;
  ;; ans lower:
  ;; ( testfalse & elses.lower)       ;; test is false --> else
  ;;   | ( testtrue & thens.lower)    ;; test is true --> then
  ;;   | ( (~testfalse & ~testtrue)
  ;;        & elses.upper & thens.upper & elses.lower & thens.lower )


  (b* (((a4vec a) x)
       ((a4vec b) y)
       ((a4vec c) z)
       ;; common subexpressions between the two
       (a=1 (aig-not (aig-iszero-s a.lower)))
       (a=0 (aig-iszero-s a.upper))
       (a=x (aig-nor a=1 a=0))

       ;; upper
       (boolcase (aig-logior-ss (aig-ite-bss-fn a=1 b.upper nil)
                                (aig-ite-bss-fn a=0 c.upper nil)))
       (upper (aig-logior-ss
               boolcase
               (aig-ite-bss a=x
                            (aig-logior-ss (if z3p
                                               c.upper ;; implied by c.lower
                                             (aig-logior-ss c.upper c.lower))
                                           (if y3p
                                               b.upper ;; implied by b.lower
                                             (aig-logior-ss b.upper b.lower)))
                            nil)))

       ;; lower
       (boolcase (aig-logior-ss (aig-ite-bss-fn a=1 b.lower nil)
                                (aig-ite-bss-fn a=0 c.lower nil)))
       (lower (aig-logior-ss
               boolcase
               (aig-ite-bss a=x
                            (aig-logand-ss (if z3p
                                               c.lower ;; implies c.upper
                                             (aig-logand-ss c.upper c.lower))
                                           (if y3p
                                               b.lower ;; implies b.upper
                                             (aig-logand-ss b.upper b.lower)))
                            nil))))
    (a4vec upper lower))
  ///
  (local (in-theory (disable iff not acl2::zip-open)))
  (local (in-theory (disable bitops::logand-natp-type-2
                             bitops::logand-natp-type-1
                             bitops::logior-natp-type
                             bitops::logand->=-0-linear-2
                             bitops::logand->=-0-linear-1
                             bitops::upper-bound-of-logand
                             aig-list->s
                             bitops::logbitp-when-bit
                             bitops::logbitp-nonzero-of-bit
                             bitops::logbitp-when-bitmaskp
                             bitops::lognot-negp
                             bitops::lognot-natp
                             bitops::logior-<-0-linear-2
                             bitops::logior-<-0-linear-1
                             bitops::lognot-<-const
                             acl2::aig-env-lookup)))


  (defthm a3vec-?-correct
    (implies (and (case-split (implies y3p (3vec-p (a4vec-eval y env))))
                  (case-split (implies z3p (3vec-p (a4vec-eval z env))))
                  (3vec-p (a4vec-eval x env)))
             (equal (a4vec-eval (a3vec-? x y y3p z z3p) env)
                    (3vec-? (a4vec-eval x env)
                            (a4vec-eval y env)
                            (a4vec-eval z env))))
    :hints(("Goal" :in-theory (enable 3vec-? 3vec-p))
           (bitops::logbitp-reasoning))))

(define a3vec-?* ((x a4vec-p)
                 (y a4vec-p)
                 y3p
                 (z a4vec-p)
                 z3p)
  :short "Symbolic version of @(see 3vec-?*)."
  :returns (res a4vec-p)

  ;; ~test.upper --> false
  ;; test.lower --> true
  ;; otherwise x.
  ;;
  ;; ans upper:
  ;; ( ( testfalse & elses.upper)       ;; test is false --> else
  ;;   | ( testtrue & thens.upper) )    ;; test is true --> then
  ;; | ( (~testfalse & ~testtrue)
  ;;      & (elses.upper | thens.upper | elses.lower | thens.lower)
  ;;      )
  ;;
  ;; ans lower:
  ;; ( testfalse & elses.lower)       ;; test is false --> else
  ;;   | ( testtrue & thens.lower)    ;; test is true --> then
  ;;   | ( (~testfalse & ~testtrue)
  ;;        & elses.upper & thens.upper & elses.lower & thens.lower )


  (b* (((a4vec a) x)
       ((a4vec b) y)
       ((a4vec c) z)
       ;; common subexpressions between the two
       (a=1 (aig-not (aig-iszero-s a.lower)))
       (a=0 (aig-iszero-s a.upper))
       (a=x (aig-nor a=1 a=0))

       ;; upper
       (boolcase (aig-logior-ss (aig-ite-bss-fn a=1 b.upper nil)
                                (aig-ite-bss-fn a=0 c.upper nil)))
       (upper (aig-logior-ss
               boolcase
               (aig-ite-bss a=x
                            (aig-logior-ss (aig-logior-ss b.upper c.upper)
                                           (aig-logxor-ss
                                            (if y3p nil b.lower) ;; implied by not b.upper
                                            (if z3p nil c.lower)))
                            nil)))

       ;; lower
       (boolcase (aig-logior-ss (aig-ite-bss-fn a=1 b.lower nil)
                                (aig-ite-bss-fn a=0 c.lower nil)))
       (lower (aig-logior-ss
               boolcase
               (aig-ite-bss a=x
                            (aig-logand-ss (aig-logand-ss b.lower c.lower)
                                           (aig-lognot-s
                                            (aig-logxor-ss
                                             (if y3p '(t) b.upper)
                                             (if z3p '(t) c.upper))))
                            nil))))
    (a4vec upper lower))
  ///
  (local (in-theory (disable iff not acl2::zip-open)))
  (local (in-theory (disable bitops::logand-natp-type-2
                             bitops::logand-natp-type-1
                             bitops::logior-natp-type
                             bitops::logand->=-0-linear-2
                             bitops::logand->=-0-linear-1
                             bitops::upper-bound-of-logand
                             aig-list->s
                             bitops::logbitp-when-bit
                             bitops::logbitp-nonzero-of-bit
                             bitops::logbitp-when-bitmaskp
                             bitops::lognot-negp
                             bitops::lognot-natp
                             bitops::logior-<-0-linear-2
                             bitops::logior-<-0-linear-1
                             bitops::lognot-<-const
                             acl2::aig-env-lookup)))


  (defthm a3vec-?*-correct
    (implies (and (case-split (implies y3p (3vec-p (a4vec-eval y env))))
                  (case-split (implies z3p (3vec-p (a4vec-eval z env))))
                  (3vec-p (a4vec-eval x env)))
             (equal (a4vec-eval (a3vec-?* x y y3p z z3p) env)
                    (3vec-?* (a4vec-eval x env)
                            (a4vec-eval y env)
                            (a4vec-eval z env))))
    :hints(("Goal" :in-theory (enable 3vec-?* 3vec-p))
           (bitops::logbitp-reasoning)
           (and stable-under-simplificationp
                '(:bdd (:vars nil))))))



(define a4vec-?! ((x a4vec-p)
                 (y a4vec-p)
                 (z a4vec-p))
  :short "Symbolic version of @(see 3vec-?*)."
  :returns (res a4vec-p)


  (b* (((a4vec a) x)
       ((a4vec b) y)
       ((a4vec c) z)
       (pick-c (aig-iszero-s (aig-logand-ss a.upper a.lower)))

       (upper (aig-ite-bss pick-c c.upper b.upper))
       (lower (aig-ite-bss pick-c c.lower b.lower)))
    (a4vec upper lower))
  ///
  (local (in-theory (disable iff not acl2::zip-open)))
  (local (in-theory (disable bitops::logand-natp-type-2
                             bitops::logand-natp-type-1
                             bitops::logior-natp-type
                             bitops::logand->=-0-linear-2
                             bitops::logand->=-0-linear-1
                             bitops::upper-bound-of-logand
                             aig-list->s
                             bitops::logbitp-when-bit
                             bitops::logbitp-nonzero-of-bit
                             bitops::logbitp-when-bitmaskp
                             bitops::lognot-negp
                             bitops::lognot-natp
                             bitops::logior-<-0-linear-2
                             bitops::logior-<-0-linear-1
                             bitops::lognot-<-const
                             acl2::aig-env-lookup)))


  (defthm a4vec-?!-correct
    (equal (a4vec-eval (a4vec-?! x y z) env)
           (4vec-?! (a4vec-eval x env)
                    (a4vec-eval y env)
                    (a4vec-eval z env)))
    :hints(("Goal" :in-theory (enable 4vec-?!))
           (bitops::logbitp-reasoning))))

(define a3vec-bit? ((x a4vec-p)
                    (y a4vec-p)
                    y3p
                    (z a4vec-p)
                    z3p)
  :ignore-ok t :irrelevant-formals-ok t
  :short "Symbolic version of @(see a3vec-bit?)."
  :returns (res a4vec-p)
  (b* (((a4vec a) x)
       ((a4vec b) y)
       ((a4vec c) z)
       (a=x   (aig-logandc2-ss a.upper a.lower))
       ;; upper
       (boolcase (aig-logior-ss (aig-logand-ss a.lower b.upper)
                                (aig-logandc1-ss a.upper c.upper)))
       (xcase (aig-logior-ss (if z3p
                                 c.upper ;; implied by c.lower
                               (aig-logior-ss c.upper c.lower))
                             (if y3p
                                 b.upper ;; implied by b.lower
                               (aig-logior-ss b.upper b.lower))))
       (upper (aig-logior-ss boolcase
                             (aig-logand-ss a=x xcase)))

       ;; lower
       (boolcase (aig-logior-ss (aig-logand-ss a.lower b.lower)
                                (aig-logandc1-ss a.upper c.lower)))
       (xcase (aig-logand-ss (if z3p
                                 c.lower ;; implies c.upper
                               (aig-logand-ss c.upper c.lower))
                             (if y3p
                                 b.lower ;; implies b.upper
                               (aig-logand-ss b.upper b.lower))))
       (lower (aig-logior-ss boolcase
                             (aig-logand-ss a=x xcase))))
    (a4vec upper lower))
  ///
  (local (in-theory (disable iff not acl2::zip-open)))
  (local (in-theory (disable bitops::logand-natp-type-2
                             bitops::logand-natp-type-1
                             bitops::logior-natp-type
                             bitops::logand->=-0-linear-2
                             bitops::logand->=-0-linear-1
                             bitops::upper-bound-of-logand
                             aig-list->s
                             bitops::logbitp-when-bit
                             bitops::logbitp-nonzero-of-bit
                             bitops::logbitp-when-bitmaskp
                             bitops::lognot-negp
                             bitops::lognot-natp
                             bitops::logior-<-0-linear-2
                             bitops::logior-<-0-linear-1
                             bitops::lognot-<-const
                             acl2::aig-env-lookup)))
  (defthm a3vec-bit?-correct
    (implies (and (case-split (implies y3p (3vec-p (a4vec-eval y env))))
                  (case-split (implies z3p (3vec-p (a4vec-eval z env))))
                  (3vec-p (a4vec-eval x env)))
             (equal (a4vec-eval (a3vec-bit? x y y3p z z3p) env)
                    (3vec-bit? (a4vec-eval x env)
                               (a4vec-eval y env)
                               (a4vec-eval z env))))
    :hints(("Goal" :in-theory (enable 3vec-bit? 3vec-p))
           (bitops::logbitp-reasoning)
           (and stable-under-simplificationp
                '(:bdd (:vars nil))))))



(define a4vec-bit?! ((x a4vec-p)
                     (y a4vec-p)
                     y3p
                     (z a4vec-p)
                     z3p)
  :ignore-ok t :irrelevant-formals-ok t
  :short "Symbolic version of @(see a3vec-bit?)."
  :returns (res a4vec-p)
  (b* (((a4vec a) x)
       ((a4vec b) y)
       ((a4vec c) z)
       (a=1   (aig-logand-ss a.upper a.lower))
       (a!=1  (aig-lognot-s a=1))
       (upper (aig-logior-ss (aig-logand-ss a=1 b.upper)
                             (aig-logand-ss a!=1 c.upper)))
       (lower (aig-logior-ss (aig-logand-ss a=1 b.lower)
                             (aig-logand-ss a!=1 c.lower))))
    (a4vec upper lower))
  ///
  (local (in-theory (disable iff not acl2::zip-open)))
  (local (in-theory (disable bitops::logand-natp-type-2
                             bitops::logand-natp-type-1
                             bitops::logior-natp-type
                             bitops::logand->=-0-linear-2
                             bitops::logand->=-0-linear-1
                             bitops::upper-bound-of-logand
                             aig-list->s
                             bitops::logbitp-when-bit
                             bitops::logbitp-nonzero-of-bit
                             bitops::logbitp-when-bitmaskp
                             bitops::lognot-negp
                             bitops::lognot-natp
                             bitops::logior-<-0-linear-2
                             bitops::logior-<-0-linear-1
                             bitops::lognot-<-const
                             acl2::aig-env-lookup)))
  (defthm a4vec-bit?!-correct
    (implies (and (case-split (implies y3p (3vec-p (a4vec-eval y env))))
                  (case-split (implies z3p (3vec-p (a4vec-eval z env))))
                  (3vec-p (a4vec-eval x env)))
             (equal (a4vec-eval (a4vec-bit?! x y y3p z z3p) env)
                    (4vec-bit?! (a4vec-eval x env)
                               (a4vec-eval y env)
                               (a4vec-eval z env))))
    :hints(("Goal" :in-theory (enable 4vec-bit?! 3vec-p))
           (bitops::logbitp-reasoning)
           (and stable-under-simplificationp
                '(:bdd (:vars nil))))))





(local (encapsulate nil
         (local (in-theory (enable aig-logtail-ns)))
         (deffixequiv aig-logtail-ns)))

(local (encapsulate nil
         (local (in-theory (enable aig-loghead-ns)))
         (deffixequiv aig-loghead-ns)))

(define aig-logcollapse-ns ((n natp) (x true-listp))
  :parents (bitops::logcollapse)
  (b* ((n (lnfix n)))
    (aig-logior-ss (aig-loghead-ns n x)
                   (aig-logapp-nss n nil
                                   (aig-scons (aig-not (aig-=-ss nil (aig-logtail-ns n x)))
                                              (aig-sterm nil)))))
  ///
  (defthm aig-logcollapse-ns-correct
    (equal (aig-list->s (aig-logcollapse-ns n x) env)
           (bitops::logcollapse n (aig-list->s x env)))
    :hints(("Goal" :in-theory (enable bitops::logcollapse bool->bit)))))



(local (defthm ash-1-lte-implies-lte-integer-length
         (implies (and (natp x)
                       (integerp y)
                       (<= (ash 1 x) y))
                  (<= x (integer-length y)))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)
                 :induct (logbitp x y)))))


(local (defthm butlast-redef
           (equal (butlast x n)
                  (if (<= (len x) (nfix n))
                      nil
                    (cons (car x)
                          (butlast (cdr x) n))))
           :hints (("goal" :in-theory (enable butlast)))
           :rule-classes ((:definition :controller-alist ((butlast t t))))))

(local (defthm butlast-of-rev
         (equal (butlast (rev x) 1)
                (rev (cdr x)))
         :hints(("Goal" :in-theory (enable rev)))))


(local (defthm aig-logapp-nss-of-list-fix-1
         (equal (aig-logapp-nss n (list-fix x) y)
                (aig-logapp-nss n x y))
         :hints(("Goal" :in-theory (enable aig-logapp-nss)))))

(local (defthm aig-logapp-nss-of-list-fix-2
         (equal (aig-logapp-nss n x (list-fix y))
                (aig-logapp-nss n x y))
         :hints(("Goal" :in-theory (enable aig-logapp-nss)))))

(local (defthm aig-logtail-ns-of-list-fix
         (equal (aig-logtail-ns n (list-fix y))
                (aig-logtail-ns n y))
         :hints(("Goal" :in-theory (enable aig-logtail-ns)))))

(local (defthm aig-loghead-ns-of-list-fix
         (equal (aig-loghead-ns n (list-fix y))
                (aig-loghead-ns n y))
         :hints(("Goal" :in-theory (enable aig-loghead-ns)))))

(local (defthm aig-logext-ns-of-list-fix
         (equal (aig-logext-ns n (list-fix y))
                (aig-logext-ns n y))
         :hints(("Goal" :in-theory (enable aig-logext-ns)))))

(local (defthm aig-ite-bss-fn-of-list-fix
         (equal (aig-ite-bss-fn test (list-fix then) else)
                (aig-ite-bss-fn test then else))
         :hints(("Goal" :in-theory (e/d (aig-ite-bss-fn
                                         AIG-ITE-BSS-FN-AUX)
                                        (GL::AIG-ITE-BSS-FN-AUX-ELIM))))))

(local (defthm logext-of-pos-fix
         (Equal (logext (pos-fix n) x)
                (logext n x))
         :hints(("Goal" :expand ((logext 1 x)
                                 (logext n x)
                                 (pos-fix n))))))


(local (defthm aig-sign-s-of-list-fix
         (equal (aig-sign-s (list-fix x)) (aig-sign-s x))
         :hints(("Goal" :in-theory (enable aig-sign-s)))))


(local (defthm aig-list->s-of-list-fix
         (equal (aig-list->s (list-fix x) env)
                (aig-List->s x env))
         :hints(("Goal" :in-theory (enable aig-List->s)))))


(local (DEFTHM LOGEXT***
         (EQUAL (LOGEXT SIZE I)
                (COND ((eql (pos-fix size) 1)
                       (IF (BIT->BOOL (LOGCAR I)) -1 0))
                      (T (LOGCONS (LOGCAR I)
                                  (LOGEXT (1- SIZE)
                                          (LOGCDR I))))))
         :HINTS
         (("Goal"
           :IN-THEORY (e/d (pos-fix) (LOGEXT))
           :expand ((logext size i))
           :USE ((:INSTANCE
                  bitops::LOGEXT** (size size) (i i)))))
         :RULE-CLASSES
         ((:DEFINITION :CLIQUE (LOGEXT)
           :CONTROLLER-ALIST ((LOGEXT T NIL))))))

(local (in-theory (disable bitops::logext** logext***)))
(local
 (encapsulate nil
   (local (in-theory (enable logext***)))
   (local (defthm pos-fix-not-1-implies-pos-fix-of-m-minus-1
            (implies (not (equal 1 (pos-fix m)))
                     (and (equal (pos-fix (+ -1 m)) (+ -1 m))
                          (equal (pos-fix m) m)))
            :hints(("Goal" :in-theory (enable pos-fix)))))

   (defrule logext-of-logapp-more
     (implies (<= (pos-fix n) (nfix m))
              (equal (logext n (logapp m a b))
                     (logext n a)))
     :enable (ihsext-inductions ihsext-recursive-redefs)
     :disable (signed-byte-p**))

   (defrule logext-of-logapp-less
     (implies (> (pos-fix n) (nfix m))
              (equal (logext n (logapp m a b))
                     (logapp m a (logext (- (pos-fix n) (nfix m)) b))))
     :induct (my-ind m n a b)
     :enable (ihsext-inductions ihsext-recursive-redefs)
     :disable (signed-byte-p**)
     :prep-lemmas
     ((defun my-ind (m n a b)
        (if (or (zp m)
                (eql (pos-fix n) 1))
            (list m n a b)
          (my-ind (- m 1) (- n 1) (logcdr a) b)))))

   ;; (defrule logext-of-logapp-same
   ;;   (implies (equal (pos-fix n) (nfix m))
   ;;            (equal (logext n (logapp m a b))
   ;;                   (logext n a)))
   ;;   :enable (ihsext-inductions ihsext-recursive-redefs)
   ;;   :disable (signed-byte-p**))

   (defruled logext-of-logapp-split
     (equal (logext n (logapp m a b))
            (if (<= (pos-fix n) (nfix m))
                (logext n a)
              (logapp m a (logext (- (pos-fix n) (nfix m)) b)))))

   

   (local (defun induct-n-m-x (n m x)
            (if (or (eql 1 (pos-fix m)) (zp n))
                x
              (induct-n-m-x (1- n) (1- m) (logcdr x)))))
   

   (defthmd logtail-of-logext
     (implies (< (nfix n) (pos-fix m))
              (equal (logtail n (logext m x))
                     (logext (- (pos-fix m) (nfix n)) (logtail n x))))
     :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                        bitops::logtail**)
             :induct (induct-n-m-x n m x)
             :do-not-induct t
             :expand ((:free (x) (logtail n x))))
            ;; (and stable-under-simplificationp
            ;;      '(:in-theory (enable pos-fix)))
            ))

   (local (defthm pos-fix-when-not-posp
            (implies (not (posp x))
                     (equal (pos-fix x) 1))
            :hints(("Goal" :in-theory (enable pos-fix)))))

   (defthmd logtail-greater-of-logext
     (implies (<= (pos-fix m) (nfix n))
              (equal (logtail n (logext m x))
                     (if (logbitp (- (pos-fix m) 1) x) -1 0)))
     :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                        bitops::logtail**
                                        bitops::logbitp**)
             :induct (induct-n-m-x n m x)
             :do-not-induct t
             :expand ((:free (x) (logtail n x))))
            ;; (and stable-under-simplificationp
            ;;      '(:in-theory (enable pos-fix)))
            ))

   (defthmd logtail-of-equal-logext
     (implies (and (equal y (logext m x))
                   (< (nfix n) (pos-fix m)))
              (equal (logtail n y)
                     (logext (- (pos-fix m) (nfix n)) (logtail n x))))
     :hints(("Goal" :in-theory (enable logtail-of-logext))))))

(local
 (progn
   (defthm aig-eval-of-nil
     (equal (aig-eval nil env) nil))

   (defthm aig-eval-of-t
     (equal (aig-eval t env) t))

   (in-theory (disable aig-eval))))

(local (defthm aig-list->u-bound
         (< (aig-list->u x env)
            (ash 1 (len x)))
         :hints(("Goal" :in-theory (enable aig-list->u)
                 :expand ((ash 1 (+ 1 (len (cdr x)))))))
         :rule-classes :linear))

(local (defthmd aig-list->u-bound2-lemma
         (implies (aig-eval (car (last x)) env)
                  (<= (ash 1 (len (cdr x)))
                      (aig-list->u x env)))
         :hints(("Goal" :in-theory (enable aig-list->u last)
                 :expand ((ash 1 (+ 1 (len (cddr x)))))))))

(local (defthmd aig-list->u-bound3-lemma
         (implies (not (aig-eval (car (last x)) env))
                  (< (aig-list->u x env)
                     (ash 1 (len (cdr x)))))
         :hints(("Goal" :in-theory (enable aig-list->u last)
                 :expand ((ash 1 (+ 1 (len (cddr x)))))))))

(local (defthm car-last-rev
         (equal (car (last (rev x)))
                (car x))
         :hints(("Goal" :in-theory (enable last rev)))))

(local (defthm len-cdr-rev
         (equal (len (cdr (rev x)))
                (len (cdr x)))
         :hints(("Goal" :in-theory (enable rev)))))

(local (defthm aig-list->u-bound2
         (implies (aig-eval (car x) env)
                  (<= (ash 1 (len (cdr x)))
                      (aig-list->u (rev x) env)))
         :hints(("Goal" :use ((:instance aig-list->u-bound2-lemma
                               (x (rev x))))
                 :in-theory (disable last rev aig-list->u)))
         :rule-classes :linear))

(local (defthm aig-list->u-bound3
         (implies (not (aig-eval (car x) env))
                  (< (aig-list->u (rev x) env)
                     (ash 1 (len (cdr x)))))
         :hints(("Goal" :use ((:instance aig-list->u-bound3-lemma
                               (x (rev x))))
                 :in-theory (disable last rev aig-list->u)))
         :rule-classes :linear))

(local (defthm our-logtail-of-logapp-1
         (IMPLIES (<= (NFIX ACL2::N) (NFIX ACL2::SIZE))
                  (EQUAL (LOGTAIL ACL2::N
                                  (LOGAPP ACL2::SIZE ACL2::I ACL2::J))
                         (LOGAPP (- (NFIX ACL2::SIZE) (NFIX ACL2::N))
                                 (LOGTAIL ACL2::N ACL2::I)
                                 ACL2::J)))
         :hints (("goal" :use bitops::logtail-of-logapp-1))))



(local (defthmd aig-list->u-plus-shift-lemma
         (implies (aig-eval (car (last x)) env)
                  (equal (+ (- (ash 1 (len (cdr x)))) (aig-list->u x env))
                         (aig-list->u (butlast x 1) env)))
         :hints (("Goal" :induct (len x)
                  :expand ((Aig-list->u x env)
                           (:free (a b) (aig-list->u (cons a b) env))
                           (butlast x 1)
                           (len (cdr x))
                           (len x)
                           (last x)
                           (:free (a) (ash 1 (+ 1 a))))
                  :in-theory (disable aig-list->u butlast (:d len) last))
                 (and stable-under-simplificationp
                      '(:in-theory (e/d (logcons)
                                        (aig-list->u butlast (:d len) last)))))))

(local (defthm aig-list->u-plus-shift
         (implies (and (aig-eval (car (last x)) env)
                       (equal len (len (cdr x))))
                  (equal (+ (- (ash 1 len)) (aig-list->u x env))
                         (aig-list->u (butlast x 1) env)))
         :hints (("goal" :use ((:instance aig-list->u-plus-shift-lemma))))))

(local (defthm aig-list->u-plus-shift-rev
         (implies (aig-eval (car x) env)
                  (= (+ (ash 1 (len (cdr x)))
                        (aig-list->u (rev (cdr x)) env))
                     (aig-list->u (rev x) env)))
         :hints (("goal" :use ((:instance aig-list->u-plus-shift-lemma
                                (x (rev x))))
                  :in-theory (disable aig-list->u-plus-shift-lemma
                                      aig-list->u-plus-shift)))
         :rule-classes ((:rewrite :corollary
                         (implies (and (aig-eval (car x) env)
                                       (equal len (len (cdr x))))
                                  (equal (+ (ash 1 len) (aig-list->u (rev (cdr x)) env))
                                         (aig-list->u (rev x) env))))
                        (:rewrite :corollary
                         (implies (and (aig-eval (car x) env)
                                       (equal len (len (cdr x))))
                                  (equal (+ (- (ash 1 len)) (- (aig-list->u (rev (cdr x)) env)))
                                         (- (aig-list->u (rev x) env)))))
                        :linear)))

(local (defthmd aig-list->u-when-not-car-lemma
         (implies (not (aig-eval (car (last x)) env))
                  (equal (aig-list->u (butlast x 1) env)
                         (aig-list->u x env)))
         :hints (("Goal" :induct (len x)
                  :expand ((Aig-list->u x env)
                           (:free (a b) (aig-list->u (cons a b) env))
                           (butlast x 1)
                           (len (cdr x))
                           (len x)
                           (last x)
                           (:free (a) (ash 1 (+ 1 a))))
                  :in-theory (disable aig-list->u butlast (:d len) last))
                 (and stable-under-simplificationp
                      '(:in-theory (e/d (logcons)
                                        (aig-list->u butlast (:d len) last)))))))

(local (defthm aig-list->u-when-not-car
         (implies (not (aig-eval (car x) env))
                  (equal (aig-list->u (rev (cdr x)) env)
                         (aig-list->u (rev x) env)))
         :hints (("goal" :use ((:instance aig-list->u-when-not-car-lemma
                                (x (rev x))))))))

(local (defthmd equal-of-logapp
         (equal (equal (logapp w x y) z)
                (and (integerp z)
                     (equal (loghead w x) (loghead w z))
                     (equal (ifix y) (logtail w z))))
         :hints((logbitp-reasoning))))

(define aig-head-tail-concat-aux ((rev-shift true-listp)
                                  (shift-len (eql shift-len (len rev-shift)))
                                  (lsbs true-listp) ;; already truncated at width
                                  (msbs true-listp)
                                  (msbs-len (eql msbs-len (len msbs)))
                                  (width posp)
                                  (const-rsh natp))
  :returns (concat true-listp)
  :ruler-extenders :all
  ;; 
  ;; we will compute:
  ;;    (logext width (logtail const-rsh (logapp (+ nshifted rest-shift) lsbs msbs)))
  ;; where nshifted is the contribution from (car rev-shift), which is
  ;; (ash (if (eval (car rev-shift)) 1 0) shift-len).

  (b* ((width (lposfix width))
       (const-rsh (lnfix const-rsh))
       ((when (atom rev-shift))
        (aig-logext-ns width (aig-logtail-ns const-rsh msbs)))
       (msbs-len (mbe :logic (len msbs) :exec msbs-len))
       (shift-len (1- (mbe :logic (len rev-shift) :exec shift-len)))
       ((when (eq (car rev-shift) nil))
        ;; if (car rev-shift) is false, we simply recur on the rest
        (aig-head-tail-concat-aux
         (cdr rev-shift) shift-len lsbs msbs msbs-len width const-rsh))
       (width-plus-rsh (+ width const-rsh))
       (shift-too-widep (mbe :logic (<= width-plus-rsh (ash 1 shift-len))
                             :exec (or (< (integer-length width-plus-rsh) shift-len)
                                       (<= width-plus-rsh (ash 1 shift-len)))))

       (shift-too-narrowp (and (not shift-too-widep)
                               (>= const-rsh (+ msbs-len (1- (ash 1 (+ 1 shift-len)))))))
                          
       ((when shift-too-narrowp)
        ;; Special case: the constant right shift is so big that we can't
        ;; possibly get anything except just the sign bit of the msbs.
        (aig-sterm (aig-sign-s msbs)))

       (rest1
        (if shift-too-widep
            ;; nshifted > width+const-rsh, so we don't get any contribution from the msbs --
            ;; logext width (logtail const-rsh lsbs) but we assume lsbs are already
            ;; truncated at width+const-rsh so just logtail.
            (aig-logtail-ns const-rsh lsbs)
          (b* ((nshifted (ash 1 shift-len))
               ((when (<= nshifted const-rsh))
                ;; with nshifted <= const-rsh -->
                ;; (logext width (logtail (- const-rsh nshifted)
                ;;                         (logapp rest-shift (logtail nshifted lsbs) msbs)))
                (aig-head-tail-concat-aux
                 (cdr rev-shift) shift-len
                 (aig-logtail-ns nshifted lsbs)
                 msbs msbs-len
                 width
                 (- const-rsh nshifted))))
            ;; (logext width (logtail const-rsh (logapp (+ nshifted rest-shift) lsbs msbs)))
            ;; when nshifted > const-rsh -->
            ;; (logext width (logapp (+ (- nshfted const-rsh) rest-shift)
            ;;                        (logtail const-rsh lsbs) msbs)
            ;; = (logext width (logapp (- nshifted const-rsh)
            ;;                          (logtail const-rsh lsbs)
            ;;                          (logapp rest-shift
            ;;                                  (logtail nshifted lsbs)
            ;;                                  msbs)))
            ;; already know width+const-rsh >= nshifted (not shift-too-widep)
            ;; so this =
            ;; (logapp (- nshifted const-rsh)
            ;;         (logtail const-rsh lsbs)
            ;;         (logext (- width (- nshifted const-rsh)) ;; = (+ width const-rsh (- nshifted))
            ;;                  (logapp rest-shift (logtail nshifted lsbs) msbs)))
            (aig-logapp-nss (- nshifted const-rsh)
                            (aig-logtail-ns const-rsh lsbs)
                            (aig-head-tail-concat-aux
                             (cdr rev-shift) shift-len
                             (aig-logtail-ns nshifted lsbs)
                             msbs msbs-len
                             (- width-plus-rsh nshifted)
                             0)))))
       ((when (eq (car rev-shift) t)) rest1)
       ;; if (car rev-shift) is false, we simply recur on the rest of rev-shift
       (rest0 (aig-head-tail-concat-aux
               (cdr rev-shift) shift-len lsbs msbs msbs-len width const-rsh)))
    (aig-ite-bss (car rev-shift) rest1 rest0))
  ///
  (local (in-theory (disable signed-byte-p
                             signed-byte-p**)))

  




  

  (local (defthm hack-width-<-aig-list->u-when-car
           (implies (and (equal (car rev-shift) t)
                         (< WIDTH (ASH 1 (+ -1 (LEN REV-SHIFT)))))
                    (<= width (AIG-LIST->U (REV REV-SHIFT) ENV)))
           :hints (("goal" :use ((:instance aig-list->u-bound2 (x rev-shift)))
                    :in-theory (disable aig-list->u-bound2)))))

  (local (defthm logtail-of-logapp-add-thing-lemma
           (implies (and (<= b c)
                         (natp b) (natp c) (natp a))
                    (equal (logtail (+ c (- b))
                                    (logapp a (logtail b x) y))
                           (logtail c (logapp (+ b a) x y))))
           :hints ((logbitp-reasoning))))

  

  
           

  

  
  ;; (local (defthm logext-when-zp
  ;;          (implies (zp n)
  ;;                   (equal (loghead n x) 0))))

  


  (local (defthmd my-loghead-identity
           (implies (unsigned-byte-p (nfix width) x)
                    (equal (loghead width x) (ifix x)))
           :hints(("Goal" :in-theory (enable bitops::loghead-identity)
                   :cases ((natp width))))))

  (local (defthm signed-byte-p-of-logtail
           (implies (and (posp w)
                         (integerp x))
                    (iff (signed-byte-p w (logtail sh x))
                         (signed-byte-p (+ w (nfix sh)) x)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                              bitops::ihsext-inductions)))))


  (DEFTHM our-LOGEXT-IDENTITY
    (IMPLIES (SIGNED-BYTE-P (pos-fix SIZE) I)
             (EQUAL (LOGEXT SIZE I)
                    I))
    :hints(("Goal" :in-theory (enable pos-fix logext***))))

  

  (defruled signed-byte-p-monotonic
    (implies (and (signed-byte-p n x)
                  (<= n m)
                  (integerp m))
             (signed-byte-p m x))
    :enable (signed-byte-p)
    :prep-lemmas
    ((defrule l0
       (implies (and (< x (expt 2 n))
                     (<= n m)
                     (integerp n)
                     (integerp m)
                     (integerp x))
                (< x (expt 2 m)))
       :disable (acl2::expt-is-increasing-for-base>1)
       :use ((:instance acl2::expt-is-increasing-for-base>1
              (r 2) (i n) (j m))))
     (defrule l1
       (implies (and (<= (- (expt 2 n)) x)
                     (<= n m)
                     (integerp n)
                     (integerp m)
                     (integerp x))
                (<= (- (expt 2 m)) x))
       :disable (acl2::expt-is-increasing-for-base>1)
       :use ((:instance acl2::expt-is-increasing-for-base>1
              (r 2) (i n) (j m))))))

  ;; (defthm aig-head-tail-concat-aux-of-width-0
  ;;   (implies (zp width)
  ;;            (equal (aig-list->s (aig-head-tail-concat-aux rev-shift shift-len lsbs msbs width const-rsh) env)
  ;;                   0)))
  
  ;; (local (in-theory (disable POS-FIX-NOT-1-IMPLIES-POS-FIX-OF-M-MINUS-1)))

  ;; (local (defthm logapp-of-equal-logapp-id
  ;;          (implies (and (equal x (logapp n y z))
  ;;                        (equal res (logapp m w (logapp n y z)))
  ;;                        (syntaxp (not (equal res `(logapp ,m ,w ,x)))))
  ;;                   (equal (logapp m w x)
  ;;                          res))))
  (local (defthm len-minus-1
           (implies (consp x)
                    (equal (+ -1 (len x))
                           (len (cdr x))))))

  (local (in-theory (disable len)))

  (local (Defthm pos-fix-of-nfix
           (equal (pos-fix (nfix x)) (pos-fix x))
           :hints(("Goal" :in-theory (enable pos-fix)))))


  (local (defthm logtail-when-signed-byte-p
           (implies (<= (integer-length x) (nfix width))
                    (equal (logtail width x)
                           (bool->vec (< (ifix x) 0))))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (local (defthm logext-of-bool->vec
           (equal (logext n (bool->vec x))
                  (bool->vec x))
           :hints(("Goal" :in-theory (enable bool->vec)))))

  (local (defthm integer-length-of-logapp-bound
           (<= (integer-length (logapp n a b))
               (+ (integer-length b) (nfix n)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                             bitops::ihsext-recursive-redefs)))
           :rule-classes :linear))

  (local (defthm integer-length-of-aig-list->s
           (<= (integer-length (aig-list->s x env)) (len (cdr x)))
           :hints(("Goal" :in-theory (enable aig-list->s gl::s-endp gl::scdr
                                             integer-length** len)))))

  (local (defthm integer-length-of-logapp-aig-list->s-bound
           (implies (and (<= (+ -1 (len msbs) (ash 1 len)) const-rsh)
                         (equal len (len shift)))
                    (<= (integer-length (logapp (aig-list->u shift env)
                                                lsbs (aig-list->s msbs env)))
                        const-rsh))
           :hints (("goal" :use ((:instance aig-list->u-bound (x shift))
                                 (:instance integer-length-of-aig-list->s
                                  (x msbs))
                                 (:instance integer-length-of-logapp-bound
                                  (n (aig-list->u shift env))
                                  (a lsbs)
                                  (b (aig-list->s msbs env))))
                    :expand ((len msbs))
                    :in-theory (disable integer-length-of-logapp-bound
                                        integer-length-of-aig-list->s
                                        aig-list->u-bound)))))


  (local (in-theory (enable len)))


  (defthm aig-head-tail-concat-aux-correct
    (implies (signed-byte-p (+ (pos-fix width) (nfix const-rsh)) (aig-list->s lsbs env))
             (equal (aig-list->s (aig-head-tail-concat-aux rev-shift shift-len lsbs msbs msbs-len width const-rsh) env)
                    (logext width
                            (logtail const-rsh
                                     (logapp (aig-list->u (rev rev-shift) env)
                                             (aig-list->s lsbs env)
                                             (aig-list->s msbs env))))))
    :hints (("goal" :induct t :do-not-induct t
             :in-theory (disable bitops::logtail-of-loghead
                                 (:d aig-head-tail-concat-aux))
             :expand ((aig-head-tail-concat-aux rev-shift shift-len lsbs msbs msbs-len width const-rsh)))
            ;; (and stable-under-simplificationp
            ;;      '(:cases ((< (ASH 1 (LEN (CDR REV-SHIFT)))
            ;;                   (+ (pos-fix WIDTH) (NFIX CONST-RSH))))))
            (and stable-under-simplificationp
                 '(:in-theory (enable logtail-of-logext
                                      logtail-greater-of-logext
                                      logtail-of-equal-logext
                                      signed-byte-p-monotonic)))
            (and stable-under-simplificationp
                 '(:in-theory (enable logext-of-logapp-split)))
            (and stable-under-simplificationp
                 '(:in-theory (enable equal-of-logapp))))))

(local (defthm signed-byte-p-of-logext
         (implies (equal width1 (pos-fix width))
                  (signed-byte-p width1 (logext width x)))
         :hints(("Goal" :in-theory (e/d* (bitops::ihsext-recursive-redefs
                                          bitops::ihsext-inductions)
                                         (signed-byte-p))))))

(define aig-head-of-concat ((concat-width true-listp)
                            (lsbs true-listp)
                            (msbs true-listp)
                            (width posp))
  (b* ((width (lposfix width))
       ((when (atom concat-width))
        (aig-logext-ns width msbs))
       (rev-shift (rev concat-width))
       (sign-bit (car rev-shift))
       (rev-shift (cdr rev-shift))
       (msbs-len (len msbs)))
    (aig-ite-bss sign-bit
                 (b* ((const-rsh (ash 1 (len rev-shift)))
                      (lsbs (aig-logext-ns (+ width const-rsh) lsbs)))
                   (aig-head-tail-concat-aux rev-shift
                                             (len rev-shift)
                                             lsbs
                                             msbs msbs-len
                                             width
                                             const-rsh))
                 (b* ((lsbs (aig-logext-ns width lsbs)))
                   (aig-head-tail-concat-aux rev-shift
                                             (len rev-shift)
                                             lsbs
                                             msbs msbs-len
                                             width
                                             0))))
  ///
  (local (defthm butlast-of-rev
           (equal (butlast (rev x) 1)
                  (rev (cdr x)))
           :hints(("Goal" :in-theory (enable rev)))))

  (local (defthm rev-cdr-rev
           (implies (consp x)
                    (equal (rev (cdr (rev x)))
                           (butlast x 1)))
           :hints (("Goal" :use ((:instance butlast-of-rev (x (rev x))))
                    :in-theory (disable butlast-of-rev)))))

  (local (defthm len-equal-0
           (equal (equal (len x) 0) (atom x))))

  (local (defthm aig-list->u-of-butlast
           (implies (< (aig-list->s x env) 0)
                    (= (aig-list->u (butlast x 1) env)
                       (+ (aig-list->s x env)
                          (ash 1 (1- (len x))))))
           :hints(("Goal" :in-theory (e/d (aig-list->s aig-list->u
                                                       gl::scdr
                                                       gl::s-endp)
                                          (butlast))
                   :induct t)
                  (and stable-under-simplificationp
                       '(:in-theory (e/d (logcons) (butlast))
                         :expand ((:free (x) (ash 1 (len (cdr x))))))))))

  (local (defthm aig-list->u-of-butlast-when-nonneg
           (implies (<= 0 (aig-list->s x env))
                    (= (aig-list->u (butlast x 1) env)
                       (aig-list->s x env)))
           :hints(("Goal" :in-theory (e/d (aig-list->s aig-list->u
                                                       gl::scdr
                                                       gl::s-endp
                                                       butlast-redef)
                                          (butlast))
                   :induct t)
                  (and stable-under-simplificationp
                       '(:in-theory (e/d (logcons) (butlast))
                         :expand ((:free (x) (ash 1 (len (cdr x))))))))))


  (local (defthm len-cdr-rev
           (equal (len (cdr (rev x)))
                  (len (cdr x)))
           :hints(("Goal" :in-theory (enable rev)))))

  (local (in-theory (disable butlast butlast-redef)))

  (local (defthm aig-eval-of-car-rev-x
           (iff (aig-eval (car (rev x)) env)
                (< (aig-list->s x env) 0))
           :hints(("Goal" :in-theory (enable aig-list->s rev
                                             gl::scdr gl::s-endp)))))


  (local (defthm ash-1-len-greater-than-minus-aig-list->s
           (<= (- (aig-list->s x env)) (ash 1 (len (cdr x))))
           :hints(("Goal"
                   :induct t
                   :in-theory (enable aig-list->s
                                      gl::s-endp gl::scdr len
                                      logcons)
                   :expand ((ash 1 (+ 1 (len (cddr x)))))))
           :rule-classes :linear))

  (local (defthm dumb-lemma-for-logtail-of-logapp
           (implies (and (< n 0) (natp m))
                    (<= (nfix (+ m n)) m))))

  (local (defthm our-logtail-of-logapp-1
           (IMPLIES (<= (NFIX ACL2::N) (NFIX ACL2::SIZE))
                    (EQUAL (LOGTAIL ACL2::N
                                    (LOGAPP ACL2::SIZE ACL2::I ACL2::J))
                           (LOGAPP (- (NFIX ACL2::SIZE) (NFIX ACL2::N))
                                   (LOGTAIL ACL2::N ACL2::I)
                                   ACL2::J)))
           :hints (("goal" :use bitops::logtail-of-logapp-1))))

  (local (defthm aig-list->s-when-not-consp
           (implies (not (consp x))
                    (equal (aig-list->s x env) 0))
           :hints(("Goal" :in-theory (enable aig-list->s gl::s-endp)))))


  (local (defthm logext-logapp-logext
           (equal (logext n (logapp m (logext n x) y))
                  (logext n (logapp m x y)))
           :hints ((logbitp-reasoning))))


  (local (in-theory (disable signed-byte-p)))


  (defthm aig-head-of-concat-correct
    (equal (aig-list->s (aig-head-of-concat concat-width lsbs msbs width) env)
           (b* ((concat-width (aig-list->s concat-width env))
                (lsbs (aig-list->s lsbs env))
                (msbs (aig-list->s msbs env)))
             (logext width (if (< concat-width 0)
                               (ash msbs concat-width)
                             (logapp concat-width lsbs msbs)))))))
  


(local (defthm logand-of-logext-integer-length
         (implies (<= 0 (ifix mask))
                  (equal (logand mask (logext (+ 1 (integer-length mask)) x))
                         (logand mask x)))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)
                 :induct (logand mask x)
                 :do-not-induct t))))

(local (defthm logext-of-integer-length-mask-under-logior
         (implies (<= 0 (ifix mask))
                  (equal (logior (lognot mask)
                                 (logext (+ 1 (integer-length mask)) x))
                         (logior (lognot mask) x)))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)
                 :induct (logand mask x)
                 :do-not-induct t))))

(define a4vec-concat ((w    a4vec-p  "Width argument to the concat.")
                      (x    a4vec-p  "Low bits to concatenate.")
                      (y    a4vec-p  "High bits to concatenate.")
                      (mask 4vmask-p "Care mask for the result."))
  :short "Symbolic version of @(see 4vec-concat)."
  :long "<p>As a special consideration, we use the care mask to try to avoid
creating enormous vectors when given a huge @('width') argument.</p>"
  :returns (res a4vec-p)
  (b* (((a4vec w))
       ((a4vec x))
       ((a4vec y))
       (mask (4vmask-fix mask))
       ((when (sparseint-equal mask 0))
        ;; [Jared] this was previously using 4vec-0.  I think it's probably
        ;; better to use 4vec-x, in general, since for instance many
        ;; arithmetic operations check a2vec-p and then do something really
        ;; simple in the "nope, not a 2vec, may as well just return all xes."
        (a4vec-x))
       ((when (sparseint-< 0 mask))
        (b* ((width (+ 1 (sparseint-length mask))))
          (a4vec-ite (aig-and (a2vec-p w) ;; Is the width properly two-valued?
                              (aig-not (aig-sign-s w.upper))) ;; Is it natural?
                     ;; Note: May want to do something more to coerce w to
                     ;; something with sign bit equal to NIL.
                     (b* ((upper (aig-head-of-concat w.upper x.upper y.upper width))
                          (lower (aig-head-of-concat w.upper x.lower y.lower width)))
                       (a4vec upper lower))
                     (a4vec-x)))))
    (and (not (a4vec-constantp w))
         (cw "Warning: bitblasting variable-width concat under unbounded mask~%"))
    (a4vec-ite (aig-and (a2vec-p w) ;; Is the width properly two-valued?
                        (aig-not (aig-sign-s w.upper)) ;; Is it natural?
                        )
               ;; Proper concatenation width.  But, take special care here to
               ;; avoid catastrophic shifts.
               (b* ((shift w.upper)
                    (xmask (aig-lognot-s (aig-ash-ss 1 (aig-sterm t) shift)))
                    (yshu  (aig-ash-ss 1 y.upper shift))
                    (yshl  (aig-ash-ss 1 y.lower shift)))
                 (a4vec (aig-logior-ss (aig-logand-ss xmask x.upper) yshu)
                        (aig-logior-ss (aig-logand-ss xmask x.lower) yshl)))
               ;; Nonsensical concatenation width.  Just return all Xes.
               (a4vec-x)))
  ///

  (local (defthm logapp-formulation
           (implies (natp n)
                    (equal (logior (ash y n)
                                   (logand x (lognot (ash -1 n))))
                           (logapp n x y)))
           :hints((bitops::logbitp-reasoning))))

  (defthm a4vec-concat-correct
    (4vec-mask-equiv (a4vec-eval (a4vec-concat n x y mask) env)
                     (4vec-concat (a4vec-eval n env)
                                  (a4vec-eval x env)
                                  (a4vec-eval y env))
                     mask)
    :hints(("Goal" :expand ((:free (x) (hide x)))
            :in-theory '(equal-of-4vec-mask?-when-equal-under-mask)
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:expand nil
                  :in-theory (enable 4vec-concat 4vec-mask))))
    :otf-flg t))


(define a4vec-zero-ext ((n    a4vec-p  "Place to zero extend or truncate.")
                        (x    a4vec-p  "Vector to zero extend at this place.")
                        (mask 4vmask-p "Care mask for the result."))
  :short "Symbolic version of @(see 4vec-zero-ext)."
  :long "<p>We just reuse @(see a4vec-concat) since it already provides special
optimization to avoid problems due to large masks.</p>"
  :returns (res a4vec-p)
  (a4vec-concat n x (a4vec-0) mask)
  ///
  (defthm a4vec-zero-ext-correct
    (4vec-mask-equiv (a4vec-eval (a4vec-zero-ext n x mask) env)
                     (4vec-zero-ext (a4vec-eval n env)
                                    (a4vec-eval x env))
                     mask)
    :hints(("Goal" :expand ((:free (x) (hide x)))
            :in-theory '(equal-of-4vec-mask?-when-equal-under-mask)
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:expand nil
                  :in-theory (enable 4vec-zero-ext
                                     4vec-concat))))))

(define aig-list->s-upper-bound ((x true-listp))
  :short "Computes a constant upper bound for the symbolic value of x."
  :returns (upper-bound integerp :rule-classes :type-prescription)
  (b* (((mv first rest end) (gl::first/rest/end x))
       ((when end)
        (if (eq first t)
            -1
          0))
       (rest-bound (aig-list->s-upper-bound rest)))
    (logcons (if (eq first nil) 0 1) rest-bound))
  ///
  (defthmd aig-list->s-upper-bound-correct
    (<= (aig-list->s x env) (aig-list->s-upper-bound x))
    :hints(("Goal" :in-theory (enable aig-list->s)))
    :rule-classes :linear)

  (defthm aig-list->s-upper-bound-lower-bound-when-sign-bit-non-t
    (implies (not (equal (aig-sign-s x) t))
             (<= 0 (aig-list->s-upper-bound x)))
    :hints(("Goal" :in-theory (enable aig-sign-s)))
    :rule-classes :linear))

(define aig-list->s-lower-bound ((x true-listp))
  :short "Computes a constant lower bound for the symbolic value of x."
  :returns (lower-bound integerp :rule-classes :type-prescription)
  (b* (((mv first rest end) (gl::first/rest/end x))
       ((when end)
        (if (eq first nil)
            0
          -1))
       (rest-bound (aig-list->s-lower-bound rest)))
    (logcons (if (eq first t) 1 0) rest-bound))
  ///
  (defthmd aig-list->s-lower-bound-correct
    (>= (aig-list->s x env) (aig-list->s-lower-bound x))
    :hints(("Goal" :in-theory (enable aig-list->s)))
    :rule-classes :linear))

(define a4vec-part-select ((lsb   a4vec-p "LSB of the select -- may be negative")
                           (width a4vec-p "Width of the range to select")
                           (in    a4vec-p "input to select from")
                           (mask  4vmask-p))

  :prepwork ((local (defthm aig-and-implies-nonnil
                      (implies (aig-and a b)
                               (and a b))
                      :hints(("Goal" :in-theory (enable aig-and)))
                      :rule-classes :forward-chaining))
             (local (Defthm aig-not-implies-non-t
                      (implies (aig-not x)
                               (not (equal x t)))
                      :hints(("Goal" :in-theory (enable aig-not)))
                      :rule-classes :forward-chaining)))

  :returns (partsel a4vec-p)

  (b* (((a4vec width))
       ((a4vec lsb))
       ((a4vec in))
       (mask (4vmask-fix mask))
       ((when (sparseint-equal mask 0))
        ;; [Jared] this was previously using 4vec-0.  I think it's probably
        ;; better to use 4vec-x, in general, since for instance many
        ;; arithmetic operations check a2vec-p and then do something really
        ;; simple in the "nope, not a 2vec, may as well just return all xes."
        (a4vec-x)))
    (a4vec-ite
     (aig-and (a2vec-p lsb)
              (aig-and (a2vec-p width)
                       (aig-not (aig-sign-s width.upper)))) 
     (b* ((maskwidth (and (or (sparseint-< 0 mask)
                              (and (not (and (a4vec-constantp width)
                                             (a4vec-constantp lsb)))
                                   (cw "Warning: bitblasting variable part select under unbounded mask~%")))
                          (+ 1 (sparseint-length mask))))
          (width-limit (if maskwidth
                           (min maskwidth (aig-list->s-upper-bound width.upper))
                         (aig-list->s-upper-bound width.upper)))
          ((when (eql 0 width-limit))
           ;; width is 0
           (aig-sterm nil))
          (neg-lsb (aig-unary-minus-s lsb.upper))
          ;; First compute the shifted, un-truncated result:
          ;;   if LSB >= 0 then (rsh lsb in) else (concat (- lsb) (x) in).
          (shift.upper (aig-head-of-concat neg-lsb (aig-sterm t) in.upper width-limit))
          (shift.lower (aig-head-of-concat neg-lsb (aig-sterm nil) in.lower width-limit)))
          ;; next, truncate the shifted result at width -- (concat width shifted 0)
       (a4vec-zero-ext width (a4vec shift.upper shift.lower) mask))

     ;; bad lsb/width case
     (a4vec-x)))
  ///
  (local (defthm loghead-of-logext-when-head-less
           (implies (<= (nfix w1) (nfix w2))
                    (equal (loghead w1 (logext w2 x))
                           (loghead w1 x)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                              bitops::ihsext-inductions)))))


  ;; (local (defthm loghead-of-logext-hack
  ;;          (implies (and (equal (aig-list->s upper env)
  ;;                               (aig-list->s lower env))
  ;;                        (< ext-width (aig-list->s-upper-bound upper)))
  ;;                   (<= ext-width (aig-list->s lower env))


  (local (defthm logbitp-past-integer-length-when-nonneg
           (implies (and (natp mask)
                         (<= (+ 1 (integer-length mask)) (nfix bit)))
                    (not (logbitp bit mask)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                              bitops::ihsext-inductions)))))

  (local (defthm logior-loghead-logext-mask
           (implies (posp mask)
                    (equal (logior (lognot mask)
                                   (loghead headwidth (logext (+ 1 (integer-length mask)) x)))
                           (logior (lognot mask)
                                   (loghead headwidth x))))
           :hints ((logbitp-reasoning))))

  (local (defthm logand-loghead-logext-mask
           (implies (posp mask)
                    (equal (logand mask
                                   (loghead headwidth (logext (+ 1 (integer-length mask)) x)))
                           (logand mask
                                   (loghead headwidth x))))
           :hints ((logbitp-reasoning))))


  (defthm a4vec-part-select-correct
    (4vec-mask-equiv (a4vec-eval (a4vec-part-select lsb width in mask) env)
                     (4vec-part-select (a4vec-eval lsb env)
                                             (a4vec-eval width env)
                                             (a4vec-eval in env))
                     mask)
    :hints(("Goal" :expand ((:free (x) (hide x)))
            :in-theory '(equal-of-4vec-mask?-when-equal-under-mask)
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:expand nil
                  :in-theory (enable 4vec-part-select 4vec-zero-ext 4vec-rsh 4vec-shift-core 4vec-concat
                                      aig-list->s-upper-bound-correct)))
           (and stable-under-simplificationp
                '(:in-theory (enable 4vec-mask))))))


(define aig-overlap-width-ss-aux ((rev-pos true-listp)
                                  (pos-len (equal pos-len (len rev-pos)))
                                  (x true-listp)
                                  (y true-listp)
                                  ;; (max-len (equal max-len (max (len x) (len y))))
                                  (width posp))
   ;; (logext width (logapp pos x (ash y (- pos))))
  :ruler-extenders :all
  :measure (len rev-pos)
  (b* ((rev-pos (llist-fix rev-pos))
       (y (llist-fix y))
       (x (llist-fix x))
       (width (lposfix width))
       ((when (atom rev-pos)) y)
       (pos-len (1- (mbe :logic (len rev-pos) :exec pos-len)))
       ((when (eq (car rev-pos) nil))
        (aig-overlap-width-ss-aux (cdr rev-pos) pos-len x y width))
       (pos-too-large (mbe :logic (<= width (ash 1 pos-len))
                           :exec (or (< (integer-length width) pos-len)
                                     (<= width (ash 1 pos-len)))))
       (rest1
        (if pos-too-large
            x
          (b* ((nshifted (ash 1 pos-len)))
            (aig-logapp-nss nshifted x
                            (aig-overlap-width-ss-aux
                             (cdr rev-pos) pos-len
                             (aig-logtail-ns nshifted x)
                             (aig-logtail-ns nshifted y)
                             (- width nshifted))))))
       ((when (eq (car rev-pos) t)) rest1)
       (rest0 (aig-overlap-width-ss-aux (cdr rev-pos) pos-len x y width)))
    (aig-ite-bss (car rev-pos) rest1 rest0))
  ///
  (local (in-theory (disable signed-byte-p)))


  (local (defthm signed-byte-p-of-logtail
           (implies (and (posp w)
                         (integerp x))
                    (iff (signed-byte-p w (logtail sh x))
                         (signed-byte-p (+ w (nfix sh)) x)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                              bitops::ihsext-inductions)))))


  (local (defthm logapp-of-logapp-ident
           (equal (logapp a x (logapp b (logtail a x) y))
                  (logapp (+ (nfix a) (nfix b)) x y))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                              bitops::ihsext-inductions)))))

  (local (defthm logapp-of-logtail-ident
           (equal (logapp a x (logtail a x))
                  (ifix x))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                              bitops::ihsext-inductions)))))



  (local (defthmd logext-of-equal-logapp-signed-byte
           (implies (and (equal y (logapp a b c))
                         (signed-byte-p (pos-fix x) y))
                    (equal (logext x y)
                           y))))

  (local (defthm dumb-lemma
           (implies (and (not (aig-eval (car rev-pos) env))
                         (< (ash 1 (len (cdr rev-pos))) width))
                    (and (<= (aig-list->u (rev rev-pos) env) width)
                         (< (aig-list->u (rev rev-pos) env) width)))))
  
  (local (defthm bitops::signed-byte-p-of-equal-logapp
           (implies (and (equal x (logapp size i j))
                         (integerp size1)
                         (<= (nfix size) size1)
                         (signed-byte-p (- size1 (nfix size))
                                        j))
                    (signed-byte-p size1 x))))

  (local (acl2::use-trivial-ancestors-check))

  (local (defthm len-minus-1
           (implies (consp x)
                    (equal (+ -1 (len x))
                           (len (cdr x))))
           :hints(("Goal" :in-theory (enable len)))))


  (defthm aig-overlap-width-ss-aux-correct
    (implies (and (signed-byte-p (pos-fix width) (aig-list->s x env))
                  (signed-byte-p (pos-fix width) (aig-list->s y env)))
             (equal (aig-list->s (aig-overlap-width-ss-aux rev-pos pos-len x y width) env)
                    (b* ((pos (aig-list->u (rev rev-pos) env)))
                      (logext width
                              (logapp pos
                                      (aig-list->s x env)
                                      (logtail pos (aig-list->s y env)))))))
    :hints (("Goal" :induct (aig-overlap-width-ss-aux rev-pos pos-len x y width)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable logext-of-logapp-split
                                      logext-of-equal-logapp-signed-byte))))))


(define aig-overlap-width-ss ((pos true-listp)
                              (x true-listp)
                              (y true-listp)
                              (width posp))
  :parents (a4vec-part-install)
  :short "Symbolic function that replaces @('pos') lower bits of @('y') with bits of @('x')."
  :long "<p>Symbolically computes:</p>
@({
 (logext width (logapp pos x (logtail pos y)))
 })

<p>where all variables except @('width') are symbolic.  I.e., it replaces the
lowermost @('pos') bits of @('y') with the corresponding bits of @('x').</p>"
  (b* ((width (lposfix width))
       (same-signp (hons-equal (aig-sign-s x)
                               (aig-sign-s y)))
       (width (if same-signp
                  (min (+ 1 (max (len x) (len y))) width)
                width))
       (y-ext (aig-logext-ns width y)))
    (aig-ite-bss (aig-sign-s pos)
                 y-ext
                 (b* ((rev-pos (cdr (rev pos))))
                   (aig-overlap-width-ss-aux rev-pos (len rev-pos)
                                             (aig-logext-ns width x)
                                             y-ext
                                             width))))
  ///
  (local (defthm logapp-when-zp
           (implies (zp width)
                    (equal (logapp width x y) (ifix y)))
           :hints(("Goal" :in-theory (enable bitops::logapp**)))))

  (local (defthm logtail-when-zp
           (implies (zp width)
                    (equal (logtail width x) (ifix x)))
           :hints(("Goal" :in-theory (enable bitops::logtail**)))))

  (local (defthm butlast-of-rev
           (equal (butlast (rev x) 1)
                  (rev (cdr x)))
           :hints(("Goal" :in-theory (enable rev)))))

  (local (defthm rev-cdr-rev
           (equal (rev (cdr (rev x)))
                  (if (consp x)
                      (butlast x 1)
                    nil))
           :hints (("Goal" :use ((:instance butlast-of-rev (x (rev x))))
                    :in-theory (disable butlast-of-rev)))))

  (local (defthm aig-list->s-when-not-consp
           (implies (atom x)
                    (equal (aig-list->s x env) 0))
           :hints(("Goal" :in-theory (enable aig-list->s)))))

  (local (defthm aig-list->s-when-len-lte-1
           (implies (and (<= (len x) 1)
                         (<= 0 (aig-list->s x env)))
                    (equal (aig-list->s x env) 0))
           :hints(("Goal" :in-theory (enable aig-list->s len gl::s-endp)))))

  (local (in-theory (disable butlast)))

  (local (defthm logext-logapp-logext
           (equal (logext width (logapp n (logext width x) y))
                  (logext width (logapp n x y)))
           :hints ((logbitp-reasoning))))

  (local (defthm logext-logapp-logtail-logext
           (equal (logext width (logapp n x (logtail n (logext width y))))
                  (logext width (logapp n x (logtail n y))))
           :hints ((logbitp-reasoning))))


  ;; (local (defthm len-equal-0
  ;;          (equal (equal (len x) 0) (atom x))))

  ;; (local (defthm aig-list->u-of-butlast
  ;;          (implies (< (aig-list->s x env) 0)
  ;;                   (= (aig-list->u (butlast x 1) env)
  ;;                      (+ (aig-list->s x env)
  ;;                         (ash 1 (1- (len x))))))
  ;;          :hints(("Goal" :in-theory (e/d (aig-list->s aig-list->u
  ;;                                                      gl::scdr
  ;;                                                      gl::s-endp)
  ;;                                         (butlast))
  ;;                  :induct t)
  ;;                 (and stable-under-simplificationp
  ;;                      '(:in-theory (e/d (logcons) (butlast))
  ;;                        :expand ((:free (x) (ash 1 (len (cdr x))))))))))

  (local (defthm aig-list->u-of-butlast-when-nonneg
           (implies (<= 0 (aig-list->s x env))
                    (= (aig-list->u (butlast x 1) env)
                       (aig-list->s x env)))
           :hints(("Goal" :in-theory (e/d (aig-list->s aig-list->u
                                                       gl::scdr
                                                       gl::s-endp
                                                       butlast-redef)
                                          (butlast))
                   :induct t)
                  (and stable-under-simplificationp
                       '(:in-theory (e/d (logcons) (butlast))
                         :expand ((:free (x) (ash 1 (len (cdr x))))))))))


  (local (defthm logext-past-integer-length
           (implies (< (integer-length x) (pos-fix w))
                    (equal (logext w x) (ifix x)))
           :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs
                                              ihsext-inductions
                                              pos-fix)))))


  (local (defthm integer-length-of-aig-list->s-bound
           (<= (integer-length (aig-list->s x env)) (len x))
           :hints(("Goal" :in-theory (enable* aig-list->s
                                              ihsext-recursive-redefs
                                              gl::scdr gl::s-endp)))
           :rule-classes :linear))
  
  ;; (local (defthm logext-of-aig-list->s
  ;;          (implies (< (len y) (pos-fix w))
  ;;                   (equal (logext w (aig-list->s y env))
  ;;                          (aig-list->s y env)))))

  (local (defthmd signed-byte-p-by-integer-length
           (implies (and (< (integer-length x) w)
                         (posp w)
                         (integerp x))
                    (signed-byte-p w x))
           :hints(("Goal" :in-theory (e/d* (ihsext-recursive-redefs
                                            ihsext-inductions)
                                           (signed-byte-p))
                   :induct t))))
                    

  (local (defthm signed-byte-p-of-aig-list->s
           (implies (and (< (len y) w)
                         (posp w))
                    (signed-byte-p w (aig-list->s y env)))
           :hints (("goal" :in-theory (disable signed-byte-p
                                               signed-byte-p-by-integer-length)
                    :use ((:instance signed-byte-p-by-integer-length
                           (x (aig-list->s y env))))))))

  (local (defthmd integer-length-of-loghead-nonneg
           (implies (<= 0 (ifix x))
                    (<= (integer-length (loghead n x))
                        (integer-length x)))
           :hints(("Goal" :in-theory (e/d* (ihsext-recursive-redefs
                                            ihsext-inductions))))
           :rule-classes :linear))

  (local (defthmd integer-length-of-logapp-neg-1
           (implies (< (ifix x) 0)
                    (<= (integer-length (logapp n x -1))
                        (integer-length x)))
           :hints(("Goal" :in-theory (e/d* (ihsext-recursive-redefs
                                            ihsext-inductions))))
           :rule-classes :linear))

  (local (defthm integer-length-of-logapp-same-sign
           (implies (iff (< (ifix x) 0)
                         (< (ifix y) 0))
                    (<= (integer-length (logapp w x (logtail w y)))
                        (max (integer-length x)
                             (integer-length y))))
           :hints (("goal" :in-theory (enable* ihsext-recursive-redefs
                                               ihsext-inductions
                                               integer-length-of-loghead-nonneg
                                               integer-length-of-logapp-neg-1)))
           :rule-classes
           ((:rewrite :corollary
             (implies (and (iff (< (ifix x) 0)
                                (< (ifix y) 0))
                           (<= (max (integer-length x)
                                    (integer-length y))
                               len))
                    (<= (integer-length (logapp w x (logtail w y))) len)))
            (:rewrite :corollary
             (implies (and (iff (< (ifix x) 0)
                                (< (ifix y) 0))
                           (< (max (integer-length x)
                                    (integer-length y))
                              len))
                      (< (integer-length (logapp w x (logtail w y))) len)))
            :linear)))

  (local (defthm max-when-<
           (implies (< x y) (equal (max x y) y))))

  (local (defthm max-when->
           (implies (< x y) (equal (max y x) y))))

  (local (Defthm <-x-x
           (not (< x x))))

  (local (defthm max-integer-length-of-aig-list->s
           (implies (<= (+ 1 (max (len x) (len y))) w)
                    (< (max (integer-length (aig-list->s x env))
                            (integer-length (aig-list->s y env)))
                       w))))

  (local (Defthm integer-length-of-logtail
           (equal (integer-length (logtail n x))
                  (nfix (- (integer-length x) (nfix n))))
           :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs
                                              ihsext-inductions)))))

  ;; (local (defthm equal-of-logexts-above-integer-length
  ;;          (implies (and (< (integer-length x) (pos-fix w1))
  ;;                        (< (integer-length x) (pos-fix w2)))
  ;;                   (equal (equal (logext w1 x) (logext w2 x))
  ;;                          t))
  ;;          :hints ((logbitp-reasoning))))

  (local (defthmd signs-same-implies-signs-same
           (implies (Equal (aig-sign-s x) (aig-sign-s y))
                    (iff (< (aig-list->s x env) 0)
                         (< (aig-list->s y env) 0)))
           :hints (("goal" :use ((:instance aig-sign-s-correct (env env))
                                 (:instance aig-sign-s-correct (x y) (env env)))
                    :in-theory (disable aig-sign-s-correct)))))


  ;; (local (defthm sign-of-logtail
  ;;          (iff (< (logtail n x) 0)
  ;;               (< (ifix x) 0))
  ;;          :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs
  ;;                                             ihsext-inductions)))))

  ;; (local (defthm equal-of-logexts-of-logapps
  ;;          (implies (and (< (integer-length x) (pos-fix w1))
  ;;                        (< (integer-length y) (pos-fix w1))
  ;;                        (< (integer-length x) (pos-fix w2))
  ;;                        (< (integer-length y) (pos-fix w2))
  ;;                        (iff (< (ifix x) 0)
  ;;                             (< (ifix y) 0)))
  ;;                   (equal (equal (logext w1 (logapp n x (logtail n y)))
  ;;                                 (logext w2 (logapp n x (logtail n y))))
  ;;                          t))
  ;;          :hints (("goal" :use ((:instance integer-length-of-logapp-same-sign
  ;;                                 (w n)))
  ;;                   :in-theory (disable integer-length-of-logapp-same-sign)))))

  (local (in-theory (disable max)))

  (defthm aig-overlap-width-ss-correct
    (equal (aig-list->s (aig-overlap-width-ss pos x y width) env)
           (b* ((pos (aig-list->s pos env)))
             (logext width
                     (logapp pos
                             (aig-list->s x env)
                             (logtail pos (aig-list->s y env))))))
    :hints ((and stable-under-simplificationp
                 '(:use signs-same-implies-signs-same))
            (and stable-under-simplificationp
                 '(:in-theory (enable max))))))



(define aig-right-shift-ss ((place posp) (n true-listp) (shamt true-listp))
  :parents (a4vec-rsh)
  (b* (((mv shdig shrst shend) (gl::first/rest/end shamt))
       (place (lposfix place))
       ((when shend)
        (aig-logtail-ns 1 n))
       (rst (aig-right-shift-ss (* 2 place) n shrst)))
    (aig-ite-bss shdig rst (aig-logtail-ns place rst)))
  ///
  (local (defthm logtail-of-equal-to-ash
           (implies (equal x (ash a b))
                    (equal (logtail n x)
                           (ash a (+ (ifix b) (- (nfix n))))))
           :hints(("Goal" :in-theory (enable bitops::logtail-of-ash)))))

  (local (defthm minus-plus-2x
           (equal (+ (- a) (* 2 a) b)
                  (+ a b))))

  (local (defthm a+a+b
           (equal (+ a a b)
                  (+ (* 2 a) b))))

  (defthm aig-right-shift-ss-correct
    (implies (< (aig-list->s shamt env) 0)
             (equal (aig-list->s (aig-right-shift-ss place n shamt) env)
                    (ash (aig-list->s n env)
                         (+ -1 (pos-fix place)
                            (* (pos-fix place)
                               (aig-list->s shamt env))))))
    :hints (("goal" :induct t
             :in-theory (enable acl2::logcons)
             :expand ((aig-list->s shamt env))))))

(define aig-force-sign-s ((sign)
                          (x true-listp))
  :returns (new-x true-listp :rule-classes :type-prescription)
  (b* (((mv first rest end) (gl::first/rest/end x))
       ((when end) (list sign)))
    (aig-scons first (aig-force-sign-s sign rest)))
  ///
  (defret <fn>-correct
    (implies (equal (aig-eval (aig-sign-s x) env)
                    (aig-eval sign env))
             (equal (aig-list->s (aig-force-sign-s sign x) env)
                    (aig-list->s x env)))
    :hints(("Goal" :in-theory (enable aig-sign-s
                                      gl::s-endp)
            :expand ((:free (a b) (aig-list->s (cons a b) env))
                     (aig-list->s x env))))))
    
(define a4vec-rsh ((amt  a4vec-p  "Right-shift amount.")
                   (x    a4vec-p  "Vector to shift.")
                   (mask 4vmask-p "Care mask for the result."))
  :short "Symbolic version of @(see 4vec-rsh)."
  :long "<p>As a special consideration, we use the care mask to try to avoid
creating enormous vectors when given a huge shift amount.</p>"
  :returns (res a4vec-p)
  (b* (((a4vec amt))
       ((a4vec x))
       (mask (4vmask-fix mask)))
    ;; BOZO we probably can rework this to avoid doing a unary minus on the shift amount.
    (a4vec-ite (a2vec-p amt)
               ;; Valid shift amount.
               (b* ((shamt (aig-unary-minus-s amt.upper))
                    ((when (sparseint-equal 0 mask)) (a4vec-x))
                    ((when (sparseint-< 0 mask))
                     (b* ((maskwidth (+ 1 (sparseint-length mask)))
                          (upper (aig-head-of-concat shamt (aig-sterm nil) x.upper maskwidth))
                          (lower (aig-head-of-concat shamt (aig-sterm nil) x.lower maskwidth)))
                       (a4vec upper lower)))
                    (- (and (not (a4vec-constantp amt))
                            (cw "Warning: bitblasting variable rightshift under unbounded mask~%")))
                    (sign  (aig-sign-s shamt))
                    ((mv upper-left lower-left)
                     (if (eq sign t)
                         (mv nil nil)
                       (b* ((lsh-amt (aig-force-sign-s nil shamt)))
                         (mv (aig-ash-ss 1 x.upper lsh-amt)
                             (aig-ash-ss 1 x.lower lsh-amt)))))
                    ((mv upper-right lower-right)
                     (if (not sign)
                         (mv nil nil)
                       (b* ((rsh-amt (aig-force-sign-s t shamt)))
                         (mv (aig-right-shift-ss 1 x.upper rsh-amt)
                             (aig-right-shift-ss 1 x.lower rsh-amt))))))
                 (a4vec (aig-ite-bss-fn sign upper-right upper-left)
                        (aig-ite-bss-fn sign lower-right lower-left)))
               ;; X/Z bits in shift amount, just return all Xes.
               (a4vec-x)))
  ///

  (defthm a4vec-rsh-correct
    (4vec-mask-equiv (a4vec-eval (a4vec-rsh amt x mask) env)
                     (4vec-rsh (a4vec-eval amt env)
                               (a4vec-eval x env))
                     mask)
    :hints (("Goal" :expand ((:free (x) (hide x)))
             :in-theory '(equal-of-4vec-mask?-when-equal-under-mask)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:expand nil
                   :in-theory (e/d (4vec-rsh 4vec-shift-core 4vec-mask)
                                   (aig-sign-s-correct))
                   :use ((:instance aig-sign-s-correct
                          (x (aig-unary-minus-s (a4vec->upper amt)))
                          (gl::env env))))))
    :otf-flg t))


(define a4vec-part-install ((lsb   a4vec-p "LSB of the range to write -- may be negative")
                            (width a4vec-p "Width of the range to write")
                            (in    a4vec-p "input in which the range gets written")
                            (val   a4vec-p "value to write to the range")
                            (mask  4vmask-p))

  :prepwork ((local (defthm aig-and-implies-nonnil
                      (implies (aig-and a b)
                               (and a b))
                      :hints(("Goal" :in-theory (enable aig-and)))
                      :rule-classes :forward-chaining))
             (local (Defthm aig-not-implies-non-t
                      (implies (aig-not x)
                               (not (equal x t)))
                      :hints(("Goal" :in-theory (enable aig-not)))
                      :rule-classes :forward-chaining)))

  :returns (partsel a4vec-p)

  (b* (((a4vec width))
       ((a4vec lsb))
       ((a4vec in))
       ((a4vec val))
       (mask (4vmask-fix mask))
       ((when (sparseint-equal mask 0))
        ;; [Jared] this was previously using 4vec-0.  I think it's probably
        ;; better to use 4vec-x, in general, since for instance many
        ;; arithmetic operations check a2vec-p and then do something really
        ;; simple in the "nope, not a 2vec, may as well just return all xes."
        (a4vec-x)))
    (a4vec-ite
     (aig-and (a2vec-p lsb)
              (aig-and (a2vec-p width)
                       (aig-not (aig-sign-s width.upper)))) 
     (b* (((unless (sparseint-< 0 mask))
           (and (not (and (a4vec-constantp width)
                          (a4vec-constantp lsb)))
                (cw "Warning: bitblasting variable part install under unbounded mask~%"))
           (a4vec-ite (aig-sign-s lsb.upper)
                      (a4vec-rsh (let ((minus-lsb (aig-unary-minus-s lsb.upper)))
                                   (a4vec minus-lsb minus-lsb))
                                 (a4vec-concat
                                  width val (a4vec-rsh
                                             (let ((sum (aig-+-ss nil lsb.upper width.upper)))
                                               (a4vec sum sum))
                                             in -1) -1)
                                 mask)
                      (a4vec-concat
                       lsb in
                       (a4vec-concat
                        width val (a4vec-rsh (let ((sum (aig-+-ss nil lsb.upper width.upper)))
                                               (a4vec sum sum))
                                             in -1) -1)
                       mask)))
          (maskwidth (+ 1 (sparseint-length mask)))
          ;; first concatenate the lower bits of x with the val, not truncated at width
          (lsbs.upper (aig-head-of-concat lsb.upper in.upper val.upper maskwidth))
          (lsbs.lower (aig-head-of-concat lsb.upper in.lower val.lower maskwidth))
          ;; now overlap these LSBs width in at (lsb + width)
          (overlap-idx (aig-+-ss nil lsb.upper width.upper))
          (overlap.upper (aig-overlap-width-ss overlap-idx lsbs.upper in.upper maskwidth))
          (overlap.lower (aig-overlap-width-ss overlap-idx lsbs.lower in.lower maskwidth)))
       (a4vec overlap.upper overlap.lower))
     (a4vec-x)))
  ///
  (local (defthm logext-past-integer-length
           (implies (< (integer-length x) (pos-fix w))
                    (equal (logext w x) (ifix x)))
           :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs
                                              ihsext-inductions
                                              pos-fix)))))

  (local (Defthm integer-length-of-logtail
           (equal (integer-length (logtail n x))
                  (nfix (- (integer-length x) (nfix n))))
           :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs
                                              ihsext-inductions)))))
  

  (local (defthm logapp-of-logapp-less
           (implies (<= (nfix w2) (nfix w1))
                    (equal (logapp w1 (logapp w2 x y) z)
                           (logapp w2 x (logapp (- (nfix w1) (nfix w2)) y z))))
           :hints ((logbitp-reasoning))))

  ;; (local (defthm logior-lognot-of-logapp-logapp
  ;;          (implies (<= 0 (ifix mask))
  ;;                   (equal (logior (lognot mask)
  ;;                                  (logapp w1 x (logapp w2 y (logext (+ 1 (integer-length mask)
  ;;                                                                       minus-w1)
  ;;                                                                    z)

  (local (defthm logbitp-past-integer-length-when-nonneg
           (implies (and (<= 0 (ifix mask))
                         (<= (+ 1 (integer-length mask)) (nfix bit)))
                    (not (logbitp bit mask)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                              bitops::ihsext-inductions)))))

  (local (defthm logior-of-logext-mask
           (implies (<= 0 (ifix mask))
                    (equal (logior (lognot mask)
                                   (logext (+ 1 (integer-length mask)) x))
                           (logior (lognot mask) x)))
           :hints ((logbitp-reasoning))))

  (local (defthm logior-of-logapp-logext-mask
           (implies (<= 0 (ifix mask))
                    (equal (logior (lognot mask)
                                   (logapp w (logext (+ 1 (integer-length mask)) x) y))
                           (logior (lognot mask) (logapp w x y))))
           :hints ((logbitp-reasoning))))

  (local (defthm logand-of-logext-mask
           (implies (<= 0 (ifix mask))
                    (equal (logand mask
                                   (logext (+ 1 (integer-length mask)) x))
                           (logand mask x)))
           :hints ((logbitp-reasoning))))

  (local (defthm logand-of-logapp-logext-mask
           (implies (<= 0 (ifix mask))
                    (equal (logand mask
                                   (logapp w (logext (+ 1 (integer-length mask)) x) y))
                           (logand mask (logapp w x y))))
           :hints ((logbitp-reasoning))))

  (local (defthm logapp-when-zp
           (implies (zp w)
                    (equal (logapp w x y) (ifix y)))
           :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs)))))

  (local (defthm logtail-when-zp
           (implies (zp w)
                    (equal (logtail w x) (ifix x)))
           :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs)))))

  (defthm a4vec-part-install-correct
    (4vec-mask-equiv (a4vec-eval (a4vec-part-install lsb width in val mask) env)
                     (4vec-part-install (a4vec-eval lsb env)
                                              (a4vec-eval width env)
                                              (a4vec-eval in env)
                                              (a4vec-eval val env))
                     mask)
    :hints(("Goal" :expand ((:free (x) (hide x)))
             :in-theory '(equal-of-4vec-mask?-when-equal-under-mask)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:expand nil
                   :in-theory (enable 4vec-part-install)))
            (and stable-under-simplificationp
                 '(:in-theory (enable  4vec-zero-ext 4vec-rsh 4vec-shift-core 4vec-concat 4vec-mask))))))


                                                                 



(define a4vec-sign-ext ((n a4vec-p)
                        (x a4vec-p)
                        (mask 4vmask-p))
  :short "Symbolic version of @(see 4vec-sign-ext)."
  :long "<p>We essentially just extract the sign bit, sign extend it, and then
use @(see a4vec-concat) to carry out the concatenation, since it already
provides special optimization to avoid problems due to large masks.</p>"
  :returns (res a4vec-p)
  (b* (((a4vec n) n)
       ((a4vec x) x))
    (a4vec-ite (aig-and (a2vec-p n) ;; X/Z free?
                        (aig-nor (aig-sign-s n.upper) ;; Negative index?
                                 (aig-=-ss n.upper (aig-sterm nil)) ;; Zero index?
                                 ))

               ;; Index is properly X/Z free and positive.
               (b* (;; Subtract one from the index to get the sign position.
                    (signpos (aig-+-ss nil (aig-sterm t) n.upper))
                    ;; Extract the sign bit from upper and lower, and sign
                    ;; extend them to infinity, creating a new high vector to
                    ;; concatenate onto the low bits of X.
                    (high-bits (a4vec (aig-sterm (aig-logbitp-n2v 1 signpos x.upper))
                                      (aig-sterm (aig-logbitp-n2v 1 signpos x.lower)))))
                 ;; Concatenate these new high bits onto the low bits.
                 (a4vec-concat n x high-bits mask))

               ;; Invalid index, just return all Xes
               (a4vec-x)))
  ///
  (local (in-theory (enable a4vec-sign-ext)))

  (local (defthm logext-formulation
           (implies (and (posp n)
                         (integerp x))
                    (equal (logapp n
                                   x
                                   (bool->vec (logbitp (+ -1 n) x)))
                           (logext n x)))
           :hints((bitops::logbitp-reasoning))))

  (defthm a4vec-sign-ext-correct
    (4vec-mask-equiv (a4vec-eval (a4vec-sign-ext n x mask) env)
                     (4vec-sign-ext (a4vec-eval n env)
                                    (a4vec-eval x env))
                     mask)
    :hints(("Goal" :expand ((:free (x) (hide x)))
             :in-theory '(equal-of-4vec-mask?-when-equal-under-mask)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:expand nil
                   :in-theory (enable 4vec-sign-ext 4vec-concat))))))




(define a4vec-lsh ((amt a4vec-p)
                   (x a4vec-p)
                   (mask 4vmask-p))
  :short "Symbolic version of @(see 4vec-lsh)."
  :returns (res a4vec-p)
  (b* (((a4vec amt))
       ((a4vec x))
       (mask (4vmask-fix mask)))
    (a4vec-ite (a2vec-p amt)
               ;; Valid shift amount.  In our semantics, left-shifting by a
               ;; negative is right-shifting, so we care about the sign.
               (b* ((shamt amt.upper)
                    (sign  (aig-sign-s shamt))

                    ((mv upper-left lower-left)
                     ;; Compute the upper/lower answer vectors in the left-shift case.
                     (b* (((when (eq sign t))
                           ;; We're definitely right-shifting, so left-shift answers
                           ;; don't matter, don't bother doing anything.
                           (mv nil nil))
                          (lsh-amt
                           ;; Try to defend against catastrophically large
                           ;; shift amounts by reducing the shift amount by
                           ;; the mask.
                           (if (sparseint-< mask 0)
                               shamt
                             (aig-logcollapse-ns (integer-length (sparseint-length mask))
                                                 shamt))))
                       (mv (aig-ash-ss 1 x.upper lsh-amt)
                           (aig-ash-ss 1 x.lower lsh-amt))))

                    ((mv upper-right lower-right)
                     ;; Compute the upper/lower answer vectors in the right-shift case.
                     ;; Since we're right-shifting, we don't have to worry about shifting
                     ;; by too much, so this is pretty simple.
                     (if (not sign)
                         (mv nil nil)
                       (mv (aig-right-shift-ss 1 x.upper shamt)
                           (aig-right-shift-ss 1 x.lower shamt))))

                    (upper (aig-ite-bss-fn sign upper-right upper-left))
                    (lower (aig-ite-bss-fn sign lower-right lower-left)))

                 (a4vec upper lower))

               ;; X/Z bits in shift amount, just return all Xes.
               (a4vec-x)))
  ///

  (defthm a4vec-lsh-correct
    (4vec-mask-equiv (a4vec-eval (a4vec-lsh amt x mask) env)
                     (4vec-lsh (a4vec-eval amt env)
                               (a4vec-eval x env))
                     mask)
    :hints(("Goal" :expand ((:free (x) (hide x)))
            :in-theory '(equal-of-4vec-mask?-when-equal-under-mask)
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:expand nil
                  :in-theory (e/d (4vec-lsh 4vec-shift-core 4vec-mask)
                                  (aig-sign-s-correct))
                  :use ((:instance aig-sign-s-correct
                         (x (a4vec->upper amt))
                         (gl::env env))))))
    :otf-flg t))



(define aig-rev-blocks-nns ((nbits natp)
                            (blocksz posp)
                            (x true-listp))
  :parents (a4vec-rev-blocks)
  (b* ((nbits   (lnfix nbits))
       (blocksz (lposfix blocksz))
       ((when (< nbits blocksz))
        (aig-loghead-ns nbits x))
       (next-nbits (- nbits blocksz))
       (rest (aig-rev-blocks-nns next-nbits blocksz (aig-logtail-ns blocksz x))))
    (aig-logapp-nss next-nbits rest (aig-loghead-ns blocksz x)))
  ///
  (defthm aig-rev-blocks-nns-correct
    (equal (aig-list->s (aig-rev-blocks-nns nbits blocksz x) env)
           (rev-blocks nbits blocksz (aig-list->s x env)))
    :hints (("goal" :induct (aig-rev-blocks-nns nbits blocksz x)
             :expand ((:free (x) (rev-blocks nbits blocksz x)))))))

(define aig-rev-blocks-nss ((nbits natp)
                            (blocksz-lowbits natp)
                            (blocksz-bitidx natp)
                            (blocksz true-listp)
                            (x true-listp))
  :parents (a4vec-rev-blocks)
  :prepwork ((local (in-theory (disable unsigned-byte-p))))
  :guard (unsigned-byte-p blocksz-bitidx blocksz-lowbits)
  (b* (((mv head tail end) (gl::first/rest/end blocksz))
       (lowbits (mbe :logic (loghead blocksz-bitidx (nfix blocksz-lowbits))
                     :exec blocksz-lowbits))
       ((when end)
        (aig-ite-bss head
                     ;; negative: revert to 1
                     (aig-rev-blocks-nns nbits 1 x)
                     ;; nonnegative
                     (aig-rev-blocks-nns nbits (pos-fix lowbits) x))))
    (aig-ite-bss head
                 (aig-rev-blocks-nss nbits
                                     (logior (ash 1 (lnfix blocksz-bitidx))
                                             lowbits)
                                     (+ 1 (lnfix blocksz-bitidx))
                                     tail
                                     x)
                 (aig-rev-blocks-nss nbits
                                     lowbits
                                     (+ 1 (lnfix blocksz-bitidx))
                                     tail
                                     x)))
  ///
  (local (defthm ash-of-logcons
           (implies (natp n)
                    (equal (ash (bitops::logcons b x) n)
                           (logior (ash (bitops::bfix b) n)
                                   (bitops::logcons 0 (ash x n)))))
           :hints(("Goal" :in-theory (enable* bitops::ash**
                                              bitops::ihsext-inductions)))))

  (local (defthm pos-fix-nfix
           (equal (acl2::pos-fix (nfix x))
                  (acl2::pos-fix x))
           :hints(("Goal" :in-theory (enable acl2::pos-fix)))))

  (local (defthm rev-blocks-of-nfix-blocksz
           (equal (rev-blocks nbits (nfix blocksz) x)
                  (rev-blocks nbits blocksz x))
           :hints(("Goal" :in-theory (enable (:i rev-blocks))
                   :induct (rev-blocks nbits blocksz x)
                   :expand ((:free (blocksz) (rev-blocks nbits blocksz x)))))))

  (local (defthm rev-blocks-of-nonpositive
           (implies (not (posp blocksz))
                    (equal (rev-blocks nbits blocksz x)
                           (rev-blocks nbits 1 x)))
           :hints(("Goal" :in-theory (enable (:i rev-blocks) acl2::pos-fix)
                   :induct (rev-blocks nbits blocksz x)
                   :expand ((:free (blocksz) (rev-blocks nbits blocksz x)))))))

  (local (defthm not-posp-when-negative
           (implies (< x 0)
                    (not (posp x)))))

  (defthm aig-rev-blocks-nss-correct
    (equal (aig-list->s (aig-rev-blocks-nss nbits
                                            blocksz-lowbits
                                            blocksz-bitidx
                                            blocksz
                                            x)
                        env)
           (rev-blocks nbits (logior (loghead blocksz-bitidx (nfix blocksz-lowbits))
                                     (ash (aig-list->s blocksz env)
                                          (nfix blocksz-bitidx)))
                       (aig-list->s x env)))
    :hints (("goal" :induct (aig-rev-blocks-nss nbits
                                                blocksz-lowbits
                                                blocksz-bitidx
                                                blocksz
                                                x
                                                )
             :in-theory (enable bitops::ash-<-0-linear))
            (and stable-under-simplificationp
                 '(:expand ((aig-list->s blocksz env)
                            (:free (x n) (ash x (+ 1 n)))
                            (:free (x n) (loghead (+ 1 n) x))))))))


(define aig-rev-blocks-sss ((nbits-lowbits natp)
                            (nbits-bitidx natp)
                            (nbits true-listp)
                            (blocksz true-listp)
                            (x true-listp))
  :prepwork ((local (in-theory (disable unsigned-byte-p))))
  :guard (unsigned-byte-p nbits-bitidx nbits-lowbits)
  (b* (((mv head tail end) (gl::first/rest/end nbits))
       (lowbits (mbe :logic (loghead nbits-bitidx (nfix nbits-lowbits))
                     :exec nbits-lowbits))
       ((when end)
        (aig-ite-bss head
                     ;; negative: revert to 0
                     (aig-rev-blocks-nss 0 0 0 blocksz x)
                     ;; nonnegative
                     (aig-rev-blocks-nss lowbits 0 0 blocksz x))))
    (aig-ite-bss head
                 (aig-rev-blocks-sss (logior
                                      (ash 1 (lnfix nbits-bitidx))
                                      lowbits)
                                     (+ 1 (lnfix nbits-bitidx))
                                     tail
                                     blocksz
                                     x)
                 (aig-rev-blocks-sss lowbits
                                     (+ 1 (lnfix nbits-bitidx))
                                     tail
                                     blocksz
                                     x)))
  ///
  (local (defthm ash-of-logcons
           (implies (natp n)
                    (equal (ash (bitops::logcons b x) n)
                           (logior (ash (bitops::bfix b) n)
                                   (bitops::logcons 0 (ash x n)))))
           :hints(("Goal" :in-theory (enable* bitops::ash**
                                              bitops::ihsext-inductions)))))

  (local (defthm pos-fix-nfix
           (equal (acl2::pos-fix (nfix x))
                  (acl2::pos-fix x))
           :hints(("Goal" :in-theory (enable acl2::pos-fix)))))

  (local (defthm rev-blocks-of-nfix-nbits
           (equal (rev-blocks (nfix nbits) blocksz x)
                  (rev-blocks nbits blocksz x))
           :hints(("Goal" :in-theory (enable (:i rev-blocks))
                   :induct (rev-blocks nbits blocksz x)
                   :expand ((:free (nbits blocksz) (rev-blocks nbits blocksz x)))))))

  (local (defthm rev-blocks-of-nonnat
           (implies (not (natp nbits))
                    (equal (rev-blocks nbits blocksz x)
                           (rev-blocks 0 blocksz x)))
           :hints(("Goal" :in-theory (enable (:i rev-blocks) acl2::pos-fix)
                   :induct (rev-blocks nbits blocksz x)
                   :expand ((:free (nbits blocksz) (rev-blocks nbits blocksz x)))))))

  (local (defthm not-posp-when-negative
           (implies (< x 0)
                    (not (posp x)))))

  (defthm aig-rev-blocks-sss-correct
    (equal (aig-list->s (aig-rev-blocks-sss nbits-lowbits
                                            nbits-bitidx
                                            nbits
                                            blocksz
                                            x)
                        env)
           (rev-blocks (logior (loghead nbits-bitidx (nfix nbits-lowbits))
                               (ash (aig-list->s nbits env)
                                    (nfix nbits-bitidx)))
                       (aig-list->s blocksz env)
                       (aig-list->s x env)))
    :hints (("goal" :induct (aig-rev-blocks-sss nbits-lowbits
                                                nbits-bitidx
                                                nbits
                                                blocksz
                                                x)
             :in-theory (enable bitops::ash-<-0-linear))
            (and stable-under-simplificationp
                 '(:expand ((aig-list->s nbits env)
                            (:free (x n) (ash x (+ 1 n)))
                            (:free (x n) (loghead (+ 1 n) x))))))))

(define a4vec-rev-blocks ((w a4vec-p)
                          (b a4vec-p)
                          (x a4vec-p))
  :short "Symbolic version of @(see 4vec-rev-blocks)."
  :returns (res a4vec-p)
  (b* (((a4vec w) w)
       ((a4vec b) b)
       ((a4vec x) x))
    (a4vec-ite (aig-and (a2vec-p w)
                        (aig-not (aig-sign-s w.upper))
                        (a2vec-p b)
                        (aig-not (aig-sign-s b.upper))
                        (aig-not (aig-=-ss b.upper nil)))
               (a4vec (aig-rev-blocks-sss 0 0 w.upper b.upper x.upper)
                      (aig-rev-blocks-sss 0 0 w.upper b.upper x.lower))
               (a4vec-x)))
  ///
  (defthm a4vec-rev-blocks-correct
    (equal (a4vec-eval (a4vec-rev-blocks w b x) env)
           (4vec-rev-blocks (a4vec-eval w env)
                            (a4vec-eval b env)
                            (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 4vec-rev-blocks)))))
