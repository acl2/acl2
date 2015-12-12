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
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
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
  :short "@(call a4vec-0) return an @(see a4vec) that evaluates to @(see
4vec-0) under every environment."
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

(define a4vec-mask-check ((mask 4vmask-p)
                          (idx natp)
                          (vec "aig list")
                          (upperp booleanp))
  :returns (already-maskedp booleanp)
  :measure (len vec)
  (b* (((mv first rest endp) (gl::first/rest/end vec))
       ((when endp)
        (or (equal (4vmask-fix mask) -1)
            (equal first (mbe :logic (acl2::bool-fix upperp) :exec upperp)))))
    (and (or (logbitp idx (4vmask-fix mask))
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
                            (equal (logior (lognot (logtail idx (4vmask-fix mask)))
                                           (aig-list->s vec env))
                                   (aig-list->s vec env)))
                   (implies (not upperp)
                            (equal (logand (logtail idx (4vmask-fix mask))
                                           (aig-list->s vec env))
                                   (aig-list->s vec env)))))
     :hints(("Goal" :in-theory (enable* aig-list->s aig-logior-ss aig-i2v
                                        bitops::ihsext-recursive-redefs)
             :induct (a4vec-mask-check mask idx vec upperp)
             :expand ((:with logtail-in-terms-of-logbitp
                       (LOGTAIL IDX (4VMASK-FIX mask))))
             ))
     :rule-classes nil))

  (defthmd a4vec-mask-check-correct
    (and (implies (a4vec-mask-check mask 0 vec t)
                  (equal (logior (lognot (4vmask-fix mask)) (aig-list->s vec env))
                         (aig-list->s vec env)))
         (implies (a4vec-mask-check mask 0 vec nil)
                  (equal (logand (4vmask-fix mask) (aig-list->s vec env))
                         (aig-list->s vec env))))
    :hints (("goal" :use ((:instance a4vec-mask-check-correct-lemma
                           (idx 0) (upperp t))
                          (:instance a4vec-mask-check-correct-lemma
                           (idx 0) (upperp nil)))))))


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
       (dontcare (lognot mask))
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


(define a4vec-wildeq-safe-aux ((a.upper "aig list")
                          (a.lower "aig list")
                          (b.upper "aig list")
                          (b.lower "aig list"))
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


(define a4vec-wildeq-aux ((a.upper "aig list")
                          (a.lower "aig list")
                          (b.upper "aig list")
                          (b.lower "aig list"))
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

(define aig-iszero-s (a)
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


(define logcollapse ((position natp)
                     (x integerp))
  :short "OR together all the bits of x at position or above, collapsing them
into the single bit at position."

  :long "<p>This operation helps avoid catastrophically large shifts in
computing, e.g., concatenations with symbolic widths.  When there is a
care-mask of width w, then we can collapse all the bits at w and above into the
bit at w, because the presence of those upper bits means that the shift is
longer than we care about.</p>

<p>There is a large potential for off-by-one errors when thinking about this
function.  It may help to start with the fact that @('(logcollapse 0 x)')
collapses all bits of x into a single bit.  In general, @('(logcollapse n x)')
results in at most n+1 bits.</p>"
  (b* ((position (lnfix position)))
    (logior (loghead position x)
            (ash (b-not (bool->bit (eql 0 (logtail position x)))) position))))

(local
 (defsection masked-shifts

   (local (defthm loghead-when-logtail-is-0
            (implies (equal 0 (logtail n x))
                     (equal (loghead n x) (ifix x)))
            :hints(("Goal" :in-theory (enable* acl2::loghead** acl2::logtail**
                                               acl2::ihsext-inductions)))))

   (local (defthm ash-integer-length-greater
            (implies (natp x)
                     (< x (ash 1 (integer-length x))))
            :hints(("Goal" :in-theory (enable* acl2::ash**
                                               acl2::integer-length**
                                               acl2::ihsext-inductions)))
            :rule-classes :linear))

   (local (defthm logior-of-nats-greater
            (implies (and (natp x) (natp y))
                     (<= x (logior x y)))
            :hints(("Goal" :in-theory (enable* acl2::logior**
                                               acl2::ihsext-inductions)))
            :rule-classes :linear))

   (defthm logcollapse-greater-when-greater
     (implies (and (natp m)
                   (integerp i)
                   (<= m i))
              (<= m
                  (logcollapse (integer-length m) i)))
     :hints(("Goal" :in-theory (enable logcollapse bool->bit))))

   (local (defthm logtail-integer-length-when-less
            (implies (and (integerp m)
                          (natp i)
                          (< i m))
                     (equal (logtail (integer-length m) i) 0))
            :hints(("Goal" :in-theory (enable* acl2::logtail**
                                               acl2::integer-length**
                                               acl2::ihsext-inductions)
                    :induct (logand m i)))))

   (defthm logcollapse-equal-when-less
     (implies (and (integerp m)
                   (natp i)
                   (< i m))
              (equal (logcollapse (integer-length m) i)
                     i))
     :hints(("Goal" :in-theory (enable logcollapse bool->bit))))


   ;; Example.  Suppose our mask is #xab and we are computing (concat n a b).
   ;; Whenever n is greater than or equal the length of the mask, 8, the answer is
   ;; just a, as far as we're concerned.  We can transform n however we like as
   ;; long as we preserve its value when less than 8, and we leave it >= 8 if it
   ;; is >= 8.  In particular, we can logcollapse it in such a way that this
   ;; holds: i.e., to the length of 8, or the length of the length of the mask.

   (defthm loghead-of-ash-greater
     (implies (and (natp i)
                   (integerp j)
                   (<= i j))
              (equal (loghead i (ash x j))
                     0))
     :hints(("Goal" :in-theory (enable* acl2::loghead** acl2::ash**
                                        acl2::ihsext-inductions))))

   (local (defun mask-equiv-ind (mask x y)
            (if (zp mask)
                (list x y)
              (mask-equiv-ind (logcdr mask) (logcdr x) (logcdr y)))))

   (defthm maskedvals-equiv-when-logheads-equiv
     (implies (and (natp mask)
                   (equal (loghead (integer-length mask) x)
                          (loghead (integer-length mask) y)))
              (equal (equal (logand mask x)
                            (logand mask y))
                     t))
     :hints(("Goal" :in-theory (enable* acl2::loghead** acl2::logand**
                                        acl2::integer-length**)
             :induct (mask-equiv-ind mask x y))))

   (defthm maskedvals-equiv-when-logheads-equiv-logior
     (implies (and (natp mask)
                   (equal (loghead (integer-length mask) x)
                          (loghead (integer-length mask) y)))
              (equal (equal (logior (lognot mask) x)
                            (logior (lognot mask) y))
                     t))
     :hints(("Goal" :in-theory (enable* acl2::loghead** acl2::logior** acl2::lognot**
                                        acl2::integer-length**)
             :induct (mask-equiv-ind mask x y))))


   (defthm mask-ash-of-logcollapse
     (implies (and (natp mask)
                   (natp shift))
              (equal (logand mask (ash x (logcollapse (integer-length (integer-length mask))
                                                      shift)))
                     (logand mask (ash x shift))))
     :hints (("goal" :cases ((<= (integer-length mask) shift)))))

   (defthm mask-ash-of-logcollapse
     (implies (and (natp mask)
                   (natp shift))
              (equal (logand mask (ash x (logcollapse (integer-length (integer-length mask))
                                                      shift)))
                     (logand mask (ash x shift))))
     :hints (("goal" :cases ((<= (integer-length mask) shift)))))

   (defthm logior-mask-ash-of-logcollapse
     (implies (and (natp mask)
                   (natp shift))
              (equal (logior (lognot mask) (ash x (logcollapse (integer-length (integer-length mask))
                                                               shift)))
                     (logior (lognot mask) (ash x shift))))
     :hints (("goal" :cases ((<= (integer-length mask) shift)))))

   (defthm mask-logapp-of-logcollapse
     (implies (and (natp mask)
                   (natp width))
              (equal (logand mask (logapp (logcollapse (integer-length (integer-length mask))
                                                       width)
                                          x y))
                     (logand mask (logapp width x y))))
     :hints (("goal" :cases ((<= (integer-length mask) width)))))

   (defthm logior-mask-logapp-of-logcollapse
     (implies (and (natp mask)
                   (natp width))
              (equal (logior (lognot mask) (logapp (logcollapse (integer-length (integer-length mask))
                                                                width)
                                                   x y))
                     (logior (lognot mask) (logapp width x y))))
     :hints (("goal" :cases ((<= (integer-length mask) width)))))

   ))

(define aig-logcollapse-ns ((n natp) x)
  :parents (logcollapse)
  (b* ((n (lnfix n)))
    (aig-logior-ss (aig-loghead-ns n x)
                   (aig-logapp-nss n nil
                                   (aig-scons (aig-not (aig-=-ss nil (aig-logtail-ns n x)))
                                              (aig-sterm nil)))))
  ///
  (defthm aig-logcollapse-ns-correct
    (equal (aig-list->s (aig-logcollapse-ns n x) env)
           (logcollapse n (aig-list->s x env)))
    :hints(("Goal" :in-theory (enable logcollapse)))))


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
       ((when (eql mask 0))
        ;; [Jared] this was previously using 4vec-0.  I think it's probably
        ;; better to use 4vec-x, in general, since for instance many
        ;; arithmetic operations check a2vec-p and then do something really
        ;; simple in the "nope, not a 2vec, may as well just return all xes."
        (a4vec-x)))
    (a4vec-ite (aig-and (a2vec-p w) ;; Is the width properly two-valued?
                        (aig-not (aig-sign-s w.upper)) ;; Is it natural?
                        )
               ;; Proper concatenation width.  But, take special care here to
               ;; avoid catastrophic shifts.
               (b* ((shift (if (< 0 mask)
                               ;; Collapse the upper bits of the shift
                               (aig-logcollapse-ns (integer-length (integer-length mask))
                                                   w.upper)
                             w.upper))
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
    (equal (4vec-mask mask (a4vec-eval (a4vec-concat n x y mask) env))
           (4vec-mask mask (4vec-concat (a4vec-eval n env)
                                        (a4vec-eval x env)
                                        (a4vec-eval y env))))
    :hints(("Goal" :in-theory (enable 4vec-concat 4vec-mask)
            :do-not-induct t))
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
    (equal (4vec-mask mask (a4vec-eval (a4vec-zero-ext n x mask) env))
           (4vec-mask mask (4vec-zero-ext (a4vec-eval n env)
                                          (a4vec-eval x env))))
    :hints(("Goal" :in-theory (enable 4vec-zero-ext
                                      4vec-concat)))))


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
    (equal (4vec-mask mask (a4vec-eval (a4vec-sign-ext n x mask) env))
           (4vec-mask mask (4vec-sign-ext (a4vec-eval n env)
                                          (a4vec-eval x env))))
    :hints(("Goal" :in-theory (enable 4vec-sign-ext 4vec-concat)))))


(define aig-right-shift-ss ((place posp) n shamt)
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
                    (sign  (aig-sign-s shamt))
                    ((mv upper-left lower-left)
                     (if (eq sign t)
                         (mv nil nil)
                       (b* ((lsh-amt (if (<= 0 mask)
                                         (aig-logcollapse-ns
                                          (integer-length (integer-length mask))
                                          shamt)
                                       shamt)))
                         (mv (aig-ash-ss 1 x.upper lsh-amt)
                             (aig-ash-ss 1 x.lower lsh-amt)))))
                    ((mv upper-right lower-right)
                     (if (not sign)
                         (mv nil nil)
                       (mv (aig-right-shift-ss 1 x.upper shamt)
                           (aig-right-shift-ss 1 x.lower shamt)))))
                 (a4vec (aig-ite-bss-fn sign upper-right upper-left)
                        (aig-ite-bss-fn sign lower-right lower-left)))
               ;; X/Z bits in shift amount, just return all Xes.
               (a4vec-x)))
  ///
  (defthm a4vec-rsh-correct
    (equal (4vec-mask mask (a4vec-eval (a4vec-rsh amt x mask) env))
           (4vec-mask mask
                      (4vec-rsh (a4vec-eval amt env)
                                (a4vec-eval x env))))
    :hints(("Goal" :in-theory (e/d (4vec-rsh 4vec-mask)
                                   (aig-sign-s-correct))
            :use ((:instance aig-sign-s-correct
                   (x (aig-unary-minus-s (a4vec->upper amt)))
                   (gl::env env)))))
    :otf-flg t))

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
                           (if (<= 0 mask)
                               (aig-logcollapse-ns (integer-length (integer-length mask))
                                                   shamt)
                             shamt)))
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
    (equal (4vec-mask mask (a4vec-eval (a4vec-lsh amt x mask) env))
           (4vec-mask mask
                      (4vec-lsh (a4vec-eval amt env)
                                (a4vec-eval x env))))
    :hints(("Goal" :in-theory (e/d (4vec-lsh 4vec-mask)
                                   (aig-sign-s-correct))
            :use ((:instance aig-sign-s-correct
                   (x (a4vec->upper amt))
                   (gl::env env)))))
    :otf-flg t))



(define aig-rev-blocks-nns ((nbits natp)
                            (blocksz posp)
                            x)
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
                            blocksz
                            x)
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
                            nbits
                            blocksz
                            x)
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
