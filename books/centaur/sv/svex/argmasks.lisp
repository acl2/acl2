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
(include-book "4vmask")
(include-book "xeval")
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "lattice"))
(local (xdoc::set-default-parents svex-argmasks))

; ----------------------------------------------------------------------------
;
;  Are you trying to understand this file?
;
;  Start with the documentation for svex-argmasks, which is near the bottom.
;  After you read that, everything will make sense.
;
; ----------------------------------------------------------------------------

(local (in-theory (enable svex-eval-when-2vec-p-of-minval)))

(local (defthm nth-open-constidx
         (implies (syntaxp (quotep n))
                  (equal (nth n x)
                         (if (zp n)
                             (car x)
                           (nth (1- n) (cdr x)))))))

(local (defthm len-equal-0
         (equal (equal (len x) 0)
                (not (consp x)))))

(local (defthm logand-x-x-y
         (equal (logand x x y)
                (logand x y))
         :hints(("Goal"
                 :in-theory
                 (enable* bitops::ihsext-inductions
                          bitops::ihsext-recursive-redefs)))))

(defthm 4veclist-nth-safe-of-nthcdr
  (equal (4veclist-nth-safe m (nthcdr n x))
         (4veclist-nth-safe (+ (nfix m) (nfix n)) x))
  :hints(("Goal" :in-theory (enable 4veclist-nth-safe))))



(defcong svexlist-equiv svex-equiv (nth n x) 2
  :hints(("Goal" :in-theory (enable svexlist-equiv svex-equiv svexlist-fix)
          :induct (svex-equiv (nth n x) (nth n x-equiv))
          :expand ((svexlist-fix x) (svexlist-fix x-equiv)))))

;; (local (in-theory (disable nth-open-constidx nth)))

(defthm equal-of-4veclist-mask-cons
  (equal (equal (4veclist-mask (cons m1 m) x)
                (4veclist-mask (cons m1 m) y))
         (and (equal (consp x) (consp y))
              (equal (4vec-mask m1 (car x))
                     (4vec-mask m1 (car y)))
              (equal (4veclist-mask m (cdr x))
                     (4veclist-mask m (cdr y)))))
  :hints(("Goal" :in-theory (enable 4veclist-mask))))

(defthm equal-of-4veclist-mask-nil
  (equal (equal (4veclist-mask nil x)
                (4veclist-mask nil y))
         (equal (4veclist-fix x)
                (4veclist-fix y)))
  :hints(("Goal" :in-theory (enable 4veclist-mask 4veclist-fix))))

(defthm svex-eval-of-nth
  (4vec-equiv (nth n (svexlist-eval x env))
              (svex-eval (nth n x) env))
  :hints(("Goal" :in-theory (enable svexlist-eval nth))))

(local (in-theory (disable acl2::bit->bool)))




(defun svex-nths-binding-list (args n form)
  (if (atom args)
      nil
    (cons (list (car args) `(svex-nth ,n ,form))
          (svex-nths-binding-list (cdr args) (1+ n) form))))

(acl2::def-b*-binder svex-nths
  :parents (svexlist)
  :short "@(see b*) binder for extracting @(see svex)es from a list using @(see
svex-nth)."
  :long "<p>Example:</p>
@({
      (b* (((svex-nths a b c) args))
         body)
      -->
      (b* ((a (svex-nth 0 args))
           (b (svex-nth 1 args))
           (c (svex-nth 2 args)))
        body)
})"
  :body
  (let* ((binding (car acl2::forms))
         (evaledp (or (atom binding) (eq (car binding) 'quote)))
         (form (if evaledp binding (acl2::pack binding)))
         (binders (svex-nths-binding-list args 0 form)))
    (if evaledp
        `(b* ,binders ,acl2::rest-expr)
      `(let ((,form ,binding))
         (declare (ignorable ,form))
         (b* ,binders
           (check-vars-not-free (,form) ,acl2::rest-expr))))))

(defun def-svmask-fn (fnname formals body fix-hints prep hints otf-flg long inline nobindings prepwork)
  (declare (xargs :mode :program))
  (b* ((maskfn  (intern$ (cat "SVMASK-FOR-" (symbol-name fnname)) "SV"))
       (thmname (intern$ (cat (symbol-name maskfn) "-CORRECT")    "SV")))
    `(define ,maskfn
       :short ,(cat "Implements @(see svex-argmasks) for @('" (symbol-name fnname) "').")
       ((mask 4vmask-p   "Care mask for the full expression.")
        (args svexlist-p ,(cat "Arguments to this @('" (symbol-name fnname) "') operator.")))
       :returns (argmasks 4vmasklist-p "The new care masks inferred for the @('args').")
       ,@(and long `(:long ,long))
       ,@(and inline `(:inline ,inline))
       :ignore-ok t
       :irrelevant-formals-ok t
       :prepwork ,prepwork
       (b* (,@(if nobindings
                 nil
                `(((svex-nths . ,formals) args)))
            (mask (4vmask-fix mask)))
         ,body)
       ///
       (local (progn . ,prep))

       (deffixequiv ,maskfn :hints ,fix-hints)

       (defthm ,thmname
         (implies (and (equal (4veclist-mask (,maskfn mask args) (svexlist-eval args env))
                              (4veclist-mask (,maskfn mask args) args1))
                       (syntaxp (not (equal args1 `(svexlist-eval ,args ,env)))))
                  (equal (4vec-mask mask (svex-apply ',fnname args1))
                         (4vec-mask mask (svex-apply ',fnname (svexlist-eval args env)))))
         :hints ,hints
         :otf-flg ,otf-flg))))

(defmacro def-svmask (fnname formals &key body fix-hints prep hints otf-flg long inline nobindings prepwork)
  (def-svmask-fn fnname formals body fix-hints prep hints otf-flg long inline nobindings prepwork))

(local (def-ruleset! expensive-rules
         '(acl2::zip-open
           BITOPS::LOGAND-NATP-TYPE-2
           BITOPS::LOGIOR-NATP-TYPE
           4VEC->LOWER-WHEN-2VEC-P
           DOUBLE-CONTAINMENT
           BITOPS::LOGBITP-NONZERO-OF-BIT
           BITOPS::LOGBITP-WHEN-BITMASKP
           BITOPS::LOGNOT-NEGP
           BITOPS::LOGAND-NATP-TYPE-1
           svex-eval-when-quote
           3vec-p-implies-bits
           acl2::bfix-when-not-1
           bitops::logbitp-of-negative-const
           bitops::logbitp-of-mask
           bitops::logbitp-of-const
           bitops::open-logbitp-of-const-lite-meta
           bitops::logior-<-0-linear-2
           bitops::logand->=-0-linear-2
           bitops::logior-<-0-linear-1
           bitops::logand->=-0-linear-1
           bitops::logand-<-0-linear
           bitops::logior->=-0-linear
           bitops::upper-bound-of-logand
           bitops::lognot-<-const
           bitops::lognot-natp)))

(local (def-ruleset! bitand-speed-hint
         ;; Dumb accumulated persistence hacking
         '((:t ACL2::BIT->BOOL$INLINE)
           default-car
           default-cdr
           SVEX-EVAL-WHEN-FNCALL
           ACL2::BIT-FUNCTIONS-TYPE
           (:e tau-system)
           (:t ACL2::B-IOR$INLINE)
           (:t ACL2::B-AND$INLINE)
           (:t ACL2::BIT-EQUIV$INLINE)
           (:t ACL2::BITP$INLINE)
           (:t ACL2::BITMASKP$INLINE)
           CAR-OF-SVEXLIST-FIX-X-NORMALIZE-CONST-UNDER-SVEX-EQUIV
           SVEX-XEVAL-OF-SVEX-FIX-EXPR-NORMALIZE-CONST
           CDR-OF-SVEXLIST-FIX-X-NORMALIZE-CONST-UNDER-SVEXLIST-EQUIV
           BITOPS::LOGBITP-WHEN-BIT)))

(local (in-theory (disable* expensive-rules)))

(define 4vmask-all-or-none
  :short "Care mask for an argument that matters fully, unless we don't care
about any bits at all."
  ((outer-mask 4vmask-p "Care mask from the outer expression."))
  :returns (arg-mask 4vmask-p "Care mask for the argument.")
  :long "<p>In various SVEX @(see functions), such as @('(bitsel index expr)'),
the @('index') expressions have a simple care-mask behavior:</p>

<ul>

<li>If we care about any bit of the @('bitsel') expression, then we care about
<i>all</i> of the bits of @('index').</li>

<li>Otherwise, we don't care about this expression at all, so all of its
arguments are completely irrelevant and there is no reason to care about the
@('index') at all.</li>

</ul>

<p>Similar things happen in, e.g., reduction operators, arithmetic
operators (due to globally caring about whether there are any X/Z bits), etc.,
so this function ends up being widely used in the the functions that implement
@(see svex-argmasks).</p>"
  :inline t
  (if (4vmask-empty outer-mask)
      0
    -1)
  ///
  (deffixequiv 4vmask-all-or-none))

(def-svmask unfloat (x)
  :long "<p>Unfloating just turns X bits into Z bits without moving any bits
around or merging them together, it doesn't seem like there's any way to
improve on the outer care mask here.</p>"
  :inline t
  :nobindings t
  :body (list mask)
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  3vec-fix
                                  4veclist-nth-safe))))
          (bitops::logbitp-reasoning)))

(def-svmask id (x)
  :long "<p>Since the identity just passes its argument through verbatim, it
doesn't seem like there's any way to improve on the outer care mask here.</p>"
  :inline t
  :nobindings t
  :body (list mask)
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  3vec-fix
                                  4veclist-nth-safe))))
          (bitops::logbitp-reasoning)))

(def-svmask bitnot (x)
  :long "<p>Since bitwise negation just negates bits without moving them around
or merging them together, it doesn't seem like there's any way to improve on
the outer care mask here.</p>"
  :inline t
  :nobindings t
  :body (list mask)
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  3vec-fix
                                  3vec-bitnot
                                  4vec-bitnot
                                  4veclist-nth-safe))))
          (bitops::logbitp-reasoning)))

(def-svmask onp (x)
  :long "<p>Since @('onp') just turns Z bits into 0s without moving them around
or merging them together, it doesn't seem like there's any way to improve on
the outer care mask here.</p>"
  :inline t
  :nobindings t
  :body (list mask)
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  3vec-fix
                                  4vec-onset
                                  4veclist-nth-safe))))
          (bitops::logbitp-reasoning)))

(def-svmask offp (x)
  :long "<p>Since @('offp') affects each bit, without moving bits around or
merging them together, it doesn't seem like there's any way to improve on the
outer care mask here.</p>"
  :inline t
  :nobindings t
  :body (list mask)
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  3vec-fix
                                  4vec-offset
                                  4veclist-nth-safe))))
          (bitops::logbitp-reasoning)))

(def-svmask res (x y)
  :long "<p>Since each bit of @('(res x y)') always depends on the
corresponding bits of @('x') and @('y'), it doesn't seem like there's any way
to improve on the outer care mask here.</p>"
  :inline t
  :nobindings t
  :body (list mask mask)
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    4vec-mask
                                    4vec-res))
          (bitops::logbitp-reasoning)
          (and stable-under-simplificationp
               '(:bdd (:vars nil)))))

(def-svmask uand (x)
  :long "<p>We are considering a @('(uand x)') expression and we know that we
only care about the bits mentioned in @('mask').  We know that @(see
4vec-reduction-and) will need to consider all of the bits of @('x').  Since it
follows the @(see boolean-convention), we also know that it is either going to
return all 1s, all 0s, or all Xes.</p>

<p>Accordingly, it seems that if we care about <i>any</i> bit of the result, we
need to care about <i>all</i> of the bits of the argument.  On the other hand,
if we don't care about any bits of the result, then we don't need to care about
any bit of the argument.</p>"
  :inline t
  :body (list (4vmask-all-or-none mask))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  3vec-fix
                                  4vmask-all-or-none
                                  4vec-reduction-and
                                  3vec-reduction-and
                                  ))))
          (bitops::logbitp-reasoning
           :add-hints (:in-theory (enable* logbitp-when-4vec-[=-svex-eval-strong)))
          (and stable-under-simplificationp
               '(:bdd (:vars nil)))))

(def-svmask uor (x)
  :long "<p>See @(see svmask-for-uand); the same reasoning applies here.</p>"
  :inline t
  :body (list (4vmask-all-or-none mask))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  3vec-fix
                                  4vmask-all-or-none
                                  4vec-reduction-or
                                  3vec-reduction-or
                                  ))))
          (bitops::logbitp-reasoning
           :add-hints (:in-theory (enable* logbitp-when-4vec-[=-svex-eval-strong)))
          (and stable-under-simplificationp
               '(:bdd (:vars nil)))))

(def-svmask uxor (x)
  :long "<p>See @(see svmask-for-uand); the same reasoning applies here.</p>"
  :inline t
  :body (list (4vmask-all-or-none mask))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  3vec-fix
                                  4vmask-all-or-none
                                  4vec-parity
                                  ))))
          (bitops::logbitp-reasoning
           :add-hints (:in-theory (enable* logbitp-when-4vec-[=-svex-eval-strong)))
          (and stable-under-simplificationp
               '(:bdd (:vars nil)))))

(def-svmask + (x y)
  :long "<p>We can't do anything smart here.  Since @('(+ x y)') returns pure
Xes whenever there are <i>any</i> X/Z bits in x or y, we always have to
consider all of the bits of both arguments, unless we truly don't care about
any bits of the result at all.</p>

<p>It would be possible to improve the mask in the case that we knew some bit
of some argument was @('z'), because in that case we would know that the whole
answer was definitely Xes.  However, since Z values are pretty uncommon, it
probably isn't worth doing this.</p>"
  :inline t
  :nobindings t
  :body (b* ((argmask (4vmask-all-or-none mask)))
          (list argmask argmask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    4vmask-all-or-none))))

(def-svmask u- (x)
  :long "<p>As in @(see svmask-for-+), we can't do anything smart here because
of global X/Z detection.</p>"
  :inline t
  :nobindings t
  :body (list (4vmask-all-or-none mask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    4vmask-all-or-none))))

(def-svmask b- (x y)
  :long "<p>As in @(see svmask-for-+), we can't do anything smart here because
of global X/Z detection.</p>"
  :inline t
  :nobindings t
  :body (b* ((argmask (4vmask-all-or-none mask)))
          (list argmask argmask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    4vmask-all-or-none))))

(def-svmask * (x y)
  :long "<p>As in @(see svmask-for-+), we can't do anything smart here because
of global X/Z detection.</p>"
  :inline t
  :nobindings t
  :body (b* ((argmask (4vmask-all-or-none mask)))
          (list argmask argmask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    4vmask-all-or-none))))

(def-svmask / (x y)
  :long "<p>As in @(see svmask-for-+), we can't do anything smart here because
of global X/Z detection.</p>"
  :inline t
  :nobindings t
  :body (b* ((argmask (4vmask-all-or-none mask)))
          (list argmask argmask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    4vmask-all-or-none))))

(def-svmask % (x y)
  :long "<p>As in @(see svmask-for-+), we can't do anything smart here because
of global X/Z detection.</p>"
  :inline t
  :nobindings t
  :body (b* ((argmask (4vmask-all-or-none mask)))
          (list argmask argmask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    4vmask-all-or-none))))

(def-svmask < (x y)
  :long "<p>As in @(see svmask-for-+), we can't do anything smart here because
of global X/Z detection.</p>"
  :inline t
  :nobindings t
  :body (b* ((argmask (4vmask-all-or-none mask)))
          (list argmask argmask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    4vmask-all-or-none))))

(def-svmask == (x y)
  :long "<p>As in @(see svmask-for-+), we can't do anything smart here because
of global X/Z detection.</p>"
  :inline t
  :nobindings t
  :body (b* ((argmask (4vmask-all-or-none mask)))
          (list argmask argmask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    4vmask-all-or-none))))

(def-svmask clog2 (x)
  :long "<p>As in @(see svmask-for-+), we can't do anything smart here because
of global X/Z detection.</p>"
  :inline t
  :nobindings t
  :body (list (4vmask-all-or-none mask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    4vmask-all-or-none))))


(def-svmask xdet (x)
  :long "<p>We can't do anything smart here.  Since @('(xdet x)') returns pure
Xes whenever there are <i>any</i> X/Z bits in x, we always have to consider all
of the bits of @('x'), unless we truly don't care about any bits of the result
at all.</p>"
  :inline t
  :nobindings t
  :body (list (4vmask-all-or-none mask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    4vmask-all-or-none))))

(def-svmask === (x y)
  :long "<p>We can't do anything smart here because @('(=== x y)') cares about
every bit of X and Y, with no short circuiting or any kind.</p>"
  :inline t
  :nobindings t
  :body (b* ((argmask (4vmask-all-or-none mask)))
          (list argmask argmask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    4vmask-all-or-none))))

(def-svmask ==? (a b)
  :long "<p>We are considering @('(==? a b)') and we want to compute the care
masks for @('a') and @('b'), given some outer care mask for the whole
expression.</p>

<p>The outer mask doesn't much matter since there's nothing bitwise about this,
except that if the whole outer mask is zero then we (of course) don't care
about any bits at all.</p>

<p>We can't do anything smart for @('b'), but for @('a') we definitely don't
care about any bits that are Z in @('b'), since @(see 4vec-wildeq) doesn't care
about the corresponding bit in @('a').</p>"

  :body (b* (((when (eql mask 0))
              ;; Don't care about any bits at all.
              (list 0 0))
             ((4vec bval) (svex-xeval b))
             (b-nonz (logorc2 bval.upper bval.lower)))
          (list b-nonz -1))
  :prepwork ((local (in-theory (disable not))))
  :hints(("Goal" :in-theory (e/d (svex-apply
                                  4veclist-nth-safe))
          :do-not-induct t)
         (and stable-under-simplificationp
              '(:in-theory (e/d (svex-apply 4veclist-nth-safe
                                            4vec-wildeq 3vec-reduction-and
                                            3vec-bitor 3vec-bitnot 4vec-bitxor
                                            4vec-mask bool->vec 4vec-[=)
                                (svex-eval-gte-xeval))
                :use ((:instance svex-eval-gte-xeval
                       (x (car args)))
                      (:instance svex-eval-gte-xeval
                       (x (cadr args))))))
         (bitops::logbitp-reasoning :passes 2
                                    :simp-hint nil
                                    :add-hints nil)
         (and stable-under-simplificationp
              '(:bdd (:vars nil)))))

(def-svmask ==?? (a b)
  :long "<p>We are considering @('(==?? a b)'), i.e., @(see 4vec-symwildeq).
We want to compute the care masks for @('a') and @('b'), given some outer care
mask for the whole expression.</p>

<p>We of course care about any bits @('ai') and @('bi') where neither @('ai')
or @('bi') are known to be Z.  However, if we can statically determine that,
e.g., @('ai') is Z, then there's no reason to care about the corresponding
@('bi').  Symmetrically, if we can determine that @('bi') is Z, we (almost)
don't need to care about @('ai').  The only catch is that if both vectors share
a Z, we can't ignore both bits simultaneously, but instead have to choose to
keep one or the other.  We make this decision following a strategy that is
similar to @(see svmask-for-bitand).</p>"

  :body
  (b* (((4vec aval) (svex-xeval a))
       ((4vec bval) (svex-xeval b))
       (a-is-z      (logandc1 aval.upper aval.lower))
       (b-is-z      (logandc1 bval.upper bval.lower))
       (both-are-z  (logand a-is-z b-is-z))
       ((when (eql both-are-z 0))
        ;; No overlap, can mask both aggressively.
        (list (lognot b-is-z) (lognot a-is-z)))

       ;; Otherwise there are overlapping Zs so we cannot mask them both
       ;; aggressively.  Idea: we will (arbitrarily) mask B more aggressively
       ;; UNLESS all of the bits of B are known to be constant.
       (b-x  (logandc2 bval.upper bval.lower))
       ((when (eql 0 b-x))
        ;; We know all bits of B.  Let's mask A more aggressively, then.
        (list (lognot b-is-z)
              (logorc1 a-is-z both-are-z))))
    ;; Otherwise, no reason to prefer masking A more aggressively, so just
    ;; arbitrary default to masking B more aggressively than A.
    (list (logorc1 b-is-z both-are-z)
          (lognot a-is-z)))

  :prepwork
  ((local (defthm logbitp-of-bool->vec
            (iff (logbitp n (bool->vec bool))
                 bool)))

   (local (defthm logior-with-bool->vec
            (equal (logior a (bool->vec b))
                   (if b
                       -1
                     (ifix a)))))

   (local (defthm logand-with-bool->vec
            (equal (logand a (bool->vec b))
                   (if b
                       (ifix a)
                     0))))

   (local (in-theory (disable* not
                               bitand-speed-hint
                               (:e tau-system)))))

  :hints(("Goal" :in-theory (e/d (svex-apply
                                  4veclist-nth-safe))
          :do-not-induct t)
         (and stable-under-simplificationp
              '(:in-theory (e/d (svex-apply 4veclist-nth-safe
                                            4vec-symwildeq
                                            3vec-reduction-and
                                            3vec-bitor
                                            3vec-bitnot
                                            4vec-bitxor
                                            4vec-mask
                                            4vec-[=)
                                (svex-eval-gte-xeval))
                :use ((:instance svex-eval-gte-xeval (x (car args)))
                      (:instance svex-eval-gte-xeval (x (cadr args))))
                ))
         (bitops::logbitp-reasoning :passes 2)
         (and stable-under-simplificationp
              '(:bdd (:vars nil)))))

(def-svmask override (stronger weaker)
  :long "<p>We are considering a @('(override stronger weaker)') expression and
we know that we only care about the bits mentioned in @('mask').  We want to
figure out which bits of @('stronger') and @('weaker') we care about.  As a
starting point, since @('override') operates in a bit-by-bit fashion, we
certainly don't care about any bits that are don't cares in our outer
@('mask').</p>

<p>It doesn't seem like we can do any better than @('mask') for @('stronger'),
since the output bit always depends on the stronger bit.</p>

<p>However, we definitely don't care about the value of @('weaker') when the
corresponding bit of @('stronger') has a good Boolean value.  So, we remove any
such bits from the mask for @('weaker').</p>"
  :body (b* (((4vec sval)    (svex-xeval stronger))
             (strong-nonbool (logxor sval.upper sval.lower))
             (weak-mask      (logand mask strong-nonbool)))
          (list mask weak-mask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    4vec-mask
                                    4vec-override
                                    ))
         (bitops::logbitp-reasoning
          :add-hints (:in-theory (enable* logbitp-when-4vec-[=-svex-eval-strong)))
         (and stable-under-simplificationp
              '(:bdd (:vars nil)))))

(def-svmask bitsel (n x)
  :long "<p>For @('n').  If we care about ANY bit of @('(bitsel n x)'), then we
care about all of @('n').  But if we don't care about any bit of @('(bitsel n
x)'), then N is completely irrelevant.</p>

<p>For @('x').  The result of (4vec-bit-extract n x) is only one bit wide.  If
we can statically determine that @('n') is a non-negative constant, then we can
tell exactly which bit of @('x') we care about and just care about that one
bit.</p>

<p>Otherwise, if @('n') is statically determined to be a negative constant,
then the @('bitsel') expression is going to return X anyway no matter what
@('x') is, so we don't care about @('x') at all.</p>

<p>Otherwise, @('n') might refer to anything, so we care about all of @('x')
unless the whole expression is completely irrelevant.</p>"
  :body
  (b* ((nval  (svex-xeval n))
       (nmask (4vmask-all-or-none mask))
       ((unless (2vec-p nval))
        ;; N is not statically known, so we don't know which bit we care about.
        (list nmask nmask))
       (nv (2vec->val nval))
       ((when (< nv 0))
        ;; N is negative so we don't care about X at all, the bitsel returns Xes
        (list nmask 0)))
    ;; N is a positive, so we care about exactly the nth bit.
    (list nmask
          (the unsigned-byte (ash (the bit (logbit 0 mask))
                                  (the unsigned-byte nv)))))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vmask-all-or-none
                                  4vec-mask
                                  4veclist-nth-safe
                                  4vec-bit-index
                                  4vec-bit-extract))))
          (bitops::logbitp-reasoning)))

(def-svmask zerox (n x)
  :long "<p>We are considering a @('(zerox n x)') expression and we know that
we only care about the bits mentioned in @('mask').  We need to figure out
which bits of @('n') and @('x') we care about.</p>

<p>For @('n').  If we care about ANY bit of @('(zerox n x)'), then we care
about all of @('n').  But if we don't care about any bit of @('(zerox n x)'),
then @('n') is completely irrelevant.</p>

<p>For @('x').  The result of @('(zerox n x)') is just the low @('n') bits of
@('x').  So when @('n') is a constant, we can reduce the outer @('mask') by
chopping off any bits beyond position @('n').  Otherwise, we don't know how
</p>"

  :body (list (4vmask-all-or-none mask)
              (let ((nval (svex-xeval n)))
                (if (4vec-index-p nval)
                    (loghead (2vec->val nval) mask)
                  mask)))

  :prepwork
  ((local (in-theory (enable svex-eval-when-2vec-p-of-minval
                             4vmask-all-or-none)))

   (local (defthm equal-of-svex-eval
            (equal (equal (svex-eval x env) y)
                   (and (4vec-p y)
                        (equal (4vec->upper (svex-eval x env))
                               (4vec->upper y))
                        (equal (4vec->lower (svex-eval x env))
                               (4vec->lower y))))))

   (local (defthm 2vec-p-when-4vec-index-p
            (implies (4vec-index-p x)
                     (2vec-p x))
            :hints(("Goal" :in-theory (enable 4vec-index-p))))))

  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  4veclist-nth-safe
                                  4vec-zero-ext))))
          (bitops::logbitp-reasoning)
          (and stable-under-simplificationp
               '(:bdd (:vars nil)))))

(define sign-ext-mask ((mask 4vmask-p) (n natp))
  :parents (svmask-for-signx)
  :inline t
  (logior (loghead n mask)
          (if (eql 0 (logtail n mask))
              0
            (ash 1 (- n 1)))))

(define mask-for-generic-signx ((outer-mask 4vmask-p))
  :parents (signx)
  :short "BOZO eventually try to use something like this."
  :returns (arg-mask 4vmask-p :rule-classes :type-prescription)
  :inline t
  (b* ((mask (lifix outer-mask)))
    (if (< mask 0)
        -1
      ;; We might care about any bit up to the length of the mask, but
      ;; we definitely don't care about other bits.
      (let* ((mask-upper-bound (+ 1 (integer-length mask))))
        (1- (ash 1 mask-upper-bound)))))
  ///
  (local (include-book "centaur/bitops/integer-length" :dir :system))
  (local (in-theory (enable* mask-for-generic-signx
                             bitops::logbitp-case-splits
                             expensive-rules)))

  (defthm logbitp-of-mask-for-generic-signx
    (equal (logbitp n (mask-for-generic-signx outer-mask))
           (or (< (ifix outer-mask) 0)
               (<= (nfix n) (integer-length outer-mask))))))

(def-svmask signx (n x)
  :long "<p>We are considering a @('(signx n x)') expression and we know that
we only care about the bits mentioned in @('mask').  We need to figure out
which bits of @('n') and @('x') we care about.</p>

<p>For @('n').  If we care about ANY bit of @('(signx n x)'), then we care
about all of @('n').  But if we don't care about any bit of @('(signx n x)'),
then @('n') is completely irrelevant.</p>

<p>For @('x').  The result of @('(signx n x)') is just the low @('n') bits of
@('x'), with the @('n')th bit being sign extended to infinity.</p>

<p>If we statically determine that @('n') is negative, then we don't care about
@('x') at all because @(see 4vec-sign-ext) will just return all Xes no matter
what it is.</p>

<p>If we statically determine that @('n') is positive, then:</p>

<ul>

<li>the bits below @('n') only matter if they are marked as care bits in the
outer @('mask');</li>

<li>bit @('n') will only matter when bit @('n') <i>or any greater bit</i>, is
marked as a care bit in the outer @('mask').</li>

</ul>

<p>If we can't statically determine @('n'), we may still be able to do
something based on the outer mask.  For instance, if @('mask') is @('#b1000'),
then we know that we don't care about any bits above bit @('4').  However, we
might depend on <i>any</i> of the bits below 4, because we might be sign
extending any one of them.</p>

<p>BOZO for now we don't exploit this and simply say that we depend on all of
@('x').  In the future, it would be good to integrate something like @(see
mask-for-generic-signx) here.</p>"
  :body (b* (((when (eql mask 0))
              ;; Don't care about the result, so don't care about any args.
              (list 0 0))
             (nval (svex-xeval n))
             ((unless (2vec-p nval))
              ;; We don't statically know N.  BOZO I think we can do better
              ;; than just assuming we need all bits of X.  In particular,
              ;; we should be able to do something like:
              ;;    (mask-for-generic-signx mask)
              ;; It didn't seem super easy to prove this, so I'm holding off
              ;; for now.
              (list -1 -1))
             ((unless (<= 0 (2vec->val nval)))
              ;; We know N but it is a negative number, so the result is pure X
              ;; bits, regardless of the x argument.
              (list -1 0))
             (xmask (sign-ext-mask mask (2vec->val nval))))
          (list -1 xmask))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  4veclist-nth-safe
                                  4vec-sign-ext
                                  4vec-index-p
                                  sign-ext-mask
                                  4vmask-all-or-none
                                  ))))
          (bitops::logbitp-reasoning
           :add-hints (:in-theory
                       (enable* bitops::logbitp-case-splits
                                bitops::logbitp-of-const-split))
           :simp-hint (:in-theory
                       (enable* bitops::logbitp-case-splits
                                bitops::logbitp-of-const-split))
           :prune-examples nil)
          (and stable-under-simplificationp
               '(:bdd (:vars nil)))))

(def-svmask concat (n x y)
  :long "<p>We are considering a @('(concat n x y)') expression and we know
that we only care about the bits mentioned in @('mask').  We need to figure out
which bits of @('n'), @('x'), and @('y') we care about.</p>

<p>For @('n').  If we care about ANY bit of @('(concat n x y)'), then we care
about all of @('n').  But if we don't care about any bit of the result, then
@('n') is completely irrelevant.</p>

<p>For @('x') and @('y').  If @('n') is statically known but is negative, then
the result of @(see 4vec-concat) is just all Xes no matter what @('x') and
@('y') are, so they don't matter at all.</p>

<p>If @('n') is statically known and positive, then we can adjust @('mask') as
appropriate, taking the first @('n') bits of it as the care mask for @('x'),
and taking the remaining bits of it as the care mask for @('y').</p>

<p>If we don't statically know @('n'), then we may still be able to do
something based on the outer @('mask').  For instance, if @('mask') is
@('#b1000'), then even if we don't know where the bits are coming from, we
certainly know that we don't care about bits of @('x') or @('y') that are above
bit 4, because no matter what index is used that's as many bits as we could
take from either of them.</p>

<p>BOZO for now we don't exploit this and simply say that we depend on all of
@('x').  In the future, it would be good to integrate something like @(see
mask-for-generic-signx) here.</p>"

  :body (b* (((when (4vmask-empty mask))
              ;; Don't care about any bits of the result, so we don't care
              ;; about any of the arguments.
              (list 0 0 0))
             (nval (svex-xeval n))
             ((unless (2vec-p nval))
              ;; Don't know what the index is.  Punt for now.  BOZO eventually
              ;; try to use mask-for-generic-signx here for X and Y.
              (list -1 -1 -1))
             (n (2vec->val nval))
             ((unless (<= 0 n))
              ;; N is statically known to be negative, so the whole result is X
              ;; for sure and we don't care about x or y at all.
              (list -1 0 0)))
          ;; X is statically known and positive, so adjust mask accordingly on
          ;; the arguments.
          (list -1
                (loghead n mask)
                (logtail n mask)))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  4veclist-nth-safe
                                  4vec-concat))))
          (bitops::logbitp-reasoning)))

(def-svmask rsh (n x)
  :long "<p>We are considering a @('(rsh n x)') expression and we know that we
only care about the bits mentioned in @('mask').  We need to figure out which
bits of @('n') and @('x') we care about.</p>

<p>For @('n').  If we care about ANY bit of @('(rsh n x)'), then we care about
all of @('n').  But if we don't care about any bit of the result, then @('n')
is completely irrelevant.</p>

<p>For @('x').  If we statically know @('n'), then we are just going to shift
the bits of @('x') right (or left, if @('n') is negative) by that many places,
so we just need to similarly shift the outer care mask.</p>

<p>If @('n') is not statically known, and we care about any bits of the answer,
then it seems like we need to care about all of @('x').  After all, any bit of
@('x') might in principle get shifted into the bit position that we care
about.</p>"
  :body (b* (((when (4vmask-empty mask))
              ;; Don't care about this expression at all, hence don't care
              ;; about any of the arguments.
              (list 0 0))
             (nval (svex-xeval n))
             ((when (2vec-p nval))
              ;; Statically known shift amount, so just shift the mask by
              ;; the shift amount.
              (list -1 (ash mask (2vec->val nval)))))
          ;; No idea which bits will get shifted in, so we have to depend on
          ;; all of them.
          (list -1 -1))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  4veclist-nth-safe
                                  4vec-rsh))
                 :cases ((<= 0 (2vec->val (svex-xeval (car args)))))))
          (bitops::logbitp-reasoning)))

(def-svmask lsh (n x)
  :long "<p>See @(see svmask-for-rsh).  This is entirely similar, just for left
shifts instead of right shifts.</p>"
  :body (b* (((when (4vmask-empty mask))
              ;; Don't care about this expression at all, hence don't care
              ;; about any of the arguments.
              (list 0 0))
             (nval (svex-xeval n))
             ((when (2vec-p nval))
              ;; Statically known shift amount, so just shift the mask by the
              ;; shift amount.
              (list -1 (ash mask (- (2vec->val nval))))))
          ;; No idea which bits will get shifted in, so we have to depend on
          ;; all of them.
          (list -1 -1))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  4veclist-nth-safe
                                  4vec-lsh))
                 :cases ((<= 0 (2vec->val (svex-xeval (car args)))))))
          (bitops::logbitp-reasoning)))


(add-to-ruleset bitand-speed-hint
                '(SVEX-EVAL-WHEN-2VEC-P-OF-MINVAL
                 2VEC-P
                 4VMASK-P-WHEN-MEMBER-EQUAL-OF-4VMASKLIST-P
                 BITOPS::LOGAND-WITH-BITMASK
                 4VECLIST-FIX-WHEN-4VECLIST-P
                 4VECLIST-P-OF-CDR-WHEN-4VECLIST-P
                 BITOPS::LOGBITP-WHEN-BIT
                 default-<-1
                 default-<-2
                 acl2::natp-rw
                 acl2::natp-when-integerp
                 arith-equiv-forwarding
                 ACL2::NOT-BIT->BOOL-FORWARD-TO-BIT-EQUIV-0
                 ACL2::BIT->BOOL-FORWARD-TO-EQUAL-1
                 CAR-OF-4VECLIST-FIX-X-NORMALIZE-CONST-UNDER-4VEC-EQUIV
                 (:t 4vmask-p)
                 ACL2::CANCEL_TIMES-EQUAL-CORRECT
                 acl2::CANCEL_PLUS-EQUAL-CORRECT
                 SVEX-EVAL-OF-SVEX-FIX-X-NORMALIZE-CONST
                 SVEX-EVAL-OF-SVEX-ENV-FIX-ENV-NORMALIZE-CONST
                 SVEX-EVAL-OF-QUOTED
                 CDR-OF-4VECLIST-FIX-X-NORMALIZE-CONST-UNDER-4VECLIST-EQUIV
                 ACL2::BFIX-WHEN-NOT-BITP
                 EQUAL-OF-4VECLIST-FIX-2-FORWARD-TO-4VECLIST-EQUIV
                 EQUAL-OF-4VECLIST-FIX-1-FORWARD-TO-4VECLIST-EQUIV
                 default-car
                 default-cdr

                 ))

(def-svmask bitand (x y)
  :long "<p>We are considering a @('(bitand x y)') expression and we know that
we only care about the bits mentioned in @('mask').  We want to figure out
which bits of X and Y we care about.  As a starting point, since bitwise AND
operates in a bit-by-bit fashion, we certainly don't care about any bits that
are don't cares in our outer @('mask').  But we can do better than that.</p>

<p>For any particular bit of @('x'), if we can tell that the corresponding bit
of @('y') is zero, then we know that the resulting bit from the AND is going to
be 0, so this bit of X doesn't matter.  The basic idea here, then, is to
improve @('mask') for @('x') by taking away any bits of @('y') that we can tell
are zero.  Symmetrically, we can take improve @('mask') for @('y') by taking
away any bits of @('x') that are known to be zero.</p>

<p>Well, almost.  What if we know that bit 4 of @('x') is zero AND that bit 4
of @('y') is zero.  We can't just mark bit 4 as a don't care in both arguments,
because we need to keep at least one zero or the other.  This leads to a
certain kind of asymmetry, and leaves us with some choice regarding which
argument we want to mask more aggressively.</p>

<p>We don't currently try very hard to make any kind of sensible choice here.
Instead, as a rather arbitrary default, we normally mask @('y') more
aggressively than @('x').  However, as a special exception, if @('y') is
entirely constant under the outer mask, then we will mask @('x') more
aggressively.</p>"

    :body (b* (((4vec xval)  (svex-xeval x))
               ((4vec yval)  (svex-xeval y))
               (x-nonzero    (logior xval.upper xval.lower))
               (y-nonzero    (logior yval.upper yval.lower))
               (xm-nonzero   (logand mask x-nonzero))
               (ym-nonzero   (logand mask y-nonzero))
               (shared-zeros (lognand xm-nonzero ym-nonzero))
               ((when (eql 0 shared-zeros))
                ;; There are no overlapping zeroes in any bits that we care
                ;; about, so we can aggressively mask both arguments.
                (list ym-nonzero xm-nonzero))
               ;; Otherwise there are overlapping zeroes so we cannot mask them
               ;; both aggressively.  Idea: we will (arbitrarily) mask Y more
               ;; aggressively UNLESS all of the relevant bits of Y are known
               ;; to be constant under the current mask, in which case we would
               ;; probably rather mask X more aggressively.
               (y-x     (logandc2 yval.upper yval.lower))
               (ym-x    (logand mask y-x))
               ((when (eql 0 ym-x))
                ;; There are no masked bits of Y that are X, so the parts of Y we
                ;; care about are constant or are nearly constant.  So let's mask
                ;; X more aggressively.
                (list ym-nonzero (logior xm-nonzero shared-zeros))))
            ;; Otherwise, no reason to prefer masking X more aggressively, so
            ;; just arbitrary default to masking Y more aggressively than X.
            (list (logior ym-nonzero shared-zeros) xm-nonzero))
    :prepwork
    ((local (in-theory (disable* bitand-speed-hint not))))
    :hints (("Goal" :in-theory (e/d (svex-apply
                                     4veclist-nth-safe)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (svex-apply
                                    4vec-mask
                                    3vec-fix
                                    3vec-bitand
                                    4vec-bitand
                                    4veclist-nth-safe))))
            (bitops::logbitp-reasoning
             :add-hints (:in-theory (enable* logbitp-when-4vec-[=-svex-eval-strong))
             )
            (and stable-under-simplificationp
                 '(:bdd (:vars nil)))))

(def-svmask resand (x y)
  :long "<p>See @(see svmask-for-bitand); the same analysis applies equally
well to @('(resand x y)').</p>"
  :inline t
  :nobindings t
  :body (svmask-for-bitand mask args)
  :prepwork ((local (in-theory (disable* bitand-speed-hint not))))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  3vec-fix
                                  4vec-resand
                                  4veclist-nth-safe
                                  ;4vec-bitand-mask
                                  svmask-for-bitand))))
          (bitops::logbitp-reasoning
           :add-hints (:in-theory (enable* logbitp-when-4vec-[=-svex-eval-strong)))
          (and stable-under-simplificationp
               '(:bdd (:vars nil)))))

(def-svmask bitor (x y)
  :long "<p>See @(see svmask-for-bitand).  This is similar, except that since
we are dealing with @('(bitor x y)'), the bits of @('x') that are 1 (instead of
0) are the don't cares bits for @('y'), and vice versa.  Again we have to watch
out for cases where both arguments have a @('1') bit, and in such cases mark at
least one or the other as a care bit.</p>"

  :body (b* (((4vec xval)  (svex-xeval x))
             ((4vec yval)  (svex-xeval y))
             (x-non1       (lognand xval.upper xval.lower))
             (y-non1       (lognand yval.upper yval.lower))
             (xm-non1      (logand mask x-non1))
             (ym-non1      (logand mask y-non1))
             (shared-1s    (lognand xm-non1 ym-non1))
             ((when (eql 0 shared-1s))
              ;; There are no overlapping zeroes in any bits that we care
              ;; about, so we can aggressively mask both arguments.
              (list ym-non1 xm-non1))
             ;; Otherwise there are overlapping 1s so we cannot mask them both
             ;; aggressively.  Idea: we will (arbitrarily) mask Y more
             ;; aggressively UNLESS all of the relevant bits of Y are known to
             ;; be constant under the current mask, in which case we would
             ;; probably rather mask X more aggressively.
             (y-x  (logandc2 yval.upper yval.lower))
             (ym-x (logand mask y-x))
             ((when (eql 0 ym-x))
              ;; There are no masked bits of Y that are X, so the parts of Y we
              ;; care about are constant or are nearly constant.  So let's mask
              ;; X more aggressively.
              (list ym-non1 (logior xm-non1 shared-1s))))
          ;; Otherwise, no reason to prefer masking X more aggressively, so
          ;; just arbitrary default to masking Y more aggressively than X.
          (list (logior ym-non1 shared-1s) xm-non1))
  :prepwork ((local (in-theory (disable* bitand-speed-hint not))))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  3vec-fix
                                  3vec-bitor
                                  4vec-bitor
                                  4veclist-nth-safe))))
          (bitops::logbitp-reasoning
           :add-hints (:in-theory (enable* logbitp-when-4vec-[=-svex-eval-strong)))
          (and stable-under-simplificationp
               '(:bdd (:vars nil)))))

(def-svmask resor (x y)
  :long "<p>See @(see svmask-for-bitand); the same analysis applies equally
well to @('(resand x y)').</p>"
  :inline t
  :nobindings t
  :body (svmask-for-bitor mask args)
  :prepwork ((local (in-theory (disable* bitand-speed-hint not))))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  3vec-fix
                                  4vec-resor
                                  svmask-for-bitor
                                  4veclist-nth-safe))))
          (bitops::logbitp-reasoning
           :add-hints (:in-theory (enable* logbitp-when-4vec-[=-svex-eval-strong)))
          (and stable-under-simplificationp
               '(:bdd (:vars nil)))))

(def-svmask bitxor (x y)
  :long "<p>We are considering a @('(bitxor x y)') expression and we know that
we only care about the bits mentioned in @('mask').  We want to figure out
which bits of X and Y we care about.  As a starting point, since bitwise XOR
operates in a bit-by-bit fashion, we certainly don't care about any bits that
are don't cares in our outer @('mask').  We can only do slightly better than
this.</p>

<p>Consider any two bits, Xi and Yi.  Even if we know that Xi is 0 or 1, that
doesn't help us to avoid needing to evaluate Yi.  On the other hand, if we can
statically determine that Xi is definitely X or Z, then we don't need to care
about the corresponding bit of Yi.</p>

<p>We typically do these kinds of static determinations using @(see
svex-xeval).  This can tell us when Xi is definitely Z, but not when it is
definitely X.  So for now we only try to improve the mask in cases where Xi is
definitely Z, and we don't yet try to take advantage of knowing that Xi is
definitely X.  Some day we might want to consider whether we could easily
modify @('svex-xeval') to identify definite X values as well.</p>

<p>At any rate, this is largely similar to @(see svmask-for-bitand); we can
symmetrically ignore any bits in X where the corresponding bits of Y are Zs,
and vice versa, except that we again have to watch out for the case where both
X and Y share some Z bit and, in that case, we have to keep one or the
other.</p>"

  :body (b* (((4vec xval)  (svex-xeval x))
             ((4vec yval)  (svex-xeval y))
             ;; Z is upper 0, lower 1.  so nonZ if (OR UPPER (NOT LOWER))
             (x-nonZ       (logorc2 xval.upper xval.lower))
             (y-nonZ       (logorc2 yval.upper yval.lower))
             (xm-nonZ      (logand mask x-nonZ))
             (ym-nonZ      (logand mask y-nonZ))
             (shared-Zs    (lognand xm-nonZ ym-nonZ))
             ((when (eql 0 shared-Zs))
              ;; There are no overlapping zeroes in any bits that we care
              ;; about, so we can aggressively mask both arguments.
              (list ym-nonZ xm-nonZ))
             ;; Otherwise there are overlapping Zs so we cannot mask them both
             ;; aggressively.  Idea: we will (arbitrarily) mask Y more
             ;; aggressively UNLESS all of the relevant bits of Y are known to
             ;; be constant under the current mask, in which case we would
             ;; probably rather mask X more aggressively.
             (y-x  (logandc2 yval.upper yval.lower))
             (ym-x (logand mask y-x))
             ((when (eql 0 ym-x))
              ;; There are no masked bits of Y that are X, so the parts of Y we
              ;; care about are constant or are nearly constant.  So let's mask
              ;; X more aggressively.
              (list ym-nonZ (logior xm-nonZ shared-Zs))))
          ;; Otherwise, no reason to prefer masking X more aggressively, so
          ;; just arbitrary default to masking Y more aggressively than X.
          (list (logior ym-nonZ shared-Zs) xm-nonZ))
          ;;    )
          ;; (b* ((xval (svex-xeval x))
          ;;      (yval (svex-xeval y))
          ;;      (mask mask))
          ;;   (list (4vec-bitxor-mask mask x y)
          ;;         (4vec-bitxor-mask mask y x))))
  :prepwork ((local (in-theory (disable* bitand-speed-hint not))))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  3vec-fix
                                  4vec-bitxor
                                  4veclist-nth-safe
                                  ))))
          (bitops::logbitp-reasoning
           :add-hints (:in-theory (enable* logbitp-when-4vec-[=-svex-eval-strong)))
          (and stable-under-simplificationp
               '(:bdd (:vars nil)))))

(def-svmask bit? (tests)
  :long "<p>We are considering a @('(bit? tests thens elses)') expression and
we know that we only care about the bits mentioned in @('mask').  We want to
figure out which bits of X and Y we care about.</p>

<p>As a starting point, since @(see 4vec-bit?) operates in a bit-by-bit
fashion, we certainly don't care about any bits that are don't cares in our
outer @('mask').</p>

<p>For @('tests'), for now we don't try to do anything smart&mdash;we just keep
the outer @('mask').  We might consider eventually extending this: if we can
determine that @('thens[i]') and @('elses[i]') agree on some value, then we the
test bit is irrelevant because of the way that @(see 4vec-bit?) does its
merging.  But it doesn't seem like this would help us very often, so for now it
doesn't seem worth doing.</p>

<p>For @('thens'), the main thing we want to take advantage of is that if we
know that @('test[i]') is going to be false, then we don't care about
@('thens[i]') because we're going to choose @('elses[i]') instead.  So, we
improve the mask by excluding any bits of @('tests') that are obviously
false.</p>

<p>For @('elses'), likewise we improve the mask by removing any bits of
@('tests') that are obviously true.</p>"

  :body (b* (((4vec tval) (svex-xeval tests))
             (tests-non0  (logior  tval.upper tval.lower))
             (tests-non1  (lognand tval.upper tval.lower)))
          (list mask
                (logand mask tests-non0)
                (logand mask tests-non1)))
  :prepwork ((local (in-theory (disable not))))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  3vec-fix
                                  3vec-bit?
                                  4vec-bit?
                                  4veclist-nth-safe
                                  ))))
          (bitops::logbitp-reasoning
           :add-hints (:in-theory (enable* logbitp-when-4vec-[=-svex-eval-strong)))
          (and stable-under-simplificationp
               '(:bdd (:vars nil)))
          ))

(local (defthm <-0-when-natp
         (implies (natp x)
                  (equal (< 0 x)
                         (not (equal 0 x))))
         :hints (("goal" :cases ((< 0 x))))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))

(local (defthm loghead-1-is-logbit
         (equal (loghead 1 x)
                (logbit 0 x))
         :hints(("Goal" :in-theory (enable bitops::loghead** bitops::logbitp**)))))

(local (defthm ?-check-lemma-1
         (implies (and (equal (logior (4vec->lower x)
                                      (4vec->upper x))
                              0)
                       (4vec-[= x y))
                  (equal (logior (4vec->lower y)
                                 (4vec->upper y))
                              0))
         :rule-classes nil))

(local (defthm ?-check-lemma-2
         (implies (and (not (equal (logand (4vec->lower x)
                                           (4vec->upper x))
                                   0))
                       (4vec-[= x y))
                  (not (equal (logand (4vec->lower y)
                                      (4vec->upper y))
                              0)))
         :hints(("Goal" :in-theory (enable 4vec-[=))
                (bitops::logbitp-reasoning)
                (and stable-under-simplificationp
                     '(:in-theory (enable bool->bit))))
         :rule-classes nil))

(define svmask-for-?-aux ((mask 4vmask-p)
                          (then svex-p)
                          (else svex-p))
  :parents (svmask-for-?)
  :short "Used when we don't know for sure which way the test will evaluate.
We may not care about the test if then/else are pure-Boolean and agree on all
mask bits."
  :returns (masks 4vmasklist-p)
  (b* ((mask           (4vmask-fix mask))
       ((4vec thenval) (svex-xeval then))
       ((4vec elseval) (svex-xeval else))
       (then-bool      (logeqv thenval.upper thenval.lower)) ;; bits where then is 1/0
       (else-bool      (logeqv elseval.upper elseval.lower)) ;; bits where else is 1/0

       ((when (and (eql (logorc1 mask then-bool) -1) ;; for every care bit, then is 1/0
                   (eql (logorc1 mask else-bool) -1) ;; for every care bit, else is 1/0
                   (eql (logand mask thenval.upper)
                        (logand mask elseval.upper))))
        ;; The obscure case: test/then agree completely on all relevant
        ;; bits, so test doesn't matter.
        (list 0 mask mask)))

    (list -1 mask mask)))

;; (local (defthm logior-zero
;;          (equal (equal 0 (logior x y))
;;                 (and (equal (ifix x) 0)
;;                      (equal (ifix y) 0)))))

;; (local (defthm equal-of-bit->bool
;;             (equal (equal (bit->bool x) (bit->bool y))
;;                    (bit-equiv x y))
;;             :hints(("Goal" :in-theory (enable bit->bool)))))

;; (local (defthm equal-of-bool->bit
;;             (equal (equal (bool->bit x) (bool->bit y))
;;                    (iff x y))))

;; (local (in-theory (disable (:t bit-n))))

(def-svmask ? (test then else)
  :long "<p>We are considering a @('(? test then else)') expression and we know
that we only care about the bits mentioned in @('mask').  We need to figure out
which bits of @('test'), @('then'), and @('else') we care about.</p>

<p>We will almost always need to care about the entire @('test') expression.
The only exceptions to this would be when either:</p>

<ul>

<li>We don't care about any bits at all, i.e., the outer @('mask') is
empty.</li>

<li>For all bits we care about, the corresponding bits of @('then') and
@('else') branches are known to agree.  For instance, @('(? test 5 5)') is
going to be 5 regardless of @('test').  (This is pretty obscure).</li>

</ul>

<p>More obvious and probably more useful mask improvements:</p>

<ul>
<li>When we know that some bit of @('test') is 1, we can completely don't
care @('else');</li>
<li>When we know that all bits of @('test') are 0, we can completely don't
care @('then').</li>
</ul>"

  :body (b* (((when (4vmask-empty mask))
              (list 0 0 0))

             ((4vec testval) (svex-xeval test))
             (test-1s (logand testval.upper testval.lower))
             ((unless (eql test-1s 0))
              ;; There is some bit of the test that is definitely 1, so the
              ;; else branch doesn't matter at all.
              (list test-1s mask 0))

             ((when (and (eql testval.upper 0)
                         (eql testval.lower 0)))
              ;; The test is definitely all 0s, so the then branch doesn't
              ;; matter at all.
              (list -1 0 mask)))

          ;; BOZO this is sound but very slow for the proof of correctness.
          ;; Can we speed this proof up?
          (svmask-for-?-aux mask then else)
          ;;(list -1 mask mask)
          )
  :prepwork
  ((local (defthm svex-apply-?
            (equal (svex-apply '? args)
                   (4vec-? (4veclist-nth-safe 0 args)
                           (4veclist-nth-safe 1 args)
                           (4veclist-nth-safe 2 args)))
            :hints(("Goal" :in-theory (enable svex-apply)))))
   (local (in-theory (disable* not
                               ACL2::BIT-FUNCTIONS-TYPE
                               (:t ACL2::BIT->BOOL)
                               (:t ACL2::BIT-EQUIV)
                               SVEX-EVAL-WHEN-2VEC-P-OF-MINVAL
                               (:t b-ior)
                               (:t b-and)
                               default-car
                               default-cdr
                               (:t svex-kind)
                               SVEX-EVAL-WHEN-FNCALL
                               SVEX-XEVAL-OF-SVEX-FIX-EXPR-NORMALIZE-CONST
                               ACL2::CANCEL_TIMES-EQUAL-CORRECT
                               ACL2::CANCEL_PLUS-EQUAL-CORRECT
                               ACL2::BFIX-WHEN-NOT-BITP
                               ACL2::BFIX-WHEN-BITP
                               ;; all the above are ok
                               ACL2::NOT-BIT->BOOL-FORWARD-TO-BIT-EQUIV-0
                               ACL2::BIT->BOOL-FORWARD-TO-EQUAL-1
                               CAR-OF-SVEXLIST-FIX-X-NORMALIZE-CONST-UNDER-SVEX-EQUIV
                               4VECLIST-P-OF-CDR-WHEN-4VECLIST-P
                               CAR-OF-4VECLIST-FIX-X-NORMALIZE-CONST-UNDER-4VEC-EQUIV
                               CDR-OF-4VECLIST-FIX-X-NORMALIZE-CONST-UNDER-4VECLIST-EQUIV
                               CDR-OF-SVEXLIST-FIX-X-NORMALIZE-CONST-UNDER-SVEXLIST-EQUIV
                               SVEX-EVAL-OF-SVEX-FIX-X-NORMALIZE-CONST
                               SVEX-EVAL-OF-SVEX-ENV-FIX-ENV-NORMALIZE-CONST
                               SVEX-EVAL-OF-QUOTED
;bitand-speed-hint
                               (:e tau-system)

                               ;; the above passed in 551 seconds with AP on.
                               ACL2::NATP-FC-2
                               ACL2::NATP-FC-1
                               default-<-1
                               default-<-2
                               4VMASK-P-WHEN-MEMBER-EQUAL-OF-4VMASKLIST-P
                               (:t bitmaskp)
                               ACL2::NATP-WHEN-GTE-0
                               EQUAL-OF-4VECLIST-FIX-2-FORWARD-TO-4VECLIST-EQUIV
                               EQUAL-OF-4VECLIST-FIX-1-FORWARD-TO-4VECLIST-EQUIV
                               (:t 4veclist-fix)
                               (:t svexlist-eval)
                               ACL2::CANCEL_PLUS-LESSP-CORRECT
                               ACL2::NATP-WHEN-INTEGERP
                               acl2::natp-rw
                               (:t natp)
                               EQUAL-OF-4VMASK-FIX-2-FORWARD-TO-4VMASK-EQUIV
                               EQUAL-OF-4VMASK-FIX-1-FORWARD-TO-4VMASK-EQUIV
                               (:t svex-eval)
                               ;; good, this cuts it down to 443 seconds
                               (:t bitp)
                               BITOPS::LOGIOR-EQUAL-0-FORWARD
                               4VEC-FIX-OF-4VEC
                               BITOPS::LOGBITP-WHEN-BIT
                               (:t 4vmask-p)

                               ))))
  :hints(("Goal"
          :in-theory (enable ;svex-apply
                             4veclist-nth-safe))
         (and stable-under-simplificationp
              '(:in-theory (e/d (4vec-mask
                                 2vec-p
                                 4vec-?
                                 3vec-?
                                 3vec-fix
                                 svmask-for-?-aux
                                 )
                                (bitops::logior-equal-0
                                 ))
                 :use ((:instance ?-check-lemma-1 (x (svex-xeval (car args)))
                                                  (y (svex-eval (car args) env)))
                       (:instance ?-check-lemma-2 (x (svex-xeval (car args)))
                                                  (y (svex-eval (car args) env)))
                       )))
         (progn$ (cw "Using logbitp reasoning~%")
                 (bitops::logbitp-reasoning
                  :add-hints (:in-theory (enable*
                                          4vec-equal
                                          logbitp-when-4vec-[=-svex-eval-strong
                                          ))))
         (and stable-under-simplificationp
              (progn$ (cw "Using BDDs~%")
                      '(:bdd (:vars nil))))
          )
  :otf-flg t)



(define unrev-blocks ((nbits natp)
                      (blocksz posp)
                      (x integerp))
  ;; Inverse function of rev-blocks.
  :measure (nfix nbits)
  :returns (res natp :rule-classes :type-prescription)
  (b* ((nbits (lnfix nbits))
       (blocksz (mbe :logic (acl2::pos-fix blocksz) :exec blocksz))
       ((when (< nbits blocksz))
        (loghead nbits x))
       ;; Take bits [nbits-1:nbits-blocksz] and put them at the bottom.
       ;; Recursively unreverse bits [nbits-blocksz-1:0] and then place them at the top.
       (next-nbits (- nbits blocksz))
       (rest (unrev-blocks next-nbits blocksz x)))
    (logapp blocksz (logtail next-nbits x) rest)))

(define unrev-block-index ((i natp)
                           (nbits natp)
                           (blocksz posp))
  :measure (nfix nbits)
  :returns (idx natp :rule-classes :type-prescription)
  (b* ((nbits (lnfix nbits))
       (blocksz (mbe :logic (acl2::pos-fix blocksz) :exec blocksz))
       (i (lnfix i))
       ((when (< nbits blocksz)) i)
       (next-nbits (- nbits blocksz))
       ((when (< i blocksz)) (+ i next-nbits)))
    (unrev-block-index (- i blocksz) next-nbits blocksz))
  ///
  (local (defun ind (i nbits blocksz x)
           (declare (xargs :measure (nfix nbits)))
           (b* ((nbits (lnfix nbits))
                (blocksz (mbe :logic (acl2::pos-fix blocksz) :exec blocksz))
                (i (lnfix i)))
             (if (< nbits blocksz)
                 (list x i)
               (ind (- i blocksz) (- nbits blocksz) blocksz x)))))

  (defthm logbitp-of-unrev-blocks
    (equal (logbitp i (unrev-blocks nbits blocksz x))
           (and (< (nfix i) (nfix nbits))
                (logbitp (unrev-block-index i nbits blocksz) x)))
    :hints (("goal" :induct (ind i nbits blocksz x)
             :in-theory (enable (:t logbitp) not)
             :expand ((unrev-block-index i nbits blocksz)
                      (unrev-blocks nbits blocksz x)))
            (and stable-under-simplificationp
                 (cw "clause: ~x0~%" clause))))

  (defthm unrev-of-rev-block-index
    (implies (< (nfix i) (nfix nbits))
             (equal (unrev-block-index (rev-block-index i nbits blocksz) nbits blocksz)
                    (nfix i)))
    :hints(("Goal" :in-theory (enable rev-block-index))))

  (defthm unrev-block-index-bound
    (implies (< (nfix i) (nfix nbits))
             (< (unrev-block-index i nbits blocksz) (nfix nbits)))
    :rule-classes :linear)
  (defthm rev-block-index-bound
    (implies (< (nfix i) (nfix nbits))
             (< (rev-block-index i nbits blocksz) (nfix nbits)))
    :hints(("Goal" :in-theory (enable rev-block-index)))
    :rule-classes :linear)

  (defthm rev-of-unrev-block-index
    (implies (< (nfix i) (nfix nbits))
             (equal (rev-block-index (unrev-block-index i nbits blocksz) nbits blocksz)
                    (nfix i)))
    :hints(("Goal" :in-theory (enable rev-block-index)
            :induct (unrev-block-index i nbits blocksz))))


  (defthm unrev-blocks-correct1
    (equal (unrev-blocks nbits blocksz (rev-blocks nbits blocksz x))
           (loghead nbits x))
    :hints((bitops::logbitp-reasoning)))

  (defthm unrev-blocks-correct2
    (equal (rev-blocks nbits blocksz (unrev-blocks nbits blocksz x))
           (loghead nbits x))
    :hints((bitops::logbitp-reasoning))))



(encapsulate nil
  (local (include-book "std/lists/index-of" :dir :system))
  #!bitops
  (local (defun remove-nth (n x)
           (declare (xargs :guard (natp n)))
           (if (atom x)
               nil
             (if (zp n)
                 (cdr x)
               (cons (car x) (remove-nth (1- n) (cdr x)))))))


  (local (defthm nth-of-pseudo-term-list
           (implies (and (pseudo-term-listp x)
                         (< (nfix n) (len x)))
                    (pseudo-termp (nth n x)))))


  #!bitops
  (local (define my-eqbylbp-solve-for-var ((x pseudo-termp)
                                           (var symbolp)
                                           (target pseudo-termp))
           :returns (mv ok
                        (res pseudo-termp :hyp (and (pseudo-termp x)
                                                    (pseudo-termp target))))
           (b* (((when (eqbylbp-is-var x var)) (mv t target))
                ((when (atom x)) (mv nil nil))
                ((when (eq (car x) 'quote)) (mv nil nil))
                ((when (eq (car x) 'unary--))
                 (my-eqbylbp-solve-for-var (cadr x) var `(unary-- ,target)))
                ((when (eq (car x) 'rev-block-index))
                 (my-eqbylbp-solve-for-var
                  (cadr x) var `(unrev-block-index ,target ,(caddr x) (cadddr x))))
                ((when (eq (car x) 'unrev-block-index))
                 (my-eqbylbp-solve-for-var
                  (cadr x) var `(rev-block-index ,target ,(caddr x) (cadddr x))))
                (var-index (acl2::index-of var (cdr x)))
                ((when (and var-index
                            (consp target)
                            (equal (len (cdr target))
                                   (len (cdr x)))
                            (equal (car x) (car target))
                            (equal (remove-nth var-index (cdr x))
                                   (remove-nth var-index (cdr target)))))
                 (mv t (nth var-index (cdr target))))
                ((unless (eq (car x) 'binary-+))
                 (cw "x: ~x0 var: ~x1 target: ~x2~%" x var target)
                 (mv nil nil))
                ((when (eqbylbp-is-var (cadr x) var))
                 (mv t `(binary-+ ,target (unary-- ,(caddr x))))))
             (my-eqbylbp-solve-for-var
              (caddr x) var
              `(binary-+ ,target (unary-- ,(cadr x)))))))

  (local (defattach bitops::eqbylbp-solve-for-var bitops::my-eqbylbp-solve-for-var))

  (local (defthm lemma1
           (IMPLIES
            (AND (EQUAL (LOGIOR x1
                                (LOGNOT (UNREV-BLOCKS n b m)))
                        (LOGIOR x
                                (LOGNOT (UNREV-BLOCKS n b m)))))
            (equal (EQUAL (LOGIOR (LOGNOT m)
                                  (REV-BLOCKS n b x))
                          (LOGIOR (LOGNOT m)
                                  (REV-BLOCKS n b x1)))
                   t))
           :hints ((bitops::logbitp-reasoning))))

  (local (defthm lemma2
           (IMPLIES
            (AND (EQUAL (LOGAND x1
                                (UNREV-BLOCKS n b m))
                        (LOGAND x
                                (UNREV-BLOCKS n b m))))
            (equal (EQUAL (LOGAND m
                                  (REV-BLOCKS n b x))
                          (LOGAND m
                                  (REV-BLOCKS n b x1)))
                   t))
           :hints ((bitops::logbitp-reasoning))))

  (def-svmask blkrev (n b x)
    :body
    (b* (((when (4vmask-empty mask))
          (list 0 0 0))
         (nval (svex-xeval n))
         (bval (svex-xeval b))
         (mask mask)
         ((when (and (2vec-p nval)
                     (2vec-p bval)
                     (<= 0 (2vec->val nval))
                     (< 0 (2vec->val bval))))
          (b* ((n (2vec->val nval))
               (b (2vec->val bval)))
            (list -1 -1 (unrev-blocks n b mask)))))
      (list -1 -1 -1))
    :hints (("Goal" :in-theory (e/d (svex-apply
                                     4veclist-nth-safe)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (svex-apply
                                    4vec-mask
                                    4veclist-nth-safe
                                    4vec-rev-blocks
                                    4vec-index-p)))))
    :otf-flg t))


(local (defthm 4vmasklist-of-replicate-mask
         (implies (4vmask-p m)
                  (4vmasklist-p (replicate n m)))
         :hints(("Goal" :in-theory (enable replicate)))))

(defthm 4veclist-mask-of-replicate-neg-1
  (equal (4veclist-mask (replicate n -1) args)
         (4veclist-fix args))
  :hints(("Goal" :in-theory (enable replicate 4veclist-mask 4veclist-fix)
          :induct (nth n args))))


(define svmask-for-unknown-function ((mask 4vmask-p) (args svexlist-p))
  :returns (m (4vmasklist-p m))
  (replicate (len args)
             (4vmask-all-or-none mask))
  ///

  (local (in-theory (enable 4vmask-all-or-none)))

  (defthm svmask-for-unknown-function-correct
    (implies (and (equal (4veclist-mask
                          (svmask-for-unknown-function mask args)
                          (svexlist-eval args env))
                         (4veclist-mask
                          (svmask-for-unknown-function mask args)
                          args1))
                  (syntaxp (not (equal args1 `(svexlist-eval ,args ,env)))))
             (equal (4vec-mask mask (svex-apply fn args1))
                    (4vec-mask mask (svex-apply fn (svexlist-eval args env))))))
  (fty::deffixequiv svmask-for-unknown-function))

(defun svex-argmasks-cases-fn (op-table)
  (declare (xargs :mode :program))
  (if (atom op-table)
      '((otherwise (svmask-for-unknown-function mask args)))
    (cons (let* ((sym (caar op-table))
                 (maskfn (intern$ (cat "SVMASK-FOR-" (symbol-name sym)) "SV")))
            `(,sym (,maskfn mask args)))
          (svex-argmasks-cases-fn (cdr op-table)))))

(defmacro svex-argmasks-cases (fn)
  `(case ,fn . ,(svex-argmasks-cases-fn *svex-op-table*)))



(define 4vmasklist-len-fix ((n natp) (x 4vmasklist-p))
  :inline t
  :verify-guards nil
  :returns (xx 4vmasklist-p)
  (if (zp n)
      nil
    (if (atom x)
        (cons -1 (4vmasklist-len-fix (1- n) nil))
      (cons (4vmask-fix (car x))
            (4vmasklist-len-fix (1- n) (cdr x)))))
  ///
  (local (defthm 4vmasklist-len-fix-when-len-ok
           (implies (equal (nfix n) (len x))
                    (equal (4vmasklist-len-fix n x)
                           (4vmasklist-fix x)))
           :hints(("Goal" :in-theory (enable 4vmasklist-fix)))))
  (verify-guards 4vmasklist-len-fix$inline
    :hints (("goal" :expand ((4vmasklist-p x)))))

  (defthm len-of-4vmasklist-len-fix
    (equal (len (4vmasklist-len-fix n x))
           (nfix n)))

  (defthm 4vmasklist-len-fix-of-cons
    (equal (4vmasklist-len-fix n (cons a b))
           (if (zp n)
               nil
             (cons (4vmask-fix a) (4vmasklist-len-fix (1- n) b)))))

  (defthm 4vmasklist-len-fix-of-0
    (equal (4vmasklist-len-fix 0 args) nil))

  (fty::deffixequiv 4vmasklist-len-fix)

  (local (defun ind (len m x)
           (if (atom x)
               (list len m)
             (ind (1- len) (cdr m) (cdr x)))))


  (defthm 4veclist-mask-of-4vmasklist-len-fix
    (implies (<= (len x) (nfix len))
             (equal (4veclist-mask (4vmasklist-len-fix len m) x)
                    (4veclist-mask m x)))
    :hints(("Goal" :in-theory (enable 4veclist-mask 4veclist-fix)
            :induct (ind len m x))))

  (defthm 4veclist-mask-of-len-fix
    (equal (4veclist-mask (4vmasklist-len-fix len (cons mask1 masks)) args)
           (and (consp args)
                (if (zp len)
                    (4veclist-fix args)
                  (cons (4vec-mask mask1 (4veclist-nth-safe 0 args))
                        (4veclist-mask (4vmasklist-len-fix (1- len) masks)
                                       (cdr args))))))
    :hints(("Goal" :in-theory (enable 4veclist-mask 4veclist-nth-safe))))

  (defthm 4veclist-mask-of-len-fix-nthcdr
    (equal (4veclist-mask (4vmasklist-len-fix len (cons mask1 masks))
                          (nthcdr n args))
           (and (consp (nthcdr n args))
                (if (zp len)
                    (4veclist-fix (nthcdr n args))
                  (cons (4vec-mask mask1 (4veclist-nth-safe n args))
                        (4veclist-mask (4vmasklist-len-fix (1- len) masks)
                                       (nthcdr (+ 1 (nfix n)) args))))))
    :hints(("Goal" :in-theory (e/d (4veclist-mask 4veclist-nth-safe)
                                   (4vmasklist-len-fix))))))



(define svex-argmasks
  :parents (4vmask)
  :short "Statically compute the care masks for a function's arguments,
starting from the care mask for the result of the function application."

  ((mask 4vmask-p
         "Outer care mask, i.e., the care mask for the whole expression
          @('fn(args)').")
   (fn   fnsym-p
         "The function being applied.")
   (args svexlist-p
         "The arguments that @('fn') is being applied to, whose care masks we
          want to determine."))
  :returns
  (argmasks (and (4vmasklist-p argmasks)
                 (equal (len argmasks) (len args)))
            "Care masks to use for the arguments.")

  :long "<p>This function understands the SVEX @(see functions) and which bits
of their arguments are sure to influence which bits of their outputs.  For
example, if we are given a function like:</p>

@({
     (bitsel 4 <bigexpr>)
})

<p>and if the initial, outer @(see 4vmask) for the whole expression is @('-1'),
i.e., we care about all of the bits of the result, then we will produce two new
masks, one for each of the function's arguments:</p>

<ul>

<li>For @('4'), we will just care about all the bits, i.e., our mask will be
@('-1').  This expression is already a constant anyway so there isn't much hope
of simplifying it further and it poses no problems in computations such as
reaching a compositional fixpoint.</li>

<li>For @('<bigexpr>'), since we are selecting bit 4, we obviously only care
about the fourth bit.  Accordingly, the resulting care mask will be
@('#b1000').  Knowing that we only care about the fourth bit of @('<bigexpr>')
may allow us to make important simplifications to it, and may also allow us to
generate better (more restrictive) care masks for its subexpressions.</li>

</ul>

<p>In this way, care mask information can flow downward, starting from the
outside of the expression and into the arguments.</p>"

  (if (4vmask-empty mask)
      (replicate (len args) 0)
    (4vmasklist-len-fix (len args)
                        (svex-argmasks-cases (mbe :logic (fnsym-fix fn) :exec fn))))
  ///

  (local (defthm equal-of-fnsym-fix-fwd
         (implies (equal (fnsym-fix fn) x)
                  (fnsym-equiv fn x))
         :rule-classes :forward-chaining))

  (local (Defun ind (len masks args0 args1)
           (declare (xargs :measure (+ (len args0) (len args1))))
           (if (and (atom args0) (atom args1))
               (list len masks)
             (ind (1- len) (cdr masks) (cdr args0) (cdr args1)))))

  (local (defthm rewrite-equal-of-4veclist-mask-len-fix
           (iff (equal (4veclist-mask (4vmasklist-len-fix len masks) args0)
                       (4veclist-mask (4vmasklist-len-fix len masks) args1))
                (and (equal (4veclist-mask masks args0) (4veclist-mask masks args1))
                     (hide (equal (4veclist-mask (4vmasklist-len-fix len masks) args0)
                                  (4veclist-mask (4vmasklist-len-fix len masks) args1)))))
           :hints (("goal" :in-theory (enable 4veclist-mask
                                              4vmasklist-len-fix
                                              4veclist-fix)
                    :expand ((:free (x) (hide x)))
                    :induct (ind len masks args0 args1)))))

  (local (in-theory (disable 4veclist-mask-of-4vmasklist-len-fix)))


  (defthm svex-argmasks-correct
    (implies (and (equal (4veclist-mask
                          (svex-argmasks mask fn args)
                          (svexlist-eval args env))
                         (4veclist-mask
                          (svex-argmasks mask fn args)
                          args1))
                  (syntaxp (not (equal args1 `(svexlist-eval ,args ,env)))))
             (equal (4vec-mask mask (svex-apply fn args1))
                    (4vec-mask mask (svex-apply fn (svexlist-eval args env))))))

  (defthm svex-argmasks-correct2
    (implies (and (equal (4veclist-mask
                          (svex-argmasks mask fn args)
                          args1)
                         (4veclist-mask
                          (svex-argmasks mask fn args)
                          (svexlist-eval args env)))
                  (syntaxp (not (equal args1 `(svexlist-eval ,args ,env)))))
             (equal (4vec-mask mask (svex-apply fn args1))
                    (4vec-mask mask (svex-apply fn (svexlist-eval args env)))))
    :hints (("goal" :use svex-argmasks-correct
             :in-theory (disable svex-argmasks-correct))))

  (fty::deffixequiv svex-argmasks)

  (defthm svex-argmasks-of-none
    (implies (4vmask-empty mask)
             (equal (svex-argmasks mask fn args)
                    (replicate (len args) 0))))

  (defthm 4veclist-mask-idempotent
    (Equal (4veclist-mask masks (4veclist-mask masks x))
           (4veclist-mask masks x))
    :hints(("Goal" :in-theory (enable 4veclist-mask))))

  (defthm svex-argmasks-remove-mask
    (equal (4vec-mask mask (svex-apply fn (4veclist-mask
                                           (svex-argmasks mask fn args)
                                           (svexlist-eval args env))))
           (4vec-mask mask (svex-apply fn (svexlist-eval args env))))
    :hints(("Goal" :in-theory (disable svex-argmasks
                                       svex-argmasks-correct
                                       svex-argmasks-correct2)
            :use ((:instance svex-argmasks-correct
                   (args1 (4veclist-mask
                           (svex-argmasks mask fn args)
                           (svexlist-eval args env)))))))))





;; (define 4vec-bitand-mask
;;   :parents (svmask-for-bitand)
;;   :inline t
;;   :ignore-ok t
;;   :irrelevant-formals-ok t
;;   ((mask 4vmask-p)
;;    (xval 4vec-p)
;;    (yval 4vec-p))

;;   (logand (4vmask-fix mask)
;;           ;; Recall that 0 is encoded as upper 0, lower 0.
;;           ;; So whenever Yi.lower or Yi.upper are set, Yi is nonzero, so
;;           ;; we can't improve on the mask that way.

;;           ;; But why do we care about x.upper and x.lower here?
;;           ;; Aha, well, if X is 0 AND Y is 0, then we can't mark them both
;;           ;; as irrelevant.  Can we keep any bits where X is known
;;           ;; to be zero?  Yes, this seems to work.

;;           ;; OK, so which is better?  It seems like mine might be better?

;;           ;; (defconst *mask* #b1111)
;;           ;; (defconst *zx10* (make-4vec :upper #b0110 :lower #b1010))
;;           ;; (defconst *zzzz* (make-4vec :upper #b0000 :lower #b1111))
;;           ;; (defconst *xxxx* (make-4vec :upper #b1111 :lower #b0000))
;;           ;; (defconst *1111* (make-4vec :upper #b1111 :lower #b1111))
;;           ;; (defconst *0000* (make-4vec :upper #b0000 :lower #b0000))

;;           ;; (4vec-bitand *zx10* *0000*) ;; 0            == 0000
;;           ;; (4vec-bitand *zx10* *1111*) ;; (1110 . 10)  == XX10
;;           ;; (4vec-bitand *zx10* *xxxx*) ;; (1110 . 0)   == XXX0
;;           ;; (4vec-bitand *zx10* *zzzz*) ;; (1110 . 0)   == XXX0

;;           ;;                                         ;; sol's        mine
;;           ;; (4vec-bitand-mask *mask* *zx10* *0000*) ;; 1011    vs.  0000 --->no, 0001 instead
;;           ;; (4vec-bitand-mask *mask* *zx10* *1111*) ;; 1111         1111
;;           ;; (4vec-bitand-mask *mask* *zx10* *zzzz*) ;; 1111         1111
;;           ;; (4vec-bitand-mask *mask* *zx10* *xxxx*) ;; 1111         1111

;;           ;; So it seems like this is strictly fewer bits, perhaps therefore
;;           ;; better?  Is there any other intuition we need to consider?

;;           (let ((x-is-zero (lognor (4vec->lower xval)
;;                                    (4vec->upper xval)))
;;                 ;; Sol's term:
;;                 ;; (x-is-constant (logior (4vec->lower xval)
;;                 ;;                        (lognot (4vec->upper xval))))
;;                 )
;;             (logior x-is-zero  ;; or x-is-constant??
;;                     (4vec->lower yval)           ; Yi is Z or 1  -- Yi is nonzero
;;                     (4vec->upper yval)           ; Yi is X or 1  --
;;                     ))))




;; So that seems perfectly reasonable, right??

        ;; Upper  Lower  Value
        ;;   0      0      0
        ;;   0      1      Z
        ;;   1      0      X
        ;;   1      1      1





