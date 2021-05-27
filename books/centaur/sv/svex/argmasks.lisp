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
(include-book "seval")
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

(local (defthm logbitp-of-bool->vec
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

;; (defthm 4veclist-nth-safe-of-nthcdr
;;   (equal (4veclist-nth-safe m (nthcdr n x))
;;          (4veclist-nth-safe (+ (nfix m) (nfix n)) x))
;;   :hints(("Goal" :in-theory (enable 4veclist-nth-safe))))




;; (local (in-theory (disable nth-open-constidx nth)))




;; (defthm equal-of-4veclist-mask-nil
;;   (equal (equal (4veclist-mask nil x)
;;                 (4veclist-mask nil y))
;;          (equal (4veclist-fix x)
;;                 (4veclist-fix y)))
;;   :hints(("Goal" :in-theory (enable 4veclist-mask 4veclist-fix))))


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
           bitops::lognot-natp

           acl2::loghead-identity
           SVEX-EVAL-WHEN-FNCALL
           SVEX-EVAL-WHEN-QUOTE
           signed-byte-p
           unsigned-byte-p
           acl2::integer-range-p
           default-car
           default-cdr
           default-<-1
           default-<-2
           DEFAULT-+-1
           default-+-2

           ;; ok through here

           ACL2::LOGEXT-IDENTITY
           ACL2::BFIX-WHEN-NOT-BITP
           ACL2::CANCEL_TIMES-EQUAL-CORRECT
           ACL2::CANCEL_PLUS-EQUAL-CORRECT
           ACL2::CANCEL_PLUS-LESSP-CORRECT
           SVEX-EVAL-OF-QUOTED
           ;; 4VMASK-P-WHEN-MEMBER-EQUAL-OF-4VMASKLIST-P

           )))


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


;; (defun destructor-elim-entry-p (hist-entry)
;;   (let ((processor (access acl2::history-entry hist-entry :processor)))
;;     (eq processor 'acl2::eliminate-destructors-clause)))

;; (defun history-has-destructor-elim-entry-p (hist)
;;   (if (atom hist)
;;       nil
;;     (or (destructor-elim-entry-p (car hist))
;;         (history-has-destructor-elim-entry-p (cdr hist)))))

;; (defmacro after-destructor-elimination-p ()
;;   `(history-has-destructor-elim-entry-p acl2::hist))

(local (defthmd hide-past-first-arg
         (and
          (equal (equal (4veclist-fix (svexlist-eval (rest args) env)) y)
                 (hide (equal (svexlist-eval (rest args) env) y)))
          (equal (equal (svexlist-eval (rest args) env) y)
                 (hide (equal (svexlist-eval (rest args) env) y))))
         :hints(("Goal" :expand ((:free (x) (hide x)))))))

(local (defthmd hide-past-second-arg
         (and
          (equal (equal (4veclist-fix (svexlist-eval (rest (rest args)) env)) y)
                 (hide (equal (svexlist-eval (rest (rest args)) env) y)))
          (equal (equal (svexlist-eval (rest (rest args)) env) y)
                 (hide (equal (svexlist-eval (rest (rest args)) env) y))))
         :hints(("Goal" :expand ((:free (x) (hide x)))))))

(local (defthmd hide-past-third-arg
         (and
          (equal (equal (4veclist-fix (svexlist-eval (rest (rest (rest args))) env)) y)
                 (hide (equal (svexlist-eval (rest (rest (rest args))) env) y)))
          (equal (equal (svexlist-eval (rest (rest (rest args))) env) y)
                 (hide (equal (svexlist-eval (rest (rest (rest args))) env) y))))
         :hints(("Goal" :expand ((:free (x) (hide x)))))))


(def-svmask id (x)
  :long "<p>Since the identity just passes its argument through verbatim, it
doesn't seem like there's any way to improve on the outer care mask here.</p>"
  :inline t
  :nobindings t
  :body (list mask)
  :hints (("Goal" :in-theory (enable svex-apply))))

(def-svmask unfloat (x)
  :long "<p>Unfloating just turns X bits into Z bits without moving any bits
around or merging them together, it doesn't seem like there's any way to
improve on the outer care mask here.</p>"
  :inline t
  :nobindings t
  :body (list mask)
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe
                                   hide-past-first-arg)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  3vec-fix))))
          (bitops::logbitp-reasoning)))

(def-svmask bitnot (x)
  :long "<p>Since bitwise negation just negates bits without moving them around
or merging them together, it doesn't seem like there's any way to improve on
the outer care mask here.</p>"
  :inline t
  :nobindings t
  :body (list mask)
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe
                                   hide-past-first-arg)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (4vec-mask
                                  3vec-fix
                                  3vec-bitnot
                                  4vec-bitnot))))
          (bitops::logbitp-reasoning)))

(def-svmask onp (x)
  :long "<p>Since @('onp') just turns Z bits into 0s without moving them around
or merging them together, it doesn't seem like there's any way to improve on
the outer care mask here.</p>"
  :inline t
  :nobindings t
  :body (list mask)
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe
                                   hide-past-first-arg)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (4vec-mask
                                  3vec-fix
                                  4vec-onset))))
          (bitops::logbitp-reasoning)))

(def-svmask offp (x)
  :long "<p>Since @('offp') affects each bit, without moving bits around or
merging them together, it doesn't seem like there's any way to improve on the
outer care mask here.</p>"
  :inline t
  :nobindings t
  :body (list mask)
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe
                                   hide-past-first-arg)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (4vec-mask
                                  3vec-fix
                                  4vec-offset))))
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
                                    hide-past-second-arg))
         (and stable-under-simplificationp
              '(:in-theory (enable 4vec-mask
                                   4vec-res)))
         (bitops::logbitp-reasoning)))

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
                                   4veclist-nth-safe
                                   hide-past-first-arg)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (4vec-mask
                                  3vec-fix
                                  4vmask-all-or-none
                                  4vec-reduction-and
                                  3vec-reduction-and))))))

(def-svmask uor (x)
  :long "<p>See @(see svmask-for-uand); the same reasoning applies here.</p>"
  :inline t
  :body (list (4vmask-all-or-none mask))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe
                                   hide-past-first-arg)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (4vec-mask
                                  3vec-fix
                                  4vmask-all-or-none
                                  4vec-reduction-or
                                  3vec-reduction-or))))))

(def-svmask uxor (x)
  :long "<p>See @(see svmask-for-uand); the same reasoning applies here.</p>"
  :inline t
  :body (list (4vmask-all-or-none mask))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe
                                   hide-past-first-arg)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (4vec-mask
                                  3vec-fix
                                  4vmask-all-or-none
                                  4vec-parity))))))

(defthm 4vmask-when-mask-0
  (implies (equal (sparseint-val (4vmask-fix mask)) 0)
           (equal (4vec-mask mask x) '(-1 . 0)))
  :hints(("Goal" :in-theory (enable 4vec-mask))))

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
                                    hide-past-second-arg))
         (and stable-under-simplificationp
              '(:in-theory (enable 4vmask-all-or-none)))))

(def-svmask u- (x)
  :long "<p>As in @(see svmask-for-+), we can't do anything smart here because
of global X/Z detection.</p>"
  :inline t
  :nobindings t
  :body (list (4vmask-all-or-none mask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    hide-past-first-arg))
         (and stable-under-simplificationp
              '(:in-theory (enable 4vmask-all-or-none)))))

(def-svmask b- (x y)
  :long "<p>As in @(see svmask-for-+), we can't do anything smart here because
of global X/Z detection.</p>"
  :inline t
  :nobindings t
  :body (b* ((argmask (4vmask-all-or-none mask)))
          (list argmask argmask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    hide-past-second-arg))
         (and stable-under-simplificationp
              '(:in-theory (enable 4vmask-all-or-none)))))

(def-svmask * (x y)
  :long "<p>As in @(see svmask-for-+), we can't do anything smart here because
of global X/Z detection.</p>"
  :inline t
  :nobindings t
  :body (b* ((argmask (4vmask-all-or-none mask)))
          (list argmask argmask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    hide-past-second-arg))
         (and stable-under-simplificationp
              '(:in-theory (enable 4vmask-all-or-none)))))

(def-svmask / (x y)
  :long "<p>As in @(see svmask-for-+), we can't do anything smart here because
of global X/Z detection.</p>"
  :inline t
  :nobindings t
  :body (b* ((argmask (4vmask-all-or-none mask)))
          (list argmask argmask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    hide-past-second-arg))
         (and stable-under-simplificationp
              '(:in-theory (enable 4vmask-all-or-none)))))

(def-svmask % (x y)
  :long "<p>As in @(see svmask-for-+), we can't do anything smart here because
of global X/Z detection.</p>"
  :inline t
  :nobindings t
  :body (b* ((argmask (4vmask-all-or-none mask)))
          (list argmask argmask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    hide-past-second-arg))
         (and stable-under-simplificationp
              '(:in-theory (enable 4vmask-all-or-none)))))

(def-svmask < (x y)
  :long "<p>As in @(see svmask-for-+), we can't do anything smart here because
of global X/Z detection.</p>"
  :inline t
  :nobindings t
  :body (b* ((argmask (4vmask-all-or-none mask)))
          (list argmask argmask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    hide-past-second-arg))
         (and stable-under-simplificationp
              '(:in-theory (enable 4vmask-all-or-none)))))

(def-svmask == (x y)
  :long "<p>As in @(see svmask-for-+), we can't do anything smart here because
of global X/Z detection.</p>"
  :inline t
  :nobindings t
  :body (b* ((argmask (4vmask-all-or-none mask)))
          (list argmask argmask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    hide-past-second-arg))
         (and stable-under-simplificationp
              '(:in-theory (enable 4vmask-all-or-none)))))

(def-svmask clog2 (x)
  :long "<p>As in @(see svmask-for-+), we can't do anything smart here because
of global X/Z detection.</p>"
  :inline t
  :nobindings t
  :body (list (4vmask-all-or-none mask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    hide-past-first-arg))
         (and stable-under-simplificationp
              '(:in-theory (enable 4vmask-all-or-none)))))

(def-svmask pow (x y)
  :long "<p>As in @(see svmask-for-+), we can't do anything smart here because
of global X/Z detection.</p>"
  :inline t
  :nobindings t
  :body (b* ((argmask (4vmask-all-or-none mask)))
          (list argmask argmask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    hide-past-first-arg))
         (and stable-under-simplificationp
              '(:in-theory (enable 4vmask-all-or-none)))))

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
                                    hide-past-first-arg))
         (and stable-under-simplificationp
              '(:in-theory (enable 4vmask-all-or-none)))))

(def-svmask countones (x)
  :long "<p>We can't do anything smart here.</p>"
  :inline t
  :nobindings t
  :body (list (4vmask-all-or-none mask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    hide-past-first-arg))
         (and stable-under-simplificationp
              '(:in-theory (enable 4vmask-all-or-none)))))

(def-svmask onehot (x)
  :long "<p>We can't do anything smart here that I can think of.</p>"
  :inline t
  :nobindings t
  :body (list (4vmask-all-or-none mask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    hide-past-first-arg))
         (and stable-under-simplificationp
              '(:in-theory (enable 4vmask-all-or-none)))))

(def-svmask onehot0 (x)
  :long "<p>We can't do anything smart here that I can think of.</p>"
  :inline t
  :nobindings t
  :body (list (4vmask-all-or-none mask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    hide-past-first-arg))
         (and stable-under-simplificationp
              '(:in-theory (enable 4vmask-all-or-none)))))

(def-svmask === (x y)
  :long "<p>We can't do anything smart here because @('(=== x y)') cares about
every bit of X and Y, with no short circuiting or any kind.</p>"
  :inline t
  :nobindings t
  :body (b* ((argmask (4vmask-all-or-none mask)))
          (list argmask argmask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    hide-past-second-arg))
         (and stable-under-simplificationp
              '(:in-theory (enable 4vmask-all-or-none)))))

(def-svmask ===* (x y)
  :long "<p>We can't do anything smart here because @('(=== x y)') cares about
every bit of X and Y, with no short circuiting or any kind.</p>"
  :inline t
  :nobindings t
  :body (b* ((argmask (4vmask-all-or-none mask)))
          (list argmask argmask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    hide-past-second-arg))
         (and stable-under-simplificationp
              '(:in-theory (enable 4vmask-all-or-none)))))


(local (defthm sparseint-val-of-s4vec->lower
         (equal (sparseint-val (s4vec->lower x))
                (4vec->lower (s4vec->4vec x)))
         :hints(("Goal" :in-theory (enable s4vec->4vec)))))
(local (defthm sparseint-val-of-s4vec->upper
         (equal (sparseint-val (s4vec->upper x))
                (4vec->upper (s4vec->4vec x)))
         :hints(("Goal" :in-theory (enable s4vec->4vec)))))

(local (in-theory (disable 4VEC->UPPER-OF-S4VEC->4VEC
                           4VEC->LOWER-OF-S4VEC->4VEC)))

(def-svmask safer-==? (a b)
  :long "<p>We are considering @('(safer-==? a b)') and we want to compute the care
masks for @('a') and @('b'), given some outer care mask for the whole
expression.</p>

<p>The outer mask doesn't much matter since there's nothing bitwise about this,
except that if the whole outer mask is zero then we (of course) don't care
about any bits at all.</p>

<p>We can't do anything smart for @('b'), but for @('a') we definitely don't
care about any bits that are Z in @('b'), since @(see 4vec-wildeq) doesn't care
about the corresponding bit in @('a').</p>"

  :body (b* (((when (sparseint-equal mask 0))
              ;; Don't care about any bits at all.
              (list 0 0))
             ((s4vec bval) (svex-s4xeval b))
             (b-nonz (sparseint-bitorc2 bval.upper bval.lower)))
          (list b-nonz -1))
  :prepwork ((local (in-theory (disable* not))))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    hide-past-second-arg))
         (and stable-under-simplificationp
              '(:in-theory (e/d (4vec-wildeq-safe
                                 3vec-reduction-and
                                 3vec-bitor
                                 3vec-bitnot
                                 4vec-bitxor
                                 4vec-mask
                                 4vec-[=)
                                (svex-eval-gte-xeval))
                :use ((:instance svex-eval-gte-xeval (x (car args)))
                      (:instance svex-eval-gte-xeval (x (cadr args))))))
         (bitops::logbitp-reasoning)
         (and stable-under-simplificationp '(:bdd (:vars nil)))))

(def-svmask ==? (a b)
  :long "<p>We just reuse the argmasks for @('safer-==?') here.  We could
someday check for bits in @('b') that are known to be @('x') and mark them as
don't-cares for @('a'), but we currently don't have a good way to find bits
that are known to be @('x').</p>"

  :body (b* (((when (sparseint-equal mask 0))
              ;; Don't care about any bits at all.
              (list 0 0))
             ((s4vec bval) (svex-s4xeval b))
             (b-nonz (sparseint-bitorc2 bval.upper bval.lower)))
          (list b-nonz -1))
  :prepwork ((local (in-theory (disable* not))))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    hide-past-second-arg))
         (and stable-under-simplificationp
              '(:in-theory (e/d (4vec-wildeq
                                 3vec-reduction-and
                                 3vec-bitor
                                 3vec-bitnot
                                 4vec-bitxor
                                 4vec-mask
                                 4vec-[=)
                                (svex-eval-gte-xeval))
                :use ((:instance svex-eval-gte-xeval (x (car args)))
                      (:instance svex-eval-gte-xeval (x (cadr args))))))
         (bitops::logbitp-reasoning)
         (and stable-under-simplificationp '(:bdd (:vars nil)))))


(encapsulate nil
  (local (in-theory (disable bitops::logbitp-when-bit
                             svex-eval-when-2vec-p-of-minval
                             2vec-p)))

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
    (b* (((s4vec aval) (svex-s4xeval a))
         ((s4vec bval) (svex-s4xeval b))
         (a-is-not-z      (sparseint-bitorc2 aval.upper aval.lower))
         (b-is-not-z      (sparseint-bitorc2 bval.upper bval.lower))
         (both-are-z  (sparseint-bitnor a-is-not-z b-is-not-z))
         ((when (sparseint-equal both-are-z 0))
          ;; No overlap, can mask both aggressively.
          (list b-is-not-z a-is-not-z))

         ;; Otherwise there are overlapping Zs so we cannot mask them both
         ;; aggressively.  Idea: we will (arbitrarily) mask B more aggressively
         ;; UNLESS all of the bits of B are known to be constant.
         (not-b-x  (sparseint-test-bitandc2 bval.upper bval.lower))
         ((when (not not-b-x))
          ;; We know all bits of B.  Let's mask A more aggressively, then.
          (list b-is-not-z
                (sparseint-bitnand a-is-not-z both-are-z))))
      ;; Otherwise, no reason to prefer masking A more aggressively, so just
      ;; arbitrary default to masking B more aggressively than A.
      (list (sparseint-bitnand b-is-not-z both-are-z)
            a-is-not-z))
    :prepwork ((local (in-theory (disable not))))
    :hints(("Goal"
            :in-theory (enable svex-apply
                               4veclist-nth-safe
                               hide-past-second-arg))
           (and stable-under-simplificationp
                '(:in-theory (e/d (4vec-symwildeq
                                   3vec-reduction-and
                                   3vec-bitor
                                   3vec-bitnot
                                   4vec-bitxor
                                   4vec-mask
                                   4vec-[=)
                                  (svex-eval-gte-xeval))
                  :use ((:instance svex-eval-gte-xeval (x (car args)))
                        (:instance svex-eval-gte-xeval (x (cadr args))))))
           (bitops::logbitp-reasoning
            :simp-hint (:IN-THEORY (ENABLE* LOGBITP-CASE-SPLITS
                                            ;; BITOPS::LOGBITP-WHEN-BIT
                                            BITOPS::LOGBITP-OF-CONST-SPLIT))
            :add-hints (:IN-THEORY (ENABLE* LOGBITP-CASE-SPLITS
                                            ;; BITOPS::LOGBITP-WHEN-BIT
                                            BITOPS::LOGBITP-OF-CONST-SPLIT))
            :passes 2)
           (and stable-under-simplificationp
                '(:bdd (:vars nil))))))

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
  :body (b* (((s4vec sval)    (svex-s4xeval stronger))
             (strong-nonbool (sparseint-bitxor sval.upper sval.lower))
             (weak-mask      (sparseint-bitand mask strong-nonbool)))
          (list mask weak-mask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth-safe
                                    hide-past-second-arg))
         (and stable-under-simplificationp
              '(:in-theory (e/d (4vec-mask
                                 4vec-override
                                 4vec-[=)
                                (svex-eval-gte-xeval))
                :use ((:instance svex-eval-gte-xeval (x (car args)))
                      (:instance svex-eval-gte-xeval (x (cadr args))))))
         (bitops::logbitp-reasoning)))


(local (defthm xeval-non-x-implies-eval-is-xeval
         (implies (equal (4vec->upper (svex-xeval x))
                         (4vec->lower (svex-xeval x)))
                  (equal (svex-eval x env)
                         (svex-xeval x)))
         :hints (("goal" :use ((:instance svex-eval-gte-xeval))
                  :in-theory (disable svex-eval-gte-xeval)))))

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
  (b* ((nval  (svex-s4xeval n))
       (nmask (4vmask-all-or-none mask))
       ((unless (s4vec-2vec-p nval))
        ;; N is not statically known, so we don't know which bit we care about.
        (list nmask nmask))
       (nv (s4vec->upper nval))
       ((when (sparseint-< nv 0))
        ;; N is negative so we don't care about X at all, the bitsel returns Xes
        (list nmask 0)))
    ;; N is a positive, so we care about exactly the nth bit.
    (list nmask
          (sparseint-concatenate (sparseint-val nv) 0 (int-to-sparseint (sparseint-bit 0 mask)))))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe
                                   hide-past-second-arg)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (4vmask-all-or-none
                                  4vec-mask
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

  :body (b* ((nmask (4vmask-all-or-none mask))
             (nval (svex-s4xeval n))
             ((unless (s4vec-2vec-p nval))
              ;; Can't statically resolve N.  Well, we at least don't care
              ;; about any bits that aren't part of our mask.
              (list nmask mask))
             (nv (s4vec->upper nval))
             ((when (sparseint-< nv 0))
              ;; Negative index, going to just be all Xes, mask for x is
              ;; irrelevant.
              (list nmask 0)))
          (list nmask (sparseint-concatenate (sparseint-val nv) mask 0)))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe
                                   hide-past-second-arg)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (4vec-zero-ext
                                  4vmask-all-or-none
                                  4vec-mask
                                  4vec-[=
                                  )
                                 (svex-eval-gte-xeval))
                 :use ((:instance svex-eval-gte-xeval (x (car args))))))
          (bitops::logbitp-reasoning)))

(define mask-for-fixed-signx ((mask 4vmask-p) (n natp))
  :parents (svmask-for-signx)
  :returns (mask 4vmask-p)
  :inline t
  (if (zp n)
      (if (sparseint-equal mask 0) 0 1)
    (sparseint-bitor (sparseint-concatenate n mask 0)
                     (if (sparseint-test-bitand mask
                                                (sparseint-concatenate n 0 -1))
                         (sparseint-concatenate (- n 1) 0 1)
                       0))))

(define mask-for-generic-signx ((outer-mask 4vmask-p))
  :parents (svmask-for-signx)
  :returns (arg-mask 4vmask-p :rule-classes :type-prescription)
  :inline t
  (b* ((mask (4vmask-fix outer-mask)))
    (if (sparseint-< mask 0)
        -1
      ;; We might care about any bit up to the length of the mask, but
      ;; we definitely don't care about other bits.
      (let* ((mask-upper-bound (+ 1 (sparseint-length mask))))
        (sparseint-concatenate mask-upper-bound -1 0))))
  ///
  (local (include-book "centaur/bitops/integer-length" :dir :system))
  (local (in-theory (enable* mask-for-generic-signx
                             bitops::logbitp-case-splits
                             expensive-rules)))

  (deffixequiv mask-for-generic-signx)

  (local (defthm logbitp-of-mask-for-generic-signx
           (equal (logbitp n (sparseint-val (mask-for-generic-signx outer-mask)))
                  (or (sparseint-< (4vmask-fix outer-mask) 0)
                      (<= (nfix n) (sparseint-length outer-mask))))
           :hints(("Goal" :in-theory (enable 4vmask-fix)))))

  (local (defthm integer-length-bounds-logbitp-alt1
           (implies (< (integer-length x) (nfix n))
                    (equal (logbitp n x)
                           (negp x)))
           :hints(("Goal"
                   :induct (bitops::logbitp-ind n x)
                   :in-theory (enable* bitops::ihsext-recursive-redefs
                                       bitops::ihsext-inductions)))))

  (defthmd mask-for-generic-signx-correct-for-signx
    (equal (4vec-mask mask (4vec-sign-ext n (4vec-mask (mask-for-generic-signx mask) x)))
           (4vec-mask mask (4vec-sign-ext n x)))
    :hints(("Goal" :in-theory (enable mask-for-generic-signx
                                      4vec-[=
                                      4vec-mask
                                      4vec-sign-ext
                                      negp
                                      4vmask-fix
                                      ))
           (bitops::logbitp-reasoning)
           (and stable-under-simplificationp
                '(:in-theory (enable bool->bit)))))

  (defthmd mask-for-generic-signx-specialized-for-signx
    (implies (and (equal (4vec-mask (mask-for-generic-signx mask) val1)
                         (4vec-mask (mask-for-generic-signx mask) val2))
                  (syntaxp (term-order val2 val1)))
             (equal (4vec-mask mask (4vec-sign-ext n val2))
                    (4vec-mask mask (4vec-sign-ext n val1))))
    :hints(("goal"
            :in-theory (disable MASK-FOR-GENERIC-SIGNX)
            :use ((:instance mask-for-generic-signx-correct-for-signx (mask mask) (n n) (x val1))
                  (:instance mask-for-generic-signx-correct-for-signx (mask mask) (n n) (x val2))))))


  (defthmd mask-for-generic-signx-correct-for-concat-x
    (equal (4vec-mask mask (4vec-concat n (4vec-mask (mask-for-generic-signx mask) x) y))
           (4vec-mask mask (4vec-concat n x y)))
    :hints(("Goal" :in-theory (enable mask-for-generic-signx
                                      4vec-[=
                                      4vec-mask
                                      4vec-concat
                                      negp
                                      4vmask-fix
                                      ))
           (bitops::logbitp-reasoning)
           (and stable-under-simplificationp
                '(:in-theory (enable bool->bit)))))

  (defthmd mask-for-generic-signx-correct-for-concat-y
    (equal (4vec-mask mask (4vec-concat n x (4vec-mask (mask-for-generic-signx mask) y)))
           (4vec-mask mask (4vec-concat n x y)))
    :hints(("Goal" :in-theory (enable mask-for-generic-signx
                                      4vec-[=
                                      4vec-mask
                                      4vec-concat
                                      negp
                                      4vmask-fix
                                      ))
           (bitops::logbitp-reasoning)
           (and stable-under-simplificationp
                '(:in-theory (enable bool->bit)))))

  (defthmd mask-for-generic-signx-specialized-for-concat-x
    (implies (and (EQUAL (4VEC-MASK (MASK-FOR-GENERIC-SIGNX MASK) xval1)
                         (4VEC-MASK (MASK-FOR-GENERIC-SIGNX MASK) xval2))
                  (syntaxp (term-order xval2 xval1)))
             (EQUAL (4VEC-MASK MASK (4VEC-CONCAT n xval1 yval))
                    (4VEC-MASK MASK (4VEC-CONCAT n xval2 yval))))
    :hints(("Goal"
            :in-theory (disable MASK-FOR-GENERIC-SIGNX)
            :use ((:instance mask-for-generic-signx-correct-for-concat-x (n n) (x xval1) (y yval))
                  (:instance mask-for-generic-signx-correct-for-concat-x (n n) (x xval2) (y yval))))))

  (defthmd mask-for-generic-signx-specialized-for-concat-y
    (implies (and (EQUAL (4VEC-MASK (MASK-FOR-GENERIC-SIGNX MASK) yval1)
                         (4VEC-MASK (MASK-FOR-GENERIC-SIGNX MASK) yval2))
                  (syntaxp (term-order yval2 yval1)))
             (EQUAL (4VEC-MASK MASK (4VEC-CONCAT n xval yval1))
                    (4VEC-MASK MASK (4VEC-CONCAT n xval yval2))))
    :hints(("Goal"
            :in-theory (disable MASK-FOR-GENERIC-SIGNX)
            :use ((:instance mask-for-generic-signx-correct-for-concat-y (n n) (x xval) (y yval1))
                  (:instance mask-for-generic-signx-correct-for-concat-y (n n) (x xval) (y yval2)))))))

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
  :body (b* (((when (sparseint-equal mask 0))
              ;; Don't care about the result, so don't care about any args.
              (list 0 0))
             (nval (svex-s4xeval n))
             ((unless (s4vec-2vec-p nval))
              ;; We don't statically know N.  BOZO I think we can do better
              ;; than just assuming we need all bits of X.  In particular,
              ;; we should be able to do something like:
              ;;    (mask-for-generic-signx mask)
              ;; It didn't seem super easy to prove this, so I'm holding off
              ;; for now.
              (list -1 (mask-for-generic-signx mask)))
             (nv (s4vec->upper nval))
             ((when (sparseint-< nv 0))
              ;; We know N but it is a negative number, so the result is pure X
              ;; bits, regardless of the x argument.
              (list -1 0))
             (xmask (mask-for-fixed-signx mask (sparseint-val nv))))
          (list -1 xmask))
  :prepwork ((local (in-theory (disable* 2vec-p))))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe
                                   hide-past-second-arg
                                   mask-for-generic-signx-specialized-for-signx)))
          (and stable-under-simplificationp
               ;; Don't open up 4vec-mask yet, want
               '(:in-theory (e/d (mask-for-fixed-signx
                                  4vec-[=
                                  4vec-sign-ext
                                  4vec-mask
                                  2vec-p)
                                 (svex-eval-gte-xeval))
                 :use ((:instance svex-eval-gte-xeval (x (first args))))))
          (bitops::logbitp-reasoning
           :add-hints (:in-theory
                       (enable* bitops::logbitp-case-splits
                                bitops::logbitp-of-const-split))
           :simp-hint (:in-theory
                       (enable* bitops::logbitp-case-splits
                                bitops::logbitp-of-const-split))
           :prune-examples nil)))

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
             (nval (svex-s4xeval n))
             ((unless (s4vec-2vec-p nval))
              ;; Don't know what the index is.  We can at least use the
              ;; saturated mask as in sign extension for both arguments.
              (let ((argmask (mask-for-generic-signx mask)))
                (list -1 argmask argmask)))
             (n (s4vec->upper nval))
             ((when (sparseint-< n 0)) ;; (unless (<= 0 n))
              ;; N is statically known to be negative, so the whole result is X
              ;; for sure and we don't care about x or y at all.
              (list -1 0 0)))
          ;; X is statically known and positive, so adjust mask accordingly on
          ;; the arguments.
          (list -1
                (sparseint-concatenate (sparseint-val n) mask 0)
                (sparseint-rightshift (sparseint-val n) mask)))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe
                                   hide-past-third-arg
                                   mask-for-generic-signx-specialized-for-concat-x
                                   mask-for-generic-signx-specialized-for-concat-y)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (4vec-mask
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
             (nval (svex-s4xeval n))
             ((when (s4vec-2vec-p nval))
              ;; Statically known shift amount, so just shift the mask by
              ;; the shift amount.
              (list -1 (sparseint-ash mask (sparseint-val (s4vec->upper nval))))))
          ;; No idea which bits will get shifted in, so we have to depend on
          ;; all of them.
          (list -1 -1))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe
                                   hide-past-second-arg)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (4vec-mask
                                  4vec-rsh 4vec-shift-core))
                 :cases ((<= 0 (2vec->val (svex-xeval (car args)))))
                 ))
          (bitops::logbitp-reasoning)))

(def-svmask lsh (n x)
  :long "<p>See @(see svmask-for-rsh).  This is entirely similar, just for left
shifts instead of right shifts.</p>"
  :body (b* (((when (4vmask-empty mask))
              ;; Don't care about this expression at all, hence don't care
              ;; about any of the arguments.
              (list 0 0))
             (nval (svex-s4xeval n))
             ((when (s4vec-2vec-p nval))
              ;; Statically known shift amount, so just shift the mask by the
              ;; shift amount.
              (list -1 (sparseint-ash mask (sparseint-val (sparseint-unary-minus (s4vec->upper nval)))))))
          ;; No idea which bits will get shifted in, so we have to depend on
          ;; all of them.
          (list -1 -1))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe
                                   hide-past-second-arg)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (4vec-mask
                                  4vec-lsh 4vec-shift-core))
                 :cases ((<= 0 (2vec->val (svex-xeval (car args)))))))
          (bitops::logbitp-reasoning)))

(def-svmask partsel (lsb width in)

  :body (b* (((when (4vmask-empty mask))
              ;; Don't care about any bits of the result, so we don't care
              ;; about any of the arguments.
              (list 0 0 0))
             (widthval (svex-s4xeval width))
             (lsbval (svex-s4xeval lsb))
             ((unless (s4vec-2vec-p widthval))
              ;; We don't know the width, but if we know the lsb, then the mask
              ;; for in can be a shift of the input mask.
              (if (s4vec-2vec-p lsbval)
                  (list -1 -1 (sparseint-ash mask (sparseint-val (s4vec->upper lsbval))))
                (list -1 -1 -1)))
             (widthval (s4vec->upper widthval))

             ((when (sparseint-< widthval 0))
              ;; width is statically known to be negative, so the whole result is X
              ;; for sure and we don't care about lsb or in
              (list 0 -1 0))
             (widthval (sparseint-val widthval))

             ((unless (s4vec-2vec-p lsbval))
              ;; Don't know what the lsb is. The one thing we can do in this
              ;; case: if there are no mask bits inside the width, then we
              ;; don't care about in.
              (if (sparseint-equal 0 (sparseint-concatenate widthval mask 0))
                  (list -1 -1 0)
                (list -1 -1 -1)))
             (lsbval (s4vec->upper lsbval)))
          ;; X is statically known and positive, so adjust mask accordingly on
          ;; the arguments.
          (list -1 -1 (sparseint-ash (sparseint-concatenate widthval mask 0) (sparseint-val lsbval))))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe
                                   hide-past-third-arg)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (4vec-mask
                                  4vec-concat 4vec-rsh 4vec-shift-core 4vec-zero-ext 4vec-part-select))))
          (bitops::logbitp-reasoning)))




(local (defthmd move-minus-over-comparison
         (and (iff (< (+ a (- b)) c)
                   (< a (+ b c)))
              (iff (> (+ a (- b)) c)
                   (> a (+ b c))))))


(local (in-theory (disable acl2::logtail-identity
                           bitops::logtail-natp
                           bitops::logbitp-when-bit
                           (:t logbitp)
                           (:t bit->bool)
                            not
                           ACL2::|x < y  =>  0 < -x+y|)))

(def-svmask partinst (lsb width in val)

  :body (b* (((when (4vmask-empty mask))
              ;; Don't care about any bits of the result, so we don't care
              ;; about any of the arguments.
              (list 0 0 0 0))
             (lsbval (svex-s4xeval lsb))
             (widthval (svex-s4xeval width))
             ((unless (s4vec-2vec-p widthval))
              ;; Knowing the LSB without knowing the width doesn't give us
              ;; anything in this case.  But we can always mask in by the outer
              ;; mask because its bits always line up.
              (list -1 -1 mask -1))
             (widthval (s4vec->upper widthval))
             ((when (sparseint-< widthval 0))
              ;; width is negative, so the whole thing is X
              (list 0 -1 0 0))
             ((unless (s4vec-2vec-p lsbval))
              ;; We don't know what the LSB is, but we can at least mask the
              ;; val by width.
              (list -1 -1 mask (sparseint-concatenate (sparseint-val widthval) -1 0)))
             ;; We know what both LSB and width are.  We can basically divide
             ;; the outer mask into the portion for val and the portion for in.
             (lsbval (s4vec->upper lsbval))
             ((unless (sparseint-< lsbval 0))
              ;; some bits of in, then val, then in
              (b* ((lsbval (sparseint-val lsbval))
                   (widthval (sparseint-val widthval))
                   (inmask (sparseint-concatenate
                            lsbval
                            mask
                            (sparseint-concatenate
                             widthval
                             0
                             (sparseint-ash mask
                                            (- (+ lsbval widthval))))))
                   (valmask (sparseint-concatenate widthval (sparseint-rightshift lsbval mask) 0)))
                (list -1 -1
                      inmask
                      valmask)))
             ((when (sparseint-< (sparseint-unary-minus lsbval) widthval))
              ;; some bits of val, then in
              (b* ((width+lsb (sparseint-val (sparseint-plus widthval lsbval)))
                   (inmask (sparseint-concatenate width+lsb 0 (sparseint-rightshift width+lsb mask)))
                   (valmask (sparseint-concatenate
                             (sparseint-val (sparseint-unary-minus lsbval))
                             0
                             (sparseint-concatenate width+lsb mask 0))))
                (list -1 -1 inmask valmask))))
          ;; just in, no val
          (list -1 -1 mask 0))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe
                                   hide-past-third-arg)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (4vec-mask
                                  4vec-concat 4vec-rsh 4vec-shift-core 4vec-zero-ext 4vec-part-install))))
          (bitops::logbitp-reasoning
           :add-hints (:in-theory (enable* logbitp-case-splits
                                           bitops::logbitp-of-const-split
                                           move-minus-over-comparison))
           :simp-hint (:in-theory (enable* logbitp-case-splits
                                            bitops::logbitp-of-const-split
                                            move-minus-over-comparison)))
          (and stable-under-simplificationp
               '(:bdd (:vars nil)
                 :in-theory (enable (:t logbitp) (:t bit->bool)))))
  :otf-flg t)



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

    :body (b* (((s4vec xval)  (svex-s4xeval x))
               ((s4vec yval)  (svex-s4xeval y))
               (x-zero       (sparseint-bitnor xval.upper xval.lower))
               (y-zero       (sparseint-bitnor yval.upper yval.lower))
               (shared-zeros (sparseint-bitand x-zero (sparseint-bitand y-zero mask)))
               (xm-nonzero   (sparseint-bitandc2 mask x-zero))
               (ym-nonzero   (sparseint-bitandc2 mask y-zero))
               ((when (sparseint-equal 0 shared-zeros))
                ;; There are no overlapping zeroes in any bits that we care
                ;; about, so we can aggressively mask both arguments.
                (list ym-nonzero xm-nonzero))
               ;; Otherwise there are overlapping zeroes so we cannot mask them
               ;; both aggressively.  Idea: we will (arbitrarily) mask Y more
               ;; aggressively UNLESS all of the relevant bits of Y are known
               ;; to be constant under the current mask, in which case we would
               ;; probably rather mask X more aggressively.
               (y-x     (sparseint-bitandc2 yval.upper yval.lower))
               (ym-x    (sparseint-test-bitand mask y-x))
               ((unless ym-x)
                ;; There are no masked bits of Y that are X, so the parts of Y we
                ;; care about are constant or are nearly constant.  So let's mask
                ;; X more aggressively.
                (list ym-nonzero (sparseint-bitor xm-nonzero shared-zeros))))
            ;; Otherwise, no reason to prefer masking X more aggressively, so
            ;; just arbitrary default to masking Y more aggressively than X.
            (list (sparseint-bitor ym-nonzero shared-zeros) xm-nonzero))
    :prepwork ((local (in-theory (disable* not))))
    :hints (("Goal" :in-theory (e/d (svex-apply
                                     4veclist-nth-safe
                                     hide-past-second-arg)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (4vec-mask
                                    3vec-fix
                                    3vec-bitand
                                    4vec-bitand
                                    4vec-[=)
                                   (svex-eval-gte-xeval))
                   :use ((:instance svex-eval-gte-xeval (x (first args)))
                         (:instance svex-eval-gte-xeval (x (second args))))))
            (bitops::logbitp-reasoning)
            (and stable-under-simplificationp
                 '(:bdd (:vars nil)
                   :in-theory (enable (:t logbitp) (:t bit->bool))))))

(def-svmask resand (x y)
  :long "<p>See @(see svmask-for-bitand); the same analysis applies equally
well to @('(resand x y)').</p>"
  :inline t
  :nobindings t
  :body (svmask-for-bitand mask args)
  :prepwork ((local (in-theory (disable* not))))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe
                                   hide-past-second-arg)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (4vec-mask
                                  3vec-fix
                                  4vec-resand
                                  svmask-for-bitand
                                  4vec-[=)
                                 (svex-eval-gte-xeval))
                 :use ((:instance svex-eval-gte-xeval (x (first args)))
                       (:instance svex-eval-gte-xeval (x (second args))))))
          (bitops::logbitp-reasoning)
          (and stable-under-simplificationp
               '(:bdd (:vars nil)
                   :in-theory (enable (:t logbitp) (:t bit->bool))))))

(def-svmask bitor (x y)
  :long "<p>See @(see svmask-for-bitand).  This is similar, except that since
we are dealing with @('(bitor x y)'), the bits of @('x') that are 1 (instead of
0) are the don't cares bits for @('y'), and vice versa.  Again we have to watch
out for cases where both arguments have a @('1') bit, and in such cases mark at
least one or the other as a care bit.</p>"

  :body (b* (((s4vec xval)  (svex-s4xeval x))
             ((s4vec yval)  (svex-s4xeval y))
             (x-1          (sparseint-bitand xval.upper xval.lower))
             (y-1          (sparseint-bitand yval.upper yval.lower))
             (shared-1s    (sparseint-bitand x-1 (sparseint-bitand y-1 mask)))
             (xm-non1      (sparseint-bitandc2 mask x-1))
             (ym-non1      (sparseint-bitandc2 mask y-1))
             ((when (sparseint-equal 0 shared-1s))
              ;; There are no overlapping zeroes in any bits that we care
              ;; about, so we can aggressively mask both arguments.
              (list ym-non1 xm-non1))
             ;; Otherwise there are overlapping 1s so we cannot mask them both
             ;; aggressively.  Idea: we will (arbitrarily) mask Y more
             ;; aggressively UNLESS all of the relevant bits of Y are known to
             ;; be constant under the current mask, in which case we would
             ;; probably rather mask X more aggressively.
             (y-x  (sparseint-bitandc2 yval.upper yval.lower))
             (ym-x (sparseint-test-bitand mask y-x))
             ((unless ym-x)
              ;; There are no masked bits of Y that are X, so the parts of Y we
              ;; care about are constant or are nearly constant.  So let's mask
              ;; X more aggressively.
              (list ym-non1 (sparseint-bitor xm-non1 shared-1s))))
          ;; Otherwise, no reason to prefer masking X more aggressively, so
          ;; just arbitrary default to masking Y more aggressively than X.
          (list (sparseint-bitor ym-non1 shared-1s) xm-non1))
  :prepwork ((local (in-theory (disable* not))))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe
                                   hide-past-second-arg)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (4vec-mask
                                  3vec-fix
                                  3vec-bitor
                                  4vec-bitor
                                  4vec-[=)
                                 (svex-eval-gte-xeval))
                 :use ((:instance svex-eval-gte-xeval (x (first args)))
                       (:instance svex-eval-gte-xeval (x (second args))))))
          (bitops::logbitp-reasoning)
          (and stable-under-simplificationp
               '(:bdd (:vars nil)
                   :in-theory (enable (:t logbitp) (:t bit->bool))))))

(def-svmask resor (x y)
  :long "<p>See @(see svmask-for-bitand); the same analysis applies equally
well to @('(resand x y)').</p>"
  :inline t
  :nobindings t
  :body (svmask-for-bitor mask args)
  :prepwork ((local (in-theory (disable* not))))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe
                                   hide-past-second-arg)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svmask-for-bitor
                                  4vec-mask
                                  3vec-fix
                                  3vec-bitor
                                  4vec-bitor
                                  4vec-resor
                                  4vec-[=)
                                 (svex-eval-gte-xeval))
                 :use ((:instance svex-eval-gte-xeval (x (first args)))
                       (:instance svex-eval-gte-xeval (x (second args))))))
          (bitops::logbitp-reasoning)
          (and stable-under-simplificationp
               '(:bdd (:vars nil)
                 :in-theory (enable (:t logbitp) (:t bit->bool))))))

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

  :body (b* (((s4vec xval)  (svex-s4xeval x))
             ((s4vec yval)  (svex-s4xeval y))
             ;; Z is upper 0, lower 1.
             (x-Z          (sparseint-bitandc1 xval.upper xval.lower))
             (y-Z          (sparseint-bitandc1 yval.upper yval.lower))
             (shared-Zs    (sparseint-bitand x-Z (sparseint-bitand y-Z mask)))
             (xm-nonZ      (sparseint-bitandc2 mask x-Z))
             (ym-nonZ      (sparseint-bitandc2 mask y-Z))
             ((when (sparseint-equal 0 shared-Zs))
              ;; There are no overlapping zeroes in any bits that we care
              ;; about, so we can aggressively mask both arguments.
              (list ym-nonZ xm-nonZ))
             ;; Otherwise there are overlapping Zs so we cannot mask them both
             ;; aggressively.  Idea: we will (arbitrarily) mask Y more
             ;; aggressively UNLESS all of the relevant bits of Y are known to
             ;; be constant under the current mask, in which case we would
             ;; probably rather mask X more aggressively.
             (y-x  (sparseint-bitandc2 yval.upper yval.lower))
             (ym-x (sparseint-test-bitand mask y-x))
             ((unless ym-x)
              ;; There are no masked bits of Y that are X, so the parts of Y we
              ;; care about are constant or are nearly constant.  So let's mask
              ;; X more aggressively.
              (list ym-nonZ (sparseint-bitor xm-nonZ shared-Zs))))
          ;; Otherwise, no reason to prefer masking X more aggressively, so
          ;; just arbitrary default to masking Y more aggressively than X.
          (list (sparseint-bitor ym-nonZ shared-Zs) xm-nonZ))
          ;;    )
          ;; (b* ((xval (svex-xeval x))
          ;;      (yval (svex-xeval y))
          ;;      (mask mask))
          ;;   (list (4vec-bitxor-mask mask x y)
          ;;         (4vec-bitxor-mask mask y x))))
  :prepwork ((local (in-theory (disable* not))))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe
                                   hide-past-second-arg)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (4vec-mask
                                  3vec-fix
                                  4vec-bitxor
                                  4vec-[=)
                                 (svex-eval-gte-xeval))
                 :use ((:instance svex-eval-gte-xeval (x (first args)))
                       (:instance svex-eval-gte-xeval (x (second args))))))
          (bitops::logbitp-reasoning)
          (and stable-under-simplificationp
               '(:bdd (:vars nil)
                   :in-theory (enable (:t logbitp) (:t bit->bool))))))

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

  :body (b* (((s4vec tval) (svex-s4xeval tests))
             (tests-non0  (sparseint-bitor  tval.upper tval.lower))
             (tests-non1  (sparseint-bitnand tval.upper tval.lower)))
          (list mask
                (sparseint-bitand mask tests-non0)
                (sparseint-bitand mask tests-non1)))
  :prepwork ((local (in-theory (disable not))))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe
                                   hide-past-third-arg)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (4vec-mask
                                  3vec-fix
                                  3vec-bit?
                                  4vec-bit?
                                  4vec-[=)
                                 (svex-eval-gte-xeval))
                 :use ((:instance svex-eval-gte-xeval (x (first args))))))
          (bitops::logbitp-reasoning)
          (and stable-under-simplificationp
               '(:bdd (:vars nil)
                   :in-theory (enable (:t logbitp) (:t bit->bool))))))

(def-svmask bit?! (tests)
  :long "<p>We are considering a @('(bit?! tests thens elses)') expression and
we know that we only care about the bits mentioned in @('mask').  We want to
figure out which bits of X and Y we care about.</p>

<p>As a starting point, since @(see 4vec-bit?!) operates in a bit-by-bit
fashion, we certainly don't care about any bits that are don't cares in our
outer @('mask').</p>

<p>For @('tests'), for now we don't try to do anything smart&mdash;we just keep
the outer @('mask').  We might consider eventually extending this: if we can
determine that @('thens[i]') and @('elses[i]') agree on some value, then we the
test bit is irrelevant because of the way that @(see 4vec-bit?) does its
merging.  But it doesn't seem like this would help us very often, so for now it
doesn't seem worth doing.</p>

<p>For @('thens'), the main thing we want to take advantage of is that if we
know that @('test[i]') is not going to be 1, then we don't care about
@('thens[i]') because we're going to choose @('elses[i]') instead.  So, we
improve the mask by excluding any bits of @('tests') that are obviously
false.</p>

<p>For @('elses'), likewise we improve the mask by removing any bits of
@('tests') that are obviously 1.</p>"

  :body (b* (((mv maybe-1 maybe-not1)
              (if (svex-case tests :quote)
                  (b* (((4vec test) (svex-quote->val tests))
                       (known1 (logand test.upper test.lower)))
                    (mv (int-to-sparseint known1)
                        (int-to-sparseint (lognot known1))))
                (b* (((s4vec tval) (svex-s4xeval tests)))
                  ;; If 1 or X, then it might be 1 -- (1 . 1) or (1 . 0) -> upper
                  ;; if 0 or X or Z, then it might be 0 -- not (1 . 1)
                  (mv tval.upper
                      (sparseint-bitnand tval.upper tval.lower))))))
          (list mask
                (sparseint-bitand mask maybe-1)
                (sparseint-bitand mask maybe-not1)))
  :prepwork ((local (in-theory (disable not))))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe
                                   hide-past-third-arg
                                   svex-eval-when-quote)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (4vec-mask
                                  3vec-fix
                                  4vec-bit?!
                                  4vec-[=
                                   svex-eval-when-quote)
                                 (svex-eval-gte-xeval))
                 :use ((:instance svex-eval-gte-xeval (x (first args))))))
          (bitops::logbitp-reasoning)
          (and stable-under-simplificationp
               '(:bdd (:vars nil)
                   :in-theory (enable (:t logbitp) (:t bit->bool))))
          ))

(local
 (encapsulate nil
   (local (in-theory (enable not)))

   (defthm strengthen-4vec-?-then
     (implies (and (equal (4vec-mask mask then1)
                          (4vec-mask mask then2))
                   (syntaxp (term-order then2 then1)))
              (equal (4vec-mask mask (4vec-? test then1 else))
                     (4vec-mask mask (4vec-? test then2 else))))
     :hints(("Goal" :in-theory (enable 4vec-?
                                       3vec-?
                                       3vec-fix
                                       4vec-mask))
            (bitops::logbitp-reasoning)))

   (defthm strengthen-4vec-?-else
     (implies (and (EQUAL (4VEC-MASK MASK else1)
                          (4VEC-MASK MASK ELSE2))
                   (syntaxp (term-order else2 else1)))
              (equal (4vec-mask mask (4vec-? test then else1))
                     (4vec-mask mask (4vec-? test then else2))))
     :hints(("Goal" :in-theory (enable 4vec-?
                                       3vec-?
                                       3vec-fix
                                       4vec-mask))
            (bitops::logbitp-reasoning)))

   (defthm strengthen-4vec-?*-then
     (implies (and (equal (4vec-mask mask then1)
                          (4vec-mask mask then2))
                   (syntaxp (term-order then2 then1)))
              (equal (4vec-mask mask (4vec-?* test then1 else))
                     (4vec-mask mask (4vec-?* test then2 else))))
     :hints(("Goal" :in-theory (enable 4vec-?*
                                       3vec-?*
                                       3vec-fix
                                       4vec-mask))
            (bitops::logbitp-reasoning)))

   (defthm strengthen-4vec-?*-else
     (implies (and (EQUAL (4VEC-MASK MASK else1)
                          (4VEC-MASK MASK ELSE2))
                   (syntaxp (term-order else2 else1)))
              (equal (4vec-mask mask (4vec-?* test then else1))
                     (4vec-mask mask (4vec-?* test then else2))))
     :hints(("Goal" :in-theory (enable 4vec-?*
                                       3vec-?*
                                       3vec-fix
                                       4vec-mask))
            (bitops::logbitp-reasoning)))

   (defthm strengthen-4vec-?!-then
     (implies (and (equal (4vec-mask mask then1)
                          (4vec-mask mask then2))
                   (syntaxp (term-order then2 then1)))
              (equal (4vec-mask mask (4vec-?! test then1 else))
                     (4vec-mask mask (4vec-?! test then2 else))))
     :hints(("Goal" :in-theory (enable 4vec-?!
                                       3vec-fix
                                       4vec-mask))
            (bitops::logbitp-reasoning)))

   (defthm strengthen-4vec-?!-else
     (implies (and (EQUAL (4VEC-MASK MASK else1)
                          (4VEC-MASK MASK ELSE2))
                   (syntaxp (term-order else2 else1)))
              (equal (4vec-mask mask (4vec-?! test then else1))
                     (4vec-mask mask (4vec-?! test then else2))))
     :hints(("Goal" :in-theory (enable 4vec-?!
                                       3vec-fix
                                       4vec-mask))
            (bitops::logbitp-reasoning)))))

(define branches-same-under-mask-p ((mask 4vmask-p)
                                      (then svex-p)
                                      (else svex-p))
  :parents (svmask-for-?)
  :short "Checks whether @('then') and @('else') are statically known to agree,
in which case we don't care about @('test') at all."
  (b* ((mask           (4vmask-fix mask))
       ((s4vec thenval) (svex-s4xeval then))
       (then-bool      (sparseint-biteqv thenval.upper thenval.lower))  ;; bits where then is 1/0/z
       ((when (sparseint-test-bitandc2 mask then-bool)) ;; exists a care bit where then is x/z
        nil)
       ((s4vec elseval) (svex-s4xeval else))
       (else-bool      (sparseint-biteqv elseval.upper elseval.lower)) ;; bits where else is 1/0/z
       ((when (sparseint-test-bitandc2 mask else-bool)) ;; exists a care bit where else is x/z
        nil))
    (sparseint-equal (sparseint-bitand mask thenval.upper)
                     (sparseint-bitand mask elseval.upper)))
  ///
  (deffixequiv branches-same-under-mask-p))

(local
 (defsection branches-same-under-mask-lemmas

   (local (in-theory (disable not)))

   (local (in-theory (enable (:t logbitp) (:t bool->bit))))
   (defthmd branches-same-under-mask-p-correct
     (implies (and (branches-same-under-mask-p mask then else)
                   (syntaxp (not (equal any-test ''0))))
              (equal (4vec-mask mask (4vec-? any-test
                                             (svex-eval then env)
                                             (svex-eval else env)))
                     (4vec-mask mask (4vec-? 0
                                             (4vec-mask mask (svex-eval then env))
                                             (4vec-mask mask (svex-eval else env))))))
     :hints(("Goal" :in-theory (e/d (branches-same-under-mask-p
                                     4vec-mask
                                     4vec-?
                                     3vec-?
                                     3vec-fix
                                     4vec-[=)
                                    (svex-eval-gte-xeval
                                     ))
             :use ((:instance svex-eval-gte-xeval (x then))
                   (:instance svex-eval-gte-xeval (x else)))
             )
            (bitops::logbitp-reasoning :passes 2)
            ;; (and stable-under-simplificationp
            ;;      '(:in-theory (enable bool->bit)))
            (and stable-under-simplificationp '(:bdd (:vars nil)
                                                :in-theory (enable (:t logbitp) (:t bool->bit))))
            ))

   (defthmd branches-same-under-mask-p-crux
     (implies
      (and (branches-same-under-mask-p mask then else)
           (equal (4vec-mask mask (svex-eval then env)) (4vec-mask mask thenval))
           (equal (4vec-mask mask (svex-eval else env)) (4vec-mask mask elseval)))
      (equal (4vec-mask mask (4vec-? testval thenval elseval))
             (4vec-mask mask
                        (4vec-? 0
                                (4vec-mask mask (svex-eval then env))
                                (4vec-mask mask (svex-eval else env))))))
     :hints(("Goal"
             :use ((:instance branches-same-under-mask-p-correct
                    (any-test testval))))))

   (defthmd branches-same-under-mask-p-correct*
     (implies (and (branches-same-under-mask-p mask then else)
                   (syntaxp (not (equal any-test ''0))))
              (equal (4vec-mask mask (4vec-?* any-test
                                             (svex-eval then env)
                                             (svex-eval else env)))
                     (4vec-mask mask (4vec-?* 0
                                             (4vec-mask mask (svex-eval then env))
                                             (4vec-mask mask (svex-eval else env))))))
     :hints(("Goal" :in-theory (e/d (branches-same-under-mask-p
                                     4vec-mask
                                     4vec-?*
                                     3vec-?*
                                     3vec-fix
                                     4vec-[=)
                                    (svex-eval-gte-xeval
                                     ))
             :use ((:instance svex-eval-gte-xeval (x then))
                   (:instance svex-eval-gte-xeval (x else)))
             )
            (bitops::logbitp-reasoning)
            (and stable-under-simplificationp '(:bdd (:vars nil)))))

   (defthmd branches-same-under-mask-p-crux*
     (implies
      (and (branches-same-under-mask-p mask then else)
           (equal (4vec-mask mask (svex-eval then env)) (4vec-mask mask thenval))
           (equal (4vec-mask mask (svex-eval else env)) (4vec-mask mask elseval)))
      (equal (4vec-mask mask (4vec-?* testval thenval elseval))
             (4vec-mask mask
                        (4vec-?* 0
                                (4vec-mask mask (svex-eval then env))
                                (4vec-mask mask (svex-eval else env))))))
     :hints(("Goal"
             :use ((:instance branches-same-under-mask-p-correct*
                    (any-test testval))))))

   (defthmd branches-same-under-mask-p-correct!
     (implies (and (branches-same-under-mask-p mask then else)
                   (syntaxp (not (equal any-test ''0))))
              (equal (4vec-mask mask (4vec-?! any-test
                                             (svex-eval then env)
                                             (svex-eval else env)))
                     (4vec-mask mask (4vec-?! 0
                                             (4vec-mask mask (svex-eval then env))
                                             (4vec-mask mask (svex-eval else env))))))
     :hints(("Goal" :in-theory (e/d (branches-same-under-mask-p
                                     4vec-mask
                                     4vec-?!
                                     3vec-fix
                                     4vec-[=)
                                    (svex-eval-gte-xeval
                                     ))
             :use ((:instance svex-eval-gte-xeval (x then))
                   (:instance svex-eval-gte-xeval (x else)))
             )
            (bitops::logbitp-reasoning)
            (and stable-under-simplificationp '(:bdd (:vars nil)))))

   (defthmd branches-same-under-mask-p-crux!
     (implies
      (and (branches-same-under-mask-p mask then else)
           (equal (4vec-mask mask (svex-eval then env)) (4vec-mask mask thenval))
           (equal (4vec-mask mask (svex-eval else env)) (4vec-mask mask elseval)))
      (equal (4vec-mask mask (4vec-?! testval thenval elseval))
             (4vec-mask mask
                        (4vec-?! 0
                                (4vec-mask mask (svex-eval then env))
                                (4vec-mask mask (svex-eval else env))))))
     :hints(("Goal"
             :use ((:instance branches-same-under-mask-p-correct!
                    (any-test testval))))))))

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
             ((s4vec testval) (svex-s4xeval test))
             (test-1s (sparseint-bitand testval.upper testval.lower))
             ((unless (sparseint-equal test-1s 0))
              ;; There is some bit of the test that is definitely 1, so the
              ;; else branch doesn't matter at all.
              (list test-1s mask 0))
             ((when (and (sparseint-equal testval.upper 0)
                         (sparseint-equal testval.lower 0)))
              ;; The test is definitely all 0s, so the then branch doesn't
              ;; matter at all.
              (list -1 0 mask)))
          ;; BOZO this is sound but very slow for the proof of correctness.
          ;; Can we speed this proof up?
          (if (branches-same-under-mask-p mask then else)
              (list 0 mask mask)
            (list -1 mask mask)))
  :prepwork ((local (in-theory (disable* not
                                         svex-eval-gte-xeval
                                         bitops::logior-equal-0))))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe
                                   hide-past-third-arg
                                   branches-same-under-mask-p-crux
                                   )))
          (and stable-under-simplificationp
               (not (member-equal
                     '(not (branches-same-under-mask-p mask (CAR (CDR ARGS))
                                                       (CAR (CDR (CDR ARGS)))))
                     clause))
               '(:computed-hint-replacement
                 ((logbitp-reasoning)
                  (and stable-under-simplificationp
                       '(:bdd (:vars nil)
                         :in-theory (enable (:t logbitp)
                                            (:t bit->bool)))))
                 :in-theory (e/d (4vec-mask
                                  2vec-p
                                  4vec-?
                                  3vec-?
                                  3vec-fix
                                  4vec-[=)
                                 (svex-eval-gte-xeval))
                 :use ((:instance svex-eval-gte-xeval (x (first args))))))))


(local (defthm 4vec-?*-of-equal-branches
         (equal (4vec-?* test then then)
                (4vec-fix then))
         :hints(("Goal" :in-theory (enable 4vec-?* 3vec-?*)))))


(def-svmask ?* (test then else)
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
             ((s4vec testval) (svex-s4xeval test))
             (test-1s (sparseint-bitand testval.upper testval.lower))
             ((unless (sparseint-equal test-1s 0))
              ;; There is some bit of the test that is definitely 1, so the
              ;; else branch doesn't matter at all.
              (list test-1s mask 0))
             ((when (and (sparseint-equal testval.upper 0)
                         (sparseint-equal testval.lower 0)))
              ;; The test is definitely all 0s, so the then branch doesn't
              ;; matter at all.
              (list -1 0 mask)))
          ;; BOZO this is sound but very slow for the proof of correctness.
          ;; Can we speed this proof up?
          (if (or (equal then else)
                  (branches-same-under-mask-p mask then else))
              (list 0 mask mask)
            (list -1 mask mask)))
  :prepwork ((local (in-theory (disable* not
                                         svex-eval-gte-xeval
                                         bitops::logior-equal-0))))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe
                                   hide-past-third-arg
                                   branches-same-under-mask-p-crux*
                                   )))
          (and stable-under-simplificationp
               (not (member-equal
                     '(not (EQUAL (SVEX-FIX$INLINE (CAR (CDR ARGS)))
                                  (SVEX-FIX$INLINE (CAR (CDR (CDR ARGS))))))
                     clause))
               (not (member-equal
                     '(not (branches-same-under-mask-p mask (CAR (CDR ARGS))
                                                       (CAR (CDR (CDR ARGS)))))
                     clause))
               '(:computed-hint-replacement
                 ((logbitp-reasoning)
                  (and stable-under-simplificationp
                       '(:bdd (:vars nil)
                         :in-theory (enable (:t logbitp)
                                            (:t bit->bool)))))
                 :in-theory (e/d (4vec-mask
                                  2vec-p
                                  4vec-?*
                                  3vec-?*
                                  3vec-fix
                                  4vec-[=)
                                 (svex-eval-gte-xeval))
                 :use ((:instance svex-eval-gte-xeval (x (first args))))))))



(local (defthm 4vec-?!-of-equal-branches
         (equal (4vec-?! test then then)
                (4vec-fix then))
         :hints(("Goal" :in-theory (enable 4vec-?!)))))


(def-svmask ?! (test then else)
  :long "<p>We are considering a @('(?! test then else)') expression and we know
that we only care about the bits mentioned in @('mask').  We need to figure out
which bits of @('test'), @('then'), and @('else') we care about.</p>

<p>We will almost always need to care about the entire @('test') expression.
The only exceptions to this would be when either:</p>

<ul>

<li>We don't care about any bits at all, i.e., the outer @('mask') is
empty.</li>

<li>For all bits we care about, the corresponding bits of @('then') and
@('else') branches are known to agree.  For instance, @('(?! test 5 5)') is
going to be 5 regardless of @('test').  (This is pretty obscure).</li>

</ul>

<p>More obvious and probably more useful mask improvements:</p>

<ul>
<li>When we know that some bit of @('test') is 1, we can completely don't
care @('else');</li>
<li>When we know that all bits of @('test') are not 1, we can completely don't
care @('then').  We don't really have a good way to check this other than
checking that the xeval is 0, though.</li>
</ul>"
  :body (b* (((when (4vmask-empty mask))
              (list 0 0 0))
             ((s4vec testval) (svex-s4xeval test))
             (test-1s (sparseint-bitand testval.upper testval.lower))
             ((unless (sparseint-equal test-1s 0))
              ;; There is some bit of the test that is definitely 1, so the
              ;; else branch doesn't matter at all.
              (list test-1s mask 0))
             ((when (and (sparseint-equal testval.upper 0)
                         (sparseint-equal testval.lower 0)))
              ;; The test is definitely all 0s, so the then branch doesn't
              ;; matter at all.
              (list -1 0 mask)))
          ;; BOZO this is sound but very slow for the proof of correctness.
          ;; Can we speed this proof up?
          (if (or (equal then else)
                  (branches-same-under-mask-p mask then else))
              (list 0 mask mask)
            (list -1 mask mask)))
  :prepwork ((local (in-theory (disable* not
                                         svex-eval-gte-xeval
                                         bitops::logior-equal-0))))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth-safe
                                   hide-past-third-arg
                                   branches-same-under-mask-p-crux!
                                   )))
          (and stable-under-simplificationp
               (not (member-equal
                     '(not (EQUAL (SVEX-FIX$INLINE (CAR (CDR ARGS)))
                                  (SVEX-FIX$INLINE (CAR (CDR (CDR ARGS))))))
                     clause))
               (not (member-equal
                     '(not (branches-same-under-mask-p mask (CAR (CDR ARGS))
                                                       (CAR (CDR (CDR ARGS)))))
                     clause))
               '(:computed-hint-replacement
                 ((logbitp-reasoning)
                  (and stable-under-simplificationp
                       '(:bdd (:vars nil)
                         :in-theory (enable (:t logbitp)
                                            (:t bit->bool)))))
                 :in-theory (e/d (4vec-mask
                                  2vec-p
                                  4vec-?!
                                  3vec-fix
                                  4vec-[=)
                                 (svex-eval-gte-xeval))
                 :use ((:instance svex-eval-gte-xeval (x (first args))))))))

(define sparseint-unrev-blocks ((nbits natp)
                      (blocksz posp)
                      (x sparseint-p))
  ;; Inverse function of rev-blocks.
  :measure (nfix nbits)
  :returns (res sparseint-p)
  :verify-guards nil
  (b* ((nbits (lnfix nbits))
       (blocksz (mbe :logic (acl2::pos-fix blocksz) :exec blocksz))
       ((when (< nbits blocksz))
        (sparseint-concatenate nbits x 0))
       ;; Take bits [nbits-1:nbits-blocksz] and put them at the bottom.
       ;; Recursively unreverse bits [nbits-blocksz-1:0] and then place them at the top.
       (next-nbits (- nbits blocksz))
       (rest (sparseint-unrev-blocks next-nbits blocksz x)))
    (sparseint-concatenate blocksz (sparseint-rightshift next-nbits x) rest))
  ///
  (defret sparseint-unrev-blocks-val
    (natp (sparseint-val res))
    :rule-classes :type-prescription)
  (verify-guards sparseint-unrev-blocks))

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

  (defthm logbitp-of-sparseint-unrev-blocks
    (equal (logbitp i (sparseint-val (sparseint-unrev-blocks nbits blocksz x)))
           (and (< (nfix i) (nfix nbits))
                (logbitp (unrev-block-index i nbits blocksz) (sparseint-val x))))
    :hints (("goal" :induct (ind i nbits blocksz x)
             :in-theory (enable (:t logbitp) not)
             :expand ((unrev-block-index i nbits blocksz)
                      (sparseint-unrev-blocks nbits blocksz x)))
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
    :hints(("Goal" :in-theory (enable* expensive-rules
                                       rev-block-index)
            :induct (unrev-block-index i nbits blocksz))))

  (defthm sparseint-unrev-blocks-correct1
    (equal (sparseint-val (sparseint-unrev-blocks nbits blocksz (sparseint-rev-blocks nbits blocksz x)))
           (loghead nbits (sparseint-val x)))
    :hints((bitops::logbitp-reasoning)))

  (defthm sparseint-unrev-blocks-correct2
    (equal (sparseint-val (sparseint-rev-blocks nbits blocksz (sparseint-unrev-blocks nbits blocksz x)))
           (loghead nbits (sparseint-val x)))
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

  (local (in-theory (enable (:t logbitp) (:t bit->bool))))

  (local (defthm lemma1
           (IMPLIES
            (AND (EQUAL (LOGIOR x1
                                (LOGNOT (sparseint-val (sparseint-UNREV-BLOCKS n b m))))
                        (LOGIOR x
                                (LOGNOT (sparseint-val (sparseint-UNREV-BLOCKS n b m))))))
            (equal (EQUAL (LOGIOR (LOGNOT (sparseint-val m))
                                  (REV-BLOCKS n b x))
                          (LOGIOR (LOGNOT (sparseint-val m))
                                  (REV-BLOCKS n b x1)))
                   t))
           :hints ((bitops::logbitp-reasoning))))

  (local (defthm lemma2
           (IMPLIES
            (AND (EQUAL (LOGAND x1
                                (sparseint-val (sparseint-UNREV-BLOCKS n b m)))
                        (LOGAND x
                                (sparseint-val (sparseint-UNREV-BLOCKS n b m)))))
            (equal (EQUAL (LOGAND (sparseint-val m)
                                  (REV-BLOCKS n b x))
                          (LOGAND (sparseint-val m)
                                  (REV-BLOCKS n b x1)))
                   t))
           :hints ((bitops::logbitp-reasoning))))

  (def-svmask blkrev (n b x)
    :body
    (b* (((when (4vmask-empty mask))
          (list 0 0 0))
         (nval (svex-s4xeval n))
         (bval (svex-s4xeval b))
         (mask mask)
         ((when (and (s4vec-2vec-p nval)
                     (s4vec-2vec-p bval)
                     (not (sparseint-< (s4vec->upper nval) 0))
                     (sparseint-< 0 (s4vec->upper bval))))
          (b* ((n (sparseint-val (s4vec->upper nval)))
               (b (sparseint-val (s4vec->upper bval))))
            (list -1 -1 (sparseint-unrev-blocks n b mask)))))
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


(local (in-theory (enable* expensive-rules)))

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

  (deffixequiv svex-argmasks)

  (defthm svex-argmasks-of-none
    (implies (4vmask-empty mask)
             (equal (svex-argmasks mask fn args)
                    (replicate (len args) 0))))

  (defthm 4veclist-mask-idempotent
    (equal (4veclist-mask masks (4veclist-mask masks x))
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
