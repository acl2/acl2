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
(include-book "aig-arith")
(include-book "svex-rewrite")
(include-book "centaur/gl/gl-mbe" :dir :system)
(include-book "centaur/gl/def-gl-rewrite" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/alists/alist-keys" :dir :System))
(local (include-book "std/osets/element-list" :dir :system))

(local (std::add-default-post-define-hook :fix))

(local (std::deflist svarlist-p (x) (svar-p x) :true-listp t :elementp-of-nil nil))


(defxdoc svex-symbolic-evaluation
  :parents (svex)
  :short "Translating SVEX objects into AIGs for symbolic evaluation")

(defxdoc symbolic.lisp :parents (svex-symbolic-evaluation))
(local (xdoc::set-default-parents symbolic.lisp))

(defsection svex-envs-mask-equiv
  ;; this is only used in symbolic.lisp so could be moved there
  (acl2::defquant svex-envs-mask-equiv (masks env1 env2)
    (forall var
            (equal (equal (4vec-mask (svex-mask-lookup (svex-var var) masks)
                                     (svex-env-lookup var env1))
                          (4vec-mask (svex-mask-lookup (svex-var var) masks)
                                     (svex-env-lookup var env2)))
                   t)))

  (acl2::defexample svex-envs-mask-equiv-mask-look-example
    :pattern (svex-mask-lookup (svex-var var) masks)
    :templates (var)
    :instance-rulename svex-envs-mask-equiv-instancing)

  (acl2::defexample svex-envs-mask-equiv-env-look-example
    :pattern (svex-env-lookup var env)
    :templates (var)
    :instance-rulename svex-envs-mask-equiv-instancing)

  (deffixequiv svex-envs-mask-equiv
    :args ((masks svex-mask-alist-p)
           (env1 svex-env-p)
           (env2 svex-env-p))
    :hints (("goal" :cases ((svex-envs-mask-equiv masks env1 env2)))
            (acl2::witness)))

  (local (acl2::defexample svex-argmasks-okp-example
           :pattern (equal (4vec-mask mask (svex-apply fn (svexlist-eval args env1)))
                           (4vec-mask mask (svex-apply fn (svexlist-eval args env2))))
           :templates (env1 (svexlist-eval args env2))
           :instance-rulename svex-argmasks-okp-instancing))

  (defthm-svex-eval-flag
    (defthm svex-eval-of-mask-equiv-envs
      (implies (and (svex-mask-alist-complete masks)
                    (svex-envs-mask-equiv masks env1 env2))
               (equal (equal (4vec-mask (svex-mask-lookup x masks)
                                        (svex-eval x env1))
                             (4vec-mask (svex-mask-lookup x masks)
                                        (svex-eval x env2)))
                      t))
      :hints ('(:expand ((:free (env) (svex-eval x env)))
                :do-not-induct t)
              (acl2::witness)
              (acl2::witness)
              ;; (and stable-under-simplificationp
              ;;      '(:use ((:instance svex-argmasks-okp-necc
              ;;               (mask (svex-mask-lookup x masks))
              ;;               (argmasks (svex-argmasks-lookup
              ;;                          (svex-call->args x) masks))
              ;;               (env env1)
              ;;               (vals (svexlist-eval (svex-call->args x) env2))))))
              )
      :flag expr)
    (defthm svexlist-eval-of-mask-equiv-envs
      (implies (and (svex-mask-alist-complete masks)
                    (svex-envs-mask-equiv masks env1 env2))
               (equal (equal (4veclist-mask (svex-argmasks-lookup x masks)
                                            (svexlist-eval x env1))
                             (4veclist-mask (svex-argmasks-lookup x masks)
                                            (svexlist-eval x env2)))
                      t))
      :hints ('(:expand ((:free (env) (svexlist-eval x env))
                         (svex-argmasks-lookup x masks))))
      :flag list)))

(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))





;; A symbolic 4vec, with lists of AIGs for the upper/lower
(defprod a4vec
  ((upper true-listp)
   (lower true-listp))
  :layout :tree)

(define a4vec-eval ((x a4vec-p) env)
  :returns (res 4vec-p)
  (b* (((a4vec x) x))
    (4vec (aig-list->s x.upper env)
          (aig-list->s x.lower env)))
  ///
  (defthm a4vec-eval-of-a4vec
    (equal (a4vec-eval (a4vec upper lower) env)
           (4vec (aig-list->s upper env)
                 (aig-list->s lower env))))

  (defthm a4vec-eval-of-const
    (implies (syntaxp (quotep x))
             (equal (a4vec-eval x env)
                    (4vec (aig-list->s (a4vec->upper x) env)
                          (aig-list->s (a4vec->lower x) env)))))

  (defthm a4vec-eval-of-var
    (implies (syntaxp (symbolp x))
             (equal (a4vec-eval x env)
                    (4vec (aig-list->s (a4vec->upper x) env)
                          (aig-list->s (a4vec->lower x) env))))))

(defthm true-listp-of-bfr-scons
  (implies (true-listp b)
           (true-listp (gl::bfr-scons a b)))
  :hints(("Goal" :in-theory (enable gl::bfr-scons)))
  :rule-classes :type-prescription)

(defthm true-listp-of-bfr-sterm
  (true-listp (gl::bfr-sterm a))
  :hints(("Goal" :in-theory (enable gl::bfr-sterm)))
  :rule-classes :type-prescription)

;; (define a4vec-bit-index ((n natp) (x a4vec-p))
;;   :returns (res a4vec-p)
;;   (b* (((a4vec x) x))
;;     (a4vec (aig-scons (nth n x.upper) (aig-sterm nil))
;;            (aig-scons (nth n x.lower) (aig-sterm nil))))
;;   ///
;;   (defthm a4vec-bit-index-correct
;;     (equal (a4vec-eval (a4vec-bit-index n x) env)
;;            (4vec-bit-index n (a4vec-eval x env)))
;;     :hints(("Goal" :in-theory (enable a4vec-eval 4vec-bit-index aig-list->s)))))

(define a2vec-p ((x a4vec-p))
  (b* (((a4vec x) x))
    (aig-=-ss x.upper x.lower))
  ///
  (defthm a2vec-p-correct
    (equal (aig-eval (a2vec-p x) env)
           (2vec-p (a4vec-eval x env)))))

(defmacro a4vec-x () (list 'quote (a4vec (aig-sterm t)
                                         (aig-sterm nil))))
(defmacro a4vec-1x () (list 'quote (a4vec (aig-scons t (aig-sterm nil))
                                          (aig-sterm nil))))
(defmacro a4vec-z () (list 'quote (a4vec (aig-sterm nil)
                                         (aig-scons t (aig-sterm nil)))))
(defmacro a4vec-0 () (list 'quote (a4vec (aig-sterm nil)
                                         (aig-sterm nil))))
(defmacro a4vec-neg1 () (list 'quote (a4vec (aig-sterm t)
                                            (aig-sterm t))))

(defmacro a4vec-pos1 () (list 'quote (a4vec (aig-scons t (aig-sterm nil))
                                            (aig-scons t (aig-sterm nil)))))

(local (defthm aig-ite-of-consts
         (and (equal (aig-ite t a b) a)
              (equal (aig-ite nil a b) b))
         :hints(("Goal" :in-theory (enable aig-ite)))))


(local (defthm true-listp-of-scdr
         (implies (true-listp x)
                  (true-listp (gl::scdr x)))
         :hints(("Goal" :in-theory (enable gl::scdr)))
         :rule-classes :type-prescription))

(define a4vec-ite-fn (test (then a4vec-p) (else a4vec-p))
  :returns (res a4vec-p)
  (cond ((eq test t) (a4vec-fix then))
        ((eq test nil) (a4vec-fix else))
        (t (b* (((a4vec then) then)
                ((a4vec else) else))
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
         (equal (a4vec-ite-fn nil then else) (a4vec-fix else))))

  (defmacro a4vec-ite (test then else)
    (cond ((and (or (symbolp then) (quotep then))
                (or (symbolp else) (quotep else)))
           `(a4vec-ite-fn ,test ,then ,else))
          (t `(mbe :logic (a4vec-ite-fn ,test ,then ,else)
                   :exec (let ((a4vec-ite-test ,test))
                           (if a4vec-ite-test
                               (let ((a4vec-ite-then ,then))
                                 (if (eq a4vec-ite-test t)
                                     a4vec-ite-then
                                   (a4vec-ite-fn a4vec-ite-test a4vec-ite-then ,else)))
                             ,else)))))))

(defthm aig-list->u-when-aig-list->s-nonneg
  (implies (<= 0 (aig-list->s x env))
           (equal (aig-list->u x env)
                  (aig-list->s x env)))
  :hints(("Goal" :in-theory (enable aig-list->u
                                    aig-list->s
                                    gl::scdr
                                    gl::s-endp))))

(local (in-theory (disable gl::s-endp-of-bfr-scons
                           aig-list->s)))

(defthm aig-list->s-open-quote
  (implies (syntaxp (quotep x))
           (equal (aig-list->s x env)
                  (B* (((MV FIRST REST GL::END)
                        (GL::FIRST/REST/END X)))
                      (IF GL::END
                          (GL::BOOL->SIGN (AIG-EVAL FIRST ENV))
                          (BITOPS::LOGCONS (BOOL->BIT (AIG-EVAL FIRST ENV))
                                         (AIG-LIST->S REST ENV))))))
  :hints(("Goal" :in-theory (enable aig-list->s))))


(defthm aig-list->s-of-bfr-snorm
  (equal (aig-list->s (gl::bfr-snorm x) env)
         (aig-list->s x env))
  :hints(("Goal" :in-theory (enable aig-list->s gl::bfr-snorm))))

(defthm aig-list->s-of-bfr-scons
  (equal (aig-list->s (gl::bfr-scons a b) env)
         (bitops::logcons (bool->bit (aig-eval a env))
                  (aig-list->s b env)))
  :hints(("Goal" :expand ((aig-list->s (gl::bfr-scons a b) env)
                          (aig-list->s b env))
          :in-theory (enable gl::s-endp-of-bfr-scons)
          :do-not-induct t)))

(defthm aig-list->s-of-bfr-sterm
  (equal (aig-list->s (gl::bfr-sterm x) env)
         (bool->vec (aig-eval x env)))
  :hints(("Goal" :in-theory (enable aig-list->s))))

(define a4vec-bit-extract ((n a4vec-p) (x a4vec-p))
  :returns (res a4vec-p)
  (b* (((a4vec x) x)
       ((a4vec n) n))
    (a4vec-ite (aig-and (a2vec-p n)
                        (aig-not (aig-sign-s n.upper)))
               (b* ((ubit (aig-logbitp-n2v 1 n.upper x.upper))
                    (lbit (aig-logbitp-n2v 1 n.upper x.lower)))
                 (a4vec (aig-scons ubit (aig-sterm nil))
                        (aig-scons lbit (aig-sterm nil))))
               (a4vec-1x)))
  ///
  (defthm a4vec-bit-extract-correct
    (equal (a4vec-eval (a4vec-bit-extract n x) env)
           (4vec-bit-extract (a4vec-eval n env)
                             (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 4vec-bit-extract
                                      4vec-bit-index)))))

(define a4vec-syntactic-3vec-p-rec ((x true-listp) (y true-listp))
  :measure (+ (len x) (len y))
  (b* (((mv xf xr xe) (gl::first/rest/end x))
       ((mv yf yr ye) (gl::first/rest/end y)))
    (and (or (hons-equal xf yf)
             (eq xf t)
             (eq yf nil))
         (if (and xe ye)
             t
           (a4vec-syntactic-3vec-p-rec xr yr))))
  ///
  (defthm a4vec-syntactic-3vec-p-rec-correct
    (implies (a4vec-syntactic-3vec-p-rec x y)
             (equal (logand (aig-list->s y env) (lognot (aig-list->s x env)))
                    0))
    :hints (("goal" :induct (a4vec-syntactic-3vec-p-rec x y)
             :expand ((aig-list->s y env)
                      (aig-list->s x env))))))

(define a4vec-syntactic-3vec-p ((x a4vec-p))
  (b* (((a4vec x) x))
    (a4vec-syntactic-3vec-p-rec x.upper x.lower))
  ///
  (defthm a4vec-syntactic-3vec-p-correct
    (implies (a4vec-syntactic-3vec-p x)
             (3vec-p (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 3vec-p)))))

(define a3vec-fix ((x a4vec-p))
  :returns (xx a4vec-p)
  (if (a4vec-syntactic-3vec-p x)
      (a4vec-fix x)
    (b* (((a4vec x) x))
      (a4vec (aig-logior-ss x.upper x.lower)
             (aig-logand-ss x.upper x.lower))))
  ///
  (defthm a3vec-fix-correct
    (equal (a4vec-eval (a3vec-fix x) env)
           (3vec-fix (a4vec-eval x env)))
    :hints (("goal" :in-theory (disable a4vec-eval-of-var))
            (and stable-under-simplificationp
                 '(:in-theory (enable 3vec-fix a4vec-eval-of-var))))))


(define a3vec-bitnot ((x a4vec-p))
  :returns (res a4vec-p)
  (b* (((a4vec x) x))
    (a4vec (aig-lognot-s x.lower)
           (aig-lognot-s x.upper)))
  ///
  (defthm a3vec-bitnot-correct
    (equal (a4vec-eval (a3vec-bitnot x) env)
           (3vec-bitnot (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 3vec-bitnot)))))

(define a4vec-onset ((x a4vec-p))
  :returns (res a4vec-p)
  (b* (((a4vec x) x))
    (a4vec x.upper (aig-logand-ss x.upper x.lower)))
  ///
  (defthm a4vec-onset-correct
    (equal (a4vec-eval (a4vec-onset x) env)
           (4vec-onset (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 4vec-onset)))))

(define a4vec-offset ((x a4vec-p))
  :returns (res a4vec-p)
  (b* (((a4vec x) x))
    (a4vec (aig-lognot-s x.lower) (aig-lognot-s (aig-logior-ss x.upper x.lower))))
  ///
  (defthm a4vec-offset-correct
    (equal (a4vec-eval (a4vec-offset x) env)
           (4vec-offset (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 4vec-offset)))))

(define a3vec-bitand ((x a4vec-p) (y a4vec-p))
  :returns (res a4vec-p)
  (b* (((a4vec x) x)
       ((a4vec y) y))
    (a4vec (aig-logand-ss x.upper y.upper)
           (aig-logand-ss x.lower y.lower)))
  ///
  (defthm a3vec-bitand-correct
    (equal (a4vec-eval (a3vec-bitand x y) env)
           (3vec-bitand (a4vec-eval x env)
                        (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 3vec-bitand)))))

(define a3vec-bitor ((x a4vec-p) (y a4vec-p))
  :returns (res a4vec-p)
  (b* (((a4vec x) x)
       ((a4vec y) y))
    (a4vec (aig-logior-ss x.upper y.upper)
           (aig-logior-ss x.lower y.lower)))
  ///
  (defthm a3vec-bitor-correct
    (equal (a4vec-eval (a3vec-bitor x y) env)
           (3vec-bitor (a4vec-eval x env)
                        (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 3vec-bitor)))))

(define a3vec-bitxor ((x a4vec-p) (y a4vec-p))
  :returns (res a4vec-p)
  (b* (((a4vec x) x)
       ((a4vec y) y)
       (xmask (aig-logior-ss
               (aig-logand-ss x.upper (aig-lognot-s x.lower))
               (aig-logand-ss y.upper (aig-lognot-s y.lower)))))
    (a4vec (aig-logior-ss xmask (aig-logxor-ss x.upper y.upper))
           (aig-logand-ss (aig-lognot-s xmask)
                          (aig-logxor-ss x.lower y.lower))))
  ///
  (defthm a3vec-bitxor-correct
    (equal (a4vec-eval (a3vec-bitxor x y) env)
           (3vec-bitxor (a4vec-eval x env)
                        (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 3vec-bitxor)))))



(define a4vec-res ((a a4vec-p) (b a4vec-p))
  :returns (res a4vec-p)
  (b* (((a4vec a) a)
       ((a4vec b) b))
    (a4vec (aig-logior-ss a.upper b.upper)
           (aig-logand-ss a.lower b.lower)))
  ///
  (defthm a4vec-res-correct
    (equal (a4vec-eval (a4vec-res x y) env)
           (4vec-res (a4vec-eval x env)
                     (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 4vec-res)))))

(define a4vec-resand ((a a4vec-p) (b a4vec-p))
  :returns (res a4vec-p)
  (b* (((a4vec a) a)
       ((a4vec b) b))
    (a4vec (aig-logand-ss (aig-logior-ss a.upper a.lower)  ;; a not 0
                          (aig-logand-ss (aig-logior-ss b.upper b.lower)  ;; b not 0
                                         (aig-logior-ss a.upper b.upper)))
           (aig-logand-ss a.lower b.lower)))
  ///
  (defthm a4vec-resand-correct
    (equal (a4vec-eval (a4vec-resand x y) env)
           (4vec-resand (a4vec-eval x env)
                     (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 4vec-resand)))))

(define a4vec-resor ((a a4vec-p) (b a4vec-p))
  :returns (res a4vec-p)
  (b* (((a4vec a) a)
       ((a4vec b) b))
    (a4vec (aig-logior-ss a.upper b.upper)
           (aig-logior-ss (aig-logand-ss a.upper a.lower)  ;; a not 0
                          (aig-logior-ss (aig-logand-ss b.upper b.lower)  ;; b not 0
                                         (aig-logand-ss a.lower b.lower)))))
  ///
  (defthm a4vec-resor-correct
    (equal (a4vec-eval (a4vec-resor x y) env)
           (4vec-resor (a4vec-eval x env)
                     (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 4vec-resor)))))

(define a4vec-override ((a a4vec-p) (b a4vec-p))
  :returns (res a4vec-p)
  (b* (((a4vec a) a)
       ((a4vec b) b))
    (a4vec (aig-logior-ss (aig-logand-ss a.lower b.upper) a.upper)
           (aig-logand-ss (aig-logior-ss a.upper b.lower) a.lower)))
  ///
  (defthm a4vec-override-correct
    (equal (a4vec-eval (a4vec-override x y) env)
           (4vec-override (a4vec-eval x env)
                          (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 4vec-override))
           (bitops::logbitp-reasoning))))

(define a3vec-reduction-and ((x a4vec-p))
  :returns (res a4vec-p)
  (b* (((a4vec x) x))
    (a4vec (aig-sterm (aig-=-ss x.upper (aig-sterm t)))
           (aig-sterm (aig-=-ss x.lower (aig-sterm t)))))
  ///
  (defthm a3vec-reduction-and-correct
    (equal (a4vec-eval (a3vec-reduction-and x) env)
           (3vec-reduction-and (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 3vec-reduction-and)))))

(define a3vec-reduction-or ((x a4vec-p))
  :returns (res a4vec-p)
  (b* (((a4vec x) x))
    (a4vec (aig-sterm (aig-not (aig-=-ss x.upper (aig-sterm nil))))
           (aig-sterm (aig-not (aig-=-ss x.lower (aig-sterm nil))))))
  ///
  (defthm a3vec-reduction-or-correct
    (equal (a4vec-eval (a3vec-reduction-or x) env)
           (3vec-reduction-or (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 3vec-reduction-or)))))

(define a4vec-zero-ext ((n a4vec-p) (x a4vec-p))
  :returns (res a4vec-p)
  (b* (((a4vec n) n)
       ((a4vec x) x))
  (a4vec-ite
   (aig-and (a2vec-p n)
            (aig-not (aig-sign-s n.upper)))
   (b* ((mask (aig-lognot-s (aig-ash-ss 1 (aig-sterm t) n.upper))))
     (a4vec (aig-logand-ss x.upper mask)
            (aig-logand-ss x.lower mask)))
   (a4vec-x)))
  ///
  (local (defthm logand-of-lognot-ash-minus1
           (implies (natp n)
                    (equal (logand x (lognot (ash -1 n)))
                           (loghead n x)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                              bitops::ihsext-inductions)))))

  (defthm a4vec-zero-ext-correct
    (equal (a4vec-eval (a4vec-zero-ext n x) env)
           (4vec-zero-ext (a4vec-eval n env)
                          (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 4vec-zero-ext)))))

(define a4vec-sign-ext ((n a4vec-p) (x a4vec-p))
  :returns (res a4vec-p)
  (b* (((a4vec n) n)
       ((a4vec x) x))
  (a4vec-ite
   (aig-and (a2vec-p n)
            (aig-and (aig-not (aig-sign-s n.upper))
                     (aig-not (aig-=-ss n.upper (aig-sterm nil)))))
   (b* ((smask (aig-ash-ss 1 (aig-sterm t) n.upper))
        (bmask (aig-lognot-s smask))
        (signpos (aig-+-ss nil (aig-sterm t) n.upper))
        (uext  (aig-sterm (aig-logbitp-n2v 1 signpos x.upper)))
        (lext  (aig-sterm (aig-logbitp-n2v 1 signpos x.lower))))
     (a4vec (aig-logior-ss (aig-logand-ss bmask x.upper)
                           (aig-logand-ss smask uext))
            (aig-logior-ss (aig-logand-ss bmask x.lower)
                           (aig-logand-ss smask lext))))
   (a4vec-x)))
  ///
  (local (defthm logext-formulation
           (implies (natp n)
                    (equal (logior (logand x (lognot (ash -1 n)))
                                   (logand (ash -1 n)
                                           (bool->vec (logbitp (+ -1 n) x))))
                           (logext n x)))
           :hints((bitops::logbitp-reasoning))))


  (defthm a4vec-sign-ext-correct
    (equal (a4vec-eval (a4vec-sign-ext n x) env)
           (4vec-sign-ext (a4vec-eval n env)
                          (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 4vec-sign-ext)
            :do-not-induct t))
    :otf-flg t))

(define logcollapse ((position natp)
                     (x integerp))
  :short "OR together all the bits of x at position or above, collapsing them
into the single bit at position."
  :long "<p>This operation helps avoid catastrophically large shifts in computing,
e.g., concatenations with symbolic widths.  When there is a care-mask of width
w, then we can collapse all the bits at w and above into the bit at w, because
the presence of those upper bits means that the shift is longer than we care
about.</p>

<p>There is a large potential for off-by-one errors when thinking about this
function.  It may help to start with the fact that @('(logcollapse 0 x)')
collapses all bits of x into a single bit.  In general, @('(logcollapse n x)')
results in at most n+1 bits.</p>"
  (b* ((position (lnfix position))
       (x (lifix x)))
    (logior (loghead position x)
            (ash (acl2::b-not (bool->bit (eql 0 (logtail position x)))) position))))


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

  (defun mask-equiv-ind (mask x y)
    (if (zp mask)
        (list x y)
      (mask-equiv-ind (logcdr mask) (logcdr x) (logcdr y))))

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

  )

(define aig-logcollapse-ns ((n natp)
                            x)
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


(define a4vec-concat ((w a4vec-p) (x a4vec-p) (y a4vec-p) (mask 4vmask-p))
  :returns (res a4vec-p)
  (b* (((a4vec w) w)
       ((a4vec x) x)
       ((a4vec y) y))
  (a4vec-ite
   (aig-and (a2vec-p w)
            (aig-not (aig-sign-s w.upper)))
   (b* ((mask (4vmask-fix mask))
        ((when (eql mask 0)) (a4vec-0))
        (shift (if (< 0 mask)
                   ;; Collapse the upper bits of the shift
                   (aig-logcollapse-ns (integer-length (integer-length mask))
                                       w.upper)
                 w.upper))
        (xmask (aig-lognot-s (aig-ash-ss 1 (aig-sterm t) shift)))
        (yshu (aig-ash-ss 1 y.upper shift))
        (yshl (aig-ash-ss 1 y.lower shift)))
     (a4vec (aig-logior-ss (aig-logand-ss xmask x.upper)
                           yshu)
            (aig-logior-ss (aig-logand-ss xmask x.lower)
                           yshl)))
   (a4vec-x)))
  ///
  (local (defthm logapp-formulation
           (implies (natp n)
                    (equal (logior (ash y n)
                                   (logand x (lognot (ash -1 n))))
                           (logapp n x y)))
           :hints((bitops::logbitp-reasoning))))

  ;; (local (defthm logapp-of-loghead-under-mask
  ;;          (implies (and (integerp mask)
  ;;                        (<= 0 mask))
  ;;                   (equal (logand mask
  ;;                                  (logapp (loghead (integer-length mask) bits)


  (defthm a4vec-concat-correct
    (equal (4vec-mask mask (a4vec-eval (a4vec-concat n x y mask) env))
           (4vec-mask mask (4vec-concat (a4vec-eval n env)
                                        (a4vec-eval x env)
                                        (a4vec-eval y env))))
    :hints(("Goal" :in-theory (enable 4vec-concat 4vec-mask)
            :do-not-induct t))
    :otf-flg t))

(define aig-right-shift-ss ((place posp) n shamt)
  (b* (((mv shdig shrst shend) (gl::first/rest/end shamt))
       (place (mbe :logic (acl2::pos-fix place)
                   :exec place)))
     (if shend
         (aig-logtail-ns 1 n)
       (let ((rst (aig-right-shift-ss (* 2 place) n shrst)))
         (aig-ite-bss shdig rst (aig-logtail-ns place rst)))))
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
                         (+ -1 (acl2::pos-fix place)
                            (* (acl2::pos-fix place)
                               (aig-list->s shamt env))))))
    :hints (("goal" :induct t
             :in-theory (enable acl2::logcons)
             :expand ((aig-list->s shamt env))))))


(define a4vec-rsh ((amt a4vec-p) (x a4vec-p) (mask 4vmask-p))
  :returns (res a4vec-p)
  (b* (((a4vec amt) amt)
       ((a4vec x) x))
    (a4vec-ite
     (a2vec-p amt)
     (b* ((shamt (aig-unary-minus-s amt.upper))
          (sign (aig-sign-s shamt))
          (mask (4vmask-fix mask))
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

(define a4vec-lsh ((amt a4vec-p) (x a4vec-p))
  :returns (res a4vec-p)
  (b* (((a4vec amt) amt)
       ((a4vec x) x))
    (a4vec-ite
     (a2vec-p amt)
     (a4vec (aig-ash-ss 1 x.upper amt.upper)
            (aig-ash-ss 1 x.lower amt.upper))
     (a4vec-x)))
  ///
  (defthm a4vec-lsh-correct
    (equal (a4vec-eval (a4vec-lsh amt x) env)
           (4vec-lsh (a4vec-eval amt env)
                     (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 4vec-lsh)))))

(defthm parity-of-greater
  (implies (and (< (+ 1 (integer-length x)) (nfix n))
                (natp x))
           (equal (parity n x)
                  (parity (+ 1 (integer-length x)) x)))
  :hints(("Goal" :in-theory (enable parity)
          :induct (parity n x)
          :expand ((integer-length x)
                   (:free (n) (parity n x))))))

(define aig-parity-s ((x true-listp))
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
  :returns (res a4vec-p)
  (b* (((a4vec x) x))
    (a4vec-ite
     (aig-and (a2vec-p x)
              (aig-not (aig-sign-s x.upper)))
     (let* ((bit (aig-parity-s x.upper))
            (vec (aig-sterm bit)))
       (a4vec vec vec))
     (a4vec-x)))
  ///
  (defthm a4vec-parity-correct
    (equal (a4vec-eval (a4vec-parity x) env)
           (4vec-parity (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 4vec-parity bool->vec)))))

(define a4vec-plus ((x a4vec-p) (y a4vec-p))
  :returns (res a4vec-p)
  (a4vec-ite
   (aig-and (a2vec-p x)
            (a2vec-p y))
   (b* (((a4vec x) x)
        ((a4vec y) y)
        (res (aig-+-ss nil x.upper y.upper)))
     (a4vec res res))
   (a4vec-x))
  ///
  (defthm a4vec-plus-correct
    (equal (a4vec-eval (a4vec-plus x y) env)
           (4vec-plus (a4vec-eval x env)
                      (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 4vec-plus)))))


(define a4vec-minus ((x a4vec-p) (y a4vec-p))
  :returns (res a4vec-p)
  (a4vec-ite
   (aig-and (a2vec-p x)
            (a2vec-p y))
   (b* (((a4vec x) x)
        ((a4vec y) y)
        (res (aig-+-ss t x.upper (aig-lognot-s y.upper))))
     (a4vec res res))
   (a4vec-x))
  ///
  (defthm a4vec-minus-correct
    (equal (a4vec-eval (a4vec-minus x y) env)
           (4vec-minus (a4vec-eval x env)
                      (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 4vec-minus lognot)))))

(define a4vec-uminus ((x a4vec-p))
  :returns (res a4vec-p)
  (a4vec-ite
   (a2vec-p x)
   (b* (((a4vec x) x)
        (res (aig-+-ss t nil (aig-lognot-s x.upper))))
     (a4vec res res))
   (a4vec-x))
  ///
  (defthm a4vec-uminus-correct
    (equal (a4vec-eval (a4vec-uminus x) env)
           (4vec-uminus (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 4vec-uminus lognot)))))

(define a4vec-xdet ((x a4vec-p))
  :returns (res a4vec-p)
  (a4vec-ite
   (a2vec-p x)
   (a4vec-fix x)
   (a4vec-x))
  ///
  (defthm a4vec-xdet-correct
    (equal (a4vec-eval (a4vec-xdet x) env)
           (4vec-xdet (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 4vec-xdet lognot)))))

(define a4vec-clog2 ((x a4vec-p))
  :returns (res a4vec-p)
   (b* (((a4vec x) x))
     (a4vec-ite
      (aig-and (a2vec-p x)
               (aig-not (aig-sign-s x.upper)))
      (b* ((res (aig-integer-length-s (aig-+-ss nil '(t) x.upper))))
        (a4vec res res))
      (a4vec-x)))
  ///
  (defthm a4vec-clog2-correct
    (equal (a4vec-eval (a4vec-clog2 x) env)
           (4vec-clog2 (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 4vec-clog2)))))

(define a4vec-times ((x a4vec-p) (y a4vec-p))
  :returns (res a4vec-p)
  (a4vec-ite
   (aig-and (a2vec-p x)
            (a2vec-p y))
   (b* (((a4vec x) x)
        ((a4vec y) y)
        (res (aig-*-ss x.upper y.upper)))
     (a4vec res res))
   (a4vec-x))
  ///
  (defthm a4vec-times-correct
    (equal (a4vec-eval (a4vec-times x y) env)
           (4vec-times (a4vec-eval x env)
                      (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 4vec-times lognot)))))

(define a4vec-quotient ((x a4vec-p) (y a4vec-p))
  :returns (res a4vec-p)
  (a4vec-ite
   (aig-and (aig-and (a2vec-p x)
                     (a2vec-p y))
            (aig-not (aig-=-ss (a4vec->upper y) (aig-sterm nil))))
   (b* (((a4vec x) x)
        ((a4vec y) y)
        (res (aig-truncate-ss x.upper y.upper)))
     (a4vec res res))
   (a4vec-x))
  ///
  (defthm a4vec-quotient-correct
    (equal (a4vec-eval (a4vec-quotient x y) env)
           (4vec-quotient (a4vec-eval x env)
                      (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 4vec-quotient lognot)))))

(define a4vec-remainder ((x a4vec-p) (y a4vec-p))
  :returns (res a4vec-p)
  (a4vec-ite
   (aig-and (aig-and (a2vec-p x)
                     (a2vec-p y))
            (aig-not (aig-=-ss (a4vec->upper y) (aig-sterm nil))))
   (b* (((a4vec x) x)
        ((a4vec y) y)
        (res (aig-rem-ss x.upper y.upper)))
     (a4vec res res))
   (a4vec-x))
  ///
  (defthm a4vec-remainder-correct
    (equal (a4vec-eval (a4vec-remainder x y) env)
           (4vec-remainder (a4vec-eval x env)
                      (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 4vec-remainder lognot)))))

(define a4vec-< ((x a4vec-p) (y a4vec-p))
  :returns (res a4vec-p)
  (a4vec-ite
   (aig-and (a2vec-p x)
            (a2vec-p y))
   (b* (((a4vec x) x)
        ((a4vec y) y)
        (res (aig-sterm (aig-<-ss x.upper y.upper))))
     (a4vec res res))
   (a4vec-x))
  ///
  (defthm a4vec-<-correct
    (equal (a4vec-eval (a4vec-< x y) env)
           (4vec-< (a4vec-eval x env)
                   (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 4vec-< lognot)))))

(define a3vec-== ((x a4vec-p) (y a4vec-p))
  :returns (res a4vec-p)
  (a3vec-reduction-and (a3vec-bitnot (a3vec-bitxor x y)))
  ///
  (defthm a3vec-==-correct
    (equal (a4vec-eval (a3vec-== x y) env)
           (3vec-== (a4vec-eval x env)
                    (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 4vec-== 3vec-==)))))

(define a4vec-=== ((x a4vec-p) (y a4vec-p))
  :returns (res a4vec-p)
  (b* (((a4vec x))
       ((a4vec y))
       (val (aig-sterm (aig-and (aig-=-ss x.upper y.upper)
                                (aig-=-ss x.lower y.lower)))))
    (a4vec val val))
  ///
  (defthm a4vec-===-correct
    (equal (a4vec-eval (a4vec-=== x y) env)
           (4vec-=== (a4vec-eval x env)
                    (a4vec-eval y env)))
    :hints(("Goal" :in-theory (enable 4vec-=== bool->vec)))))

(defun aig-neg/abs (x)
  (b* (((when (or (atom x) (cdr x)))
        (mv nil x))
       ((mv neg1 abs1) (aig-neg/abs (car x))))
    (mv (not neg1) abs1)))

;; (~a.1 &  c.1) |
;; ( a.0 &  b.1) |
;; ( (a.1 & ~a.0) & (   ( b.1 | c.1 )
;;                    | (   ~( b.0 &  c.0)
;;                         & ( b.0 | c.0 ) ) ) ) ) )

;; (~a.1 &  c.0) |
;; ( a.0 &  b.0) |
;; ( (a.1 & ~a.0) & (   ( b.0 & c.0 )
;;                    & (   ~( b.1 |  c.1)
;;                         | ( b.1 & c.1 ) ) ) ) ) )

;; This reduces nicely when a is known and when known Boolean.

;; When b and c are both known 3vec, then the a=x portion reduces to:
;; ( (a.1 & ~a.0) & ( b.1 | c.1 )
;; ( (a.1 & ~a.0) & ( b.0 & c.0 )

;; when e.g. just b is known Boolean, it reduces to:
;; ( (a.1 & ~a.0) & ( ( b.1 | c.1 ) | c.0 )
;; ( (a.1 & ~a.0) & ( ( b.0 & c.0 ) & c.1 )


;; (define aig-logand-is ((mask integerp)
;;                        x)
;;   :returns (new-x)
;;   :prepwork ((local (in-theory (enable acl2::integer-length**))))
;;   :measure (integer-length mask)
;;   (b* (((when (zip mask)) nil)
;;        ((when (eql mask -1)) x)
;;        ((mv first rest ?end) (gl::first/rest/end x)))
;;     (aig-scons (if (logbitp 0 mask) first nil)
;;                (aig-logand-is (logcdr mask) rest)))
;;   ///

;;   ;; (local (defthm logcar/logcdr-of-bool->sign
;;   ;;          (and (equal (logcar (gl::bool->sign x))
;;   ;;                      (acl2::bool->bit x))
;;   ;;               (equal (logcdr (gl::bool->sign x))
;;   ;;                      (gl::bool->sign x)))
;;   ;;          :hints(("Goal" :in-theory (enable gl::bool->sign acl2::bool->bit)))))

;;   (defthm aig-logand-is-correct
;;     (equal (aig-list->s (aig-logand-is mask x) env)
;;            (logand mask (aig-list->s x env)))
;;     :hints(("Goal" :in-theory (e/d (acl2::logand** aig-list->s)
;;                                    (GL::SCDR-WHEN-S-ENDP))))))
       
(define aig-i2v ((x integerp))
  :measure (integer-length x)
  :prepwork ((local (in-theory (enable acl2::integer-length**))))
  (cond ((zip x) nil)
        ((eql x -1) '(t))
        (t (aig-scons (logbitp 0 x) (aig-i2v (logcdr x)))))
  ///
  (defthm aig-i2v-correct
    (equal (aig-list->s (aig-i2v x) env)
           (ifix x))))


(local (defthm 3vec-p-of-4vec-mask
         (implies (3vec-p x)
                  (3vec-p (4vec-mask mask x)))
         :hints(("Goal" :in-theory (enable 4vec-mask 3vec-p))
                (acl2::logbitp-reasoning))))

(define a4vec-mask ((mask 4vmask-p)
                    (x a4vec-p))
  :returns (masked-a4vec a4vec-p)
  (B* (((a4vec x)))
    (a4vec (aig-logior-ss (aig-i2v (lognot (4vmask-fix mask))) x.upper)
           (aig-logand-ss (aig-i2v (4vmask-fix mask)) x.lower)))
  ///
  (defthm a4vec-mask-correct
    (equal (a4vec-eval (a4vec-mask mask x) env)
           (4vec-mask mask (a4vec-eval x env)))
    :hints(("Goal" :in-theory (enable 4vec-mask)))))
  

(define a3vec-? ((x a4vec-p) (y a4vec-p) y3p (z a4vec-p) z3p)
  :returns (res a4vec-p)
  (b* (((a4vec a) x)
       ((a4vec b) y)
       ((a4vec c) z)
       ;; common subexpressions between the two
       (a=1 (aig-not (aig-=-ss a.lower nil)))
       (a=0 (aig-=-ss a.upper nil))
       (a=x (aig-and (aig-not a=1) (aig-not a=0)))
       (b1vc1 (aig-logior-ss b.upper c.upper))
       (b0^c0 (aig-logand-ss b.lower c.lower))

       ;; upper
       (boolcase (aig-logior-ss (aig-ite-bss-fn a=1 b.upper nil)
                                (aig-ite-bss-fn a=0 c.upper nil)))
       (xcase (cond ((and y3p z3p) b1vc1)
                    (y3p (aig-logior-ss b1vc1 c.lower))
                    (z3p (aig-logior-ss b1vc1 b.lower))
                    (t (aig-logior-ss b1vc1
                                      (aig-logand-ss
                                       (aig-lognot-s b0^c0)
                                       (aig-logior-ss b.lower c.lower))))))
       (upper (aig-logior-ss boolcase
                             (aig-ite-bss-fn a=x xcase nil)))

       ;; lower
       (boolcase (aig-logior-ss (aig-ite-bss-fn a=1 b.lower nil)
                                (aig-ite-bss-fn a=0 c.lower nil)))
       (xcase (cond ((and y3p z3p) b0^c0)
                    (y3p (aig-logand-ss b0^c0 c.upper))
                    (z3p (aig-logand-ss b0^c0 b.upper))
                    (t (aig-logand-ss b0^c0
                                      (aig-logior-ss
                                       (aig-lognot-s b1vc1)
                                       (aig-logand-ss b.upper c.upper))))))
       (lower (aig-logior-ss boolcase
                             (aig-ite-bss-fn a=x xcase nil))))
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
           (bitops::logbitp-reasoning)
           (and stable-under-simplificationp
                '(:bdd (:vars nil))))))

(define a3vec-bit? ((x a4vec-p) (y a4vec-p) y3p (z a4vec-p) z3p)
  :returns (res a4vec-p)
  (b* (((a4vec a) x)
       ((a4vec b) y)
       ((a4vec c) z)
       ;; common subexpressions between the two
       (b1vc1 (aig-logior-ss b.upper c.upper))
       (b0^c0 (aig-logand-ss b.lower c.lower))
       (a=x   (aig-logand-ss a.upper (aig-lognot-s a.lower)))
       ;; upper
       (boolcase (aig-logior-ss (aig-logand-ss a.lower b.upper)
                                (aig-logand-ss (aig-lognot-s a.upper) c.upper)))
       (xcase (cond ((and y3p z3p) b1vc1)
                    (y3p (aig-logior-ss b1vc1 c.lower))
                    (z3p (aig-logior-ss b1vc1 b.lower))
                    (t (aig-logior-ss b1vc1
                                      (aig-logand-ss
                                       (aig-lognot-s b0^c0)
                                       (aig-logior-ss b.lower c.lower))))))
       (upper (aig-logior-ss boolcase
                             (aig-logand-ss a=x xcase)))

       ;; lower
       (boolcase (aig-logior-ss (aig-logand-ss a.lower b.lower)
                                (aig-logand-ss (aig-lognot-s a.upper) c.lower)))
       (xcase (cond ((and y3p z3p) b0^c0)
                    (y3p (aig-logand-ss b0^c0 c.upper))
                    (z3p (aig-logand-ss b0^c0 b.upper))
                    (t (aig-logand-ss b0^c0
                                      (aig-logior-ss
                                       (aig-lognot-s b1vc1)
                                       (aig-logand-ss b.upper c.upper))))))
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

(defthm aig-list->s-of-i2v
  (equal (aig-list->s (gl::i2v x) env)
         (ifix x))
  :hints(("Goal" :in-theory (enable aig-list->s gl::i2v))))


(define 4vec->a4vec ((x 4vec-p))
  :returns (res a4vec-p)
  (b* (((4vec x) x))
    (a4vec (gl::i2v x.upper)
           (gl::i2v x.lower)))
  ///
  (defthm 4vec->a4vec-correct
    (equal (a4vec-eval (4vec->a4vec x) env)
           (4vec-fix x))))

(defalist svex-a4vec-env :key-type svar :val-type a4vec)

(define svex-a4vec-env-eval ((x svex-a4vec-env-p) env)
  :returns (xx svex-env-p)
  :measure (len (svex-a4vec-env-fix x))
  (b* ((x (svex-a4vec-env-fix x)))
    (if (atom x)
        nil
      (cons (cons (svar-fix (caar x))
                  (a4vec-eval (cdar x) env))
            (svex-a4vec-env-eval (cdr x) env)))))

(deflist a4veclist :elt-type a4vec :true-listp t)

(define a4veclist-eval ((x a4veclist-p) env)
  :returns (vals 4veclist-p)
  (if (atom x)
      nil
    (cons (a4vec-eval (car x) env)
          (a4veclist-eval (cdr x) env))))








(define a4veclist-nth ((n natp) (x a4veclist-p))
  :returns (elt a4vec-p)
  :guard-hints (("goal" :in-theory (enable nth a4veclist-p)))
  (mbe :logic (if (< (nfix n) (len x))
                  (a4vec-fix (nth n x))
                (a4vec-x))
       :exec (or (nth n x) (a4vec-x)))
  ///
  (defthm a4veclist-nth-out-of-bounds
    (implies (<= (len x) (nfix n))
             (equal (a4veclist-nth n x) (a4vec-x))))
  (defthm a4veclist-nth-in-of-bounds
    (implies (< (nfix n) (len x))
             (equal (a4veclist-nth n x) (a4vec-fix (nth n x))))))

(define svexlist-nth ((n natp) (x svexlist-p))
  :returns (elt svex-p)
  :guard-hints (("goal" :in-theory (enable nth svexlist-p)))
  (mbe :logic (if (< (nfix n) (len x))
                  (svex-fix (nth n x))
                (svex-x))
       :exec (or (nth n x) (svex-x)))
  ///
  (defthm svexlist-nth-out-of-bounds
    (implies (<= (len x) (nfix n))
             (equal (svexlist-nth n x) (svex-x))))
  (defthm svexlist-nth-in-of-bounds
    (implies (< (nfix n) (len x))
             (equal (svexlist-nth n x) (svex-fix (nth n x))))))

(local (defthm nth-of-svexlist-eval
         (equal (nth n (svexlist-eval x env))
                (and (< (nfix n) (len x))
                     (svex-eval (nth n x) env)))
         :hints(("Goal" :in-theory (enable nth svexlist-eval)
                 :induct (nth n x)))))
(local (defthm nth-of-a4veclist-eval
         (equal (nth n (a4veclist-eval x env))
                (and (< (nfix n) (len x))
                     (a4vec-eval (nth n x) env)))
         :hints(("Goal" :in-theory (enable nth a4veclist-eval)
                 :induct (nth n x)))))

(define maybe-a3vec-fix ((v (a4vec-p v)) (x svex-p))
  :returns (vv a4vec-p)
  (if (3valued-syntaxp (svex-fix x))
      (a4vec-fix v)
    (a3vec-fix v))
  ///
  (local (defthm nth-under-iff-when-a4veclist-p
           (implies (a4veclist-p x)
                    (iff (nth n x)
                         (< (nfix n) (len x))))
           :hints(("Goal" :in-theory (enable a4veclist-p nth)))))

  (local (defthm nth-out-of-bounds
           (implies (<= (len x) (nfix n))
                    (not (nth n x)))
           :hints(("Goal" :in-theory (enable nth)))))

  (defthm maybe-a3vec-fix-when-implies
    (implies (case-split (implies (3valued-syntaxp x)
                                  (3vec-p (a4vec-eval v env))))
             (equal (a4vec-eval (maybe-a3vec-fix v x) env)
                    (3vec-fix (a4vec-eval v env)))))

  (defthm maybe-a3vec-fix-of-nths
    (implies (equal (a4veclist-eval vals env)
                    (svexlist-eval x (svex-a4vec-env-eval a4env env)))
             (equal (a4vec-eval (maybe-a3vec-fix (nth n vals) (nth n x)) env)
                    (3vec-fix (a4vec-eval (nth n vals) env))))
    :hints(("Goal" :in-theory (e/d (a4veclist-nth)
                                   (nth-of-svexlist-eval)
                                   (nth-of-a4veclist-eval))
            :use ((:instance nth-of-svexlist-eval
                   (env (svex-a4vec-env-eval a4env env)))
                  (:instance nth-of-a4veclist-eval)))))

  (defthm maybe-a3vec-fix-of-a3vec
    (implies (a4vec-syntactic-3vec-p v)
             (equal (maybe-a3vec-fix v x)
                    (a4vec-fix v)))
    :hints(("Goal" :in-theory (enable a3vec-fix)))))

(define aig-rev-blocks-nns ((nbits natp)
                            (blocksz posp)
                            x)
  (b* ((nbits (lnfix nbits))
       (blocksz (mbe :logic (acl2::pos-fix blocksz) :exec blocksz))
       ((when (< nbits blocksz))
        (aig-loghead-ns nbits x))
       (next-nbits (- nbits blocksz))
       (rest (aig-rev-blocks-nns
              next-nbits blocksz (aig-logtail-ns blocksz x))))
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
  :prepwork ((local (in-theory (disable unsigned-byte-p))))
  :guard (unsigned-byte-p blocksz-bitidx blocksz-lowbits)

  :guard-debug t
  (b* (((mv head tail end) (gl::first/rest/end blocksz))
       (lowbits (mbe :logic (loghead blocksz-bitidx (nfix blocksz-lowbits))
                     :exec blocksz-lowbits))
       ((when end)
        (aig-ite-bss head
                     ;; negative: revert to 1
                     (aig-rev-blocks-nns nbits 1 x)
                     ;; nonnegative
                     (aig-rev-blocks-nns nbits (acl2::pos-fix lowbits) x))))
    (aig-ite-bss head
                 (aig-rev-blocks-nss nbits
                                     (logior
                                      (ash 1 (lnfix blocksz-bitidx))
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
                                                x)
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

  :guard-debug t
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

  (local (defthm not-natp-when-negative
           (implies (< x 0)
                    (not (natp x)))))

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
  :returns (res a4vec-p)
  (b* (((a4vec w) w)
       ((a4vec b) b)
       ((a4vec x) x))
    (a4vec-ite
     (aig-and* (a2vec-p w)
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

(define a4vec-wildeq ((a a4vec-p) (b a4vec-p))
  :returns (res a4vec-p)
  (b* ((eq (a3vec-bitnot (a3vec-bitxor (a3vec-fix a) (a3vec-fix b))))
       ((a4vec a)) ((a4vec b))
       (zmask (aig-logand-ss
               (aig-lognot-s b.upper) b.lower)))
    (a3vec-reduction-and (a3vec-bitor eq (a4vec zmask zmask))))
  ///
  (defthm a4vec-wildeq-correct
    (equal (a4vec-eval (a4vec-wildeq a b) env)
           (4vec-wildeq (a4vec-eval a env)
                        (a4vec-eval b env)))
    :hints(("Goal" :in-theory (enable 4vec-wildeq 4vec-bitxor-redef 2vec)))))


(define a4vec-symwildeq ((a a4vec-p) (b a4vec-p))
  :returns (res a4vec-p)
  (b* ((eq (a3vec-bitnot (a3vec-bitxor (a3vec-fix a) (a3vec-fix b))))
       ((a4vec a)) ((a4vec b))
       (zmask (aig-logior-ss
               (aig-logand-ss
                (aig-lognot-s b.upper) b.lower)
               (aig-logand-ss
                (aig-lognot-s a.upper) a.lower))))
    (a3vec-reduction-and (a3vec-bitor eq (a4vec zmask zmask))))
  ///
  (defthm a4vec-symwildeq-correct
    (equal (a4vec-eval (a4vec-symwildeq a b) env)
           (4vec-symwildeq (a4vec-eval a env)
                        (a4vec-eval b env)))
    :hints(("Goal" :in-theory (enable 4vec-symwildeq 4vec-bitxor-redef 2vec)))))


(define 4vmask-nth ((n natp) (x 4vmasklist-p))
  :returns (mask 4vmask-p :rule-classes (:rewrite :type-prescription))
  (b* ((x (4vmasklist-fix x)))
    (if (< (lnfix n) (len x))
        (4vmask-fix (nth n x))
      -1)))
  

;; (define maybe-a4vec-fix ((v (or (a4vec-p v) (not v))))
;;   :returns (vv a4vec-p)
;;   (if v (a4vec-fix v) (a4vec-x)))

(defconst *svex-aig-op-table*
  ;; fn name, non-3vec-fixing function, args (with notation for 3vec-fixed ones and masks)
  '((id        a4vec-fix            (x)                     "identity function")
    (bitsel    a4vec-bit-extract    (index x)               "bit select")
    (unfloat   a4vec-fix            ((3v x))                "change Z bits to Xes")
    (bitnot    a3vec-bitnot         ((3v x))                "bitwise negation")
    (onp       a4vec-onset          (x)                     "bitwise onset")
    (offp      a4vec-offset         (x)                     "bitwise offset")
    (bitand    a3vec-bitand         ((3v x) (3v y))         "bitwise AND")
    (bitor     a3vec-bitor          ((3v x) (3v y))         "bitwise OR")
    (bitxor    a3vec-bitxor         ((3v x) (3v y))         "bitwise XOR")
    (res       a4vec-res            (x y)                   "resolve (short together)")
    (resand    a4vec-resand         (x y)                   "resolve wired AND")
    (resor     a4vec-resor          (x y)                   "resolve wired OR")
    (override  a4vec-override       (x y)                   "resolve different strengths")
    (uand      a3vec-reduction-and  ((3v x))                "unary (reduction) AND")
    (uor       a3vec-reduction-or   ((3v x))                "unary (reduction) OR")
    (uxor      a4vec-parity         (x)                     "reduction XOR, i.e. parity")
    (zerox     a4vec-zero-ext       (width x)               "zero extend")
    (signx     a4vec-sign-ext       (width x)               "sign extend")
    (concat    a4vec-concat         (width x y (mask m))    "concatenate at a given bit width")
    (blkrev    a4vec-rev-blocks     (width blksz x)         "reverse block order")
    (rsh       a4vec-rsh            (shift x (mask m))      "right shift")
    (lsh       a4vec-lsh            (shift x)               "left shift")
    (+         a4vec-plus           (x y)                   "addition")
    (b-        a4vec-minus          (x y)                   "subtraction")
    (u-        a4vec-uminus         (x)                     "unary minus")
    (xdet      a4vec-xdet           (x)                     "x detect")
    (*         a4vec-times          (x y)                   "multiplication")
    (/         a4vec-quotient       (x y)                   "division")
    (%         a4vec-remainder      (x y)                   "modulus")
    (<         a4vec-<              (x y)                   "less than")
    (clog2     a4vec-clog2          (x)                     "ceiling of log2")
    (==        a3vec-==             ((3v x) (3v y))         "equality")
    (===       a4vec-===            (x y)                   "case equality")
    (==?       a4vec-wildeq         (x y)                   "wildcard equality")
    (==??      a4vec-symwildeq      (x y)                   "symmetric wildcard equality")
    (?         a3vec-?              ((3v test) (3vp then) (3vp else)) "if-then-else")
    (bit?      a3vec-bit?           ((3v test) (3vp then) (3vp else)) "bitwise if-then-else")))



(defun svex-apply-aig-collect-args (n restargs argsvar svvar maskvar ;; argmasks-var
                                      )
  (let* ((n (nfix n)))
    (if (atom restargs)
        nil
      (append (if (consp (car restargs))
                  (case (caar restargs)
                    (3v
                     `((maybe-a3vec-fix ;; (a4vec-mask (4vmask-nth ,n ,argmasks-var)
                        (a4veclist-nth ,n ,argsvar)
                        (svexlist-nth ,n ,svvar))))
                    (3vp
                     `(;; (a4vec-mask (4vmask-nth ,n ,argmasks-var)
                       (a4veclist-nth ,n ,argsvar)
                       (3valued-syntaxp (svexlist-nth ,n ,svvar))))
                    (mask
                     `(,maskvar))
                    (t (prog2$
                        (er hard? 'svex-apply-aig-collect-args "bad formal expr")
                        `((a4veclist-nth ,n ,argsvar)))))
                `((a4veclist-nth ,n ,argsvar)))
              (svex-apply-aig-collect-args (+ 1 n) (cdr restargs) argsvar svvar maskvar ;; argmasks-var
                                           )))))


;; (defun svex-apply-aig-uses-argmasks (args)
;;   (if (atom args)
;;       nil
;;     (or (and (consp (car args))
;;              (or (eq (caar args) '3v)
;;                  (eq (caar args) '3vp)))
;;         (svex-apply-aig-uses-argmasks (cdr args)))))

(defun svex-apply-aig-cases-fn (argsvar svvar maskvar optable)
  (b* (((when (atom optable)) '((otherwise (a4vec-x))))
       ((list sym fn args) (car optable))
       (acc-args (svex-apply-aig-collect-args 0 args argsvar svvar maskvar ;; 'tmp-argmasks
                                              ))
       (call `(,fn . ,acc-args))
       (full ;; (if (svex-apply-aig-uses-argmasks args)
             ;;     `(let ((tmp-argmasks (svex-argmasks ,maskvar ',sym ,svvar)))
             ;;        ,call)
               call))
    (cons `(,sym ,full)
          (svex-apply-aig-cases-fn argsvar svvar maskvar (cdr optable)))))

(defmacro svex-apply-aig-cases (fn args svex mask)
  `(case ,fn
     . ,(svex-apply-aig-cases-fn args svex mask *svex-aig-op-table*)))


(defthm svex-p-when-nth
  (implies (and (svexlist-p x)
                (nth n x))
           (svex-p (nth n x)))
  :hints(("Goal" :in-theory (enable nth svexlist-p))))

(defthm a4vec-p-when-nth
  (implies (and (a4veclist-p x)
                (nth n x))
           (a4vec-p (nth n x)))
  :hints(("Goal" :in-theory (enable nth svexlist-p))))

;; (defthm a4vec-eval-of-maybe-a4vec-fix-nth-out-of-bounds
;;   (implies (<= (len x) (nfix n))
;;            (equal (a4vec-eval (maybe-a4vec-fix (nth n x)) env)
;;                   (4vec-x)))
;;   :hints(("Goal" :in-theory (enable maybe-a4vec-fix nth))))


(local (in-theory (disable nth)))

(defthm len-of-a4veclist-eval
  (equal (len (a4veclist-eval x env))
         (len x))
  :hints(("Goal" :in-theory (enable a4veclist-eval))))








(define svex-apply-aig ((fn fnsym-p) (args a4veclist-p) (terms svexlist-p) (mask 4vmask-p))
  :prepwork ((local (Defthm 4veclist-nth-safe-of-a4veclist-eval
                      (equal (a4vec-eval (a4veclist-nth n x) aigenv)
                             (4veclist-nth-safe n (a4veclist-eval x aigenv)))
                      :hints(("Goal" :in-theory (enable a4veclist-eval a4veclist-nth 4veclist-nth-safe)))))
             (local (defun ind (n vals x)
                      (if (zp n)
                          (list vals x)
                        (ind (1- n) (cdr vals) (cdr x)))))
             (local (defthm 3vec-p-when-3valued-syntaxp-nth
                      (implies (and (EQUAL (A4VECLIST-EVAL VALS AIGENV)
                                           (SVEXLIST-EVAL X (SVEX-A4VEC-ENV-EVAL A4ENV AIGENV)))
                                    (3valued-syntaxp (svexlist-nth n x)))
                               (3vec-p (a4vec-eval (nth n vals) aigenv)))
                      :hints(("Goal" :in-theory (enable a4veclist-eval
                                                        svexlist-eval
                                                        svexlist-nth
                                                        nth)
                              :induct (ind n vals x)
                              :expand ((a4veclist-eval vals aigenv)
                                       (:free (env) (svexlist-eval x env))))
                             (and stable-under-simplificationp
                                  '(:use ((:instance 3vec-p-of-eval-when-3valued-syntaxp
                                           (x (car x))
                                           (env (svex-a4vec-env-eval a4env aigenv)))))))))
             (local (encapsulate nil
                      (local (defun ind2 (n masks vals x)
                               (if (zp n)
                                   (list masks vals x)
                                 (ind2 (1- n) (cdr masks) (cdr vals) (cdr x)))))

                      (defthm 4vmask-of-nths
                        (implies (equal (len masks) (len vecs))
                                 (equal (4vec-mask (4vmask-nth n masks)
                                                   (4veclist-nth-safe n vecs))
                                        (4veclist-nth-safe n (4veclist-mask masks vecs))))
                        :hints(("Goal" :in-theory (enable 4vmask-nth 4veclist-nth-safe 4veclist-mask nth
                                                          4vmasklist-fix)
                                :induct (ind2 n masks vecs nil))))

                      (defthm svex-eval-of-nth-rev
                        (equal (svex-eval (nth n x) env)
                               (4veclist-nth-safe n (svexlist-eval x env))))

                      (in-theory (disable svex-eval-of-nth
                                          4veclist-nth-safe-of-svexlist-eval))

                      (local (defthm 3vec-p-of-eval-by-equal
                               (implies (and (equal x (svex-eval y env))
                                             (3valued-syntaxp y))
                                        (3vec-p x))))

                      (local (defthm 3vec-p-of-eval-by-equal-with-mask
                               (implies (and (equal x (4vec-mask mask (svex-eval y env)))
                                             (3valued-syntaxp y))
                                        (3vec-p x))))

                      (defthm 4veclist-masked-idempotent
                        (implies (equal x (4veclist-mask masks y))
                                 (equal (4veclist-mask masks x) x)))


                      (defthm dumb
                        (implies (and (EQUAL (A4VECLIST-EVAL VALS AIGENV)
                                             (4VECLIST-MASK masks
                                                            (SVEXLIST-EVAL X (SVEX-A4VEC-ENV-EVAL A4ENV AIGENV))))
                                      (3valued-syntaxp (svexlist-nth n x)))
                                 (3vec-p (4veclist-nth-safe n (a4veclist-eval vals aigenv)))
                                 ;; (3vec-p (4vec-mask (4vmask-nth n masks)
                                 ;;                    (a4vec-eval (a4veclist-nth n vals) aigenv)))
                                 )
                        :hints (("goal" :in-theory (e/d (nth len 4veclist-nth-safe a4veclist-eval
                                                             4veclist-mask svexlist-eval
                                                             a4veclist-eval svexlist-nth)
                                                        (4veclist-nth-safe-of-a4veclist-eval))
                                 :expand ((:free (env) (svexlist-eval x env))
                                          (a4veclist-eval vals aigenv)
                                          (:free (a b) (4veclist-mask masks (cons a b))))
                                 :induct (ind2 n masks vals x))))
                      )))
  :verbosep t
  :guard-debug t
  :returns (res a4vec-p)
  (b* ((fn (fnsym-fix fn))
       (args (a4veclist-fix args))
       (res (svex-apply-aig-cases fn args terms mask)))
    (a4vec-mask mask res))
  ///

  (defthm svex-apply-aig-correct
    (implies (and (fnsym-p fn)
                  (bind-free '((a4env . env)) (a4env))
                  (equal (a4veclist-eval vals aigenv)
                         (4veclist-mask argmasks (svexlist-eval x (svex-a4vec-env-eval a4env aigenv))))
                  (svex-argmasks-okp (svex-call fn x) mask argmasks))
             (equal (a4vec-eval (svex-apply-aig fn vals x mask) aigenv)
                    (4vec-mask mask (svex-apply fn (svexlist-eval x (svex-a4vec-env-eval a4env aigenv))))))
    :hints(("Goal" :in-theory (disable len-of-4veclist-mask
                                       svex-apply-aig)
            ;; Establish that (len vals) = (len x).
            :use ((:instance len-of-4veclist-mask
                   (masks (svex-argmasks mask fn x))
                   (values (a4veclist-eval vals aigenv)))
                  (:instance len-of-4veclist-mask
                   (masks (svex-argmasks mask fn x))
                   (values (svexlist-eval x (svex-a4vec-env-eval a4env aigenv))))))
           (and stable-under-simplificationp
                '(
                  :in-theory (e/d (svex-apply svexlist-eval ;; 4veclist-nth-safe ;; 4veclist-mask
                                              4vec-bitnot
                                              4vec-bitand
                                              4vec-bitor
                                              4vec-bitxor-redef
                                              4vec-reduction-and
                                              4vec-reduction-or
                                              4vec-?
                                              4vec-bit?
                                              4vec-==)
                                  (;; len-of-svexlist-eval
                                   ;; len-of-a4veclist-eval
                                   ;; len-of-4veclist-mask
                                   svex-argmasks-correct
                                   svex-argmasks-remove-mask))
                  :use ;; ((:instance len-of-svexlist-eval
                  ;;   (env (svex-a4vec-env-eval a4env aigenv)))
                  ;;  (:instance len-of-a4veclist-eval
                  ;;   (x vals) (env aigenv)))
                  ((:instance svex-argmasks-okp-necc
                    (x (svex-call fn x))
                    (vals (a4veclist-eval vals aigenv))
                    (env (svex-a4vec-env-eval a4env aigenv)))
                   ;; (:instance svex-argmasks-remove-mask
                   ;;  (fn fn)
                   ;;  (args x)
                   ;;  (env (svex-a4vec-env-eval a4env aigenv)))
                   
                   
                   )
                  :do-not-induct t
                  :do-not '(fertilize generalize eliminate-destructors)
                  )))
    :otf-flg t))


(defalist svex-aig-memotable :key-type svex :val-type a4vec)

(defthm a4vec-p-of-svex-a4vec-env-lookup
  (implies (and (svex-a4vec-env-p x)
                (hons-assoc-equal k x))
           (a4vec-p (cdr (hons-assoc-equal k x)))))

(defthm a4vec-p-of-svex-aig-memotable-lookup
  (implies (and (svex-aig-memotable-p x)
                (hons-assoc-equal k x))
           (a4vec-p (cdr (hons-assoc-equal k x)))))

;; (SVEX->A4VEC
;;  '(RSH (? (< 0 (* 32 (B- (CONCAT 16 CNST 0) 0))) (* 32 (B- (CONCAT 16 CNST 0) 0)) 0) '(-71265535176078871931497435759850128999 . 269016831744859591531877171671918082457))
;;  (make-fast-alist `((cnst ,(acl2::numlist 0 2 16) . ,(acl2::numlist 1 2 16))))
;;  nil)


(defines svex->a4vec
  ;; Self-memoized version of svex-eval, for GL
  :verify-guards nil
  (define svex->a4vec ((x svex-p)
                       (env svex-a4vec-env-p)
                       (masks svex-mask-alist-p)
                       (memo svex-aig-memotable-p))
    :returns (mv (res a4vec-p)
                 (memo1 svex-aig-memotable-p))
    :measure (svex-count x)
    (b* ((memo (svex-aig-memotable-fix memo))
         (env (svex-a4vec-env-fix env)))
      (svex-case x
        :quote (b* ((mask (svex-mask-lookup x masks)))
                 (mv (4vec->a4vec (4vec-mask mask x.val)) memo))
        :var (mv (let ((look (hons-get x.name env))
                       (mask (svex-mask-lookup x masks)))
                   (a4vec-mask mask (if look (cdr look) (a4vec-x))))
                 memo)
        :call (b* ((x (svex-fix x))
                   (look (hons-get x memo))
                   ((when look) (mv (cdr look) memo))
                   ((mv args memo) (svexlist->a4vec x.args env masks memo))
                   (mask (svex-mask-lookup x masks))
                   (res (svex-apply-aig x.fn args x.args mask))
                   (memo (hons-acons x res memo)))
                (mv res memo)))))
  (define svexlist->a4vec ((x svexlist-p)
                           (env svex-a4vec-env-p)
                           (masks svex-mask-alist-p)
                           (memo svex-aig-memotable-p))
    :returns (mv (res a4veclist-p)
                 (memo1 svex-aig-memotable-p))
    :measure (svexlist-count x)
    (b* (((when (atom x)) (mv nil (svex-aig-memotable-fix memo)))
         ((mv first memo) (svex->a4vec (car x) env masks memo))
         ((mv rest memo) (svexlist->a4vec (cdr x) env masks memo)))
      (mv (cons first rest) memo)))
  ///
  (verify-guards svex->a4vec)

  (defun-sk svex->a4vec-table-ok (memo env masks aigenv)
    (forall x
            (let* ((memo (svex-aig-memotable-fix memo))
                   (mask (svex-mask-lookup x masks)))
              (implies (hons-assoc-equal (svex-fix x) memo)
                       (equal (a4vec-eval (cdr (hons-assoc-equal (svex-fix x) memo)) aigenv)
                              (4vec-mask mask (svex-eval x (svex-a4vec-env-eval env aigenv)))))))
    :rewrite :direct)

  (in-theory (disable svex->a4vec-table-ok
                      svex->a4vec-table-ok-necc))
  (local (in-theory (enable svex->a4vec-table-ok-necc)))

  ;; (defthm svex->a4vec-table-ok-necc-rw2
  ;;   (implies (svex->a4vec-table-ok memo env masks aigenv)
  ;;            (let* ((memo (svex-aig-memotable-fix memo))
  ;;                   (mask (svex-mask-lookup x masks)))
  ;;              (implies (and (svex-p x)
  ;;                            (hons-assoc-equal x memo))
  ;;                       (equal (a4vec-eval (cdr (hons-assoc-equal x memo)) aigenv)
  ;;                              (4vec-mask mask (svex-eval x (svex-a4vec-env-eval env aigenv)))))))
  ;;   :hints (("goal" :use svex->a4vec-table-ok-necc
  ;;            :in-theory (disable svex->a4vec-table-ok-necc))))

  (defthm svex->a4vec-table-ok-empty
    (svex->a4vec-table-ok nil env masks aigenv)
    :hints(("Goal" :in-theory (enable svex->a4vec-table-ok))))

  (defthm svex->a4vec-table-ok-extend
    (implies (and (svex->a4vec-table-ok memo env masks aigenv)
                  (equal (a4vec-eval val aigenv)
                         (4vec-mask (svex-mask-lookup x masks)
                                    (svex-eval x (svex-a4vec-env-eval env aigenv)))))
             (svex->a4vec-table-ok
              (cons (cons x val) memo) env masks aigenv))
    :hints (("goal" :expand ((svex->a4vec-table-ok
                              (cons (cons x val) memo) env masks aigenv)))))

  (defthm svex->a4vec-table-ok-memotable-fix
    (iff (svex->a4vec-table-ok (svex-aig-memotable-fix memo) env masks aigenv)
         (svex->a4vec-table-ok memo env masks aigenv))
    :hints ((and stable-under-simplificationp
                 (if (eq (caar clause) 'not)
                     `(:expand (,(car (last clause)))
                       :in-theory (disable svex->a4vec-table-ok-necc)
                       :use ((:instance svex->a4vec-table-ok-necc
                              (x (svex->a4vec-table-ok-witness memo env masks aigenv))
                              (memo (svex-aig-memotable-fix memo)))))
                   `(:expand (,(car clause))
                     :in-theory (disable svex->a4vec-table-ok-necc)
                     :use ((:instance svex->a4vec-table-ok-necc
                            (x (svex->a4vec-table-ok-witness
                                (svex-aig-memotable-fix memo) env masks aigenv)))))))))

  (defthm svex->a4vec-table-ok-env-fix
    (iff (svex->a4vec-table-ok memo (svex-a4vec-env-fix env) masks aigenv)
         (svex->a4vec-table-ok memo env masks aigenv))
    :hints ((and stable-under-simplificationp
                 (if (eq (caar clause) 'not)
                     `(:expand (,(car (last clause)))
                       :in-theory (disable svex->a4vec-table-ok-necc)
                       :use ((:instance svex->a4vec-table-ok-necc
                              (x (svex->a4vec-table-ok-witness memo env masks aigenv))
                              (env (svex-a4vec-env-fix env)))))
                   `(:expand (,(car clause))
                     :in-theory (disable svex->a4vec-table-ok-necc)
                     :use ((:instance svex->a4vec-table-ok-necc
                            (x (svex->a4vec-table-ok-witness
                                memo (svex-a4vec-env-fix env) masks aigenv)))))))))

  (local (in-theory (disable svex->a4vec svexlist->a4vec)))

  (encapsulate nil
    (local (defthm lookup-in-svex-a4vec-env-eval-lemma
             (implies (svex-a4vec-env-p env)
                      (equal (hons-assoc-equal k (svex-a4vec-env-eval env aigenv))
                             (and (hons-assoc-equal k env)
                                  (cons k (a4vec-eval (cdr (hons-assoc-equal k env))
                                                      aigenv)))))
             :hints(("Goal" :in-theory (enable svex-a4vec-env-eval
                                               svex-a4vec-env-p)
                     :induct (svex-a4vec-env-eval env aigenv)
                     :do-not-induct t))
             :rule-classes nil))

    (defthm lookup-in-svex-a4vec-env-eval
      (equal (hons-assoc-equal k (svex-a4vec-env-eval env aigenv))
             (and (hons-assoc-equal k (svex-a4vec-env-fix env))
                  (cons k (a4vec-eval (cdr (hons-assoc-equal k (svex-a4vec-env-fix env)))
                                      aigenv))))
      :hints(("Goal" :use ((:instance lookup-in-svex-a4vec-env-eval-lemma
                            (env (svex-a4vec-env-fix env))))))))

  (defthm svex-env-lookup-in-svex-a4vec-env-eval
    (equal (svex-env-lookup k (svex-a4vec-env-eval env aigenv))
           (if (hons-assoc-equal (svar-fix k) (svex-a4vec-env-fix env))
               (a4vec-eval (cdr (hons-assoc-equal (svar-fix k) (svex-a4vec-env-fix env)))
                                      aigenv)
             (4vec-x)))
    :hints(("Goal" :in-theory (enable svex-env-lookup))))

   ;; (local (defthm svex-apply-aig-correct-rw
   ;;        (implies (and (fnsym-p fn)
   ;;                (bind-free '((a4env . env)) (a4env))
   ;;                (equal (a4veclist-eval vals aigenv)
   ;;                       (4veclist-mask argmasks (svexlist-eval x (svex-a4vec-env-eval a4env aigenv))))
   ;;                (svex-argmasks-okp (svex-call fn x) mask argmasks))
   ;;           (equal (a4vec-eval (svex-apply-aig fn vals x mask) aigenv)
   ;;                  (4vec-mask mask (svex-apply fn (svexlist-eval x (svex-a4vec-env-eval a4env aigenv))))))


  (local (in-theory (enable svex-mask-alist-complete-necc)))

  (defthm-svex->a4vec-flag
    (defthm svex->a4vec-correct
      (b* (((mv res memo1) (svex->a4vec x env masks memo)))
        (implies (and (svex->a4vec-table-ok memo env masks aigenv)
                      (svex-mask-alist-complete masks))
                 (and (svex->a4vec-table-ok memo1 env masks aigenv)
                      (equal (a4vec-eval res aigenv)
                             (4vec-mask (svex-mask-lookup x masks)
                                        (svex-eval x (svex-a4vec-env-eval env aigenv)))))))
      :hints ('(:expand ((svex->a4vec x env masks memo)
                         (:free (env) (svex-eval x env)))))
      :flag svex->a4vec)
    (defthm svexlist->a4vec-correct
      (b* (((mv res memo1) (svexlist->a4vec x env masks memo)))
        (implies (and (svex->a4vec-table-ok memo env masks aigenv)
                      (svex-mask-alist-complete masks))
                 (and (svex->a4vec-table-ok memo1 env masks aigenv)
                      (equal (a4veclist-eval res aigenv)
                             (4veclist-mask (svex-argmasks-lookup x masks)
                                            (svexlist-eval x (svex-a4vec-env-eval env aigenv)))))))
      :hints ('(:expand ((svexlist->a4vec x env masks memo)
                         (:free (env) (svexlist-eval x env))
                         (a4veclist-eval nil aigenv)
                         (svex-argmasks-lookup x masks)
                         (:free (a b) (a4veclist-eval (cons a b) aigenv)))
                :in-theory (enable 4veclist-mask)))
      :flag svexlist->a4vec))

  (deffixequiv-mutual svex->a4vec
    :hints (("goal" :expand ((:free (env masks memo) (svexlist->a4vec x env masks memo))
                             (:free (env masks memo)
                              (svexlist->a4vec (svexlist-fix x) env masks memo))
                             (:free (env masks memo) (svex->a4vec x env masks memo))
                             (:free (env masks memo)
                              (svex->a4vec (svex-fix x) env masks memo)))))))

(define svex->a4vec-top ((x svex-p) (env svex-a4vec-env-p) (masks svex-mask-alist-p))
  :returns (res a4vec-p)
  (b* (((mv res memo)
        (svex->a4vec x (make-fast-alist env) masks nil)))
    (fast-alist-free memo)
    res)
  ///
  (defthm svex->a4vec-top-correct
    (implies (svex-mask-alist-complete masks)
             (equal (a4vec-eval (svex->a4vec-top x env masks) aigenv)
                    (4vec-mask (svex-mask-lookup x masks)
                               (svex-eval x (svex-a4vec-env-eval env aigenv)))))))


(define svexlist->a4vec-top ((x svexlist-p) (env svex-a4vec-env-p) (masks svex-mask-alist-p))
  ;; note: env must be fast
  :returns (res a4veclist-p)
  (b* (((mv res memo)
        (svexlist->a4vec x env masks nil)))
    (fast-alist-free memo)
    res)
  ///
  (defthm svexlist->a4vec-top-correct
    (implies (svex-mask-alist-complete masks)
             (equal (a4veclist-eval (svexlist->a4vec-top x env masks) aigenv)
                    (4veclist-mask (svex-argmasks-lookup x masks)
                                   (svexlist-eval x (svex-a4vec-env-eval env aigenv)))))))


;; There are a few possible approaches to generating the a4vec-env to use in
;; building AIGs.  Basically, we're going to generate a pair of Boolean
;; variables for each bit that matters (mask-wise) in x; the masks for the
;; variables of x must be finite so that we can determine which bits matter.
;; (The don't-care bits will be assigned X.)
;; But there are still a few options:

;; 1. Always assign AIG variables to every care bit of every variable.  This
;; has the advantage that the input and output to svexlist->a4vec is always
;; identical for a given svexlist, so we can memoize, which may improve
;; performance if we run several simulations with the same svex but different
;; environments.  But the complete set of variables might be overkill,
;; e.g. svtvs have lots of variables for don't-care inputs and initial
;; states.

;; 2. Assign AIG variables to the care bits of all the variables bound in the
;; environment.  This could still allow good memoization as long as the same
;; variables are going to be assigned basically all the time.  We can extract
;; and sort the variables so that the order of the bindings doesn't matter.

;; 3. In between 1 and 2: Take a list of variables as an extra argument,
;; ignored in the logic, which should be a superset of the variables in the
;; environment; only generate AIG vars for these variables.  This care list
;; could be provided e.g. by the SVTV.  This has the advantage over 2 that
;; memoization still works if different subsets of the care variables are
;; used in different runs.

;; The implementations of 1,2,3 would be quite similar and could basically
;; all be based on 3.

;; 4. More extreme than 2, more difficult to implement, and little chance of
;; memoization working: in the symbolic environment provided, we only really
;; need AIG variables for non-constant bits.  So ignore masks and just
;; produce an a4vec environment that replicates the constants assigned in env
;; and generates AIG variables for the non-constant bits.  This would mean
;; we'd need to get a hold of the symbolic environment, which probably would
;; mean we'd need a symbolic counterpart function, not just an alternate
;; definition.


;; The following implements option 3 above.  We provide the svexlist and the
;; list of care vars.  The function returns the a4veclist and the a4vec-env.

(define nat-bool-listp (x)
  (if (atom x)
      (eq x nil)
    (and (or (natp (car x))
             (booleanp (car x)))
         (nat-bool-listp (cdr x))))
  ///
  (defthm nat-bool-listp-of-aig-sterm
    (implies (or (booleanp x) (natp x))
             (nat-bool-listp (aig-sterm x)))
    :hints(("Goal" :in-theory (enable gl::bfr-sterm))))

  (defthm nat-bool-listp-of-aig-scons
    (implies (and (or (booleanp x) (natp x))
                  (nat-bool-listp y))
             (nat-bool-listp (aig-scons x y)))
    :hints(("Goal" :in-theory (enable gl::bfr-scons)))))

(define nat-bool-list-nats ((x nat-bool-listp))
  :prepwork ((local (in-theory (enable nat-bool-listp))))
  (if (atom x)
      nil
    (if (booleanp (car x))
        (nat-bool-list-nats (cdr x))
      (cons (lnfix (car x))
            (nat-bool-list-nats (cdr x)))))
  ///
  (defthm nat-bool-list-nats-of-aig-sterm
    (equal (nat-bool-list-nats (aig-sterm x))
           (if (booleanp x)
               nil
             (list (nfix x))))
    :hints(("Goal" :in-theory (enable gl::bfr-sterm))))

  (defthm nat-bool-list-nats-of-aig-scons-bool
    (implies (booleanp x)
             (equal (nat-bool-list-nats (aig-scons x y))
                    (nat-bool-list-nats y)))
    :hints(("Goal" :in-theory (enable gl::bfr-scons))))

  (defthm nat-bool-list-nats-of-aig-scons-nat
    (implies (and (natp x)
                  (not (member x (nat-bool-list-nats y))))
             (equal (nat-bool-list-nats (aig-scons x y))
                    (cons x (nat-bool-list-nats y))))
    :hints(("Goal" :in-theory (enable gl::bfr-scons)))))

(define nat-bool-list-lower-boundp ((bound natp) (x nat-bool-listp))
  :prepwork ((local (in-theory (enable nat-bool-listp))))
  (if (atom x)
      t
    (and (or (booleanp (car x))
             (<= (lnfix bound) (lnfix (car x))))
         (nat-bool-list-lower-boundp bound (cdr x))))
  ///
  (defthm nat-bool-list-nonmember-by-lower-bound
    (implies (and (nat-bool-list-lower-boundp bound x)
                  (< v (nfix bound))
                  (nat-bool-listp x))
             (not (member v (nat-bool-list-nats x))))
    :hints(("Goal" :in-theory (enable nat-bool-list-nats))))

  (Defthm nat-bool-list-lower-boundp-lower
    (implies (and (nat-bool-list-lower-boundp bound x)
                  (<= (nfix n) (nfix bound)))
             (nat-bool-list-lower-boundp n x))))

(define nat-bool-list-upper-boundp ((bound natp) (x nat-bool-listp))
  :prepwork ((local (in-theory (enable nat-bool-listp))))
  (if (atom x)
      t
    (and (or (booleanp (car x))
             (< (lnfix (car x)) (lnfix bound)))
         (nat-bool-list-upper-boundp bound (cdr x))))
  ///
  (defthm nat-bool-list-nonmember-by-upper-bound
    (implies (and (nat-bool-list-upper-boundp bound x)
                  (<= (nfix bound) v)
                  (nat-bool-listp x))
             (not (member v (nat-bool-list-nats x))))
    :hints(("Goal" :in-theory (enable nat-bool-list-nats))))

  (defthm nat-bool-list-no-intersection-by-bounds
    (implies (and (nat-bool-list-upper-boundp bound0 x0)
                  (nat-bool-list-lower-boundp bound1 x1)
                  (<= (nfix bound0) (nfix bound1))
                  (nat-bool-listp x0)
                  (nat-bool-listp x1))
             (not (intersectp (nat-bool-list-nats x0)
                              (nat-bool-list-nats x1))))
    :hints(("Goal" :in-theory (e/d (intersectp-equal
                                    nat-bool-listp
                                    nat-bool-list-nats)
                                   (acl2::intersectp-equal-commute)))))

  (Defthm nat-bool-list-upper-boundp-higher
    (implies (and (nat-bool-list-upper-boundp bound x)
                  (<= (nfix bound) (nfix n)))
             (nat-bool-list-upper-boundp n x))))


(define nat-bool-a4vec-p ((x a4vec-p))
  (b* (((a4vec x) x))
    (and (nat-bool-listp x.upper)
         (nat-bool-listp x.lower)))
  ///
  (deffixtype nba4vec :pred nat-bool-a4vec-p! :fix a4vec-fix :equiv a4vec-equiv))

(defmacro nat-bool-a4vec-p! (x)
  `(and (a4vec-p ,x)
        (nat-bool-a4vec-p ,x)))

(define nat-bool-a4vec-vars ((x nat-bool-a4vec-p!))
  :prepwork ((local (in-theory (enable nat-bool-a4vec-p))))
  (b* (((a4vec x) x))
    (append (nat-bool-list-nats x.upper)
            (nat-bool-list-nats x.lower))))

(define nat-bool-a4vec-lower-boundp ((bound natp) (x nat-bool-a4vec-p!))
  :prepwork ((local (in-theory (enable nat-bool-a4vec-p))))
  (b* (((a4vec x) x))
    (and (nat-bool-list-lower-boundp bound x.upper)
         (nat-bool-list-lower-boundp bound x.lower)))
  ///
  (defthm nat-bool-a4vec-vars-nonmember-by-lower-bound
    (implies (and (nat-bool-a4vec-lower-boundp bound x)
                  (< v (nfix bound))
                  (nat-bool-a4vec-p x))
             (not (member v (nat-bool-a4vec-vars x))))
    :hints(("Goal" :in-theory (enable nat-bool-a4vec-vars
                                      nat-bool-a4vec-p
                                      nat-bool-list-nonmember-by-lower-bound))))

  (Defthm nat-bool-a4vec-lower-boundp-lower
    (implies (and (nat-bool-a4vec-lower-boundp bound x)
                  (<= (nfix n) (nfix bound)))
             (nat-bool-a4vec-lower-boundp n x))))

(define nat-bool-a4vec-upper-boundp ((bound natp) (x nat-bool-a4vec-p!))
  :prepwork ((local (in-theory (enable nat-bool-a4vec-p))))
  (b* (((a4vec x) x))
    (and (nat-bool-list-upper-boundp bound x.upper)
         (nat-bool-list-upper-boundp bound x.lower)))
  ///
  (defthm nat-bool-a4vec-vars-nonmember-by-upper-bound
    (implies (and (nat-bool-a4vec-upper-boundp bound x)
                  (<= (nfix bound) v)
                  (nat-bool-a4vec-p x))
             (not (member v (nat-bool-a4vec-vars x))))
    :hints(("Goal" :in-theory (enable nat-bool-a4vec-vars
                                      nat-bool-a4vec-p
                                      nat-bool-list-nonmember-by-upper-bound))))

  (defthm nat-bool-a4vec-no-intersection-by-bounds
    (implies (and (nat-bool-a4vec-upper-boundp bound0 x0)
                  (nat-bool-a4vec-lower-boundp bound1 x1)
                  (<= (nfix bound0) (nfix bound1))
                  (nat-bool-a4vec-p x0)
                  (nat-bool-a4vec-p x1))
             (not (intersectp (nat-bool-a4vec-vars x0)
                              (nat-bool-a4vec-vars x1))))
    :hints(("Goal" :in-theory (e/d (intersectp-equal
                                    nat-bool-a4vec-p
                                    nat-bool-a4vec-vars
                                    nat-bool-a4vec-upper-boundp
                                    nat-bool-a4vec-lower-boundp)
                                   (acl2::intersectp-equal-commute)))))

  (Defthm nat-bool-a4vec-upper-boundp-higher
    (implies (and (nat-bool-a4vec-upper-boundp bound x)
                  (<= (nfix bound) (nfix n)))
             (nat-bool-a4vec-upper-boundp n x))))


(define nat-bool-a4env-p ((x svex-a4vec-env-p))
  :prepwork ((local (in-theory (enable svex-a4vec-env-fix))))
  (if (atom x)
      t
    (and (if (mbt (consp (car x)))
             (nat-bool-a4vec-p (cdar x))
           t)
         (nat-bool-a4env-p (cdr x))))
  ///
  (deffixtype nba4env :pred nat-bool-a4env-p! :fix svex-a4vec-env-fix :equiv svex-a4vec-env-equiv))

(defmacro nat-bool-a4env-p! (x)
  `(and (svex-a4vec-env-p ,x)
        (nat-bool-a4env-p ,x)))

(define nat-bool-a4env-vars ((x nat-bool-a4env-p!))
  :prepwork ((local (in-theory (enable nat-bool-a4env-p
                                       svex-a4vec-env-fix))))
  (if (atom x)
      nil
    (append (and (mbt (consp (car x)))
                 (nat-bool-a4vec-vars (cdar x)))
            (nat-bool-a4env-vars (cdr x)))))

(define nat-bool-a4env-lower-boundp ((bound natp) (x nat-bool-a4env-p!))
  :prepwork ((local (in-theory (enable nat-bool-a4env-p
                                       svex-a4vec-env-fix))))
  (if (atom x)
      t
    (and (if (mbt (consp (car x)))
             (nat-bool-a4vec-lower-boundp bound (cdar x))
           t)
         (nat-bool-a4env-lower-boundp bound (cdr x))))
  ///
  (defthm nat-bool-a4env-vars-nonmember-by-lower-bound
    (implies (and (nat-bool-a4env-lower-boundp bound x)
                  (< v (nfix bound))
                  (nat-bool-a4env-p x))
             (not (member v (nat-bool-a4env-vars x))))
    :hints(("Goal" :in-theory (enable nat-bool-a4env-vars
                                      nat-bool-a4env-p
                                      nat-bool-list-nonmember-by-lower-bound))))

  (Defthm nat-bool-a4env-lower-boundp-lower
    (implies (and (nat-bool-a4env-lower-boundp bound x)
                  (<= (nfix n) (nfix bound)))
             (nat-bool-a4env-lower-boundp n x))))

(define nat-bool-a4env-upper-boundp ((bound natp) (x nat-bool-a4env-p!))
  :prepwork ((local (in-theory (enable nat-bool-a4env-p
                                       svex-a4vec-env-fix))))
  (if (atom x)
      t
    (and (if (mbt (consp (car x)))
             (nat-bool-a4vec-upper-boundp bound (cdar x))
           t)
         (nat-bool-a4env-upper-boundp bound (cdr x))))
  ///
  (defthm nat-bool-a4env-vars-nonmember-by-upper-bound
    (implies (and (nat-bool-a4env-upper-boundp bound x)
                  (<= (nfix bound) v)
                  (nat-bool-a4env-p x))
             (not (member v (nat-bool-a4env-vars x))))
    :hints(("Goal" :in-theory (enable nat-bool-a4env-vars
                                      nat-bool-a4env-p
                                      nat-bool-list-nonmember-by-upper-bound))))

  (defthm nat-bool-a4vec/env-no-intersection-by-bounds
    (implies (and (nat-bool-a4vec-upper-boundp bound0 x0)
                  (nat-bool-a4env-lower-boundp bound1 x1)
                  (<= (nfix bound0) (nfix bound1))
                  (nat-bool-a4vec-p x0)
                  (nat-bool-a4env-p x1))
             (not (intersectp (nat-bool-a4vec-vars x0)
                              (nat-bool-a4env-vars x1))))
    :hints(("Goal" :in-theory (e/d (intersectp-equal
                                    nat-bool-a4env-p
                                    nat-bool-a4env-lower-boundp)
                                   (acl2::intersectp-equal-commute))
            :expand ((nat-bool-a4env-vars x1))
            :induct (nat-bool-a4env-lower-boundp bound1 x1))))

  (defthm nat-bool-a4env-no-intersection-by-bounds
    (implies (and (nat-bool-a4env-upper-boundp bound0 x0)
                  (nat-bool-a4env-lower-boundp bound1 x1)
                  (<= (nfix bound0) (nfix bound1))
                  (nat-bool-a4env-p x0)
                  (nat-bool-a4env-p x1))
             (not (intersectp (nat-bool-a4env-vars x0)
                              (nat-bool-a4env-vars x1))))
    :hints(("Goal" :in-theory (e/d (intersectp-equal
                                    nat-bool-a4env-p
                                    nat-bool-a4env-vars
                                    nat-bool-a4env-upper-boundp
                                    nat-bool-a4env-lower-boundp)
                                   (acl2::intersectp-equal-commute)))))

  (defthm nat-bool-a4env-a4vec-no-intersection-by-bounds
    (implies (and (nat-bool-a4env-upper-boundp bound0 x0)
                  (nat-bool-a4vec-lower-boundp bound1 x1)
                  (<= (nfix bound0) (nfix bound1))
                  (nat-bool-a4env-p x0)
                  (nat-bool-a4vec-p x1))
             (not (intersectp (nat-bool-a4env-vars x0)
                              (nat-bool-a4vec-vars x1))))
    :hints(("Goal" :in-theory (e/d (intersectp-equal
                                    nat-bool-a4env-p
                                    nat-bool-a4env-vars
                                    nat-bool-a4env-upper-boundp
                                    nat-bool-a4env-lower-boundp)
                                   (acl2::intersectp-equal-commute)))))

  (Defthm nat-bool-a4env-upper-boundp-higher
    (implies (and (nat-bool-a4env-upper-boundp bound x)
                  (<= (nfix bound) (nfix n)))
             (nat-bool-a4env-upper-boundp n x))))




(local (defthm logcount-of-logand
         (implies (natp y)
                  (<= (logcount (logand x y))
                      (logcount y)))
         :hints(("Goal" :in-theory (e/d* (bitops::logcount**
                                          bitops::logand**
                                          bitops::ihsext-inductions))))
         :rule-classes :linear))

(define 4vmask-to-a4vec-varcount ((mask natp) (boolmask integerp))
  :returns (count natp :rule-classes :type-prescription)
  (b* ((mask (lnfix mask)))
    (- (* 2 (logcount mask))
       (logcount (logand mask (lifix boolmask))))))

(define 4vmask-to-a4vec-rec ((mask natp) (boolmask integerp) (nextvar natp))
  :returns (mv (upper nat-bool-listp)
               (lower nat-bool-listp))
  :measure (integer-length mask)
  :hints(("Goal" :in-theory (enable bitops::integer-length**
                                    4vmask-fix)))
  (b* ((mask (lnfix mask))
       (nextvar (lnfix nextvar))
       ((when (eql mask 0))
        (mv (aig-sterm t) (aig-sterm nil)))
       ((mv ubit0 ubit1 nextvar)
        (if (logbitp 0 mask)
            (if (logbitp 0 boolmask)
                (mv nextvar nextvar (+ 1 nextvar))
              (mv nextvar (1+ nextvar) (+ 2 nextvar)))
          (mv t nil nextvar)))
       ((mv rest-upper rest-lower)
        (4vmask-to-a4vec-rec (logcdr mask) (logcdr boolmask) nextvar)))
    (mv (aig-scons ubit0 rest-upper)
        (aig-scons ubit1 rest-lower)))
  ///
  ;; (defthm 4vmask-to-a4vec-rec-nextvar
  ;;   (equal (mv-nth 2 (4vmask-to-a4vec-rec mask nextvar))
  ;;          (+ (* 2 (logcount (nfix mask))) (nfix nextvar)))
  ;;   :hints(("Goal" :in-theory (enable bitops::logcount**))))

  (defthm 4vmask-to-a4vec-rec-lower-bounds
    (and (nat-bool-list-lower-boundp nextvar (mv-nth 0 (4vmask-to-a4vec-rec mask boolmask nextvar)))
         (nat-bool-list-lower-boundp nextvar (mv-nth 1 (4vmask-to-a4vec-rec mask boolmask nextvar))))
    :hints(("Goal" :in-theory (enable nat-bool-list-lower-boundp gl::bfr-scons)))
    :rule-classes ((:forward-chaining :trigger-terms ((4vmask-to-a4vec-rec mask boolmask nextvar)))))

  (defthm 4vmask-to-a4vec-rec-upper-bounds
    (and (nat-bool-list-upper-boundp (+ (nfix nextvar)
                                        (4vmask-to-a4vec-varcount mask boolmask))
                                     (mv-nth 0 (4vmask-to-a4vec-rec mask boolmask nextvar)))
         (nat-bool-list-upper-boundp (+ (nfix nextvar)
                                        (4vmask-to-a4vec-varcount mask boolmask))
                                     (mv-nth 1 (4vmask-to-a4vec-rec mask boolmask nextvar))))
    :hints(("Goal" :in-theory (enable gl::bfr-scons
                                      4vmask-to-a4vec-varcount
                                      bitops::logand**
                                      bitops::logbitp**
                                      bitops::logcount**)
            :induct (4vmask-to-a4vec-rec mask boolmask nextvar)
            :expand ((:free (bound a b) (nat-bool-list-upper-boundp bound (cons a b)))
                     (:free (bound) (nat-bool-list-upper-boundp bound nil)))
            :do-not-induct t))
    :rule-classes ((:forward-chaining :trigger-terms ((4vmask-to-a4vec-rec mask boolmask nextvar)))))

  ;; (defthm 4vmask-to-a4vec-rec-no-duplicate-vars
  ;;   (b* (((mv upper lower)
  ;;         (4vmask-to-a4vec-rec mask boolmask nextvar)))
  ;;     (and (no-duplicatesp (nat-bool-list-nats upper))
  ;;          (no-duplicatesp (nat-bool-list-nats lower))
  ;;          (not (intersectp (nat-bool-list-nats upper)
  ;;                           (nat-bool-list-nats lower)))))
  ;;   :hints(("Goal" :in-theory (enable nat-bool-list-nats
  ;;                                     intersectp-equal))))

  (defthm member-4vmask-to-a4vec-rec-vars
    ;; not a good rewrite rule but useful for the next phase
    (iff (member v (append (nat-bool-list-nats (mv-nth 0 (4vmask-to-a4vec-rec mask boolmask nextvar)))
                           (nat-bool-list-nats (mv-nth 1 (4vmask-to-a4vec-rec mask boolmask nextvar)))))
         (and (natp v)
              (<= (nfix nextvar) v)
              (< v (+ (nfix nextvar)
                      (4vmask-to-a4vec-varcount mask boolmask)))))
    :hints(("Goal" :in-theory (enable nat-bool-list-nats
                                      4vmask-to-a4vec-varcount
                                      bitops::logand**
                                      bitops::logcount**
                                      bitops::logbitp**)))
    :rule-classes nil))

  ;; (defthm eval-4vmask-to-a4vec-rec-cons-greater
  ;;   (b* (((mv ?err upper lower nextvar1)
  ;;         (4vmask-to-a4vec-rec mask nextvar)))
  ;;     (implies (<= nextvar1 var)
  ;;              (and (equal (aig-list->s upper (cons (cons var val) env))
  ;;                          (aig-list->s upper env))
  ;;                   (equal (aig-list->s lower (cons (cons var val) env))
  ;;                          (aig-list->s lower env))))))

  ;; (defthm eval-4vmask-to-a4vec-rec-cons-lesser
  ;;   (b* (((mv ?err upper lower ?nextvar1)
  ;;         (4vmask-to-a4vec-rec mask nextvar)))
  ;;     (implies (< var (nfix nextvar))
  ;;              (and (equal (aig-list->s upper (cons (cons var val) env))
  ;;                          (aig-list->s upper env))
  ;;                   (equal (aig-list->s lower (cons (cons var val) env))
  ;;                          (aig-list->s lower env)))))))

(define 4vmask-to-a4vec-rec-env ((mask natp)
                                 (boolmask integerp)
                                 (upper integerp)
                                 (lower integerp)
                                 (nextvar natp))
  :returns (env "environment for the resulting 4vmask")
  :measure (integer-length mask)
  :hints(("Goal" :in-theory (enable bitops::integer-length**
                                    4vmask-fix)))
  (b* ((mask (lnfix mask))
       (nextvar (lnfix nextvar))
       ((when (eql mask 0)) nil)
       (rest-env
        (4vmask-to-a4vec-rec-env (logcdr mask)
                                 (logcdr boolmask)
                                 (logcdr upper)
                                 (logcdr lower)
                                 (if (logbitp 0 mask)
                                     (if (logbitp 0 boolmask)
                                         (+ 1 nextvar)
                                       (+ 2 nextvar))
                                   nextvar))))
    (if (logbitp 0 mask)
        (cons (cons nextvar (logbitp 0 upper))
              (if (logbitp 0 boolmask)
                  rest-env
                (cons (cons (1+ nextvar) (logbitp 0 lower))
                      rest-env)))
      rest-env))
  ///

  (defthm key-exists-in-4vmask-to-a4vec-rec-env
    (iff (hons-assoc-equal v (4vmask-to-a4vec-rec-env mask boolmask upper lower nextvar))
         (and (natp v)
              (<= (nfix nextvar) v)
              (< v (+ (nfix nextvar)
                      (4vmask-to-a4vec-varcount mask boolmask)))))
    :hints(("Goal" :in-theory (enable bitops::logcount**
                                      bitops::logbitp**
                                      4vmask-to-a4vec-varcount
                                      bitops::logand**)
            :do-not-induct t
            :induct (4vmask-to-a4vec-rec-env mask boolmask upper lower nextvar))))

  (defthm nat-bool-aig-list->s-of-cons-nonmember
    (implies (and (nat-bool-listp x)
                  (not (member n (nat-bool-list-nats x))))
             (equal (aig-list->s x (cons (cons n v) env))
                    (aig-list->s x env)))
    :hints(("Goal" :in-theory (enable aig-list->s nat-bool-listp
                                      nat-bool-list-nats
                                      gl::scdr
                                      gl::s-endp))))

  (local (defthm equal-nfix-plus-1
           (not (equal x (+ 1 (nfix x))))
           :hints(("Goal" :in-theory (enable nfix)))))

  (defthm eval-4vmask-to-a4vec-rec-with-env
    (b* (((mv uppera lowera)
          (4vmask-to-a4vec-rec mask boolmask nextvar))
         (env
          (4vmask-to-a4vec-rec-env mask boolmask upper lower nextvar)))
      (and (equal (logand (nfix mask) (aig-list->s uppera env))
                  (logand (nfix mask) upper))
           (implies (eql 0 (logand boolmask (logxor upper lower)))
                    (equal (logand (nfix mask) (aig-list->s lowera env))
                           (logand (nfix mask) lower)))))
    :hints(("Goal" :in-theory (enable 4vmask-to-a4vec-rec
                                      bitops::logand**
                                      bitops::logxor**
                                      bitops::logbitp**
                                      4vmask-fix)
            :induct (4vmask-to-a4vec-rec-env mask boolmask upper lower nextvar))
           (and stable-under-simplificationp
                '(:in-theory (enable bitops::b-xor))))))

(define 4vec-boolmaskp ((x 4vec-p) (mask integerp))
  (b* (((4vec x) x))
    (eql 0 (logand mask (logxor x.upper x.lower)))))

(define 4vmask-to-a4vec ((mask natp) (boolmask integerp) (nextvar natp))
  :returns (res nat-bool-a4vec-p!
                :hints(("Goal" :in-theory (enable nat-bool-a4vec-p))))
  :prepwork ((local (defthm true-listp-when-nat-bool-listp
                      (implies (nat-bool-listp x)
                               (true-listp x))
                      :hints(("Goal" :in-theory (enable nat-bool-listp))))))
  (b* (((mv upper lower)
        (4vmask-to-a4vec-rec mask boolmask nextvar)))
    (a4vec upper lower))
  ///
  ;; (defthm 4vmask-to-a4vec-nextvar
  ;;   (equal (mv-nth 1 (4vmask-to-a4vec mask nextvar))
  ;;          (+ (* 2 (logcount (nfix mask))) (nfix nextvar))))

  (defthm member-vars-of-4vmask-to-a4vec
    (iff (member v (nat-bool-a4vec-vars (4vmask-to-a4vec mask boolmask nextvar)))
         (and (natp v)
              (<= (nfix nextvar) v)
              (< v (+ (nfix nextvar) (4vmask-to-a4vec-varcount mask boolmask)))))
    :hints (("goal" :use member-4vmask-to-a4vec-rec-vars
             :in-theory (enable nat-bool-a4vec-vars))))

  (defthm 4vmask-to-a4vec-lower-bounds
    (nat-bool-a4vec-lower-boundp nextvar (4vmask-to-a4vec mask boolmask nextvar))
    :hints(("Goal" :in-theory (enable nat-bool-a4vec-lower-boundp)))
    :rule-classes ((:forward-chaining :trigger-terms ((4vmask-to-a4vec mask boolmask nextvar)))))

  (defthm 4vmask-to-a4vec-upper-bounds
    (nat-bool-a4vec-upper-boundp (+ (nfix nextvar) (4vmask-to-a4vec-varcount mask boolmask))
                                 (4vmask-to-a4vec mask boolmask nextvar))
    :hints(("Goal" :in-theory (enable nat-bool-a4vec-upper-boundp)))
    :rule-classes ((:forward-chaining :trigger-terms ((4vmask-to-a4vec mask boolmask nextvar))))))


(define 4vmask-to-a4vec-env ((mask natp) (boolmask integerp) (val 4vec-p) (nextvar natp))
  :returns env
  :prepwork ((local (defthm true-listp-when-nat-bool-listp
                      (implies (nat-bool-listp x)
                               (true-listp x))
                      :hints(("Goal" :in-theory (enable nat-bool-listp))))))
  (4vmask-to-a4vec-rec-env mask boolmask (4vec->upper val) (4vec->lower val) nextvar)
  ///

  (defthm key-exists-in-4vmask-to-a4vec-env
    (iff (hons-assoc-equal v (4vmask-to-a4vec-env mask boolmask val nextvar))
         (and (natp v)
              (<= (nfix nextvar) v)
              (< v (+ (nfix nextvar) (4vmask-to-a4vec-varcount mask boolmask))))))

  (local (defthm mask-lemma
           (IMPLIES
            (AND
             (EQUAL (LOGAND mask a)
                    (LOGAND b mask)))
            (EQUAL (LOGIOR b (lognot mask))
                   (LOGIOR (LOGNOT mask) a)))
     :hints ((bitops::logbitp-reasoning))))

  (defthm eval-4vmask-to-a4vec-with-env
    (b* ((vala (4vmask-to-a4vec mask boolmask nextvar))
         (env (4vmask-to-a4vec-env mask boolmask val nextvar)))
      (implies (4vec-boolmaskp val boolmask)
               (equal (4vec-mask (nfix mask) (a4vec-eval vala env))
                      (4vec-mask (nfix mask) val))))
    :hints(("Goal" :in-theory (e/d (4vmask-to-a4vec
                                    4vec-boolmaskp
                                      4vmask-fix
                                      4vec-mask
                                      a4vec-eval)
                                   (eval-4vmask-to-a4vec-rec-with-env))
            :use ((:instance eval-4vmask-to-a4vec-rec-with-env
                   (upper (4vec->upper val))
                   (lower (4vec->lower val)))))
           (bitops::logbitp-reasoning)
           ;; (and stable-under-simplificationp
           ;;      '(:bdd (:vars nil)))
           ))

  (defthm eval-4vmask-to-a4vec-with-env-mask-natp
    (b* ((vala (4vmask-to-a4vec mask boolmask nextvar))
         (env (4vmask-to-a4vec-env mask boolmask val nextvar)))
      (implies (and (natp mask)
                    (4vec-boolmaskp val boolmask))
               (equal (4vec-mask mask (a4vec-eval vala env))
                      (4vec-mask mask val))))
    :hints (("Goal" :use eval-4vmask-to-a4vec-with-env
             :in-theory (disable eval-4vmask-to-a4vec-with-env)))))



(define svar-boolmasks-lookup-nofix ((v svar-p) (boolmasks svar-boolmasks-p))
  :returns (boolmask (implies (svar-boolmasks-p boolmasks)
                              (equal boolmask
                                     (svar-boolmasks-lookup v boolmasks)))
                     :hints(("Goal" :in-theory (enable svar-boolmasks-lookup))))
  :hooks ((:fix :omit (boolmasks)))
  (ifix (cdr (hons-get (mbe :logic (svar-fix v) :exec v)
                       boolmasks))))

(local (in-theory (disable PICK-A-POINT-SUBSET-STRATEGY)))



(define svex-maskbits-for-vars ((vars svarlist-p)
                                (masks svex-mask-alist-p)
                                (boolmasks svar-boolmasks-p))
  :prepwork ((local (in-theory (enable svarlist-p svarlist-fix))))
  :returns (incr natp :rule-classes :type-prescription)
  (b* (((when (atom vars)) 0)
       (mask (svex-mask-lookup (svex-var (car vars)) masks))
       (boolmask (svar-boolmasks-lookup (car vars) boolmasks))
       ((when (< mask 0)) 0))
    (+ (4vmask-to-a4vec-varcount mask boolmask)
       (svex-maskbits-for-vars (cdr vars) masks boolmasks))))

(define svex-maskbits-ok ((vars svarlist-p)
                          (masks svex-mask-alist-p))
  :prepwork ((local (in-theory (enable svarlist-p svarlist-fix))))
  (b* (((when (atom vars)) t)
       (mask (svex-mask-lookup (svex-var (car vars)) masks))
       ((when (< mask 0)) nil))
    (svex-maskbits-ok (cdr vars) masks)))

(define svex-varmasks->a4env-rec ((vars svarlist-p)
                                  (masks svex-mask-alist-p)
                                  (boolmasks svar-boolmasks-p)
                                  (nextvar natp)
                                  (acc nat-bool-a4env-p!))
  :prepwork ((local (in-theory (enable svarlist-p svarlist-fix
                                       nat-bool-a4env-p
                                       svex-mask-alist-fix
                                       svex-a4vec-env-fix))))
  :returns (mv (err "some mask was negative"
                    (iff err (not (svex-maskbits-ok vars masks)))
                    :hints(("Goal" :in-theory (enable svex-maskbits-ok))))
               (a4env nat-bool-a4env-p! :hyp (nat-bool-a4env-p! acc))
               (nextvar1 (equal nextvar1 (+ (nfix nextvar)
                                            (svex-maskbits-for-vars vars masks boolmasks)))

                         :hints(("Goal" :in-theory (enable svex-maskbits-for-vars)))))
  (b* ((acc (svex-a4vec-env-fix acc))
       ((when (atom vars))
        (mv nil acc (lnfix nextvar)))
       (mask (svex-mask-lookup (svex-var (car vars)) masks))
       ((when (< mask 0))
        (mv (msg "Negative mask: ~x0~%" (svar-fix (car vars))) acc (lnfix nextvar)))
       (boolmask (svar-boolmasks-lookup (car vars) boolmasks))
       (a4vec (4vmask-to-a4vec mask boolmask nextvar))
       (nextvar (+ (lnfix nextvar)
                   (4vmask-to-a4vec-varcount mask boolmask))))
    (svex-varmasks->a4env-rec
     (cdr vars) masks boolmasks nextvar (cons (cons (svar-fix (car vars)) a4vec)
                                    acc)))
  ///

  (defthm member-vars-of-svex-varmasks->a4env-rec
    (iff (member v (nat-bool-a4env-vars
                    (mv-nth 1 (svex-varmasks->a4env-rec vars masks boolmasks nextvar acc))))
         (or (member v (nat-bool-a4env-vars acc))
             (and (natp v)
                  (<= (nfix nextvar) v)
                  (< v (+ (nfix nextvar) (svex-maskbits-for-vars vars masks boolmasks))))))
    :hints(("Goal" :in-theory (enable svex-maskbits-for-vars
                                      nat-bool-a4env-vars))))

  (defthm svex-varmasks->a4env-rec-lower-bounds
    (implies (and (nat-bool-a4env-lower-boundp bound acc)
                  (<= (nfix bound) (nfix nextvar)))
             (nat-bool-a4env-lower-boundp bound (mv-nth 1 (svex-varmasks->a4env-rec vars masks boolmasks nextvar acc))))
    :hints(("Goal" :in-theory (enable nat-bool-a4env-lower-boundp))))

  (defthm svex-varmasks->a4env-rec-upper-bounds
    (implies (and (nat-bool-a4env-upper-boundp bound acc)
                  (<= (+ (nfix nextvar) (svex-maskbits-for-vars vars masks boolmasks))
                      (nfix bound)))
             (nat-bool-a4env-upper-boundp bound (mv-nth 1 (svex-varmasks->a4env-rec vars masks boolmasks nextvar acc))))
    :hints(("Goal" :in-theory (enable nat-bool-a4env-upper-boundp
                                      svex-maskbits-for-vars)))))

(defsection svex-envs-masks-partly-equiv
  (acl2::defquant svex-envs-masks-partly-equiv (vars masks env1 env2)
    (forall v
            (implies (not (member (svar-fix v) (svarlist-fix vars)))
                     (equal (4vec-mask (svex-mask-lookup (svex-var v) masks)
                                       (svex-env-lookup v env1))
                            (4vec-mask (svex-mask-lookup (svex-var v) masks)
                                       (svex-env-lookup v env2)))))
    :rewrite :direct)

  (acl2::defexample svex-envs-masks-partly-equiv-example
    :pattern (equal (4vec-mask (svex-mask-lookup (svex-var v) masks)
                               val1)
                    (4vec-mask mask2 val2))
    :templates (v)
    :instance-rulename svex-envs-masks-partly-equiv-instancing))

(local (defthm hons-assoc-equal-of-append
         (equal (hons-assoc-equal k (append a b))
                (or (hons-assoc-equal k a)
                    (hons-assoc-equal k b)))))

(defthm aig-list->s-of-append-when-first-superset
  (implies (and (nat-bool-listp x)
                (subsetp (nat-bool-list-nats x)
                         (alist-keys env)))
           (equal (aig-list->s x (append env rest))
                  (aig-list->s x env)))
  :hints(("Goal" :in-theory (e/d* (aig-list->s
                                   nat-bool-listp
                                   nat-bool-list-nats
                                   gl::scdr
                                   gl::s-endp)
                                 ((:rules-of-class :type-prescription :here)))
          :induct (aig-list->s x env))))


(defthm a4vec-eval-of-append-when-first-superset
  (implies (and (nat-bool-a4vec-p x)
                (subsetp (nat-bool-a4vec-vars x)
                         (alist-keys env)))
           (equal (a4vec-eval x (append env rest))
                  (a4vec-eval x env)))
  :hints(("Goal" :in-theory (enable a4vec-eval
                                    nat-bool-a4vec-p
                                    nat-bool-a4vec-vars))))

(defthm aig-list->s-of-append-when-first-not-intersect
  (implies (and (nat-bool-listp x)
                (not (intersectp (nat-bool-list-nats x)
                                 (alist-keys prev))))
           (equal (aig-list->s x (append prev env))
                  (aig-list->s x env)))
  :hints(("Goal" :in-theory (e/d* (aig-list->s
                                   nat-bool-listp
                                   nat-bool-list-nats
                                   gl::scdr
                                   gl::s-endp)
                                 ((:rules-of-class :type-prescription :here)))
          :induct (aig-list->s x env))))


(defthm a4vec-eval-of-append-when-first-not-intersect
  (implies (and (nat-bool-a4vec-p x)
                (not (intersectp (nat-bool-a4vec-vars x)
                                 (alist-keys prev))))
           (equal (a4vec-eval x (append prev env))
                  (a4vec-eval x env)))
  :hints(("Goal" :in-theory (enable a4vec-eval
                                    nat-bool-a4vec-p
                                    nat-bool-a4vec-vars))))

(defthm nat-bool-a4vec-p-of-nat-bool-a4env
  (implies (and (nat-bool-a4env-p x)
                (hons-assoc-equal k x))
           (nat-bool-a4vec-p (cdr (hons-assoc-equal k x))))
  :hints(("Goal" :in-theory (enable nat-bool-a4env-p))))

(define svex-mask-lookup-nofix (x masks)
  :prepwork ((local (Defthm assoc-when-svex-mask-alist-p
                      (implies (svex-mask-alist-p x)
                               (equal (assoc k x)
                                      (hons-assoc-equal k x)))
                      :hints(("Goal" :in-theory (enable svex-mask-alist-p))))))
  (or (cdr (hons-get x masks)) 0)
  ///
  (defthm svex-mask-lookup-nofix-when-right-types
    (implies (and (svex-p x)
                  (svex-mask-alist-p masks))
             (equal (svex-mask-lookup-nofix x masks)
                    (svex-mask-lookup x masks)))
    :hints(("Goal" :in-theory (enable svex-mask-lookup)))))

(define svex-env-lookup-nofix (x env)
  (or (cdr (hons-get x env)) (4vec-x))
  ///
  (defthm svex-env-lookup-nofix-when-right-types
    (implies (and (svar-p x)
                  (svex-env-p env))
             (equal (svex-env-lookup-nofix x env)
                    (svex-env-lookup x env)))
    :hints(("Goal" :in-theory (enable svex-env-lookup
                                      svex-env-p)))))








(define svex-varmasks/env->aig-env-rec ((vars svarlist-p)
                                        (masks svex-mask-alist-p)
                                        (boolmasks svar-boolmasks-p)
                                        (env svex-env-p "look up variables in env to get 4vecs to assign -- symbolic")
                                        (nextvar natp)
                                        (acc "aig environment accumulator"))
  :prepwork ((local (in-theory (enable svarlist-p svarlist-fix))))
  :returns (mv (err "some mask was negative"
                    (implies (svex-mask-alist-p masks)
                             (iff err (not (svex-maskbits-ok vars masks))))
                    :hints(("Goal" :in-theory (enable svex-maskbits-ok))))
               (env) ;; binds AIG vars to Boolean values
               (nextvar1
                (implies (and (svex-mask-alist-p masks)
                              (svar-boolmasks-p boolmasks))
                         (equal nextvar1
                                (+ (nfix nextvar)
                                   (svex-maskbits-for-vars vars masks boolmasks))))
                :hints(("Goal" :in-theory (enable svex-maskbits-for-vars)))))
  :hooks ((:fix :args (vars nextvar)))
  (b* (((when (atom vars))
        (mv nil acc (lnfix nextvar)))
       (mask (svex-mask-lookup-nofix (svex-var (car vars)) masks))
       ((when (< mask 0))
        (mv (msg "Negative mask: ~x0~%" (svar-fix (car vars)))
            acc (lnfix nextvar)))
       (boolmask (svar-boolmasks-lookup-nofix (car vars) boolmasks))
       (4vec (svex-env-lookup-nofix (svar-fix (car vars)) env))
       (env-part
        (4vmask-to-a4vec-env mask boolmask 4vec nextvar))
       (nextvar (+ (lnfix nextvar)
                   (4vmask-to-a4vec-varcount mask boolmask))))
    (svex-varmasks/env->aig-env-rec
     (cdr vars) masks boolmasks env nextvar (append env-part acc)))
  ///

  (defthm key-exists-in-svex-varmasks/env->aig-env-rec
    (implies (and (svex-mask-alist-p masks)
                  (svar-boolmasks-p boolmasks))
             (iff (hons-assoc-equal v (mv-nth 1 (svex-varmasks/env->aig-env-rec
                                                 vars masks boolmasks env nextvar acc)))
                  (or (hons-assoc-equal v acc)
                      (and (natp v)
                           (<= (nfix nextvar) v)
                           (< v (+ (nfix nextvar) (svex-maskbits-for-vars vars masks boolmasks)))))))
    :hints(("Goal" :in-theory (enable svex-maskbits-for-vars))))

  (local
   (defun svex-varmasks->a4env-rec-induct (vars masks boolmasks nextvar a4acc goalenv envacc)
     (declare (ignorable vars masks boolmasks nextvar a4acc goalenv envacc))
     (b* (((when (atom vars)) nil)
          (mask (svex-mask-lookup (svex-var (car vars)) masks))
          ((when (< mask 0)) nil)
          (boolmask (svar-boolmasks-lookup (car vars) boolmasks))
          (4vec (svex-env-lookup (car vars) goalenv))
          (env-part
           (4vmask-to-a4vec-env mask boolmask 4vec nextvar))
          (a4vec (4vmask-to-a4vec mask boolmask nextvar))
          (nextvar (+ (lnfix nextvar)
                      (4vmask-to-a4vec-varcount mask boolmask))))
       (svex-varmasks->a4env-rec-induct
        (cdr vars) masks boolmasks nextvar
        (cons (cons (svar-fix (car vars)) a4vec)
              a4acc)
        goalenv (append env-part envacc)))))

  (defthm 4vmask-to-a4vec-vars-subset-of-keys
    (SUBSETP-EQUAL
     (NAT-BOOL-A4VEC-VARS
      (4vmask-to-a4vec mask boolmask nextvar))
     (ALIST-KEYS
      (4vmask-to-a4vec-env mask boolmask val nextvar)))
    :hints ((acl2::set-reasoning)))

  (defthm member-nat-bool-a4vec-vars-of-lookup-when-upper-bounded
    (implies (and (nat-bool-a4env-p a4acc)
                  (nat-bool-a4env-upper-boundp nextvar a4acc)
                  (<= (nfix nextvar) k))
             (not (member k (nat-bool-a4vec-vars (cdr (hons-assoc-equal v a4acc))))))
    :hints(("Goal" :in-theory (enable nat-bool-a4env-p
                                      nat-bool-a4env-upper-boundp))))

  (defthm 4vmask-to-a4vec-env-vars-not-intersect-when-upper-bounded
    (implies (and (nat-bool-a4env-p a4acc)
                  (double-rewrite (nat-bool-a4env-upper-boundp nextvar a4acc)))
             (not (intersectp (nat-bool-a4vec-vars
                               (cdr (hons-assoc-equal v a4acc)))
                              (alist-keys (4vmask-to-a4vec-env mask boolmask val nextvar)))))
    :hints ((acl2::set-reasoning)))

  (acl2::defquant svex-env-boolmasks-ok (env boolmasks)
    (forall v
            (4vec-boolmaskp (svex-env-lookup v env)
                            (svar-boolmasks-lookup v boolmasks)))
    :rewrite :direct)

  (local (defthm svex-env-lookup-of-cons
           (equal (svex-env-lookup k (cons (cons k0 v0) rest))
                  (if (equal (svar-fix k) (svar-fix k0))
                      (4vec-fix v0)
                    (svex-env-lookup k rest)))
           :hints(("Goal" :in-theory (enable svex-env-lookup
                                             svex-env-fix)))))

  (local (in-theory (enable svex-env-boolmasks-ok-necc)))

  (defthm eval-svex-varmasks->a4env-rec-with-env
    (b* (((mv err a4env ?nextvar1)
          (svex-varmasks->a4env-rec vars masks boolmasks nextvar a4acc))
         ((mv ?err1 env ?nextvar1)
          (svex-varmasks/env->aig-env-rec vars masks boolmasks goalenv nextvar envacc)))
      (implies (and (not err)
                    (nat-bool-a4env-p a4acc)
                    (nat-bool-a4env-upper-boundp nextvar a4acc)
                    (svex-mask-alist-p masks)
                    (svar-boolmasks-p boolmasks)
                    (svex-env-boolmasks-ok goalenv boolmasks)
                    (svex-env-p goalenv)
                    (svex-envs-masks-partly-equiv
                     vars masks
                     (svex-a4vec-env-eval a4acc envacc)
                     goalenv)
                    (subsetp (alist-keys (svex-env-fix goalenv))
                             (append (svarlist-fix vars)
                                     (alist-keys (svex-a4vec-env-fix a4acc)))))
               (svex-envs-mask-equiv masks
                                     (svex-a4vec-env-eval a4env env)
                                     goalenv)))
    :hints(("Goal" :in-theory (enable svex-varmasks->a4env-rec
                                      svarlist-fix
                                      svex-maskbits-ok
                                      nat-bool-a4env-p
                                      nat-bool-a4env-upper-boundp
                                      svex-a4vec-env-fix
                                      svex-a4vec-env-eval
                                      alist-keys
                                      svex-alist-keys)
            :induct (svex-varmasks->a4env-rec-induct
                     vars masks boolmasks nextvar a4acc goalenv envacc)
            :expand (svex-varmasks/env->aig-env-rec
                     vars masks boolmasks goalenv nextvar envacc))
           (and stable-under-simplificationp
                (cond ((assoc 'subsetp-equal clause) ;; has a (not (subsetp-equal... lit
                       (acl2::set-reasoning))
                      ((assoc 'svex-envs-masks-partly-equiv clause)
                       '(:computed-hint-replacement
                         ((acl2::witness :ruleset (svex-envs-masks-partly-equiv-witnessing))
                          (acl2::witness :ruleset (svex-envs-masks-partly-equiv-example)))
                         :in-theory (enable ;; svex-env-lookup
                                            svex-env-fix)))
                      (t '(:computed-hint-replacement
                           ((acl2::witness :ruleset (svex-envs-mask-equiv-witnessing))
                            (acl2::witness :ruleset (svex-envs-masks-partly-equiv-example)))
                           :no-op t)))))))


(define svex-varmasks->a4env ((vars svarlist-p)
                              (masks svex-mask-alist-p)
                              (boolmasks svar-boolmasks-p))
  :returns (mv (err "some mask was negative"
                    (iff err (not (svex-maskbits-ok vars masks))))
               (a4env nat-bool-a4env-p!))
  (b* (((mv err res &)
        (svex-varmasks->a4env-rec vars masks boolmasks 0 nil)))
    (mv err res)))


(define svex-varmasks/env->aig-env ((vars svarlist-p)
                                    (masks svex-mask-alist-p)
                                    (boolmasks svar-boolmasks-p)
                                    (env svex-env-p "look up variables in env to get 4vecs to assign"))
  :returns (mv (err "some mask was negative"
                    (implies (svex-mask-alist-p masks)
                             (iff err (not (svex-maskbits-ok vars masks))))
                    :hints(("Goal" :in-theory (enable svex-maskbits-ok))))
               (env "binds AIG vars to Boolean values"))
    :hooks ((:fix :args (vars)))
  (b* (((mv err res &)
        (svex-varmasks/env->aig-env-rec vars masks boolmasks env 0 nil)))
    (mv err res))
  ///
  (defthm eval-svex-varmasks->a4env-with-env
    (b* (((mv err a4env)
          (svex-varmasks->a4env vars masks boolmasks))
         ((mv ?err1 env)
          (svex-varmasks/env->aig-env vars masks boolmasks goalenv)))
      (implies (and (not err)
                    (svex-mask-alist-p masks)
                    (svar-boolmasks-p boolmasks)
                    (svex-env-p goalenv)
                    (svex-env-boolmasks-ok goalenv boolmasks)
                    (subsetp (alist-keys (svex-env-fix goalenv))
                             (svarlist-fix vars)))
               (svex-envs-mask-equiv masks
                                     (svex-a4vec-env-eval a4env env)
                                     goalenv)))
    :hints (("goal" :use ((:instance eval-svex-varmasks->a4env-rec-with-env
                           (nextvar 0)
                           (a4acc nil)
                           (envacc nil)))
             :in-theory (e/d (svex-varmasks->a4env
                              svex-env-lookup
                              svex-lookup)
                             (eval-svex-varmasks->a4env-rec-with-env)))
            (acl2::witness :ruleset (svex-envs-masks-partly-equiv-witnessing))
            (acl2::set-reasoning))))

(define svex-env-check-boolmasks ((boolmasks svar-boolmasks-p)
                                  (env svex-env-p))
  :prepwork ((local (in-theory (enable svar-boolmasks-p svar-boolmasks-fix))))
  :hooks nil
  (b* (((when (atom boolmasks)) t)
       ((unless (mbt (consp (car boolmasks))))
        (svex-env-check-boolmasks (cdr boolmasks) env))
       ((cons var mask) (car boolmasks))
       (val (svex-env-lookup-nofix var env))
       (ok (4vec-boolmaskp val mask))
       (?ign (and (not ok)
                  (cw "not 4vec-boolmaskp: ~x0~%" var))))
    (and (svex-env-check-boolmasks (cdr boolmasks) env)
         ok))
  ///
  (acl2::defexample svex-env-boolmasks-ok-example
    :pattern (svex-env-lookup v env)
    :templates (v)
    :instance-rulename svex-env-boolmasks-ok-instancing)

  (defthm svex-env-check-boolmasks-correct
    (implies (and (svex-env-check-boolmasks boolmasks env)
                  (svex-env-p env)
                  (svar-boolmasks-p boolmasks))
             (svex-env-boolmasks-ok env boolmasks))
    :hints (("goal" :induct (svex-env-check-boolmasks boolmasks env))
            (acl2::witness :ruleset (svex-env-boolmasks-ok-witnessing
                                     svex-env-boolmasks-ok-example))
            (and stable-under-simplificationp
                 '(:in-theory (enable svar-boolmasks-lookup)
                   :expand ((:free (x) (4vec-boolmaskp x 0))))))))

(define svexlist-mask-alist-memo ((x svexlist-p))
  :enabled t
  (svexlist-mask-alist x)
  ///
  (memoize 'svexlist-mask-alist-memo))

(define svexlist->a4vecs-for-varlist ((x svexlist-p)
                                      (vars svarlist-p)
                                      (boolmasks svar-boolmasks-p))
  :returns (mv (err (iff err (not (svex-maskbits-ok vars (svexlist-mask-alist x)))))
               (a4vecs a4veclist-p))
  :short "Creates a symbolic bit-level representation for x, assuming that vars
          are the only vars relevant to x and that the bits of vars given in boolmasks
          are Boolean-valued."
  :long "<p>Steps: First creates a symbolic environment mapping the variables
to a4vec structures, each bit of which is a free variable.  (For bits
constrained to be Boolean by boolmasks, the same variable is shared for
upper/lower.)  Then uses @('svexlist->a4vec-top') to generate a4vecs corresponding
to the svexes.</p>"

  (b* (;; (- (sneaky-push 'svexlist x))
       (masks (svexlist-mask-alist-memo x))
       ((mv err a4env) (svex-varmasks->a4env vars masks boolmasks))
       ((when err) (mv err nil))
       (a4env (make-fast-alist a4env))
       (res (svexlist->a4vec-top x a4env masks))
       (?ign (fast-alist-free a4env)))
    (mv nil res))
  ///
  (memoize 'svexlist->a4vecs-for-varlist))

(define svexlist->a4vec-aig-env-for-varlist ((x svexlist-p)
                                             (vars svarlist-p)
                                             (boolmasks svar-boolmasks-p)
                                             (env svex-env-p))
  :returns (mv (err (iff err (not (svex-maskbits-ok vars (svexlist-mask-alist x)))))
               (aig-env))
  :hooks ((:fix :args (x vars)))
  (b* ((masks (svexlist-mask-alist-memo x)))
    (svex-varmasks/env->aig-env vars masks boolmasks env))
  ///
  (defthm svexlist->a4vec-for-varlist-correct
    (b* (((mv err a4vecs) (svexlist->a4vecs-for-varlist x vars boolmasks))
         ((mv ?err1 aig-env) (svexlist->a4vec-aig-env-for-varlist x vars boolmasks env)))
      (implies (and (not err)
                    (svex-env-p env)
                    (svar-boolmasks-p boolmasks)
                    (svex-env-boolmasks-ok env boolmasks)
                    (subsetp (alist-keys env)
                             (svarlist-fix vars)))
               (equal (a4veclist-eval a4vecs aig-env)
                      (svexlist-eval x env))))
    :hints(("Goal" :in-theory (e/d (svexlist->a4vecs-for-varlist)
                                   (svexlist-eval-of-mask-equiv-envs))
            :use ((:instance svexlist-eval-of-mask-equiv-envs
                   (masks (svexlist-mask-alist x))
                   (env1 (SVEX-A4VEC-ENV-EVAL
                          (MV-NTH 1
                                  (SVEX-VARMASKS->A4ENV VARS (SVEXLIST-MASK-ALIST X) boolmasks))
                          (MV-NTH 1
                                  (SVEX-VARMASKS/ENV->AIG-ENV VARS (SVEXLIST-MASK-ALIST X)
                                                              boolmasks ENV))))
                   (env2 env)))))))




(local (defthm subset-of-mergesorts-is-subsetp
         (iff (subset (mergesort a) (mergesort b))
              (subsetp a b))
         :hints(("Goal" :in-theory (enable* set::definitions)))))


(define svexlist-rewrite-fixpoint-memo ((x svexlist-p))
  :enabled t
  (svexlist-rewrite-fixpoint x :verbosep t)
  ///
  (memoize 'svexlist-rewrite-fixpoint-memo))

(define svexlist-eval-gl-with-var-superset
  ((x svexlist-p     "Svex expressions to evaluate.")
   (vars svarlist-p  "List of variables; should be a superset of the names bound in @('env').")
   (boolmasks svar-boolmasks-p "Mapping from variables to bitmasks on which those
                                variables' bindings in @('env') should be
                                Boolean-valued.")
   (env svex-env-p   "Bindings of variables to @(see 4vec) values."))
  :short "Equivalent of svexlist-eval intended to work well under GL symbolic execution."
  :long "

<p>This function is provably equivalent to @(see svexlist-eval), but is
tailored to perform well under symbolic execution.  For symbolic execution, we
assume that the inputs to this function other than @('env') are fully concrete,
and that @('env') is symbolic only in its values, not its keys or its shape.</p>

<p>The extra variables @('vars') and @('boolmasks') are logically irrelevant,
but offer important optimizations for symbolic execution performance; we
discuss them further below.  It is safe (but not necessarily fast) to call this
function with @('vars') set to @('(svar-alist-keys env)') and @('boolmasks')
set to @('NIL').</p>

<h4>Behavior under Symbolic Execution</h4>

<ol>

<li>Applies rewriting to the supplied svex expressions -- see @(see
svexlist-rewrite-fixpoint).</li>

<li>Compares the given @('env') and @('boolmasks').  If there is a pair
@('(name . mask)') in boolmasks for which the binding for @('name') in env is
not Boolean-valued on the bits set to 1 in @('mask'), then fail out of symbolic
simulation.  (In AIG mode, the masked bits must be <i>syntactically</i>
Boolean-valued -- practically speaking, this means the upper/lower parts should
result from the same computation.)</li>

<li>Ensures that the variables bound in @('env') are indeed a subset of
@('vars').</li>

<li>Compiles the svex list @('x') into @(see a4vec) objects, a symbolic
analogue of @(see 4vec) but with each bit an AIG -- see @(see
svexlist->a4vecs-for-varlist).  This computation uses the assumptions, checked
in the two steps above, that only the variables in @('vars') are non-X, and
that the masked bits in @('boolmasks') are Boolean-valued. These assumptions
can reduce the complexity of the generated AIGs.  (Note everything used in this
computation is concrete -- the @('env') isn't involved.)</li>

<li>Creates an alist binding the AIG variables used in the above step to the
appropriate symbolic bits from @('env').</li>

<li>Symbolically evaluates each of the a4vec objects from step 4 under the
bindings from step 5 using GL's symbolic simulator of @(see acl2::aig-eval).
This results in GL-native symbolic 4vec objects, which is the result we
want.</li>

</ol>

<h4>Optimization using the Extra Arguments</h4>

<p>Performance of symbolic execution (and SAT solving, when in AIG mode) is
related to the size of the AIGs produced by the svex to AIG
transformation (step 4, above).  Two ways to decrease that size are (1) to turn
certain variables into constant Xes, if it is known that they're irrelevant,
and (2) to assume certain bits of some variables are Boolean-valued, which
means it can be represented by just one AIG variable rather than two.</p>

<p>Another performance consideration is that the transformation to AIGs is
itself sometimes significant.  Especially for theorems proved by
case-splitting, it is important not to need to repeat this transformation for
each case.  The function that does the transformation is memoized, but it is
important in this case that it always be called with the same arguments.</p>

<p>The @('vars') list pertains to optimization (1): if not present in the list,
a variable in the svex expressions will just be replaced with an X.  Therefore,
in general it's best to use exactly the set of variables bound in the
environment.  However, it may not be worth it to redo the AIG conversion each
time the environment's bound variables changes, so we take @('vars')
separately.</p>

<p>The @('boolmasks') allows optimization (2).  It is best for symbolic
execution performance to bind every variable in @('vars') to -1, but this may
fail if the @('env') is not constructed in such a way that the values are
obviously 2-vectors.</p>"
  (b* ((env (svex-env-fix env))
       (vars (hons-copy (svarlist-fix vars)))
       (x (svexlist-rewrite-fixpoint-memo x))
       ;; Syntax checking...
       (keys (alist-keys env))
       (keys (mbe :logic (set::mergesort keys)
                  :exec (if (set::setp keys) keys (set::mergesort keys))))
       (svars (mbe :logic (set::mergesort vars)
                   :exec (if (set::setp vars) vars (set::mergesort vars))))
       (env (make-fast-alist env))
       ((unless (set::subset keys svars))
        (b* ((?ign (cw "ERROR! Expected environment variables to be a subset ~
                        of the given list.  Missing: ~x0~%"
                       (set::difference keys svars)))
             (?ign (gl::gl-error 'subset-check-failed)))
          (gl::gl-hide (svexlist-eval x env))))
       (boolmasks (make-fast-alist (hons-copy (svar-boolmasks-fix boolmasks))))
       ((unless (svex-env-check-boolmasks boolmasks env))
        (b* ((?ign (cw "ERROR: some bits assumed to be Boolean were not~%"))
             (?ign (gl::gl-error 'boolcheck-failed)))
          (gl::gl-hide (svexlist-eval x env))))
       ;; (?ign (cw "Boolmasks: ~x0~%" boolmasks))
       ;; (?ign (bitops::sneaky-push 'boolmasks boolmasks))
       ;; (?ign (bitops::sneaky-push 'vars vars))
       ;; (?ign (bitops::sneaky-push 'x x))
       ((mv err a4vecs) (time$ (svexlist->a4vecs-for-varlist x vars boolmasks)
                               :msg "; svex->aigs: ~st sec, ~sa bytes.~%"))
       ((when err)
        (b* ((?ign (cw "ERROR gathering AIG bits for variables: ~@0~%" err))
             (?ign (gl::gl-error 'a4env-failed)))
          (gl::gl-hide (svexlist-eval x env))))
       ((mv ?err aig-env)
        ;; ignore the error; it can't exist if the above doesn't
        (time$ (svexlist->a4vec-aig-env-for-varlist x vars boolmasks env)
               :msg "; env -> aig env: ~st sec, ~sa bytes.~%"))
       (?ign (fast-alist-free env)))
    (a4veclist-eval a4vecs aig-env))
  ///
  (defthm svexlist-eval-gl-with-var-superset-is-svexlist-eval
    (equal (svexlist-eval-gl-with-var-superset x vars boolmasks env)
           (svexlist-eval x env))
    :hints (("goal" :use ((:instance svexlist->a4vec-for-varlist-correct
                           (boolmasks (svar-boolmasks-fix boolmasks))
                           (x (svexlist-rewrite-fixpoint-memo x))
                           (env (svex-env-fix env))))
             :in-theory (disable svexlist->a4vec-for-varlist-correct))))

  (gl::def-gl-rewrite svexlist-eval-with-vars-redef
    (equal (svexlist-eval-with-vars x vars boolmasks env)
           (svexlist-eval-gl-with-var-superset x vars boolmasks env))))



;;; Now rework a4veclist-eval to phrase it in terms of a single call to aig-eval-list

(define a4vec->aiglist ((x a4vec-p))
  :returns (lst true-listp :rule-classes :type-prescription)
  (b* (((a4vec x) x))
    (append x.upper x.lower)))

(local (defthm true-listp-nthcdr
         (implies (true-listp x)
                  (true-listp (nthcdr n x)))
         :hints(("Goal" :in-theory (e/d (nthcdr)
                                        (acl2::cdr-nthcdr))
                 :induct (nthcdr n x)))
         :rule-classes :type-prescription))

(local (defthm aig-eval-list-of-append
         (Equal (aig-eval-list (append x y) env)
                (append (aig-eval-list x env)
                        (aig-eval-list y env)))))

(local (defthm len-of-aig-eval-list
         (equal (len (aig-eval-list x env))
                (len x))))

(local (defthm consp-of-aig-eval-list
         (equal (consp (aig-eval-list x env))
                (consp x))))

(local (defthm nthcdr-of-append-equal-len
         (implies (equal (nfix n) (len x))
                  (equal (nthcdr n (append x y))
                         y))
         :hints(("Goal" :in-theory (e/d (nthcdr)
                                        (acl2::cdr-nthcdr))
                 :induct (nthcdr n x)))))

(local (defthm take-of-append-equal-len
         (implies (equal (nfix n) (len x))
                  (equal (take n (append x y))
                         (list-fix x)))
         :hints(("Goal" :in-theory (e/d (acl2::take-redefinition))
                 :induct (nthcdr n x)))))

(local (in-theory (disable double-containment)))

(local (defthm v2i-of-aig-eval-list
         (equal (gl::v2i (aig-eval-list x env))
                (aig-list->s x env))
         :hints(("Goal" :in-theory (enable (:i aig-list->s) gl::v2i gl::scdr gl::s-endp)
                 :induct (aig-list->s x env)
                 :expand ((aig-list->s x env)
                          (aig-eval-list x env)
                          (:free (A b) (gl::v2i (cons a b))))))))

(define 4vec-from-bitlist ((upper-len natp) (lower-len natp) (bits true-listp))
  :hooks ((:fix :omit (bits)))
  :returns (mv (vec 4vec-p)
               (rest true-listp
                     :hyp (true-listp bits)
                     :rule-classes :type-prescription))
  ;; note: list-fixing bits is bad here because it's not even linear in the
  ;; number of bits we're operating on
  (b* ((upper-bits (take upper-len bits))
       (rest (nthcdr upper-len bits))
       (lower-bits (take lower-len rest))
       (rest (nthcdr lower-len rest)))
    (mv (4vec (gl::v2i upper-bits)
              (gl::v2i lower-bits))
        rest))
  ///
  (defthm 4vec-from-bitlist-correct
    (b* (((a4vec x) x))
      (equal (4vec-from-bitlist (len x.upper) (len x.lower)
                                (append (aig-eval-list (a4vec->aiglist x) env)
                                        rest))
             (mv (a4vec-eval x env) rest)))
    :hints(("Goal" :in-theory (enable a4vec->aiglist)))))

(define a4veclist->aiglist ((x a4veclist-p))
  :returns (aigs true-listp :rule-classes :type-prescription)
  (if (atom x)
      nil
    (append (a4vec->aiglist (car x))
            (a4veclist->aiglist (cdr x)))))

(define 4veclist-from-bitlist ((origs a4veclist-p) (bits true-listp))
  :returns (4vecs 4veclist-p)
  :hooks ((:fix :omit (bits)))
  (b* (((when (atom origs)) nil)
       ((a4vec x) (car origs))
       ((mv first restbits)
        (4vec-from-bitlist (len x.upper) (len x.lower) bits)))
    (cons first (4veclist-from-bitlist (cdr origs) restbits)))
  ///
  (defthm 4veclist-from-bitlist-correct
    (equal (4veclist-from-bitlist x (aig-eval-list (a4veclist->aiglist x) env))
           (a4veclist-eval x env))
    :hints(("Goal" :in-theory (enable a4veclist-eval
                                      a4veclist->aiglist)))))


(define a4veclist-eval-gl ((x a4veclist-p) (env))
  :returns (res 4veclist-p)
  (b* ((aiglist (time$ (a4veclist->aiglist x)
                       :msg "; a4vecs->aigs: ~st sec, ~sa bytes.~%"))
       (bitlist (time$ (aig-eval-list aiglist env)
                       :msg "; aig eval: ~st sec, ~sa bytes.~%")))
    (time$ (4veclist-from-bitlist x bitlist)
           :msg "; bits->4vecs: ~st sec, ~sa bytes.~%"))
  ///
  (defthm a4veclist-eval-gl-correct
    (equal (a4veclist-eval-gl x env)
           (a4veclist-eval x env)))

  (gl::def-gl-rewrite a4veclist-eval-redef
    (equal (a4veclist-eval x env)
           (a4veclist-eval-gl x env))))




(gl::def-gl-rewrite svex-alist-eval-gl-rewrite
    (equal (svex-alist-eval x env)
           (pairlis$ (svex-alist-keys x)
                     (svexlist-eval-with-vars
                      (svex-alist-vals x) (alist-keys env) nil env)))
    :hints(("Goal" :in-theory (enable svex-alist-eval pairlis$ svex-alist-keys
                                      svex-alist-vals svexlist-eval))))

(gl::def-gl-rewrite svex-eval-gl-rewrite
  (equal (svex-eval x env)
         (car (svexlist-eval-with-vars (list x) (alist-keys env) nil env))))
