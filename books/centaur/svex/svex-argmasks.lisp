; SVEX - Symbolic, Vector-Level Hardware Description Library
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "SVEX")
(include-book "svmask")
;; (include-book "coi/nary/nary" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "bits"))
(local (include-book "lattice"))

(local (in-theory (enable svex-eval-when-2vec-p-of-minval)))

(defxdoc svex-argmasks.lisp :parents (svex-argmasks))
(local (xdoc::set-default-parents svex-argmasks.lisp))

;; (defthm svobj-fix-equal-forward-to-svobj-equiv
;;   (implies (equal (svobj-fix x1) (svobj-fix x2))
;;            (svobj-equiv x1 x2))
;;   :hints(("Goal" :in-theory (enable svobj-equiv)))
;;   :rule-classes :forward-chaining)



(defthm len-of-4veclist-fix
  (equal (len (4veclist-fix x))
         (len x)))


(defthm 4veclist-nth-out-of-bounds
  (implies (<= (len x) (nfix n))
           (equal (4veclist-nth n x) (4vec-x)))
  :hints(("Goal" :in-theory (enable 4veclist-nth))))


;; (local (defthm svobj-fix-when-natp
;;          (implies (natp x)
;;                   (equal (svobj-fix x) x))
;;          :hints(("Goal" :in-theory (enable svobj-fix 4vec-p)))))



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
            :induct (ind len m x)))))


;; (defthm nth-of-svexlist-eval
;;   (svobj-equiv (nth n (svexlist-eval args env))
;;                (svex-eval (nth n args) env))
;;   :hints(("Goal" :in-theory (enable svexlist-eval))))

;; (defthm svex-args-aritycheck-expand-nths
;;   (equal (svex-args-aritycheck

;; (local (defthm nth-when-gte-than-len
;;          (implies (<= (len x) (nfix n))
;;                   (equal (nth n x) nil))))



(local (defthm nth-open-constidx
         (implies (syntaxp (quotep n))
                  (equal (nth n x)
                         (if (zp n)
                             (car x)
                           (nth (1- n) (cdr x)))))))

(defthm len-equal-0
  (equal (equal (len x) 0)
         (not (consp x))))


(defthm svexlist-eval-when-atom
  (implies (not (consp x))
           (equal (svexlist-eval x env) nil))
  :hints(("Goal" :in-theory (enable svexlist-eval)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm svexlist-eval-under-iff
  (iff (svexlist-eval x env)
       (consp x))
  :hints(("Goal" :expand ((svexlist-eval x env)))))

(defthm consp-svexlist-eval
  (equal (consp (svexlist-eval x env))
         (consp x))
  :hints(("Goal" :expand ((svexlist-eval x env)))))

(defun svex-nths-binding-list (args n form)
  (if (atom args)
      nil
    (cons (list (car args) `(svex-nth ,n ,form))
          (svex-nths-binding-list (cdr args) (1+ n) form))))

(acl2::def-b*-binder svex-nths
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


(defun def-svmask-fn (fnname formals body fix-hints prep hints otf-flg)
  (b* ((maskfn (intern-in-package-of-symbol
                (concatenate 'string "SVMASK-FOR-" (symbol-name fnname))
                (if (equal (symbol-package-name fnname) "COMMON-LISP")
                    'acl2::foo
                  fnname)))
       (thmname (intern-in-package-of-symbol
                (concatenate 'string (symbol-name maskfn) "-CORRECT")
                maskfn)))
    `(define ,maskfn ((mask 4vmask-p)
                      (args svexlist-p))
       :ignore-ok t
       :irrelevant-formals-ok t
       :returns (m (4vmasklist-p m))
       (b* (((svex-nths . ,formals) args)
            (mask (mbe :logic (4vmask-fix mask) :exec mask)))
         ,body)
       ///
       (local (progn . ,prep))

       (fty::deffixequiv ,maskfn :hints ,fix-hints)

       (defthm ,thmname
         (implies (and (equal (4veclist-mask
                               (,maskfn mask args)
                               (svexlist-eval args env))
                              (4veclist-mask
                               (,maskfn mask args)
                               args1))
                       (syntaxp (not (equal args1 `(svexlist-eval ,args ,env)))))
                  (equal (4vec-mask mask (svex-apply ',fnname args1))
                         (4vec-mask mask (svex-apply ',fnname (svexlist-eval args env)))))
         :hints ,hints
         :otf-flg ,otf-flg))))

(defmacro def-svmask (fnname formals body &key fix-hints prep hints otf-flg)
  (def-svmask-fn fnname formals body fix-hints prep hints otf-flg))






(defthm 4veclist-nth-of-nthcdr
  (equal (4veclist-nth m (nthcdr n x))
         (4veclist-nth (+ (nfix m) (nfix n)) x))
  :hints(("Goal" :in-theory (enable 4veclist-nth))))

(defthm 4veclist-mask-of-len-fix
  (equal (4veclist-mask (4vmasklist-len-fix len (cons mask1 masks)) args)
         (and (consp args)
              (if (zp len)
                  (4veclist-fix args)
                (cons (4vec-mask mask1 (4veclist-nth 0 args))
                      (4veclist-mask (4vmasklist-len-fix (1- len) masks)
                                         (cdr args))))))
  :hints(("Goal" :in-theory (enable 4veclist-mask 4veclist-nth))))

(defthm 4veclist-mask-of-len-fix-nthcdr
  (equal (4veclist-mask (4vmasklist-len-fix len (cons mask1 masks))
                            (nthcdr n args))
         (and (consp (nthcdr n args))
              (if (zp len)
                  (4veclist-fix (nthcdr n args))
                (cons (4vec-mask mask1 (4veclist-nth n args))
                      (4veclist-mask (4vmasklist-len-fix (1- len) masks)
                                         (nthcdr (+ 1 (nfix n)) args))))))
  :hints(("Goal" :in-theory (enable 4veclist-mask 4veclist-nth))))


(local (in-theory (disable 4vmasklist-len-fix-of-cons)))



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


(define 4vmask-empty ((x 4vmask-p))
  :enabled t
  (mbe :logic (4vmask-equiv x 0)
       :exec (eql x 0)))

(define 4vmask-all-or-none ((x 4vmask-p))
  :returns (xx 4vmask-p)
  (if (4vmask-empty x) 0 -1)
  ///
  (fty::deffixequiv 4vmask-all-or-none))




(def-svmask bitsel (n x)
  (b* ((nval (svex-xeval n)))
    (list (4vmask-all-or-none mask)
          (if (4vec-index-p nval)
              (ash (bool->bit (logbitp 0 mask))
                   (2vec->val nval))
            (4vmask-all-or-none mask))))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vmask-all-or-none
                                  4vec-mask
                                  4veclist-nth
                                  4vec-bit-index
                                  4vec-bit-extract))))
          (bitops::logbitp-reasoning))
  :otf-flg t)

(def-svmask unfloat (x)
  (list mask)
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  3vec-fix
                                  4veclist-nth))))
          (bitops::logbitp-reasoning)))


(def-svmask id (x)
  (list mask)
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  3vec-fix
                                  4veclist-nth))))
          (bitops::logbitp-reasoning)))

(def-svmask bitnot (x)
  (list mask)
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  3vec-fix
                                  3vec-bitnot
                                  4vec-bitnot
                                  4veclist-nth))))
          (bitops::logbitp-reasoning)))

(def-svmask onp (x)
  (list mask)
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  3vec-fix
                                  4vec-onset
                                  4veclist-nth))))
          (bitops::logbitp-reasoning)))

(def-svmask offp (x)
  (list mask)
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  3vec-fix
                                  4vec-offset
                                  4veclist-nth))))
          (bitops::logbitp-reasoning)))



(local (in-theory (disable acl2::zip-open
                           BITOPS::LOGAND-NATP-TYPE-2
                           BITOPS::LOGIOR-NATP-TYPE
                           4VEC->LOWER-WHEN-2VEC-P
                           DOUBLE-CONTAINMENT
                           SVEX-EVAL-WHEN-2VEC-P-OF-MINVAL
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
                           not)))

;; (local (in-theory (enable logbitp-when-4vec-[=-svex-eval)))

;; (defthm logbitp-when-4vec-[=-svex-eval-1
;;   (implies (and (syntaxp (not (equal env ''nil)))
;;                 (case-split (not (logbitp n (4vec->upper (svex-xeval b))))))
;;            (and (equal (logbitp n (4vec->upper (svex-eval b env)))
;;                        (logbitp n (4vec->upper (svex-xeval b))))
;;                 (equal (logbitp n (4vec->lower (svex-eval b env)))
;;                        (logbitp n (4vec->lower (svex-xeval b))))))
;;   :hints(("Goal" :in-theory (enable logbitp-when-4vec-[=-svex-eval))))

;; (defthm logbitp-when-4vec-[=-svex-eval-2
;;   (implies (and (syntaxp (not (equal env ''nil)))
;;                 (case-split (logbitp n (4vec->lower (svex-xeval b)))))
;;            (and (equal (logbitp n (4vec->upper (svex-eval b env)))
;;                        (logbitp n (4vec->upper (svex-xeval b))))
;;                 (equal (logbitp n (4vec->lower (svex-eval b env)))
;;                        (logbitp n (4vec->lower (svex-xeval b))))))
;;   :hints(("Goal" :in-theory (enable logbitp-when-4vec-[=-svex-eval))))

(define 4vec-bitand-mask ((mask 4vmask-p)
                          (x svex-p)
                          (y svex-p))
  (logand
   (mbe :logic (4vmask-fix mask) :exec mask)
   (logior
    (4vec->lower (svex-xeval x))
    (4vec->lower (svex-xeval y))
    (4vec->upper (svex-xeval y))
    (lognot (4vec->upper (svex-xeval x))))))

(def-svmask bitand (x y)
  (b* ((xval (svex-xeval x))
       (yval (svex-xeval y))
       (mask mask))
    (list (4vec-bitand-mask mask x y)
          (4vec-bitand-mask mask y x)))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  3vec-fix
                                  3vec-bitand
                                  4vec-bitand
                                  4veclist-nth
                                  4vec-bitand-mask))))
          (bitops::logbitp-reasoning
           :add-hints (:in-theory (enable* logbitp-when-4vec-[=-svex-eval-strong)))
          (and stable-under-simplificationp
               '(:bdd (:vars nil)))))

(define 4vec-bit?-y-mask ((mask 4vmask-p)
                          (x svex-p))
  (logand
   (mbe :logic (4vmask-fix mask) :exec mask)
   (let ((xval (svex-xeval x)))
     (logior (4vec->upper xval)
             (4vec->lower xval)))))

(define 4vec-bit?-z-mask ((mask 4vmask-p)
                          (x svex-p))
  (logand
   (mbe :logic (4vmask-fix mask) :exec mask)
   (let ((xval (svex-xeval x)))
     (logior (lognot (4vec->upper xval))
             (lognot (4vec->lower xval))))))

;; BOZO something like this should work
;; (define 4vec-bit?-x-mask ((mask 4vmask-p)
;;                           (y svex-p)
;;                           (z svex-p))
;;   (logand
;;    (mbe :logic (4vmask-fix mask) :exec mask)
;;    (b* ((yval (svex-xeval y))
;;         (zval (svex-xeval z))
;;         ((4vec yval))
;;         ((4vec zval)))
;;      (lognot
;;       (logand
;;        ;; y is not x
;;        (logior (lognot yval.upper) yval.lower)
;;        ;; y equals z
;;        (logeqv yval.upper zval.upper)
;;        (logeqv yval.lower zval.lower))))))


(def-svmask bit? (x y z)
  (b* ((xval (svex-xeval x))
       (mask mask))
    (list mask ;; (4vec-bit?-x-mask mask y z)
          (4vec-bit?-y-mask mask x)
          (4vec-bit?-z-mask mask x)))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  3vec-fix
                                  3vec-bit?
                                  4vec-bit?
                                  4veclist-nth
                                  ;; 4vec-bit?-x-mask
                                  4vec-bit?-y-mask
                                  4vec-bit?-z-mask))))
          (bitops::logbitp-reasoning
           :add-hints (:in-theory (enable* logbitp-when-4vec-[=-svex-eval-strong)))
          (and stable-under-simplificationp
               '(:bdd (:vars nil)))
          ))


(def-svmask resand (x y)
  (b* ((xval (svex-xeval x))
       (yval (svex-xeval y))
       (mask mask))
    (list (4vec-bitand-mask mask x y)
          (4vec-bitand-mask mask y x)))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  3vec-fix
                                  4vec-resand
                                  4veclist-nth
                                  4vec-bitand-mask))))
          (bitops::logbitp-reasoning
           :add-hints (:in-theory (enable* logbitp-when-4vec-[=-svex-eval-strong)))
          (and stable-under-simplificationp
               '(:bdd (:vars nil)))))


(define 4vec-bitor-mask ((mask 4vmask-p)
                            (x svex-p)
                            (y svex-p))
  (logand
   (mbe :logic (4vmask-fix mask) :exec mask)
   (logior
    (4vec->lower (svex-xeval x))
    (lognot (4vec->lower (svex-xeval y)))
    (lognot (4vec->upper (svex-xeval y)))
    (lognot (4vec->upper (svex-xeval x))))))


(def-svmask bitor (x y)
  (b* ((xval (svex-xeval x))
       (yval (svex-xeval y))
       (mask mask))
    (list (4vec-bitor-mask mask x y)
          (4vec-bitor-mask mask y x)))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  3vec-fix
                                  3vec-bitor
                                  4vec-bitor
                                  4veclist-nth
                                  4vec-bitor-mask))))
          (bitops::logbitp-reasoning
           :add-hints (:in-theory (enable* logbitp-when-4vec-[=-svex-eval-strong)))
          (and stable-under-simplificationp
               '(:bdd (:vars nil)))))



(def-svmask resor (x y)
  (b* ((xval (svex-xeval x))
       (yval (svex-xeval y))
       (mask mask))
    (list (4vec-bitor-mask mask x y)
          (4vec-bitor-mask mask y x)))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  3vec-fix
                                  4vec-resor
                                  4veclist-nth
                                  4vec-bitor-mask))))
          (bitops::logbitp-reasoning
           :add-hints (:in-theory (enable* logbitp-when-4vec-[=-svex-eval-strong)))
          (and stable-under-simplificationp
               '(:bdd (:vars nil)))))

(define 4vec-bitxor-mask ((mask 4vmask-p)
                            (x svex-p)
                            (y svex-p))
  (logand
   (mbe :logic (4vmask-fix mask) :exec mask)
   (logior
    (4vec->lower (svex-xeval x))
    (lognot (4vec->lower (svex-xeval y)))
    (4vec->upper (svex-xeval y))
    (lognot (4vec->upper (svex-xeval x))))))


(def-svmask bitxor (x y)
  (b* ((xval (svex-xeval x))
       (yval (svex-xeval y))
       (mask mask))
    (list (4vec-bitxor-mask mask x y)
          (4vec-bitxor-mask mask y x)))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  3vec-fix
                                  4vec-bitxor
                                  4veclist-nth
                                  4vec-bitxor-mask))))
          (bitops::logbitp-reasoning
           :add-hints (:in-theory (enable* logbitp-when-4vec-[=-svex-eval-strong)))
          (and stable-under-simplificationp
               '(:bdd (:vars nil)))))

(def-svmask res (x y)
  (list mask
        mask)
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth
                                    4vec-mask
                                    4vec-res))
          (bitops::logbitp-reasoning)
          (and stable-under-simplificationp
               '(:bdd (:vars nil)))))

(def-svmask override (x y)
  (list mask
        mask)
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth
                                    4vec-mask
                                    4vec-override))
         (bitops::logbitp-reasoning)
         (and stable-under-simplificationp
              '(:bdd (:vars nil)))))


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

(def-svmask uand (x)
  (list -1)
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth))))

(def-svmask uor (x)
  (list -1)
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth))))

(def-svmask uxor (x)
  (list -1)
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth))
         (and stable-under-simplificationp
              '(:in-theory (e/d (4vec-mask
                                 2vec-p
                                 4vec-parity
                                 3vec-fix)
                                (bitops::logior-equal-0))
                :cases ((logbitp 0 (4vmask-fix mask)))))
         (bitops::logbitp-reasoning)))

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

(def-svmask ? (x y z)
  (b* (((when (4vmask-empty mask))
        (list 0 0 0))
       (xval (svex-xeval x))
       ((4vec xv) (3vec-fix xval))
       ((when (eql xv.upper 0))
        (list -1 0 mask))
       ((when (not (eql xv.lower 0)))
        (list -1 mask 0)))
    (list -1 mask mask))
  :hints(("Goal" :in-theory (enable svex-apply
                                    4veclist-nth))
         (and stable-under-simplificationp
              '(:in-theory (enable 4vec-?)))
         (and stable-under-simplificationp
              '(:in-theory (e/d (4vec-mask
                                 2vec-p
                                 4vec-?
                                 3vec-?
                                 3vec-fix)
                                (bitops::logior-equal-0))
                :use ((:instance ?-check-lemma-1
                       (x (svex-eval (car args) nil))
                       (y (svex-eval (car args) env)))
                      (:instance ?-check-lemma-2
                       (x (svex-eval (car args) nil))
                       (y (svex-eval (car args) env)))
                      )))
          (bitops::logbitp-reasoning)
          (and stable-under-simplificationp
               '(:bdd (:vars nil))))
  :otf-flg t)

(local (in-theory (enable SVEX-EVAL-WHEN-2VEC-P-OF-MINVAL
                          4vmask-all-or-none)))

(local (defthm equal-of-svex-eval
         (equal (equal (svex-eval x env) y)
                (and (4vec-p y)
                     (equal (4vec->upper (svex-eval x env))
                            (4vec->upper y))
                     (equal (4vec->lower (svex-eval x env))
                            (4vec->lower y))))))

(def-svmask zerox (n x)
  (list (4vmask-all-or-none mask)
        (let ((nval (svex-xeval n)))
          (if (4vec-index-p nval)
              (loghead (2vec->val nval)
                       mask)
            (4vmask-all-or-none mask))))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  4veclist-nth
                                  4vec-zero-ext))))
          (bitops::logbitp-reasoning)
          (and stable-under-simplificationp
               '(:bdd (:vars nil)))))

(define sign-ext-mask ((mask 4vmask-p) (n natp))
  (logior
   (loghead n mask)
   (if (equal 0 (logtail n mask))
       0
     (ash 1 (- (lnfix n) 1)))))

(local (in-theory (disable acl2::logext-identity
                           bitops::loghead-identity
                           bitops::logbitp-when-bit
                           acl2::nfix-when-not-natp)))

(local (defthm nfix-of-decr-gt
         (implies (natp x)
                  (equal (< (nfix (+ -1 x)) x)
                         (posp x)))
         :hints(("Goal" :in-theory (enable nfix)))))

(def-svmask signx (n x)
  (list (4vmask-all-or-none mask)
        (let ((nval (svex-xeval n)))
          (if (4vec-index-p nval)
              (sign-ext-mask mask
                             (2vec->val nval))
            (4vmask-all-or-none mask))))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  4veclist-nth
                                  4vec-sign-ext
                                  4vec-index-p
                                  sign-ext-mask))))
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
  (b* (((when (4vmask-empty mask))
        (list 0 0 0))
       (nval (svex-xeval n))
       (mask mask)
       ((when (4vec-index-p nval))
        (b* ((n (2vec->val nval)))
          (list -1
                (loghead n mask)
                (logtail n mask)))))
    (list -1 -1 -1))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  4veclist-nth
                                  4vec-concat))))
          (bitops::logbitp-reasoning)))

(def-svmask rsh (n x)
  (b* (((when (4vmask-empty mask))
        (list 0 0 0))
       (nval (svex-xeval n))
       (mask mask)
       ((when (2vec-p nval))
        (b* ((n (2vec->val nval)))
          (list -1
                (ash mask n)))))
    (list -1 -1))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  4veclist-nth
                                  4vec-rsh))
                 :cases ((<= 0 (2vec->val (svex-xeval (car args)))))))
          (bitops::logbitp-reasoning)))

(def-svmask lsh (n x)
  (b* (((when (4vmask-empty mask))
        (list 0 0 0))
       (nval (svex-xeval n))
       (mask mask)
       ((when (2vec-p nval))
        (b* ((n (2vec->val nval)))
          (list -1
                (ash mask (- n))))))
    (list -1 -1))
  :hints (("Goal" :in-theory (e/d (svex-apply
                                   4veclist-nth)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-apply
                                  4vec-mask
                                  4veclist-nth
                                  4vec-lsh))
                 :cases ((<= 0 (2vec->val (svex-xeval (car args)))))))
          (bitops::logbitp-reasoning)))

(local (in-theory (disable equal-of-svex-eval)))

(def-svmask + (x y)
  (list -1 -1)
  :hints(("Goal" :in-theory (enable svex-apply 4veclist-nth))))

(def-svmask u- (x y)
  (list -1)
  :hints(("Goal" :in-theory (enable svex-apply 4veclist-nth))))

(def-svmask b- (x y)
  (list -1 -1)
  :hints(("Goal" :in-theory (enable svex-apply 4veclist-nth))))

(def-svmask * (x y)
  (list -1 -1)
  :hints(("Goal" :in-theory (enable svex-apply 4veclist-nth))))

(def-svmask / (x y)
  (list -1 -1)
  :hints(("Goal" :in-theory (enable svex-apply 4veclist-nth))))

(def-svmask % (x y)
  (list -1 -1)
  :hints(("Goal" :in-theory (enable svex-apply 4veclist-nth))))

(def-svmask < (x y)
  (list -1 -1)
  :hints(("Goal" :in-theory (enable svex-apply 4veclist-nth))))

(def-svmask == (x y)
  (list -1 -1)
  :hints(("Goal" :in-theory (enable svex-apply 4veclist-nth))))

(def-svmask clog2 (x)
  (list -1)
  :hints(("Goal" :in-theory (enable svex-apply 4veclist-nth))))


(encapsulate nil
  (local (in-theory (disable svex-eval-when-2vec-p-of-minval
                             svex-eval-when-fncall
                             bitops::logbitp-when-bit
                             bitops::logxor-natp-type-2)))



  (def-svmask ==? (a b)
    (b* (((4vec bval) (svex-xeval b))
         (b-is-z (logand (lognot bval.upper) bval.lower)))
      (list (lognot b-is-z) -1))
    :hints(("Goal" :in-theory (e/d (svex-apply
                                    4veclist-nth))
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:in-theory (e/d (svex-apply 4veclist-nth
                                              4vec-wildeq 3vec-reduction-and
                                              3vec-bitor 3vec-bitnot 4vec-bitxor
                                              4vec-mask bool->vec 4vec-[=)
                                  (svex-eval-monotonic svex-eval-gte-empty-env))
                  :use ((:instance svex-eval-gte-empty-env
                         (x (car args)))
                        (:instance svex-eval-gte-empty-env
                         (x (cadr args))))))
           (bitops::logbitp-reasoning :passes 2
                                    :simp-hint nil
                                    :add-hints nil)
           (and stable-under-simplificationp
                '(:bdd (:vars nil)))))

  (def-svmask ==?? (a b)
    (b* (((4vec bval) (svex-xeval b))
         ((4vec aval) (svex-xeval a))
         (b-is-z (logand (lognot bval.upper) bval.lower))
         (a-is-z (logand (lognot aval.upper) aval.lower)))
      (list (logior a-is-z (lognot b-is-z))
            (logior b-is-z (lognot a-is-z))))
    :hints(("Goal" :in-theory (e/d (svex-apply
                                    4veclist-nth))
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:in-theory (e/d (svex-apply 4veclist-nth
                                              4vec-symwildeq 3vec-reduction-and
                                              3vec-bitor 3vec-bitnot 4vec-bitxor
                                              4vec-mask bool->vec 4vec-[=)
                                  (svex-eval-monotonic svex-eval-gte-empty-env))
                  :use ((:instance svex-eval-gte-empty-env
                         (x (car args)))
                        (:instance svex-eval-gte-empty-env
                         (x (cadr args))))))
           (bitops::logbitp-reasoning :passes 2
                                    :simp-hint nil
                                    :add-hints nil)
           (and stable-under-simplificationp
                '(:bdd (:vars nil))))))



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
                                     4veclist-nth)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (svex-apply
                                    4vec-mask
                                    4veclist-nth
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
  (if (atom op-table)
      '((otherwise (svmask-for-unknown-function mask args)))
    (cons (let* ((sym (caar op-table))
                 (maskfn (intern-in-package-of-symbol
                          (concatenate 'string "SVMASK-FOR-" (symbol-name sym))
                          (if (equal (symbol-package-name sym) "COMMON-LISP")
                              'acl2::foo
                            sym))))
            `(,sym (,maskfn mask args)))
          (svex-argmasks-cases-fn (cdr op-table)))))

(defmacro svex-argmasks-cases (fn)
  `(case ,fn . ,(svex-argmasks-cases-fn *svex-op-table*)))




(define svex-argmasks ((mask 4vmask-p)
                       (fn fnsym-p)
                       (args svexlist-p))
  :parents (4vmask)
  :short "Computing the care masks of arguments to a function call given the
care mask for the function call."
  :returns (m (and (4vmasklist-p m)
                   (equal (len m) (len args))))
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
