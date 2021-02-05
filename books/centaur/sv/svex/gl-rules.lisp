; Centaur SV Hardware Verification Tutorial
; Copyright (C) 2016 Centaur Technology
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


(in-package "SV")


(include-book "centaur/gl/def-gl-rewrite" :dir :system)
(include-book "centaur/gl/ctrex-utils" :dir :system)
(include-book "symbolic")
(include-book "../svtv/fsm")

(local (include-book "centaur/bitops/ihsext-basics" :dir :System))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(define gl-non-term-p (x)
  (not (and (consp x)
            (or (eq (car x) :g-var)
                (eq (car x) :g-apply)
                (eq (car x) :g-ite)))))

(define gl-term-p (x)
  (and (consp x)
       (or (eq (car x) :g-var)
           (eq (car x) :g-apply))))

(gl::gl-set-uninterpreted ifix)

(gl::def-gl-rewrite 4vec-boolmaskp-of-ifix
  (4vec-boolmaskp (ifix x) mask)
  :hints(("Goal" :in-theory (enable 4vec-boolmaskp
                                    4vec->lower
                                    4vec->upper))))

(gl::def-gl-rewrite ifix-of-non-term
  (implies (syntaxp (gl-non-term-p x))
           (equal (ifix x)
                  (if (integerp x) x 0))))

(gl::def-gl-rewrite integerp-of-ifix
  (integerp (ifix x)))

(gl::def-gl-rewrite 4vec-fix-of-ifix
  (equal (4vec-fix (ifix x)) (ifix x))
  :hints(("Goal" :in-theory (enable 4vec-fix
                                    4vec-p))))

(gl::def-gl-rewrite 4vec->upper-of-ifix
  (equal (4vec->upper (ifix x)) (ifix x))
  :hints(("Goal" :in-theory (enable 4vec->upper
                                    4vec-p))))

(gl::def-gl-rewrite 4vec->lower-of-ifix
  (equal (4vec->lower (ifix x)) (ifix x))
  :hints(("Goal" :in-theory (enable 4vec->lower
                                    4vec-p))))


(gl::def-gl-rewrite 4vec->upper-of-4vec-fix
  (equal (4vec->upper (4vec-fix x))
         (4vec->upper x)))

(gl::def-gl-rewrite 4vec->lower-of-4vec-fix
  (equal (4vec->lower (4vec-fix x))
         (4vec->lower x)))

(gl::def-gl-rewrite 4vec->lower-of-non-term
  (implies (syntaxp (gl-non-term-p x))
           (equal (4vec->lower x)
                  (if (consp x)
                      (ifix (cdr x))
                    (if (integerp x)
                        x
                      0))))
  :hints(("Goal" :in-theory (enable 4vec->lower))))

(gl::def-gl-rewrite 4vec->upper-of-non-term
  (implies (syntaxp (gl-non-term-p x))
           (equal (4vec->upper x)
                  (if (consp x)
                      (ifix (car x))
                    (if (integerp x)
                        x
                      -1))))
  :hints(("Goal" :in-theory (enable 4vec->upper))))

(gl::def-gl-rewrite ifix-of-4vec->upper
  (equal (ifix (4vec->upper x))
         (4vec->upper x)))

(gl::def-gl-rewrite ifix-of-4vec->lower
  (equal (ifix (4vec->lower x))
         (4vec->lower x)))

;; (gl::def-gl-rewrite 4vec-fix-of-non-term
;;   (implies (syntaxp (not (and (consp x)
;;                               (or (eq (car x) :g-var)
;;                                   (eq (car x) :g-apply)))))
;;            (equal (4vec-fix x)
;;                   (if (consp x)
;;                       (4vec (ifix (car x))
;;                                 (ifix (cdr x)))
;;                     (if (integerp x)
;;                         x
;;                       (4vec-x)))))
;;   :hints(("Goal" :in-theory (enable 4vec-fix))))

;; (gl::def-gl-rewrite 4vec-of-non-term
;;   (implies (syntaxp (and (not (and (consp upper)
;;                                    (or (eq (car upper) :g-var)
;;                                        (eq (car upper) :g-apply))))
;;                          (not (and (consp lower)
;;                                    (or (eq (car lower) :g-var)
;;                                        (eq (car lower) :g-apply))))))
;;            (equal (4vec upper lower)
;;                   (B* (((THE INTEGER UPPER)
;;                         (LIFIX UPPER))
;;                        ((THE INTEGER LOWER)
;;                         (LIFIX LOWER)))
;;                     (IF (EQL UPPER LOWER)
;;                         UPPER (CONS UPPER LOWER)))))
;;   :hints(("Goal" :in-theory (enable 4vec))))

(gl::add-gl-rewrite 4vec-fix-of-4vec)
(gl::add-gl-rewrite 4vec->upper-of-4vec)
(gl::add-gl-rewrite 4vec->lower-of-4vec)


(gl::def-gl-rewrite equal-of-4vec-1
  (equal (equal (4vec a b) c)
         (and (4vec-p c)
              (equal (4vec->upper c) (ifix a))
              (equal (4vec->lower c) (ifix b)))))

(gl::def-gl-rewrite equal-of-4vec-2
  (equal (equal c (4vec a b))
         (and (4vec-p c)
              (equal (4vec->upper c) (ifix a))
              (equal (4vec->lower c) (ifix b)))))

(gl::add-gl-rewrite 4vec-p-of-4vec)
(gl::add-gl-rewrite 4vec-p-of-4vec-fix)

(gl::def-gl-rewrite 4vec-p-of-integer
  (implies (and (syntaxp (not (and (consp x)
                                   (eq (car x) :g-call)
                                   (eq (gl::g-call->fn x) '4vec))))
                (integerp x))
           (4vec-p x))
  :hints(("Goal" :in-theory (enable 4vec-p))))

(gl::def-gl-rewrite 4vec-p-of-non-term
  (implies (syntaxp (gl-non-term-p x))
           (equal (4vec-p x)
                  (OR (INTEGERP X)
                      (AND (CONSP X)
                           (INTEGERP (CAR X))
                           (INTEGERP (CDR X))
                           (NOT (EQUAL (CAR X) (CDR X)))))))
  :hints(("Goal" :in-theory (enable 4vec-p))))


(gl::gl-set-uninterpreted 4vec->lower)
(gl::gl-set-uninterpreted 4vec->upper)
(gl::gl-set-uninterpreted 4vec-fix)
(gl::gl-set-uninterpreted 4vec)
(gl::gl-set-uninterpreted 4vec-p)

(gl::def-gl-rewrite ifix-true
  (ifix x))

(define logbitp0 ((x integerp))
  (logbitp 0 x)
  ///
  (gl::def-gl-rewrite split-logbitp-0
    (implies (syntaxp (gl-term-p x))
             (equal (logbitp 0 x)
                    (if (logbitp0 x) t nil))))
  (gl::Def-gl-rewrite logbitp0-of-number
    (implies (syntaxp (gl-non-term-p x))
             (equal (logbitp0 x)
                    (logbitp 0 x))))
  (gl::def-gl-rewrite logbitp0-of-if
    (equal (logbitp0 (if a b c))
           (if a (logbitp0 b) (logbitp0 c))))

  (gl::def-gl-rewrite logbitp-of-if
    (equal (logbitp n (if a b c))
           (if a (logbitp n b) (logbitp n c))))

  (gl::def-gl-rewrite logbitp0-of-ifix
    (equal (logbitp0 (ifix x)) (logbitp0 x)))
  (gl::gl-set-uninterpreted logbitp0))



;; below this may not be necessary
(gl::gl-set-uninterpreted logcdr)

(gl::def-gl-rewrite logcdr-of-ifix
  (equal (logcdr (ifix x)) (logcdr x)))

(gl::def-gl-rewrite logcdr-of-number
  (implies (syntaxp (gl-non-term-p x))
           (equal (logcdr x) (ash x -1)))
  :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs))))


(gl::def-gl-rewrite integerp-of-logcdr
  (integerp (logcdr x)))


(gl::gl-set-uninterpreted logtail)

(gl::def-gl-rewrite logtail-of-ifix
  (equal (logtail n (ifix x))
         (logtail n x)))

(gl::def-gl-rewrite integerp-of-logtail
  (integerp (logtail n x)))

(gl::def-gl-rewrite logtail-of-number
  (implies (syntaxp (and (gl-non-term-p x)
                         (gl-non-term-p n)))
           (equal (logtail n x)
                  (ash x (- (nfix n))))))




(gl::def-gl-rewrite logcdr-of-logtail
  (equal (logcdr (logtail n x))
         (logtail (+ 1 (nfix n)) x))
  :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs))))

(gl::def-gl-rewrite logcdr-of-logcdr
  (equal (logcdr (logcdr x))
         (logtail 2 x))
  :hints(("Goal" :expand ((logtail 2 x) (logtail 1 (logcdr x))))))

(gl::def-gl-rewrite logtail-of-logtail
  (equal (logtail n (logtail m x))
         (logtail (+ (nfix n) (nfix m)) x)))


(gl::def-gl-rewrite equal-of-const-and-term
  (implies (and (syntaxp (and (integerp c)
                              (not (or (eql c 0) (eql c -1)))
                              (consp x)
                              (or (eq (car x) :g-var)
                                  (eq (car x) :g-apply))))
                (integerp c))
           (and (equal (equal c x)
                       (and (integerp x)
                            (equal (logbitp 0 c) (logbitp 0 x))
                            (equal (logcdr c) (logcdr x))))
                (equal (equal x c)
                       (and (integerp x)
                            (equal (logbitp 0 c) (logbitp 0 x))
                            (equal (logcdr c) (logcdr x)))))))

(gl::def-gl-rewrite logbitp-of-greater
  (implies (syntaxp (posp n))
           (equal (logbitp n x)
                  (if (logbitp0 (logtail n x)) t nil)))
  :hints(("Goal" :in-theory (enable logbitp0))))

(gl::def-gl-rewrite logapp-expand
  (implies (syntaxp (and (integerp n)
                         (not (or (atom x) (eq (car x) :g-integer)))))
           (equal (logapp n x y)
                  (if (zp n)
                      (ifix y)
                    (logcons (if (logbitp0 x) 1 0)
                             (logapp (1- n) (logcdr x) y)))))
  :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs logbitp0))))

(gl::def-glcp-ctrex-rewrite
  ((logbitp0 x) b)
  (x (logcons (bool->bit b) (logcdr x))))

(gl::def-glcp-ctrex-rewrite
  ((logbitp0 (logcdr x)) b)
  (x (logcons (logcar x) (logcons (bool->bit b) (logcdr (logcdr x))))))

(gl::def-glcp-ctrex-rewrite
  ((logbitp0 (logtail n x)) b)
  (x (logapp n x (logcons (bool->bit b) (logtail (1+ (nfix n)) x))))
  :test (quotep n))

;; (gl::def-glcp-ctrex-rewrite
;;   ((logtail n x) y)
;;   (x (logapp n x y))
;;   :test (quotep n))

;; (gl::def-glcp-ctrex-rewrite
;;   ((logcdr x) y)
;;   (x (logcons (logcar x) y)))

(gl::def-glcp-ctrex-rewrite
  ((ifix x) y)
  (x y))

(gl::def-glcp-ctrex-rewrite
  ((equal 0 x) nil)
  (x (logior 1 x)))

(gl::def-glcp-ctrex-rewrite
  ((4vec->upper x) y)
  (x (make-4vec :lower (4vec->lower x) :upper y)))

(gl::def-glcp-ctrex-rewrite
  ((4vec->lower x) y)
  (x (make-4vec :lower y :upper (4vec->upper x))))

(gl::gl-set-uninterpreted svex-env-fix)

(gl::def-gl-rewrite svex-env-fix-of-svex-env-fix
  (equal (svex-env-fix (svex-env-fix x))
         (svex-env-fix x)))

(gl::def-glcp-ctrex-rewrite
  ((svex-env-fix x) y)
  (x (make-fast-alist y)))

(define svex-env-fix-gl-non-term ((x svex-env-p))
  :returns (fix (equal fix (svex-env-fix x))
                :hints(("Goal" :in-theory (enable svex-env-fix))))
  (if (atom x)
      nil
    (if (and (consp (car x))
             (svar-p (caar x)))
        (cons (cons (caar x) (4vec-fix (cdar x)))
              (svex-env-fix (cdr x)))
      (svex-env-fix (cdr x)))))

(gl::Def-gl-rewrite svex-env-fix-of-non-term-gl2
  (implies (syntaxp (not (and (consp x)
                              (or (eq (car x) :g-var)
                                  (eq (car x) :g-apply)
                                  (eq (car x) :g-ite)))))
           (equal (svex-env-fix x)
                  (svex-env-fix-gl-non-term x)))
  :hints(("Goal" :in-theory (enable svex-env-fix))))

(gl::def-gl-rewrite alist-keys-of-svex-env-fix
  (equal (alist-keys (svex-env-fix x))
         (svarlist-filter (alist-keys x)))
  :hints(("Goal" :in-theory (enable alist-keys svex-env-fix svarlist-filter))))

(gl::gl-set-uninterpreted svex-env-lookup)

(gl::def-gl-rewrite svex-env-lookup-when-non-term
  (implies (syntaxp (not (and (consp env)
                              (or (eq (car env) :g-var)
                                  (eq (car env) :g-apply)))))
           (equal (svex-env-lookup x env)
                  (4vec-fix (cdr (hons-get (svar-fix x) (make-fast-alist env))))))
  :hints(("Goal" :in-theory (enable svex-env-lookup))))

(gl::def-glcp-ctrex-rewrite
  ((svex-env-lookup var env) val)
  (env (b* ((env (make-fast-alist env)))
         (if (equal (cdr (hons-get var env)) val)
             env
           (hons-acons var val env)))))

(gl::def-glcp-ctrex-rewrite
  ((svex-env-lookup var (svex-env-fix env)) val)
  (env (b* ((env (make-fast-alist env)))
         (if (equal (cdr (hons-get var env)) val)
             env
           (hons-acons var val env)))))

(gl::def-gl-rewrite svex-env-lookup-of-svex-env-fix-gl
  (equal (svex-env-lookup k (svex-env-fix x))
         (svex-env-lookup k x)))

(gl::gl-set-uninterpreted base-fsm-symbolic-env)

(gl::def-gl-rewrite svex-env-extract-when-non-term
  (implies (syntaxp (not (and (consp env)
                              (or (eq (car env) :g-var)
                                  (eq (car env) :g-apply)))))
           (equal (svex-env-extract x env)
                  (svex-env-extract-aux x (make-fast-alist env))))
  :hints(("Goal" :in-theory (enable svex-env-extract svex-env-extract-aux))))

(gl::gl-set-uninterpreted base-fsm-symbolic-env)

(gl::def-gl-rewrite svex-env-fix-of-base-fsm-symbolic-env
  (equal (svex-env-fix (base-fsm-symbolic-env ins vars prev-st))
         (base-fsm-symbolic-env ins vars prev-st)))

(gl::def-glcp-ctrex-rewrite
  ((svex-env-lookup var (base-fsm-symbolic-env ins statevars prev-st)) val)
  (ins (b* ((alist (nth (svex-cycle-var->cycle var) ins))
            (svar (svex-cycle-var->svar var))
            (lookup (hons-get svar alist))
            ((when (hons-equal (cdr lookup) val))
             ins))
         (update-nth (svex-cycle-var->cycle var)
                     (hons-acons svar val alist)
                     ins)))
  :test (and (quotep var)
             (svex-cycle-var-p (unquote var))))

(gl::def-glcp-ctrex-rewrite
  ((svex-env-lookup var (base-fsm-symbolic-env ins statevars prev-st)) val)
  (prev-st (b* ((lookup (hons-get var prev-st))
                ((when (hons-equal (cdr lookup) val)) prev-st))
             (hons-acons var val prev-st)))
  :test (and (quotep var)
             (not (svex-cycle-var-p (unquote var)))))

(gl::def-glcp-ctrex-rewrite
  ((equal a b) t)
  (a b)
  :test (not (quotep a)))

(gl::def-glcp-ctrex-rewrite
  ((equal a b) t)
  (b a)
  :test (not (quotep b)))


(gl::gl-set-uninterpreted 4vec-equiv)
(gl::def-gl-rewrite 4vec-equiv-rewrite
  (equal (4vec-equiv x y)
         (and (equal (4vec->upper x) (4vec->upper y))
              (equal (4vec->lower x) (4vec->lower y))))
  :hints(("Goal" :in-theory (enable equal-of-4vec-fix))))


(defun fast-alist-clean-list (x)
  (if (atom x)
      nil
    (b* ((car (car x))
         (clean (fast-alist-clean (car x))))
      (fast-alist-free car)
      (cons clean (fast-alist-clean-list (cdr x))))))

(define ctrex-clean-envs-rec (var-specs alist)
  :verify-guards nil
  (b* (((when (atom alist)) nil)
       ((cons var val) (car alist))
       (look (assoc var var-specs))
       ((unless look)
        (hons-acons var val (ctrex-clean-envs-rec var-specs (cdr alist))))
       ((when (eq (cdr look) :fast-alist))
        (b* ((cleanval (fast-alist-clean val)))
          (fast-alist-free val)
          (hons-acons var cleanval (ctrex-clean-envs-rec var-specs (cdr alist)))))
       ((when (eq (cdr look) :fast-alist-list))
        (hons-acons var (fast-alist-clean-list val) (ctrex-clean-envs-rec var-specs (cdr alist)))))
    (cw "Unrecognized keyword for ctrex-clean-envs: ~x0~%" (cdr look))
    (hons-acons var val (ctrex-clean-envs-rec var-specs (cdr alist)))))

(define ctrex-clean-envs (var-specs alist)
  :verify-guards nil
  ;; use with something like:
  ;; :ctrex-transform (lambda (x) (ctrex-clean-envs '((ins . :fast-alist-list) (prev-st . :fast-alist))))
  (b* ((alist1  (fast-alist-clean alist))
       (ans (ctrex-clean-envs-rec var-specs alist1)))
    (fast-alist-free alist)
    (fast-alist-free alist1)
    ans))


(define svarlist-has-svex-cycle-var-memo (x)
  :enabled t
  (mbe :logic (svarlist-has-svex-cycle-var x)
       :exec (svarlist-has-svex-cycle-var (ec-call (svarlist-fix x))))
  ///
  (memoize 'svarlist-has-svex-cycle-var-memo))




(local (defthm ENV-LOOKUP-OF-CYCLE-VAR-IN-ENV-ADD-CYCLE-NUM-diff-cycle
         (b* ((ncycle (svex-cycle-var->cycle var)))
           (implies (and (not (equal (nfix cycle) (nfix ncycle)))
                         (svar-p var)
                         (svex-cycle-var-p var))
                    (not (svex-env-boundp var  (svar-alist-add-cycle-num x cycle)))))
         :hints(("Goal" :in-theory (enable svar-alist-add-cycle-num
                                           svex-env-boundp
                                           alist-keys)))))

(local (defthm svex-env-lookup-of-cycle-var-in-non-cycle-env
         (implies (and (not (svarlist-has-svex-cycle-var (alist-keys (svex-env-fix x))))
                       (svex-cycle-var-p var))
                  (equal (svex-env-lookup var x) (4vec-x)))
         :hints(("Goal" :in-theory (enable svex-env-lookup svex-env-fix svarlist-has-svex-cycle-var alist-keys)))))

(local (defthm LOOKUP-IN-SVEX-CYCLE-ENVS-TO-SINGLE-ENV-past-end
         (b* ((cycle (svex-cycle-var->cycle var)))
           (implies (and (>= (- (nfix cycle) (nfix curr-cycle)) (len x))
                         (not (svarlist-has-svex-cycle-var (alist-keys (svex-env-fix rest))))
                         (svar-p var)
                         (svex-cycle-var-p var))
                    (equal (svex-env-lookup var (svex-cycle-envs-to-single-env x curr-cycle rest))
                           (4vec-x))))
         :hints(("Goal" :in-theory (enable svex-cycle-envs-to-single-env)))))


(local (defthm nth-past-len
         (implies (<= (len x) (nfix n))
                  (equal (nth n x) nil))
         :hints(("Goal" :in-theory (enable nth)))))

(local (defthm LOOKUP-IN-SVEX-CYCLE-ENVS-TO-SINGLE-ENV-special
         (b* ((cycle (svex-cycle-var->cycle var))
              (name (svex-cycle-var->svar var)))
           (implies (and (<= (nfix curr-cycle) (nfix cycle))
                         (not (svarlist-has-svex-cycle-var (alist-keys (svex-env-fix rest))))
                         (svar-p var)
                         (svex-cycle-var-p var))
                    (equal (svex-env-lookup var (svex-cycle-envs-to-single-env x curr-cycle rest))
                           (svex-env-lookup name (nth (- (nfix cycle) (nfix curr-cycle)) x)))))
         :hints (("goal" :use ((:instance lookup-in-svex-cycle-envs-to-single-env
                                (cycle (svex-cycle-var->cycle var))
                                (name (svex-cycle-var->svar var)))
                               (:instance EQUAL-OF-SVEX-CYCLE-VAR
                                (cvar var)
                                (cycle (svex-cycle-var->cycle var))
                                (v (svex-cycle-var->svar var))))
                  :in-theory (disable lookup-in-svex-cycle-envs-to-single-env)
                  :cases ((< (- (svex-cycle-var->cycle var) (nfix curr-cycle)) (len x)))))))

(define svarlist-member-for-svex-env-lookup-rule ((v svar-p)
                         (x svarlist-p))
  :enabled t
  (member-equal (svar-fix v) (svarlist-fix x))
  ///
  (memoize 'svarlist-member-for-svex-env-lookup-rule))

(gl::def-gl-rewrite nth-redef
  (implies (syntaxp (natp n))
           (equal (nth n x)
                  (if (zp n)
                      (car x)
                    (nth (1- (nfix n)) (cdr x))))))


#!sv
(local (defthm svarlist-has-svex-cycle-var-of-intersection
         (implies (not (svarlist-has-svex-cycle-var vars))
                  (not (svarlist-has-svex-cycle-var (intersection$ (svarlist-fix vars) keys))))
         :hints(("Goal" :in-theory (enable intersection$ svarlist-fix svarlist-has-svex-cycle-var)))))

(gl::def-gl-rewrite svex-env-lookup-of-base-fsm-symbolic-env
  (implies (and (syntaxp (and (gl::general-concretep var)
                              (gl::general-concretep statevars)))
                (not (svarlist-has-svex-cycle-var-memo statevars))
                (svar-p var))
           (equal (svex-env-lookup var (base-fsm-symbolic-env ins statevars prev-st))
                  (if (svex-cycle-var-p var)
                      (svex-env-lookup (svex-cycle-var->svar var)
                                       (nth (svex-cycle-var->cycle var) ins))
                    (if (svarlist-member-for-svex-env-lookup-rule var statevars)
                        (svex-env-lookup var prev-st)
                      (4vec-x))))))


(gl::def-glcp-ctrex-rewrite
  ((car x) val)
  (x (cons val (cdr x))))

(gl::def-glcp-ctrex-rewrite
  ((cdr x) val)
  (x (cons (car x) val)))

;; For generating counterexamples...
(memoize 'sv::svex-env-p)


(gl::def-gl-rewrite ash-minus1-on-term
  (implies (syntaxp (not (gl-non-term-p x)))
           (equal (ash x -1)
                  (logcdr x)))
  :hints(("Goal" :in-theory (enable bitops::logtail**))))




(gl::def-gl-rewrite 4vec->upper-of-integer
  (implies (and (syntaxp (not (and (consp x)
                                   (eq (car x) :g-call)
                                   (eq (gl::g-call->fn x) '4vec))))
                (integerp x))
           (equal (4vec->upper x) x))
  :hints(("Goal" :in-theory (enable 4vec->upper 4vec-p))))
(gl::def-gl-rewrite 4vec->lower-of-integer
  (implies (and (syntaxp (not (and (consp x)
                                   (eq (car x) :g-call)
                                   (eq (gl::g-call->fn x) '4vec))))
                (integerp x))
           (equal (4vec->lower x) x))
  :hints(("Goal" :in-theory (enable 4vec->lower 4vec-p))))

(gl::add-gl-rewrite integerp-of-4vec->upper)
(gl::add-gl-rewrite integerp-of-4vec->lower)
(gl::def-gl-rewrite integerp-of-4vec
  (equal (integerp (4vec upper lower))
         (equal (ifix upper) (ifix lower)))
  :hints(("Goal" :in-theory (enable 4vec))))

(gl::def-gl-rewrite 4vec-fix-of-non-4vec-call
  (implies (syntaxp (not (and (consp x)
                              (eq (car x) :g-call)
                              (eq (gl::g-call->fn x) '4vec))))
           (equal (4vec-fix x)
                  (4vec (4vec->upper x)
                        (4vec->lower x)))))



(gl::def-gl-rewrite equal-of-4vecs
  (and (equal (equal (4vec x y) z)
              (and (4vec-p z)
                   (equal (ifix x) (4vec->upper z))
                   (equal (ifix y) (4vec->lower z))))
       (equal (equal z (4vec x y))
              (and (4vec-p z)
                   (equal (ifix x) (4vec->upper z))
                   (equal (ifix y) (4vec->lower z))))))

(gl::def-gl-rewrite 4vec-of-self
  (equal (4vec x x) (ifix x))
  :hints(("Goal" :in-theory (enable 4vec-p 4vec->upper 4vec->lower))))



(gl::def-gl-rewrite logbitp0-of-4vec
  (equal (logbitp0 (4vec x y))
         (if (equal (ifix x) (ifix y))
             (logbitp0 x)
           nil))
  :hints(("Goal" :in-theory (enable 4vec logbitp0 logbitp))))

(gl::def-gl-rewrite logcdr-of-4vec
  (equal (logcdr (4vec x y))
         (if (equal (ifix x) (ifix y))
             (logcdr x)
           0))
  :hints(("Goal" :in-theory (enable 4vec logcdr))))

(gl::def-gl-rewrite logtail-of-4vec
  (equal (logtail n (4vec x y))
         (if (equal (ifix x) (ifix y))
             (logtail n x)
           0))
  :hints(("Goal" :in-theory (enable 4vec logtail))))

(gl::def-gl-rewrite lognot-of-4vec
  (equal (lognot (4vec x y))
         (if (equal (ifix x) (ifix y))
             (lognot x)
           -1))
  :hints(("Goal" :in-theory (enable 4vec lognot))))

(gl::def-gl-rewrite plus-of-4vec-1
  (equal (+ (4vec x y) z)
         (if (equal (ifix x) (ifix y))
             (+ (ifix x) z)
           (+ 0 z)))
  :hints(("Goal" :in-theory (enable 4vec))))

(gl::def-gl-rewrite plus-of-4vec-2
  (equal (+ z (4vec x y))
         (if (equal (ifix x) (ifix y))
             (+ z (ifix x))
           (+ z 0)))
  :hints(("Goal" :in-theory (enable 4vec))))

(gl::def-gl-rewrite minus-of-4vec
  (equal (- (4vec x y))
         (if (equal (ifix x) (ifix y))
             (- (ifix x))
           0))
  :hints(("Goal" :in-theory (enable 4vec))))

(gl::def-gl-rewrite <-of-4vec-1
  (equal (< (4vec x y) z)
         (if (equal (ifix x) (ifix y))
             (< (ifix x) z)
           (< 0 z)))
  :hints(("Goal" :in-theory (enable 4vec))))

(gl::def-gl-rewrite <-of-4vec-2
  (equal (< z (4vec x y))
         (if (equal (ifix x) (ifix y))
             (< z (ifix x))
           (< z 0)))
  :hints(("Goal" :in-theory (enable 4vec))))

(gl::def-gl-rewrite ifix-of-4vec
  (equal (ifix (4vec x y))
         (if (equal (ifix x) (ifix y))
             (ifix x)
           0))
  :hints(("Goal" :in-theory (enable 4vec))))
