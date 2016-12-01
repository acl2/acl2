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

(local (include-book "centaur/bitops/ihsext-basics" :dir :System))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(define gl-non-term-p (x)
  (not (and (consp x)
            (or (eq (car x) :g-var)
                (eq (car x) :g-apply)))))

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
  (implies (syntaxp (not (and (consp x)
                              (or (eq (car x) :g-var)
                                  (eq (car x) :g-apply)))))
           (equal (4vec->lower x)
                  (if (consp x)
                      (ifix (cdr x))
                    (if (integerp x)
                        x
                      0))))
  :hints(("Goal" :in-theory (enable 4vec->lower))))

(gl::def-gl-rewrite 4vec->upper-of-non-term
  (implies (syntaxp (not (and (consp x)
                              (or (eq (car x) :g-var)
                                  (eq (car x) :g-apply)))))
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

(gl::def-gl-rewrite 4vec-fix-of-non-term
  (implies (syntaxp (not (and (consp x)
                              (or (eq (car x) :g-var)
                                  (eq (car x) :g-apply)))))
           (equal (4vec-fix x)
                  (if (consp x)
                      (4vec (ifix (car x))
                                (ifix (cdr x)))
                    (if (integerp x)
                        x
                      (4vec-x)))))
  :hints(("Goal" :in-theory (enable 4vec-fix))))

(gl::def-gl-rewrite 4vec-of-non-term
  (implies (syntaxp (and (not (and (consp upper)
                                   (or (eq (car upper) :g-var)
                                       (eq (car upper) :g-apply))))
                         (not (and (consp lower)
                                   (or (eq (car lower) :g-var)
                                       (eq (car lower) :g-apply))))))
           (equal (4vec upper lower)
                  (B* (((THE INTEGER UPPER)
                        (LIFIX UPPER))
                       ((THE INTEGER LOWER)
                        (LIFIX LOWER)))
                    (IF (EQL UPPER LOWER)
                        UPPER (CONS UPPER LOWER)))))
  :hints(("Goal" :in-theory (enable 4vec))))

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
  (implies (integerp x)
           (4vec-p x))
  :hints(("Goal" :in-theory (enable 4vec-p))))

(gl::def-gl-rewrite 4vec-p-of-non-term
  (implies (syntaxp (not (and (consp x)
                              (or (eq (car x) :g-var)
                                  (eq (car x) :g-apply)))))
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
    (implies (syntaxp (and (not (gl-non-term-p x))
                           ;; (prog2$ (cw "split-logbitp-0 term: ~x0~%" (my-dumb-evisc x 3 5))
                           ;;         t)
                           ))
             (equal (logbitp 0 x)
                    (if (logbitp0 x) t nil))))
  (gl::Def-gl-rewrite logbitp0-of-number
    (implies (syntaxp (and (gl-non-term-p x)
                           ;; (prog2$ (cw "logbitp0-of-number term: ~x0~%" (my-dumb-evisc x 3 5))
                           ;;         t)
                           ))
             (equal (logbitp0 x)
                    (logbitp 0 x))))
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
                         (not (or (atom x) (eq (car x) :g-number)))))
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
  ((logtail n x) y)
  (x (logapp n x y))
  :test (quotep n))

(gl::def-glcp-ctrex-rewrite
  ((logcdr x) y)
  (x (logcons (logcar x) y)))

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

(gl::Def-gl-rewrite svex-env-fix-of-non-term
  (implies (syntaxp (not (and (consp x)
                              (or (eq (car x) :g-var)
                                  (eq (car x) :g-apply)))))
           (equal (svex-env-fix x)
                  (IF (ATOM X)
                      NIL
                      (IF (AND (CONSP (CAR X))
                               (SVAR-P (CAAR X)))
                          (CONS (CONS (CAAR X) (4VEC-FIX (CDAR X)))
                                (SVEX-ENV-FIX (CDR X)))
                          (SVEX-ENV-FIX (CDR X))))))
  :hints(("Goal" :in-theory (enable svex-env-fix))))

(gl::gl-set-uninterpreted svex-env-lookup-nofix)

(gl::def-gl-rewrite svex-env-lookup-nofix-when-non-term
  (implies (syntaxp (not (and (consp env)
                              (or (eq (car env) :g-var)
                                  (eq (car env) :g-apply)))))
           (equal (svex-env-lookup-nofix x env)
                  (or (cdr (hons-get x env)) (4vec-x))))
  :hints(("Goal" :in-theory (enable svex-env-lookup-nofix))))

(gl::def-glcp-ctrex-rewrite
  ((svex-env-lookup-nofix var env) val)
  (env (b* ((env (make-fast-alist env)))
         (if (equal (cdr (hons-get var env)) val)
             env
           (hons-acons var val env)))))

(gl::def-glcp-ctrex-rewrite
  ((svex-env-lookup-nofix var (svex-env-fix env)) val)
  (env (b* ((env (make-fast-alist env)))
         (if (equal (cdr (hons-get var env)) val)
             env
           (hons-acons var val env)))))

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

(define ctrex-clean-env ((x gl::glcp-obj-ctrex-p))
  ;; use with :ctrex-transform ctrex-clean-env
  ;; note: assumes env is the only variable bound in the counterex and the only g-var variable
  :verify-guards nil
  (b* (((gl::glcp-obj-ctrex x))
       (env-alist (cadr (assoc 'env x.obj-alist)))
       (new-env-alist (make-fast-alist (fast-alist-clean env-alist)))
       (- (fast-alist-free env-alist)
          (fast-alist-free (cdr x.genv))))
    (gl::change-glcp-obj-ctrex
     x
     :obj-alist
     (list (list 'env new-env-alist))
     :genv (cons (car x.genv) (make-fast-alist (list (cons 'env new-env-alist)))))))
