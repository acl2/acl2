; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2018 Centaur Technology
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
(include-book "4vec")
(include-book "centaur/bitops/sparseint" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (std::add-default-post-define-hook :fix))

(defxdoc s4vecs
  :parents (4vec)
  :short "Representation of 4vecs using @(see sparseint) rather than bignum elements.")

(local (xdoc::set-default-parents s4vecs))


(define s4vec-p (x)
  (or (integerp x)
      (and (consp x)
           (sparseint-p (car x))
           (or (and (not (cdr x))
                    (not (integerp (car x))))
               (and (sparseint-p (cdr x))
                    (not (equal (car x) (cdr x))))))))

(define s4vec-fix ((x s4vec-p))
  :returns (new-x s4vec-p)
  :prepwork ((local (in-theory (enable s4vec-p))))
  (mbe :logic (if (atom x)
                  (if (integerp x) x '(-1 . 0))
                (b* ((car (sparseint-fix (car x)))
                     ((unless (cdr x))
                      (if (integerp car) car (list car)))
                     (cdr (sparseint-fix (cdr x)))
                     ((when (equal car cdr))
                      (if (integerp car) car (list car))))
                  (cons car cdr)))
       :exec x)
  ///
  (defret s4vec-fix-when-s4vec-p
    (implies (s4vec-p x)
             (equal new-x x)))

  (fty::deffixtype s4vec :pred s4vec-p :fix s4vec-fix :equiv s4vec-equiv :define t :forward t))

(local (defthmd sparseint-p-when-integerp
         (implies (integerp x)
                  (sparseint-p x))
         :hints(("Goal" :in-theory (enable sparseint-p
                                           bitops::sparseint$-p
                                           bitops::sparseint$-height-correctp
                                           bitops::sparseint$-kind)))))

(define s4vec->upper ((x s4vec-p))
  :returns (upper sparseint-p
                  :hints(("Goal" :in-theory (enable sparseint-p-when-integerp))))
  :guard-hints (("goal" :in-theory (enable s4vec-p)))
  (if (atom x)
      (mbe :logic (if (integerp x) x -1)
           :exec x)
    (sparseint-fix (car x)))
  ///
  (fty::deffixequiv s4vec->upper
    :hints(("Goal" :in-theory (enable s4vec-fix)))))

(define s4vec->lower ((x s4vec-p))
  :returns (lower sparseint-p
                  :hints(("Goal" :in-theory (enable sparseint-p-when-integerp))))
  :guard-hints (("goal" :in-theory (enable s4vec-p)))
  (if (atom x)
      (lifix x)
    (if (cdr x)
        (sparseint-fix (cdr x))
      (sparseint-fix (car x))))
  ///
  (fty::deffixequiv s4vec->lower
    :hints(("Goal" :in-theory (enable s4vec-fix)))))

(define s4vec ((upper sparseint-p)
               (lower sparseint-p))
  :returns (result s4vec-p :hints(("Goal" :in-theory (enable s4vec-p))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable sparseint-p))))
  (b* ((upper (sparseint-fix upper))
       (lower (sparseint-fix lower)))
    (if (equal upper lower)
        (if (integerp upper) upper (list upper))
      (cons upper lower)))
  ///
  (defret s4vec->upper-of-s4vec
    (equal (s4vec->upper result)
           (sparseint-fix upper))
    :hints(("Goal" :in-theory (enable s4vec->upper))))

  (defret s4vec->lower-of-s4vec
    (equal (s4vec->lower result)
           (sparseint-fix lower))
    :hints(("Goal" :in-theory (enable s4vec->lower)))))

(defmacro make-s4vec (&key upper lower)
  `(s4vec ,upper ,lower))

(def-b*-binder s4vec
  :body (std::da-patbind-fn 's4vec '((upper . s4vec->upper)
                                     (lower . s4vec->lower))
                            args acl2::forms acl2::rest-expr))

(define s4vec->4vec ((x s4vec-p))
  :returns (val 4vec-p)
  :guard-hints (("goal" :in-theory (enable s4vec-p
                                           s4vec->upper
                                           s4vec->lower))
                (and stable-under-simplificationp
                     '(:expand ((sparseint-val x)
                                (sparseint-fix x)
                                (bitops::sparseint$-kind x)
                                (bitops::sparseint$-height-correctp x)
                                (bitops::sparseint$-leaf->val x)
                                (bitops::sparseint$-val x)))))
  (mbe :logic (b* (((s4vec x)))
                (4vec (sparseint-val x.upper)
                      (sparseint-val x.lower)))
       :exec (if (atom x)
                 (2vec x)
               (if (cdr x)
                   (4vec (sparseint-val (car x))
                         (sparseint-val (cdr x)))
                 (2vec (sparseint-val (car x))))))
  ///
  (defthm s4vec->4vec-of-make-s4vec
    (equal (s4vec->4vec (make-s4vec :upper upper :lower lower))
           (4vec (sparseint-val upper) (sparseint-val lower))))

  (defret 4vec->lower-of-s4vec->4vec
    (equal (4vec->lower val)
           (sparseint-val (s4vec->lower x))))

  (defret 4vec->upper-of-s4vec->4vec
    (equal (4vec->upper val)
           (sparseint-val (s4vec->upper x)))))

(define s2vec ((x sparseint-p))
  :returns (result s4vec-p)
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable sparseint-p s4vec))))
  :enabled t
  (mbe :logic (s4vec x x)
       :exec (b* ((x (sparseint-fix x)))
               (if (integerp x)
                   x
                 (list x))))
  ///
  (defret s4vec->upper-of-s2vec
    (equal (s4vec->upper result)
           (sparseint-fix x)))

  (defret s4vec->lower-of-s2vec
    (equal (s4vec->lower result)
           (sparseint-fix x))))



(define s2vec-p ((x s4vec-p))
  :guard-hints (("goal" :in-theory (enable s4vec-p
                                           s4vec->upper
                                           s4vec->lower)))
  :inline t
  :enabled t
  (mbe :logic (b* (((s4vec x)))
                (equal x.upper x.lower))
       :exec (or (atom x)
                 (not (cdr x)))))


(define s2vec->val ((x s4vec-p))
  :inline t
  :enabled t
  :guard (s2vec-p x)
  (s4vec->upper x))

(define s4vec-2vec-p ((x s4vec-p))
  :guard-hints (("goal" :in-theory (enable s4vec-p
                                           s4vec->upper
                                           s4vec->lower)))
  :inline t
  :enabled t
  (mbe :logic (b* (((s4vec x)))
                (sparseint-equal x.upper x.lower))
       :exec (or (atom x)
                 (not (cdr x))
                 (sparseint-equal (car x) (cdr x)))))


(defmacro if-s2vec-p (vars 2vec-body 4vec-body)
  `(mbe :logic ,4vec-body
        :exec (if (and . ,(pairlis$ (replicate (len vars) 's2vec-p)
                                    (pairlis$ vars nil)))
                  ,2vec-body
                ,4vec-body)))

(define s4vec-equal ((x s4vec-p) (y s4vec-p))
  :enabled t
  :guard-hints (("goal" :in-theory (enable s4vec->4vec)))
  (mbe :logic (equal (s4vec->4vec x) (s4vec->4vec y))
       :exec (if-s2vec-p (x y)
                         (sparseint-equal (s2vec->val x) (s2vec->val y))
                         (and (sparseint-equal (s4vec->upper x) (s4vec->upper y))
                              (sparseint-equal (s4vec->lower x) (s4vec->lower y))))))


(deflist s4veclist :elt-type s4vec :true-listp t)

(define s4vec-index-p ((x s4vec-p))
  (and (s4vec-2vec-p x)
       (not (sparseint-< (s4vec->upper x) 0)))
  ///
  (defthm s4vec-index-p-implies
    (implies (s4vec-index-p x)
             (and (equal (sparseint-val (s4vec->lower x)) (sparseint-val (s4vec->upper x)))
                  (<= 0 (sparseint-val (s4vec->lower x)))))
    :rule-classes :forward-chaining))

(define s4vec-correct-formal-evals (formals)
  :mode :program
  (if (atom formals)
      nil
    (cons (b* (((std::formal x1) (car formals)))
            (if (and (consp x1.guard)
                     (eq (car x1.guard) 's4vec-p))
                `(s4vec->4vec ,x1.name)
              x1.name))
          (s4vec-correct-formal-evals (cdr formals)))))

(define s4vec-correct-fn (args wrld)
  :mode :program
  (b* ((fn (std::get-define-current-function wrld))
       ((std::defguts guts) (cdr (assoc fn (std::get-define-guts-alist wrld))))
       ((std::returnspec retval) (car guts.returnspecs))
       (4vec-fn (intern$ (subseq (symbol-name fn) 1 nil) "SV")))
    `(defret <fn>-correct
       (equal (s4vec->4vec ,retval.name)
              (,4vec-fn . ,(s4vec-correct-formal-evals guts.formals)))
       :hints(("Goal" :in-theory (enable ,4vec-fn
                                         . ,(cadr (assoc-keyword :enable args))))))))

(defmacro s4vec-correct (&rest args)
  `(make-event (s4vec-correct-fn ',args (w state))))
              
              
       


(define s4vec-bit-index ((n natp)
                         (x s4vec-p))
  :returns (bit s4vec-p)
  (if-s2vec-p (x)
              (s2vec (int-to-sparseint (sparseint-bit n (s2vec->val x))))
              (make-s4vec :upper (int-to-sparseint (sparseint-bit n (s4vec->upper x)))
                          :lower (int-to-sparseint (sparseint-bit n (s4vec->lower x)))))
  ///
  (s4vec-correct))

(define 4vec->s4vec ((x 4vec-p))
  :returns (new-x s4vec-p)
  (if-2vec-p (x)
             (s2vec (int-to-sparseint (2vec->val x)))
             (s4vec (int-to-sparseint (4vec->upper x))
                    (int-to-sparseint (4vec->lower x))))
  ///
  (defret s4vec->4vec-of-<fn>
    (equal (s4vec->4vec new-x)
           (4vec-fix x))))

(defmacro s4vec-1x () `',(4vec->s4vec (4vec-1x)))

(defmacro s4vec-x () `',(4vec->s4vec (4vec-x)))

(define s4vec-bit-extract ((n s4vec-p)
                           (x s4vec-p))
  :returns (bit s4vec-p)
  (if (s4vec-index-p n)
      (s4vec-bit-index (sparseint-val (s4vec->upper n)) x)
    (s4vec-1x))
  ///
  (s4vec-correct :enable (s4vec-index-p)))


(define s3vec-p ((x s4vec-p))
  :returns bool
  (mbe :logic (b* (((s4vec x)))
                (not (sparseint-test-bitandc2 x.lower x.upper)))
       :exec (or (s2vec-p x)
                 (b* (((s4vec x)))
                   (not (sparseint-test-bitandc2 x.lower x.upper)))))
  ///
  (defret <fn>-correct
    (equal bool
           (3vec-p (s4vec->4vec x)))
    :hints(("Goal" :in-theory (enable 3vec-p)))))

(define s3vec-fix ((x s4vec-p))
  :returns (fix s4vec-p)
  (b* (((s4vec x)))
    (if (s3vec-p x)
        (s4vec-fix x)
      (s4vec (sparseint-bitor x.upper x.lower)
             (sparseint-bitand x.upper x.lower))))
  ///
  (local (defthm equal-logand
           (equal (equal x (logand x y))
                  (and (integerp x)
                       (equal (logand x (lognot y)) 0)))
           :hints ((logbitp-reasoning))))

  (local (defthm equal-logior
           (equal (equal x (logior y x))
                  (and (integerp x)
                       (equal (logand y (lognot x)) 0)))
           :hints ((logbitp-reasoning))))

  (s4vec-correct :enable (3vec-p)))

(define s3vec-bitnot ((x s4vec-p))
  :returns (res s4vec-p)
  (if-s2vec-p (x)
              (s2vec (sparseint-bitnot (s2vec->val x)))
              (b* (((s4vec x)))
                (s4vec (sparseint-bitnot x.lower)
                       (sparseint-bitnot x.upper))))
  ///
  (s4vec-correct))

(define s4vec-bitnot ((x s4vec-p))
  :returns (res s4vec-p)
  (s3vec-bitnot (s3vec-fix x))
  ///
  (s4vec-correct))

(define s3vec-bitand ((x s4vec-p)
                      (y s4vec-p))
  :returns (res s4vec-p)
  (if-s2vec-p (x y)
              (s2vec (sparseint-bitand (s2vec->val x) (s2vec->val y)))
              (b* (((s4vec x))
                   ((s4vec y)))
                (s4vec (sparseint-bitand x.upper y.upper)
                       (sparseint-bitand x.lower y.lower))))
  ///
  (s4vec-correct))

(define s4vec-bitand ((x s4vec-p)
                      (y s4vec-p))
  :returns (res s4vec-p)
  (s3vec-bitand (s3vec-fix x) (s3vec-fix y))
  ///
  (s4vec-correct))


(define s3vec-bitor ((x s4vec-p)
                      (y s4vec-p))
  :returns (res s4vec-p)
  (if-s2vec-p (x y)
              (s2vec (sparseint-bitor (s2vec->val x) (s2vec->val y)))
              (b* (((s4vec x))
                   ((s4vec y)))
                (s4vec (sparseint-bitor x.upper y.upper)
                       (sparseint-bitor x.lower y.lower))))
  ///
  (s4vec-correct))

(define s4vec-bitor ((x s4vec-p)
                      (y s4vec-p))
  :returns (res s4vec-p)
  (s3vec-bitor (s3vec-fix x) (s3vec-fix y))
  ///
  (s4vec-correct))


(define s3vec-bitxor ((x s4vec-p)
                      (y s4vec-p))
  :returns (res s4vec-p)
  (if (and (s2vec-p x)
           (s2vec-p y))
      (s2vec (sparseint-bitxor (s2vec->val x) (s2vec->val y)))
    (b* (((s4vec x))
         ((s4vec y))
         (xmask (sparseint-bitor (sparseint-bitandc2 x.upper x.lower)
                                 (sparseint-bitandc2 y.upper y.lower))))
      (s4vec (sparseint-bitor xmask (sparseint-bitxor x.upper y.upper))
             (sparseint-bitandc1 xmask (sparseint-bitxor x.lower y.lower)))))
  ///
  (s4vec-correct))

(define s4vec-bitxor ((x s4vec-p)
                      (y s4vec-p))
  :returns (res s4vec-p)
  (if (and (s2vec-p x)
           (s2vec-p y))
      (s2vec (sparseint-bitxor (s2vec->val x) (s2vec->val y)))
    (b* (((s4vec x))
         ((s4vec y))
         (xmask (sparseint-bitor (sparseint-bitxor x.upper x.lower)
                                 (sparseint-bitxor y.upper y.lower))))
      (s4vec (sparseint-bitor xmask (sparseint-bitxor x.upper y.upper))
             (sparseint-bitandc1 xmask (sparseint-bitxor x.lower y.lower)))))
  ///
  (s4vec-correct))


(define s4vec-res ((x s4vec-p)
                   (y s4vec-p))
  :returns (res s4vec-p)
  (b* (((s4vec x))
       ((s4vec y)))
    (s4vec (sparseint-bitor x.upper y.upper)
           (sparseint-bitand x.lower y.lower)))
  ///
  (s4vec-correct))


(define s4vec-resand ((x s4vec-p)
                   (y s4vec-p))
  :returns (resand s4vec-p)
  (b* (((s4vec x))
       ((s4vec y)))
    (s4vec (sparseint-bitand (sparseint-bitor x.upper x.lower)
                             (sparseint-bitand (sparseint-bitor y.upper y.lower)
                                               (sparseint-bitor x.upper y.upper)))
           (sparseint-bitand x.lower y.lower)))
  ///
  (s4vec-correct))


(define s4vec-resor ((x s4vec-p)
                   (y s4vec-p))
  :returns (resor s4vec-p)
  (b* (((s4vec x))
       ((s4vec y)))
    (s4vec (sparseint-bitor x.upper y.upper)
           (sparseint-bitor (sparseint-bitand x.lower x.upper)
                             (sparseint-bitor (sparseint-bitand y.lower y.upper)
                                              (sparseint-bitand x.lower y.lower)))))
  ///
  (s4vec-correct))




(defmacro s4vec-bit-limit () (expt 2 28))

(defmacro s4vec-very-large-integer-warning (n)
  `(prog2$ (cw "!!!!!!!! Danger -- if you continue, ~x0 will create a ~x1-bit ~
               value -- examine the backtrace to diagnose.~%"
               std::__function__ ,n)
           (break$)))

(define s4vec-sparseint-val ((x sparseint-p) &key (std::__function__ 'std::__function__))
  :inline t
  :no-function t
  :returns (val (equal val (sparseint-val x)))
  (b* ((xlen (sparseint-length x))
       (- (and (<= (s4vec-bit-limit) xlen)
               (s4vec-very-large-integer-warning xlen))))
    (sparseint-val x)))

(define s4vec-zero-ext ((x s4vec-p)
                        (y s4vec-p))
  :returns (res s4vec-p)
  :prepwork ((local (in-theory (enable s4vec-index-p))))
  (b* (((unless (s4vec-index-p x)) (s4vec-x))
       (xval (s4vec-sparseint-val (s4vec->upper x))))
    (if-s2vec-p (y)
               (s2vec (sparseint-concatenate xval (s2vec->val y) 0))
               (b* (((s4vec y)))
                 (s4vec (sparseint-concatenate xval y.upper 0)
                        (sparseint-concatenate xval y.lower 0)))))
  ///
  (s4vec-correct))


(define s4vec-sign-ext ((x s4vec-p)
                        (y s4vec-p))
  :returns (res s4vec-p)
  :prepwork ((local (in-theory (enable s4vec-index-p
                                       bool->bit))))
  (b* (((unless (and (or (s2vec-p x)
                         (sparseint-equal (s4vec->upper x) (s4vec->lower x)))
                     (sparseint-< 0 (s4vec->upper x))))
        (s4vec-x))
       (xval (s4vec-sparseint-val (s4vec->upper x))))
    (if-s2vec-p (y)
               (s2vec (sparseint-concatenate xval (s2vec->val y)
                                             (- (sparseint-bit (1- xval) (s2vec->val y)))))
               (b* (((s4vec y)))
                 (s4vec (sparseint-concatenate xval y.upper (- (sparseint-bit (1- xval) y.upper)))
                        (sparseint-concatenate xval y.lower (- (sparseint-bit (1- xval) y.lower)))))))
  ///
  (local (defthm logext-in-terms-of-logbitp
           (equal (logext n x)
                  (logapp (pos-fix n) x (- (logbit (+ -1 (pos-fix n)) x))))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)
                   :induct (logext n x))
                  (and stable-under-simplificationp
                       '(:in-theory (enable pos-fix)
                         :expand ((logbitp 0 x)
                                  (:free (y) (logapp 1 x y))
                                  (loghead 1 x)))))))

  (s4vec-correct))

(define s3vec-reduction-and ((x s4vec-p))
  :returns (res s4vec-p)
  (if-s2vec-p (x)
              (s2vec (int-to-sparseint (bool->vec (sparseint-equal (s2vec->val x) -1))))
              (b* (((s4vec x)))
                (s4vec (int-to-sparseint (bool->vec (sparseint-equal x.upper -1)))
                       (int-to-sparseint (bool->vec (sparseint-equal x.lower -1))))))
  ///
  (s4vec-correct))

(define s4vec-reduction-and ((x s4vec-p))
  :returns (res s4vec-p)
  (s3vec-reduction-and (s3vec-fix x))
  ///
  (s4vec-correct))


(define s3vec-reduction-or ((x s4vec-p))
  :returns (res s4vec-p)
  (if-s2vec-p (x)
              (s2vec (int-to-sparseint (bool->vec (not (sparseint-equal (s2vec->val x) 0)))))
              (b* (((s4vec x)))
                (s4vec (int-to-sparseint (bool->vec (not (sparseint-equal x.upper 0))))
                       (int-to-sparseint (bool->vec (not (sparseint-equal x.lower 0)))))))
  ///
  (s4vec-correct))

(define s4vec-reduction-or ((x s4vec-p))
  :returns (res s4vec-p)
  (s3vec-reduction-or (s3vec-fix x))
  ///
  (s4vec-correct))


(define s4vec-concat ((width s4vec-p)
                      (low   s4vec-p)
                      (high  s4vec-p))
  :returns (res s4vec-p)
  (b* (((unless (s4vec-index-p width)) (s4vec-x))
       (widthval (s4vec-sparseint-val (s4vec->upper width))))
    (if-s2vec-p (low high)
                (s2vec (sparseint-concatenate widthval (s2vec->val low) (s2vec->val high)))
                (b* (((s4vec low))
                     ((s4vec high)))
                  (s4vec (sparseint-concatenate widthval low.upper high.upper)
                         (sparseint-concatenate widthval low.lower high.lower)))))
  ///
  (s4vec-correct :enable (s4vec-index-p)))

(define s4vec-shift-core ((shift integerp)
                          (x s4vec-p))
  :returns (res s4vec-p)
  (if-s2vec-p (x)
              (s2vec (sparseint-ash (s2vec->val x) shift))
              (b* (((s4vec x)))
                (s4vec (sparseint-ash x.upper shift)
                       (sparseint-ash x.lower shift))))
  ///
  (s4vec-correct))

(define s4vec-rsh ((amt s4vec-p)
                   (x s4vec-p))
  :returns (res s4vec-p)
  (b* (((unless (s4vec-2vec-p amt)) (s4vec-x))
       (amtval (s4vec-sparseint-val (sparseint-unary-minus (s4vec->upper amt)))))
    (s4vec-shift-core amtval x))
  ///
  (s4vec-correct))

(define s4vec-lsh ((amt s4vec-p)
                   (x s4vec-p))
  :returns (res s4vec-p)
  (b* (((unless (s4vec-2vec-p amt)) (s4vec-x))
       (amtval (s4vec-sparseint-val (s4vec->upper amt))))
    (s4vec-shift-core amtval x))
  ///
  (s4vec-correct))

(define s4vec-parity ((x s4vec-p))
  :returns (res s4vec-p)
  (b* (((unless (s4vec-2vec-p x)) (s4vec-x))
       (xint (s4vec->upper x))
       ((when (sparseint-< xint 0)) (s4vec-x))
       ;; BOZO we could do a sparseint-native version...
       (xval (s4vec-sparseint-val (s4vec->upper x))))
    (s2vec (int-to-sparseint (- (fast-parity (+ 1 (integer-length xval)) xval)))))
  ///
  (s4vec-correct))


(define s4vec-countones ((x s4vec-p))
  :returns (res s4vec-p)
  (b* (((unless (s4vec-2vec-p x)) (s4vec-x))
       (xint (s4vec->upper x))
       ((when (sparseint-< xint 0)) (s4vec-x))
       ;; BOZO we could do a sparseint-native version...
       (xval (s4vec-sparseint-val (s4vec->upper x))))
    (s2vec (int-to-sparseint (logcount xval))))
  ///
  (s4vec-correct))


(define s4vec-onehot ((x s4vec-p))
  :returns (res s4vec-p)
  (b* (((unless (s4vec-2vec-p x)) (s4vec-x))
       (xint (s4vec->upper x))
       ((when (sparseint-< xint 0)) (s4vec-x))
       ;; BOZO we could do a sparseint-native version...
       (xval (s4vec-sparseint-val (s4vec->upper x))))
    (s2vec (int-to-sparseint (bool->bit (eql (logcount xval) 1)))))
  ///
  (s4vec-correct))

(define s4vec-onehot0 ((x s4vec-p))
  :returns (res s4vec-p)
  (b* (((unless (s4vec-2vec-p x)) (s4vec-x))
       (xint (s4vec->upper x))
       ((when (sparseint-< xint 0)) (s4vec-x))
       ;; BOZO we could do a sparseint-native version...
       (xval (s4vec-sparseint-val (s4vec->upper x))))
    (s2vec (int-to-sparseint (bool->bit (<= (logcount xval) 1)))))
  ///
  (s4vec-correct))


(define s4vec-plus ((x s4vec-p)
                    (y s4vec-p))
  :returns (res s4vec-p)
  (b* (((unless (and (s4vec-2vec-p x)
                     (s4vec-2vec-p y)))
        (s4vec-x)))
    (s2vec (sparseint-plus (s4vec->upper x) (s4vec->upper y))))
  ///
  (s4vec-correct))

(define s4vec-xdet ((x s4vec-p))
  :returns (res s4vec-p)
  (if (s4vec-2vec-p x)
      (s4vec-fix x)
    (s4vec-x))
  ///
  (s4vec-correct))

(define s4vec-minus ((x s4vec-p)
                    (y s4vec-p))
  :returns (res s4vec-p)
  (b* (((unless (and (s4vec-2vec-p x)
                     (s4vec-2vec-p y)))
        (s4vec-x)))
    (s2vec (sparseint-binary-minus (s4vec->upper x) (s4vec->upper y))))
  ///
  (s4vec-correct))

(define s4vec-uminus ((x s4vec-p))
  :returns (res s4vec-p)
  (b* (((unless (s4vec-2vec-p x))
        (s4vec-x)))
    (s2vec (sparseint-unary-minus (s4vec->upper x))))
  ///
  (s4vec-correct))


(define s4vec-times ((x s4vec-p) (y s4vec-p))
  :returns (res s4vec-p)
  (b* (((unless (and (s4vec-2vec-p x)
                     (s4vec-2vec-p y)))
        (s4vec-x))
       (xval (s4vec-sparseint-val (s4vec->upper x)))
       (yval (s4vec-sparseint-val (s4vec->upper y))))
    (s2vec (int-to-sparseint (* xval yval))))
  ///
  (s4vec-correct))

(define s4vec-quotient ((x s4vec-p) (y s4vec-p))
  :returns (res s4vec-p)
  (b* (((unless (and (s4vec-2vec-p x)
                     (s4vec-2vec-p y)))
        (s4vec-x))
       ((when (sparseint-equal (s4vec->upper y) 0))
        (s4vec-x))
       (xval (s4vec-sparseint-val (s4vec->upper x)))
       (yval (s4vec-sparseint-val (s4vec->upper y))))
    (s2vec (int-to-sparseint (truncate xval yval))))
  ///
  (s4vec-correct))

(define s4vec-remainder ((x s4vec-p) (y s4vec-p))
  :returns (res s4vec-p)
  (b* (((unless (and (s4vec-2vec-p x)
                     (s4vec-2vec-p y)))
        (s4vec-x))
       ((when (sparseint-equal (s4vec->upper y) 0))
        (s4vec-x))
       (xval (s4vec-sparseint-val (s4vec->upper x)))
       (yval (s4vec-sparseint-val (s4vec->upper y))))
    (s2vec (int-to-sparseint (rem xval yval))))
  ///
  (s4vec-correct))

(define s4vec-< ((x s4vec-p) (y s4vec-p))
  :returns (res s4vec-p)
  (b* (((unless (and (s4vec-2vec-p x)
                     (s4vec-2vec-p y)))
        (s4vec-x)))
    (s2vec (int-to-sparseint (bool->vec (sparseint-< (s4vec->upper x)
                                                     (s4vec->upper y))))))
  ///
  (s4vec-correct))

(define s3vec-== ((x s4vec-p) (y s4vec-p))
  :returns (res s4vec-p)
  (s3vec-reduction-and (s3vec-bitnot (s3vec-bitxor x y)))
  ///
  (s4vec-correct))

(define s4vec-== ((x s4vec-p) (y s4vec-p))
  :returns (res s4vec-p)
  (s3vec-== (s3vec-fix x) (s3vec-fix y))
  ///
  (s4vec-correct))

(define s4vec-=== ((x s4vec-p) (y s4vec-p))
  :returns (res s4vec-p)
  (b* (((s4vec x))
       ((s4vec y)))
    (s2vec (int-to-sparseint (bool->vec (s4vec-equal x y)))))
  ///
  (s4vec-correct :enable (s4vec->4vec bool->vec)))

(define s4vec-===* ((left s4vec-p) (right s4vec-p))
  :returns (equal s4vec-p)
  (b* (((s4vec left))
       ((s4vec right))
       (uppers-diff (sparseint-bitxor left.upper right.upper))
       (lowers-diff (sparseint-bitxor left.lower right.lower))
       (diff (sparseint-bitor uppers-diff lowers-diff))
       (left-non-x (sparseint-bitorc1 left.upper left.lower))
       (right-non-x (sparseint-bitorc1 right.upper right.lower))
       (true ;; inputs are non-x and identical
        (sparseint-equal -1
                         (sparseint-bitandc1 diff
                                             ;; not X: ~(upper & ~lower) = ~upper | lower
                                             left-non-x)))
       ((when true) (mbe :logic (s4vec (int-to-sparseint -1) (int-to-sparseint -1)) :exec -1))
       (not-false (sparseint-equal 0
                                   (sparseint-bitand
                                    left-non-x ;; factor this out because both conditions below include it
                                    (sparseint-bitorc2
                                     ;; bits are Boolean and not equal
                                     ;; (sparseint-bitand right-non-x
                                     diff
                                     ;; left is non-x and y is X
                                     right-non-x))))
       ((when not-false) (s4vec-x)))
    (mbe :logic (s4vec (int-to-sparseint 0) (int-to-sparseint 0)) :exec 0))

  ///
  (s4vec-correct))

(define s3vec-? ((test s4vec-p)
                 (then s4vec-p)
                 (else s4vec-p))
  :returns (res s4vec-p)
  (b* (((s4vec test))
       ((when (sparseint-equal test.upper 0)) (s4vec-fix else))
       ((when (not (sparseint-equal test.lower 0))) (s4vec-fix then))
       ((s4vec then))
       ((s4vec else)))
    (s4vec (sparseint-bitor (sparseint-bitor then.upper else.upper)
                            (sparseint-bitor then.lower else.lower))
           (sparseint-bitand (sparseint-bitand then.upper else.upper)
                            (sparseint-bitand then.lower else.lower))))
  ///
  (s4vec-correct))

(define s4vec-? ((test s4vec-p)
                 (then s4vec-p)
                 (else s4vec-p))
  :returns (res s4vec-p)
  (s3vec-? (s3vec-fix test) then else)
  ///
  (s4vec-correct))


(define s3vec-bit? ((test s4vec-p)
                    (then s4vec-p)
                    (else s4vec-p))
  :returns (res s4vec-p)
  (b* (((s4vec test))
       ((s4vec then))
       ((s4vec else))
       (test-x (sparseint-bitandc2 test.upper test.lower)))
    (s4vec (sparseint-bitor (sparseint-bitandc1 test.upper else.upper)
                            (sparseint-bitor
                             (sparseint-bitand test.lower then.upper)
                             (sparseint-bitand test-x
                                               (sparseint-bitor
                                                (sparseint-bitor then.upper then.lower)
                                                (sparseint-bitor else.upper else.lower)))))
           (sparseint-bitor (sparseint-bitandc1 test.upper else.lower)
                            (sparseint-bitor
                             (sparseint-bitand test.lower then.lower)
                             (sparseint-bitand test-x
                                               (sparseint-bitand
                                                (sparseint-bitand then.upper then.lower)
                                                (sparseint-bitand else.upper else.lower)))))))
  ///
  (s4vec-correct))

(define s4vec-bit? ((test s4vec-p)
                    (then s4vec-p)
                    (else s4vec-p))
  :returns (res s4vec-p)
  (s3vec-bit? (s3vec-fix test) then else)
  ///
  (s4vec-correct))

(define s4vec-bit?! ((test s4vec-p)
                     (thens s4vec-p)
                     (elses s4vec-p))
  :returns (res s4vec-p)
  (b* (((s4vec test))
       (pick-then (sparseint-bitand test.upper test.lower))
       ((when (sparseint-equal pick-then -1)) (s4vec-fix thens))
       ((when (sparseint-equal pick-then 0)) (s4vec-fix elses))
       (pick-else (sparseint-bitnot pick-then))
       ((s4vec thens))
       ((s4vec elses))
       (upper (sparseint-bitor (sparseint-bitand pick-then thens.upper)
                               (sparseint-bitand pick-else elses.upper)))
       (lower (sparseint-bitor (sparseint-bitand pick-then thens.lower)
                               (sparseint-bitand pick-else elses.lower))))
    (s4vec upper lower))
  ///
  (local (defthm logand-a-b-c-when-a-b-equal-cons
           (implies (and (equal k (logand x y))
                         (syntaxp (quotep k)))
                    (equal (logand x y z) (logand k z)))
           :hints(("Goal" :use ((:instance bitops::associativity-of-logand
                                 (a x) (b y) (c z)))
                   :in-theory (disable bitops::associativity-of-logand)))))
  (local (defthm logior-0
           (equal (logior x 0) (ifix x))
           :hints(("Goal" :in-theory (enable bitops::logior**)))))
  (local (in-theory (disable acl2::commutativity-of-logand
                             acl2::commutativity-of-logior
                             bitops::commutativity-2-of-logand)))
  (s4vec-correct))


(define s4vec-?! ((test s4vec-p)
                  (then s4vec-p)
                  (else s4vec-p))
  :returns (choices s4vec-p)
  :short "If-then-elses of @(see s4vec)s following the SystemVerilog semantics for
          procedural conditional branches, i.e. if the test has any bit that is
          exactly 1 (not 0, Z, or X), we choose the then branch, else the else
          branch. (Non-monotonic semantics)."

  (b* (((s4vec test))
       ;; We choose the THEN branch if any bit has upper and lower both set.
       (pick-else (sparseint-equal 0 (sparseint-bitand test.upper test.lower))))
    (if pick-else (s4vec-fix else) (s4vec-fix then)))
  ///
  (s4vec-correct))

(define s3vec-?* ((test s4vec-p)
                  (then s4vec-p)
                  (else s4vec-p))
  :returns (res s4vec-p)
  (b* (((s4vec test))
       ((when (sparseint-equal test.upper 0)) (s4vec-fix else))
       ((when (not (sparseint-equal test.lower 0))) (s4vec-fix then))
       ((s4vec then))
       ((s4vec else)))
    (s4vec (sparseint-bitor (sparseint-bitor then.upper else.upper)
                            (sparseint-bitxor then.lower else.lower))
           (sparseint-bitand (sparseint-biteqv then.upper else.upper)
                             (sparseint-bitand then.lower else.lower))))
  ///
  (s4vec-correct))

(define s4vec-?* ((test s4vec-p)
                 (then s4vec-p)
                 (else s4vec-p))
  :returns (res s4vec-p)
  (s3vec-?* (s3vec-fix test) then else)
  ///
  (s4vec-correct))


(define s4vec-override ((strong s4vec-p)
                        (weak s4vec-p))
  :returns (res s4vec-p)
  (b* (((s4vec strong))
       ((s4vec weak)))
    (s4vec (sparseint-bitor (sparseint-bitand strong.lower weak.upper) strong.upper)
           (sparseint-bitand (sparseint-bitor strong.upper weak.lower) strong.lower)))
  ///
  (local (defthm s4vec-override-correct1
           (equal (logior (logand sl wu (lognot su))
                          (logand su (lognot (logand sl (lognot su)))))
                  (logior su (logand sl wu)))
           :hints ((logbitp-reasoning))))
  (local (defthm s4vec-override-correct2
           (equal (logior (logand sl wl (lognot su))
                          (logand sl (lognot (logand sl (lognot su)))))
                  (logand sl (logior wl su)))
           :hints ((logbitp-reasoning))))
  (s4vec-correct))

(define s4vec-onset ((x s4vec-p))
  :returns (res s4vec-p)
  (if (s2vec-p x)
      (s4vec-fix x)
    (b* (((s4vec x)))
      (s4vec x.upper (sparseint-bitand x.upper x.lower))))
  ///
  (s4vec-correct))

(define s4vec-offset ((x s4vec-p))
  :returns (res s4vec-p)
  (if (s2vec-p x)
      (s2vec (sparseint-bitnot (s2vec->val x)))
    (b* (((s4vec x)))
      (s4vec (sparseint-bitnot x.lower)
             (sparseint-bitnor x.upper x.lower))))
  ///
  (s4vec-correct))


(define sparseint-rev-blocks ((nbits natp)
                              (blocksz posp)
                              (x sparseint-p))
  :returns (res sparseint-p)
  :verify-guards nil
  (b* ((nbits (lnfix nbits))
       (blocksz (lposfix blocksz))
       ((when (< nbits blocksz))
        (sparseint-concatenate nbits x 0))
       (next-nbits (- nbits blocksz))
       (rest (sparseint-rev-blocks next-nbits blocksz
                                   (sparseint-rightshift blocksz x))))
    (sparseint-concatenate next-nbits rest (sparseint-concatenate blocksz x 0)))
  ///
  (verify-guards sparseint-rev-blocks)

  (defret <fn>-correct
    (equal (sparseint-val res)
           (rev-blocks nbits blocksz (sparseint-val x)))
    :hints(("Goal" :in-theory (enable rev-blocks)))))


(define s4vec-rev-blocks ((nbits s4vec-p)
                          (blocksz s4vec-p)
                          (x s4vec-p))
  :returns (res s4vec-p)
  (b* (((unless (and (s4vec-2vec-p nbits)
                     (s4vec-2vec-p blocksz)))
        (s4vec-x))
       (nbits-int (s4vec->upper nbits))
       ((when (sparseint-< nbits-int 0)) (s4vec-x))
       (blocksz-int (s4vec->upper blocksz))
       ((unless (sparseint-< 0 blocksz-int)) (s4vec-x))
       (nbits-val (s4vec-sparseint-val nbits-int))
       (blocksz-val (s4vec-sparseint-val blocksz-int)))
    (if-s2vec-p (x)
                (s2vec (sparseint-rev-blocks nbits-val blocksz-val (s2vec->val x)))
                (b* (((s4vec x)))
                  (s4vec (sparseint-rev-blocks nbits-val blocksz-val x.upper)
                         (sparseint-rev-blocks nbits-val blocksz-val x.lower)))))
  ///
  (s4vec-correct))


(define s4vec-wildeq-safe ((a s4vec-p)
                           (b s4vec-p))
  :returns (res s4vec-p)
  (b* ((eq (s3vec-bitnot (s4vec-bitxor a b)))
       ((s4vec b))
       (zmask (sparseint-bitandc1 b.upper b.lower)))
    (s3vec-reduction-and (s3vec-bitor eq (s2vec zmask))))
  ///
  (s4vec-correct :enable (2vec)))

(define s4vec-wildeq ((a s4vec-p)
                      (b s4vec-p))
  :returns (res s4vec-p)
  (b* ((eq (s3vec-bitnot (s4vec-bitxor a b)))
       ((s4vec b))
       (zxmask (sparseint-bitxor b.upper b.lower)))
    (s3vec-reduction-and (s3vec-bitor eq (s2vec zxmask))))
  ///
  (s4vec-correct :enable (2vec)))


(define s4vec-symwildeq ((a s4vec-p)
                         (b s4vec-p))
  :returns (res s4vec-p)
  (b* ((eq (s3vec-bitnot (s4vec-bitxor a b)))
       ((s4vec b))
       ((s4vec a))
       (zxmask (sparseint-bitor (sparseint-bitandc1 b.upper b.lower)
                                (sparseint-bitandc1 a.upper a.lower))))
    (s3vec-reduction-and (s3vec-bitor eq (s2vec zxmask))))
  ///
  (s4vec-correct :enable (2vec)))
       
       
(define s4vec-clog2 ((a s4vec-p))
  :returns (res s4vec-p)
  (if (s4vec-index-p a)
      (s2vec (int-to-sparseint (sparseint-length (sparseint-plus (s4vec->upper a) -1))))
    (s4vec-x))
  ///
  (s4vec-correct :enable (s4vec-index-p)))
       
(define s4vec-pow ((base s4vec-p) (exp s4vec-p))
  :returns (res s4vec-p)
  (b* (((unless (and (s4vec-2vec-p base)
                     (s4vec-2vec-p exp)))
        (s4vec-x))
       (expint (s4vec->upper exp))
       (baseint (s4vec->upper base))
       ((when (sparseint-equal expint 0)) ;; 1
        (s2vec 1))
       ((when (sparseint-< expint 0))
        (b* (((when (sparseint-equal baseint 0)) (s4vec-x))
             ((when (sparseint-equal baseint 1)) (s2vec 1))
             ((when (sparseint-equal baseint -1))
              (s2vec (int-to-sparseint (- 1 (* 2 (sparseint-bit 0 expint)))))))
          (s2vec 0)))
       ((when (or (sparseint-equal expint 1)
                  (sparseint-equal baseint 0)
                  (sparseint-equal baseint 1)))
        (s2vec baseint))
       ((when (sparseint-equal baseint -1))
        (s2vec (int-to-sparseint (- 1 (* 2 (sparseint-bit 0 expint))))))
       ;; exponent is 2 or greater and base is not -1, 0, 1.
       (expval (s4vec-sparseint-val expint))
       (baseval (s4vec-sparseint-val baseint)))
    (s2vec (int-to-sparseint (expt baseval expval))))
  ///
  (local (defthm expt-neg1
           (equal (expt -1 n)
                  (- 1 (* 2 (logbit 0 n))))
           :hints(("Goal" :in-theory (enable expt)
                   :expand ((logbitp 0 (+ 1 n))
                            (logbitp 0 (+ -1 n)))))))
  (s4vec-correct :enable (expt)))


(define s4vec-part-select ((lsb s4vec-p)
                           (width s4vec-p)
                           (in s4vec-p))
  :returns (res s4vec-p)
  (b* (((unless (and (s4vec-2vec-p lsb)
                     (s4vec-2vec-p width)))
        (s4vec-x))
       (widthint (s4vec->upper width))
       ((when (sparseint-< widthint 0)) (s4vec-x))
       (lsbint (s4vec->upper lsb))
       ((unless (sparseint-< lsbint 0))
        (s4vec-zero-ext width (s4vec-rsh lsb in))))
    (s4vec-zero-ext width (s4vec-concat (s2vec (sparseint-unary-minus lsbint))
                                        (s4vec-x)
                                        in)))
  ///
  (s4vec-correct :enable (2vec)))


(define s4vec-part-install ((lsb s4vec-p)
                            (width s4vec-p)
                            (in s4vec-p)
                            (val s4vec-p))
  :returns (res s4vec-p)
  (b* (((unless (and (s4vec-2vec-p lsb)
                     (s4vec-2vec-p width)))
        (s4vec-x))
       (widthint (s4vec->upper width))
       ((when (sparseint-< widthint 0)) (s4vec-x))
       (lsbint (s4vec->upper lsb))
       ((unless (sparseint-< lsbint 0))
        (s4vec-concat lsb in (s4vec-concat width val (s4vec-rsh (s2vec (sparseint-plus lsbint widthint)) in))))
       (neg-lsb (sparseint-unary-minus lsbint))
       ((unless (sparseint-< neg-lsb widthint))
        (s4vec-fix in))
       (width+lsb (sparseint-plus lsbint widthint)))
    (s4vec-concat (s2vec width+lsb)
                  (s4vec-rsh (s2vec neg-lsb) val)
                  (s4vec-rsh (s2vec width+lsb) in)))
  ///
  (s4vec-correct :enable (2vec)))

(define s4vec-xfree-p ((x s4vec-p))
  :returns (res)
  (b* (((s4vec x)))
    (not (sparseint-test-bitandc2 x.upper x.lower)))
  ///
  (local (defthm equal-neg1-logior
           (equal (equal -1 (logior a b))
                  (equal 0 (logand (lognot a) (lognot b))))
           :hints ((logbitp-reasoning))))

  (defret <fn>-correct
    (equal res
           (4vec-xfree-p (s4vec->4vec x)))
    :hints(("Goal" :in-theory (enable 4vec-xfree-p)))))


       

                        
