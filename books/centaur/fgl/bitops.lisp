; GL - A Symbolic Simulation Framework for ACL2
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

(in-package "FGL")


(include-book "arith-base")
(include-book "glcp-config")
(include-book "def-gl-rewrite")
(include-book "syntax-bind")
(include-book "gl-object")
(include-book "centaur/misc/starlogic" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(table gl-fn-modes 'intcons
       (make-gl-function-mode :dont-expand-def t))
(table gl-fn-modes 'intcons*
       (make-gl-function-mode :dont-expand-def t))
(table gl-fn-modes 'endint
       (make-gl-function-mode :dont-expand-def t))
(table gl-fn-modes 'intcar
       (make-gl-function-mode :dont-expand-def t))
(table gl-fn-modes 'intcdr
       (make-gl-function-mode :dont-expand-def t))
(table gl-fn-modes 'int-endp
       (make-gl-function-mode :dont-expand-def t))
(table gl-fn-modes 'int
       (make-gl-function-mode :dont-expand-def t))


(table gl-fn-modes 'acl2::logcons$inline
       (make-gl-function-mode :dont-expand-def t))
(def-gl-rewrite logcons-is-intcons
  (equal (logcons a b) (intcons (eql a 1) b)))

(table gl-fn-modes 'acl2::logcar$inline
       (make-gl-function-mode :dont-expand-def t))
(def-gl-rewrite logcar-is-intcar
  (equal (logcar x) (if (intcar x) 1 0)))

(table gl-fn-modes 'acl2::logcdr$inline
       (make-gl-function-mode :dont-expand-def t))
(def-gl-rewrite logcdr-is-intcdr
  (equal (logcdr x) (intcdr x)))

(def-gl-rewrite ifix-is-int
  (equal (ifix x) (int x)))

(defund gl-int-endp (x)
  (gl-object-case x
    :g-integer (atom (cdr x.bits))
    :g-boolean t
    :g-cons t
    :g-concrete (or (zip x.val) (eql x.val -1))
    :otherwise nil))

(define check-int-endp (x xsyn)
  :verify-guards nil
  (and (gl-int-endp xsyn)
       (int-endp x))
  ///
  (defthm check-int-endp-open
    (iff (check-int-endp x xsyn)
         (and* (gl-int-endp xsyn)
               (int-endp x)))))

(table gl-fn-modes 'lognot
       (make-gl-function-mode :dont-expand-def t))

(def-gl-rewrite fgl-lognot
  (equal (lognot x)
         (b* ((x (int x))
              (xsyn (syntax-bind xsyn (g-concrete x)))
              ((when (check-int-endp x xsyn)) (endint (not (intcar x)))))
           (intcons (not (intcar x))
                    (lognot (intcdr x)))))
  :hints(("Goal" :in-theory (enable bitops::lognot** int-endp))))

(table gl-fn-modes 'binary-logand
       (make-gl-function-mode :dont-expand-def t))


(def-gl-rewrite fgl-logand
  (equal (logand x y)
         (b* ((x (int x))
              (y (int y))
              (xsyn (syntax-bind xsyn (g-concrete x)))
              (ysyn (syntax-bind ysyn (g-concrete y)))
              ((when (check-int-endp x xsyn)) (if (intcar x) y 0))
              ((when (check-int-endp y ysyn)) (if (intcar y) x 0)))
           (intcons (and (intcar x)
                         (intcar y))
                    (logand (intcdr x) (intcdr y)))))
  :hints(("Goal" :in-theory (enable bitops::logand** int-endp))))

(table gl-fn-modes 'binary-logior
       (make-gl-function-mode :dont-expand-def t))

(def-gl-rewrite fgl-logior
  (equal (logior x y)
         (b* ((x (int x))
              (y (int y))
              (xsyn (syntax-bind xsyn (g-concrete x)))
              (ysyn (syntax-bind ysyn (g-concrete y)))
              ((when (check-int-endp x xsyn)) (if (intcar x) -1 y))
              ((when (check-int-endp y ysyn)) (if (intcar y) -1 x)))
           (intcons (or (intcar x)
                        (intcar y))
                    (logior (intcdr x) (intcdr y)))))
  :hints(("Goal" :in-theory (enable bitops::logior** int-endp))))

(table gl-fn-modes 'acl2::binary-logxor
       (make-gl-function-mode :dont-expand-def t))

(def-gl-rewrite fgl-logxor
  (equal (logxor x y)
         (b* ((x (int x))
              (y (int y))
              (xsyn (syntax-bind xsyn (g-concrete x)))
              (ysyn (syntax-bind ysyn (g-concrete y)))
              ((when (check-int-endp x xsyn)) (if (intcar x) (lognot y) y))
              ((when (check-int-endp y ysyn)) (if (intcar y) (lognot x) x)))
           (intcons (xor (intcar x)
                         (intcar y))
                    (logxor (intcdr x) (intcdr y)))))
  :hints(("Goal" :in-theory (enable bitops::logxor** int-endp
                                    bitops::equal-logcons-strong))))

(table gl-fn-modes 'acl2::binary-logeqv
       (make-gl-function-mode :dont-expand-def t))

(def-gl-rewrite fgl-logeqv
  (equal (logeqv x y)
         (b* ((x (int x))
              (y (int y))
              (xsyn (syntax-bind xsyn (g-concrete x)))
              (ysyn (syntax-bind ysyn (g-concrete y)))
              ((when (check-int-endp x xsyn)) (if (intcar x) y (lognot y)))
              ((when (check-int-endp y ysyn)) (if (intcar y) x (lognot x))))
           (intcons (iff (intcar x)
                         (intcar y))
                    (logeqv (intcdr x) (intcdr y)))))
  :hints(("Goal" :in-theory (e/d* (logeqv bitops::logand** bitops::logior** bitops::lognot** int-endp
                                          bitops::equal-logcons-strong)
                                 (bitops::logcdr-natp bitops::logcar-of-bit
                                                      bitops::logior-natp-type
                                                      bitops::logand-natp-type-2
                                                      bitops::logcdr-of-bit
                                                      bitops::logcons-negp
                                                      bitops::logand-with-negated-bitmask
                                                      fty::bitp-when-unsigned-byte-p-1
                                                      bitops::logand-natp-type-1
                                                      bitops::logcons-posp-2
                                                      bitops::lognot-negp)))))




(def-gl-rewrite int-less-than-0
  (implies (and (syntaxp (gl-object-case x :g-integer))
                (integerp x))
           (equal (< x 0)
                  (b* ((x-endp (check-int-endp x (syntax-bind xsyn (g-concrete x))))
                       ((when x-endp)
                        (intcar x)))
                    (< (intcdr x) 0))))
  :hints(("Goal" :in-theory (enable int-endp))))

(define check-signed-byte-p (n x)
  (signed-byte-p n x))

(table gl-fn-modes 'check-signed-byte-p
       (make-gl-function-mode :dont-expand-def t))

(def-gl-rewrite check-signed-byte-p-by-syntax-when-const-width
  (implies (and (syntaxp (and (gl-object-case x :g-integer)
                              (gl-object-case n :g-concrete)))
                (integerp x)
                (b* (((when (zp n)) nil)
                     (x-endp (check-int-endp x (syntax-bind xsyn (g-concrete x))))
                     ((when x-endp) t))
                  (check-signed-byte-p (1- n) (intcdr x))))
           (equal (check-signed-byte-p n x) t))
  :hints(("Goal" :in-theory (e/d (check-signed-byte-p
                                  bitops::signed-byte-p**
                                  int-endp)
                                 (signed-byte-p)))))

(define check-unsigned-byte-p (n x)
  (unsigned-byte-p n x))

(table gl-fn-modes 'check-unsigned-byte-p
       (make-gl-function-mode :dont-expand-def t))

(def-gl-rewrite check-unsigned-byte-p-by-syntax-when-const-width
  (implies (and (syntaxp (and (gl-object-case x :g-integer)
                              (gl-object-case n :g-concrete)))
                (integerp x)
                (b* (((unless (natp n)) nil)
                     (x-endp (check-int-endp x (syntax-bind xsyn (g-concrete x))))
                     ((when x-endp) (not (intcar x))))
                  (check-unsigned-byte-p (1- n) (intcdr x))))
           (equal (check-unsigned-byte-p n x) t))
  :hints(("Goal" :in-theory (e/d (check-unsigned-byte-p
                                  bitops::unsigned-byte-p**
                                  int-endp)
                                 (unsigned-byte-p)))))

(table gl-fn-modes 'acl2::loghead$inline
       (make-gl-function-mode :dont-expand-def t))

(def-gl-rewrite loghead-const-width
  (implies (syntaxp (integerp n))
           (equal (loghead n x)
                  (if (or (zp n)
                          (and (check-int-endp x (syntax-bind xsyn (g-concrete x)))
                               (not (intcar x))))
                      0
                    (intcons (and (intcar x) t)
                             (loghead (1- n) (intcdr x))))))
  :hints(("Goal" :in-theory (enable intcons intcar intcdr int-endp
                                    bitops::loghead**))))

(table gl-fn-modes 'logext
       (make-gl-function-mode :dont-expand-def t))

(def-gl-rewrite logext-const-width
  (implies (syntaxp (integerp n))
           (equal (logext n x)
                  (cond ((or (zp n)
                             (eql n 1)
                             (check-int-endp x (syntax-bind xsyn (g-concrete x))))
                         (endint (and (intcar x) t)))
                        (t (intcons (and (intcar x) t)
                                    (logext (1- n) (intcdr x)))))))
  :hints(("Goal" :in-theory (enable intcons intcar intcdr int-endp
                                    bitops::logext**))))

(table gl-fn-modes 'acl2::logtail$inline
       (make-gl-function-mode :dont-expand-def t))

(def-gl-rewrite logtail-const-shift
  (implies (syntaxp (integerp n))
           (equal (logtail n x)
                  (if (or (zp n)
                          (check-int-endp x (syntax-bind xsyn (g-concrete x))))
                      (int x)
                    (logtail (1- n) (intcdr x)))))
  :hints(("Goal" :in-theory (enable intcons intcar intcdr int-endp
                                    bitops::logtail**))))

(local (defthm logcdr-of-nfix
         (equal (logcdr (nfix x))
                (nfix (logcdr x)))
         :hints(("Goal" :in-theory (enable nfix))
                (and stable-under-simplificationp
                     '(:in-theory (enable ifix logcdr))))))



(local (defthm signed-byte-p-implies-less-than-ash-1
         (implies (signed-byte-p n x)
                  (< x (ash 1 (+ -1 n))))
         :hints(("Goal" :in-theory (enable signed-byte-p
                                           bitops::ash-is-expt-*-x)))
         :rule-classes :forward-chaining))

(local (defthm signed-byte-p-implies-neg-lte-ash-1
         (implies (signed-byte-p n x)
                  (<= (- x) (ash 1 (+ -1 n))))
         :hints(("Goal" :in-theory (enable signed-byte-p
                                           bitops::ash-is-expt-*-x)))
         :rule-classes :forward-chaining))

;; (local (defthm ash-1-when-signed-byte-p
;;          (implies (signed-byte-p n x)
;;                   (< x (ash 1 n)))
;;          :hints(("Goal" :in-theory (e/d* (bitops::ihsext-inductions
;;                                           bitops::ihsext-recursive-redefs)
;;                                          (signed-byte-p))))))

;; (local (defthm ash-1-when-signed-byte-p-2
;;          (implies (signed-byte-p n x)
;;                   (<= (- x) (ash 1 n)))
;;          :hints(("Goal" :in-theory (e/d* (bitops::ash-is-expt-*-x
;;                                           signed-byte-p))
;;                  :expand ((expt 2 n))))))



(local (defthm ash-1-posp
         (implies (posp n)
                  (and (integerp (ash 1 n))
                       (< 1 (ash 1 n))))
         :hints(("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                          bitops::ihsext-recursive-redefs)
                                         (signed-byte-p))))           
         :rule-classes :type-prescription))

(local (defthm signed-byte-p-fwd
         (implies (signed-byte-p n x)
                  (and (posp n) (integerp x)))
         :rule-classes :forward-chaining))

(local (defthm posp-ash-1
         (implies (natp n)
                  (posp (ash 1 n)))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)))
         :rule-classes :type-prescription))

(define logtail-helper ((shift integerp)
                        (shift-bound natp)
                        (x integerp))
  :verify-guards nil
  (if (<= (ifix shift) (nfix shift-bound))
      (logtail shift x)
    (ifix x))
  ///
  (def-gl-rewrite logtail-helper-impl
    (implies (and (syntaxp (and (gl-object-case shift :g-integer)
                                (natp shift-bound)))
                  (natp shift-bound)
                  (integerp shift))
             (equal (logtail-helper shift shift-bound x)
                    (cond ((eql 0 shift-bound)
                           (int x))
                          ((eql shift shift-bound)
                           (logtail shift-bound x))
                          (t (logtail-helper shift (1- shift-bound) x)))))
    :hints(("Goal" :in-theory (enable bitops::logtail**))))

  (local (defthm logtail-when-signed-byte-p-lemma
           (implies (signed-byte-p n (ifix x))
                    (equal (logtail (+ -1 n) x)
                           (if (< (ifix x) 0) -1 0)))
           :hints(("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)
                                           (signed-byte-p))
                   :induct (logtail n x)))))

  (local (defthm logtail-when-signed-byte-p
           (implies (and (signed-byte-p n (ifix x))
                         (<= (+ -1 n) (nfix m)))
                    (equal (logtail m x)
                           (if (< (ifix x) 0) -1 0)))
           :hints(("Goal" :use ((:instance logtail-when-signed-byte-p-lemma
                                 (n (+ 1 (nfix m)))))))))

  (local (defthm logtail-when-signed-byte-p-no-ifix
           (implies (and (signed-byte-p n x)
                         (<= (+ -1 n) (nfix m)))
                    (equal (logtail m x)
                           (if (< (ifix x) 0) -1 0)))
           :hints(("Goal" :use ((:instance logtail-when-signed-byte-p
                                 (n (+ 1 (nfix m)))))
                   :in-theory (disable logtail-when-signed-byte-p)))))
  ;; (local (in-theory (disable max)))


  (def-gl-rewrite logtail-to-logtail-helper
    (implies (and (syntaxp (gl-object-case shift :g-integer))
                  (integerp shift))
             (equal (logtail shift x)
                    (b* ((x (int x))
                         (xwidth (syntax-bind xwidth (gl-object-case x
                                                       :g-integer (max 1 (len x.bits))
                                                       :g-concrete (+ 1 (integer-length x.val))
                                                       :otherwise nil)))
                         ((unless (and xwidth
                                       (check-signed-byte-p xwidth x)))
                          (abort-rewrite (logtail shift x)))
                         (shiftwidth (syntax-bind shiftwidth (len (g-integer->bits shift))))
                         ((unless (check-signed-byte-p shiftwidth shift))
                          (abort-rewrite (logtail shift x)))
                         (bound (min (1- (ash 1 (1- shiftwidth))) (1- xwidth))))
                      (if (< bound shift)
                          (logtail bound x)
                        (logtail-helper shift bound x)))))
    :hints(("Goal" :in-theory (e/d (check-signed-byte-p)
                                   (signed-byte-p
                                    signed-byte-p-implies-neg-lte-ash-1
                                    signed-byte-p-implies-less-than-ash-1))
            :use ((:instance signed-byte-p-implies-less-than-ash-1 (n xwidth) (x (ifix x)))
                  (:instance signed-byte-p-implies-neg-lte-ash-1 (n xwidth) (x (ifix x)))
                  (:instance signed-byte-p-implies-less-than-ash-1 (n shiftwidth) (x shift))
                  ;; (:instance ash-1-when-signed-byte-p (n shiftwidth) (x shift))
                  )
            )))

  (table gl-fn-modes 'logtail-helper
       (make-gl-function-mode :dont-expand-def t)))


(def-gl-rewrite logbitp-const-index
  (implies (syntaxp (integerp n))
           (equal (logbitp n x)
                  (intcar (logtail n x))))
  :hints(("Goal" :in-theory (enable intcons intcar intcdr int-endp))))


(define logbitp-helper ((index integerp)
                        (index-bound natp)
                        (x integerp))
  :verify-guards nil
  (if (<= (ifix index) (nfix index-bound))
      (logbitp index x)
    (intcar x))
  ///
  (def-gl-rewrite logbitp-helper-impl
    (implies (and (syntaxp (and (gl-object-case index :g-integer)
                                (natp index-bound)))
                  (natp index-bound)
                  (integerp index))
             (equal (logbitp-helper index index-bound x)
                    (cond ((eql 0 index-bound)
                           (intcar x))
                          ((eql index index-bound)
                           (logbitp index-bound x))
                          (t (logbitp-helper index (1- index-bound) x)))))
    :hints(("Goal" :in-theory (enable bitops::logbitp**))))

  ;; (local (defthm logbitp-when-signed-byte-p-lemma
  ;;          (implies (signed-byte-p n (ifix x))
  ;;                   (equal (logbitp n x)
  ;;                          (if (< (ifix x) 0) -1 0)))
  ;;          :hints(("Goal" :in-theory (e/d* (bitops::ihsext-inductions
  ;;                                           bitops::ihsext-recursive-redefs)
  ;;                                          (signed-byte-p))))))
  (local (defun logbitp-when-signed-byte-p-ind (n m x)
           (if (zp n)
               (list m x)
             (logbitp-when-signed-byte-p-ind (1- n) (1- m) (logcdr x)))))

  (local (defthm logcdr-when-endp
           (implies (int-endp x)
                    (equal (logcdr x) (ifix x)))
           :hints(("Goal" :in-theory (enable int-endp)))))

  (local (defthm int-endp-by-bound
           (implies (and (<= -1 (ifix x))
                         (< (ifix x) 1))
                    (int-endp x))
           :hints(("Goal" :in-theory (enable int-endp)))))

  (local (defthm logbitp-when-int-endp
           (implies (int-endp x)
                    (equal (logbitp n x) (< (ifix x) 0)))
           :hints(("Goal" :in-theory (enable int-endp)))))

  (local (defthm logbitp-when-signed-byte-p
           (implies (and (signed-byte-p n (ifix x))
                         (<= (+ -1 n) (nfix m)))
                    (equal (logbitp m x) (< (ifix x) 0)))
           :hints (("goal" :induct (logbitp-when-signed-byte-p-ind n m x)
                    :expand ((signed-byte-p n (ifix x))
                             (logbitp m x))
                    :do-not-induct t)
                   )
           :otf-flg t))

  (local (defthm nfix-lower-bound
           (implies (integerp x)
                    (<= x (nfix x)))
           :hints(("Goal" :in-theory (enable nfix)))
           :rule-classes :linear))

  (def-gl-rewrite logbitp-to-logbitp-helper
    (implies (and (syntaxp (gl-object-case index :g-integer))
                  (integerp index))
             (equal (logbitp index x)
                    (b* ((x (int x))
                         (xwidth (syntax-bind xwidth (gl-object-case x
                                                       :g-integer (len x.bits)
                                                       :g-concrete (+ 1 (integer-length x.val))
                                                       :otherwise nil)))
                         ((unless (and xwidth
                                       (check-signed-byte-p xwidth x)))
                          (abort-rewrite (logbitp index x)))
                         (indexwidth (syntax-bind indexwidth (len (g-integer->bits index))))
                         ((unless (check-signed-byte-p indexwidth index))
                          (abort-rewrite (logbitp index x)))
                         (bound (1- (min (ash 1 (1- indexwidth)) (1- xwidth)))))
                      (if (< bound index)
                          (< x 0)
                        (logbitp-helper index bound x)))))
    :hints(("Goal" :in-theory (e/d (check-signed-byte-p)
                                   (signed-byte-p
                                    signed-byte-p-implies-less-than-ash-1
                                    signed-byte-p-implies-neg-lte-ash-1))
            :use ((:instance signed-byte-p-implies-less-than-ash-1 (n xwidth) (x (ifix x)))
                  (:instance signed-byte-p-implies-neg-lte-ash-1 (n xwidth) (x (ifix x)))
                  (:instance signed-byte-p-implies-less-than-ash-1 (n indexwidth) (x index)))
            :do-not-induct t))
    :otf-flg t)

  (table gl-fn-modes 'logbitp-helper
       (make-gl-function-mode :dont-expand-def t))

  (table gl-fn-modes 'logbitp
       (make-gl-function-mode :dont-expand-def t)))

(define logbitp-helper2 ((place posp)
                         (digit natp)
                         (digit-width natp)
                         (x integerp))
  :verify-guards nil
  (logbitp (* (lposfix place) (loghead digit-width digit)) x)
  ///
  (local (defthm commutativity-2-of-*
           (equal (* y x z)
                  (* x y z))
           :hints (("goal" :use ((:instance associativity-of-*)
                                 (:instance commutativity-of-*)
                                 (:instance associativity-of-*
                                  (x y) (y x)))
                    :in-theory (disable associativity-of-* commutativity-of-*)))))

  (def-gl-rewrite logbitp-helper2-impl
    (implies (and (syntaxp (and (gl-object-case digit :g-integer)
                                (posp place)
                                (natp digit-width)))
                  (posp place)
                  (natp digit-width)
                  (integerp digit))
             (equal (logbitp-helper2 place digit digit-width x)
                    (b* (((when (or (check-int-endp x (syntax-bind xsyn (g-concrete x)))
                                    (eql 0 digit-width)))
                          (intcar x)))
                      (if (intcar digit)
                          (logbitp-helper2 (* 2 place) (intcdr digit) (1- digit-width) (logtail place x))
                        (logbitp-helper2 (* 2 place) (intcdr digit) (1- digit-width) x)))))
    :hints(("Goal" :in-theory (enable bitops::logbitp**
                                      int-endp)
            :expand ((loghead digit-width digit)
                     (:free (b) (logcons b (loghead (+ -1 digit-width) (logcdr digit))))))))


  (local (defthm loghead-when-signed-byte-p
           (implies (and (<= 0 (ifix x))
                         (signed-byte-p n x))
                    (equal (loghead (+ -1 n) x)
                           (ifix x)))
           :hints(("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)
                                           (signed-byte-p))))))

  (def-gl-rewrite logbitp-to-logbitp2-helper
    (equal (logbitp index x)
           (b* ((index (nfix (int index)))
                (idx-width (syntax-bind idx-width (gl-object-case index
                                                    :g-integer (max 1 (len index.bits))
                                                    :g-concrete (+ 1 (integer-length index.bits))
                                                    :otherwise nil)))
                ((unless (and idx-width
                              (check-signed-byte-p idx-width index)))
                 (abort-rewrite (logbitp index x)))
                (x (int x))
                ;; (xwidth (syntax-bind xwidth (gl-object-case x
                ;;                               :g-integer (len x.bits)
                ;;                               :g-concrete (+ 1 (integer-length x.val))
                ;;                               :otherwise nil)))
                ;; ((unless (and xwidth
                ;;               (check-signed-byte-p xwidth x)))
                ;;  (abort-rewrite (logbitp index x)))
                ;; (indexwidth (syntax-bind indexwidth (len (g-integer->bits index))))
                ;; ((unless (check-signed-byte-p indexwidth index))
                ;;  (abort-rewrite (logbitp index x)))
                ;; (bound (1- (min (ash 1 (1- indexwidth)) (1- xwidth))))
                )
             (logbitp-helper2 1 index (1- idx-width) x)))
    :hints(("Goal" :in-theory (e/d (check-signed-byte-p)
                                   (signed-byte-p
                                    ;; signed-byte-p-implies-less-than-ash-1
                                    ;; signed-byte-p-implies-neg-lte-ash-1
                                    ))
            ;; :use ((:instance signed-byte-p-implies-less-than-ash-1 (n idx-width) (x (nfix index))))
            :do-not-induct t))
    :otf-flg t)

  (table gl-fn-modes 'logbitp-helper2
       (make-gl-function-mode :dont-expand-def t))

  (table gl-fn-modes 'logbitp
       (make-gl-function-mode :dont-expand-def t)))


(table gl-fn-modes 'acl2::logmask$inline
       (make-gl-function-mode :dont-expand-def t))



(define logmask-helper ((width integerp)
                        (width-max natp)
                        (shift natp))
  :verify-guards nil
  (logtail shift (acl2::logmask (min (ifix width) (nfix width-max))))
  ///
  (local (defun tail-of-mask-ind (width shift)
           (if (zp width)
               shift
             (tail-of-mask-ind (1- width) (1- shift)))))
  (local (defthm logtail-of-logmask
           (implies (<= (nfix width) (nfix shift))
                    (equal (logtail shift (acl2::logmask width)) 0))
           :hints(("Goal" :in-theory (e/d* (bitops::ihsext-recursive-redefs)
                                           (acl2::logmask))
                   :induct (tail-of-mask-ind width shift)))))

  (def-gl-rewrite logmask-helper-impl
    (implies (and (syntaxp (and (gl-object-case width :g-integer)
                                (natp width-max)
                                (natp shift)))
                  (natp width-max)
                  (natp shift)
                  (integerp width))
             (equal (logmask-helper width width-max shift)
                    (if (<= width-max shift)
                        0
                      (intcons (< shift width)
                               (logmask-helper width width-max (+ 1 shift))))))
    :hints(("Goal" :in-theory (e/d (bitops::logmask** bitops::logtail**
                                                      bool->bit bitops::equal-logcons-strong)
                                   (acl2::logmask))
            ;; :cases ((zp width))
            :expand ((acl2::logmask width)))))

  (def-gl-rewrite logmask-to-logmask-helper
    (implies (syntaxp (not (gl-object-case width :g-concrete)))
             (equal (acl2::logmask width)
                    (b* ((width (int width))
                         ((when (syntax-bind width-concrete (gl-object-case width :g-concrete)))
                          (acl2::logmask width))
                         ((unless (syntax-bind width-g-integer (gl-object-case width :g-integer)))
                          (abort-rewrite (acl2::logmask width)))
                         (widthwidth (syntax-bind widthwidth (len (g-integer->bits width))))
                         ((unless (check-signed-byte-p widthwidth width))
                          (abort-rewrite (acl2::logmask width)))
                         (bound (1- (ash 1 (1- widthwidth)))))
                      (logmask-helper width bound 0))))
    :hints(("Goal" :in-theory (e/d (check-signed-byte-p)
                                   (signed-byte-p acl2::logmask
                                    signed-byte-p-implies-less-than-ash-1))
            :use ((:instance signed-byte-p-implies-less-than-ash-1 (n widthwidth) (x (ifix width)))))))

  ;; (local (defthm logand-of-logmask
  ;;          (equal (logand (acl2::logmask n) x)
  ;;                 (loghead n x))
  ;;          :hints(("Goal" :in-theory (disable acl2::logmask)))))

  (local (defun loghead-signed-byte-ind (n w x)
           (if (zp n)
               (list w x)
             (loghead-signed-byte-ind (1- n) (1- w) (logcdr x)))))

  (local (defthm loghead-when-signed-byte-p
           (implies (and (signed-byte-p n (ifix x))
                         (<= (+ -1 n) (ifix w))
                         (<= 0 (ifix x)))
                    (equal (loghead w x) (ifix x)))
           :hints(("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)
                                           (signed-byte-p))
                   :induct (loghead-signed-byte-ind n w x)))))

  (def-gl-rewrite loghead-to-logmask-helper
    (implies (syntaxp (not (gl-object-case width :g-concrete)))
             (equal (loghead width x)
                    (b* ((width (int width))
                         (x (int x))
                         ((when (syntax-bind width-concrete (gl-object-case width :g-concrete)))
                          (loghead width x))
                         ((unless (syntax-bind width-g-integer (gl-object-case width :g-integer)))
                          (abort-rewrite (loghead width x)))
                         (xwidth (syntax-bind xwidth (gl-object-case x
                                                       :g-integer (len x.bits)
                                                       :g-concrete (+ 1 (integer-length x.val))
                                                       :otherwise nil)))
                         ((unless (and xwidth
                                       (check-signed-byte-p xwidth x)))
                          (abort-rewrite (loghead width x)))
                         (x-nonneg (<= 0 x))
                         (x-const-nonneg (syntax-bind x-const-nonneg (equal x-nonneg t)))
                         (widthwidth (syntax-bind widthwidth (len (g-integer->bits width))))
                         ((unless (check-signed-byte-p widthwidth width))
                          (abort-rewrite (loghead width x)))
                         (bound (if (and* x-const-nonneg x-nonneg)
                                    (min (1- (ash 1 (1- widthwidth))) (1- xwidth))
                                  (1- (ash 1 (1- widthwidth))))))
                      (logand (logmask-helper width bound 0) x))))
    :hints(("Goal" :in-theory (e/d (check-signed-byte-p)
                                   (signed-byte-p
                                    acl2::logmask
                                    signed-byte-p-implies-less-than-ash-1
                                    signed-byte-p-implies-neg-lte-ash-1
                                                  ))
            :use ((:instance signed-byte-p-implies-less-than-ash-1 (n widthwidth) (x (ifix width))))
            )))

  (table gl-fn-modes 'logmask-helper
       (make-gl-function-mode :dont-expand-def t)))
                         

(def-gl-rewrite logapp-const-width
  (implies (syntaxp (integerp n))
           (equal (logapp n x y)
                  (cond ((zp n) (int y))
                        (t (intcons (intcar x)
                                    (logapp (1- n) (intcdr x) y))))))
  :hints(("Goal" :in-theory (enable intcons intcar intcdr int-endp
                                    bitops::logapp**))))
                         

(define logapp-helper ((width integerp)
                       (width-bound natp)
                       (lsbs integerp)
                       (msbs integerp))
  :verify-guards nil
  (if (<= (ifix width) (nfix width-bound))
      (logapp width lsbs msbs)
    (int msbs))
  ///
  (table gl-fn-modes 'logapp-helper
       (make-gl-function-mode :dont-expand-def t))
  (table gl-fn-modes 'logapp
       (make-gl-function-mode :dont-expand-def t))

  (def-gl-rewrite logapp-helper-impl
    (implies (and (syntaxp (and (gl-object-case width :g-integer)
                                (natp width-bound)))
                  (integerp width)
                  (natp width-bound))
             (equal (logapp-helper width width-bound lsbs msbs)
                    (cond ((equal 0 width-bound)
                           (int msbs))
                          ((equal width width-bound)
                           (logapp width-bound lsbs msbs))
                          (t (logapp-helper width (1- width-bound) lsbs msbs)))))
                          
    :hints(("Goal" :in-theory (e/d (bitops::logapp**)))))

  

  (def-gl-rewrite logapp-to-logapp-helper
    (implies (syntaxp (not (gl-object-case width :g-concrete)))
             (equal (logapp width lsbs msbs)
                    (b* ((width (nfix (int width)))
                         ((when (syntax-bind width-concrete (gl-object-case width :g-concrete)))
                          (logapp width lsbs msbs))
                         (widthwidth (syntax-bind widthwidth (gl-object-case width
                                                               :g-integer (len width.bits)
                                                               :otherwise nil)))
                         ((unless (and widthwidth
                                       (check-signed-byte-p widthwidth width)))
                          (abort-rewrite (logapp width lsbs msbs)))
                         (bound (1- (ash 1 (1- widthwidth)))))
                      (logapp-helper width bound lsbs msbs))))
    :hints(("Goal" :in-theory (e/d (check-signed-byte-p)
                                   (signed-byte-p))))))


(define rightshift-helper ((shift integerp)
                           (shift-bound integerp)
                           (x integerp))
  :verify-guards nil
  (if (<= (- (ifix shift)) (- (ifix shift-bound)))
      (logtail (- (ifix shift)) x)
    (ifix x))
  ///
  (def-gl-rewrite rightshift-helper-impl
    (implies (and (syntaxp (and (gl-object-case shift :g-integer)
                                (integerp shift-bound)))
                  (integerp shift-bound)
                  (integerp shift))
             (equal (rightshift-helper shift shift-bound x)
                    (cond ((<= 0 shift-bound)
                           (int x))
                          ((eql shift shift-bound)
                           (logtail (- shift-bound) x))
                          (t (rightshift-helper shift (1+ shift-bound) x)))))
    :hints(("Goal" :expand ((logtail (- shift) x)))))

  (table gl-fn-modes 'rightshift-helper
       (make-gl-function-mode :dont-expand-def t)))

(local (defthm logtail-when-zp
         (implies (zp n)
                  (equal (logtail n x) (ifix x)))
         :hints (("goal" :expand ((logtail n x))))))

(local (defthm minus-minus
         (equal (- (- x))
                (fix x))))




(def-gl-rewrite ash-impl
  (equal (ash x sh)
         (b* ((sh (int sh))
              (x (int x))
              ((when (<= 0 sh))
               (logapp (nfix sh) 0 x))
              ((when (equal 0 sh)) (int x))
              ((when (syntax-bind sh-concrete (gl-object-case sh :g-concrete)))
               (logtail (- sh) x))
              (shwidth (syntax-bind shwidth (gl-object-case sh
                                              :g-integer (len sh.bits)
                                              :otherwise nil)))
              ((unless (and shwidth
                            (check-signed-byte-p shwidth sh)))
               (abort-rewrite (ash x sh)))
              (bound (- (ash 1 (1- shwidth)))))
           (rightshift-helper sh bound x)))
  :hints (("goal" ;; :expand ((logtail (- sh) x))
           :in-theory (e/d (rightshift-helper check-signed-byte-p)
                           (signed-byte-p)))))

(table gl-fn-modes 'ash
       (make-gl-function-mode :dont-expand-def t))



(define +carry ((c booleanp)
                (x integerp)
                (y integerp))
  (+ (bool->bit c)
     (lifix x)
     (lifix y))
  ///
  (table gl-fn-modes '+carry
       (make-gl-function-mode :dont-expand-def t))

  (def-gl-rewrite fgl-+carry
    (equal (+carry c x y)
           (intcons (xor c (xor (intcar x) (intcar y)))
                    (if (and (check-int-endp x (syntax-bind xsyn (g-concrete x)))
                             (check-int-endp y (syntax-bind ysyn (g-concrete y))))
                        (endint (if* c
                                     (and (intcar x) (intcar y))
                                     (or (intcar x) (intcar y))))
                      (+carry (if* c
                                   (or (intcar x) (intcar y))
                                   (and (intcar x) (intcar y)))
                              (intcdr x)
                              (intcdr y)))))
    :hints(("Goal" :in-theory (enable +carry int-endp if*
                                      bitops::equal-logcons-strong
                                      bitops::logxor** b-not))))

  (def-gl-rewrite +-to-+carry
    (implies (and (integerp x) (integerp y))
             (equal (+ x y) (+carry nil x y))))

  (def-gl-rewrite minus-to-+carry
    (implies (integerp x)
             (equal (- x) (+carry t 0 (lognot x))))
    :hints(("Goal" :in-theory (enable lognot)))))

(encapsulate nil
  (local (defthm replace-mult
           (implies (equal (+ 1 z) x)
                    (equal (* x y)
                           (+ y (* z y))))))
  (local (defthm commute-*-2
           (equal (* y x z) (* x y z))
           :hints (("goal" :use ((:instance associativity-of-*)
                                 (:instance associativity-of-*
                                  (x y) (y x)))
                    :in-theory (disable associativity-of-*)))))

  (def-gl-rewrite fgl-*
    (implies (and (integerp x) (integerp y))
             (equal (* x y)
                    (if (check-int-endp x (syntax-bind xsyn (g-concrete x)))
                        (if (intcar x) (- y) 0)
                      (+ (if (intcar x) y 0)
                         (intcons nil
                                  (* (intcdr x) y))))))
    :hints(("Goal" :in-theory (e/d (int-endp logcons)
                                   (acl2::logcar-logcdr-elim
                                    bitops::logcons-destruct))
            :use ((:instance acl2::logcar-logcdr-elim
                   (i x)))))))



(define </= ((x integerp) (y integerp))
  (mv (< (ifix x) (ifix y))
      (equal (ifix x) (ifix y)))
  ///
  (table gl-fn-modes '</=
         (make-gl-function-mode :dont-expand-def t))

  (local (defthm logcar-when-zip
           (implies (zip x) (equal (logcar x) 0))
           :hints(("Goal" :in-theory (enable logcar)))))

  (def-gl-rewrite </=-impl
    (equal (</= x y)
           (b* ((x (int x))
                (y (int y))
                ((when (and (check-int-endp x (syntax-bind xsyn (g-concrete x)))
                            (check-int-endp y (syntax-bind ysyn (g-concrete y)))))
                 (mv (and (intcar x) (not (intcar y)))
                     (iff (intcar x) (intcar y))))
                ((mv rest< rest=) (</= (intcdr x) (intcdr y))))
             (mv (or* rest<
                     (and* rest= (not (intcar x)) (intcar y)))
                 (and* rest= (iff (intcar x) (intcar y))))))
    :hints(("Goal" :in-theory (e/d (int-endp or* and*
                                    bitops::logcons-<-n-strong
                                    bitops::logcons->-n-strong)
                                   (cons-equal not))
            :cases ((integerp x)))
           '(:cases ((integerp y)))))

  (def-gl-rewrite <-impl
    (implies (and (integerp x) (integerp y))
             (equal (< x y)
                    (if (and (syntax-bind y-0 (eql y 0))
                             (equal y 0))
                        (if (check-int-endp x (syntax-bind xsyn (g-concrete x)))
                            (intcar x)
                          (< (intcdr x) 0))
                      (mv-nth 0 (</= x y)))))
    :hints(("Goal" :in-theory (enable int-endp)))))

(define check-integerp (x xsyn)
  :verify-guards nil
  (and (gobj-syntactic-integerp xsyn)
       (integerp x))
  ///
  (defthm check-integerp-open
    (iff (check-integerp x xsyn)
         (and* (gobj-syntactic-integerp xsyn)
               (integerp x)))))



(define gobj-non-integerp ((x gl-object-p))
  (gl-object-case x
    :g-boolean t
    :g-concrete (not (integerp x.val))
    :g-cons t
    :otherwise nil))

(define check-non-integerp (x xsyn)
  :verify-guards nil
  (and (gobj-non-integerp xsyn)
       (not (integerp x)))
  ///
  (defthm check-non-integerp-open
    (iff (check-non-integerp x xsyn)
         (and* (gobj-non-integerp xsyn)
               (not (integerp x))))))

(define check-consp (x xsyn)
  :verify-guards nil
  (and (gobj-syntactic-consp xsyn)
       (consp x))
  ///
  (defthm check-consp-open
    (iff (check-consp x xsyn)
         (and* (gobj-syntactic-consp xsyn)
               (consp x)))))



(define check-booleanp (x xsyn)
  :verify-guards nil
  (and (gobj-syntactic-booleanp xsyn)
       (booleanp x))
  ///
  (defthm check-booleanp-open
    (iff (check-booleanp x xsyn)
         (and* (gobj-syntactic-booleanp xsyn)
               (booleanp x)))))






(define gobj-non-booleanp ((x gl-object-p))
  (gl-object-case x
    :g-integer t
    :g-concrete (not (booleanp x.val))
    :g-cons t
    :otherwise nil))

(define check-non-booleanp (x xsyn)
  :verify-guards nil
  (and (gobj-non-booleanp xsyn)
       (not (booleanp x)))
  ///
  (defthm check-non-booleanp-open
    (iff (check-non-booleanp x xsyn)
         (and* (gobj-non-booleanp xsyn)
               (not (booleanp x))))))

(define gobj-non-consp ((x gl-object-p))
  (gl-object-case x
    :g-integer t
    :g-concrete (not (consp x.val))
    :g-boolean t
    :otherwise nil))

(define check-non-consp (x xsyn)
  :verify-guards nil
  (and (gobj-non-consp xsyn)
       (not (consp x)))
  ///
  (defthm check-non-consp-open
    (iff (check-non-consp x xsyn)
         (and* (gobj-non-consp xsyn)
               (not (consp x))))))

(def-gl-rewrite fgl-equal
  (equal (equal x y)
         (let ((xsyn (syntax-bind xsyn (g-concrete x)))
               (ysyn (syntax-bind ysyn (g-concrete y))))
           (cond ((check-integerp x xsyn)
                  (cond ((check-integerp y ysyn)
                         (and (iff (intcar x) (intcar y))
                              (or (and (check-int-endp x xsyn)
                                       (check-int-endp y ysyn))
                                  (equal (intcdr x) (intcdr y)))))
                        ((check-non-integerp y ysyn) nil)
                        (t (abort-rewrite (equal x y)))))
                 ((check-booleanp x xsyn)
                  (cond ((check-booleanp y ysyn)
                         (iff x y))
                        ((check-non-booleanp y ysyn) nil)
                        (t (abort-rewrite (equal x y)))))
                 ((check-consp x xsyn)
                  (cond ((check-consp y ysyn)
                         (and (equal (car x) (car y))
                              (equal (cdr x) (cdr y))))
                        ((check-non-consp y ysyn) nil)
                        (t (abort-rewrite (equal x y)))))
                 ((and (check-integerp y ysyn)
                       (check-non-integerp x xsyn)) nil)
                 ((and (check-booleanp y ysyn)
                       (check-non-booleanp x xsyn)) nil)
                 ((and (check-consp y ysyn)
                       (check-non-consp x xsyn)) nil)
                 (t (abort-rewrite (equal x y))))))
  :hints(("Goal" :in-theory (enable int-endp))))



(local (defthm xor-facts
         (and (iff (xor x nil) x)
              (iff (xor nil x) x)
              (iff (xor t x) (not x))
              (iff (xor x t) (not x)))))

(define +carry-ext ((width posp)
                      (c booleanp)
                      (x integerp)
                      (y integerp))
  (logext width (+ (bool->bit c)
                    (lifix x)
                    (lifix y)))
  ///
  (table gl-fn-modes '+carry-ext
       (make-gl-function-mode :dont-expand-def t))

  (local (Defthm logext-0
           (equal (logext 0 x)
                  (endint (intcar x)))
           :hints(("Goal" :in-theory (enable bitops::logext**)))))

  (def-gl-rewrite fgl-+carry-ext
    (implies (syntaxp (natp width))
             (equal (+carry-ext width c x y)
                    (b* ((bit0 (xor c (xor (intcar x) (intcar y))))
                         ((when (or (zp width) (eql width 1)))
                          (endint bit0))
                         ((when (and (check-int-endp x (syntax-bind xsyn (g-concrete x)))
                                     (check-int-endp y (syntax-bind ysyn (g-concrete y)))))
                          (intcons bit0
                                   (endint (if* c
                                                (and (intcar x) (intcar y))
                                                (or (intcar x) (intcar y)))))))
                      (intcons bit0
                               (+carry-ext (1- width)
                                             (if* c
                                                  (or (intcar x) (intcar y))
                                                  (and (intcar x) (intcar y)))
                                             (intcdr x)
                                             (intcdr y))))))
    :hints(("Goal" :in-theory (e/d (+carry-ext
                                    int-endp if*
                                    bitops::logext**
                                    bitops::equal-logcons-strong
                                    bitops::logxor** b-not b-xor)
                                   (xor))
            :expand ((:free (x) (logext width x))))))

  ;; (local (defthm signed-byte-p-of-+
  ;;          (implies (and (posp width)
  ;;                        (signed-byte-p width y)
  ;;                        (signed-byte-p width x))
  ;;                   (signed-byte-p (+ 1 width) (+ x y)))
  ;;          :hints(("Goal" :in-theory (enable signed-byte-p)
  ;;                  :expand ((expt 2 width))))))

  ;; (local (defthm signed-byte-p-of--
  ;;          (implies (and (posp width)
  ;;                        (signed-byte-p width x))
  ;;                   (signed-byte-p (+ 1 width) (- x)))
  ;;          :hints(("Goal" :in-theory (enable signed-byte-p)
  ;;                  :expand ((expt 2 width))))))

  ;; (local (defthm signed-byte-p-when-<=
  ;;          (implies (and (signed-byte-p width1 x)
  ;;                        (integerp width2)
  ;;                        (<= width1 width2))
  ;;                   (signed-byte-p width2 x))
  ;;          :hints(("Goal" :in-theory (disable signed-byte-p)))))

  ;; (local (defthm logext-when-signed-byte-p
  ;;          (implies (signed-byte-p width x)
  ;;                   (equal (logext width x) x))
  ;;          :hints(("Goal" :in-theory (e/d* (bitops::ihsext-inductions
  ;;                                           bitops::ihsext-recursive-redefs)
  ;;                                          (signed-byte-p))))))

  ;; (def-gl-rewrite +-to-+carry-ext
  ;;   (implies (and (integerp x) (integerp y))
  ;;            (equal (+ x y)
  ;;                   (b* ((x (int x))
  ;;                        (y (int y))
  ;;                        ((when (syntax-bind concrete (and (gl-object-case x :g-concrete)
  ;;                                                          (gl-object-case y :g-concrete))))
  ;;                         (+ x y))
  ;;                        (xwidth (syntax-bind xwidth (gl-object-case x
  ;;                                                      :g-integer (len x.bits)
  ;;                                                      :g-concrete (+ 1 (integer-length x.val))
  ;;                                                      :otherwise nil)))
  ;;                        ((unless (and xwidth
  ;;                                      (check-signed-byte-p xwidth x)))
  ;;                         (abort-rewrite (+ x y)))
  ;;                        (ywidth (syntax-bind ywidth (gl-object-case y
  ;;                                                      :g-integer (len y.bits)
  ;;                                                      :g-concrete (+ 1 (integer-length y.val))
  ;;                                                      :otherwise nil)))
  ;;                        ((unless (and ywidth
  ;;                                      (check-signed-byte-p ywidth y)))
  ;;                         (abort-rewrite (+ x y)))
  ;;                        (width (+ 1 (max xwidth ywidth))))
  ;;                     (+carry-ext width nil x y))))
  ;;   :hints(("Goal" :in-theory (e/d (check-signed-byte-p)
  ;;                                  (signed-byte-p)))))

  ;; (def-gl-rewrite minus-to-+carry-ext
  ;;   (implies (integerp x)
  ;;            (equal (- x)
  ;;                   (b* ((x (int x))
  ;;                        ((when (syntax-bind concrete (gl-object-case x :g-concrete)))
  ;;                         (- x))
  ;;                        (xwidth (syntax-bind xwidth (gl-object-case x
  ;;                                                      :g-integer (len x.bits)
  ;;                                                      :otherwise nil)))
  ;;                        ((unless (and xwidth
  ;;                                      (check-signed-byte-p xwidth x)))
  ;;                         (abort-rewrite (- x)))
  ;;                        (width (+ 1 xwidth)))
  ;;                     (+carry-ext width t 0 (lognot x)))))
  ;;   :hints(("Goal" :in-theory (e/d (lognot check-signed-byte-p)
  ;;                                  (signed-byte-p)))))
  )

(define +carry-trunc ((width natp)
                      (c booleanp)
                      (x integerp)
                      (y integerp))
  (loghead width (+ (bool->bit c)
                    (lifix x)
                    (lifix y)))
  ///
  (table gl-fn-modes '+carry-trunc
       (make-gl-function-mode :dont-expand-def t))

  ;; (local (Defthm logext-0
  ;;          (equal (logext 0 x)
  ;;                 (endint (intcar x)))
  ;;          :hints(("Goal" :in-theory (enable bitops::logext**)))))

  (def-gl-rewrite fgl-+carry-trunc
    (implies (syntaxp (natp width))
             (equal (+carry-trunc width c x y)
                    (b* (((when (zp width)) 0))
                      (intcons (xor c (xor (intcar x) (intcar y)))
                               (+carry-trunc (1- width)
                                             (if* c
                                                  (or (intcar x) (intcar y))
                                                  (and (intcar x) (intcar y)))
                                             (intcdr x)
                                             (intcdr y))))))
    :hints(("Goal" :in-theory (e/d (+carry-trunc
                                    int-endp if*
                                    bitops::loghead**
                                    bitops::equal-logcons-strong
                                    bitops::logxor** b-not b-xor)
                                   (xor))
            :expand ((:free (x) (loghead width x)))))))



(define logcount-helper ((width natp)
                         (signbit booleanp)
                         (x integerp))
  (logcount (loghead width (if signbit (lognot x) x)))
  ///
  (table gl-fn-modes 'logcount-helper
       (make-gl-function-mode :dont-expand-def t))

  (local (defthm logcount-of-loghead-<=-width
           (<= (logcount (loghead width x)) (nfix width))
           :hints (("goal" 
                    :in-theory (enable* bitops::ihsext-inductions
                                        bitops::ihsext-recursive-redefs)))
           :rule-classes :linear))

  (local (defthmd loghead-of-integer-length-of-bound
           (implies (and (natp x) (integerp y) (<= x y))
                    (equal (loghead (integer-length y) x)
                           x))
           :hints (("goal" :induct (logand x y)
                    :in-theory (enable* bitops::ihsext-inductions
                                        bitops::ihsext-recursive-redefs)))))

  (def-gl-rewrite logcount-helper-impl
    (implies (and (syntaxp (and (gl-object-case x :g-integer)
                                (natp width)))
                  (natp width))
             (equal (logcount-helper width signbit x)
                    (if (zp width)
                        0
                      (b* ((len (integer-length width)))
                        (+carry-trunc len
                                      (xor signbit (intcar x))
                                      0
                                      (logcount-helper (1- width) signbit (intcdr x)))))))
  :hints(("Goal" :in-theory (e/d* (+carry-trunc)
                                  (acl2::loghead-identity
                                   ;;acl2::zip-open
                                   acl2::unsigned-byte-p**
                                   unsigned-byte-p
                                   bitops::logcons->-constant))
          :expand ((loghead width x)
                   (loghead width -1)
                   (lognot x)
                   (integer-length width)
                   (:free (x y) (loghead width (logcons x y)))
                   (:free (x y) (logcount (logcons x y))))
          :use ((:instance loghead-of-integer-length-of-bound
                 (x (logcount-helper width signbit x))
                 (y width))))))


  (local (defthm logcount-of-ifix
           (equal (logcount (ifix x)) (logcount x))
           :hints(("Goal" 
                   :expand ((logcount (ifix x))
                            (logcount x))))))

  (local (defthm logcount-of-loghead-when-signed-byte-p
           (implies (and (signed-byte-p width (ifix x))
                         (not (acl2::negp x)))
                    (equal (logcount (loghead width x))
                           (logcount x)))
           :hints(("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)
                                           (signed-byte-p))))))

  (local (defthm logcount-of-lognot
           (equal (logcount (lognot x))
                  (logcount x))
           :hints (("goal" :in-theory (enable logcount)))))

  (def-gl-rewrite logcount-impl
    (equal (logcount x)
           (b* ((x (int x))
                ((when (syntax-bind x-concrete (gl-object-case x :g-concrete)))
                 (logcount x))
                (xwidth (syntax-bind xwidth (gl-object-case x
                                              :g-integer (len x.bits)
                                              :otherwise nil)))
                ((unless (and xwidth
                              (check-signed-byte-p xwidth x)))
                 (abort-rewrite (logcount x)))
                (x-neg (< x 0)))
             (logcount-helper xwidth x-neg x)))
    :hints(("Goal" :in-theory (e/d (check-signed-byte-p
                                    bitops::logcount**)
                                   (signed-byte-p))))))



;; (def-gl-rewrite fgl-logcount
;;   (equal (logcount x)
;;          (b* ((x (int x)))
;;            (if (check-int-endp x (syntax-bind xsyn (g-concrete x)))
;;                0
;;              (if (acl2::negp x)
;;                  (if (eql x -1)
;;                      0
;;                    (+ (bool->bit (not (intcar x)))
;;                       (logcount (intcdr x))))
;;                (if (eql x 0)
;;                    0
;;                  (+ (bool->bit (intcar x))
;;                     (logcount (intcdr x))))))))
;;   :hints(("Goal" :in-theory (enable int-endp
;;                                     bitops::logcount**))))


(def-gl-rewrite expt-2-of-integer
  (implies (natp x)
           (equal (expt 2 x) (ash 1 x)))
  :hints(("Goal" :in-theory (enable bitops::ash-is-expt-*-x))))

(def-gl-rewrite unsigned-byte-p-const-width
  (implies (syntaxp (integerp n))
           (equal (unsigned-byte-p n x)
                  (and (natp n)
                       (equal x (loghead n x)))))
  :hints(("Goal" :in-theory (e/d (bitops::unsigned-byte-p**)
                                 (unsigned-byte-p)))))

(def-gl-rewrite signed-byte-p-const-width
  (implies (syntaxp (integerp n))
           (equal (signed-byte-p n x)
                  (and (posp n)
                       (equal x (logext n x)))))
  :hints(("Goal" :in-theory (e/d (bitops::signed-byte-p**)
                                 (signed-byte-p)))))




(define integer-length-helper ((bound posp)
                               (x integerp))
  (b* ((x-ext (logext bound x))
       (len (integer-length x-ext)))
    (mv len
        (equal len 0)
        (< x-ext 0)))
  ///
  (table gl-fn-modes 'integer-length-helper
         (make-gl-function-mode :dont-expand-def t))

  (local (defthm loghead-of-integer-length-when-<=
           (implies (and (natp x)
                         (integerp y)
                         (<= x y))
                    (equal (loghead (integer-length y) x) x))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs
                                              bitops::equal-logcons-strong)
                   :induct (logand x y)))))

  (local (defthm integer-length-of-logext
           (implies (posp n)
                    (< (integer-length (logext n x)) n))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))
           :rule-classes :linear))

  (def-gl-rewrite integer-length-helper-impl
    (implies (and (syntaxp (and (gl-object-case x :g-integer)
                                (posp bound)))
                  (posp bound))
             (equal (integer-length-helper bound x)
                    (b* (((when (or (eql bound 1)
                                    (check-int-endp x (syntax-bind xsyn (g-concrete x)))))
                          (mv 0 t (intcar x)))
                         ((mv rest-len rest-endp rest-negp)
                          (integer-length-helper (1- bound) (intcdr x)))
                         (endp (and rest-endp (iff (intcar x) rest-negp)))
                         (bound-len (integer-length (1- bound)))
                         (len (if endp 0 (+carry-trunc bound-len t nil rest-len))))
                      (mv len endp rest-negp))))
    :hints(("Goal" :in-theory (enable int-endp bitops::integer-length**
                                      +carry-trunc)
            :expand ((logext bound x)))
           (and stable-under-simplificationp
                '(:expand ((integer-length (logext (+ -1 bound) (logcdr x))
                           ;; (logext 1 x)
                           ;; (logext bound x)
                           ))))
           ))

  (table gl-fn-modes 'integer-length
         (make-gl-function-mode :dont-expand-def t))

  (def-gl-rewrite integer-length-impl
    (equal (integer-length x)
           (b* ((x (int x))
                ((when (syntax-bind x-concrete (gl-object-case x :g-concrete)))
                 (integer-length x))
                (bound (syntax-bind x-bound
                                    (gl-object-case x :g-integer (len x.bits) :otherwise nil)))
                ((unless (and bound
                              (check-signed-byte-p x-bound x)))
                 (abort-rewrite (integer-length x))))
             (mv-nth 0 (integer-length-helper bound x))))
    :hints(("Goal" :in-theory (e/d (check-signed-byte-p)
                                   (signed-byte-p))))))
