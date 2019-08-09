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

(disable-definition intcons)
(disable-definition intcons*)
(disable-definition endint)
(disable-definition intcar)
(disable-definition intcdr)
(disable-definition int-endp)
(disable-definition int)

(disable-definition acl2::logcons$inline)
(def-gl-rewrite logcons-is-intcons
  (equal (logcons a b) (intcons (eql a 1) b)))

(disable-definition acl2::logcar$inline)
(def-gl-rewrite logcar-is-intcar
  (equal (logcar x) (if (intcar x) 1 0)))

(disable-definition acl2::logcdr$inline)
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

(disable-definition lognot)

(def-gl-rewrite fgl-lognot
  (equal (lognot x)
         (b* ((x (int x))
              (xsyn (syntax-bind xsyn (g-concrete x)))
              ((when (check-int-endp x xsyn)) (endint (not (intcar x)))))
           (intcons (not (intcar x))
                    (lognot (intcdr x)))))
  :hints(("Goal" :in-theory (enable bitops::lognot** int-endp))))

(disable-definition binary-logand)


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

(disable-definition binary-logior)

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

(disable-definition acl2::binary-logxor)

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

(disable-definition acl2::binary-logeqv)

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

(disable-definition check-signed-byte-p)

(def-gl-rewrite check-signed-byte-p-by-syntax-when-const-width
  (implies (and (syntaxp (and (gl-object-case x :g-integer)
                              (gl-object-case n :g-concrete)))
                (integerp x)
                (posp n)
                (b* ((x-endp (check-int-endp x (syntax-bind xsyn (g-concrete x))))
                     ((when x-endp) t))
                  (check-signed-byte-p (1- n) (intcdr x))))
           (equal (check-signed-byte-p n x) t))
  :hints(("Goal" :in-theory (e/d (check-signed-byte-p
                                  bitops::signed-byte-p**
                                  int-endp)
                                 (signed-byte-p)))))

(define check-unsigned-byte-p (n x)
  (unsigned-byte-p n x))

(disable-definition check-unsigned-byte-p)

(def-gl-rewrite check-unsigned-byte-p-by-syntax-when-const-width
  (implies (and (syntaxp (and (gl-object-case x :g-integer)
                              (gl-object-case n :g-concrete)))
                (integerp x)
                (natp n)
                (b* ((x-endp (check-int-endp x (syntax-bind xsyn (g-concrete x))))
                     ((when x-endp) (not (intcar x))))
                  (check-unsigned-byte-p (1- n) (intcdr x))))
           (equal (check-unsigned-byte-p n x) t))
  :hints(("Goal" :in-theory (e/d (check-unsigned-byte-p
                                  bitops::unsigned-byte-p**
                                  int-endp)
                                 (unsigned-byte-p)))))

(disable-definition acl2::loghead$inline)

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

(disable-definition logext)

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

(disable-definition acl2::logtail$inline)

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

(def-gl-rewrite logbitp-const-index
  (implies (syntaxp (integerp n))
           (equal (logbitp n x)
                  (intcar (logtail n x))))
  :hints(("Goal" :in-theory (enable intcons intcar intcdr int-endp))))


(define int-revapp ((nbits natp)
                    (x integerp)
                    (acc integerp))
  :returns (res integerp)
  (if (zp nbits)
      (lifix acc)
    (int-revapp (1- nbits)
                (intcdr x)
                (intcons (intcar x) acc)))
  ///
  (local (defun-sk int-revapp-normalize-cond (nbits x)
           (forall acc
                   (implies (syntaxp (not (equal acc ''0)))
                            (equal (int-revapp nbits x acc)
                                   (logapp nbits (int-revapp nbits x 0) acc))))
           :rewrite :direct))

  (local (in-theory (disable int-revapp-normalize-cond)))

  (local (defthm int-revapp-normalize-lemma
           (int-revapp-normalize-cond nbits x)
           :hints(("Goal" :induct (int-revapp nbits x acc))
                  (and stable-under-simplificationp
                       `(:expand (,(car (last clause))
                                  (:free (acc) (int-revapp nbits x acc))
                                  (:free (x y) (logapp 1 x y)))
                         :in-theory (enable bitops::logapp-right-assoc))))))

  (defthm int-revapp-normalize
    (implies (syntaxp (not (equal acc ''0)))
             (equal (int-revapp nbits x acc)
                    (logapp nbits (int-revapp nbits x 0) acc)))
    :hints(("Goal" :in-theory (enable bitops::logapp**))))

  (local (defthm logcar-of-int-revapp
           (equal (logcar (int-revapp n x y))
                  (if (zp n)
                      (logcar y)
                    (bool->bit (logbitp (1- n) x))))
           :hints(("Goal" :in-theory (enable bitops::logbitp**)))))

  (local (defthm logcdr-of-int-revapp
           (equal (logcdr (int-revapp n x y))
                  (if (zp n)
                      (logcdr y)
                    (int-revapp (1- n) x y)))
           :hints(("Goal" :in-theory (disable int-revapp-normalize
                                              int-revapp-normalize-cond-necc)))))

  (local (defun int-revapp-of-int-revapp-ind (n x y)
           (if (zp n)
               (list x y)
             (int-revapp-of-int-revapp-ind
              (1- n) x
              (logcons (bool->bit (logbitp (1- n) x)) y)))))
           

  (local (defthm logapp-logcons
           (implies (and (posp n)
                         (equal q (bool->bit (logbitp (+ -1 n) x))))
                    (equal (logapp (+ -1 n) x (logcons q y))
                           (logapp n x y)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (defthm int-revapp-of-int-revapp
    (equal (int-revapp n (int-revapp n x z) y)
           (logapp n x y))
    :hints(("Goal" :in-theory (e/d* (bitops::unsigned-byte-p**
                                     bitops::ihsext-inductions)
                                    (unsigned-byte-p
                                     bitops::logapp**
                                     int-revapp-normalize int-revapp-normalize-cond-necc))
            :induct (int-revapp-of-int-revapp-ind n x y )
            :expand ((:free (x) (int-revapp n x y)))))))


(define logtail-helper ((shift-rev integerp)
                         (shift-width natp)
                         (x integerp))
  :verify-guards nil
  (logtail (int-revapp shift-width shift-rev 0) x)
  ///

  (local (defthm natp-of-int-revapp
           (implies (natp acc)
                    (natp (int-revapp nbits x acc)))
           :hints(("Goal" :in-theory (enable int-revapp)))
           :rule-classes :type-prescription))

  (local (defthm loghead-of-int-revapp
           (equal (loghead width (int-revapp width x acc))
                  (int-revapp width x 0))
           :hints(("Goal" :in-theory (enable int-revapp bitops::loghead**)))))

  (def-gl-rewrite logtail-helper-impl
    (implies (and (syntaxp (and (gl-object-case shift-rev '(:g-integer :g-concrete))
                                (natp shift-width)))
                  (natp shift-width)
                  (integerp shift-rev))
             (equal (logtail-helper shift-rev shift-width x)
                    (b*  (((when (or (check-int-endp x (syntax-bind xsyn (g-concrete x)))
                                     (eql 0 shift-width)))
                           (int x)))
                      (if (intcar shift-rev)
                          (logtail-helper (intcdr shift-rev) (1- shift-width)
                                           (logtail (ash 1 (1- shift-width)) x))
                        (logtail-helper (intcdr shift-rev) (1- shift-width) x)))))
    :hints(("Goal" :in-theory (enable bitops::logtail**
                                      int-endp)
  
            :expand ((int-revapp shift-width shift-rev 0)
                     (int-revapp 0 shift-rev 0)
                     (logtail (logcar shift-rev) x)
                     (:free (b) (logcons b (loghead (+ -1 shift-width) (logcdr shift))))))
           (and stable-under-simplificationp
                '(:in-theory (enable logapp
                                     bitops::expt-2-is-ash)))))

  (def-gl-rewrite logtail-to-logtail-helper
    (implies (syntaxp (not (gl-object-case n :g-concrete)))
             (equal (logtail n x)
                    (b* ((x (int x))
                         (n (nfix (int n)))
                         ((when (syntax-bind n-concrete (gl-object-case n :g-concrete)))
                          (logtail n x))
                         (n-width (syntax-bind n-width (gl-object-case n
                                                         :g-integer (max 0 (1- (len n.bits)))
                                                         :otherwise nil)))
                         ((unless (and n-width
                                       (check-unsigned-byte-p n-width n)))
                          (abort-rewrite (logtail n x)))
                         (n-rev (int-revapp n-width n 0)))
                      (logtail-helper n-rev n-width x))))
    :hints(("Goal" :in-theory (enable check-unsigned-byte-p))))

  (disable-definition logtail-helper))



(define gobj-both-endp-and-same ((x gl-object-p) (y gl-object-p))
  (b* (((mv xok xfix) (gobj-syntactic-integer-fix x))
       ((unless xok) nil)
       (xbits (gobj-syntactic-integer->bits xfix))
       ((unless (atom (cdr xbits))) nil)
       ((mv yok yfix) (gobj-syntactic-integer-fix y))
       ((unless yok) nil)
       (ybits (gobj-syntactic-integer->bits yfix)))
    (and (atom (cdr ybits))
         (equal (car xbits) (car ybits))))
  ///
  ;; (local (include-book "primitive-lemmas"))
  ;; (defthm both-0-or-neg1-when-gobj-both-endp-and-same
  ;;   (implies (gobj-both-endp-and-same x y)
  ;;            (or (and (equal (ifix (fgl-object-eval x env)) -1)
  ;;                     (equal (ifix (fgl-object-eval y env)) -1))
  ;;                (and (equal (ifix (fgl-object-eval x env)) 0)
  ;;                     (equal (ifix (fgl-object-eval y env)) 0))))
  ;;   :hints (("goal" :use ((:instance fgl-object-eval-of-gobj-syntactic-integer-fix)
  ;;                         (:instance fgl-object-eval-of-gobj-syntactic-integer-fix (x y)))
  ;;            :in-theory (e/d (bools->int gobj-bfr-list-eval)
  ;;                            (fgl-object-eval-of-gobj-syntactic-integer-fix)))))
  )

(define logapp-helper ((shift-rev integerp)
                        (shift-width natp)
                        (x integerp)
                        (y integerp))
  :verify-guards nil
  (logapp (int-revapp shift-width shift-rev 0) x y)
  ///

  (local (defthm natp-of-int-revapp
           (implies (natp acc)
                    (natp (int-revapp nbits x acc)))
           :hints(("Goal" :in-theory (enable int-revapp)))
           :rule-classes :type-prescription))

  (local (defthm loghead-of-int-revapp
           (equal (loghead width (int-revapp width x acc))
                  (int-revapp width x 0))
           :hints(("Goal" :in-theory (enable int-revapp bitops::loghead**)))))

  (local (defthm logapp-of-logtail
           (equal (logapp n x (logapp m (logtail n x) y))
                  (logapp (+ (nfix n) (nfix m)) x y))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (def-gl-rewrite logapp-helper-impl
    (implies (and (syntaxp (and (gl-object-case shift-rev '(:g-integer :g-concrete))
                                (natp shift-width)))
                  (natp shift-width)
                  (integerp shift-rev))
             (equal (logapp-helper shift-rev shift-width x y)
                    (b*  (((when (eql 0 shift-width))
                           (int y))
                          ((when (and (syntax-bind x-y-equal-endp
                                                   (b* (((mv xok xfix) (gobj-syntactic-integer-fix x))
                                                        ((unless xok) nil)
                                                        (xbits (gobj-syntactic-integer->bits xfix))
                                                        ((unless (atom (cdr xbits))) nil)
                                                        ((mv yok yfix) (gobj-syntactic-integer-fix y))
                                                        ((unless yok) nil)
                                                        (ybits (gobj-syntactic-integer->bits yfix)))
                                                     (and (atom (cdr ybits))
                                                          (equal (car xbits) (car ybits))))
                                                   ;; (gobj-both-endp-and-same x y)
                                                   )
                                      (int-endp x) (equal (int x) (int y))))
                           (int x))
                          )
                      (if (intcar shift-rev)
                          (b* ((width (ash 1 (1- shift-width))))
                            (logapp width x
                                    (logapp-helper (intcdr shift-rev) (1- shift-width)
                                                    (logtail (ash 1 (1- shift-width)) x)
                                                    y)))
                        (logapp-helper (intcdr shift-rev) (1- shift-width) x y)))))
    :hints(("Goal" :in-theory (enable bitops::logapp**
                                      int-endp)
            
            :expand ((int-revapp shift-width shift-rev 0)
                     (int-revapp 0 shift-rev 0)
                     (logapp (logcar shift-rev) x y)
                     (:free (b) (logcons b (loghead (+ -1 shift-width) (logcdr shift))))))
           (and stable-under-simplificationp
                '(:in-theory (enable bitops::expt-2-is-ash)
                  :expand ((:with logapp (logapp (+ -1 shift-width)
                                                 (int-revapp (+ -1 shift-width)
                                                             (logcdr shift-rev)
                                                             0)
                                                 1)))))))

  (def-gl-rewrite logapp-to-logapp-helper
    (implies (syntaxp (not (gl-object-case n :g-concrete)))
             (equal (logapp n x y)
                    (b* ((x (int x))
                         (y (int y))
                         (n (nfix (int n)))
                         ((when (syntax-bind n-concrete (gl-object-case n :g-concrete)))
                          (logapp n x y))
                         (n-width (syntax-bind n-width (gl-object-case n
                                                         :g-integer (max 0 (1- (len n.bits)))
                                                         :otherwise nil)))
                         ((unless (and n-width
                                       (check-unsigned-byte-p n-width n)))
                          (abort-rewrite (logapp n x y)))
                         (n-rev (int-revapp n-width n 0)))
                      (logapp-helper n-rev n-width x y))))
    :hints(("Goal" :in-theory (enable check-unsigned-byte-p))))

  (disable-definition logapp-helper)

  (def-gl-rewrite loghead-to-logapp
    (implies (syntaxp (not (gl-object-case n :g-concrete)))
             (equal (loghead n x)
                    (logapp n x 0))))
  )

                         
(def-gl-rewrite logmask-to-logapp
  (equal (bitops::logmask n)
         (logapp n -1 0))
  :hints(("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                  bitops::ihsext-recursive-redefs)
                                 (bitops::logmask)))))






(define logbitp-helper ((digit-rev integerp)
                         (digit-width natp)
                         (x integerp))
  :verify-guards nil
  (logbitp (int-revapp digit-width digit-rev 0) x)
  ///
  (local (defthm commutativity-2-of-*
           (equal (* y x z)
                  (* x y z))
           :hints (("goal" :use ((:instance associativity-of-*)
                                 (:instance commutativity-of-*)
                                 (:instance associativity-of-*
                                  (x y) (y x)))
                    :in-theory (disable associativity-of-* commutativity-of-*)))))

  (local (defthm natp-of-int-revapp
           (implies (natp acc)
                    (natp (int-revapp nbits x acc)))
           :hints(("Goal" :in-theory (enable int-revapp)))
           :rule-classes :type-prescription))

  (local (defthm loghead-of-int-revapp
           (equal (loghead width (int-revapp width x acc))
                  (int-revapp width x 0))
           :hints(("Goal" :in-theory (enable int-revapp bitops::loghead**)))))

  (def-gl-rewrite logbitp-helper-impl
    (implies (and (syntaxp (and (gl-object-case digit-rev '(:g-integer :g-concrete))
                                (natp digit-width)))
                  (natp digit-width)
                  (integerp digit-rev))
             (equal (logbitp-helper digit-rev digit-width x)
                    (b* (((when (or (check-int-endp x (syntax-bind xsyn (g-concrete x)))
                                    (eql 0 digit-width)))
                          (intcar x)))
                      (if (intcar digit-rev)
                          (logbitp-helper (intcdr digit-rev) (1- digit-width) (logtail (ash 1 (1- digit-width)) x))
                        (logbitp-helper (intcdr digit-rev) (1- digit-width) x)))))
    :hints(("Goal" :in-theory (enable bitops::logbitp**
                                      int-endp)
            :expand ((int-revapp digit-width digit-rev 0)
                     (int-revapp 0 digit-rev 0)
                     (logbitp (logcar digit-rev) x)
                     (:free (b) (logcons b (loghead (+ -1 digit-width) (logcdr digit))))))
           (and stable-under-simplificationp
                '(:in-theory (enable logapp
                                     bitops::expt-2-is-ash)))))

  (def-gl-rewrite logbitp-to-logbitp-helper
    (implies (syntaxp (not (gl-object-case n :g-concrete)))
             (equal (logbitp n x)
                    (b* ((x (int x))
                         (n (nfix (int n)))
                         ((when (syntax-bind n-concrete (gl-object-case n :g-concrete)))
                          (logbitp n x))
                         (n-width (syntax-bind n-width (gl-object-case n
                                                         :g-integer (max 0 (1- (len n.bits)))
                                                         :otherwise nil)))
                         ((unless (and n-width
                                       (check-unsigned-byte-p n-width n)))
                          (abort-rewrite (logbitp n x)))
                         (n-rev (int-revapp n-width n 0)))
                      (logbitp-helper n-rev n-width x))))
    :hints(("Goal" :in-theory (enable check-unsigned-byte-p))))

  (disable-definition logbitp-helper)

  (disable-definition logbitp))


(disable-definition acl2::logmask$inline)




(def-gl-rewrite logapp-const-width
  (implies (syntaxp (integerp n))
           (equal (logapp n x y)
                  (cond ((zp n) (int y))
                        (t (intcons (and (intcar x) t)
                                    (logapp (1- n) (intcdr x) y))))))
  :hints(("Goal" :in-theory (enable intcons intcar intcdr int-endp
                                    bitops::logapp**))))
                         


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
               (logapp (nfix sh) 0 x)))
           (logtail (nfix (- sh)) x))))

(disable-definition ash)



(define +carry ((c booleanp)
                (x integerp)
                (y integerp))
  (+ (bool->bit c)
     (lifix x)
     (lifix y))
  ///
  (disable-definition +carry)

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
  (disable-definition </=)

  (local (defthm logcar-when-zip
           (implies (zip x) (equal (logcar x) 0))
           :hints(("Goal" :in-theory (enable logcar)))))

  (def-gl-rewrite </=-impl2
    (equal (</= x y)
           (b* ((x (int x))
                (y (int y))
                ((when (and (check-int-endp x (syntax-bind xsyn (g-concrete x)))
                            (check-int-endp y (syntax-bind ysyn (g-concrete y)))))
                 (b* ((less (and (intcar x) (not (intcar y)))))
                   (mv less
                       (and (not less) (or (intcar x) (not (intcar y)))))))
                ((mv rest< rest=) (</= (intcdr x) (intcdr y)))
                ;; ((when (and (syntax-bind rest<-true (eq rest< t))
                ;;             rest<))
                ;;  (mv t nil))
                ;; ((when (and (syntax-bind rest=-false (eq rest= nil))
                ;;             (not rest=)))
                ;;  (mv rest< nil))
                ;; (head< (and (not (intcar x)) (intcar y)))
                )
             (mv (or rest<
                     (and rest= (not (intcar x)) (intcar y)))
                 (and rest= (iff (intcar x) (intcar y))
                      ;; (not (and (not (intcar x)) (intcar y)))
                      ;; (or (not (intcar x)) (intcar y))
                      ))))
    :hints(("Goal" :in-theory (e/d (int-endp or* and*
                                    bitops::logcons-<-n-strong
                                    bitops::logcons->-n-strong)
                                   (not))
            :cases ((integerp x)))
           '(:cases ((integerp y)))
           ;; (and stable-under-simplificationp
           ;;      '(:in-theory (enable cons-equal)))
           ))

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
  (disable-definition +carry-ext)

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

  )

(define +carry-trunc ((width natp)
                      (c booleanp)
                      (x integerp)
                      (y integerp))
  (loghead width (+ (bool->bit c)
                    (lifix x)
                    (lifix y)))
  ///
  (disable-definition +carry-trunc)

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
  (disable-definition logcount-helper)

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



(def-gl-rewrite expt-2-of-integer
  (implies (natp x)
           (equal (expt 2 x) (ash 1 x)))
  :hints(("Goal" :in-theory (enable bitops::ash-is-expt-*-x))))

(def-gl-rewrite unsigned-byte-p-const-width
  (implies (syntaxp (integerp n))
           (equal (unsigned-byte-p n x)
                  (and (natp n)
                       (equal x (loghead n x))
                       t)))
  :hints(("Goal" :in-theory (e/d (bitops::unsigned-byte-p**)
                                 (unsigned-byte-p)))))

(def-gl-rewrite signed-byte-p-const-width
  (implies (syntaxp (integerp n))
           (equal (signed-byte-p n x)
                  (and (posp n)
                       (equal x (logext n x))
                       t)))
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
  (disable-definition integer-length-helper)

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

  (disable-definition integer-length)

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


(def-gl-rewrite logext-to-logapp
  (implies (syntaxp (not (integerp n)))
           (equal (logext n x)
                  (logapp n x (endint (logbitp (+ -1 (pos-fix n)) x)))))
  :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                     bitops::ihsext-recursive-redefs
                                     pos-fix))))

(def-gl-rewrite booleanp-fgl
  (equal (booleanp x)
         (and (equal x (if x t nil)) t)))


