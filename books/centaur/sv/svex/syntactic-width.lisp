; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2022 Intel Corporation
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "SV")

(include-book "width")
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable signed-byte-p)))
(local (std::add-default-post-define-hook :fix))

(local (defthm maybe-posp-fix-when-nonnil
         (implies x
                  (equal (acl2::maybe-posp-fix x) (pos-fix x)))
         :hints(("Goal" :in-theory (enable acl2::maybe-posp-fix
                                           pos-fix)))))





(define svex-width-max ((x maybe-posp)
                        (y maybe-posp))
  :Returns (max maybe-posp :rule-classes :type-prescription)
  (and x y (max (lposfix x) (lposfix y)))
  ///
  (defthm svex-width-max-of-nil
    (and (equal (svex-width-max nil y) nil)
         (equal (svex-width-max x nil) nil)))

  (defret svex-width-max-bounds
    (implies (and x y)
             (and (<= (nfix x) max)
                  (<= (nfix y) max)))
    :rule-classes :linear)

  (defret svex-width-max-bounds-2
    (implies max
             (and (<= (nfix x) max)
                  (<= (nfix y) max)))
    :rule-classes :linear)
  
  (defret svex-width-max-when-y
    (implies (and x y)
             (and (implies (<= (pos-fix x) (pos-fix y))
                           (equal max (pos-fix y)))
                  (implies (<= (pos-fix y) (pos-fix x))
                           (equal max (pos-fix x)))))))

(define svex-width-inc ((n natp)
                        (x maybe-posp))
  :Returns (inc maybe-posp :rule-classes :type-prescription)
  (and x (+ (lnfix n) (lposfix x))))

(define svex-width-add ((n integerp)
                        (x maybe-posp))
  :Returns (inc maybe-posp :rule-classes :type-prescription)
  (and x (max 1 (+ (lifix n) (lposfix x))))
  ///
  (defthm svex-width-add-nil
    (equal (svex-width-add n nil) nil)))

(define svex-width-dec ((n natp)
                        (x maybe-posp))
  :Returns (inc maybe-posp :rule-classes :type-prescription)
  (and x (max 1 (- (lposfix x) (lnfix n)))))



(define svex-syntactic-width ((x svex-p))
  :returns (width maybe-posp :rule-classes :type-prescription)
  :measure (svex-count x)
  (svex-case x
    :var nil
    :quote (b* (((4vec x.val)))
             (+ 1 (max (integer-length x.val.upper)
                       (integer-length x.val.lower))))
    :call
    (case x.fn
      (bitsel 2) ;; returns a single bit
      ((uand
        uor
        uxor
        <
        ==
        ===
        ===*
        ==?
        safer-==?
        ==??)
       ;; returns -1 or 0
       1)
      ((id
        unfloat
        bitnot
        onp
        offp
        xdet)
       (and (eql (len x.args) 1)
            (svex-syntactic-width (first x.args))))
      ((bitand
        bitor
        bitxor
        res
        resand
        resor
        override)
       (and (eql (len x.args) 2)
            (svex-width-max
             (svex-syntactic-width (first x.args))
             (svex-syntactic-width (second x.args)))))
      (zerox
       (and (eql (len x.args) 2)
            (b* ((arg1 (first x.args)))
              (svex-case arg1
                :quote (if (and (2vec-p arg1.val)
                                (<= 0 (2vec->val arg1.val)))
                           (+ 1 (2vec->val arg1.val))
                         1) ;; x case
                :otherwise nil))))
      (signx
       (and (eql (len x.args) 2)
            (b* ((arg1 (first x.args)))
              (svex-case arg1
                :quote (if (and (2vec-p arg1.val)
                                (< 0 (2vec->val arg1.val)))
                           (2vec->val arg1.val)
                         1) ;; x case
                :otherwise nil))))
      (concat
       (and (eql (len x.args) 3)
            (b* ((arg1 (first x.args)))
              (svex-case arg1
                :quote (if (and (2vec-p arg1.val)
                                (<= 0 (2vec->val arg1.val)))
                           (svex-width-inc (2vec->val arg1.val)
                                           (svex-syntactic-width (third x.args)))
                         1)
                :otherwise nil))))
      (rsh
       (and (eql (len x.args) 2)
            (b* ((arg1 (first x.args)))
              (svex-case arg1
                :quote (if (2vec-p arg1.val)
                           (svex-width-add (- (2vec->val arg1.val))
                                           (svex-syntactic-width (second x.args)))
                         1)
                :otherwise nil))))
      (lsh
       (and (eql (len x.args) 2)
            (b* ((arg1 (first x.args)))
              (svex-case arg1
                :quote (if (2vec-p arg1.val)
                           (svex-width-add (2vec->val arg1.val)
                                           (svex-syntactic-width (second x.args)))
                         1)
                :otherwise nil))))
      ((? ?* ?!)
       (and (eql (len x.args) 3)
            (svex-width-max
             (svex-syntactic-width (second x.args))
             (svex-syntactic-width (third x.args)))))
      ((bit? bit?!)
       (and (eql (len x.args) 3)
            (svex-width-max
             (svex-syntactic-width (first x.args))
             (svex-width-max (svex-syntactic-width (second x.args))
                             (svex-syntactic-width (third x.args))))))
      (partsel
       (and (eql (len x.args) 3)
            (b* ((arg2 (second x.args)))
              (svex-case arg2
                :quote (if (and (2vec-p arg2.val)
                                (<= 0 (2vec->val arg2.val)))
                           (+ 1 (2vec->val arg2.val))
                         1) ;; x case
                :otherwise nil))))
      (partinst
       (and (eql (len x.args) 4)
            (b* ((lsb (first x.args))
                 (width (second x.args))
                 (in (third x.args)))
              (svex-case lsb
                :quote
                (svex-case width
                  :quote
                  (if (and (2vec-p lsb.val)
                           (2vec-p width.val)
                           (<= 0 (2vec->val width.val)))
                      (b* ((lsbval (2vec->val lsb.val))
                           (widthval (2vec->val width.val)))
                        (if (<= widthval (- lsbval))
                            (svex-syntactic-width in)
                          (svex-width-max
                           (svex-syntactic-width in)
                           (+ 1 lsbval widthval))))
                    1) ;; x
                  :otherwise nil)
                :otherwise nil))))
      (& nil)))

  ///
  (local (in-theory (disable (:d svex-syntactic-width))))
  
  (local (defthm open-svex-apply
           (implies (syntaxp (quotep fn))
                    (equal (svex-apply fn args)
                           (b* ((fn (fnsym-fix fn))
                                (args (4veclist-fix args)))
                             (svex-apply-cases fn args))))
           :hints(("Goal" :in-theory (enable svex-apply)))))
  
  (local (defthm nth-of-svexlist-eval
           (4vec-equiv (nth n (svexlist-eval x env))
                       (svex-eval (nth n x) env))
           :hints(("Goal" :in-theory (enable nth svexlist-eval)))))


  (local (defthm 4veclist-nth-safe-of-svex-eval
           (equal (4veclist-nth-safe n (svexlist-eval x env))
                  (svex-eval (nth n x) env))
           :hints(("Goal" :in-theory (enable 4veclist-nth-safe nth)))))

  (local (defthm nth-open
           (implies (syntaxp (quotep n))
                    (equal (nth n x)
                           (if (zp n)
                               (car x)
                             (nth (1- n) (cdr x)))))))

  (local (in-theory (disable len)))

  
  (local (defthm 4vec-width-p-of-4vec-concat-proper
           (implies (and (2vec-p w)
                         (<= 0 (2vec->val w))
                         (< (2vec->val w) (pos-fix n))
                         (4vec-width-p (- (nfix n) (2vec->val w)) y))
                    (4vec-width-p n (4vec-concat w x y)))
           :hints(("Goal" :in-theory (enable 4vec-width-p 4vec-concat pos-fix)))))

  (local (defthm 4vec-width-p-of-4vec-concat-improper
           (implies (not (and (2vec-p w)
                              (<= 0 (2vec->val w))))
                    (4vec-width-p 1 (4vec-concat w x y)))
           :hints(("Goal" :in-theory (enable 4vec-width-p 4vec-concat pos-fix)))))

  (local (defthm 4vec-width-p-of-4vec-rsh-proper
           (implies (and (2vec-p sh)
                         (<= 1 (+ (pos-fix n) (2vec->val sh)))
                         (4vec-width-p (+ (pos-fix n) (2vec->val sh)) x))
                    (4vec-width-p n (4vec-rsh sh x)))
           :hints(("Goal" :in-theory (enable 4vec-width-p 4vec-rsh 4vec-shift-core)))))

  (local (defthm 4vec-width-p-of-4vec-lsh-proper
           (implies (and (2vec-p sh)
                         (<= 1 (+ (pos-fix n) (- (2vec->val sh))))
                         (4vec-width-p (+ (pos-fix n) (- (2vec->val sh))) x))
                    (4vec-width-p n (4vec-lsh sh x)))
           :hints(("Goal" :in-theory (enable 4vec-width-p 4vec-lsh 4vec-shift-core)))))

  (local (defthm 4vec-width-p-of-4vec-lsh-improper
           (implies (not (2vec-p sh))
                    (4vec-width-p n (4vec-lsh sh x)))
           :hints(("Goal" :in-theory (enable 4vec-width-p 4vec-lsh 4vec-shift-core)))))

  (local (defthm 4vec-width-p-of-4vec-rsh-improper
           (implies (not (2vec-p sh))
                    (4vec-width-p n (4vec-rsh sh x)))
           :hints(("Goal" :in-theory (enable 4vec-width-p 4vec-rsh 4vec-shift-core)))))

  (local (defthm 4vec-width-p-when-lesser
           (implies (and (4vec-width-p n x)
                         (<= (pos-fix n) (pos-fix m)))
                    (4vec-width-p m x))
           :hints(("Goal" :in-theory (enable 4vec-width-p)))))

  (local (defthm 4vec-width-p-of-4vec-x
           (4vec-width-p n (4vec-x))
           :hints(("Goal" :in-theory (enable 4vec-width-p)))))

  (local (defthm 4vec-zero-ext-to-concat
           (equal (4vec-zero-ext n x)
                  (4vec-concat n x 0))
           :hints(("Goal" :in-theory (enable 4vec-zero-ext
                                             4vec-concat)))))

  (local (defthm 4vec-width-p-of-3vec-fix
           (implies (4vec-width-p n x)
                    (4vec-width-p n (3vec-fix x)))
           :hints(("Goal" :in-theory (enable 3vec-fix 4vec-width-p)))))
  
  ;; (local (defthm 4vec-width-p-of-3vec-bit?
  ;;          (implies (and (4vec-width-p n1 x1)
  ;;                        (4vec-width-p n2 x2)
  ;;                        (4vec-width-p n3 x3)
  ;;                        (<= (pos-fix n1) (pos-fix w))
  ;;                        (<= (pos-fix n2) (pos-fix w))
  ;;                        (<= (pos-fix n2) (pos-fix w)))
  ;;                   (4vec-width-p (pos-fix w) (3vec-bit? x1 x2 x3)))
  ;;          :hints(("Goal" :in-theory (enable 3vec-bit? 4vec-width-p)))))
  
  (local (defthm 4vec-width-p-of-4vec-bit?
           (implies (and (4vec-width-p n1 x1)
                         (4vec-width-p n2 x2)
                         (4vec-width-p n3 x3)
                         (<= (pos-fix n1) (pos-fix w))
                         (<= (pos-fix n2) (pos-fix w))
                         (<= (pos-fix n3) (pos-fix w)))
                    (4vec-width-p w (4vec-bit? x1 x2 x3)))
           :hints(("Goal" :in-theory (e/d (4vec-bit? 3vec-bit? 4vec-width-p)
                                          (4vec-width-p-of-3vec-fix))
                   :use ((:instance 4vec-width-p-of-3vec-fix
                          (n n1) (x x1)))))))


  (local (defthm 4vec-width-p-of-4vec-bit?!
           (implies (and (4vec-width-p n1 x1)
                         (4vec-width-p n2 x2)
                         (4vec-width-p n3 x3)
                         (<= (pos-fix n1) (pos-fix w))
                         (<= (pos-fix n2) (pos-fix w))
                         (<= (pos-fix n3) (pos-fix w)))
                    (4vec-width-p w (4vec-bit?! x1 x2 x3)))
           :hints(("Goal" :in-theory (e/d (4vec-bit?! 4vec-width-p))))))


  (local (defthm 4vec-width-p-of-4vec-?
           (implies (and (4vec-width-p n2 x2)
                         (4vec-width-p n3 x3)
                         (<= (pos-fix n2) (pos-fix w))
                         (<= (pos-fix n3) (pos-fix w)))
                    (4vec-width-p w (4vec-? x1 x2 x3)))
           :hints(("Goal" :in-theory (e/d (4vec-? 3vec-? 4vec-width-p)
                                          (4vec-width-p-of-3vec-fix))
                   :use ((:instance 4vec-width-p-of-3vec-fix
                          (n n1) (x x1)))))))

  (local (defthm 4vec-width-p-of-4vec-?*
           (implies (and (4vec-width-p n2 x2)
                         (4vec-width-p n3 x3)
                         (<= (pos-fix n2) (pos-fix w))
                         (<= (pos-fix n3) (pos-fix w)))
                    (4vec-width-p w (4vec-?* x1 x2 x3)))
           :hints(("Goal" :in-theory (e/d (4vec-?* 3vec-?* 4vec-width-p)
                                          (4vec-width-p-of-3vec-fix))
                   :use ((:instance 4vec-width-p-of-3vec-fix
                          (n n1) (x x1)))))))

  (local (defthm 4vec-width-p-of-4vec-?!
           (implies (and (4vec-width-p n2 x2)
                         (4vec-width-p n3 x3)
                         (<= (pos-fix n2) (pos-fix w))
                         (<= (pos-fix n3) (pos-fix w)))
                    (4vec-width-p w (4vec-?! x1 x2 x3)))
           :hints(("Goal" :in-theory (e/d (4vec-?! 4vec-width-p))))))

  (local (defthm 4vec-width-p-of-4vec-sign-ext-proper
           (implies (and (2vec-p n)
                         (< 0 (2vec->val n))
                         (<= (2vec->val n) (pos-fix m)))
                    (4vec-width-p m (4vec-sign-ext n x)))
           :hints(("Goal" :in-theory (enable 4vec-width-p 4vec-sign-ext)))))

  (local (defthm 4vec-width-p-of-4vec-sign-ext-improper
           (implies (not (and (2vec-p n)
                              (< 0 (2vec->val n))))
                    (4vec-width-p m (4vec-sign-ext n x)))
           :hints(("Goal" :in-theory (enable 4vec-width-p 4vec-sign-ext)))))

  (local (defthm 4vec-width-p-of-4vec-bitand
           (implies (and (4vec-width-p n1 x1)
                         (4vec-width-p n2 x2)
                         (<= (pos-fix n1) (pos-fix w))
                         (<= (pos-fix n2) (pos-fix w)))
                    (4vec-width-p w (4vec-bitand x1 x2)))
           :hints(("Goal" :in-theory (e/d (4vec-bitand 3vec-bitand 4vec-width-p)
                                          (4vec-width-p-of-3vec-fix))
                   :use ((:instance 4vec-width-p-of-3vec-fix
                          (n n1) (x x1))
                         (:instance 4vec-width-p-of-3vec-fix
                          (n n2) (x x2)))))))

  (local (defthm 4vec-width-p-of-4vec-bitor
           (implies (and (4vec-width-p n1 x1)
                         (4vec-width-p n2 x2)
                         (<= (pos-fix n1) (pos-fix w))
                         (<= (pos-fix n2) (pos-fix w)))
                    (4vec-width-p w (4vec-bitor x1 x2)))
           :hints(("Goal" :in-theory (e/d (4vec-bitor 3vec-bitor 4vec-width-p)
                                          (4vec-width-p-of-3vec-fix))
                   :use ((:instance 4vec-width-p-of-3vec-fix
                          (n n1) (x x1))
                         (:instance 4vec-width-p-of-3vec-fix
                          (n n2) (x x2)))))))

  (local (defthm 4vec-width-p-of-4vec-bitxor
           (implies (and (4vec-width-p n1 x1)
                         (4vec-width-p n2 x2)
                         (<= (pos-fix n1) (pos-fix w))
                         (<= (pos-fix n2) (pos-fix w)))
                    (4vec-width-p w (4vec-bitxor x1 x2)))
           :hints(("Goal" :in-theory (e/d (4vec-bitxor 3vec-bitxor 4vec-width-p)
                                          (4vec-width-p-of-3vec-fix))
                   :use ((:instance 4vec-width-p-of-3vec-fix
                          (n n1) (x x1))
                         (:instance 4vec-width-p-of-3vec-fix
                          (n n2) (x x2)))))))

  (local (defthm 4vec-width-p-of-4vec-resor
           (implies (and (4vec-width-p n1 x1)
                         (4vec-width-p n2 x2)
                         (<= (pos-fix n1) (pos-fix w))
                         (<= (pos-fix n2) (pos-fix w)))
                    (4vec-width-p w (4vec-resor x1 x2)))
           :hints(("Goal" :in-theory (e/d (4vec-resor 4vec-width-p))))))

  (local (defthm 4vec-width-p-of-4vec-resand
           (implies (and (4vec-width-p n1 x1)
                         (4vec-width-p n2 x2)
                         (<= (pos-fix n1) (pos-fix w))
                         (<= (pos-fix n2) (pos-fix w)))
                    (4vec-width-p w (4vec-resand x1 x2)))
           :hints(("Goal" :in-theory (e/d (4vec-resand 4vec-width-p))))))

  (local (defthm 4vec-width-p-of-4vec-res
           (implies (and (4vec-width-p n1 x1)
                         (4vec-width-p n2 x2)
                         (<= (pos-fix n1) (pos-fix w))
                         (<= (pos-fix n2) (pos-fix w)))
                    (4vec-width-p w (4vec-res x1 x2)))
           :hints(("Goal" :in-theory (e/d (4vec-res 4vec-width-p))))))

  

  (local (defthm 4vec-width-p-of-4vec-override
           (implies (and (4vec-width-p n1 x1)
                         (4vec-width-p n2 x2)
                         (<= (pos-fix n1) (pos-fix w))
                         (<= (pos-fix n2) (pos-fix w)))
                    (4vec-width-p w (4vec-override x1 x2)))
           :hints(("Goal" :in-theory (e/d (4vec-override 4vec-width-p))))))

  (local (defthm 4vec-width-p-of-4vec-onset
           (implies (and (4vec-width-p w x1))
                    (4vec-width-p w (4vec-onset x1)))
           :hints(("Goal" :in-theory (e/d (4vec-onset 4vec-width-p))))))

  (local (defthm 4vec-width-p-of-4vec-offset
           (implies (and (4vec-width-p w x1))
                    (4vec-width-p w (4vec-offset x1)))
           :hints(("Goal" :in-theory (e/d (4vec-offset 4vec-width-p))))))

  (local (defthm 4vec-width-p-of-4vec-xdet
           (implies (and (4vec-width-p w x1))
                    (4vec-width-p w (4vec-xdet x1)))
           :hints(("Goal" :in-theory (e/d (4vec-xdet 4vec-width-p))))))

  (local (defthm 4vec-width-p-of-4vec-bitnot
           (implies (and (4vec-width-p w x1))
                    (4vec-width-p w (4vec-bitnot x1)))
           :hints(("Goal" :in-theory (e/d (4vec-bitnot 3vec-bitnot 4vec-width-p)
                                          (4vec-width-p-of-3vec-fix))
                   :use ((:instance 4vec-width-p-of-3vec-fix
                          (n w) (x x1)))))))

  (local (defthm 4vec-width-p-of-4vec-reduction-and
           (4vec-width-p 1 (4vec-reduction-and x))
           :hints(("Goal" :in-theory (enable 4vec-reduction-and 3vec-reduction-and 4vec-width-p bool->vec)))))

  (local (defthm 4vec-width-p-of-4vec-reduction-or
           (4vec-width-p 1 (4vec-reduction-or x))
           :hints(("Goal" :in-theory (enable 4vec-reduction-or 3vec-reduction-or 4vec-width-p bool->vec)))))

  (local (defthm signed-byte-p-of-neg-bit
           (implies (and (bitp x)
                         (posp n))
                    (signed-byte-p n (- x)))
           :hints(("Goal" :in-theory (enable bitp)))))
  
  (local (defthm 4vec-width-p-of-4vec-parity
           (4vec-width-p 1 (4vec-parity x))
           :hints(("Goal" :in-theory (enable 4vec-parity 4vec-width-p)))))

  (local (defthm 4vec-width-p-of-4vec-<
           (4vec-width-p 1 (4vec-< x y))
           :hints(("Goal" :in-theory (enable 4vec-< 4vec-width-p bool->vec)))))

  (local (defthm 4vec-width-p-of-4vec-==
           (4vec-width-p 1 (4vec-== x y))
           :hints(("Goal" :in-theory (enable 4vec-== 3vec-== 3vec-reduction-and 4vec-width-p bool->vec)))))

  (local (defthm 4vec-width-p-of-4vec-===*
           (4vec-width-p 1 (4vec-===* x y))
           :hints(("Goal" :in-theory (enable 4vec-===* 4vec-width-p)))))

  (local (defthm 4vec-width-p-of-4vec-===
           (4vec-width-p 1 (4vec-=== x y))
           :hints(("Goal" :in-theory (enable 4vec-=== 4vec-width-p bool->vec)))))
  
  (local (defthm 4vec-width-p-of-4vec-wildeq
           (4vec-width-p 1 (4vec-wildeq x y))
           :hints(("Goal" :in-theory (enable 4vec-wildeq  3vec-reduction-and 4vec-width-p bool->vec)))))

  
  
  (local (defthm 4vec-width-p-of-4vec-wildeq-safe
           (4vec-width-p 1 (4vec-wildeq-safe x y))
           :hints(("Goal" :in-theory (enable 4vec-wildeq-safe  3vec-reduction-and 4vec-width-p bool->vec)))))

  (local (defthm 4vec-width-p-of-4vec-symwildeq
           (4vec-width-p 1 (4vec-symwildeq x y))
           :hints(("Goal" :in-theory (enable 4vec-symwildeq 3vec-reduction-and 4vec-width-p bool->vec)))))

  (local (defthm 4vec-width-p-of-4vec-bit-extract
           (4vec-width-p 2 (4vec-bit-extract n x))
           :hints(("Goal" :in-theory (enable 4vec-bit-extract 4vec-width-p 4vec-bit-index bool->bit)))))


  (local (defthmd signed-byte-p-integer-length
           (implies (integerp x)
                    (signed-byte-p (+ 1 (integer-length x)) x))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))
  
  (local (defthm 4vec-width-p-by-integer-length
           (and (implies (<= (integer-length (4vec->lower x))
                             (integer-length (4vec->upper x)))
                         (4vec-width-p (+ 1 (integer-length (4vec->upper x))) x))
                (implies (<= (integer-length (4vec->upper x))
                             (integer-length (4vec->lower x)))
                         (4vec-width-p (+ 1 (integer-length (4vec->lower x))) x)))
           :hints(("Goal" :in-theory (enable 4vec-width-p)
                   :use ((:instance signed-byte-p-integer-length
                          (x (4vec->upper x)))
                         (:instance signed-byte-p-integer-length
                          (x (4vec->lower x))))))))
  
  ;;                   (equal (4vec-sign-ext w1 (4vec-concat w2 x y))
  ;;                          (if (and (2vec-p w2)
  ;;                                   (<= 0 (2vec->val w2)))
  ;;                              (if (<= (2vec->val w1) (2vec->val w2))
  ;;                                  (4vec-sign-ext w1 x)
  ;;                                (4vec-concat w2 x (4vec-sign-ext (2vec (- (2vec->val w1) (2vec->val w2))) y)))
  ;;                            (4vec-x))))
  ;;          :hints(("Goal" :in-theory (enable 4vec-sign-ext 4vec-concat)))))


  ;; (local (defthm logext-of-logtail
  ;;          (equal (logext n (logtail m x))
  ;;                 (logtail m (logext (+ (nfix m) (pos-fix n)) x)))
  ;;          :hints((acl2::logbitp-reasoning)
  ;;                 (and stable-under-simplificationp
  ;;                      '(:in-theory (enable pos-fix))))))

  ;; (local (defthm 4vec-sign-ext-of-4vec-rsh
  ;;          (implies (and (2vec-p w)
  ;;                        (< 0 (2vec->val w))
  ;;                        (2vec-p sh)
  ;;                        (<= 0 (2vec->val sh)))
  ;;                   (equal (4vec-sign-ext w (4vec-rsh sh x))
  ;;                          (4vec-rsh sh (4vec-sign-ext (2vec (+ (2vec->val sh) (2vec->val w))) x))))
  ;;          :hints(("Goal" :in-theory (enable 4vec-sign-ext 4vec-rsh 4vec-shift-core)))))

  (local (defthm 2vec-p-of-2vec
           (2vec-p (2vec x))
           :hints(("Goal" :in-theory (enable 2vec-p 2vec)))))
  
  (local (in-theory (disable 2vec-p)))

  

  (defret <fn>-correct
    (implies width
             (4vec-width-p width (svex-eval x env)))
    :hints (("goal" :expand ((svex-eval x env)
                             <call>)
             :in-theory (enable 4vec-part-install
                                4vec-part-select)
             :induct <call>
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable svex-width-max
                                      svex-width-add
                                      svex-width-inc))))))


(local (defthm maybe-natp-fix-when-nonnil
         (implies x
                  (equal (acl2::maybe-natp-fix x) (nfix x)))
         :hints(("Goal" :in-theory (enable acl2::maybe-natp-fix
                                           nfix)))))
                 




(define svexlist-syntactic-width ((x svexlist-p))
  :returns (width maybe-natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (svex-width-sum (svex-syntactic-width (car x))
                    (svexlist-syntactic-width (cdr x)))))


(define svex-alist-syntactic-width ((x svex-alist-p))
  :returns (width maybe-natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (if (mbt (and (consp (car x))
                  (svar-p (caar x))))
        (svex-width-sum (svex-syntactic-width (cdar x))
                        (svex-alist-syntactic-width (cdr x)))
      (svex-alist-syntactic-width (cdr x))))
  ///
  (local (in-theory (enable svex-alist-fix))))

