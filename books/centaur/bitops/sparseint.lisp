; Centaur Bitops Library
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
; Original authors: Sol Swords <sswords@centtech.com>

(in-package "BITOPS")


(include-book "std/basic/arith-equivs" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "std/util/defenum" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "trailing-0-count")
(include-book "fast-logext")
(include-book "fast-part-select")
(local (include-book "ihsext-basics"))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (std::add-default-post-define-hook :fix))
(std::make-returnspec-config :hints-sub-returnnames t)

(defxdoc sparseint-impl
  :parents (sparseint)
  :short "Umbrella topic for functions used in implementation of sparseint operations.")

(local (xdoc::set-default-parents sparseint-impl))

(local (in-theory (disable acl2::logext-identity
                           loghead-identity
                           logtail-identity)))

(local (defthm open-logbitp-const
         (implies (syntaxp (quotep n))
                  (equal (logbitp n x)
                         (if (zp n)
                             (bit->bool (logcar x))
                           (logbitp (1- n) (logcdr x)))))
         :hints(("Goal" :in-theory (enable logbitp**)))))

(local (defthm open-logtail-const
         (implies (syntaxp (quotep n))
                  (equal (logtail n x)
                         (if (zp n)
                             (ifix x)
                           (logtail (1- n) (logcdr x)))))
         :hints(("Goal" :in-theory (enable logtail**)))))

(fty::deftypes sparseint$
  (fty::defflexsum sparseint$
    (:leaf
     :cond (atom x)
     :fields ((val :type integerp :rule-classes :type-prescription
                   :acc-body x))
     :ctor-body val
     :extra-binder-names (color))
    (:concat
     :shape (and (consp (cdr x))
                 (integerp (car x)))
     :fields ((width :type posp :rule-classes :type-prescription
                     :acc-body (logtail 2 (car x)))
              (lsbs-taller :type booleanp :rule-classes :type-prescription
                           :acc-body (logbitp 0 (car x)))
              (msbs-taller :type booleanp :rule-classes :type-prescription
                           :acc-body (logbitp 1 (car x)))
              (lsbs :type sparseint$ :acc-body (cadr x))
              (msbs :type sparseint$ :acc-body (cddr x)))
     :ctor-body (cons (logcons (bool->bit lsbs-taller) (logcons (bool->bit msbs-taller) width))
                      (cons lsbs msbs)))
    :measure (acl2-count x)))

(local (in-theory (disable open-logbitp-const open-logtail-const)))



(define sparseint$-val ((x sparseint$-p))
  :returns (val integerp :rule-classes :type-prescription)
  :measure (sparseint$-count x)
  (sparseint$-case x
    :leaf x.val
    :concat (logapp x.width
                    (sparseint$-val x.lsbs)
                    (sparseint$-val x.msbs)))
  ///
  (defret sparseint$-val-of-leaf
    (implies (sparseint$-case x :leaf)
             (equal (sparseint$-val x)
                    (sparseint$-leaf->val x))))
  (defret sparseint$-val-of-concat
    (implies (sparseint$-case x :concat)
             (equal (sparseint$-val x)
                    (b* (((sparseint$-concat x)))
                      (logapp x.width
                              (sparseint$-val x.lsbs)
                              (sparseint$-val x.msbs)))))))



(define sparseint$-real-height ((x sparseint$-p))
  :returns (height natp :rule-classes :type-prescription)
  :measure (sparseint$-count x)
  (sparseint$-case x
    :leaf 0
    :concat (+ 1
               (max (sparseint$-real-height x.lsbs)
                    (sparseint$-real-height x.msbs)))))


(define sparseint$-height-correct-exec ((x sparseint$-p))
  :returns (height-if-correct acl2::maybe-natp :rule-classes :type-prescription)
  :measure (sparseint$-count x)
  (sparseint$-case x
    :leaf 0
    :concat (b* ((lsb-height (sparseint$-height-correct-exec x.lsbs))
                 ((unless lsb-height) nil)
                 (msb-height (sparseint$-height-correct-exec x.msbs)))
              (and msb-height
                   (cond (x.lsbs-taller (and (not x.msbs-taller)
                                             (eql lsb-height (+ 1 msb-height))
                                             (+ 1 lsb-height)))
                         (x.msbs-taller (and (eql msb-height (+ 1 lsb-height))
                                             (+ 1 msb-height)))
                         (t (and (eql msb-height lsb-height)
                                 (+ 1 lsb-height)))))))
  ///
  (defret height-if-correct-of-sparseint$-height-correct-exec
    (implies height-if-correct
             (equal height-if-correct
                    (sparseint$-real-height x)))
    :hints(("Goal" :in-theory (enable sparseint$-real-height)))))

(define within-1 ((x natp) (y natp))
  (<= (abs (- (lnfix x) (lnfix y))) 1)
  ///
  (defthm within-1-when-equal
    (within-1 x x))

  (defthm within-1-when-y-greater
    (implies (equal (+ 1 (nfix x)) (nfix y))
             (within-1 x y)))

  (defthm within-1-when-x-greater
    (implies (equal (+ 1 (nfix y)) (nfix x))
             (within-1 x y)))

  (defthm within-1-commutative
    (implies (within-1 y x)
             (within-1 x y)))

  (defthmd <-when-within-1
    (implies (and (within-1 x y)
                  (natp x) (natp y))
             (equal (< x y)
                    (equal (+ 1 x) y))))

  (defthmd >-when-within-1
    (implies (and (within-1 x y)
                  (natp x) (natp y))
             (equal (< y x)
                    (equal (+ 1 y) x))))

  (defthm within-1-when-<
    (implies (< (nfix x) (nfix y))
             (equal (within-1 x y)
                    (equal (nfix y) (+ 1 (nfix x))))))

  (defthm within-1-when->
    (implies (> (nfix x) (nfix y))
             (equal (within-1 x y)
                    (equal (nfix x) (+ 1 (nfix y)))))))

;; (local (in-theory (enable <-when-within-1 >-when-within-1)))

(define sparseint$-height-correctp ((x sparseint$-p))
  :returns (correctp)
  :measure (sparseint$-count x)
  :verify-guards nil
  (mbe :logic
       (sparseint$-case x
         :leaf t
         :concat (and (sparseint$-height-correctp x.lsbs)
                      (sparseint$-height-correctp x.msbs)
                      (b* ((lsb-height (sparseint$-real-height x.lsbs))
                           (msb-height (sparseint$-real-height x.msbs)))
                        (cond (x.lsbs-taller (and (not x.msbs-taller)
                                                  (eql lsb-height (+ 1 msb-height))))
                              (x.msbs-taller (eql msb-height (+ 1 lsb-height)))
                              (t (eql msb-height lsb-height))))))
       :exec (and (sparseint$-height-correct-exec x) t))
  ///

  (local (defret sparseint$-height-correct-exec-iff-correctp
           (iff (sparseint$-height-correct-exec x)
                (sparseint$-height-correctp x))
           :hints(("Goal" :in-theory (enable sparseint$-height-correct-exec)))))

  (verify-guards sparseint$-height-correctp))


(define sparseint$-height ((x sparseint$-p))
  :guard (sparseint$-height-correctp x)
  :returns (height natp :rule-classes :type-prescription)
  :measure (sparseint$-count x)
  :verify-guards nil
  (sparseint$-case x
    :leaf 0
    :concat (mbe :logic (+ 1 (max (sparseint$-height x.lsbs)
                                  (sparseint$-height x.msbs)))
                 :exec (cond (x.lsbs-taller
                              (+ 2 (sparseint$-height x.msbs)))
                             (x.msbs-taller
                              (+ 2 (sparseint$-height x.lsbs)))
                             (t (+ 1 (sparseint$-height x.lsbs))))))

  ///
  (defret sparseint$-real-height-equals-sparseint$-height
    (equal (sparseint$-real-height x)
           height)
    :hints(("Goal" :in-theory (enable sparseint$-real-height))))
  
  (verify-guards sparseint$-height
    :hints (("goal" :Expand ((sparseint$-height-correctp x)))))

  (defret sparseint$-height-equal-0
    (equal (equal height 0)
           (sparseint$-case x :leaf)))

  (defthmd sparseint$-height-when-concat
    (implies (sparseint$-case x :concat)
             (equal (sparseint$-height x)
                    (b* (((sparseint$-concat x)))
                      (+ 1 (max (sparseint$-height x.lsbs)
                                (sparseint$-height x.msbs)))))))

  (defthm sparseint$-height-of-concat
    (equal (sparseint$-height (make-sparseint$-concat
                                   :width width
                                   :lsbs lsbs
                                   :msbs msbs
                                   :lsbs-taller lsbs-taller
                                   :msbs-taller msbs-taller))
           (+ 1 (max (sparseint$-height lsbs)
                     (sparseint$-height msbs))))
    :hints(("Goal" :in-theory (enable sparseint$-height-when-concat))))

  (defthm sparseint$-height-when-leaf
    (implies (sparseint$-case x :leaf)
             (equal (sparseint$-height x) 0))
    :rule-classes (:rewrite :forward-chaining))

  (defret sparseint$-height-posp-when-concat
    (iff (posp height)
         (equal (sparseint$-kind x) :concat))
    :rule-classes ((:forward-chaining :trigger-terms ((sparseint$-height x))
                    :corollary (implies (posp height) (equal (sparseint$-kind x) :concat)))
                   (:forward-chaining :trigger-terms ((equal (sparseint$-kind x) :concat))
                    :corollary (implies (equal (sparseint$-kind x) :concat) (posp height)))))

  (defret sparseint$-height-gt-0-implies-concat
    (implies (< 0 height)
             (equal (sparseint$-kind x) :concat))
    :rule-classes ((:forward-chaining :trigger-terms ((sparseint$-height x)))))

  (defthm sparseint$-height-of-lsbs-upper-bound
    (implies (sparseint$-case x :concat)
             (<= (sparseint$-height (sparseint$-concat->lsbs x)) (+ -1 (sparseint$-height x))))
    :rule-classes :linear)

  (defthm sparseint$-height-of-msbs-upper-bound
    (implies (sparseint$-case x :concat)
             (<= (sparseint$-height (sparseint$-concat->msbs x)) (+ -1 (sparseint$-height x))))
    :rule-classes :linear))


(defsection sparseint$-height-correctp-thms
  (local (std::set-define-current-function sparseint$-height-correctp))
  (local (in-theory (enable sparseint$-height-correctp)))


  (defthm sparseint$-height-correctp-implies
    (implies (and (sparseint$-height-correctp x)
                  (sparseint$-case x :concat))
             (b* (((sparseint$-concat x)))
               (and (sparseint$-height-correctp x.lsbs)
                    (sparseint$-height-correctp x.msbs)
                    (implies x.lsbs-taller (not x.msbs-taller))
                    (implies x.msbs-taller (not x.lsbs-taller))
                    (b* ((x-height (sparseint$-height x))
                         (lsb-height (sparseint$-height x.lsbs))
                         (msb-height (sparseint$-height x.msbs)))
                      (and (implies x.lsbs-taller
                                    (equal msb-height (+ -2 x-height)))
                           (implies x.msbs-taller
                                    (equal lsb-height (+ -2 x-height)))
                           (implies (not x.lsbs-taller)
                                    (equal msb-height (+ -1 x-height)))
                           (implies (not x.msbs-taller)
                                    (equal lsb-height (+ -1 x-height)))
                           (within-1 lsb-height msb-height))))))
    :hints (("goal" :expand ((sparseint$-height-correctp x)
                             (sparseint$-height x)))))

  (defthm sparseint$-height-of-lsbs-lower-bound
    (implies (and (sparseint$-case x :concat)
                  (sparseint$-height-correctp x))
             (>= (sparseint$-height (sparseint$-concat->lsbs x)) (+ -2 (sparseint$-height x))))
    :hints (("goal" :expand ((sparseint$-height x))))
    :rule-classes :linear)

  (defthm sparseint$-height-of-msbs-lower-bound
    (implies (and (sparseint$-case x :concat)
                  (sparseint$-height-correctp x))
             (>= (sparseint$-height (sparseint$-concat->msbs x)) (+ -2 (sparseint$-height x))))
    :hints (("goal" :expand ((sparseint$-height x))))
    :rule-classes :linear)

  (defthmd sparseint$-height-correct-same-height-branches-implies
    (implies (and (sparseint$-height-correctp x)
                  (sparseint$-case x :concat)
                  (equal (sparseint$-height (sparseint$-concat->msbs x))
                         (sparseint$-height (sparseint$-concat->lsbs x))))
             (and (equal (sparseint$-height (sparseint$-concat->msbs x))
                         (+ -1 (sparseint$-height x)))
                  (equal (sparseint$-height (sparseint$-concat->lsbs x))
                         (+ -1 (sparseint$-height x))))))

  (defthmd sparseint$-height-correctp-when-leaf
    (implies (sparseint$-case x :leaf)
             (sparseint$-height-correctp x)))

  (defthm sparseint$-height-correctp-of-leaf
    (sparseint$-height-correctp (sparseint$-leaf x))))


;; (define sparseint$-non-truncatablep ((width natp)
;;                                     (x sparseint$-p))
;;   (sparseint$-case x
;;     :leaf t
;;     :concat (< x.width (lnfix width)))
;;   ///
;;   (defthm sparseint$-non-truncatablep-implies
;;     (implies (and (sparseint$-non-truncatablep width x)
;;                   (sparseint$-case x :concat))
;;              (< (sparseint$-concat->width x) (nfix width))))

;;   (defthm sparseint$-non-truncatablep-when-leaf
;;     (implies (sparseint$-case x :leaf)
;;              (sparseint$-non-truncatablep width x)))

;;   (defthmd sparseint$-non-truncatablep-when-concat
;;     (implies (sparseint$-case x :concat)
;;              (iff (sparseint$-non-truncatablep width x)
;;                   (< (sparseint$-concat->width x) (nfix width)))))

;;   (defthm sparseint$-non-truncatablep-of-concat
;;     (iff (sparseint$-non-truncatablep width
;;                                      (make-sparseint$-concat
;;                                       :width cwidth
;;                                       :lsbs lsbs
;;                                       :msbs msbs
;;                                       :lsbs-taller lsbs-taller
;;                                       :msbs-taller msbs-taller))
;;          (< (nfix cwidth) (nfix width)))))

;; (define sparseint$-irredundantp ((x sparseint$-p))
;;   :measure (sparseint$-count x)
;;   (sparseint$-case x
;;     :leaf t
;;     :concat (and (sparseint$-non-truncatablep x.width x.lsbs)
;;                  (sparseint$-irredundantp x.lsbs)
;;                  (sparseint$-irredundantp x.msbs)))
;;   ///
;;   (defthm sparseint$-irredundantp-implies
;;     (implies (and (sparseint$-irredundantp x)
;;                   (sparseint$-case x :concat))
;;              (b* (((sparseint$-concat x)))
;;                (and (sparseint$-non-truncatablep x.width x.lsbs)
;;                     (sparseint$-irredundantp x.lsbs)
;;                     (sparseint$-irredundantp x.msbs)))))


;;   )

(define sparseint$-truncate ((width posp)
                            (x sparseint$-p))
  :returns (new-x sparseint$-p)
  :measure (sparseint$-count x)
  (sparseint$-case x
    :leaf (sparseint$-fix x)
    :concat (if (< x.width (lposfix width))
                (sparseint$-fix x)
              (sparseint$-truncate width x.lsbs)))
  ///
  (defret loghead-of-sparseint$-truncate
    (implies (equal width1 (pos-fix width))
             (equal (loghead width1 (sparseint$-val new-x))
                    (loghead width1 (sparseint$-val x))))
    :hints(("Goal" :in-theory (enable loghead-of-logapp-split))))

  (defret logapp-of-sparseint$-truncate
    (implies (equal width1 (pos-fix width))
             (equal (logapp width1 (sparseint$-val new-x) y)
                    (logapp width1 (sparseint$-val x) y)))
    :hints(("Goal" :in-theory (enable logapp-right-assoc))))

  (defret sparseint$-height-correctp-of-sparseint$-truncate
    (implies (sparseint$-height-correctp x)
             (sparseint$-height-correctp new-x))
    :hints(("Goal" :in-theory (enable sparseint$-height-correctp))))

  (defret height-of-sparseint$-truncate
    (<= (sparseint$-height new-x) (sparseint$-height x))
    :rule-classes :linear)

  ;; (defret sparseint$-non-truncatablep-of-truncate
  ;;   (sparseint$-non-truncatablep width new-x)
  ;;   :hints(("Goal" :in-theory (enable sparseint$-non-truncatablep-when-concat))))


  ;; (defret sparseint$-irredundantp-of-truncate
  ;;   (implies (sparseint$-irredundantp x)
  ;;            (sparseint$-irredundantp new-x)))
  )

(define sparseint$-truncate-height ((width posp)
                                   (x sparseint$-p)
                                   (height))
  :guard (and (sparseint$-height-correctp x)
               (equal height (sparseint$-height x)))
  :prepwork ((local (in-theory (enable sparseint$-truncate))))
  :returns (mv (new-x (equal new-x (sparseint$-truncate width x)))
               (new-height (equal new-height (sparseint$-height (sparseint$-truncate width x)))))
  :measure (sparseint$-count x)
  (b* ((height (mbe :logic (sparseint$-height x)
                    :exec height)))
    (sparseint$-case x
      :leaf (mv (sparseint$-fix x) height)
      :concat (if (< x.width (lposfix width))
                  (mv (sparseint$-fix x) height)
                (sparseint$-truncate-height width x.lsbs (- height (if x.msbs-taller 2 1)))))))

(defconst *sparseint$-leaf-bitlimit* 256)
(defmacro sparseint$-leaf-bitlimit () '*sparseint$-leaf-bitlimit*)
(defxdoc sparseint$-leaf-bitlimit
  :parents (sparseint)
  :short "Limit on the size (in bits) of sparseint leaves."
  :long "<p>This constant sets a tradeoff between representation efficiency of
a single element versus opportunities for structure sharing between multiple
elements.  If the bitlimit is small, then we can potentially share structure
more granularly among objects.  However, if it is so small that the bignums on
the leaves are dwarfed in size by the conses used to create the tree nodes,
then this is unlikely to be efficient.</p>

<p>Absent empirical evidence, we currently set the limit to 256, which we think
is likely to be the size of a tree node in most 64-bit Lisps (i.e., two conses,
128 bits each).</p>

<p>We wrap the constant @('*sparseint$-leaf-bitlimit*') in a macro so that if
dereferencing that global variable becomes a performance consideration, we can
change the macro to just return the value instead of the constant.  We use a
defconst in the first place to make it easy to experiment with different values
by redefining the constant.</p>")


(define sparseint$-leaves-mergeable-p ((width posp)
                                       (lsbs integerp)
                                       (msbs integerp))
  :returns (mergep)
  (b* ((msbs (lifix msbs))
       (lsbs (lifix lsbs))
       (width (lposfix width))
       ((when (eql 0 width)) t)
       ((when (or (eql msbs 0)
                  (eql msbs -1)))
        ;; Always make the leaf if it's just a sign-extension of lsbs.
        (b* (((when (eql (logbitp (1- width) lsbs) (logbitp 0 msbs)))
              t)
             ((when (< width (sparseint$-leaf-bitlimit)))
              t))
          ;; Would make a new bignum larger than sparseint$-leaf-bitlimit, so
          ;; make the concat instead.
          nil))
       ;; Since msbs are not -1 or 0, width of new int will be width +
       ;; (integer-length msbs).
       ((when (< (+ width (integer-length msbs))
                 (sparseint$-leaf-bitlimit)))
        t))
    nil))
  
(define sparseint$-mergeable-leaves-p ((width posp)
                                       (lsbs sparseint$-p)
                                       (msbs sparseint$-p))
  :returns (mergep)
  (and (sparseint$-case lsbs :leaf)
       (sparseint$-case msbs :leaf)
       (sparseint$-leaves-mergeable-p width (sparseint$-leaf->val lsbs) (sparseint$-leaf->val msbs)))
  ///
  (defret not-mergeable-leaves-when-lsbs-concat
    (implies (sparseint$-case lsbs :concat)
             (not mergep)))
  (defret not-mergeable-leaves-when-msbs-concat
    (implies (sparseint$-case msbs :concat)
             (not mergep))))


(define sparseint$-finalize-concat ((width posp)
                                    (lsbs sparseint$-p)
                                    (lsbs.height)
                                    (msbs sparseint$-p)
                                    (msbs.height))
  :guard (and (sparseint$-height-correctp lsbs)
              (equal lsbs.height (sparseint$-height lsbs))
              (sparseint$-height-correctp msbs)
              (equal msbs.height (sparseint$-height msbs))
              (within-1 lsbs.height msbs.height))
  :returns (mv (concat sparseint$-p)
               (height (equal height (sparseint$-height concat))))
  (b* ((lsbs.height (mbe :logic (sparseint$-height lsbs)
                         :exec lsbs.height))
       (msbs.height (mbe :logic (sparseint$-height msbs)
                         :exec msbs.height))
       ((unless (and (eql lsbs.height 0)
                     (eql msbs.height 0)))
        (mv (make-sparseint$-concat :width width
                                   :lsbs lsbs
                                   :msbs msbs
                                   :lsbs-taller (> lsbs.height msbs.height)
                                   :msbs-taller (> msbs.height lsbs.height))
            (+ 1 (max lsbs.height msbs.height))))
       ((sparseint$-leaf lsbs))
       ((sparseint$-leaf msbs))
       (width (lposfix width))
       ((when (eql 0 width))
        ;; trivial case
        (mv (sparseint$-fix msbs) 0))
       ;; Try to reason out the integer length of the concatenation.
       ((when (or (eql msbs.val 0)
                  (eql msbs.val -1)))
        ;; Always make the leaf if it's just a sign-extension of lsbs.val.
        (b* (((when (eql (logbitp (1- width) lsbs.val) (logbitp 0 msbs.val)))
              (if (< (integer-length lsbs.val) width)
                  ;; Identity
                  (mv (sparseint$-fix lsbs) 0)
                (mv (make-sparseint$-leaf :val (bignum-logext width lsbs.val))
                    0)))
             ((when (< width (sparseint$-leaf-bitlimit)))
              (mv (make-sparseint$-leaf :val (logapp width lsbs.val msbs.val))
                  0)))
          ;; Would make a new bignum larger than sparseint$-leaf-bitlimit, so
          ;; make the concat instead.
          (mv (make-sparseint$-concat :width width 
                                     :lsbs lsbs
                                     :msbs msbs)
              1)))
       ;; Since msbs are not -1 or 0, width of new int will be width +
       ;; (integer-length msbs).
       ((when (< (+ width (integer-length msbs.val))
                 (sparseint$-leaf-bitlimit)))
        (mv (make-sparseint$-leaf :val (logapp width lsbs.val msbs.val))
            0)))
    (mv (make-sparseint$-concat :width width 
                               :lsbs lsbs
                               :msbs msbs)
        1))
  ///

  ;; (defret <fn>-height-result-correct
  ;;   (implies (and (sparseint$-height-correctp lsbs)
  ;;                 (sparseint$-height-correctp msbs)
  ;;                 (<= (abs (- (sparseint$-height lsbs)
  ;;                             (sparseint$-height msbs))) 1))
  ;;            (equal height (sparseint$-height concat))))

  ;; (local (defthm sparseint$-height-when-leaf
  ;;          (implies (equal (sparseint$-kind x) :leaf)
  ;;                   (equal 0 (sparseint$-height x)))
  ;;          :rule-classes :forward-chaining))

  ;; (local (defthm sparseint$-height-when-concat
  ;;          (implies (equal (sparseint$-kind x) :concat)
  ;;                   (posp (sparseint$-height x)))
  ;;          :rule-classes :forward-chaining))

  (defret <fn>-height-correctp
    (implies (and (sparseint$-height-correctp lsbs)
                  (sparseint$-height-correctp msbs)
                  (within-1 (sparseint$-height lsbs) (sparseint$-height msbs)))
             (sparseint$-height-correctp concat))
    :hints (("goal" :expand ((:free (lsbs-taller msbs-taller)
                              (sparseint$-height-correctp
                               (make-sparseint$-concat :width width
                                                      :lsbs lsbs
                                                      :msbs msbs
                                                      :lsbs-taller lsbs-taller
                                                      :msbs-taller msbs-taller)))
                             (:free (val)
                              (sparseint$-height-correctp
                               (make-sparseint$-leaf :val val)))))))


  (local (defthm logext-when-logbitp
           (implies (and (posp width)
                         (equal bit (logbitp (+ -1 width) x))
                         (syntaxp (quotep bit)))
                    (equal (logext width x)
                           (logapp width x (if bit -1 0))))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))

  (local (in-theory (disable logapp-of-j-0)))

  (local (defthm logapp-identity
           (implies (and (< (integer-length x) (nfix width))
                         (equal y (if (logbitp (+ -1 (nfix width)) x) -1 0)))
                    (equal (logapp width x y)
                           (ifix x)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))

  (defret <fn>-correct
    (equal (sparseint$-val concat)
           (logapp (pos-fix width) (sparseint$-val lsbs) (sparseint$-val msbs))))

  (defretd <fn>-height-possibilities
    (equal (sparseint$-height concat)
           (+ (if (sparseint$-mergeable-leaves-p width lsbs msbs) 0 1)
              (max (sparseint$-height lsbs)
                   (sparseint$-height msbs))))
    :hints(("Goal" :in-theory (enable sparseint$-mergeable-leaves-p
                                      sparseint$-leaves-mergeable-p))))

  (defret <fn>-not-leaf-unless-merged
    (implies (not (sparseint$-mergeable-leaves-p width lsbs msbs))
             (equal (sparseint$-kind concat) :concat))
    :hints(("Goal" :in-theory (enable sparseint$-mergeable-leaves-p
                                      sparseint$-leaves-mergeable-p))))

  (defret <fn>-leaf-when-merged
    (implies (sparseint$-mergeable-leaves-p width lsbs msbs)
             (equal (sparseint$-kind concat) :leaf))
    :hints(("Goal" :in-theory (enable sparseint$-mergeable-leaves-p
                                      sparseint$-leaves-mergeable-p)))))



(local (defthm positive-integer-when-positive-integer-nminus1
         (implies (and (posp (+ -1 n))
                       (acl2-numberp n))
                  (posp n))
         :rule-classes :forward-chaining))


(defines sparseint$-concatenate-rebalance
  :prepwork ((local (defthm max-when-less
                      (implies (< a b)
                               (equal (max a b) b))))
             (local (defthm max-when-greater
                      (implies (< b a)
                               (equal (max a b) a))))
             (local (in-theory (disable min max
                                        sparseint$-height-when-leaf))))
  (define sparseint$-concatenate-rebalance ((width posp)
                                            (lsbs sparseint$-p)
                                            (lsbs.height)
                                            (msbs sparseint$-p)
                                            (msbs.height))
    :guard (and (sparseint$-height-correctp lsbs)
                (equal lsbs.height (sparseint$-height lsbs))
                (sparseint$-height-correctp msbs)
                (equal msbs.height (sparseint$-height msbs)))
    :verify-guards nil
    :measure-debug t
    :well-founded-relation acl2::nat-list-<
    :measure (b* ((lsbs (sparseint$-truncate width lsbs)))
               (if (within-1 (sparseint$-height lsbs)
                     (sparseint$-height msbs))
                   (list 0 0 0)
                 (list (max (sparseint$-height lsbs)
                            (sparseint$-height msbs))
                       (sparseint$-height lsbs)
                       10)))
    :hints (("goal" :in-theory (enable max))
            (and stable-under-simplificationp
                 '(:in-theory (enable sparseint$-height-correct-same-height-branches-implies))))
    :returns (mv (concat sparseint$-p)
                 (height (equal height (sparseint$-height concat))))
    (b* ((msbs.height (mbe :logic (sparseint$-height msbs)
                           :exec msbs.height))
         ;; (lsbs.height (mbe :logic (sparseint$-height lsbs)
         ;;                   :exec lsbs.height))
         ((mv lsbs lsbs.height) (sparseint$-truncate-height width lsbs lsbs.height))
         ((when (within-1 lsbs.height msbs.height))
          (sparseint$-finalize-concat width lsbs lsbs.height msbs msbs.height))
         ((when (< lsbs.height msbs.height))
          (sparseint$-concatenate-rebalance-lsbs width lsbs lsbs.height msbs msbs.height)))
      (sparseint$-concatenate-rebalance-msbs width lsbs lsbs.height msbs msbs.height)))

  (define sparseint$-concatenate-rebalance-lsbs ((width posp)
                                                 (lsbs sparseint$-p)
                                                 (lsbs.height)
                                                 (msbs sparseint$-p)
                                                 (msbs.height))
    :guard (and (sparseint$-height-correctp lsbs)
                (equal lsbs.height (sparseint$-height lsbs))
                (sparseint$-height-correctp msbs)
                (equal msbs.height (sparseint$-height msbs))
                (<= (+ 2 lsbs.height) msbs.height))
    :measure (list (max (sparseint$-height lsbs) (sparseint$-height msbs))
                   (sparseint$-height lsbs)
                   5)
    :returns (mv (concat sparseint$-p)
                 (height (equal height (sparseint$-height concat))))
    (b* ((lsbs.height (mbe :logic (sparseint$-height lsbs)
                           :exec lsbs.height))
         (msbs.height (mbe :logic (sparseint$-height msbs)
                           :exec msbs.height))
         ((unless (mbt (and (< (+ 1 lsbs.height) msbs.height)
                            (sparseint$-height-correctp lsbs)
                            (sparseint$-height-correctp msbs))))
          ;; (Measure check)
          (sparseint$-finalize-concat width lsbs lsbs.height msbs msbs.height))

         ((sparseint$-concat msbs))
         (msbs.lsbs.height (mbe :logic (sparseint$-height msbs.lsbs)
                                :exec (- msbs.height (if msbs.msbs-taller 2 1))))
         (msbs.msbs.height (mbe :logic (sparseint$-height msbs.msbs)
                                :exec (- msbs.height (if msbs.lsbs-taller 2 1))))
         
         ;; Msbs-taller case:
         ;; msbs.height = h
         ;; msbs.lsbs.height = h-2
         ;; msbs.msbs.height = h-1
         ;; lsbs.height <= h-2
         ;; lsbs-concat = concat(lsbs, msbs.lsbs)
         ;; lsbs-concat.height <= h-1
         ;; result = concat(lsbs-concat, msbs.msbs)

         ;; Lsbs-taller case:
         ;; msbs.height = h
         ;; msbs.lsbs.height = h-1
         ;; msbs.msbs.height = h-2
         ;; lsbs.height <= h-2
         ;; msbs.lsbs.lsbs.height = h-2 or h-3
         ;; msbs.lsbs.msbs.height = h-2 or h-3
         ;; lsbs-concat = concat(lsbs, msbs.lsbs.lsbs)
         ;; lsbs-concat.height <= h-1
         ;; msbs-concat = concat(msbs.lsbs.msbs, msbs.msbs)
         ;; msbs-concat.height <= h-1
         ;; result = concat(lsbs-concat, msbs-concat)

         ;; Neither taller case:
         ;; msbs.height = h
         ;; msbs.lsbs.height = h-1
         ;; msbs.msbs.height = h-1
         ;; lsbs.height <= h-2

         ;; Do it like msbs-taller case:
         ;; lsbs-concat = concat(lsbs, msbs.lsbs)
         ;; lsbs-concat.height <= h
         ;; result = concat(lsbs-concat, msbs.msbs) -- either max is h-1 or within 1

         ;; Do it like lsbs-taller case:
         ;; msbs.lsbs.lsbs.height = h-2 or h-3
         ;; msbs.lsbs.msbs.height = h-2 or h-3
         ;; lsbs-concat = concat(lsbs, msbs.lsbs.lsbs)
         ;; lsbs-concat.height <= h-1
         ;; msbs-concat = concat(msbs.lsbs.msbs, msbs.msbs)
         ;; msbs-concat.height <= h
         ;; result = concat(lsbs-concat, msbs-concat) -- bad measure

         ((when (mbe :logic (<= msbs.lsbs.height msbs.msbs.height)
                     :exec (not msbs.lsbs-taller)))
          (b* (((mv lsbs-concat lsbs-concat.height)
                (sparseint$-concatenate-rebalance width
                                                  lsbs
                                                  lsbs.height
                                                  msbs.lsbs
                                                  msbs.lsbs.height))
               (lsbs-concat.height (mbe :logic (sparseint$-height lsbs-concat)
                                        :exec lsbs-concat.height))
               ((unless (mbt (<= lsbs-concat.height msbs.height)))
                ;; (Measure check)
                (sparseint$-finalize-concat width lsbs lsbs.height msbs msbs.height)))

            ;; In the worst case, the above call produces lsbs-concat.height == msbs.height
            ;; statement in the second literal.  Lsbs-concat.height might equal
            ;; msbs.height in which case the measure wouldn't decrease
            ;; otherwise, but this means it's within 1 of msbs.msbs.height.
            (sparseint$-concatenate-rebalance (+ (lposfix width) msbs.width)
                                              lsbs-concat
                                              lsbs-concat.height
                                              msbs.msbs
                                              msbs.msbs.height)))

         ;; Here we need to dig further into msbs.lsbs since otherwise if we
         ;; merge lsbs with msbs.lsbs we might obtain a result that is the same
         ;; height as msbs, whereas msbs.msbs is two less, and therefore the
         ;; measure for the last merge fails.
         ((sparseint$-concat msbs.lsbs))
         (msbs.lsbs.lsbs.height (mbe :logic (sparseint$-height msbs.lsbs.lsbs)
                                     :exec (- msbs.lsbs.height (if msbs.lsbs.msbs-taller 2 1))))
         (msbs.lsbs.msbs.height (mbe :logic (sparseint$-height msbs.lsbs.msbs)
                                     :exec (- msbs.lsbs.height (if msbs.lsbs.lsbs-taller 2 1))))
         ((mv lsbs-concat lsbs-concat.height)
          (sparseint$-concatenate-rebalance width
                                            lsbs
                                            lsbs.height
                                            msbs.lsbs.lsbs
                                            msbs.lsbs.lsbs.height))
         (lsbs-concat.height (mbe :logic (sparseint$-height lsbs-concat)
                                  :exec lsbs-concat.height))
         ;; ((when (<= msbs.width msbs.lsbs.width))
         ;;  (b* (((unless (mbt (< lsbs-concat.height msbs.height)))
         ;;        (sparseint$-finalize-concat width lsbs lsbs.height msbs msbs.height)))
         ;;    (sparseint$-concatenate-rebalance (+ (lposfix width) msbs.width)
         ;;                                     lsbs-concat
         ;;                                     lsbs-concat.height
         ;;                                     msbs.msbs
         ;;                                     msbs.msbs.height)))

         ((mv msbs-concat msbs-concat.height)
          (if (<= msbs.width msbs.lsbs.width)
              (mv msbs.msbs msbs.msbs.height)
            (sparseint$-concatenate-rebalance (- msbs.width msbs.lsbs.width)
                                              msbs.lsbs.msbs
                                              msbs.lsbs.msbs.height
                                              msbs.msbs
                                              msbs.msbs.height)))
         (msbs-concat.height (mbe :logic (sparseint$-height msbs-concat)
                                  :exec msbs-concat.height))
         ((unless (mbt (and (< lsbs-concat.height msbs.height)
                            (< msbs-concat.height msbs.height))))
          (sparseint$-finalize-concat width lsbs lsbs.height msbs msbs.height))
         )
      (sparseint$-concatenate-rebalance (+ (lposfix width) (min msbs.width msbs.lsbs.width))
                                        lsbs-concat
                                        lsbs-concat.height
                                        msbs-concat
                                        msbs-concat.height)))

  (define sparseint$-concatenate-rebalance-msbs ((width posp)
                                                 (lsbs sparseint$-p)
                                                 (lsbs.height)
                                                 (msbs sparseint$-p)
                                                 (msbs.height))
    :guard (and (sparseint$-height-correctp lsbs)
                (equal lsbs.height (sparseint$-height lsbs))
                (sparseint$-height-correctp msbs)
                (equal msbs.height (sparseint$-height msbs))
                (<= (+ 2 msbs.height) lsbs.height))
    :measure (list (max (sparseint$-height lsbs) (sparseint$-height msbs))
                   (sparseint$-height lsbs)
                   5)
    :returns (mv (concat sparseint$-p)
                 (height (equal height (sparseint$-height concat))))
    (b* ((lsbs.height (mbe :logic (sparseint$-height lsbs)
                           :exec lsbs.height))
         (msbs.height (mbe :logic (sparseint$-height msbs)
                           :exec msbs.height))
         ((unless (mbt (and (< (+ 1 msbs.height) lsbs.height)
                            (sparseint$-height-correctp lsbs)
                            (sparseint$-height-correctp msbs))))
          ;; (Measure check)
          (sparseint$-finalize-concat width lsbs lsbs.height msbs msbs.height))

         ((sparseint$-concat lsbs))
         (lsbs.lsbs.height (mbe :logic (sparseint$-height lsbs.lsbs)
                                :exec (- lsbs.height (if lsbs.msbs-taller 2 1))))
         (lsbs.msbs.height (mbe :logic (sparseint$-height lsbs.msbs)
                                :exec (- lsbs.height (if lsbs.lsbs-taller 2 1))))
         
         ;; Lsbs-taller case:
         ;; lsbs.height = h
         ;; lsbs.msbs.height = h-2
         ;; lsbs.lsbs.height = h-1
         ;; msbs.height <= h-2
         ;; msbs-concat = concat(lsbs.msbs, msbs)
         ;; msbs-concat.height <= h-1
         ;; result = concat(lsbs.lsbs, msbs-concat)

         ;; Msbs-taller case:
         ;; lsbs.height = h
         ;; lsbs.msbs.height = h-1
         ;; lsbs.lsbs.height = h-2
         ;; msbs.height <= h-2
         ;; lsbs.msbs.msbs.height = h-2 or h-3
         ;; lsbs.msbs.lsbs.height = h-2 or h-3
         ;; msbs-concat = concat(lsbs.msbs.msbs, msbs)
         ;; msbs-concat.height <= h-1
         ;; lsbs-concat = concat(lsbs.lsbs, lsbs.msbs.lsbs)
         ;; lsbs-concat.height <= h-1
         ;; result = concat(lsbs-concat, msbs-concat)

         ;; Neither taller case:
         ;; lsbs.height = h
         ;; lsbs.msbs.height = h-1
         ;; lsbs.lsbs.height = h-1
         ;; msbs.height <= h-2

         ;; Do it like lsbs-taller case:
         ;; msbs-concat = concat(msbs, lsbs.msbs)
         ;; msbs-concat.height <= h
         ;; result = concat(lsbs.lsbs, msbs-concat)
         ;;  -- bad measure if lsbs.lsbs gets truncated and msbs-concat.height = h

         ;; Fix: Add LSBs height as its own measure term.


         ((when (mbe :logic (<= lsbs.msbs.height lsbs.lsbs.height)
                     :exec (not lsbs.msbs-taller)))
          (b* (((mv msbs-concat msbs-concat.height)
                (if (<= (lposfix width) lsbs.width)
                    (mv msbs msbs.height)
                  (sparseint$-concatenate-rebalance (- (lposfix width) lsbs.width)
                                                    lsbs.msbs
                                                    lsbs.msbs.height
                                                    msbs
                                                    msbs.height)))
               (msbs-concat.height (mbe :logic (sparseint$-height msbs-concat)
                                        :exec msbs-concat.height))

               ((unless (mbt (<= msbs-concat.height lsbs.height)))
                ;; (Measure check)
                (sparseint$-finalize-concat width lsbs lsbs.height msbs msbs.height))
               )

            (sparseint$-concatenate-rebalance (min lsbs.width (lposfix width))
                                              lsbs.lsbs
                                              lsbs.lsbs.height
                                              msbs-concat
                                              msbs-concat.height)))

         ;; Here we need to dig further into msbs.lsbs since otherwise if we
         ;; merge lsbs with msbs.lsbs we might obtain a result that is the same
         ;; height as msbs, whereas msbs.msbs is two less, and therefore the
         ;; measure for the last merge fails.
         ((sparseint$-concat lsbs.msbs))
         (lsbs.msbs.msbs.height (mbe :logic (sparseint$-height lsbs.msbs.msbs)
                                     :exec (- lsbs.msbs.height (if lsbs.msbs.lsbs-taller 2 1))))
         (lsbs.msbs.lsbs.height (mbe :logic (sparseint$-height lsbs.msbs.lsbs)
                                     :exec (- lsbs.msbs.height (if lsbs.msbs.msbs-taller 2 1))))
         ((mv lsbs-concat lsbs-concat.height)
          (sparseint$-concatenate-rebalance lsbs.width
                                            lsbs.lsbs
                                            lsbs.lsbs.height
                                            lsbs.msbs.lsbs
                                            lsbs.msbs.lsbs.height))
         (lsbs-concat.height (mbe :logic (sparseint$-height lsbs-concat)
                                  :exec lsbs-concat.height))
         ((mv msbs-concat msbs-concat.height)
          (if (<= (lposfix width) (+ lsbs.width lsbs.msbs.width))
              (mv msbs msbs.height)
            (sparseint$-concatenate-rebalance (- (lposfix width) (+ lsbs.width lsbs.msbs.width))
                                              lsbs.msbs.msbs
                                              lsbs.msbs.msbs.height
                                              msbs
                                              msbs.height)))
         (msbs-concat.height (mbe :logic (sparseint$-height msbs-concat)
                                  :exec msbs-concat.height))
         ((unless (mbt (and (< msbs-concat.height lsbs.height)
                            (< lsbs-concat.height lsbs.height))))
          (sparseint$-finalize-concat width lsbs lsbs.height msbs msbs.height))
         )
      (sparseint$-concatenate-rebalance (min (lposfix width) (+ lsbs.width lsbs.msbs.width))
                                        lsbs-concat
                                        lsbs-concat.height
                                        msbs-concat
                                        msbs-concat.height)))
  ///
  (local (in-theory (disable sparseint$-concatenate-rebalance
                             sparseint$-concatenate-rebalance-lsbs
                             sparseint$-concatenate-rebalance-msbs)))

  (std::defret-mutual sparseint$-concatenate-rebalance-height-result-correct
    (defret <fn>-height-result-correct
      (equal height (sparseint$-height concat))
      :hints ('(:expand (<call>)))
      :fn sparseint$-concatenate-rebalance)
    (defret <fn>-height-result-correct
      (equal height (sparseint$-height concat))
      :hints ('(:expand (<call>)))
      :fn sparseint$-concatenate-rebalance-lsbs)
    (defret <fn>-height-result-correct
      (equal height (sparseint$-height concat))
      :hints ('(:expand (<call>)))
      :fn sparseint$-concatenate-rebalance-msbs))

  ;;(local (in-theory (enable logapp-right-assoc)))

  (local (defthmd sparseint$-val-when-concat
           (implies (sparseint$-case x :concat)
                    (equal (sparseint$-val x)
                           (b* (((sparseint$-concat x)))
                             (logapp x.width (sparseint$-val x.lsbs) (sparseint$-val x.msbs)))))
           :hints(("Goal" :in-theory (enable sparseint$-val)))))

  (local (defthm logapp-when-width-zp
           (implies (zp width)
                    (equal (logapp width x y)
                           (ifix y)))))

  (std::defret-mutual sparseint$-concatenate-rebalance-correct
    (defret <fn>-correct
      (equal (sparseint$-val concat)
             (logapp (pos-fix width) (sparseint$-val lsbs) (sparseint$-val msbs)))
      :hints ('(:expand (<call>)))
      :fn sparseint$-concatenate-rebalance)
    (defret <fn>-correct
      (equal (sparseint$-val concat)
             (logapp (pos-fix width) (sparseint$-val lsbs) (sparseint$-val msbs)))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   '(:in-theory (enable logapp-right-assoc min max
                                        sparseint$-val-when-concat))))
      :fn sparseint$-concatenate-rebalance-lsbs)
    (defret <fn>-correct
      (equal (sparseint$-val concat)
             (logapp (pos-fix width) (sparseint$-val lsbs) (sparseint$-val msbs)))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   '(:in-theory (enable logapp-right-assoc min max
                                        sparseint$-val-when-concat))))
      :fn sparseint$-concatenate-rebalance-msbs))

  
  (local (defthm open-max-of-sparseint$-heights
           (equal (max (sparseint$-height x) (sparseint$-height y))
                  (if (< (sparseint$-height x) (sparseint$-height y))
                      (sparseint$-height y)
                    (sparseint$-height x)))
           :hints(("Goal" :in-theory (enable max)))))

  (local (in-theory (enable sparseint$-finalize-concat-height-possibilities)))

  (std::defret-mutual sparseint$-concatenate-rebalance-height-correct
    (defret <fn>-height-correct
      (implies (and (sparseint$-height-correctp lsbs)
                    (sparseint$-height-correctp msbs))
               (and (sparseint$-height-correctp concat)
                    (<= (sparseint$-height concat) (+ 1 (max (sparseint$-height lsbs)
                                                             (sparseint$-height msbs))))))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   '(:in-theory (enable within-1)))
              )
      :rule-classes (:rewrite
                     (:linear :corollary
                      (implies (and (sparseint$-height-correctp lsbs)
                                    (sparseint$-height-correctp msbs))
                               (<= (sparseint$-height concat) (+ 1 (max (sparseint$-height lsbs)
                                                                        (sparseint$-height msbs)))))))
      :fn sparseint$-concatenate-rebalance)
    (defret <fn>-height-correct
      (implies (and (sparseint$-height-correctp lsbs)
                    (sparseint$-height-correctp msbs)
                    (<= (+ 2 (sparseint$-height lsbs)) (sparseint$-height msbs)))
               (and (sparseint$-height-correctp concat)
                    (<= (sparseint$-height concat) (+ 1 (sparseint$-height msbs)))))
      :hints ('(:expand (<call>)))
      :rule-classes (:rewrite
                     (:linear :corollary
                      (implies (and (sparseint$-height-correctp lsbs)
                                    (sparseint$-height-correctp msbs)
                                    (<= (+ 2 (sparseint$-height lsbs)) (sparseint$-height msbs)))
                               (<= (sparseint$-height concat) (+ 1 (sparseint$-height msbs))))))
      :fn sparseint$-concatenate-rebalance-lsbs)
    (defret <fn>-height-correct
      (implies (and (sparseint$-height-correctp lsbs)
                    (sparseint$-height-correctp msbs)
                    (<= (+ 2 (sparseint$-height msbs)) (sparseint$-height lsbs)))
               (and (sparseint$-height-correctp concat)
                    (<= (sparseint$-height concat) (+ 1 (sparseint$-height lsbs)))))
      :hints ('(:expand (<call>)))
      :rule-classes (:rewrite
                     (:linear :corollary
                      (implies (and (sparseint$-height-correctp lsbs)
                                    (sparseint$-height-correctp msbs)
                                    (<= (+ 2 (sparseint$-height msbs)) (sparseint$-height lsbs)))
                               (<= (sparseint$-height concat) (+ 1 (sparseint$-height lsbs))))))
      :fn sparseint$-concatenate-rebalance-msbs))

  (local (defthm msbs-are-concat
           (implies (sparseint$-height-correctp x)
                    (and (implies (and (sparseint$-concat->lsbs-taller x)
                                       (< 2 (sparseint$-height x)))
                                  (equal (sparseint$-kind (sparseint$-concat->msbs x))
                                         :concat))
                         (implies (and (not (sparseint$-concat->lsbs-taller x))
                                       (<= 2 (sparseint$-height x)))
                                  (equal (sparseint$-kind (sparseint$-concat->msbs x))
                                         :concat))))
           :hints(("Goal" :expand ((sparseint$-height-correctp x)
                                   (sparseint$-height x))))))

  (local (defthm lsbs-are-concat
           (implies (sparseint$-height-correctp x)
                    (and (implies (and (sparseint$-concat->msbs-taller x)
                                       (< 2 (sparseint$-height x)))
                                  (equal (sparseint$-kind (sparseint$-concat->lsbs x))
                                         :concat))
                         (implies (and (not (sparseint$-concat->msbs-taller x))
                                       (<= 2 (sparseint$-height x)))
                                  (equal (sparseint$-kind (sparseint$-concat->lsbs x))
                                         :concat))))
           :hints(("Goal" :expand ((sparseint$-height-correctp x)
                                   (sparseint$-height x))))))

  (defret sparseint$-concatenate-rebalance-height-less-than-bound
    (implies (and (sparseint$-height-correctp lsbs)
                  (sparseint$-height-correctp msbs))
             (and (implies (and (<= (sparseint$-height lsbs) (+ -1 x))
                                (<= (sparseint$-height msbs) (+ -1 x)))
                           (<= (sparseint$-height concat) x))
                  (implies (and (< (sparseint$-height lsbs) (+ -1 x))
                                (< (sparseint$-height msbs) (+ -1 x)))
                           (< (sparseint$-height concat) x))))
    :hints(("Goal" :in-theory (disable sparseint$-concatenate-rebalance-height-correct)
            :use sparseint$-concatenate-rebalance-height-correct))
    :fn sparseint$-concatenate-rebalance)
  
  (local (defthm max-lower-bound-1
           (<= a (max a b))
           :hints(("Goal" :in-theory (enable max)))
           :rule-classes :linear))

  (local (defthm max-lower-bound-2
           (<= b (max a b))
           :hints(("Goal" :in-theory (enable max)))
           :rule-classes :linear))

  (verify-guards sparseint$-concatenate-rebalance
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable within-1)))))

  (fty::deffixequiv-mutual sparseint$-concatenate-rebalance))



(define sparseint$-concatenate ((width natp)
                                (lsbs sparseint$-p)
                                (msbs sparseint$-p))
  :guard (and (sparseint$-height-correctp lsbs)
              (sparseint$-height-correctp msbs))
  :returns (concat sparseint$-p)
  (b* (((when (eql (lnfix width) 0))
        (sparseint$-fix msbs))
       ((mv ans ?height)
        (sparseint$-concatenate-rebalance width lsbs (sparseint$-height lsbs) msbs (sparseint$-height msbs))))
    ans)
  ///
  (defret sparseint$-height-correct-of-sparseint$-concatenate
    (implies (and (sparseint$-height-correctp lsbs)
                  (sparseint$-height-correctp msbs))
             (sparseint$-height-correctp concat)))

  (defret sparseint$-concatenate-correct
    (equal (sparseint$-val concat)
           (logapp width (sparseint$-val lsbs) (sparseint$-val msbs))))

  (defret height-of-sparseint$-concatenate
    (implies (and (sparseint$-height-correctp lsbs)
                  (sparseint$-height-correctp msbs))
             (<= (sparseint$-height concat)
                 (+ 1 (max (sparseint$-height lsbs)
                           (sparseint$-height msbs)))))
    :rule-classes :linear))



(define sparseint$-rightshift-rec ((shift natp)
                                   (x sparseint$-p)
                                   (x.height))
  :guard (and (sparseint$-height-correctp x)
              (equal x.height (sparseint$-height x)))
  :measure (sparseint$-count x)
  :returns (mv (rightshift sparseint$-p)
               (height (equal height (sparseint$-height rightshift))))
  :verify-guards nil
  (sparseint$-case x
    :leaf (mv (sparseint$-leaf (logtail shift x.val)) 0)
    :concat (b* ((shift (lnfix shift))
                 (x.height (mbe :logic (sparseint$-height x)
                                :exec x.height))
                 ((when (eql shift 0)) (mv (sparseint$-fix x) x.height))
                 (x.msbs.height (mbe :logic (sparseint$-height x.msbs)
                                     :exec (- x.height (if x.lsbs-taller 2 1))))
                 ((when (<= x.width shift))
                  (sparseint$-rightshift-rec (- shift x.width) x.msbs x.msbs.height))
                 (x.lsbs.height (mbe :logic (sparseint$-height x.lsbs)
                                     :exec (- x.height (if x.msbs-taller 2 1))))
                 ((mv lsbs-shift lsbs-shift-height)
                  (sparseint$-rightshift-rec shift x.lsbs x.lsbs.height)))
              (sparseint$-concatenate-rebalance (- x.width shift)
                                                lsbs-shift lsbs-shift-height
                                                x.msbs x.msbs.height)))
  ///
  (defret sparseint$-height-correctp-of-<fn>
    (implies (sparseint$-height-correctp x)
             (sparseint$-height-correctp rightshift))
    :hints (("goal" :induct <call>)))

  (defret <fn>-correct
    (equal (sparseint$-val rightshift)
           (logtail shift (sparseint$-val x)))
    :hints(("Goal" :in-theory (enable logtail-of-logapp-split))))

  (local (defret sparseint$-concatenate-height-less-than-bound
           (implies (and (sparseint$-height-correctp lsbs)
                         (sparseint$-height-correctp msbs))
                    (and (implies (and (<= (sparseint$-height lsbs) (+ -1 x))
                                       (<= (sparseint$-height msbs) (+ -1 x)))
                                  (<= (sparseint$-height concat) x))
                         (implies (and (< (sparseint$-height lsbs) (+ -1 x))
                                       (< (sparseint$-height msbs) (+ -1 x)))
                                  (< (sparseint$-height concat) x))))
           :hints(("Goal" :in-theory (disable height-of-sparseint$-concatenate)
                   :use height-of-sparseint$-concatenate))
           :fn sparseint$-concatenate))

  (defret height-of-<fn>
    (implies (sparseint$-height-correctp x)
             (<= (sparseint$-height rightshift) (sparseint$-height x)))
    :rule-classes :linear)

  (verify-guards sparseint$-rightshift-rec))

(define sparseint$-rightshift ((shift natp)
                               (x sparseint$-p))
  :guard (sparseint$-height-correctp x)
  :returns (rightshift sparseint$-p)
  :verify-guards nil
  (sparseint$-case x
    :leaf (sparseint$-leaf (logtail shift x.val))
    :concat (b* (((mv shift ?height)
                  (sparseint$-rightshift-rec shift x (sparseint$-height x))))
              shift))
  ///
  (defret sparseint$-height-correctp-of-sparseint$-rightshift
    (implies (sparseint$-height-correctp x)
             (sparseint$-height-correctp rightshift)))

  (defret sparseint$-rightshift-correct
    (equal (sparseint$-val rightshift)
           (logtail shift (sparseint$-val x))))

  (defret height-of-sparseint$-rightshift
    (implies (sparseint$-height-correctp x)
             (<= (sparseint$-height rightshift) (sparseint$-height x)))
    :rule-classes :linear)

  (verify-guards sparseint$-rightshift))

(local
 (progn
   ;; performance test
   (define n-rightshifts ((n natp) (x sparseint$-p) acc)
     :guard (sparseint$-height-correctp x)
     (if (zp n)
         acc
       (n-rightshifts (1- n) x (cons (sparseint$-rightshift (* 40 (1- n)) x) acc))))

   (define n-concats ((n natp) (x sparseint$-p))
     :guard (sparseint$-height-correctp x)
     :returns (concat sparseint$-p)
     (if (zp n)
         (sparseint$-fix x)
       (n-concats (1- n) (sparseint$-concatenate 35 (sparseint$-leaf n) x)))
     ///
     (defret sparseint$-height-correctp-of-n-concats
       (implies (sparseint$-height-correctp x)
                (sparseint$-height-correctp concat))
       :hints (("goal" :induct t))))

   (define benchmark ((concats natp) (shifts natp))
     (b* ((- (gc$))
          (concat (time$ (n-concats concats (sparseint$-leaf -2))))
          (- (gc$))
          (shifts (time$ (n-rightshifts shifts concat nil))))
       (len shifts)))))

(define sparseint$-bit ((n natp)
                        (x sparseint$-p))
  :returns (bit bitp :rule-classes :type-prescription)
  :measure (sparseint$-count x)
  (sparseint$-case x
    :leaf (logbit n x.val)
    :concat (b* ((n (lnfix n))
                 ((when (< n x.width))
                  (sparseint$-bit n x.lsbs)))
              (sparseint$-bit (- n x.width) x.msbs)))
  ///
  (defret sparseint$-bit-correct
    (equal (sparseint$-bit n x)
           (logbit n (sparseint$-val x)))))
  


(define sparseint-p (x)
  :parents (sparseint)
  :short "Recognizer for well-formed sparseints"
  (and (sparseint$-p x)
       (sparseint$-height-correctp x)))

(define sparseint-fix ((x sparseint-p))
  :parents (sparseint)
  :short "Fixing function for sparseints"
  :returns (new-x sparseint-p)
  :measure (sparseint$-count x)
  :hints (("goal" :expand ((sparseint$-height-correctp x))))
  :prepwork ((local (in-theory (enable sparseint-p
                                       sparseint$-height-correctp-when-leaf))))
  :verify-guards nil
  :inline t
  :hooks nil
  (mbe :logic
       (b* ((x (sparseint$-fix x))
            ((when (sparseint$-height-correctp x)) x)
            ((sparseint$-concat x)))
         (sparseint$-concatenate x.width
                                  (sparseint-fix x.lsbs)
                                  (sparseint-fix x.msbs)))
       :exec x)
  ///
  
  (defthm sparseint-fix-when-sparseint-p
    (implies (sparseint-p x)
             (equal (sparseint-fix x) x)))

  (verify-guards sparseint-fix$inline)

  (local (in-theory (disable sparseint-p sparseint-fix)))

  (fty::deffixtype sparseint :pred sparseint-p :fix sparseint-fix
    :equiv sparseint-equiv :define t :forward t))

(local (defthm sparseint$-p-of-sparseint-fix
         (sparseint$-p (sparseint-fix x))
         :hints(("Goal" :in-theory (enable sparseint-fix)))))

(local (defthm sparseint$-height-correct-of-sparseint-fix
         (sparseint$-height-correctp (sparseint-fix x))
         :hints(("Goal" :in-theory (enable sparseint-fix)))))

(define sparseint-val ((x sparseint-p))
  :parents (sparseint)
  :short "Get the integer value of a sparseint"
  :returns (val integerp :rule-classes :type-prescription)
  (sparseint$-val (sparseint-fix x)))

(define sparseint-concatenate ((width natp)
                               (lsbs sparseint-p)
                               (msbs sparseint-p))
  :parents (sparseint)
  :short "Form the concatenation (logapp) of two sparseints"
  :returns (concat sparseint-p)
  :prepwork ((local (in-theory (enable sparseint-p))))
  :inline t
  (sparseint$-concatenate width (sparseint-fix lsbs) (sparseint-fix msbs))
  ///
  (defret sparseint-concatenate-correct
    (equal (sparseint-val concat)
           (logapp width (sparseint-val lsbs) (sparseint-val msbs)))
    :hints(("Goal" :in-theory (enable sparseint-val)))))


(define sparseint-rightshift  ((shift natp)
                               (x sparseint-p))
  :parents (sparseint)
  :short "Right-shift a sparseint by some shift amount"
  :prepwork ((local (in-theory (enable sparseint-p))))
  :inline t
  :returns (rightshift sparseint-p)
  (sparseint$-rightshift shift (sparseint-fix x))
  ///
  (defret sparseint-rightshift-correct
    (equal (sparseint-val rightshift)
           (logtail shift (sparseint-val x)))
    :hints(("Goal" :in-theory (enable sparseint-val)))))

(define sparseint-ash ((x sparseint-p)
                       (shift integerp))
  :parents (sparseint)
  :short "Shift a sparseint by some amount, positive or negative"
  :returns (ash sparseint-p)
  (b* ((shift (lifix shift)))
    (cond ((eql shift 0) (sparseint-fix x))
          ((< shift 0) (sparseint-rightshift (- shift) x))
          (t (sparseint-concatenate shift 0 x))))
  ///
  (defret sparseint-ash-correct
    (equal (sparseint-val ash)
           (ash (sparseint-val x) shift))))

(define sparseint-bit ((n natp)
                       (x sparseint-p))
  :parents (sparseint)
  :short "Extract the bit at the given index from a sparseint"
  :returns (bit bitp :rule-classes :type-prescription)
  :inline t
  (sparseint$-bit n (sparseint-fix x))
  ///
  (defret sparseint-bit-correct
    (equal (sparseint-bit n x)
           (logbit n (sparseint-val x)))
    :hints(("Goal" :in-theory (enable sparseint-val)))))

(define sparseint$-sign-ext ((n posp)
                             (x sparseint$-p)
                             (x.height natp))
  :guard (and (sparseint$-height-correctp x)
              (equal x.height (sparseint$-height x)))
  :guard-debug t
  :returns (mv (ext sparseint$-p)
               (height (equal height (sparseint$-height ext))))
  (b* ((n (lposfix n))
       (x.height (mbe :logic (sparseint$-height x) :exec x.height)))
    (sparseint$-concatenate-rebalance
     n x x.height (sparseint$-leaf (- (sparseint$-bit (1- n) x))) 0))
  ///
  (local (defthm logapp-when-zp
           (implies (zp w)
                    (equal (logapp w x y) (ifix y)))
           :hints(("Goal" :in-theory (enable logapp**)))))
  (local (defthm logbitp-when-zp
           (implies (and (syntaxp (not (equal w ''0)))
                         (zp w))
                    (equal (logbitp w x) (logbitp 0 x)))
           :hints(("Goal" :in-theory (enable logbitp**)))))

  (local (defthm logext-in-terms-of-logapp
           (equal (logext n x)
                  (logapp (pos-fix n) x (- (logbit (1- (pos-fix n)) x))))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs
                                              pos-fix)))))

  (defret <fn>-height-correct
    (implies (sparseint$-height-correctp x)
             (sparseint$-height-correctp ext)))

  (defret <fn>-correct
    (equal (sparseint$-val ext)
           (logext n (sparseint$-val x)))))

(define sparseint-sign-ext ((n posp)
                            (x sparseint-p))
  :parents (sparseint)
  :short "Sign-extend the given sparseint at the given (positive) position"
  :returns (ext sparseint-p)
  :prepwork ((local (in-theory (enable sparseint-p))))
  (b* ((x (sparseint-fix x))
       ((mv ans ?height) (sparseint$-sign-ext n x (sparseint$-height x))))
    ans)
  ///
  (defret sparseint-sign-ext-correct
    (equal (sparseint-val (sparseint-sign-ext n x))
           (logext n (sparseint-val x)))
    :hints(("Goal" :in-theory (enable sparseint-val)))))






(local
 (defsection logand-theory
   (local (defun logapp-binary-ind (w x y)
            (if (zp w)
                (list x y)
              (logapp-binary-ind (1- w) (logcdr x) (logcdr y)))))
   (defthmd logand-over-logapp
     (equal (logand z (logapp w x y))
            (logapp w (logand x (logext w z))
                    (logand y (logtail w z))))
     :hints(("goal" :induct (logapp-binary-ind w x z)
             :in-theory (enable* ihsext-redefs))))

   (defthmd logior-over-logapp
     (equal (logior z (logapp w x y))
            (logapp w (logior x (logext w z))
                    (logior y (logtail w z))))
     :hints(("goal" :induct (logapp-binary-ind w x z)
             :in-theory (enable* ihsext-redefs))))

   (defthmd logxor-over-logapp
     (equal (logxor z (logapp w x y))
            (logapp w (logxor x (logext w z))
                    (logxor y (logtail w z))))
     :hints(("goal" :induct (logapp-binary-ind w x z)
             :in-theory (enable* ihsext-redefs))))

   (defun find-atom (a x)
     (if (atom x)
         (equal x a)
       (or (find-atom a (car x))
           (find-atom a (cdr x)))))


   (defthm logand-of-loghead
     (equal (logand (loghead n x) (loghead n y))
            (loghead n (logand x y))))
   (in-theory (disable loghead-of-logand))

   (defthm logand-of-logext
     (equal (logand (logext n x) (logext n y))
            (logext n (logand x y))))
   (in-theory (disable logext-of-logand))

   (defthm logior-of-loghead
     (equal (logior (loghead n x) (loghead n y))
            (loghead n (logior x y))))
   (in-theory (disable loghead-of-logior))

   (defthm logior-of-logext
     (equal (logior (logext n x) (logext n y))
            (logext n (logior x y))))
   (in-theory (disable logext-of-logior))

   (defthm logxor-of-loghead
     (equal (logxor (loghead n x) (loghead n y))
            (loghead n (logxor x y))))
   (in-theory (disable loghead-of-logxor))

   (defthm logext-of-lognot
     (equal (logext n (lognot x))
            (lognot (logext n x)))
     :hints(("Goal" :in-theory (enable* ihsext-inductions
                                        ihsext-recursive-redefs))))

   (defthm logxor-of-logext
     (equal (logxor (logext n x) (logext n y))
            (logext n (logxor x y)))
     :hints(("goal" :induct (logapp-binary-ind n x y)
             :in-theory (enable* ihsext-redefs))))

   (defthm logext-of-logxor
     (equal (logext n (logxor x y))
            (logxor (logext n x) (logext n y))))

   (in-theory (disable logext-of-logxor))

   (defthm pos-fix-when-zp
     (implies (zp x)
              (equal (pos-fix x) 1))
     :hints(("Goal" :in-theory (enable pos-fix))))



   (defthm logext-of-loghead
     (implies (<= (pos-fix w1) (nfix w2))
              (equal (logext w1 (loghead w2 x))
                     (logext w1 x)))
     :hints(("Goal" :in-theory (enable* ihsext-inductions
                                        ihsext-recursive-redefs))))

   (defthm loghead-of-logext
     (implies (<= (nfix w2) (pos-fix w1))
              (equal (loghead w2 (logext w1 x))
                     (loghead w2 x)))
     :hints(("Goal" :in-theory (enable* ihsext-inductions
                                        ihsext-recursive-redefs))))

   (defthm logext-of-logext
     (implies (<= (pos-fix w1) (pos-fix w2))
              (equal (logext w1 (logext w2 x))
                     (logext w1 x)))
     :hints(("Goal" :in-theory (enable* ihsext-inductions
                                        ihsext-recursive-redefs))))

   (fty::deffixcong pos-equiv equal (logext n x) n
     :hints(("Goal" :in-theory (enable* ihsext-inductions
                                        ihsext-recursive-redefs))))

   
   (defthm logext-of-logapp-split
     (equal (logext w1 (logapp w2 x y))
            (if (<= (pos-fix w1) (nfix w2))
                (logext w1 x)
              (logapp w2 x (logext (- (pos-fix w1) (nfix w2)) y))))
     :hints(("Goal" :in-theory (enable* ihsext-inductions
                                        ihsext-recursive-redefs))))


   (defthmd equal-of-logapp-split
     (equal (equal (logapp w x y) z)
            (and (integerp z)
                 (equal (loghead w x) (loghead w z))
                 (equal (ifix y) (logtail w z))))
     :hints(("Goal" :in-theory (enable* ihsext-inductions
                                        ihsext-recursive-redefs))))

   (defthmd equal-of-logapp-split-logext
     (equal (equal (logapp w x y) z)
            (and (integerp z)
                 (or (zp w) (equal (logext w x) (logext w z)))
                 (equal (ifix y) (logtail w z))))
     :hints(("Goal" :in-theory (enable* ihsext-inductions
                                        ihsext-recursive-redefs))))

   (defthm logext-of-logtail
     (equal (logext w (logtail n x))
            (logtail n (logext (+ (pos-fix w) (nfix n)) x)))
     :hints(("Goal" :in-theory (enable* ihsext-inductions ihsext-recursive-redefs))))

   (defthmd logtail-of-logext
     (implies (< (nfix n) (pos-fix w))
              (equal (logtail n (logext w x))
                     (logext (- (pos-fix w) (nfix n)) (logtail n x)))))

   (defthmd loghead-of-logtail
     (equal (loghead w (logtail n x))
            (logtail n (loghead (+ (nfix w) (nfix n)) x)))
     :hints(("Goal" :in-theory (enable* ihsext-inductions ihsext-recursive-redefs))))))


(define sparseint$-equal-int-width ((width posp)
                                    (offset natp)
                                    (x sparseint$-p)
                                    (y integerp))
  :returns (equal booleanp :rule-classes :type-prescription)
  :measure (sparseint$-count x)
  (b* ((width (lposfix width))
       (offset (lnfix offset))
       (y (lifix y)))
    (sparseint$-case x
      :leaf (equal (bignum-logext width (logtail offset x.val)) y)
      :concat
      (b* (((when (<= x.width offset))
            (sparseint$-equal-int-width width (- offset x.width) x.msbs y))
           (width1 (- x.width offset))
           ((when (<= width width1))
            (sparseint$-equal-int-width width offset x.lsbs y)))
        (and (sparseint$-equal-int-width
              width1 offset x.lsbs (bignum-logext width1 y))
             (sparseint$-equal-int-width
              (- width width1) 0 x.msbs (logtail width1 y))))))
  ///
  (local (in-theory (disable (:d sparseint$-equal-int-width))))

  (defret <fn>-correct
    (equal equal
           (equal (logext width (logtail offset (sparseint$-val x))) (ifix y)))
    :hints (("goal" :induct <call>
             :expand ((:free (y) <call>)))
            (and stable-under-simplificationp
                 '(:in-theory (enable equal-of-logapp-split-logext))))))

(define sparseint$-equal-int ((offset natp)
                               (x sparseint$-p)
                               (y integerp))
  :returns (equal booleanp :rule-classes :type-prescription)
  :measure (sparseint$-count x)
  (b* ((y (lifix y))
       (offset (lnfix offset)))
    (sparseint$-case x
      :leaf (equal (logtail offset x.val) y)
      :concat
      (b* (((when (<= x.width offset))
            (sparseint$-equal-int (- offset x.width) x.msbs y))
           (width1 (- x.width offset)))
        (and (sparseint$-equal-int-width width1 offset x.lsbs
                                       (bignum-logext width1 y))
             (sparseint$-equal-int 0 x.msbs (logtail width1 y))))))
  ///

  (defret <fn>-correct
    (equal equal
           (equal (logtail offset (sparseint$-val x)) (ifix y)))
    :hints (("goal" :induct <call>
             :expand ((:free (y) <call>)))
            (and stable-under-simplificationp
                 '(:in-theory (enable equal-of-logapp-split-logext))))))


(define sparseint$-equal-width ((width posp)
                               (x sparseint$-p)
                               (y-offset natp)
                               (y sparseint$-p))
  :returns (equal booleanp :rule-classes :type-prescription)
  :measure (+ (sparseint$-count x) (sparseint$-count y))
  (b* ((width (lposfix width))
       (y-offset (lnfix y-offset)))
    (sparseint$-case x
      :leaf
      (sparseint$-case y
        :leaf (equal (bignum-logext width x.val)
                     (bignum-logext width (logtail y-offset y.val)))
        :concat (sparseint$-equal-int-width width y-offset y (bignum-logext width x.val)))
      :concat
      (sparseint$-case y
        :leaf (sparseint$-equal-int-width width 0 x (bignum-logext width (logtail y-offset y.val)))
        :concat
        (b* (((when (<= width x.width))
              (sparseint$-equal-width width x.lsbs y-offset y))
             ((when (<= y.width y-offset))
              (sparseint$-equal-width width x (- y-offset y.width) y.msbs))
             (y-width1 (- y.width y-offset))
             ((when (<= width y-width1))
              (sparseint$-equal-width width x y-offset y.lsbs)))
          (and (sparseint$-equal-width x.width x.lsbs y-offset y)
               (sparseint$-equal-width (- width x.width) x.msbs (+ x.width y-offset) y))))))
  ///
  

  (defret <fn>-correct
    (equal equal
           (equal (logext width (sparseint$-val x))
                  (logext width (logtail y-offset (sparseint$-val y)))))
    :hints (("goal" :induct <call>
             :do-not-induct t
             :expand ((:free (y) <call>))
             :in-theory (enable equal-of-logapp-split-logext
                                logtail-of-logapp-split)))))

(define sparseint$-equal-offset ((x sparseint$-p)
                                 (y-offset natp)
                                 (y sparseint$-p))
  :returns (equal booleanp :rule-classes :type-prescription)
  :measure (+ (sparseint$-count x) (sparseint$-count y))
  (b* ((y-offset (lnfix y-offset)))
    (sparseint$-case x
      :leaf
      (sparseint$-case y
        :leaf (equal x.val
                     (logtail y-offset y.val))
        :concat (sparseint$-equal-int y-offset y x.val))
      :concat
      (sparseint$-case y
        :leaf (sparseint$-equal-int 0 x (logtail y-offset y.val))
        :concat
        (b* (((when (<= y.width y-offset))
              (sparseint$-equal-offset x (- y-offset y.width) y.msbs)))
          (and (sparseint$-equal-width x.width x.lsbs y-offset y)
               (sparseint$-equal-offset x.msbs (+ x.width y-offset) y))))))
  ///
  

  (defret <fn>-correct
    (equal equal
           (equal (sparseint$-val x)
                  (logtail y-offset (sparseint$-val y))))
    :hints (("goal" :induct <call>
             :do-not-induct t
             :expand ((:free (y) <call>))
             :in-theory (enable equal-of-logapp-split-logext
                                logtail-of-logapp-split)))))



(define sparseint$-equal ((x sparseint$-p)
                          (y sparseint$-p))
  :returns (equal booleanp :rule-classes :type-prescription)
  :inline t
  (sparseint$-equal-offset x 0 y)
  ///
  (defret <fn>-correct
    (equal equal
           (equal (sparseint$-val x)
                  (sparseint$-val y)))))

(define sparseint-equal ((x sparseint-p)
                         (y sparseint-p))
  :parents (sparseint)
  :short "Check equality of the integer values of two sparseints"
  :returns (equal booleanp :rule-classes :type-prescription)
  :inline t
  (sparseint$-equal (sparseint-fix x) (sparseint-fix y))
  ///
  (defret <fn>-correct
    (equal equal
           (equal (sparseint-val x)
                  (sparseint-val y)))
    :hints(("Goal" :in-theory (enable sparseint-val))))

  (defequiv sparseint-equal))


(define binary-bitop ((op integerp :type (unsigned-byte 4))
                      (x integerp)
                      (y integerp))
  :returns (binary integerp :rule-classes :type-prescription)
  :prepwork ((local (in-theory (e/d (loghead-identity)
                                    (unsigned-byte-p)))))
  (b* ((op (mbe :logic (loghead 4 op) :exec op)))
    (case op
      (#b0000 0)
      (#b0001 (lognor x y))
      (#b0010 (logandc2 x y))
      (#b0011 (lognot y))
      (#b0100 (logandc1 x y))
      (#b0101 (lognot x))
      (#b0110 (logxor x y))
      (#b0111 (lognand x y))
      (#b1000 (logand x y))
      (#b1001 (logeqv x y))
      (#b1010 (lifix x))
      (#b1011 (logorc2 x y))
      (#b1100 (lifix y))
      (#b1101 (logorc1 x y))
      (#b1110 (logior x y))
      (t      -1)))
  ///
  (defret binary-bitop-correct
    (equal (logbitp n binary)
           (logbitp (+ (logbit n x)
                       (* 2 (logbit n y)))
                    op))
    :hints(("Goal" :expand ((:free (op) (loghead 4 op))
                            (:free (op) (loghead 3 op))
                            (:free (op) (loghead 2 op))
                            (:free (op) (loghead 1 op))
                            (:free (op) (loghead 0 op))
                            (:free (op) (logbitp 3 op))
                            (:free (op) (logbitp 2 op))
                            (:free (op) (logbitp 1 op))
                            (:free (op) (logbitp 0 op)))
            :in-theory (enable bool->bit))))

  (defret logext-of-<fn>
    (equal (logext n binary)
           (binary-bitop op (logext n x) (logext n y)))
    :hints(("Goal" :in-theory (e/d (logext-of-logand logext-of-logior)
                                   (logand-of-logext logior-of-logext)))))

  (defret logtail-of-<fn>
    (equal (logtail n binary)
           (binary-bitop op (logtail n x) (logtail n y)))
    :hints(("Goal" :in-theory (e/d (logtail-of-logand logtail-of-logior)))))

  (defret open-binary-bitop
    (implies (syntaxp (quotep op))
             (equal binary
                    (b* ((op (mbe :logic (loghead 4 op) :exec op)))
                      (case op
                        (#b0000 0)
                        (#b0001 (lognor x y))
                        (#b0010 (logandc2 x y))
                        (#b0011 (lognot y))
                        (#b0100 (logandc1 x y))
                        (#b0101 (lognot x))
                        (#b0110 (logxor x y))
                        (#b0111 (lognand x y))
                        (#b1000 (logand x y))
                        (#b1001 (logeqv x y))
                        (#b1010 (lifix x))
                        (#b1011 (logorc2 x y))
                        (#b1100 (lifix y))
                        (#b1101 (logorc1 x y))
                        (#b1110 (logior x y))
                        (t      -1)))))))

(define sparseint$-bitnot ((x sparseint$-p))
  :returns (bitnot sparseint$-p)
  :measure (sparseint$-count x)
  :verify-guards nil
  (sparseint$-case x
    :leaf (sparseint$-leaf (lognot x.val))
    :concat (change-sparseint$-concat x
                                      :lsbs (sparseint$-bitnot x.lsbs)
                                      :msbs (sparseint$-bitnot x.msbs)))
  ///
  (verify-guards sparseint$-bitnot)

  (defret sparseint$-height-of-<fn>
    (equal (sparseint$-height bitnot)
           (sparseint$-height x))
    :hints(("Goal" :in-theory (enable sparseint$-height-when-concat))))

  (defret sparseint$-height-correct-of-<fn>
    (implies (sparseint$-height-correctp x)
             (sparseint$-height-correctp bitnot))
    :hints (("goal" :expand (<call>
                             (sparseint$-height-correctp x)
                             (:free (width lsbs lsbs-taller msbs msbs-taller)
                              (sparseint$-height-correctp
                               (sparseint$-concat width lsbs lsbs-taller msbs msbs-taller))))
             
             :induct <call>)))

  (local (defthm lognot-of-logapp
           (equal (lognot (logapp w a b))
                  (logapp w (lognot a) (lognot b)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)
                   :induct (logapp w a b)))))

  (defret sparseint$-val-of-<fn>
    (equal (sparseint$-val bitnot)
           (lognot (sparseint$-val x)))))

(define sparseint-bitnot ((x sparseint-p))
  :parents (sparseint)
  :short "Bitwise negation of a sparseint"
  :returns (bitnot sparseint-p)
  :prepwork ((local (in-theory (enable sparseint-p))))
  :inline t
  (sparseint$-bitnot (sparseint-fix x))
  ///
  (defret sparseint-val-of-<fn>
    (equal (sparseint-val bitnot)
           (lognot (sparseint-val x)))
    :hints(("Goal" :in-theory (enable sparseint-val)))))



(define unary-bitop ((op integerp :type (unsigned-byte 2))
                     (x integerp))
  :returns (unary integerp :rule-classes :type-prescription)
  :prepwork ((local (in-theory (e/d (loghead-identity)
                                    (unsigned-byte-p)))))
  (b* ((op (mbe :logic (loghead 2 op) :exec op)))
    (case op
      (#b00 0)
      (#b01 (lognot x))
      (#b10 (lifix x))
      (t    -1)))
  ///
  (defret unary-bitop-correct
    (equal (logbitp n unary)
           (logbitp (logbit n x) op))
    :hints(("Goal" :expand ((:free (op) (loghead 2 op))
                            (:free (op) (loghead 1 op))
                            (:free (op) (loghead 0 op))
                            (:free (op) (logbitp 1 op))
                            (:free (op) (logbitp 0 op)))
            :in-theory (enable bool->bit))))

  (defret logext-of-<fn>
    (equal (logext n unary)
           (unary-bitop op (logext n x)))
    :hints(("Goal" :in-theory (e/d (logext-of-logand logext-of-logior)
                                   (logand-of-logext logior-of-logext)))))

  (defret logtail-of-<fn>
    (equal (logtail n unary)
           (unary-bitop op (logtail n x)))
    :hints(("Goal" :in-theory (e/d (logtail-of-logand logtail-of-logior)))))

  (defret open-unary-bitop
    (implies (syntaxp (quotep op))
             (equal unary
                    (b* ((op (mbe :logic (loghead 2 op) :exec op)))
                      (case op
                        (#b00 0)
                        (#b01 (lognot x))
                        (#b10 (lifix x))
                        (t    -1)))))))

(define binary-bitop-cofactor2 ((op integerp :type (unsigned-byte 4))
                                (bit bitp)) ;; positive or negative cofactor by the second variable
  :returns (unary-op integerp :rule-classes :type-prescription)
  (loghead 2 (logtail (* 2 (lbfix bit)) op))
  ///
  (defret width-of-binary-bitop-cofactor2
    (unsigned-byte-p 2 unary-op))

  (defret <fn>-correct
    (equal (unary-bitop unary-op x)
           (binary-bitop op x (- (bfix bit))))
    :hints(("Goal" :in-theory (enable unary-bitop binary-bitop bfix)
            :expand ((:free (op) (loghead 4 op))
                     (:free (op) (loghead 3 op))
                     (:free (op) (loghead 2 op))
                     (:free (op) (loghead 1 op))
                     (:free (op) (loghead 0 op))
                     (:free (op) (logbitp 3 op))
                     (:free (op) (logbitp 2 op))
                     (:free (op) (logbitp 1 op))
                     (:free (op) (logbitp 0 op)))))))

(define binary-bitop-cofactor1 ((op integerp :type (unsigned-byte 4))
                                (bit bitp)) ;; positive or negative cofactor by the second variable
  :returns (unary-op integerp :rule-classes :type-prescription)
  (logior (logbit (lbfix bit) op)
          (ash (logbit (+ 2 (lbfix bit)) op) 1))
  ///
  (defret width-of-binary-bitop-cofactor1
    (unsigned-byte-p 2 unary-op))

  (defret <fn>-correct
    (equal (unary-bitop unary-op x)
           (binary-bitop op (- (bfix bit)) x))
    :hints(("Goal" :in-theory (enable unary-bitop binary-bitop bfix)
            :expand ((:free (op) (loghead 4 op))
                     (:free (op) (loghead 3 op))
                     (:free (op) (loghead 2 op))
                     (:free (op) (loghead 1 op))
                     (:free (op) (loghead 0 op))
                     (:free (op) (logbitp 3 op))
                     (:free (op) (logbitp 2 op))
                     (:free (op) (logbitp 1 op))
                     (:free (op) (logbitp 0 op)))))))



(define binary-bitop-swap ((op integerp :type (unsigned-byte 4)))
  :returns (swap integerp :rule-classes :type-prescription)
  :prepwork ((local (in-theory (e/d (loghead-identity)
                                    (unsigned-byte-p)))))
  (b* ((op (mbe :logic (loghead 4 op)
                :exec op))
       (same #b1001) ;; (logeqv #b1010 #b1100)
       (x&~y #b0010)
       (y&~x #b0100))
    (logior (logand same op)
            (ash (logand x&~y op) 1)
            (ash (logand y&~x op) -1)))
  ///
  (defret unsigned-byte-p-of-binary-bitop-swap
    (unsigned-byte-p 4 swap))
  (defthm binary-bitop-swap-correct
    (equal (binary-bitop (binary-bitop-swap op) x y)
           (binary-bitop op y x))
    :hints(("Goal" :expand ((:free (op) (loghead 4 op))
                            (:free (op) (loghead 3 op))
                            (:free (op) (loghead 2 op))
                            (:free (op) (loghead 1 op))
                            (:free (op) (loghead 0 op)))
            :in-theory (enable binary-bitop)))))


(define sparseint$-unary-bitop ((op integerp :type (unsigned-byte 2))
                                (x sparseint$-p)
                                (x.height natp))
  :guard (and (sparseint$-height-correctp x)
              (equal x.height (sparseint$-height x)))
  :returns (mv (res sparseint$-p)
               (height (equal height (sparseint$-height res))))
  :guard-hints (("goal" :in-theory (enable loghead-identity)))

  (b* ((x.height (mbe :logic (sparseint$-height x) :exec x.height))
       (op (mbe :logic (loghead 2 op) :exec op)))
    (case op
      (#b00 (mv (sparseint$-leaf 0) 0))
      (#b01 (mv (sparseint$-bitnot x) x.height))
      (#b10 (mv (sparseint$-fix x) x.height))
      (t (mv (sparseint$-leaf -1) 0))))
  ///
  (defret <fn>-height-correctp
    (implies (sparseint$-height-correctp x)
             (sparseint$-height-correctp res)))

  (defret <fn>-correct
    (equal (sparseint$-val res)
           (unary-bitop op (sparseint$-val x)))
    :hints(("Goal" :in-theory (enable unary-bitop)))))

(define sparseint$-unary-bittest-offset ((op integerp :type (unsigned-byte 2))
                                         (offset natp)
                                         (x sparseint$-p))
  :returns (test booleanp :rule-classes :type-prescription)
  :guard-hints (("goal" :in-theory (enable loghead-identity)))

  (b* ((op (mbe :logic (loghead 2 op) :exec op)))
    (case op
      (#b00 nil)
      (#b01 (not (sparseint$-equal-int offset x -1)))
      (#b10 (not (sparseint$-equal-int offset x -0)))
      (t    t)))
  ///

  (defret <fn>-correct
    (equal test
           (not (equal (unary-bitop op (logtail offset (sparseint$-val x))) 0)))
    :hints(("Goal" :in-theory (enable unary-bitop)))))

(define sparseint$-unary-bittest-width ((op integerp :type (unsigned-byte 2))
                                        (width posp)
                                        (offset natp)
                                        (x sparseint$-p))
  :returns (test booleanp :rule-classes :type-prescription)
  :guard-hints (("goal" :in-theory (enable loghead-identity)))

  (b* ((op (mbe :logic (loghead 2 op) :exec op)))
    (case op
      (#b00 nil)
      (#b01 (not (sparseint$-equal-int-width width offset x -1)))
      (#b10 (not (sparseint$-equal-int-width width offset x -0)))
      (t    t)))
  ///

  (defret <fn>-correct
    (equal test
           (not (equal (unary-bitop op (logext width (logtail offset (sparseint$-val x)))) 0)))
    :hints(("Goal" :in-theory (enable unary-bitop)))))

(define sparseint$-unary-bittest ((op integerp :type (unsigned-byte 2))
                                  (x sparseint$-p))
  :returns (test booleanp :rule-classes :type-prescription)
  :guard-hints (("goal" :in-theory (enable loghead-identity)))
  (sparseint$-unary-bittest-offset op 0 x)
  ///

  (defret <fn>-correct
    (equal test
           (not (equal (unary-bitop op (sparseint$-val x)) 0)))
    :hints(("Goal" :in-theory (enable unary-bitop)))))



(define sparseint$-binary-bitop-int-width ((op integerp :type (unsigned-byte 4))
                                           (width posp)
                                           (offset natp)
                                           (x sparseint$-p)
                                           (x.height natp)
                                           (y integerp))
  :guard (and (sparseint$-height-correctp x)
              (equal x.height (sparseint$-height x)))
  :returns (mv (binary-res sparseint$-p)
               (height (equal height (sparseint$-height binary-res))))
  :verify-guards nil
  :measure (sparseint$-count x)
  (b* ((width (lposfix width))
       (offset (lnfix offset))
       (y (lifix y))
       (x.height (mbe :logic (sparseint$-height x) :exec x.height))
       ((when (or (eql y 0) (eql y -1)))
        (b* ((cofactor (binary-bitop-cofactor2 op (- y))))
          (mbe :logic (b* (((mv shift shift-height) (sparseint$-rightshift-rec offset x x.height))
                           ((mv ext ext-height) (sparseint$-sign-ext width shift shift-height)))
                        (sparseint$-unary-bitop cofactor ext ext-height))
               :exec (b* (((when (eql cofactor #b00)) (mv (sparseint$-leaf 0) 0))
                          ((when (eql cofactor #b11)) (mv (sparseint$-leaf -1) 0))
                          ((mv shift shift-height) (sparseint$-rightshift-rec offset x x.height))
                          ((mv ext ext-height) (sparseint$-sign-ext width shift shift-height)))
                        (sparseint$-unary-bitop cofactor ext ext-height))))))
             
    (sparseint$-case x
      :leaf (mv (sparseint$-leaf (bignum-logext width (binary-bitop op (logtail offset x.val) y))) 0)
      :concat
      (b* ((x.msbs.height (mbe :logic (sparseint$-height x.msbs)
                               :exec (- x.height (if x.lsbs-taller 2 1))))
           ((when (<= x.width offset))
            (sparseint$-binary-bitop-int-width op width (- offset x.width) x.msbs x.msbs.height y))
           (width1 (- x.width offset))
           (x.lsbs.height (mbe :logic (sparseint$-height x.lsbs)
                               :exec (- x.height (if x.msbs-taller 2 1))))
           ((when (<= width width1))
            (sparseint$-binary-bitop-int-width op width offset x.lsbs x.lsbs.height y))
           ((mv lsbs-and lsbs-and-height)
            (sparseint$-binary-bitop-int-width op width1 offset x.lsbs x.lsbs.height
                                       (bignum-logext width1 y)))
           ((mv msbs-and msbs-and-height)
            (sparseint$-binary-bitop-int-width op (- width width1) 0 x.msbs x.msbs.height (logtail width1 y))))
        (sparseint$-concatenate-rebalance width1 lsbs-and lsbs-and-height msbs-and msbs-and-height))))
  ///
  (local (in-theory (disable (:d sparseint$-binary-bitop-int-width))))

  (defret sparseint$-height-correctp-of-<fn>
    (implies (sparseint$-height-correctp x)
             (sparseint$-height-correctp binary-res))
    :hints (("goal" :induct <call>
             :expand ((:free (y) <call>)))))

  (verify-guards sparseint$-binary-bitop-int-width
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (x xh) (sparseint$-unary-bitop #b00 x xh))
                            (:free (x xh) (sparseint$-unary-bitop #b11 x xh)))))))

  (defret sparseint$-val-of-<fn>
    (equal (sparseint$-val binary-res)
           (logext (pos-fix width) (binary-bitop op (logtail offset (sparseint$-val x)) y)))
    :hints (("goal" :induct <call>
             :expand ((:free (y) <call>)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (loghead-of-logtail
                                    equal-of-logapp-split-logext)))))))

(define sparseint$-binary-bitop-int ((op integerp :type (unsigned-byte 4))
                                     (offset natp)
                                     (x sparseint$-p)
                                     (x.height natp)
                                     (y integerp))
  :guard (and (sparseint$-height-correctp x)
              (equal x.height (sparseint$-height x)))
  :returns (mv (binary-res sparseint$-p)
               (height (equal height (sparseint$-height binary-res))))
  :verify-guards nil
  :measure (sparseint$-count x)
  (b* ((y (lifix y))
       (offset (lnfix offset))
       (x.height (mbe :logic (sparseint$-height x) :exec x.height))
       ((when (or (eql y 0) (eql y -1)))
        (b* ((cofactor (binary-bitop-cofactor2 op (- y))))
          (mbe :logic (b* (((mv shift shift-height) (sparseint$-rightshift-rec offset x x.height)))
                        (sparseint$-unary-bitop cofactor shift shift-height))
               :exec (b* (((when (eql cofactor #b00)) (mv (sparseint$-leaf 0) 0))
                          ((when (eql cofactor #b11)) (mv (sparseint$-leaf -1) 0))
                          ((mv shift shift-height) (sparseint$-rightshift-rec offset x x.height)))
                        (sparseint$-unary-bitop cofactor shift shift-height))))))
    (sparseint$-case x
      :leaf (mv (sparseint$-leaf (binary-bitop op (logtail offset x.val) y)) 0)
      :concat
      (b* ((x.msbs.height (mbe :logic (sparseint$-height x.msbs)
                               :exec (- x.height (if x.lsbs-taller 2 1))))
           ((when (<= x.width offset))
            (sparseint$-binary-bitop-int op (- offset x.width) x.msbs x.msbs.height y))
           (width1 (- x.width offset))
           (x.lsbs.height (mbe :logic (sparseint$-height x.lsbs)
                               :exec (- x.height (if x.msbs-taller 2 1))))
           ((mv lsbs-and lsbs-and-height)
            (sparseint$-binary-bitop-int-width op width1 offset x.lsbs x.lsbs.height
                                       (bignum-logext width1 y)))
           (x.msbs.height (mbe :logic (sparseint$-height x.msbs)
                               :exec (- x.height (if x.lsbs-taller 2 1))))
           ((mv msbs-and msbs-and-height)
            (sparseint$-binary-bitop-int op 0 x.msbs x.msbs.height (logtail width1 y))))
        (sparseint$-concatenate-rebalance width1 lsbs-and lsbs-and-height msbs-and msbs-and-height))))
  ///

  (local (in-theory (disable (:d sparseint$-binary-bitop-int-width))))

  (defret sparseint$-height-correctp-of-<fn>
    (implies (sparseint$-height-correctp x)
             (sparseint$-height-correctp binary-res))
    :hints (("goal" :induct <call>
             :expand ((:free (y) <call>)))))

  (verify-guards sparseint$-binary-bitop-int
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (x xh) (sparseint$-unary-bitop #b00 x xh))
                            (:free (x xh) (sparseint$-unary-bitop #b11 x xh)))))))

  (defret sparseint$-val-of-<fn>
    (equal (sparseint$-val binary-res)
           (binary-bitop op (logtail offset (sparseint$-val x)) y))
    :hints (("goal" :induct <call>
             :expand ((:free (y) <call>)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (loghead-of-logtail
                                    equal-of-logapp-split-logext)))))))


(define sparseint$-binary-bitop-width ((op integerp :type (unsigned-byte 4))
                                       (width posp)
                                       (x sparseint$-p)
                                       (x.height natp)
                                       (y-offset natp)
                                       (y sparseint$-p)
                                       (y.height natp))
  :guard (and (sparseint$-height-correctp x)
              (equal x.height (sparseint$-height x))
              (sparseint$-height-correctp y)
              (equal y.height (sparseint$-height y)))
  :returns (mv (binary-res sparseint$-p)
               (height (equal height (sparseint$-height binary-res))))
  :verify-guards nil
  :measure (+ (sparseint$-count x) (sparseint$-count y))
  (b* ((x.height (mbe :logic (sparseint$-height x) :exec x.height))
       (y.height (mbe :logic (sparseint$-height y) :exec y.height))
       (width (lposfix width))
       (y-offset (lnfix y-offset)))
    (sparseint$-case x
      :leaf
      (sparseint$-case y
        :leaf (mv (sparseint$-leaf (binary-bitop op (bignum-logext width x.val)
                                                 (bignum-logext width (logtail y-offset y.val))))
                  0)
        :concat (sparseint$-binary-bitop-int-width
                 (binary-bitop-swap op)
                 width y-offset y y.height (bignum-logext width x.val)))
      :concat
      (sparseint$-case y
        :leaf (sparseint$-binary-bitop-int-width op width 0 x x.height (bignum-logext width (logtail y-offset y.val)))
        :concat
        (b* ((x.lsbs.height (mbe :logic (sparseint$-height x.lsbs)
                                 :exec (- x.height (if x.msbs-taller 2 1))))
             ((when (<= width x.width))
              (sparseint$-binary-bitop-width op width x.lsbs x.lsbs.height y-offset y y.height))
             (y.msbs.height (mbe :logic (sparseint$-height y.msbs)
                                 :exec (- y.height (if y.lsbs-taller 2 1))))
             ((when (<= y.width y-offset))
              (sparseint$-binary-bitop-width op width x x.height (- y-offset y.width) y.msbs y.msbs.height))
             (y-width1 (- y.width y-offset))
             (y.lsbs.height (mbe :logic (sparseint$-height y.lsbs)
                                 :exec (- y.height (if y.msbs-taller 2 1))))
             ((when (<= width y-width1))
              (sparseint$-binary-bitop-width op width x x.height y-offset y.lsbs y.lsbs.height))

             ((mv lsbs-and lsbs-and.height)
              (sparseint$-binary-bitop-width op x.width x.lsbs x.lsbs.height
                                     y-offset y y.height))

             (x.msbs.height (mbe :logic (sparseint$-height x.msbs)
                                 :exec (- x.height (if x.lsbs-taller 2 1))))
             ((mv msbs-and msbs-and.height)
              (sparseint$-binary-bitop-width op (- width x.width)
                                     x.msbs x.msbs.height
                                     (+ x.width y-offset)
                                     y y.height)))
          (sparseint$-concatenate-rebalance
           x.width lsbs-and lsbs-and.height msbs-and msbs-and.height)))))
  ///
  (local (in-theory (disable (:d sparseint$-binary-bitop-int-width))))

  (defret sparseint$-height-correctp-of-<fn>
    (implies (and (sparseint$-height-correctp x)
                  (sparseint$-height-correctp y))
             (sparseint$-height-correctp binary-res))
    :hints (("goal" :induct <call>
             :expand ((:free (y) <call>)))))

  (verify-guards sparseint$-binary-bitop-width)

  ;; (local (defthm logapp-when-loghead-equal
  ;;          (implies (and (equal (loghead w x) z)
  ;;                        (syntaxp (not (find-atom 'sparseint$-binary-bitop-int-width z))))
  ;;                   (equal (logapp w x y) (logapp w z y)))
  ;;          :hints(("Goal" :in-theory (enable logapp)))))

  (local (defthm logapp-of-equal-logext
           (implies (equal x (logext w z))
                    (equal (logapp w x y)
                           (logapp w z y)))
           :hints(("Goal" :in-theory (enable logapp)))))

  (local (defthm logapp-of-equal-logext-2
           (implies (equal y (logext w2 z))
                    (equal (logapp w x y)
                           (logext (+ (pos-fix w2) (nfix w))(logapp w x z))))))

  (local (in-theory (disable logext-of-logapp-split)))

  (local (defthmd logext-of-equal-to-binary-bitop
           (implies (equal x (binary-bitop op a b))
                    (equal (logext n x)
                           (binary-bitop op (logext n a) (logext n b))))))

  (defret sparseint$-val-of-<fn>
    (equal (sparseint$-val binary-res)
           (logext (pos-fix width)
                   (binary-bitop op (sparseint$-val x) (logtail y-offset (sparseint$-val y)))))
    :hints (("goal" :induct <call>
             :expand ((:free (y) <call>)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (logext-of-logapp-split)
                                   (logapp-of-equal-logext-2))))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (loghead-of-logtail
                                    logtail-of-logapp-split
                                    equal-of-logapp-split-logext
                                    logext-of-logapp-split
                                    logext-of-equal-to-binary-bitop
                                    )
                                   (logtail-of-loghead
                                    logapp-of-equal-logext-2)))))))



(define sparseint$-binary-bitop-offset ((op integerp :type (unsigned-byte 4))
                                        (x sparseint$-p)
                                        (x.height natp)
                                        (y-offset natp)
                                        (y sparseint$-p)
                                        (y.height natp))
  :guard (and (sparseint$-height-correctp x)
              (equal x.height (sparseint$-height x))
              (sparseint$-height-correctp y)
              (equal y.height (sparseint$-height y)))
  :returns (mv (binary-res sparseint$-p)
               (height (equal height (sparseint$-height binary-res))))
  :verify-guards nil
  :measure (+ (sparseint$-count x) (sparseint$-count y))
  (b* ((x.height (mbe :logic (sparseint$-height x) :exec x.height))
       (y.height (mbe :logic (sparseint$-height y) :exec y.height))
       (y-offset (lnfix y-offset)))
    (sparseint$-case x
      :leaf
      (sparseint$-case y
        :leaf (mv (sparseint$-leaf (binary-bitop op x.val (logtail y-offset y.val)))
                  0)
        :concat (sparseint$-binary-bitop-int (binary-bitop-swap op) y-offset y y.height x.val))
      :concat
      (sparseint$-case y
        :leaf (sparseint$-binary-bitop-int op 0 x x.height (logtail y-offset y.val))
        :concat
        (b* ((y.msbs.height (mbe :logic (sparseint$-height y.msbs)
                                 :exec (- y.height (if y.lsbs-taller 2 1))))
             ((when (<= y.width y-offset))
              (sparseint$-binary-bitop-offset op x x.height (- y-offset y.width) y.msbs y.msbs.height))
             (x.lsbs.height (mbe :logic (sparseint$-height x.lsbs)
                                 :exec (- x.height (if x.msbs-taller 2 1))))

             ((mv lsbs-and lsbs-and.height)
              (sparseint$-binary-bitop-width op x.width x.lsbs x.lsbs.height
                                       y-offset y y.height))

             (x.msbs.height (mbe :logic (sparseint$-height x.msbs)
                                 :exec (- x.height (if x.lsbs-taller 2 1))))
             ((mv msbs-and msbs-and.height)
              (sparseint$-binary-bitop-offset op x.msbs x.msbs.height
                                        (+ x.width y-offset)
                                        y y.height)))
          (sparseint$-concatenate-rebalance
           x.width lsbs-and lsbs-and.height msbs-and msbs-and.height)))))
  ///
  (local (in-theory (disable (:d sparseint$-binary-bitop-int-width))))

  (defret sparseint$-height-correctp-of-<fn>
    (implies (and (sparseint$-height-correctp x)
                  (sparseint$-height-correctp y))
             (sparseint$-height-correctp binary-res))
    :hints (("goal" :induct <call>
             :expand ((:free (y) <call>)))))

  (verify-guards sparseint$-binary-bitop-offset)

  ;; (local (defthm logapp-when-loghead-equal
  ;;          (implies (and (equal (loghead w x) z)
  ;;                        (syntaxp (not (find-atom 'sparseint$-binary-bitop-int-width z))))
  ;;                   (equal (logapp w x y) (logapp w z y)))
  ;;          :hints(("Goal" :in-theory (enable logapp)))))

  (local (defthm logapp-of-equal-logext
           (implies (equal x (logext w z))
                    (equal (logapp w x y)
                           (logapp w z y)))
           :hints(("Goal" :in-theory (enable logapp)))))

  (local (defthm logapp-of-equal-logext-2
           (implies (equal y (logext w2 z))
                    (equal (logapp w x y)
                           (logext (+ (pos-fix w2) (nfix w))(logapp w x z))))))

  (local (in-theory (disable logext-of-logapp-split)))

  (defret sparseint$-val-of-<fn>
    (equal (sparseint$-val binary-res)
           (binary-bitop op (sparseint$-val x) (logtail y-offset (sparseint$-val y))))
    :hints (("goal" :induct <call>
             :expand ((:free (y) <call>)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (logext-of-logapp-split)
                                   (logapp-of-equal-logext-2))))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (loghead-of-logtail
                                    logtail-of-logapp-split
                                    equal-of-logapp-split-logext
                                    logext-of-logapp-split
                                    )
                                   (logtail-of-loghead
                                    logapp-of-equal-logext-2)))))))


(define sparseint$-binary-bitop ((op integerp :type (unsigned-byte 4))
                                 (x sparseint$-p)
                                 (y sparseint$-p))
  :guard (and (sparseint$-height-correctp x)
              (sparseint$-height-correctp y))
  :returns (binary-res sparseint$-p)
  :inline t
  (b* (((mv binary-res ?height)
        (sparseint$-binary-bitop-offset op x (sparseint$-height x)
                                        0
                                        y (sparseint$-height y))))
    binary-res)
  ///
  (defret sparseint$-height-correctp-of-<fn>
    (implies (and (sparseint$-height-correctp x)
                  (sparseint$-height-correctp y))
             (sparseint$-height-correctp binary-res)))

  (defret sparseint$-val-of-<fn>
    (equal (sparseint$-val binary-res)
           (binary-bitop op (sparseint$-val x) (sparseint$-val y)))))

(define sparseint-binary-bitop ((op integerp :type (unsigned-byte 4))
                                (x sparseint-p)
                                (y sparseint-p))
  :parents (sparseint)
  :short "Apply a binary bitwise operation (represented as a 4-bit truth table) to two sparseints."
  :returns (binary-res sparseint-p)
  :prepwork ((local (in-theory (enable sparseint-p))))
  :inline t
  (sparseint$-binary-bitop op (sparseint-fix x) (sparseint-fix y))
  ///
  (defret sparseint-val-of-<fn>
    (equal (sparseint-val binary-res)
           (binary-bitop op (sparseint-val x) (sparseint-val y)))
    :hints(("Goal" :in-theory (enable sparseint-val)))))






(define binary-bittest ((op integerp :type (unsigned-byte 4))
                        (x integerp)
                        (y integerp))
  :enabled t
  (not (eql 0 (binary-bitop op x y))))

(local (include-book "equal-by-logbitp"))

(local (defthm equal-0-of-binary-bitop-of-logapp-1
         (equal (equal 0 (binary-bitop op (logapp width x y) z))
                (and (or (zp width)
                         (equal 0 (binary-bitop op (logext width x) (logext width z))))
                     (equal 0 (binary-bitop op y (logtail width z)))))
         :hints ((logbitp-reasoning))))

(define sparseint$-binary-bittest-int-width ((op integerp :type (unsigned-byte 4))
                                           (width posp)
                                           (offset natp)
                                           (x sparseint$-p)
                                           (y integerp))
  :returns (test booleanp :rule-classes :type-prescription)
;;   :verify-guards nil
  :measure (sparseint$-count x)
  (b* ((width (lposfix width))
       (offset (lnfix offset))
       (y (lifix y))
       ((when (or (eql y 0) (eql y -1)))
        (b* ((cofactor (binary-bitop-cofactor2 op (- y))))
          (sparseint$-unary-bittest-width cofactor width offset x))))
             
    (sparseint$-case x
      :leaf (binary-bittest op (bignum-logext width (logtail offset x.val))
                            (bignum-logext width y))
      :concat
      (b* (((when (<= x.width offset))
            (sparseint$-binary-bittest-int-width op width (- offset x.width) x.msbs y))
           (width1 (- x.width offset))
           ((when (<= width width1))
            (sparseint$-binary-bittest-int-width op width offset x.lsbs y)))
        (or (sparseint$-binary-bittest-int-width op width1 offset x.lsbs (bignum-logext width1 y))
            (sparseint$-binary-bittest-int-width op (- width width1) 0 x.msbs (logtail width1 y))))))
  ///
  (local (in-theory (disable (:d sparseint$-binary-bittest-int-width))))

  (defret sparseint$-val-of-<fn>
    (equal test
           (binary-bittest op (logext width (logtail offset (sparseint$-val x)))
                           (logext width y)))
    :hints (("goal" :induct <call>
             :expand ((:free (y) <call>)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (loghead-of-logtail
                                    equal-of-logapp-split-logext)))))))

(define sparseint$-binary-bittest-int ((op integerp :type (unsigned-byte 4))
                                     (offset natp)
                                     (x sparseint$-p)
                                     (y integerp))
  :returns (test booleanp :rule-classes :type-prescription)
  ;; :verify-guards nil
  :measure (sparseint$-count x)
  (b* ((y (lifix y))
       (offset (lnfix offset))
       ((when (or (eql y 0) (eql y -1)))
        (b* ((cofactor (binary-bitop-cofactor2 op (- y))))
          (sparseint$-unary-bittest-offset cofactor offset x))))
    (sparseint$-case x
      :leaf (binary-bittest op (logtail offset x.val) y)
      :concat
      (b* (((when (<= x.width offset))
            (sparseint$-binary-bittest-int op (- offset x.width) x.msbs y))
           (width1 (- x.width offset)))
        (or (sparseint$-binary-bittest-int-width op width1 offset x.lsbs (bignum-logext width1 y))
            (sparseint$-binary-bittest-int op 0 x.msbs (logtail width1 y))))))
  ///

  (local (in-theory (disable (:d sparseint$-binary-bittest-int-width))))

  (defret sparseint$-val-of-<fn>
    (equal test
           (binary-bittest op (logtail offset (sparseint$-val x)) y))
    :hints (("goal" :induct <call>
             :expand ((:free (y) <call>)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (loghead-of-logtail
                                    equal-of-logapp-split-logext)))))))


(define sparseint$-binary-bittest-width ((op integerp :type (unsigned-byte 4))
                                       (width posp)
                                       (x sparseint$-p)
                                       (y-offset natp)
                                       (y sparseint$-p))
  :returns (test booleanp :rule-classes :type-prescription)
  ;; :verify-guards nil
  :measure (+ (sparseint$-count x) (sparseint$-count y))
  (b* ((width (lposfix width))
       (y-offset (lnfix y-offset)))
    (sparseint$-case x
      :leaf
      (sparseint$-case y
        :leaf (binary-bittest op (bignum-logext width x.val)
                              (bignum-logext width (logtail y-offset y.val)))
        :concat (sparseint$-binary-bittest-int-width
                 (binary-bitop-swap op)
                 width y-offset y (bignum-logext width x.val)))
      :concat
      (sparseint$-case y
        :leaf (sparseint$-binary-bittest-int-width op width 0 x (bignum-logext width (logtail y-offset y.val)))
        :concat
        (b* (((when (<= width x.width))
              (sparseint$-binary-bittest-width op width x.lsbs y-offset y))
             ((when (<= y.width y-offset))
              (sparseint$-binary-bittest-width op width x (- y-offset y.width) y.msbs))
             (y-width1 (- y.width y-offset))
             ((when (<= width y-width1))
              (sparseint$-binary-bittest-width op width x y-offset y.lsbs)))
          (or (sparseint$-binary-bittest-width op x.width x.lsbs y-offset y)
              (sparseint$-binary-bittest-width op (- width x.width) x.msbs (+ x.width y-offset) y))))))
  ///
  (local (in-theory (disable (:d sparseint$-binary-bittest-int-width))))

  ;; (local (defthm logapp-when-loghead-equal
  ;;          (implies (and (equal (loghead w x) z)
  ;;                        (syntaxp (not (find-atom 'sparseint$-binary-bittest-int-width z))))
  ;;                   (equal (logapp w x y) (logapp w z y)))
  ;;          :hints(("Goal" :in-theory (enable logapp)))))

  ;; (local (defthm logapp-of-equal-logext
  ;;          (implies (equal x (logext w z))
  ;;                   (equal (logapp w x y)
  ;;                          (logapp w z y)))
  ;;          :hints(("Goal" :in-theory (enable logapp)))))

  ;; (local (defthm logapp-of-equal-logext-2
  ;;          (implies (equal y (logext w2 z))
  ;;                   (equal (logapp w x y)
  ;;                          (logext (+ (pos-fix w2) (nfix w))(logapp w x z))))))

  (local (in-theory (disable logext-of-logapp-split)))

  ;; (local (defthmd logext-of-equal-to-binary-bittest
  ;;          (implies (equal x (binary-bittest op a b))
  ;;                   (equal (logext n x)
  ;;                          (binary-bittest op (logext n a) (logext n b))))))

  (defret sparseint$-val-of-<fn>
    (equal test
           (binary-bittest op (logext width (sparseint$-val x))
                           (logext width (logtail y-offset (sparseint$-val y)))))
    :hints (("goal" :induct <call>
             :expand ((:free (y) <call>)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (logtail-of-logapp-split
                                    logext-of-logapp-split)
                                   (logtail-of-loghead
                                    ;; logapp-of-equal-logext-2
                                    )))))))



(define sparseint$-binary-bittest-offset ((op integerp :type (unsigned-byte 4))
                                          (x sparseint$-p)
                                          (y-offset natp)
                                          (y sparseint$-p))
  :returns (test booleanp :rule-classes :type-prescription)
  :measure (+ (sparseint$-count x) (sparseint$-count y))
  (b* ((y-offset (lnfix y-offset)))
    (sparseint$-case x
      :leaf
      (sparseint$-case y
        :leaf (binary-bittest op x.val
                              (logtail y-offset y.val))
        :concat (sparseint$-binary-bittest-int (binary-bitop-swap op) y-offset y x.val))
      :concat
      (sparseint$-case y
        :leaf (sparseint$-binary-bittest-int op 0 x (logtail y-offset y.val))
        :concat
        (b* (((when (<= y.width y-offset))
              (sparseint$-binary-bittest-offset op x (- y-offset y.width) y.msbs)))
          (or (sparseint$-binary-bittest-width op x.width x.lsbs y-offset y)
              (sparseint$-binary-bittest-offset op x.msbs (+ x.width y-offset) y))))))
  ///
  (local (in-theory (disable (:d sparseint$-binary-bittest-int-width))))

  ;; (local (defthm logapp-when-loghead-equal
  ;;          (implies (and (equal (loghead w x) z)
  ;;                        (syntaxp (not (find-atom 'sparseint$-binary-bittest-int-width z))))
  ;;                   (equal (logapp w x y) (logapp w z y)))
  ;;          :hints(("Goal" :in-theory (enable logapp)))))


  (local (in-theory (disable logext-of-logapp-split)))

  (defret sparseint$-val-of-<fn>
    (equal test
           (binary-bittest op (sparseint$-val x) (logtail y-offset (sparseint$-val y))))
    :hints (("goal" :induct <call>
             :expand ((:free (y) <call>)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (logtail-of-logapp-split)
                                   (logtail-of-loghead)))))))


(define sparseint$-binary-bittest ((op integerp :type (unsigned-byte 4))
                                   (x sparseint$-p)
                                   (y sparseint$-p))
  :returns (test booleanp :rule-classes :type-prescription)
  :inline t
  (sparseint$-binary-bittest-offset op x 0 y)
  ///
  (defret sparseint$-val-of-<fn>
    (equal test
           (binary-bittest op (sparseint$-val x) (sparseint$-val y)))))

(define sparseint-binary-bittest ((op integerp :type (unsigned-byte 4))
                                  (x sparseint-p)
                                  (y sparseint-p))
  :parents (sparseint)
  :short "Test whether a binary bitwise operation (represented as a 4-bit truth
          table) on two sparseints yields a nonzero value."
  :returns (test booleanp :rule-classes :type-prescription)
  :prepwork ((local (in-theory (enable sparseint-p))))
  :inline t
  (sparseint$-binary-bittest op (sparseint-fix x) (sparseint-fix y))
  ///
  (defret sparseint-val-of-<fn>
    (equal test
           (binary-bittest op (sparseint-val x) (sparseint-val y)))
    :hints(("Goal" :in-theory (enable sparseint-val)))))

(defmacro def-sparseint-binary-bitop (name op spec)
  (b* ((sparseint-{name} (intern$ (concatenate 'string "SPARSEINT-" (symbol-name name)) "BITOPS"))
       (sparseint-test-{name} (intern$ (concatenate 'string "SPARSEINT-TEST-" (symbol-name name)) "BITOPS")))
    `(progn
       (define ,sparseint-{name} ((x sparseint-p)
                                  (y sparseint-p))
         :parents (sparseint)
         :short ,(concatenate 'string
                              "Compute the " (str::downcase-string (symbol-name spec))
                              " of two sparseints.")
         :returns (res sparseint-p :rule-classes :type-prescription)
         :inline t
         (sparseint-binary-bitop ,op x y)
         ///
         (defret <fn>-correct
           (equal (sparseint-val res)
                  (,spec (sparseint-val x) (sparseint-val y)))))

       (define ,sparseint-test-{name} ((x sparseint-p)
                                       (y sparseint-p))
         :parents (sparseint)
         :short ,(concatenate 'string
                              "Check whether the " (str::downcase-string (symbol-name spec))
                              " of two sparseints produces a nonzero value.")
         :returns (test booleanp :rule-classes :type-prescription)
         :inline t
         (sparseint-binary-bittest ,op x y)
         ///
         (defret <fn>-correct
           (equal test
                  (not (equal 0 (,spec (sparseint-val x) (sparseint-val y))))))))))

(def-sparseint-binary-bitop bitnor   #b0001 lognor)
(def-sparseint-binary-bitop bitandc2 #b0010 logandc2)
(def-sparseint-binary-bitop bitandc1 #b0100 logandc1)
(def-sparseint-binary-bitop bitxor   #b0110 logxor)
(def-sparseint-binary-bitop bitnand  #b0111 lognand)
(def-sparseint-binary-bitop bitand   #b1000 logand)
(def-sparseint-binary-bitop biteqv   #b1001 logeqv)
(def-sparseint-binary-bitop bitorc2  #b1011 logorc2)
(def-sparseint-binary-bitop bitorc1  #b1101 logorc1)
(def-sparseint-binary-bitop bitor    #b1110 logior)

(define sparseint-bitite ((test sparseint-p)
                          (then sparseint-p)
                          (else sparseint-p))
  :parents (sparseint)
  :returns (ite sparseint-p)
  :short "Compute the bitwise if-then-else of the three sparseint inputs."
  :guard-debug t
  :prepwork ((local (in-theory (enable sparseint-p)))
             (local (defthm sparseint$-height-correctp-of-sparseint-fix
                      (sparseint$-height-correctp (sparseint-fix x))
                      :hints(("Goal" :in-theory (enable sparseint-fix sparseint-p))))))
  (b* ((test (sparseint-fix test))
       (then (sparseint-fix then))
       (else (sparseint-fix else))
       (test.height (sparseint$-height test))
       ((mv test&then test&then.height)
        (sparseint$-binary-bitop-offset #b1000 test test.height
                                        0 then (sparseint$-height then)))
       ((mv ~test&else ~test&else.height)
        (sparseint$-binary-bitop-offset #b0100 test test.height
                                        0 else (sparseint$-height else)))
       ((mv if ?if.height)
        (sparseint$-binary-bitop-offset #b1110 test&then test&then.height
                                        0 ~test&else ~test&else.height)))
    if)
  ///
  (defret <fn>-correct
    (equal (sparseint-val ite)
           (logite (sparseint-val test)
                   (sparseint-val then)
                   (sparseint-val else)))
    :hints(("Goal" :in-theory (enable sparseint-val logite)))))


(define compare ((x integerp) (y integerp))
  (b* ((x (lifix x))
       (y (lifix y)))
    (cond ((eql x y) 0)
          ((< x y) -1)
          (t 1)))
  ///
  (defthm minus-of-compare
    (equal (- (compare x y))
           (compare y x))))


(local
 (defsection <-logapp
   (local (defun <-logapp-ind (width x z)
            (if (zp width)
                (list x z)
              (<-logapp-ind (1- width) (logcdr x) (logcdr z)))))

   (defthm compare-of-logcons-1
     (equal (compare (logcons a b) c)
            (b* ((msbs (compare b (logcdr c))))
              (if (equal 0 msbs)
                  (- (bfix a) (logcar c))
                msbs)))
     :hints(("Goal" :in-theory (enable compare
                                       equal-logcons-strong
                                       logcons-<-n-strong
                                       logcons->-n-strong))))

   (defthm compare-of-logcons-2
     (equal (compare c (logcons a b))
            (b* ((msbs (compare (logcdr c) b)))
              (if (equal 0 msbs)
                  (- (logcar c) (bfix a))
                msbs)))
     :hints(("Goal" :in-theory (enable compare
                                       equal-logcons-strong
                                       logcons-<-n-strong
                                       logcons->-n-strong))))

   (defthm compare-of-logapp-1
     (equal (compare (logapp width x y) z)
            (b* ((msb-compare (compare y (logtail width z))))
              (if (equal 0 msb-compare)
                  (compare (loghead width x) (loghead width z))
                msb-compare)))
     :hints (("goal" :induct (<-logapp-ind width x z)
              :expand ((logapp width x y)
                       (logtail width z)
                       (:free (x) (loghead width x))))))

   (defthmd compare-of-logapp-2
     (equal (compare z (logapp width x y))
            (b* ((msb-compare (compare (logtail width z) y)))
              (if (equal 0 msb-compare)
                  (compare (loghead width z) (loghead width x))
                msb-compare)))
     :hints (("goal" :induct (<-logapp-ind width x z)
              :expand ((logapp width x y)
                       (logtail width z)
                       (:free (x) (loghead width x))))))))



(define sparseint$-compare-int-width ((width posp)
                                      (offset natp)
                                      (x sparseint$-p)
                                      (y integerp))
  :returns (sign integerp :rule-classes :type-prescription)
  :measure (sparseint$-count x)
  (b* ((width (lposfix width))
       (offset (lnfix offset))
       (y (lifix y)))
    (sparseint$-case x
      :leaf (b* ((x (bignum-loghead width (logtail offset x.val))))
              (compare x y))
      :concat
      (b* (((when (<= x.width offset))
            (sparseint$-compare-int-width width (- offset x.width) x.msbs y))
           (width1 (- x.width offset))
           ((when (<= width width1))
            (sparseint$-compare-int-width width offset x.lsbs y))
           (msbs-compare
            (sparseint$-compare-int-width
              (- width width1) 0 x.msbs (logtail width1 y)))
           ((unless (eql msbs-compare 0)) msbs-compare))
        (sparseint$-compare-int-width
         width1 offset x.lsbs (bignum-loghead width1 y)))))
  ///
  (local (in-theory (disable (:d sparseint$-compare-int-width))))

  (defret <fn>-correct
    (b* ((xval (loghead (pos-fix width) (logtail offset (sparseint$-val x)))))
      (equal sign
             (compare xval y)))
    :hints (("goal" :induct <call>
             :expand ((:free (y) <call>)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (equal-of-logapp-split
                                    loghead-of-logapp-split
                                    loghead-of-logtail)
                                   (logtail-of-loghead)))))))

(define sparseint$-compare-int ((offset natp)
                                (x sparseint$-p)
                                (y integerp))
  :returns (sign integerp :rule-classes :type-prescription)
  :measure (sparseint$-count x)
  (b* ((y (lifix y))
       (offset (lnfix offset)))
    (sparseint$-case x
      :leaf (b* ((x (logtail offset x.val)))
              (compare x y))
      :concat
      (b* (((when (<= x.width offset))
            (sparseint$-compare-int (- offset x.width) x.msbs y))
           (width1 (- x.width offset))
           (msbs-compare (sparseint$-compare-int 0 x.msbs (logtail width1 y)))
           ((unless (eql 0 msbs-compare)) msbs-compare))
        (sparseint$-compare-int-width width1 offset x.lsbs
                                      (bignum-loghead width1 y)))))
  ///

  (defret <fn>-correct
    (b* ((xval (logtail offset (sparseint$-val x))))
      (equal sign (compare xval y)))
    :hints (("goal" :induct <call>
             :expand ((:free (y) <call>)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (equal-of-logapp-split
                                    loghead-of-logapp-split
                                    loghead-of-logtail)
                                   (logtail-of-loghead)))))))


(define sparseint$-compare-width ((width posp)
                                  (x sparseint$-p)
                                  (y-offset natp)
                                  (y sparseint$-p))
  :returns (sign integerp :rule-classes :type-prescription)
  :measure (+ (sparseint$-count x) (sparseint$-count y))
  (b* ((width (lposfix width))
       (y-offset (lnfix y-offset)))
    (sparseint$-case x
      :leaf
      (sparseint$-case y
        :leaf (b* ((xval (bignum-loghead width x.val))
                   (yval (bignum-loghead width (logtail y-offset y.val))))
                (compare xval yval))
        :concat (- (sparseint$-compare-int-width width y-offset y (bignum-loghead width x.val))))
      :concat
      (sparseint$-case y
        :leaf (sparseint$-compare-int-width width 0 x (bignum-loghead width (logtail y-offset y.val)))
        :concat
        (b* (((when (<= width x.width))
              (sparseint$-compare-width width x.lsbs y-offset y))
             ((when (<= y.width y-offset))
              (sparseint$-compare-width width x (- y-offset y.width) y.msbs))
             (y-width1 (- y.width y-offset))
             ((when (<= width y-width1))
              (sparseint$-compare-width width x y-offset y.lsbs))
             (msbs-compare
              (sparseint$-compare-width (- width x.width) x.msbs (+ x.width y-offset) y))
             ((unless (eql 0 msbs-compare)) msbs-compare))
          (sparseint$-compare-width x.width x.lsbs y-offset y)))))
  ///
  

  (defret <fn>-correct
    (b* ((xval (loghead (pos-fix width) (sparseint$-val x)))
         (yval (loghead (pos-fix width) (logtail y-offset (sparseint$-val y)))))
      (equal sign (compare xval yval)))
    :hints (("goal" :induct <call>
             :expand ((:free (y) <call>))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:in-theory (e/d (loghead-of-logapp-split
                                    logtail-of-logapp-split)
                                   ())
                   )))))


(define sparseint$-compare-offset ((x sparseint$-p)
                                 (y-offset natp)
                                 (y sparseint$-p))
  :returns (sign integerp :rule-classes :type-prescription)
  :measure (+ (sparseint$-count x) (sparseint$-count y))
  (b* ((y-offset (lnfix y-offset)))
    (sparseint$-case x
      :leaf
      (sparseint$-case y
        :leaf (compare x.val (logtail y-offset y.val))
        :concat (- (sparseint$-compare-int y-offset y x.val)))
      :concat
      (sparseint$-case y
        :leaf (sparseint$-compare-int 0 x (logtail y-offset y.val))
        :concat
        (b* (((when (<= y.width y-offset))
              (sparseint$-compare-offset x (- y-offset y.width) y.msbs))
             (msbs-compare
              (sparseint$-compare-offset x.msbs (+ x.width y-offset) y))
             ((unless (eql 0 msbs-compare)) msbs-compare))
          (sparseint$-compare-width x.width x.lsbs y-offset y)))))
  ///
  

  (defret <fn>-correct
    (equal sign
           (compare (sparseint$-val x)
                    (logtail y-offset (sparseint$-val y))))
    :hints (("goal" :induct <call>
             :do-not-induct t
             :expand ((:free (y) <call>)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (loghead-of-logapp-split
                                    logtail-of-logapp-split)
                                   ()))))))



(define sparseint$-compare ((x sparseint$-p)
                          (y sparseint$-p))
  :returns (sign integerp :rule-classes :type-prescription)
  :inline t
  (sparseint$-compare-offset x 0 y)
  ///
  (defret <fn>-correct
    (equal sign
           (compare (sparseint$-val x)
                    (sparseint$-val y)))))

(define sparseint-compare ((x sparseint-p)
                           (y sparseint-p))
  :parents (sparseint)
  :short "Compare the values of two sparseints and return -1, 0, or 1."
  :returns (sign integerp :rule-classes :type-prescription)
  :inline t
  (sparseint$-compare (sparseint-fix x) (sparseint-fix y))
  ///
  (defret <fn>-correct
    (equal sign
           (compare (sparseint-val x)
                    (sparseint-val y)))
    :hints(("Goal" :in-theory (enable sparseint-val)))))

(define sparseint-< ((x sparseint-p)
                     (y sparseint-p))
  :parents (sparseint)
  :short "Check whether the value of @('x') is less than the value of @('y')."
  :returns (less booleanp :rule-classes :type-prescription)
  :inline t
  (eql (sparseint-compare x y) -1)
  ///
  (defret <fn>-correct
    (equal less
           (< (sparseint-val x)
              (sparseint-val y)))
    :hints(("Goal" :in-theory (enable compare)))))



(define int-to-sparseint$-rec ((x integerp)
                               (width posp)
                               (lsb natp))
  :returns (mv (sint sparseint$-p)
               (height (equal height (sparseint$-height sint)))
               (width-out posp :rule-classes :type-prescription))
  :measure (lposfix width)
  :prepwork ((local (defthm posp-logcdr-of-greater-than-2
                      (implies (<= 2 (ifix x))
                               (<= 1 (logcdr x)))
                      :rule-classes :linear))
             (local (in-theory (e/d (logcdr-<-x-when-positive)
                                    (trailing-0-count-bound
                                     logbitp-when-bitmaskp))))
             (local (defthm pos-fix-of-pos-fix-minus-pos-fix
                      (implies (and (posp half)
                                    (<= 2 (pos-fix width)))
                               (< (pos-fix (+ (pos-fix width) (- half)))
                                  (pos-fix width)))
                      :hints(("Goal" :in-theory (enable pos-fix))))))
  :verify-guards nil
  (b* ((width (lposfix width))
       ((when (< width (sparseint$-leaf-bitlimit)))
        (b* ((end (+ width (lnfix lsb)))
             (bit (logbitp (1- end) x))
             (offset (if bit
                         (trailing-1-count-from x end)
                       (trailing-0-count-from x end))))
          (mv (sparseint$-leaf (fast-part-extend x width lsb))
              0
              (+ width offset))))
       (half (logcdr width))
       ((mv lsbs lsbs-height lsbs-width)
        (int-to-sparseint$-rec x half lsb))
       ((when (<= width lsbs-width))
        (mv lsbs lsbs-height lsbs-width))
       (lsbs-width (mbe :logic (max half (pos-fix lsbs-width))
                        :exec lsbs-width))
       ((mv msbs msbs-height msbs-width)
        (int-to-sparseint$-rec x (- width lsbs-width)
                               (+ (lnfix lsb) lsbs-width)))
       ((mv concat concat-height)
        (sparseint$-concatenate-rebalance lsbs-width lsbs lsbs-height msbs msbs-height)))
    (mv concat concat-height (+ lsbs-width msbs-width)))
  ///
  (defret width-out-gte-width-of-<fn>
    (<= (pos-fix width) width-out)
    :rule-classes :linear)

  (defret sparseint$-height-correctp-of-<fn>
    (sparseint$-height-correctp sint))

  (local (defthm logapp-logext-logtail
           (equal (logapp n (logext n x) (logtail n x))
                  (ifix x))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs
                                              equal-logcons-strong)
                   :induct (logtail n x)))))

  (local (defthm logapp-by-trailing-0-count
           (equal (logapp (trailing-0-count x) x y)
                  (ash y (trailing-0-count x)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs
                                              trailing-0-count)))))

  (local (defthm logapp-trailing-0-count-of-logext
           (implies (and (posp n)
                         (not (logbitp (+ -1 n) x)))
                    (equal (logapp (+ n (trailing-0-count (logtail n x)))
                                   (logext n x)
                                   y)
                           (logapp (+ n (trailing-0-count (logtail n x))) x y)))
           :hints (("goal" :induct (logext n x)
                    :in-theory (enable* ihsext-inductions
                                        ihsext-recursive-redefs)))))

  (local (defthm logapp-by-trailing-1-count
           (equal (logapp (trailing-0-count (lognot x)) x y)
                  (logapp (trailing-0-count (lognot x)) -1 y))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs
                                              trailing-0-count)))))

  (local (defthm logapp-trailing-1-count-of-logext
           (implies (and (posp n)
                         (logbitp (+ -1 n) x))
                    (equal (logapp (+ n (trailing-0-count (lognot (logtail n x))))
                                   (logext n x)
                                   y)
                           (logapp (+ n (trailing-0-count (lognot (logtail n x)))) x y)))
           :hints (("goal" :induct (logext n x)
                    :in-theory (enable* ihsext-inductions
                                        ihsext-recursive-redefs)))))

  (local (defthm logext-of-trailing-0-count-base
           (implies (equal (logcar x) 0)
                    (equal (logext (trailing-0-count x) x) 0))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs
                                              trailing-0-count)))))

  (local (defthm logext-of-trailing-0-count-base-rw
           (implies (not (equal 0 (trailing-0-count x)))
                    (equal (logext (trailing-0-count x) x) 0))
           :hints(("Goal" :use logext-of-trailing-0-count-base
                   :expand ((trailing-0-count x))
                   :in-theory (disable logext-of-trailing-0-count-base)))))

  (local (defthm logexts-equal-by-trailing-0-count
           (implies (and (posp w1)
                         (not (logbitp (+ -1 w1) x)))
                    (equal (logext (+ w1 (trailing-0-count (logtail w1 x))) x) (logext w1 x)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs
                                              trailing-0-count)
                   :induct (logext w1 x)))
           :rule-classes nil))

  (local (defthm logext-equal-x
           (implies (equal (logext n x) (ifix x))
                    (equal (logext (+ (nfix m) (pos-fix n)) x)
                           (ifix x)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs
                                              equal-logcons-strong)
                   :induct (logext n x)
                   :expand ((logext (+ n (nfix m)) x))))
           :rule-classes nil))

  (local (defthm logext-of-between
           (implies (and (equal (logext a x) (logext c x))
                         (<= (pos-fix a) (pos-fix b))
                         (<= (pos-fix b) (pos-fix c)))
                    (equal (logext b x) (logext a x)))
           :hints (("goal" :use ((:instance logext-equal-x
                                  (x (logext c x))
                                  (n a)
                                  (m (- (pos-fix b) (pos-fix a)))))))
           :rule-classes nil))

  (local (in-theory (disable logext-of-logtail)))

  (defret sparseint$-val-of-<fn>
    (equal (sparseint$-val sint)
           (logext width-out (logtail lsb x)))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :in-theory (disable (:d int-to-sparseint$-rec)))
            (and stable-under-simplificationp
                 '(:in-theory (enable equal-of-logapp-split
                                      logtail-of-logext)))
            (and stable-under-simplificationp
                 '(:use ((:instance logexts-equal-by-trailing-0-count
                          (x (logtail lsb x))
                          (w1 (pos-fix width)))
                         (:instance logexts-equal-by-trailing-0-count
                          (x (lognot (logtail lsb x)))
                          (w1 (pos-fix width))))))
            ))

  (verify-guards int-to-sparseint$-rec)


  (local (defthm logext-when-gt-integer-length
           (implies (and (posp width)
                         (< (integer-length x) width))
                    (equal (logext width x) (ifix x)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs
                                              equal-logcons-strong)))))

  (defthmd int-to-sparseint$-rec-unchanged
    (implies (and (< width (sparseint$-leaf-bitlimit))
                  (< (integer-length x) width)
                  (posp width))
             (equal (mv-nth 0 (int-to-sparseint$-rec x width 0))
                    (ifix x)))
    :hints(("Goal" :in-theory (enable int-to-sparseint$-rec
                                      sparseint$-p
                                      sparseint$-kind
                                      sparseint$-leaf->val)))))

(define int-to-sparseint$ ((x integerp))
  :returns (sint sparseint$-p)
  :inline t
  :prepwork
  ((local (defthm logext-of-greater-than-length
            (implies (< (integer-length x) (pos-fix n))
                     (equal (logext n x) (ifix x)))
            :hints(("Goal" :in-theory (enable* ihsext-inductions
                                               ihsext-recursive-redefs))))))
  :guard-hints (("goal" :in-theory (enable int-to-sparseint$-rec-unchanged)))
  (mbe :logic
       (b* (((mv sint ?height ?width) (int-to-sparseint$-rec x (+ 1 (integer-length x)) 0)))
         sint)
       :exec (if (< (+ 1 (integer-length x)) (sparseint$-leaf-bitlimit))
                 x
               (b* (((mv sint ?height ?width) (int-to-sparseint$-rec x (+ 1 (integer-length x)) 0)))
                 sint)))
  ///
  (defret sparseint$-height-correctp-of-<fn>
    (sparseint$-height-correctp sint))

  (defret sparseint$-val-of-<fn>
    (equal (sparseint$-val sint)
           (ifix x))))

(define int-to-sparseint ((x integerp))
  :parents (sparseint)
  :short "Convert an integer into a sparseint."
  :returns (sint sparseint-p)
  :prepwork ((local (in-theory (enable sparseint-p))))
  :inline t
  (int-to-sparseint$ x)
  ///

  (defret sparseint-val-of-<fn>
    (equal (sparseint-val sint)
           (ifix x))
    :hints(("Goal" :in-theory (enable sparseint-val)))))

(define sparseint$-length-width-rec ((width posp)
                                     (tail integerp)
                                     (x sparseint$-p))
  :returns (length integerp :rule-classes :type-prescription
                   ;; Hacky encoding: 0 means tail is 0, -1 means tail is 1, otherwise must be a positive length.
                   )
  :measure (sparseint$-count x)
  (b* ((width (lposfix width)))
    (sparseint$-case x
      :leaf (b* ((val (logapp width x.val tail))
                 ((when (eql val 0)) 0)
                 ((when (eql val -1)) -1))
              (integer-length val))
      :concat (b* (((when (<= width x.width))
                    (sparseint$-length-width-rec width tail x.lsbs))
                   (tail/len
                    (sparseint$-length-width-rec (- width x.width) tail x.msbs))
                   ((when (< 0 tail/len)) (+ x.width tail/len)))
                (sparseint$-length-width-rec x.width tail/len x.lsbs))))
  ///
  (local (in-theory (disable logapp-of-j-0)))

  (local (defthm logapp-minus1-when-equal-minus1
           (implies (equal (logext n x) -1)
                    (equal (logapp n x -1) -1))
           :hints(("Goal" :in-theory (enable equal-of-logapp-split-logext)))))

  (local (defthm logapp-0-when-equal-0
           (implies (equal (logext n x) 0)
                    (equal (logapp n x 0) 0))
           :hints(("Goal" :in-theory (e/d (equal-of-logapp-split-logext))))))

  (local (defthm integer-length-equal-0
           (equal (equal 0 (integer-length x))
                  (or (equal (ifix x) 0)
                      (equal (ifix x) -1)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))

  (defretd <fn>-correct
    (and (implies (and (< 0 length)
                       (<= -1 (ifix tail))
                       (<= (ifix tail) 0))
                  (equal length
                         (integer-length (logapp (pos-fix width) (sparseint$-val x) tail))))
         (implies (and (<= length 0)
                       (<= -1 (ifix tail))
                       (<= (ifix tail) 0))
                  (and (equal length (ifix tail))
                       (equal (logext width (sparseint$-val x)) (ifix tail))))
         (<= -1 length))
    :hints (("goal" :induct <call> :do-not-induct t)
            (and stable-under-simplificationp
                 '(:cases ((zip tail))
                   :in-theory (enable logapp-right-assoc)))
            (and stable-under-simplificationp
                 '(:in-theory (enable equal-of-logapp-split-logext))))))


                 
  

(define sparseint$-length-rec ((x sparseint$-p))
  :returns (length integerp :rule-classes :type-prescription
                   ;; Hacky encoding: 0 means tail is 0, -1 means tail is 1, otherwise must be a positive length.
                   )
  :measure (sparseint$-count x)
  (sparseint$-case x
    :leaf (cond ((eql x.val 0) 0)
                ((eql x.val -1) -1)
                (t (integer-length x.val)))
    :concat (b* ((tail/len (sparseint$-length-rec x.msbs))
                 ((when (< 0 tail/len))
                  (+ x.width tail/len)))
              (sparseint$-length-width-rec x.width tail/len x.lsbs)))
  ///
  (local (in-theory (disable logapp-of-j-0)))

  (local (defthm integer-length-equal-0
           (equal (equal 0 (integer-length x))
                  (or (equal (ifix x) 0)
                      (equal (ifix x) -1)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))
  
  (local (in-theory (enable sparseint$-length-width-rec-correct)))

  (defret <fn>-correct
    (and (implies (< 0 length)
                  (equal length
                         (integer-length (sparseint$-val x))))
         (implies (<= length 0)
                  (equal length (sparseint$-val x)))
         (<= -1 length))
    :hints (("goal" :induct <call> :do-not-induct t)
            (and stable-under-simplificationp
                 '(:cases ((zip length))
                   :in-theory (enable logapp-right-assoc)))
            (and stable-under-simplificationp
                 '(:in-theory (enable equal-of-logapp-split-logext))))))

(define sparseint$-length ((x sparseint$-p))
  :returns (length)
  :inline t
  (b* ((tail/len (sparseint$-length-rec x)))
    (max tail/len 0))
  ///
  (defret <fn>-correct
    (equal length (integer-length (sparseint$-val x)))
    :hints (("goal" :use sparseint$-length-rec-correct
             :in-theory (disable sparseint$-length-rec-correct)
             :expand ((integer-length (sparseint$-length-rec x)))))))


       
(define sparseint-length ((x sparseint-p))
  :parents (sparseint)
  :short "Compute the integer-length of a sparseint.  Returns an integer, not a sparseint."
  :returns (length natp :rule-classes :type-prescription)
  :inline t
  (sparseint$-length (sparseint-fix x))
  ///
  (defret <fn>-correct
    (equal length (integer-length (sparseint-val x)))
    :hints(("Goal" :in-theory (enable sparseint-val)))))


(local (defthm b-and-plus-b-xor
         (equal (+ (b-and x y) (b-xor x y))
                (b-ior x y))
         :hints(("Goal" :in-theory (enable b-and b-xor b-ior)))))

(local (defthm b-and-plus-b-xor-2
         (equal (+ (b-and x y) (b-xor x y) z)
                (+ (b-ior x y) z))
         :hints(("Goal" :in-theory (enable b-and b-xor b-ior)))))

(local (defthm logxor-of-bits
         (implies (and (bitp a) (bitp b))
                  (equal (logxor a b)
                         (b-xor a b)))))

(local
 (defsection logext-of-sum
   (local (defun logext-sum-ind (cin width x y)
            (declare (xargs :measure (nfix width)))
            (if (<= (nfix width) 1)
                (list cin x y)
              (logext-sum-ind (b-ite cin
                                     (b-ior (logcar x) (logcar y))
                                     (b-and (logcar x) (logcar y)))
                              (1- width)
                              (logcdr x)
                              (logcdr y)))))

   (defthmd logext-of-plus-of-logext-lemma
     (implies (and (integerp y)
                   (bitp cin))
              (equal (logext width (+ cin (logext width x) y))
                     (logext width (+ cin (ifix x) y))))
     :hints (("goal" :induct (logext-sum-ind cin width x y)
              :in-theory (enable equal-logcons-strong)
              :expand ((:free (x) (logext width x))))
             (and stable-under-simplificationp
                  '(:in-theory (enable b-ite)))))

   (defthm logext-of-sum-simplify-arg1
     (implies (and (integerp x)
                   (integerp y)
                   (equal xx (logext width x))
                   (bind-free
                    (case-match xx
                      (('logext w xxx)
                       (if (equal w width)
                           (if (equal xxx x)
                               nil
                             `((xxx . ,xxx)))
                         (and (not (equal xx x))
                              `((xxx . ,xx)))))
                      (& (and (not (equal xx x))
                              `((xxx . ,xx))))))
                   (equal (logext width xxx) (logext width xx)))
              (equal (logext width (+ x y))
                     (logext width (+ (ifix xxx) y))))
     :hints (("goal" :use ((:instance logext-of-plus-of-logext-lemma
                            (cin 0) (x xxx))
                           (:instance logext-of-plus-of-logext-lemma
                            (cin 0) (x x))))))

   (defthm logext-of-sum-simplify-arg2
     (implies (and (integerp x)
                   (integerp y)
                   (equal xx (logext width x))
                   (bind-free
                    (case-match xx
                      (('logext w xxx)
                       (if (equal w width)
                           (if (equal xxx x)
                               nil
                             `((xxx . ,xxx)))
                         (and (not (equal xx x))
                              `((xxx . ,xx)))))
                      (& (and (not (equal xx x))
                              `((xxx . ,xx))))))
                   (equal (logext width xxx) (logext width xx)))
              (equal (logext width (+ y x))
                     (logext width (+ y (ifix xxx)))))
     :hints (("goal" :use logext-of-sum-simplify-arg1
              :in-theory (disable logext-of-sum-simplify-arg1))))

   
   (defthmd loghead-of-plus-of-loghead-lemma
     (implies (and (integerp y)
                   (bitp cin))
              (equal (loghead width (+ cin (loghead width x) y))
                     (loghead width (+ cin (ifix x) y))))
     :hints (("goal" :induct (logext-sum-ind cin width x y)
              :in-theory (enable equal-logcons-strong)
              :expand ((:free (x) (loghead width x))))
             (and stable-under-simplificationp
                  '(:in-theory (enable b-ite)))))

   
   (defthm loghead-of-sum-simplify-arg1
     (implies (and (integerp x)
                   (integerp y)
                   (equal xx (loghead width x))
                   (bind-free
                    (case-match xx
                      (('acl2::loghead$inline w xxx)
                       (if (equal w width)
                           (if (equal xxx x)
                               nil
                             `((xxx . ,xxx)))
                         (and (not (equal xx x))
                              `((xxx . ,xx)))))
                      (& (and (not (equal xx x))
                              `((xxx . ,xx))))))
                   (equal (loghead width xxx) (loghead width xx)))
              (equal (loghead width (+ x y))
                     (loghead width (+ (ifix xxx) y))))
     :hints (("goal" :use ((:instance loghead-of-plus-of-loghead-lemma
                            (cin 0) (x xxx))
                           (:instance loghead-of-plus-of-loghead-lemma
                            (cin 0) (x x))))))

   (defthm loghead-of-sum-simplify-arg2
     (implies (and (integerp x)
                   (integerp y)
                   (equal xx (loghead width x))
                   (bind-free
                    (case-match xx
                      (('acl2::loghead$inline w xxx)
                       (if (equal w width)
                           (if (equal xxx x)
                               nil
                             `((xxx . ,xxx)))
                         (and (not (equal xx x))
                              `((xxx . ,xx)))))
                      (& (and (not (equal xx x))
                              `((xxx . ,xx))))))
                   (equal (loghead width xxx) (loghead width xx)))
              (equal (loghead width (+ y x))
                     (loghead width (+ y (ifix xxx)))))
     :hints (("goal" :use loghead-of-sum-simplify-arg1
              :in-theory (disable loghead-of-sum-simplify-arg1))))

   
   (defthm logapp-of-sum-simplify-arg1
     (implies (and (integerp x)
                   (integerp y)
                   (equal xx (loghead width x))
                   (bind-free
                    (case-match xx
                      (('acl2::loghead$inline w xxx)
                       (if (equal w width)
                           (if (equal xxx x)
                               nil
                             `((xxx . ,xxx)))
                         (and (not (equal xx x))
                              `((xxx . ,xx)))))
                      (& (and (not (equal xx x))
                              `((xxx . ,xx))))))
                   (equal (loghead width xxx) (loghead width xx)))
              (equal (logapp width (+ x y) z)
                     (logapp width (+ (ifix xxx) y) z)))
     :hints (("goal" :use ((:instance loghead-of-plus-of-loghead-lemma
                            (cin 0) (x xxx))
                           (:instance loghead-of-plus-of-loghead-lemma
                            (cin 0) (x x)))
              :in-theory (e/d (logapp)
                              (loghead-of-sum-simplify-arg1
                               loghead-of-sum-simplify-arg2)))))

   (defthm logapp-of-sum-simplify-arg2
     (implies (and (integerp x)
                   (integerp y)
                   (equal xx (loghead width x))
                   (bind-free
                    (case-match xx
                      (('acl2::loghead$inline w xxx)
                       (if (equal w width)
                           (if (equal xxx x)
                               nil
                             `((xxx . ,xxx)))
                         (and (not (equal xx x))
                              `((xxx . ,xx)))))
                      (& (and (not (equal xx x))
                              `((xxx . ,xx))))))
                   (equal (loghead width xxx) (loghead width xx)))
              (equal (logapp width (+ y x) z)
                     (logapp width (+ y (ifix xxx)) z)))
     :hints (("goal" :use logapp-of-sum-simplify-arg1
              :in-theory (disable logapp-of-sum-simplify-arg1))))
   
   (defthm logbitp-of-sum-simplify-arg1
     (implies (and (integerp x)
                   (integerp y)
                   (equal ww (+ 1 (nfix width)))
                   (equal xx (loghead ww x))
                   (bind-free
                    (case-match xx
                      (('acl2::loghead$inline w xxx)
                       (if (equal w ww)
                           (if (equal xxx x)
                               nil
                             `((xxx . ,xxx)))
                         (and (not (equal xx x))
                              `((xxx . ,xx)))))
                      (& (and (not (equal xx x))
                              `((xxx . ,xx))))))
                   (equal (loghead ww xxx) (loghead ww xx)))
              (equal (logbitp width (+ x y))
                     (logbitp width (+ (ifix xxx) y))))
     :hints (("goal" :use ((:instance logbitp-of-loghead-in-bounds
                            (pos width)
                            (size (+ 1 (nfix width)))
                            (i (+ (loghead (+ 1 (nfix width)) x) y)))
                           (:instance logbitp-of-loghead-in-bounds
                            (pos width)
                            (size (+ 1 (nfix width)))
                            (i (+ x y)))
                           (:instance logbitp-of-loghead-in-bounds
                            (pos width)
                            (size (+ 1 (nfix width)))
                            (i (+ (loghead (+ 1 (nfix width)) xxx) y)))
                           (:instance logbitp-of-loghead-in-bounds
                            (pos width)
                            (size (+ 1 (nfix width)))
                            (i (+ (ifix xxx) y))))
              :in-theory (disable logbitp-of-loghead-in-bounds))))

   (defthm logbitp-of-sum-simplify-arg2
     (implies (and (integerp x)
                   (integerp y)
                   (equal ww (+ 1 (nfix width)))
                   (equal xx (loghead ww x))
                   (bind-free
                    (case-match xx
                      (('acl2::loghead$inline w xxx)
                       (if (equal w ww)
                           (if (equal xxx x)
                               nil
                             `((xxx . ,xxx)))
                         (and (not (equal xx x))
                              `((xxx . ,xx)))))
                      (& (and (not (equal xx x))
                              `((xxx . ,xx))))))
                   (equal (loghead ww xxx) (loghead ww xx)))
              (equal (logbitp width (+ y x))
                     (logbitp width (+ y (ifix xxx)))))
     :hints (("goal" :use logbitp-of-sum-simplify-arg1
              :in-theory (disable logbitp-of-sum-simplify-arg1))))))


(define carry-out-bit ((xbit bitp)
                       (ybit bitp)
                       (sumbit bitp))
  :returns (cout bitp :rule-classes :type-prescription)
  (b-ior (b-and xbit ybit)
         (b-and (b-ior xbit ybit)
                (b-not sumbit)))
  ///
  (local (defun logext-sum-ind (cin width x y)
           (declare (xargs :measure (nfix width)))
           (if (<= (nfix width) 1)
               (list cin x y)
             (logext-sum-ind (b-ite cin
                                    (b-ior (logcar x) (logcar y))
                                    (b-and (logcar x) (logcar y)))
                             (1- width)
                             (logcdr x)
                             (logcdr y)))))

  (local (defthmd carry-out-bit-correct-lemma
           (implies (and (posp width)
                         (bitp cin)
                         (integerp x1)
                         (integerp y1)
                         (integerp x2)
                         (integerp y2))
                    (b* ((xbit (logbit (1- width) x1))
                         (ybit (logbit (1- width) y1))
                         (sumbit (logbit (1- width) (+ cin x1 y1))))
                      (equal (logapp width (+ cin x1 y1)
                                     (+ x2 y2
                                        (carry-out-bit xbit ybit sumbit)))
                             (+ cin (logapp width x1 x2) (logapp width y1 y2)))))
           :hints (("goal" :induct (logext-sum-ind cin width x1 y1)
                    :do-not-induct t
                    :in-theory (enable equal-logcons-strong)
                    :expand ((:free (a b) (logapp width a b))
                             (:free (x) (logbitp width x))
                             (:free (x) (logbitp (+ -1 width) x1))
                             (:free (x) (logbitp (+ -1 width) y1))
                             (:free (x) (logbitp (+ -1 width) (+ cin x1 y1)))
                             (:free (x) (logbitp 0 x))))
                   (and stable-under-simplificationp
                        '(:in-theory (enable b-ite)))
                   (and stable-under-simplificationp
                        '(:in-theory (enable bitp))))))

  (defthm carry-out-bit-correct
    (implies (and (posp width)
                  (bitp cin)
                  (integerp x1)
                  (integerp y1)
                  (integerp x2)
                  (integerp y2)
                  (equal xbit (logbit (1- width) x1))
                  (equal ybit (logbit (1- width) y1))
                  (equal sumbit (logbit (1- width) (+ cin x1 y1))))
             (equal (logapp width (+ cin x1 y1)
                            (+ x2 y2
                               (carry-out-bit xbit ybit sumbit)))
                    (+ cin (logapp width x1 x2) (logapp width y1 y2))))
    :hints (("goal" :use carry-out-bit-correct-lemma)))

  (defthm carry-out-bit-correct-logtail
    (implies (and (posp width)
                  (bitp cin)
                  (integerp x)
                  (integerp y))
             (equal (logtail width (+ x y cin))
                    (+ (logtail width x)
                       (logtail width y)
                       (carry-out-bit (logbit (1- width) x)
                                      (logbit (1- width) y)
                                      (logbit (1- width) (+ cin x y))))))
    :hints (("goal" :use ((:instance carry-out-bit-correct-lemma
                           (x1 (loghead width x))
                           (x2 (logtail width x))
                           (y1 (loghead width y))
                           (y2 (logtail width y))))
             :in-theory (enable equal-of-logapp-split)))
    :rule-classes nil))

(define sum-with-cin ((cin bitp)
                      (x integerp)
                      (y integerp))
  :returns (sum integerp :rule-classes :type-prescription)
  (+ (lbfix cin)
     (lifix x)
     (lifix y))
  ///

  (defthm logext-of-sum-with-cin-simplify-arg1
    (implies (and (equal xx (logext width x))
                  (bind-free
                   (case-match xx
                     (('logext w xxx)
                      (if (equal w width)
                          (if (equal xxx x)
                              nil
                            `((xxx . ,xxx)))
                        (and (not (equal xx x))
                             `((xxx . ,xx)))))
                     (& (and (not (equal xx x))
                             `((xxx . ,xx))))))
                  (equal (logext width xxx) (logext width xx)))
             (equal (logext width (sum-with-cin cin x y))
                    (logext width (sum-with-cin cin xxx y))))
    :hints (("goal" :use ((:instance logext-of-sum-simplify-arg1
                           (x (ifix x)) (y (+ (bfix cin) (ifix y))))))))

    (defthm logext-of-sum-with-cin-simplify-arg2
      (implies (and (equal xx (logext width x))
                    (bind-free
                     (case-match xx
                       (('logext w xxx)
                        (if (equal w width)
                            (if (equal xxx x)
                                nil
                              `((xxx . ,xxx)))
                          (and (not (equal xx x))
                               `((xxx . ,xx)))))
                       (& (and (not (equal xx x))
                               `((xxx . ,xx))))))
                    (equal (logext width xxx) (logext width xx)))
               (equal (logext width (sum-with-cin cin y x))
                      (logext width (sum-with-cin cin y xxx))))
    :hints (("goal" :use ((:instance logext-of-sum-simplify-arg1
                           (x (ifix x)) (y (+ (bfix cin) (ifix y))))))))

    (defthm loghead-of-sum-with-cin-simplify-arg1
    (implies (and (equal xx (loghead width x))
                  (bind-free
                   (case-match xx
                     (('acl2::loghead$inline w xxx)
                      (if (equal w width)
                          (if (equal xxx x)
                              nil
                            `((xxx . ,xxx)))
                        (and (not (equal xx x))
                             `((xxx . ,xx)))))
                     (& (and (not (equal xx x))
                             `((xxx . ,xx))))))
                  (equal (loghead width xxx) (loghead width xx)))
             (equal (loghead width (sum-with-cin cin x y))
                    (loghead width (sum-with-cin cin xxx y))))
    :hints (("goal" :use ((:instance loghead-of-sum-simplify-arg1
                           (x (ifix x)) (y (+ (bfix cin) (ifix y))))))))

    (defthm loghead-of-sum-with-cin-simplify-arg2
      (implies (and (equal xx (loghead width x))
                    (bind-free
                     (case-match xx
                       (('acl2::loghead$inline w xxx)
                        (if (equal w width)
                            (if (equal xxx x)
                                nil
                              `((xxx . ,xxx)))
                          (and (not (equal xx x))
                               `((xxx . ,xx)))))
                       (& (and (not (equal xx x))
                               `((xxx . ,xx))))))
                    (equal (loghead width xxx) (loghead width xx)))
               (equal (loghead width (sum-with-cin cin y x))
                      (loghead width (sum-with-cin cin y xxx))))
    :hints (("goal" :use ((:instance loghead-of-sum-simplify-arg1
                           (x (ifix x)) (y (+ (bfix cin) (ifix y))))))))


    
    (defthm logapp-of-sum-with-cin-simplify-arg1
      (implies (and (equal xx (loghead width x))
                    (bind-free
                     (case-match xx
                       (('acl2::loghead$inline w xxx)
                        (if (equal w width)
                            (if (equal xxx x)
                                nil
                              `((xxx . ,xxx)))
                          (and (not (equal xx x))
                               `((xxx . ,xx)))))
                       (& (and (not (equal xx x))
                               `((xxx . ,xx))))))
                    (equal (loghead width xxx) (loghead width xx)))
               (equal (logapp width (sum-with-cin cin x y) z)
                      (logapp width (sum-with-cin cin xxx y) z)))
      :hints (("goal" :use ((:instance logapp-of-sum-simplify-arg1
                             (x (ifix x)) (y (+ (bfix cin) (ifix y))))))))

    (defthm logapp-of-sum-with-cin-simplify-arg2
      (implies (and (equal xx (loghead width x))
                    (bind-free
                     (case-match xx
                       (('acl2::loghead$inline w xxx)
                        (if (equal w width)
                            (if (equal xxx x)
                                nil
                              `((xxx . ,xxx)))
                          (and (not (equal xx x))
                               `((xxx . ,xx)))))
                       (& (and (not (equal xx x))
                               `((xxx . ,xx))))))
                    (equal (loghead width xxx) (loghead width xx)))
               (equal (logapp width (sum-with-cin cin y x) z)
                      (logapp width (sum-with-cin cin y xxx) z)))
    :hints (("goal" :use ((:instance logapp-of-sum-simplify-arg1
                           (x (ifix x)) (y (+ (bfix cin) (ifix y))))))))
    
    (defthm logbitp-of-sum-with-cin-simplify-arg1
      (implies (and (equal ww (+ 1 (nfix width)))
                    (equal xx (loghead ww x))
                    (bind-free
                     (case-match xx
                       (('acl2::loghead$inline w xxx)
                        (if (equal w ww)
                            (if (equal xxx x)
                                nil
                              `((xxx . ,xxx)))
                          (and (not (equal xx x))
                               `((xxx . ,xx)))))
                       (& (and (not (equal xx x))
                               `((xxx . ,xx))))))
                    (equal (loghead ww xxx) (loghead ww xx)))
               (equal (logbitp width (sum-with-cin cin x y))
                      (logbitp width (sum-with-cin cin xxx y))))
    :hints (("goal" :use ((:instance logbitp-of-sum-simplify-arg1
                           (x (ifix x)) (y (+ (bfix cin) (ifix y))))))))

    (defthm logbitp-of-sum-with-cin-simplify-arg2
      (implies (and (equal ww (+ 1 (nfix width)))
                    (equal xx (loghead ww x))
                    (bind-free
                     (case-match xx
                       (('acl2::loghead$inline w xxx)
                        (if (equal w ww)
                            (if (equal xxx x)
                                nil
                              `((xxx . ,xxx)))
                          (and (not (equal xx x))
                               `((xxx . ,xx)))))
                       (& (and (not (equal xx x))
                               `((xxx . ,xx))))))
                    (equal (loghead ww xxx) (loghead ww xx)))
               (equal (logbitp width (sum-with-cin cin y x))
                      (logbitp width (sum-with-cin cin y xxx))))
    :hints (("goal" :use ((:instance logbitp-of-sum-simplify-arg1
                           (x (ifix x)) (y (+ (bfix cin) (ifix y)))))))))


(define carry-out ((width posp)
                   (cin bitp)
                   (x integerp)
                   (y integerp))
  (b* ((width (lposfix width))
       (sum (sum-with-cin cin
                          (loghead width x)
                          (loghead width y))))
    (logtail (lposfix width) sum))
  ///
  (defthm carry-out-bit-is-carry-out
    (implies (and (posp width)
                  (equal xbit (bool->bit (logbitp (+ -1 width) x)))
                  (equal ybit (bool->bit (logbitp (+ -1 width) y))))
             (equal (carry-out-bit xbit
                                   ybit
                                   (bool->bit (logbitp (+ -1 width) (sum-with-cin cin x y))))
                    (carry-out width cin x y)))
    :hints (("goal" :use ((:instance carry-out-bit-correct
                           (x1 (loghead width x))
                           (x2 0)
                           (y1 (loghead width y))
                           (y2 0)
                           (cin (bfix cin))
                           (xbit (logbit (1- width) x))
                           (ybit (logbit (1- width) y))
                           (sumbit (logbit (1- width) (sum-with-cin
                                                       cin (loghead width x)
                                                       (loghead width y))))))
             :in-theory (e/d (equal-of-logapp-split
                              sum-with-cin)
                             (carry-out-bit-correct)))))


  (defthm bitp-of-carry-out
    (bitp (carry-out width cin x y))
    :hints (("goal" :use ((:instance carry-out-bit-is-carry-out
                           (x (ifix x)) (y (ifix y)) (cin (bfix cin))
                           (xbit (logbit (+ -1 (pos-fix width)) x))
                           (ybit (logbit (+ -1 (pos-fix width)) y))
                           (width (pos-fix width))))
             :in-theory (disable carry-out-bit-is-carry-out)))
    :rule-classes :type-prescription)

  (defthm carry-out-correct
    (implies (posp width)
             (equal (logapp width (sum-with-cin cin x1 y1)
                            (sum-with-cin (carry-out width cin x1 y1)
                                          x2 y2))
                    (sum-with-cin cin (logapp width x1 x2) (logapp width y1 y2))))
    :hints (("goal" :use ((:instance carry-out-bit-correct
                           (cin (bfix cin))
                           (x1 (ifix x1))
                           (x2 (ifix x2))
                           (y1 (ifix y1))
                           (y2 (ifix y2))
                           (xbit (logbit (1- width) x1))
                           (ybit (logbit (1- width) y1))
                           (sumbit (logbit (1- width) (+ (bfix cin) (ifix x1) (ifix y1)))))
                          (:instance carry-out-bit-is-carry-out
                           (x (ifix x1)) (y (ifix y1)) (cin (bfix cin))
                           (xbit (logbit (1- width) x1))
                           (ybit (logbit (1- width) y1))))
             :in-theory (e/d (sum-with-cin)
                             (carry-out-bit-correct
                              carry-out-bit-is-carry-out)))))

  (defthm carry-out-of-carry-out
    (equal (carry-out w2 (carry-out w1 cin x1 y1)
                      x2 y2)
           (carry-out (+ (pos-fix w1) (pos-fix w2))
                      cin
                      (logapp (pos-fix w1) x1 x2)
                      (logapp (pos-fix w1) y1 y2)))
    :hints (("goal" :use ((:instance carry-out-correct
                           (width (pos-fix w1))
                           (x2 (loghead (pos-fix w2) x2))
                           (y2 (loghead (pos-fix w2) y2))))
             :in-theory (e/d (equal-of-logapp-split)
                             (carry-out-correct)))))

  (defthm carry-out-of-sum
    (implies (posp width)
             (equal (logtail width (sum-with-cin cin x y))
                    (sum-with-cin (carry-out width cin x y)
                                  (logtail width x)
                                  (logtail width y))))
    :hints (("goal" :use ((:instance carry-out-bit-correct-logtail
                           (cin (bfix cin)) (x (ifix x)) (y (ifix y)))
                          (:instance carry-out-bit-is-carry-out
                           (x (ifix x)) (y (ifix y)) (cin (bfix cin))
                           (xbit (logbit (1- width) x))
                           (ybit (logbit (1- width) y))))
             :in-theory (enable sum-with-cin))))

  (local (in-theory (disable carry-out-of-sum))) ;; incompatible with definition of carry-out

  (defthm carry-out-simplify-loghead-1
    (implies (and (equal ww (pos-fix width))
                  (equal xx (loghead ww x))
                  (bind-free
                   (case-match xx
                     (('acl2::loghead$inline w xxx)
                      (if (equal w ww)
                          (if (equal xxx x)
                              nil
                            `((xxx . ,xxx)))
                        (and (not (equal xx x))
                             `((xxx . ,xx)))))
                     (& (and (not (equal xx x))
                             `((xxx . ,xx))))))
                  (equal (loghead ww xxx) (loghead ww xx)))
             (equal (carry-out width cin x y)
                    (carry-out width cin xxx y))))

  (defthm carry-out-simplify-loghead-2
    (implies (and (equal ww (pos-fix width))
                  (equal xx (loghead ww x))
                  (bind-free
                   (case-match xx
                     (('acl2::loghead$inline w xxx)
                      (if (equal w ww)
                          (if (equal xxx x)
                              nil
                            `((xxx . ,xxx)))
                        (and (not (equal xx x))
                             `((xxx . ,xx)))))
                     (& (and (not (equal xx x))
                             `((xxx . ,xx))))))
                  (equal (loghead ww xxx) (loghead ww xx)))
             (equal (carry-out width cin y x)
                    (carry-out width cin y xxx)))))

(local (defthm logext-of-pos-fix
         (equal (logext (pos-fix width) x)
                (logext width x))))
(local (defthm logext-of-greater-than-length
         (implies (< (integer-length x) (pos-fix n))
                  (equal (logext n x) (ifix x)))
         :hints(("Goal" :in-theory (enable* ihsext-inductions
                                            ihsext-recursive-redefs)))))
(local (defthm integer-length-of-logext
         (< (integer-length (logext n x)) (pos-fix n))
         :hints(("Goal" :in-theory (enable* ihsext-inductions
                                            ihsext-recursive-redefs)))
         :rule-classes :linear))

(define sparseint$-plus-int-width ((width posp)
                                   (offset natp)
                                   (x sparseint$-p)
                                   (x.height natp)
                                   (y integerp)
                                   (cin bitp))
  :guard (and (sparseint$-height-correctp x)
              (equal x.height (sparseint$-height x))
              (< (integer-length y) width))
  :returns (mv (sum sparseint$-p)
               (height (equal height (sparseint$-height sum)))
               (cout bitp :rule-classes :type-prescription))
  :verify-guards nil
  :measure (sparseint$-count x)
  (b* ((width (lposfix width))
       (offset (lnfix offset))
       (y (mbe :logic (logext width y)
               :exec y))
       (cin (lbfix cin))
       (x.height (mbe :logic (sparseint$-height x) :exec x.height))
       ;; BOZO add an optimized case for when y = 0
       )
    (sparseint$-case x
      :leaf (b* ((xval (bignum-logext width (logtail offset x.val)))
                 (sum (bignum-logext width (sum-with-cin cin xval y)))
                 (cout (carry-out-bit (logbit (1- width) xval)
                                  (logbit (1- width) y)
                                  (logbit (1- width) sum))))
              (mv (sparseint$-leaf sum) 0 cout))
      :concat
      (b* ((x.msbs.height (mbe :logic (sparseint$-height x.msbs)
                               :exec (- x.height (if x.lsbs-taller 2 1))))
           ((when (<= x.width offset))
            (sparseint$-plus-int-width width (- offset x.width) x.msbs x.msbs.height y cin))
           (width1 (- x.width offset))
           (x.lsbs.height (mbe :logic (sparseint$-height x.lsbs)
                               :exec (- x.height (if x.msbs-taller 2 1))))
           ((when (<= width width1))
            (sparseint$-plus-int-width width offset x.lsbs x.lsbs.height y cin))
           ((mv lsbs-sum lsbs-sum-height lsbs-cout)
            (sparseint$-plus-int-width width1 offset x.lsbs x.lsbs.height (bignum-logext width1 y) cin))
           ((mv msbs-sum msbs-sum-height msbs-cout)
            (sparseint$-plus-int-width (- width width1) 0 x.msbs x.msbs.height (logtail width1 y) lsbs-cout))
           ((mv sum-concat sum-height)
            (sparseint$-concatenate-rebalance width1 lsbs-sum lsbs-sum-height msbs-sum msbs-sum-height)))
        (mv sum-concat sum-height msbs-cout))))
  ///
  (local (in-theory (disable (:d sparseint$-plus-int-width))))

  (defret sparseint$-height-correctp-of-<fn>
    (implies (sparseint$-height-correctp x)
             (sparseint$-height-correctp sum))
    :hints (("goal" :induct <call>
             :expand ((:free (y) <call>)))))

  (verify-guards sparseint$-plus-int-width)

  ;; (local (defthm logapp-when-loghead-equal
  ;;          (implies (and (equal (loghead w x) z)
  ;;                        (syntaxp (not (find-atom 'sparseint$-plus-int-width z))))
  ;;                   (equal (logapp w x y) (logapp w z y)))
  ;;          :hints(("Goal" :in-theory (enable logapp)))))


  (local (defthm logbitp-of-logext-real
           (equal (logbitp pos (logext size i))
                  (if (< (nfix pos) (pos-fix size))
                      (logbitp pos i)
                    (logbitp (1- (pos-fix size)) i)))
           :hints (("goal" :cases ((zp size))))))

  (local (in-theory (disable logbitp-of-logext)))

  (defret sparseint$-val-of-<fn>
    (and (equal (sparseint$-val sum)
                (logext width (sum-with-cin cin (logtail offset (sparseint$-val x)) y)))
         (equal cout
                (carry-out width cin (logtail offset (sparseint$-val x)) y)))
    :hints (("goal" :induct <call>
             :do-not-induct t
             :expand ((:free (y) <call>)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (equal-of-logapp-split
                                    logtail-of-logext
                                    loghead-of-logtail)
                                   (logext-of-logtail
                                    logtail-of-loghead)))))))

(define sparseint$-plus-int ((offset natp)
                             (x sparseint$-p)
                             (x.height natp)
                             (y integerp)
                             (cin bitp))
  :guard (and (sparseint$-height-correctp x)
              (equal x.height (sparseint$-height x)))
  :returns (mv (sum sparseint$-p)
               (height (equal height (sparseint$-height sum))))
  :verify-guards nil
  :measure (sparseint$-count x)
  (b* ((offset (lnfix offset))
       (y (lifix y))
       (cin (lbfix cin))
       (x.height (mbe :logic (sparseint$-height x) :exec x.height))
       ;; BOZO add an optimized case for when y = 0
       )
    (sparseint$-case x
      :leaf (b* ((xval (logtail offset x.val))
                 (sum (sum-with-cin cin xval y)))
              (mv (sparseint$-leaf sum) 0))
      :concat
      (b* ((x.msbs.height (mbe :logic (sparseint$-height x.msbs)
                               :exec (- x.height (if x.lsbs-taller 2 1))))
           ((when (<= x.width offset))
            (sparseint$-plus-int (- offset x.width) x.msbs x.msbs.height y cin))
           (width1 (- x.width offset))
           (x.lsbs.height (mbe :logic (sparseint$-height x.lsbs)
                               :exec (- x.height (if x.msbs-taller 2 1))))
           ((mv lsbs-sum lsbs-sum-height lsbs-cout)
            (sparseint$-plus-int-width width1 offset x.lsbs x.lsbs.height (bignum-logext width1 y) cin))
           ((mv msbs-sum msbs-sum-height)
            (sparseint$-plus-int 0 x.msbs x.msbs.height (logtail width1 y) lsbs-cout))
           ((mv sum-concat sum-height)
            (sparseint$-concatenate-rebalance width1 lsbs-sum lsbs-sum-height msbs-sum msbs-sum-height)))
        (mv sum-concat sum-height))))
  ///

  (local (in-theory (disable (:d sparseint$-plus-int-width))))

  (defret sparseint$-height-correctp-of-<fn>
    (implies (sparseint$-height-correctp x)
             (sparseint$-height-correctp sum))
    :hints (("goal" :induct <call>
             :expand ((:free (y) <call>)))))

  (verify-guards sparseint$-plus-int)

  (defret sparseint$-val-of-<fn>
    (equal (sparseint$-val sum)
           (sum-with-cin cin (logtail offset (sparseint$-val x)) y))
    :hints (("goal" :induct <call>
             :do-not-induct t
             :expand ((:free (y) <call>)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (equal-of-logapp-split
                                    logtail-of-logext
                                    loghead-of-logtail)
                                   (logext-of-logtail
                                    logtail-of-loghead)))))))



(define sparseint$-plus-width ((width posp)
                               (x sparseint$-p)
                               (x.height natp)
                               (y-offset natp)
                               (y sparseint$-p)
                               (y.height natp)
                               (cin bitp))
  :guard (and (sparseint$-height-correctp x)
              (equal x.height (sparseint$-height x))
              (sparseint$-height-correctp y)
              (equal y.height (sparseint$-height y)))
  :returns (mv (sum sparseint$-p)
               (height (equal height (sparseint$-height sum)))
               (cout bitp :rule-classes :type-prescription))
  :verify-guards nil
  :measure (+ (sparseint$-count x) (sparseint$-count y))
  (b* ((x.height (mbe :logic (sparseint$-height x) :exec x.height))
       (y.height (mbe :logic (sparseint$-height y) :exec y.height))
       (width (lposfix width))
       (y-offset (lnfix y-offset)))
    (sparseint$-case x
      :leaf
      (sparseint$-case y
        :leaf (b* ((yval (bignum-logext width (logtail y-offset y.val)))
                   (xval (bignum-logext width x.val))
                   (sum (bignum-logext width (sum-with-cin cin xval yval)))
                   (cout (carry-out-bit (logbit (1- width) xval)
                                        (logbit (1- width) yval)
                                        (logbit (1- width) sum))))
                (mv (sparseint$-leaf sum) 0 cout))
        :concat (sparseint$-plus-int-width width y-offset y y.height (bignum-logext width x.val) cin))
      :concat
      (sparseint$-case y
        :leaf (sparseint$-plus-int-width width 0 x x.height (bignum-logext width (logtail y-offset y.val)) cin)
        :concat
        (b* ((x.lsbs.height (mbe :logic (sparseint$-height x.lsbs)
                                 :exec (- x.height (if x.msbs-taller 2 1))))
             ((when (<= width x.width))
              (sparseint$-plus-width width x.lsbs x.lsbs.height y-offset y y.height cin))
             (y.msbs.height (mbe :logic (sparseint$-height y.msbs)
                                 :exec (- y.height (if y.lsbs-taller 2 1))))
             ((when (<= y.width y-offset))
              (sparseint$-plus-width width x x.height (- y-offset y.width) y.msbs y.msbs.height cin))
             (y-width1 (- y.width y-offset))
             (y.lsbs.height (mbe :logic (sparseint$-height y.lsbs)
                                 :exec (- y.height (if y.msbs-taller 2 1))))
             ((when (<= width y-width1))
              (sparseint$-plus-width width x x.height y-offset y.lsbs y.lsbs.height cin))

             ((mv lsbs-sum lsbs-sum.height lsbs-cout)
              (sparseint$-plus-width x.width x.lsbs x.lsbs.height y-offset y y.height cin))

             (x.msbs.height (mbe :logic (sparseint$-height x.msbs)
                                 :exec (- x.height (if x.lsbs-taller 2 1))))
             ((mv msbs-sum msbs-sum.height msbs-cout)
              (sparseint$-plus-width (- width x.width)
                                     x.msbs x.msbs.height
                                     (+ x.width y-offset)
                                     y y.height lsbs-cout))
             ((mv sum-concat sum-height)
              (sparseint$-concatenate-rebalance
               x.width lsbs-sum lsbs-sum.height msbs-sum msbs-sum.height)))
          (mv sum-concat sum-height msbs-cout)))))
  ///
  (local (in-theory (disable (:d sparseint$-plus-width))))

  (defret sparseint$-height-correctp-of-<fn>
    (implies (and (sparseint$-height-correctp x)
                  (sparseint$-height-correctp y))
             (sparseint$-height-correctp sum))
    :hints (("goal" :induct <call>
             :expand ((:free (y) <call>)))))

  (verify-guards sparseint$-plus-width)

  ;; (local (defthm logapp-when-loghead-equal
  ;;          (implies (and (equal (loghead w x) z)
  ;;                        (syntaxp (not (find-atom 'sparseint$-plus-int-width z))))
  ;;                   (equal (logapp w x y) (logapp w z y)))
  ;;          :hints(("Goal" :in-theory (enable logapp)))))

  ;; (local (defthm logapp-of-equal-logext
  ;;          (implies (equal x (logext w z))
  ;;                   (equal (logapp w x y)
  ;;                          (logapp w z y)))
  ;;          :hints(("Goal" :in-theory (enable logapp)))))

  ;; (local (defthm logapp-of-equal-logext-2
  ;;          (implies (equal y (logext w2 z))
  ;;                   (equal (logapp w x y)
  ;;                          (logext (+ (pos-fix w2) (nfix w))(logapp w x z))))))

  ;; (local (in-theory (disable logext-of-logapp-split)))


  
  (local (defthm logbitp-of-logext-real
           (equal (logbitp pos (logext size i))
                  (if (< (nfix pos) (pos-fix size))
                      (logbitp pos i)
                    (logbitp (1- (pos-fix size)) i)))
           :hints (("goal" :cases ((zp size))))))

  (local (in-theory (disable logbitp-of-logext)))

  (local (defthm logapp-of-logtail-identity
           (equal (logapp w x (logtail w x))
                  (ifix x))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))


  ;; (local (defun logapp-logapp-logtail-ind (w1 x1 x2)
  ;;          (if (zp w1)
  ;;              (list w1 x1)
  ;;            (logapp-logapp-logtail-ind (1- w1)
  ;;                                       (logcdr x1)))))

  (local (defthm logapp-of-logapp-of-logtail-identity
           (implies (equal x2 (logtail w1 x1))
                    (equal (logapp w1 x1
                                   (logapp w2 x2 y))
                           (logapp (+ (nfix w1) (nfix w2)) x1 y)))
           :hints (("goal" :induct (logtail w1 x1)
                    :in-theory (enable* ihsext-inductions
                                        ihsext-recursive-redefs)))))
                    ;; :expand ((:free (y1) (logapp w1 x1 y1))
                    ;;          (:free (y1) (logapp (+ w1 (nfix w2)) x1 y1))
                    ;;          (logtail s2 x2))))))

  (local (defthm carry-out-symmetric
           (equal (equal (carry-out width cin y x)
                         (carry-out width cin x y))
                  t)
           :hints(("Goal" :in-theory (e/d (carry-out sum-with-cin)
                                          (carry-out-of-sum))))))

  (local (defthmd sum-with-cin-symmetric
           (equal (sum-with-cin cin y x)
                  (sum-with-cin cin x y))
           :hints(("Goal" :in-theory (enable sum-with-cin)))))

  (local (defthm sum-with-cin-under-logext-symm
           (equal (equal (logext width (sum-with-cin cin y x))
                         (logext width (sum-with-cin cin x y)))
                  t)
           :hints(("Goal" :in-theory (enable sum-with-cin-symmetric)))))

  (defret sparseint$-val-of-<fn>
    (and (equal (sparseint$-val sum)
                (logext width (sum-with-cin cin (sparseint$-val x) (logtail y-offset (sparseint$-val y)))))
         (equal cout
                (carry-out width cin (sparseint$-val x) (logtail y-offset (sparseint$-val y)))))
    :hints (("goal" :induct <call>
             :do-not-induct t
             :do-not '(generalize)
             :expand ((:free (y) <call>)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (equal-of-logapp-split
                                    logtail-of-logext
                                    logtail-of-logapp-split
                                    logtail-of-loghead
                                    loghead-of-logapp-split
                                    logapp-right-assoc)
                                   (logext-of-logtail
                                    loghead-of-logtail)))))))



(define sparseint$-plus-offset ((x sparseint$-p)
                                  (x.height natp)
                                  (y-offset natp)
                                  (y sparseint$-p)
                                  (y.height natp)
                                  (cin bitp))
  :guard (and (sparseint$-height-correctp x)
              (equal x.height (sparseint$-height x))
              (sparseint$-height-correctp y)
              (equal y.height (sparseint$-height y)))
  :returns (mv (sum sparseint$-p)
               (height (equal height (sparseint$-height sum))))
  :verify-guards nil
  :measure (+ (sparseint$-count x) (sparseint$-count y))
  (b* ((x.height (mbe :logic (sparseint$-height x) :exec x.height))
       (y.height (mbe :logic (sparseint$-height y) :exec y.height))
       (y-offset (lnfix y-offset)))
    (sparseint$-case x
      :leaf
      (sparseint$-case y
        :leaf (mv (sparseint$-leaf
                   (sum-with-cin cin x.val (logtail y-offset y.val))) 0)
        :concat (sparseint$-plus-int y-offset y y.height x.val cin))
      :concat
      (sparseint$-case y
        :leaf (sparseint$-plus-int 0 x x.height (logtail y-offset y.val) cin)
        :concat
        (b* ((y.msbs.height (mbe :logic (sparseint$-height y.msbs)
                                 :exec (- y.height (if y.lsbs-taller 2 1))))
             ((when (<= y.width y-offset))
              (sparseint$-plus-offset x x.height (- y-offset y.width) y.msbs y.msbs.height cin))
             (x.lsbs.height (mbe :logic (sparseint$-height x.lsbs)
                                 :exec (- x.height (if x.msbs-taller 2 1))))

             ((mv lsbs-sum lsbs-sum.height lsbs-cout)
              (sparseint$-plus-width x.width x.lsbs x.lsbs.height
                                       y-offset y y.height cin))

             (x.msbs.height (mbe :logic (sparseint$-height x.msbs)
                                 :exec (- x.height (if x.lsbs-taller 2 1))))
             ((mv msbs-sum msbs-sum.height)
              (sparseint$-plus-offset x.msbs x.msbs.height
                                        (+ x.width y-offset)
                                        y y.height lsbs-cout)))
          (sparseint$-concatenate-rebalance
           x.width lsbs-sum lsbs-sum.height msbs-sum msbs-sum.height)))))
  ///
  (local (in-theory (disable (:d sparseint$-plus-int-width))))

  (defret sparseint$-height-correctp-of-<fn>
    (implies (and (sparseint$-height-correctp x)
                  (sparseint$-height-correctp y))
             (sparseint$-height-correctp sum))
    :hints (("goal" :induct <call>
             :expand ((:free (y) <call>)))))

  (verify-guards sparseint$-plus-offset)



  (local (defthm sum-with-cin-symm
           (equal (equal (sum-with-cin cin y x)
                         (sum-with-cin cin x y))
                  t)
           :hints(("Goal" :in-theory (enable sum-with-cin)))))

  (defret sparseint$-val-of-<fn>
    (equal (sparseint$-val sum)
           (sum-with-cin cin (sparseint$-val x) (logtail y-offset (sparseint$-val y))))
    :hints (("goal" :induct <call>
             :do-not-induct t
             :do-not #!acl2 '(generalize fertilize)
             :expand ((:free (y) <call>)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (equal-of-logapp-split
                                    loghead-of-logtail
                                    ;; logtail-of-logext
                                    logtail-of-logapp-split
                                    ;; logtail-of-loghead
                                    ;; loghead-of-logapp-split
                                    ;; logapp-right-assoc
                                    )
                                   (logtail-of-loghead
                                    ;; logext-of-logtail
                                    ;; loghead-of-logtail
                                    ))
                   :do-not #!acl2 '(generalize fertilize))))))


(define sparseint$-plus ((x sparseint$-p)
                         (y sparseint$-p))
  :guard (and (sparseint$-height-correctp x)
              (sparseint$-height-correctp y))
  :returns (sum sparseint$-p)
  :inline t
  (b* (((mv sum ?height)
        (sparseint$-plus-offset x (sparseint$-height x)
                                0
                                y (sparseint$-height y)
                                0)))
    sum)
  ///
  (defret sparseint$-height-correctp-of-<fn>
    (implies (and (sparseint$-height-correctp x)
                  (sparseint$-height-correctp y))
             (sparseint$-height-correctp sum)))

  (defret sparseint$-val-of-<fn>
    (equal (sparseint$-val sum)
           (+ (sparseint$-val x) (sparseint$-val y)))
    :hints(("Goal" :in-theory (enable sum-with-cin)))))

(define sparseint-plus ((x sparseint-p)
                        (y sparseint-p))
  :parents (sparseint)
  :short "Add two sparseints."
  :returns (plus sparseint-p)
  :prepwork ((local (in-theory (enable sparseint-p))))
  :inline t
  (sparseint$-plus (sparseint-fix x) (sparseint-fix y))
  ///
  (defret sparseint-val-of-<fn>
    (equal (sparseint-val plus)
           (+ (sparseint-val x) (sparseint-val y)))
    :hints(("Goal" :in-theory (enable sparseint-val)))))


(define sparseint$-unary-minus ((x sparseint$-p))
  :guard (sparseint$-height-correctp x)
  :returns (minus sparseint$-p)
  (b* ((height (sparseint$-height x))
       (neg (sparseint$-bitnot x))
       ((mv minus ?height)
        (sparseint$-plus-int 0 neg height 0 1)))
    minus)
  ///
  (defret sparseint$-height-correctp-of-<fn>
    (implies (sparseint$-height-correctp x)
             (sparseint$-height-correctp minus)))

  (defret sparseint$-val-of-<fn>
    (equal (sparseint$-val minus)
           (- (sparseint$-val x)))
    :hints(("Goal" :in-theory (enable sum-with-cin lognot)))))


(define sparseint-unary-minus ((x sparseint-p))
  :parents (sparseint)
  :short "Negate a sparseint."
  :prepwork ((local (in-theory (enable sparseint-p))))
  :returns (minus sparseint-p)
  (sparseint$-unary-minus (sparseint-fix x))
  ///

  (defret sparseint-val-of-<fn>
    (equal (sparseint-val minus)
           (- (sparseint-val x)))
    :hints(("Goal" :in-theory (enable sparseint-val)))))


(define sparseint$-binary-minus ((x sparseint$-p)
                                 (y sparseint$-p))
  :parents (sparseint)
  :short "Subtract one sparseint from another."
  :guard (and (sparseint$-height-correctp x)
              (sparseint$-height-correctp y))
  :returns (minus sparseint$-p)
  (b* ((x.height (sparseint$-height x))
       (y.height (sparseint$-height y))
       (y.neg (sparseint$-bitnot y))
       ((mv minus ?height)
        (sparseint$-plus-offset x x.height 0 y.neg y.height 1)))
    minus)
  ///
  (defret sparseint$-height-correctp-of-<fn>
    (implies (and (sparseint$-height-correctp x)
                  (sparseint$-height-correctp y))
             (sparseint$-height-correctp minus)))

  (defret sparseint$-val-of-<fn>
    (equal (sparseint$-val minus)
           (- (sparseint$-val x)
              (sparseint$-val y)))
    :hints(("Goal" :in-theory (enable sum-with-cin lognot)))))


(define sparseint-binary-minus ((x sparseint-p)
                                (y sparseint-p))
  :parents (sparseint)
  :short "Subtract two sparseints."
  :prepwork ((local (in-theory (enable sparseint-p))))
  :returns (minus sparseint-p)
  (sparseint$-binary-minus (sparseint-fix x) (sparseint-fix y))
  ///

  (defret sparseint-val-of-<fn>
    (equal (sparseint-val minus)
           (- (sparseint-val x) (sparseint-val y)))
    :hints(("Goal" :in-theory (enable sparseint-val)))))


(local
 (defsection trailing-0-lemmas

   (defthm trailing-0-count-of-logapp
     (equal (trailing-0-count (logapp width x y))
            (if (or (zp width) (equal (logext width x) 0))
                (if (equal (ifix y) 0)
                    0
                  (+ (lnfix width) (trailing-0-count y)))
              (trailing-0-count x)))
     :hints(("Goal" :in-theory (e/d* (trailing-0-count
                                      ihsext-inductions
                                      ihsext-recursive-redefs)
                                     (logapp-of-i-0
                                      logapp-of-j-0))
             :induct (logapp width x y))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (equal-of-logapp-split-logext)
                                   (logapp-of-i-0
                                    logapp-of-j-0))))))


   (defthm lognot-of-logapp
     (equal (lognot (logapp w a b))
            (logapp w (lognot a) (lognot b)))
     :hints(("Goal" :in-theory (e/d* (ihsext-inductions
                                      ihsext-recursive-redefs)
                                     (logapp-of-j-0
                                      logapp-of-i-0)))))

   (in-theory (disable logapp-of-j-0
                       logapp-of-i-0))

   (defthmd lognot-of-logtail
     (equal (lognot (logtail n x))
            (logtail n (lognot x)))
     :hints(("Goal" :in-theory (e/d* (ihsext-inductions
                                      ihsext-recursive-redefs)))))

   (defthmd lognot-of-logext
     (equal (lognot (logext n x))
            (logext n (lognot x))))))

(define sparseint$-trailing-0-count-width ((width posp)
                                           (offset natp)
                                           (negbit bitp)
                                           (x sparseint$-p))
  :measure (sparseint$-count x)
  ;; note: nonnil if there was a 1-bit within width
  :returns (count acl2::maybe-natp :rule-classes :type-prescription)
  :prepwork ((local (defthmd logtail-0-by-integer-length
                      (iff (equal (logtail n x) 0)
                           (and (<= (integer-length x) (nfix n))
                                (not (logbitp n x))))
                      :hints(("Goal" :in-theory (enable* ihsext-inductions
                                                         ihsext-recursive-redefs)))))
             (local (defthmd logtail-neg1-by-integer-length
                      (iff (equal (logtail n x) -1)
                           (and (<= (integer-length x) (nfix n))
                                (logbitp n x)))
                      :hints(("Goal" :in-theory (enable* ihsext-inductions
                                                         ihsext-recursive-redefs))))))
  :verify-guards nil
  (sparseint$-case x
    :leaf (b* (((when (mbe :logic (equal (logtail offset x.val) (- (lbfix negbit)))
                           :exec (and (<= (integer-length x.val) (lnfix offset))
                                      (eql negbit (logbit offset x.val)))))
                nil)
               (count (if (eql 1 negbit)
                          (trailing-1-count-from x.val offset)
                        (trailing-0-count-from x.val offset))))
            (and (< count (lposfix width)) count))
    :concat (b* ((width (lposfix width))
                 (offset (lnfix offset))
                 ((when (<= x.width offset))
                  (sparseint$-trailing-0-count-width
                   width (- offset x.width) negbit x.msbs))
                 (width1 (- x.width offset))
                 ((when (<= width width1))
                  (sparseint$-trailing-0-count-width width offset negbit x.lsbs))
                 (lsb-count
                  (sparseint$-trailing-0-count-width width1 offset negbit x.lsbs))
                 ((when lsb-count) lsb-count)
                 (msb-count
                  (sparseint$-trailing-0-count-width (- width width1) 0 negbit x.msbs)))
              (and msb-count (+ width1 msb-count))))
  ///
  
  (verify-guards sparseint$-trailing-0-count-width
    :hints (("goal" :in-theory (enable logtail-0-by-integer-length
                                       logtail-neg1-by-integer-length
                                       bool->bit bitp))))


  ;; (local (in-theory (disable logtail-of-lognot
  ;;                            logext-of-lognot)))

  (local
   (progn
     (defthm logbitp-of-logext-mine
       (equal (logbitp n (logext m x))
              (if (< (nfix n) (pos-fix m))
                  (logbitp n x)
                (logbitp (+ -1 m) x)))
       :hints(("Goal" :in-theory (enable pos-fix logbitp**))))

     (defthm logext-when-larger-logext-is-0
       (implies (and (equal (logext n x) 0)
                     (<= (pos-fix m) (pos-fix n)))
                (equal (logext m x) 0))
       :hints ((logbitp-reasoning)))

     (defthm logext-when-larger-logext-is-neg1
       (implies (and (equal (logext n x) -1)
                     (<= (pos-fix m) (pos-fix n)))
                (equal (logext m x) -1))
       :hints ((logbitp-reasoning)))
     
     (defthm logext-0-when-trailing-0-count-greater
       ;; (implies (not (equal (ifix x) 0))
       (iff (equal (logext n x) 0)
            (or (equal (ifix x) 0)
                (<= (pos-fix n) (trailing-0-count x))))
       :hints(("Goal" :in-theory (enable* ihsext-inductions
                                          ihsext-recursive-redefs
                                          trailing-0-count)
               :induct (logext n x))
              (and stable-under-simplificationp
                   '(:in-theory (enable pos-fix)
                     :expand ((trailing-0-count x))))))

     (defthm logext-neg1-when-trailing-0-count-greater
       ;; (implies (not (equal (ifix x) 0))
       (iff (equal (logext n x) -1)
            (or (equal (ifix x) -1)
                (<= (pos-fix n) (trailing-0-count (lognot x)))))
       :hints(("Goal" :in-theory (enable* ihsext-inductions
                                          ihsext-recursive-redefs
                                          trailing-0-count)
               :induct (logext n x))
              (and stable-under-simplificationp
                   '(:in-theory (enable pos-fix trailing-0-count)
                     :expand ((lognot x))))))))

  (defret <fn>-correct
    (and (iff count
              (not (equal (logext width (logtail offset (sparseint$-val x)))
                          (- (bfix negbit)))))
         (implies (not (equal (logext width (logtail offset (sparseint$-val x)))
                              (- (bfix negbit))))
                  (equal count (trailing-0-count (logxor (- (bfix negbit))
                                                         (logtail offset (sparseint$-val x)))))))
    :hints (("goal" :induct <call>
             :expand (<call>))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (loghead-of-logapp-split
                                      logtail-of-logapp-split
                                      equal-of-logapp-split-logext))
                   :cases ((eql (bfix negbit) 1))
                   :do-not-induct t))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (lognot-of-logtail
                                    logtail-of-logext
                                    lognot-of-logext)
                                   (logtail-of-lognot
                                    logext-of-lognot
                                    logext-of-logtail)))))))


(define sparseint$-trailing-0-count-rec ((offset natp)
                                         (negbit bitp)
                                         (x sparseint$-p))
  :measure (sparseint$-count x)
  ;; note: nonnil if x was nonzero
  :returns (count acl2::maybe-natp :rule-classes :type-prescription)

  :prepwork ((local (defthmd logtail-0-by-integer-length
                      (iff (equal (logtail n x) 0)
                           (and (<= (integer-length x) (nfix n))
                                (not (logbitp n x))))
                      :hints(("Goal" :in-theory (enable* ihsext-inductions
                                                         ihsext-recursive-redefs)))))
             (local (defthmd logtail-neg1-by-integer-length
                      (iff (equal (logtail n x) -1)
                           (and (<= (integer-length x) (nfix n))
                                (logbitp n x)))
                      :hints(("Goal" :in-theory (enable* ihsext-inductions
                                                         ihsext-recursive-redefs))))))
  :verify-guards nil
  (sparseint$-case x
    :leaf (b* (((when (mbe :logic (equal (logtail offset x.val) (- (lbfix negbit)))
                           :exec (and (<= (integer-length x.val) (lnfix offset))
                                      (eql negbit (logbit offset x.val)))))
                nil))
            (if (eql negbit 1)
                (trailing-1-count-from x.val offset)
              (trailing-0-count-from x.val offset)))
    :concat (b* ((offset (lnfix offset))
                 ((when (<= x.width offset))
                  (sparseint$-trailing-0-count-rec (- offset x.width) negbit x.msbs))
                 (width1 (- x.width offset))
                 (lsbs-count (sparseint$-trailing-0-count-width
                              width1 offset negbit x.lsbs))
                 ((when lsbs-count) lsbs-count)
                 (msbs-count
                  (sparseint$-trailing-0-count-rec 0 negbit x.msbs)))
              (and msbs-count (+ width1 msbs-count))))
  ///

  (verify-guards sparseint$-trailing-0-count-rec
    :hints (("goal" :in-theory (enable logtail-0-by-integer-length
                                       logtail-neg1-by-integer-length
                                       bool->bit bitp))))
  

  (defret <fn>-correct
    (and (iff count
              (not (equal (logtail offset (sparseint$-val x)) (- (bfix negbit)))))
         (implies (not (equal (logtail offset (sparseint$-val x)) (- (bfix negbit))))
                  (equal count (trailing-0-count (logtail offset (logxor (- (bfix negbit))
                                                                         (sparseint$-val x)))))))
    :hints (("goal" :induct <call>
             :expand (<call>))
            (and stable-under-simplificationp
                 '(:in-theory (enable equal-of-logapp-split-logext)
                   :cases ((eql (bfix negbit) 1))
                   :do-not-induct t)))))


(define sparseint-trailing-0-count ((x sparseint-p))
  :parents (sparseint)
  :short "Count the trailing consecutive 0s of a sparseint."
  :returns (count natp :rule-classes :type-prescription)
  :prepwork ((local (in-theory (enable sparseint-p))))
  (b* ((count (sparseint$-trailing-0-count-rec 0 0 (sparseint-fix x))))
    (or count 0))
  ///
  (defret <fn>-correct
    (equal count (trailing-0-count (sparseint-val x)))
    :hints(("Goal" :in-theory (enable sparseint-val)))))

(define sparseint-trailing-0-count-from ((x sparseint-p)
                                         (offset natp))
  :parents (sparseint)
  :short "Count the consecutive 0s of a sparseint starting at the given offset."
  :returns (count natp :rule-classes :type-prescription)
  :prepwork ((local (in-theory (enable sparseint-p))))
  (b* ((count (sparseint$-trailing-0-count-rec offset 0 (sparseint-fix x))))
    (or count 0))
  ///
  (defret <fn>-correct
    (equal count (trailing-0-count-from (sparseint-val x) offset))
    :hints(("Goal" :in-theory (enable sparseint-val)))))


(define sparseint-trailing-1-count ((x sparseint-p))
  :parents (sparseint)
  :short "Count the trailing consecutive 1s of a sparseint."
  :returns (count natp :rule-classes :type-prescription)
  :prepwork ((local (in-theory (enable sparseint-p))))
  (b* ((count (sparseint$-trailing-0-count-rec 0 1 (sparseint-fix x))))
    (or count 0))
  ///
  (defret <fn>-correct
    (equal count (trailing-1-count (sparseint-val x)))
    :hints(("Goal" :in-theory (enable sparseint-val)))))

(define sparseint-trailing-1-count-from ((x sparseint-p)
                                         (offset natp))
  :parents (sparseint)
  :short "Count the consecutive 1s of a sparseint starting at the given offset."
  :returns (count natp :rule-classes :type-prescription)
  :prepwork ((local (in-theory (enable sparseint-p))))
  (b* ((count (sparseint$-trailing-0-count-rec offset 1 (sparseint-fix x))))
    (or count 0))
  ///
  (defret <fn>-correct
    (equal count (trailing-1-count-from (sparseint-val x) offset))
    :hints(("Goal" :in-theory (enable sparseint-val)))))



;; (local (defthm logapp-lt-0
;;          (equal (< (logapp w x y) 0)
;;                 (< (ifix y) 0))
;;          :hints(("Goal" :in-theory (enable* ihsext-inductions
;;                                             ihsext-recursive-redefs)))))
(local (defthmd logcount***
         (EQUAL (LOGCOUNT X)
                (COND ((ZIP X) 0)
                      ((= X -1) 0)
                      (T (+ (IF (<= 0 X)
                                (LOGCAR X)
                                (B-NOT (LOGCAR X)))
                            (LOGCOUNT (LOGCDR X))))))
         :hints(("Goal" :in-theory (enable logcount**)))
         :rule-classes ((:definition :clique (logcount)
                         :controller-alist ((logcount t))))))

(local (defthm logcount-of-logapp
         (equal (logcount (logapp w x y))
                (+ (if (< (ifix y) 0)
                       (logcount (loghead w (lognot x)))
                     (logcount (loghead w x)))
                   (logcount y)))
         :hints(("Goal" :in-theory (e/d* (ihsext-inductions
                                          ihsext-recursive-redefs
                                          logcount***)
                                         (logcount**))
                 :induct (logapp w x y)))))
                    

(define sparseint$-bitcount-width ((width posp)
                                   (offset natp)
                                   (negbit bitp)
                                   (x sparseint$-p))
  :measure (sparseint$-count x)
  ;; note: nonnil if there was a 1-bit within width
  :returns (count natp :rule-classes :type-prescription)
  :verify-guards nil
  (sparseint$-case x
    :leaf (logcount (bignum-loghead (lposfix width) (logtail offset (logxor (- (lbfix negbit)) x.val))))
    :concat (b* ((width (lposfix width))
                 (offset (lnfix offset))
                 ((when (<= x.width offset))
                  (sparseint$-bitcount-width
                   width (- offset x.width) negbit x.msbs))
                 (width1 (- x.width offset))
                 ((when (<= width width1))
                  (sparseint$-bitcount-width width offset negbit x.lsbs)))
              (+ (sparseint$-bitcount-width width1 offset negbit x.lsbs)
                 (sparseint$-bitcount-width (- width width1) 0 negbit x.msbs))))
  ///
  
  (verify-guards sparseint$-bitcount-width)


  (local (defthm logcount-loghead-logtail-split
           (equal (logcount (loghead n (logtail m x)))
                  (- (logcount (loghead (+ (nfix n) (nfix m)) x))
                     (logcount (loghead m x))))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))


  (defret <fn>-correct
    (equal count (logcount (loghead (pos-fix width) (logtail offset (logxor (- (bfix negbit)) (sparseint$-val x))))))
    :hints (("goal" :induct <call>
             :expand (<call>))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (loghead-of-logapp-split
                                    logtail-of-logapp-split
                                    equal-of-logapp-split))
                   :cases ((eql (bfix negbit) 1))
                   :do-not-induct t)))))


(define sparseint$-bitcount-rec ((offset natp)
                                 (negbit)
                                 (x sparseint$-p))
  :guard (equal negbit (bool->bit (< (sparseint$-val x) 0)))
  :measure (sparseint$-count x)
  ;; note: nonnil if x was nonzero
  :returns (count natp :rule-classes :type-prescription)
  :verify-guards nil
  (sparseint$-case x
    :leaf (logcount (logtail offset x.val))
    :concat (b* ((offset (lnfix offset))
                 (negbit (mbe :logic (bool->bit (eql (sparseint$-compare x 0) -1)) :exec negbit))
                 ((when (<= x.width offset))
                  (sparseint$-bitcount-rec (- offset x.width) negbit x.msbs))
                 (width1 (- x.width offset)))
              (+ (sparseint$-bitcount-width
                  width1 offset negbit x.lsbs)
                 (sparseint$-bitcount-rec 0 negbit x.msbs))))
  ///

  (verify-guards sparseint$-bitcount-rec
    :hints(("Goal" :in-theory (enable compare))))
  

  (defret <fn>-correct
    (equal count (logcount (logtail offset (sparseint$-val x))))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :in-theory (enable compare))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (loghead-of-logtail)
                                   (logtail-of-loghead))))
            (and stable-under-simplificationp
                 '(:in-theory (enable equal-of-logapp-split)
                   :do-not-induct t)))))

(define sparseint-bitcount ((x sparseint-p))
  :parents (sparseint)
  :short "Count the 1 bits in a sparseint if positive, 0 bits if negative."
  :returns (count natp :rule-classes :type-prescription)
  :guard-hints (("goal" :in-theory (enable sparseint-val)))
  (sparseint$-bitcount-rec 0
                           (bool->bit (sparseint-< x 0))
                           (sparseint-fix x))
  ///
  (defret <fn>-correct
    (equal count (logcount (sparseint-val x)))
    :hints(("Goal" :in-theory (enable sparseint-val)))))

(define sparseint-bitcount-from ((offset natp)
                                 (x sparseint-p))
  :parents (sparseint)
  :short "Count the 1 bits in a sparseint if positive, 0 bits if negative, starting from offset."
  :returns (count natp :rule-classes :type-prescription)
  :guard-hints (("goal" :in-theory (enable sparseint-val)))
  (sparseint$-bitcount-rec offset
                           (bool->bit (sparseint-< x 0))
                           (sparseint-fix x))
  ///
  (defret <fn>-correct
    (equal count (logcount (logtail offset (sparseint-val x))))
    :hints(("Goal" :in-theory (enable sparseint-val)))))






    

                            
  

(defxdoc sparseint
  :parents (acl2::bit-vectors)
  :short "Alternative implementation of bignums based on balanced binary trees"
  :long "<p>In some applications it's convenient to operate on long bitvectors.
Most Lisp implementations use immutable, array-based bignum representations.
This means that when you create a new bitvector, it must allocate new memory to
hold it even if a large chunk of that vector is simply a copy of some existing
one.</p>

<p>Sparseints are an alternative bignum representation that tries to avoid this
problem.  They use a binary tree representation to allow structure sharing
between vectors.  To support efficient operations, they are built using an
AVL-style balancing discipline which guarantees that the longest path from the
root to a leaf is at most twice the length of the shortest such path.  This
balancing discipline means that concatenations, which could easily be
implemented as constant-time operations, are instead @('(log n)') time, but
that right-shifts, which would otherwise be linear time, are also @('(log n)')
time.</p>

<h3>High-level interface</h3>

<p>The sparseint type is recognized by @('sparseint-p') and fixed by
@('sparseint-fix').  It is FTY discipline compliant.</p>

<p>To make a sparseint from an integer, use @('(int-to-sparseint x)').  Often
this will just return @('x').  Every integer is a sparseint, but
@('int-to-sparseint') will break down larger integers into tree structures.</p>

<p>To get the integer value of a sparseint, use @('(sparseint-val x)').  Make
sure you have enough memory to hold the integer value that this produces!</p>

<p>The rest of the operations on sparseints are listed here.  As a syntactic
convention, let x, y, and z be sparseints, and use @('xv'), @('yv'), and
@('zv') to signify @('(sparseint-val x)'), etc.</p>

<ul>

<li>@('(sparseint-concatenate width x y)'), where width is a natural number,
creates a new sparseint whose value is @('(logapp width xv yv)').  This can be
used for left shifts, i.e., @('(sparseint-concatenate shift-amt 0 y)').</li>

<li>@('(sparseint-rightshift shift x)'), where shift is a natural number,
creates a new sparseint whose value is @('(ash xv (- shift))').</li>

<li>@('(sparseint-ash x shift)'), where shift is an integer, creates a new
sparseint whose value is @('(ash xv shift)').</li>

<li>@('(sparseint-sign-ext n x)'), where n is a positive number, creates a new sparseint whose value is @('(logext n xv)').</li>

<li>@('(sparseint-bit n x)'), where n is a natural number, returns the bit
@('(logbit n xv)').</li>

<li>@('(sparseint-bitnot x)') creates a new sparseint whose value is @('(lognot
xv)').</li>

<li>Of each of the following pairs of functions, the first computes a new
sparseint whose value is @('(bitop xv yv)'), and the second returns
@('(not (equal 0 (bitop xv yv)))'):
<ul>
<li>@('(sparseint-bitand x y)'), @('(sparseint-test-bitand x y)')</li>
<li>@('sparseint-bitor'), @('sparseint-test-bitor')</li>
<li>@('sparseint-bitxor'), @('sparseint-test-bitxor')</li>
<li>@('sparseint-biteqv'), @('sparseint-test-biteqv')</li>
<li>@('sparseint-bitnand'), @('sparseint-test-bitnand')</li>
<li>@('sparseint-bitnor'), @('sparseint-test-bitnor')</li>
<li>@('sparseint-bitandc1'), @('sparseint-test-bitandc1')</li>
<li>@('sparseint-bitandc2'), @('sparseint-test-bitandc2')</li>
<li>@('sparseint-bitorc1'), @('sparseint-test-bitorc1')</li>
<li>@('sparseint-bitorc2'), @('sparseint-test-bitorc2').</li>
</ul>
These are all implemented using a pair of generic functions
@('(sparseint-binary-bitop op x y)') and @('(sparseint-binary-bittest op x
y)'), where op is a 4-bit unsigned integer interpreted as a truth table
describing the logical operation.  That is, bit @('n') of the result will be
@('(logbit (+ (logbit n xv) (* 2 (logbit n yv))) op)'), so @('#b0100')
signifies ANDc1, @('#b0110') signifies XOR, etc.</li>

<li>@('(sparseint-bitite x y z)') returns a sparseint whose value is the
bitwise if-then-else of xv, yv, zv.</li>

<li>@('(sparseint-equal x y)') returns @('(equal xv yv)').</li>

<li>@('(sparseint-compare x y)') returns @('(compare xv yv)'), where
@('compare') returns 0 when its inputs are equal, -1 when the first is less
than the second, and 1 when the first is greater than the second.</li>

<li>@('(sparseint-< x y)') returns @('(< xv yv)').</li>

<li>@('(sparseint-length x)') returns @('(integer-length xv)').</li>

<li>@('(sparseint-plus x y)') returns a new sparseint whose value is
 @('(+ xv yv)').</li>

<li>@('(sparseint-unary-minus x)') returns a new sparseint whose value is
 @('(- xv)').</li>

<li>@('(sparseint-binary-minus x y)') returns a new sparseint whose value is
@('(- xv yv)').</li>

<li>@('(sparseint-trailing-0-count x)') returns @('(trailing-0-count xv)') and
@('(sparseint-trailing-0-count-from x n)') returns @('(trailing-0-count-from xv
n)'). Similarly for @('(sparseint-trailing-1-count x)') and
@('(sparseint-trailing-1-count-from x n)').</li>

<li>@('(sparseint-bitcount x)') returns @('(logcount xv)') and
@('(sparseint-bitcount-from n x)') returns @('(logcount (logtail n xv))').</li>

</ul>")


