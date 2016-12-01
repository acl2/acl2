; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
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


; ihsext-basics.lisp
;
; Original authors: Sol Swords <sswords@centtech.com>


(in-package "BITOPS")


(include-book "ihs/basic-definitions" :dir :system)
(include-book "std/basic/arith-equiv-defs" :dir :system)

(local (include-book "ihsext-basics"))
(local (include-book "arithmetic/top-with-meta" :dir :system))


(defxdoc limited-shifts
  :parents (bitops)
  :short "Functions for performing shifts that are artificially limited so as to
          make them more amenable to symbolic execution with AIGs.")

(local (xdoc::set-default-parents limited-shifts))


(define logcollapse ((position natp)
                     (x natp))
  :short "OR together all the bits of x at position or above, collapsing them
into the single bit at position."

  :long "<p>This operation helps avoid catastrophically large shifts in
computing, e.g., concatenations with symbolic widths.  When there is a
care-mask of width w, then we can collapse all the bits at w and above into the
bit at w, because the presence of those upper bits means that the shift is
longer than we care about.</p>

<p>There is a large potential for off-by-one errors when thinking about this
function.  It may help to start with the fact that @('(logcollapse 0 x)')
collapses all bits of x into a single bit.  In general, @('(logcollapse n x)')
results in at most n+1 bits.</p>"
  (b* ((position (lnfix position)))
    (logior (loghead position x)
            (ash (b-not (bool->bit (eql 0 (logtail position x)))) position))))

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
                  (<= m (nfix i)))
             (<= m
                 (logcollapse (integer-length m) i)))
    :hints(("Goal" :in-theory (enable logcollapse bool->bit))))

  (local (defthm logtail-integer-length-when-less
           (implies (and (integerp m)
                         (<= 0 (ifix i))
                         (< (ifix i) m))
                    (equal (logtail (integer-length m) i) 0))
           :hints(("Goal" :in-theory (enable* acl2::logtail**
                                              acl2::integer-length**
                                              acl2::ihsext-inductions)
                   :induct (logand m i)))))

  (defthm logcollapse-equal-when-less
    (implies (and (integerp m)
                  (<= 0 (ifix i))
                  (< (ifix i) m))
             (equal (logcollapse (integer-length m) i)
                    (ifix i)))
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


  (local (defthm loghead-of-logapp-when-full-width-<=-concat-width
           (implies (<= (nfix full-width) (nfix concat-width))
                    (equal (loghead full-width (logapp concat-width x y))
                           (loghead full-width x)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))

  ;; (local (defthm nfixes-<=-implies-nfix-<=-ifix
  ;;          (implies (< (nfix x) (nfix y))
  ;;                   (< (nfix x) (ifix y)))
  ;;          :hints(("Goal" :in-theory (enable nfix ifix)))))

  (defthm loghead-of-logapp-logcollapse
    (implies (natp concat-width)
             (equal (loghead full-width (logapp (logcollapse (integer-length (nfix full-width)) concat-width)
                                                x y))
                    (loghead full-width (logapp concat-width x y))))
    :hints (("goal" :cases ((< (nfix concat-width) (nfix full-width)))))
    :otf-flg t)

  (local (defthm logext-of-logapp-when-full-width-<=-concat-width
           (implies (<= (pos-fix full-width) (nfix concat-width))
                    (equal (logext full-width (logapp concat-width x y))
                           (logext full-width x)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))

  (defthm logext-of-logapp-logcollapse
    (implies (natp concat-width)
             (equal (logext full-width (logapp (logcollapse (integer-length (pos-fix full-width)) concat-width)
                                               x y))
                    (logext full-width (logapp concat-width x y))))
    :hints (("goal" :cases ((< (nfix concat-width) (pos-fix full-width)))))
    :otf-flg t)

  (defthm loghead-of-ash-logcollapse
    (implies (natp sh)
             (equal (loghead width (ash x (logcollapse (integer-length (nfix width)) sh)))
                    (loghead width (ash x sh))))
    :hints (("goal" :cases ((< sh (nfix width)))
             :use ((:instance loghead-of-ash-greater
                    (i (nfix width)) (j sh))
                   (:instance loghead-of-ash-greater
                    (i (nfix width)) (j (logcollapse (integer-length (nfix width)) sh))))
             :in-theory (disable loghead-of-ash-greater))))

  (local (in-theory (enable logcdr-<-x-when-positive)))

  (local (defun mask-equiv-ind (mask x y)
           (if (zp mask)
               (list x y)
             (mask-equiv-ind (logcdr mask) (logcdr x) (logcdr y)))))

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




(define limshift-loghead-of-ash ((width natp)
                                 (x integerp)
                                 (shift-amt integerp))
  :returns (shifted integerp :rule-classes :type-prescription)
  :short "Computes (loghead width (ash x shift-amt))."
  (b* ((shift-amt (lifix shift-amt))
       (x (lifix x))
       (width (lnfix width))
       ((when (< shift-amt 0))
        (loghead width (logtail (- shift-amt) x)))
       (shift-amt-limited (logcollapse (integer-length width) shift-amt)))
    (loghead width (ash x shift-amt-limited)))
  ///
  (defthm limshift-loghead-of-ash-correct
    (equal (limshift-loghead-of-ash width x shift-amt)
           (loghead width (ash x shift-amt)))))


(define limshift-loghead-of-logapp ((full-width natp)
                           (concat-width natp)
                           (x integerp)
                           (y integerp))
  :returns (shifted integerp :rule-classes :type-prescription)
  :short "Computes (loghead full-width (logapp concat-width x y))."
  (b* ((concat-width (lnfix concat-width))
       (full-width (lnfix full-width))
       (x (lifix x))
       (y (lifix y))
       (concat-width-limited (logcollapse (integer-length full-width) concat-width)))
    (loghead full-width (logapp concat-width-limited x y)))
  ///
  (defthm limshift-loghead-of-logapp-correct
    (equal (limshift-loghead-of-logapp full-width concat-width x y)
           (loghead full-width (logapp concat-width x y)))))

(define limshift-logext-of-logapp ((full-width posp)
                          (concat-width natp)
                          (x integerp)
                          (y integerp))
  :returns (shifted integerp :rule-classes :type-prescription)
  :short "Computes (loghead full-width (logapp concat-width x y))."
  (b* ((concat-width (lnfix concat-width))
       (full-width (lposfix full-width))
       (x (lifix x))
       (y (lifix y))
       (concat-width-limited (logcollapse (integer-length full-width) concat-width)))
    (logext full-width (logapp concat-width-limited x y)))
  ///

  (local (defthm limshift-logext-of-pos-fix
           (equal (logext (pos-fix w) x)
                  (logext w x))
           :hints(("Goal" :expand ((:free (w) (logext w x)))
                   :in-theory (enable pos-fix)))))

  (defthm limshift-logext-of-logapp-correct
    (equal (limshift-logext-of-logapp full-width concat-width x y)
           (logext full-width (logapp concat-width x y)))))



