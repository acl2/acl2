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

; fast-part-select.lisp
; Original author: Sol Swords <sswords@centtech.com>

(in-package "BITOPS")

(include-book "std/bitsets/bignum-extract" :dir :system)
(include-book "centaur/fty/fixequiv" :dir :system)
(include-book "std/basic/arith-equiv-defs" :dir :system)
(include-book "part-select")
(local (include-book "ihsext-basics"))

(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable (tau-system)
                           acl2::loghead-identity
                           acl2::logtail-identity)))
(local (in-theory (disable ;; acl2::cancel_times-equal-correct
                           ;; acl2::cancel_plus-equal-correct
                           ; acl2::logior-natp-type
                           bitops::logxor-natp-type-2
                           bitops::logior-<-0-linear-2
                           bitops::lognot-negp
                           logmask
                           unsigned-byte-p)))


(local (defthm logcdr-posp
         (implies (<= 2 (ifix x))
                  (posp (logcdr x)))
         :rule-classes(:rewrite
                       (:linear :corollary (implies (<= 2 (ifix x))
                                                    (<= 1 (logcdr x)))))))
(local (defthm logcdr-less-when-posp
         (implies (posp x)
                  (< (logcdr x) x))
         :hints (("goal" :use ((:instance logcons-destruct))
                  :in-theory (e/d (logcons) (logcons-destruct))))
         :rule-classes :linear))


(define fast-psel-rec ((x integerp)
                       (low-slice natp)
                       (slices posp)
                       (low-omit natp)
                       (high-omit natp))
  :guard (and (unsigned-byte-p 5 low-omit)
              (unsigned-byte-p 5 high-omit)
              (or (< 1 slices)
                  (unsigned-byte-p 5 (+ low-omit high-omit))))
  :measure (lposfix slices)
  :verify-guards nil
  :returns (part-select natp :rule-classes :type-prescription)
  (b* ((slices (lposfix slices))
       ((when (eql 1 slices))
        (b* ((slice (bitsets::bignum-extract x low-slice)))
          (loghead (- 32 (+ (lnfix low-omit) high-omit))
                   (logtail low-omit slice))))
       (half (logcdr slices))
       (low
        (fast-psel-rec x low-slice half low-omit 0))
       (middle-slice (+ low-slice half))
       (other-half (- slices half))
       (high
        (fast-psel-rec x middle-slice other-half 0 high-omit)))
    (mbe :logic (logapp (- (* 32 half) low-omit) low high)
         :exec (logior low (ash high (- (* 32 half) low-omit)))))
  ///

  (local (defthm equal-of-logapp-split
           (equal (equal (logapp w x y) z)
                  (and (integerp z)
                       (equal (loghead w x) (loghead w z))
                       (equal (ifix y) (logtail w z))))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))

  (local (in-theory (enable loghead-of-loghead-split)))

  (defthmd loghead-of-logtail
     (equal (loghead w (logtail n x))
            (logtail n (loghead (+ (nfix w) (nfix n)) x)))
     :hints(("Goal" :in-theory (enable* ihsext-inductions ihsext-recursive-redefs))))

  (local (defthm loghead-of-equal-loghead
           (implies (equal x (loghead n y))
                    (equal (loghead n x)
                           (loghead n y)))))

  (local (in-theory (enable bitsets::bignum-extract)))

  (defret fast-psel-rec-correct
    (implies (and (natp low-omit)
                  (natp high-omit)
                  (posp slices)
                  (natp low-slice)
                  (< low-omit 32)
                  (< high-omit 32)
                  (or (< 1 slices)
                      (< (+ low-omit high-omit) 32)))
             (equal part-select
                    (loghead (- (* 32 slices)
                                (+ low-omit high-omit))
                             (logtail (+ (* 32 low-slice) low-omit) x))))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:in-theory (e/d (loghead-of-logtail)
                                   (logtail-of-loghead))))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (logtail-of-loghead)
                                   (loghead-of-logtail))))))

  (verify-guards fast-psel-rec
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable unsigned-byte-p))))))

(local (defthmd logapp-in-terms-of-logior
         (equal (logapp w x y)
                (logior (loghead w x)
                        (ash y (nfix w))))
         :hints(("Goal" :in-theory (enable* ihsext-inductions
                                            ihsext-recursive-redefs)))))


(define fast-psel-rec-middle ((x integerp)
                              (low-slice natp)
                              (slices posp))
  :guard-hints (("goal" :expand ((fast-psel-rec x low-slice slices 0 0))
                 :in-theory (e/d (bitsets::bignum-extract
                                  fast-psel-rec-middle)
                                 (fast-psel-rec-correct)))
                (and stable-under-simplificationp
                     '(:in-theory (enable fast-psel-rec-correct logapp-in-terms-of-logior))))
  :enabled t
  (mbe :logic (fast-psel-rec x low-slice slices 0 0)
       :exec (b* ((slices (lposfix slices))
                  ((when (eql 1 slices))
                   (bitsets::bignum-extract x low-slice))
                  (half (logcdr slices))
                  (low
                   (fast-psel-rec-middle x low-slice half))
                  (middle-slice (+ low-slice half))
                  (other-half (- slices half))
                  (high
                   (fast-psel-rec-middle x middle-slice other-half)))
               (logior low (ash high (* 32 half))))))


(define fast-psel-rec-low ((x integerp)
                           (low-slice natp)
                           (slices posp)
                           (low-omit natp))
  :guard (unsigned-byte-p 5 low-omit)
  :guard-hints (("goal" :expand ((fast-psel-rec x low-slice slices low-omit 0))
                 :in-theory (e/d (bitsets::bignum-extract
                                  fast-psel-rec-low)
                                 (fast-psel-rec-correct)))
                (and stable-under-simplificationp
                     '(:in-theory (enable fast-psel-rec-correct
                                          logapp-in-terms-of-logior
                                          unsigned-byte-p))))
  :enabled t
  (mbe :logic (fast-psel-rec x low-slice slices low-omit 0)
       :exec (b* ((slices (lposfix slices))
                  ((when (eql 1 slices))
                   (logtail low-omit (bitsets::bignum-extract x low-slice)))
                  (half (logcdr slices))
                  (low
                   (fast-psel-rec-low x low-slice half low-omit))
                  (middle-slice (+ low-slice half))
                  (other-half (- slices half))
                  (high
                   (fast-psel-rec-middle x middle-slice other-half)))
               (logior low (ash high (- (* 32 half) low-omit))))))


(define fast-psel-rec-high ((x integerp)
                            (low-slice natp)
                            (slices posp)
                            (high-omit natp))
  :guard (unsigned-byte-p 5 high-omit)
  :guard-hints (("goal" :expand ((fast-psel-rec x low-slice slices 0 high-omit))
                 :in-theory (e/d (bitsets::bignum-extract
                                  fast-psel-rec-high)
                                 (fast-psel-rec-correct)))
                (and stable-under-simplificationp
                     '(:in-theory (enable fast-psel-rec-correct
                                          logapp-in-terms-of-logior
                                          unsigned-byte-p))))
  :enabled t
  (mbe :logic (fast-psel-rec x low-slice slices 0 high-omit)
       :exec (b* ((slices (lposfix slices))
                  ((when (eql 1 slices))
                   (loghead (- 32 high-omit) (bitsets::bignum-extract x low-slice)))
                  (half (logcdr slices))
                  (low
                   (fast-psel-rec-middle x low-slice half))
                  (middle-slice (+ low-slice half))
                  (other-half (- slices half))
                  (high
                   (fast-psel-rec-high x middle-slice other-half high-omit)))
               (logior low (ash high (* 32 half))))))

(define fast-psel ((x integerp)
                   (low-slice natp)
                   (slices posp)
                   (low-omit natp)
                   (high-omit natp))
  :guard (and (unsigned-byte-p 5 low-omit)
              (unsigned-byte-p 5 high-omit)
              (or (< 1 slices)
                  (unsigned-byte-p 5 (+ low-omit high-omit))))
  :guard-hints (("goal" :expand ((fast-psel-rec x low-slice slices low-omit high-omit))
                 :in-theory (e/d (bitsets::bignum-extract
                                  fast-psel)
                                 (fast-psel-rec-correct)))
                (and stable-under-simplificationp
                     '(:in-theory (enable fast-psel-rec-correct
                                          logapp-in-terms-of-logior
                                          unsigned-byte-p))))
  :enabled t
  (mbe :logic (fast-psel-rec x low-slice slices low-omit high-omit)
       :exec
       (b* ((slices (lposfix slices))
            ((when (eql 1 slices))
             (b* ((slice (bitsets::bignum-extract x low-slice)))
               (loghead (- 32 (+ (lnfix low-omit) high-omit))
                        (logtail low-omit slice))))
            (half (logcdr slices))
            (low
             (fast-psel-rec-low x low-slice half low-omit))
            (middle-slice (+ low-slice half))
            (other-half (- slices half))
            (high
             (fast-psel-rec-high x middle-slice other-half high-omit)))
         (logior low (ash high (- (* 32 half) low-omit))))))

(local (defthm logext-of-loghead
         (implies (<= (pos-fix w1) (nfix w2))
                  (equal (logext w1 (loghead w2 x))
                         (logext w1 x)))
         :hints(("Goal" :in-theory (enable* ihsext-inductions
                                            ihsext-recursive-redefs)))))


(local (fty::deffixcong pos-equiv equal (logext n x) n
         :hints(("Goal" :in-theory (enable* ihsext-inductions
                                            ihsext-recursive-redefs
                                            pos-fix)))))
(local (defthm logext-of-logapp-split
         (equal (logext w1 (logapp w2 x y))
                (if (<= (pos-fix w1) (nfix w2))
                    (logext w1 x)
                  (logapp w2 x (logext (- (pos-fix w1) (nfix w2)) y))))
         :hints(("Goal" :in-theory (enable* ihsext-inductions
                                            ihsext-recursive-redefs
                                            pos-fix)))))

(define fast-pext-rec-high ((x integerp)
                            (low-slice natp)
                            (slices posp)
                            (high-omit natp))
  :guard (unsigned-byte-p 5 high-omit)
  :guard-hints (("goal" :expand ((fast-psel-rec x low-slice slices 0 high-omit))
                 :in-theory (e/d (bitsets::bignum-extract
                                  fast-pext-rec-high)
                                 (fast-psel-rec-correct)))
                (and stable-under-simplificationp
                     '(:in-theory (enable fast-psel-rec-correct
                                          unsigned-byte-p)))
                (and stable-under-simplificationp
                     '(:in-theory (enable logapp-in-terms-of-logior))))
  :enabled t
  (mbe :logic (logext (- (* 32 slices) high-omit)
                      (fast-psel-rec x low-slice slices 0 high-omit))
       :exec (b* ((slices (lposfix slices))
                  ((when (eql 1 slices))
                   (logext (- 32 high-omit) (bitsets::bignum-extract x low-slice)))
                  (half (logcdr slices))
                  (low
                   (fast-psel-rec-middle x low-slice half))
                  (middle-slice (+ low-slice half))
                  (other-half (- slices half))
                  (high
                   (fast-pext-rec-high x middle-slice other-half high-omit)))
               (logior low (ash high (* 32 half))))))

(define fast-pext ((x integerp)
                   (low-slice natp)
                   (slices posp)
                   (low-omit natp)
                   (high-omit natp))
  :guard (and (unsigned-byte-p 5 low-omit)
              (unsigned-byte-p 5 high-omit)
              (or (< 1 slices)
                  (unsigned-byte-p 5 (+ low-omit high-omit))))
  :guard-hints (("goal" :expand ((fast-psel-rec x low-slice slices low-omit high-omit))
                 :in-theory (e/d (bitsets::bignum-extract
                                  fast-psel)
                                 (fast-psel-rec-correct)))
                (and stable-under-simplificationp
                     '(:in-theory (enable fast-psel-rec-correct
                                          logapp-in-terms-of-logior
                                          unsigned-byte-p))))
  :enabled t
  (mbe :logic (logext (- (* 32 slices) (+ low-omit high-omit))
                      (fast-psel-rec x low-slice slices low-omit high-omit))
       :exec
       (b* ((slices (lposfix slices))
            ((when (eql 1 slices))
             (b* ((slice (bitsets::bignum-extract x low-slice)))
               (logext (- 32 (+ (lnfix low-omit) high-omit))
                       (logtail low-omit slice))))
            (half (logcdr slices))
            (low
             (fast-psel-rec-low x low-slice half low-omit))
            (middle-slice (+ low-slice half))
            (other-half (- slices half))
            (high
             (fast-pext-rec-high x middle-slice other-half high-omit)))
         (logior low (ash high (- (* 32 half) low-omit))))))



(local
 (defsection fast-part-select-prep
   (defret fast-psel-rec-correct-force
     (implies (force (and (natp low-omit)
                          (natp high-omit)
                          (posp slices)
                          (natp low-slice)
                          (< low-omit 32)
                          (< high-omit 32)
                          (or (< 1 slices)
                              (< (+ low-omit high-omit) 32))))
              (equal part-select
                     (loghead (- (* 32 slices)
                                 (+ low-omit high-omit))
                              (logtail (+ (* 32 low-slice) low-omit) x))))
     :fn fast-psel-rec)
   (defthmd ash-logtail
     (implies (natp n)
              (equal (ash (logtail n x) n)
                     (- (ifix x) (loghead n x))))
     :hints(("Goal" :in-theory (enable* ihsext-inductions
                                        ihsext-recursive-redefs
                                        equal-logcons-strong
                                        logcdr-of-+
                                        logcar-of-+)
             :induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable minus-to-lognot
                                      logcdr-of-+
                                      b-not)))))
   (defthm logtail-5-times-32
     (equal (* 32 (logtail 5 x))
            (- (ifix x) (loghead 5 x)))
     :hints (("goal" :use ((:instance ash-logtail (n 5)))
              :in-theory (enable ash-is-expt-*-x))))

   (defthm logtail-n-monotonic
     (implies (<= (ifix x) (ifix y))
              (<= (logtail n x) (logtail n y)))
     :hints (("goal" :in-theory (enable* ihsext-inductions
                                         ihsext-recursive-redefs))))

   (defthm greater-implies-logtail-or-loghead-greater
     (implies (and (natp x) (natp y)
                   (< x y))
              (or (< (logtail n x) (logtail n y))
                  (and (equal (logtail n x) (logtail n y))
                       (< (loghead n x) (loghead n y)))))
     :hints(("Goal" :in-theory (enable* ihsext-inductions ihsext-recursive-redefs)))
     :rule-classes nil) 

   (defthm unsigned-byte-p-5-of-31-minus
     (implies (unsigned-byte-p 5 x)
              (unsigned-byte-p 5 (- 31 x)))
     :hints(("Goal" :in-theory (enable unsigned-byte-p))))

   (defthm unsigned-byte-p-5-implies-less-than-32
     (implies (unsigned-byte-p 5 x)
              (<= x 31))
     :hints(("Goal" :in-theory (enable unsigned-byte-p))))

   (defthm unsigned-byte-diff
     (implies (and (unsigned-byte-p 5 x)
                   (unsigned-byte-p 5 y)
                   (<= x y))
              (unsigned-byte-p 5 (+  31 x (- y))))
     :hints(("Goal" :in-theory (enable unsigned-byte-p))))

   (defthm loghead-5-less-than-32
     (< (loghead 5 x) 32)
     :hints (("goal" :use ((:instance unsigned-byte-p-of-loghead
                            (size1 5) (size 5) (i x)))
              :in-theory (e/d (unsigned-byte-p)
                              (unsigned-byte-p-of-loghead)))))))




(define fast-part-select ((x integerp :type integer)
                          (width natp :type (integer 0 *))
                          (low natp :type (integer 0 *)))
  :split-types t
  :enabled t
  :inline t
  :guard-hints (("goal" :in-theory (enable part-select-width-low))
                (and stable-under-simplificationp
                     '(:cases ((equal width 1))))
                (and stable-under-simplificationp
                     '(:use ((:instance greater-implies-logtail-or-loghead-greater
                              (x low) (y (+ -1 low width)) (n 5))))))
  :guard-debug t
  :parents (bitops)
  :short "Optimized function for selecting a bit range from a big integer."
  :long "<p>Suppose you have a large (perhaps millions of bits) bignum, and you
want to extract a small range (maybe only a few thousand bits) from somewhere
in the middle.  Using regular ACL2 primitives like logand and ash, you don't
have any good options that don't require copying a much larger portion of the
number.  You either have to truncate the big number to the end of the range you
want (which may yield a large bignum) and then shift it into place, or else
shift the lowest bit into place (which may yield a large bignum) and then
truncate it to the width you want.  One option requires making a new bignum
that is @('lsb + width - 1') bits, the other requires making a new bignum that
is @('origwidth - lsb') bits.  Depending on what range you want to extract,
sometimes one or the other of these options is small enough, but in some cases
neither is palatable.</p>

<p>Fast-part-select is based on @(see bitsets::bignum-extract), which extracts
a 32-bit slice from a bignum.  It has an optimized implementation on CCL that
simply grabs the appropriate array element from within the bignum
representation.  Fast-part-select stitches together the required range from
these 32-bit slices.  It isn't particularly efficient if the width of the
selection is large, but it is independent of the width of the input integer
from which we're selecting and the bit offset at which we're selecting.</p>

<p>It's kind of a pity to have to use this; it would be nice if Lisps had
efficient implementations of the Common Lisp @('ldb') operator and we could
just use that instead.</p>

<p>Note: For good performance, it is important to use the raw Lisp definition
of bignum-extract, loaded by including the book
\"std/bitsets/bignum-extract-opt\".</p>

<p>See also @(see fast-part-extend), which performs the same operation but
returns the range sign-extended instead of zero-extended.</p>"
  (mbe :logic (part-select-width-low x width low)
       :exec (b* ((width (lnfix width))
                  (low (lnfix low))
                  ((when (eql width 0)) 0)
                  (low-slice (ash low -5))
                  (low-omit (logand #x1f low))
                  (high (+ -1 low width))
                  (high-slice (ash high -5))
                  (high-omit (- 31 (logand #x1f high)))
                  (slices (+ 1 (- high-slice low-slice))))
               (fast-psel x low-slice slices low-omit high-omit))))




(define fast-part-extend ((x integerp :type integer)
                          (width posp :type (integer 0 *))
                          (low natp :type (integer 0 *)))
  :split-types t
  :enabled t
  :inline t
  :guard-hints (("goal" :in-theory (enable part-select-width-low))
                (and stable-under-simplificationp
                     '(:cases ((equal width 1))))
                (and stable-under-simplificationp
                     '(:use ((:instance greater-implies-logtail-or-loghead-greater
                              (x low) (y (+ -1 low width)) (n 5))))))
  :guard-debug t
  :parents (fast-part-select)
  :short "Optimized function for selecting a signed bit range from a big integer."
  :long "<p>This is the same as @(see fast-part-select), but it returns a
sign-extended range instead of a zero-extended one.  Its implementation is more
efficient than applying @(see logext) to the result of @(see
fast-part-select).</p>"
  (mbe :logic (logext width (part-select-width-low x (pos-fix width) low))
       :exec (b* ((width (lposfix width))
                  (low (lnfix low))
                  (low-slice (ash low -5))
                  (low-omit (logand #x1f low))
                  (high (+ -1 low width))
                  (high-slice (ash high -5))
                  (high-omit (- 31 (logand #x1f high)))
                  (slices (+ 1 (- high-slice low-slice))))
               (fast-pext x low-slice slices low-omit high-omit))))


