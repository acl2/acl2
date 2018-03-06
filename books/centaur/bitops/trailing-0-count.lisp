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


; trailing-0-count.lisp
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "BITOPS")
(include-book "std/bitsets/bignum-extract" :dir :system)
(include-book "centaur/fty/fixequiv" :dir :system)
(include-book "std/basic/arith-equiv-defs" :dir :system)
(local (include-book "ihsext-basics"))
;; (local (include-book "equal-by-logbitp"))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable (tau-system)
                           acl2::loghead-identity
                           acl2::logtail-identity)))
(local (in-theory (disable acl2::cancel_times-equal-correct
                           acl2::cancel_plus-equal-correct
                           ; acl2::logior-natp-type
                           bitops::logxor-natp-type-2
                           bitops::logior-<-0-linear-2
                           bitops::lognot-negp
                           logmask
                           unsigned-byte-p)))

;; (local (defthm logior-same-2
;;          (equal (logior x (logior x y))
;;                 (logior x y))
;;          :hints((bitops::logbitp-reasoning))))

;; (local (defthm logand-same-2
;;          (equal (logand x (logand x y))
;;                 (logand x y))
;;          :hints((bitops::logbitp-reasoning))))


;; (local (defthm logxor-self
;;          (equal (logxor x x) 0)))

;; (def-svex-rewrite unsigned-not-less-than-0
;;   :lhs (< (concat n x 0) 0)
;;   :rhs (xdet (bitxor (concat n x 0) (concat n x 0)))
;;   :hints(("Goal" :in-theory (enable svex-apply 4vec-< 4vec-concat
;;                                     4vec-bitxor 4vec-xdet))))


(define find-bit ((x :type (unsigned-byte 32)))
  :inline t
  (b* ((x (lnfix x))
       ((the (unsigned-byte 5) x16) (ash (the bit (if (eql 0 (the (unsigned-byte 32) (logand x #x0000FFFF))) 1 0)) 4))
       ((the (unsigned-byte 4) x8)  (ash (the bit (if (eql 0 (the (unsigned-byte 32) (logand x #x00FF00FF))) 1 0)) 3))
       ((the (unsigned-byte 3) x4)  (ash (the bit (if (eql 0 (the (unsigned-byte 32) (logand x #x0F0F0F0F))) 1 0)) 2))
       ((the (unsigned-byte 2) x2)  (ash (the bit (if (eql 0 (the (unsigned-byte 32) (logand x #x33333333))) 1 0)) 1))
       ((the (unsigned-byte 1) x1)  (the bit (if (eql 0 (the (unsigned-byte 32) (logand x #x55555555))) 1 0))))
    (the (unsigned-byte 32)
         (logior
          (the (unsigned-byte 32) x16)
          (the (unsigned-byte 32)
               (logior
                (the (unsigned-byte 32) x8)
                (the (unsigned-byte 32)
                     (logior
                      (the (unsigned-byte 32) x4)
                      (the (unsigned-byte 32)
                           (logior
                            (the (unsigned-byte 32) x2)
                            (the (unsigned-byte 32) x1))))))))))
  ///
  (local (defun test-find-bit (limit)
           (if (zp limit)
               t
             (and (let ((x (1- limit)))
                    (equal (find-bit (ash 1 x)) x))
                  (test-find-bit (1- limit))))))

  (local (defthm find-bit-by-test-find-bit
           (implies (and (test-find-bit limit)
                         (natp n)
                         (< n (nfix limit)))
                    (equal (find-bit (ash 1 n)) n))
           :hints(("Goal" :in-theory (disable find-bit)))))


  (defthm find-bit-of-ash-1
    (implies (and (natp n)
                  (< n 32))
             (equal (find-bit (ash 1 n))
                    n))
    :hints (("goal" :in-theory (disable find-bit test-find-bit)
             :use ((:instance find-bit-by-test-find-bit
                    (limit 32)))))))



(local (defthm integer-length-when-loghead/logtail
         (implies (and (not (equal 0 (logtail n x)))
                       (equal 0 (loghead m (logtail n x)))
                       (posp m) (natp n))
                  (<= (+ m n) (integer-length x)))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)
                 :induct (logtail n x)))))
(local (defthm logtail-nonzero-lemma
         (implies (and (not (equal 0 (logtail n x)))
                       (equal 0 (loghead m (logtail n x)))
                       (posp m) (natp n))
                  (not (equal 0 (logtail (+ m n) x))))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)
                 :induct (logtail n x)))))
(local (defthm integer-length-when-bignum-extract
         (implies (and (not (equal 0 (logtail (* 32 (nfix idx)) x)))
                       (equal 0 (bitsets::bignum-extract x idx)))
                  (<= (+ 32 (* 32 (nfix idx))) (integer-length x)))
         :hints(("Goal" :in-theory (enable bitsets::bignum-extract)))
         :rule-classes :linear))
(local (defthm logtail-nonzero-bignum-extract
         (implies (and (not (equal 0 (logtail (* 32 idx) x)))
                       (equal 0 (bitsets::bignum-extract x idx))
                       (natp idx))
                  (not (equal 0 (logtail (+ 32 (* 32 idx)) x))))
         :hints(("Goal" :in-theory (enable bitsets::bignum-extract)))))
(local (defthm loghead-zero-compose
         (implies (and (equal 0 (loghead n x))
                       (equal 0 (loghead m (logtail n x)))
                       (natp m) (natp n))
                  (equal (loghead (+ m n) x) 0))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)
                 :induct (logtail n x)))))



(local (defthm integer-length-when-loghead/logtail-neg
         (implies (and (not (equal -1 (logtail n x)))
                       (equal (logmask m) (loghead m (logtail n x)))
                       (posp m) (natp n))
                  (<= (+ m n) (integer-length x)))
         :hints(("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                          bitops::ihsext-recursive-redefs))
                 :induct (logtail n x)))))

(local (defthm logcar-logcdr-lemma
         (implies (and (equal (logcar x) 1)
                       (equal (logcdr x) -1))
                  (equal (equal x -1) t))
         :hints(("Goal" ;; :cases ((integerp x))
                 :in-theory (disable logcar-logcdr-elim
                                     logcons-destruct)
                 :use ((:instance logcons-destruct))))))

(local (defthm logtail-not-neg1-lemma1
         (implies (and (not (equal (ifix x) -1))
                       (equal (logmask m) (loghead m x)))
                  (not (equal -1 (logtail m x))))
         :hints(("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                          bitops::ihsext-recursive-redefs))
                 :induct (logtail m x)))))
         

(local (defthm logtail-non-neg1-lemma
         (implies (and (not (equal -1 (logtail n x)))
                       (equal (logmask m) (loghead m (logtail n x)))
                       (posp m) (natp n))
                  (not (equal -1 (logtail (+ m n) x))))
         :hints(("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                          bitops::ihsext-recursive-redefs))
                 :induct (logtail n x)))))

(local (defthm integer-length-when-bignum-extract-neg
         (implies (and (not (equal -1 (logtail (* 32 (nfix idx)) x)))
                       (equal #xffffffff (bitsets::bignum-extract x idx)))
                  (<= (+ 32 (* 32 (nfix idx))) (integer-length x)))
         :hints(("Goal" :in-theory (enable bitsets::bignum-extract)))
         :rule-classes :linear))
(local (defthm logtail-nonzero-bignum-extract-neg
         (implies (and (not (equal -1 (logtail (* 32 idx) x)))
                       (equal #xffffffff (bitsets::bignum-extract x idx))
                       (natp idx))
                  (not (equal -1 (logtail (+ 32 (* 32 idx)) x))))
         :hints(("Goal" :in-theory (enable bitsets::bignum-extract)))))
(local (defthm loghead-mask-compose
         (implies (and (equal (logmask n) (loghead n x))
                       (equal (logmask m) (loghead m (logtail n x)))
                       (natp m) (natp n))
                  (equal (loghead (+ m n) x) (logmask (+ m n))))
         :hints(("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                          bitops::ihsext-recursive-redefs))
                 :induct (logtail n x)))))


(define trailing-0-count-32 ((x :type (unsigned-byte 32)))
  ;; :prepwork ((local (in-theory (disable unsigned-byte-p
  ;;                                       signed-byte-p)))
  ;;            (local (include-book "centaur/bitops/signed-byte-p" :dir :system)))
  ;; :guard (not (eql 0 x))
  :prepwork ((local (in-theory (enable unsigned-byte-p))))
  (b* ((x (lnfix x))
       ((the (unsigned-byte 32) x)
        (the (unsigned-byte 32) (logand x (the (signed-byte 33) (- x))))))
    (find-bit x))
  ///
  (fty::deffixequiv trailing-0-count-32 :args ((x natp))))

(define trailing-1-count-32  ((x :type (unsigned-byte 32)))
  :inline t
  :prepwork ((local (in-theory (enable unsigned-byte-p))))
  (trailing-0-count-32
   (the (unsigned-byte 32)
        (logand #xffffffff
                (the (signed-byte 33) (lognot (the (unsigned-byte 32) (lnfix x)))))))
  ///
  (fty::deffixequiv trailing-0-count-32 :args ((x natp))))


(fty::deffixequiv bitsets::bignum-extract :args ((x integerp) (bitsets::slice natp)))

(define trailing-0-count-rec ((x integerp)
                              (slice-idx natp))
  :guard (not (equal 0 (logtail (* 32 slice-idx) x)))
  :measure (nfix (- (integer-length x) (* 32 (nfix slice-idx))))
  :prepwork ()
  (b* (((unless (mbt (not (equal 0 (logtail (* 32 (nfix slice-idx)) x)))))
        0)
       (slice-idx (lnfix slice-idx))
       (slice (bitsets::bignum-extract x slice-idx))
       ((when (eql 0 slice))
        (trailing-0-count-rec x (+ 1 slice-idx)))
       (slice-trailing-0-count (trailing-0-count-32 slice)))
    (+ slice-trailing-0-count (* 32 slice-idx))))

(define trailing-1-count-rec ((x integerp)
                              (slice-idx natp))
  :guard (not (equal -1 (logtail (* 32 slice-idx) x)))
  :measure (nfix (- (integer-length x) (* 32 (nfix slice-idx))))
  :prepwork ()
  (b* (((unless (mbt (not (equal -1 (logtail (* 32 (nfix slice-idx)) x)))))
        0)
       (slice-idx (lnfix slice-idx))
       (slice (bitsets::bignum-extract x slice-idx))
       ((when (eql #xffffffff slice))
        (trailing-1-count-rec x (+ 1 slice-idx)))
       (slice-trailing-1-count (trailing-1-count-32 slice)))
    (+ slice-trailing-1-count (* 32 slice-idx)))
  ///
  (local (defthm loghead-of-lognot-equal-0
           (equal (equal 0 (loghead n (lognot x)))
                  (equal (logmask n) (loghead n x)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))
  
  (defthm trailing-1-count-rec-is-trailing-0-count-rec-of-lognot
    (equal (trailing-1-count-rec x slice-idx)
           (trailing-0-count-rec (lognot x) slice-idx))
    :hints(("Goal" :in-theory (enable trailing-0-count-rec
                                      trailing-1-count-32
                                      bitsets::bignum-extract)))))

(define trailing-0-count ((x integerp))
  :parents (bitops)
  :short "Optimized trailing 0 count for integers."
  :long "<p>To make this fast, be sure and include the
\"std/bitsets/bignum-extract-opt\" book (reqires a ttag), which prevents
this (at least on CCL64) from needing to create new bignums when run on
bignums.</p>"
  :verify-guards nil
  :measure (integer-length x)
  :hints(("Goal" :in-theory (enable integer-length**)))
  (mbe :logic
       (if (or (zip x)
               (logbitp 0 x))
           0
         (+ 1 (trailing-0-count (logcdr x))))
       :exec (if (eql 0 x)
                 0
               (trailing-0-count-rec x 0)))
  ///

  (defthmd trailing-0-count-properties
    (implies (not (zip x))
             (let ((count (trailing-0-count x)))
               (and (logbitp count x)
                    (equal (loghead count x) 0)
                    (implies (< (nfix idx) count)
                             (not (logbitp idx x))))))
    :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                       bitops::ihsext-inductions)
            :induct (logbitp idx x))))

  (local (in-theory (enable trailing-0-count-properties)))

  (local (in-theory (disable unsigned-byte-p)))

  (defthm logand-of-minus-in-terms-of-trailing-0-count
    (implies (not (zip x))
             (equal (logand x (- x))
                    (ash 1 (trailing-0-count x))))
    :hints(("Goal" :induct (trailing-0-count x)
            :in-theory (enable bitops::ash** bitops::minus-to-lognot)
            :expand ((:with bitops::logand** (logand x (+ 1 (lognot x))))))))

  (defthm trailing-0-count-bound
    (implies (posp x)
             (< (trailing-0-count x) (integer-length x)))
    :hints(("Goal" :induct (trailing-0-count x)
            :expand ((:with bitops::integer-length** (integer-length x)))))
    :rule-classes ((:linear :trigger-terms ((trailing-0-count x)))))

  (fty::deffixequiv trailing-0-count))

(local (in-theory (enable trailing-0-count-properties)))

(local
 (defsection trailing-0-count-lemmas



   (defthm integer-length-when-unsigned-byte-p
     (implies (unsigned-byte-p n x)
              (<= (integer-length x) n))
     :hints(("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                      bitops::ihsext-recursive-redefs)
                                     (unsigned-byte-p))))
     :rule-classes :linear)

   (defthm trailing-0-count-32-correct
     (implies (and (unsigned-byte-p 32 x)
                   (not (equal x 0)))
              (equal (trailing-0-count-32 x)
                     (trailing-0-count x)))
     :hints(("Goal" :in-theory (e/d (trailing-0-count-32)
                                    (unsigned-byte-p)))))

   (in-theory (enable trailing-0-count-rec))


   (defthm trailing-0-count-of-loghead
     (implies (not (equal 0 (loghead n x)))
              (equal (trailing-0-count (loghead n x))
                     (trailing-0-count x)))
     :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                        bitops::ihsext-recursive-redefs
                                        trailing-0-count))))

   (defthm trailing-0-count-of-logtail
     (implies (and (equal 0 (loghead n x))
                   (not (equal 0 (logtail n x))))
              (equal (trailing-0-count (logtail n x))
                     (- (trailing-0-count x) (nfix n))))
     :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                        bitops::ihsext-recursive-redefs
                                        trailing-0-count))))

   (defthm not-zip-when-logtail
     (implies (not (equal 0 (logtail n x)))
              (not (zip x)))
     :rule-classes :forward-chaining)

   (defthm trailing-0-count-rec-properties
     (implies (and (not (equal 0 (logtail (* 32 (nfix slice-idx)) x)))
                   (equal 0 (loghead (* 32 (nfix slice-idx)) x)))
              (let ((ans (trailing-0-count-rec x slice-idx)))
                (and (logbitp ans x)
                     (equal (loghead ans x) 0)
                     (implies (< (nfix idx) ans)
                              (not (logbitp idx x))))))
     :hints(("Goal" :in-theory (enable bitsets::bignum-extract))))

   (defthm trailing-0-count-rec-correct
     (implies (and (not (equal 0 (logtail (* 32 (nfix slice-idx)) x)))
                   (equal 0 (loghead (* 32 (nfix slice-idx)) x)))
              (equal (trailing-0-count-rec x slice-idx)
                     (trailing-0-count x)))
     :hints (("goal" :in-theory (disable trailing-0-count-rec
                                         trailing-0-count-rec-properties
                                         trailing-0-count-properties)
              :use ((:instance trailing-0-count-rec-properties
                     (idx (trailing-0-count x)))
                    (:instance trailing-0-count-properties
                     (idx (trailing-0-count-rec x slice-idx)))))))))

(verify-guards trailing-0-count
  :hints(("Goal" :in-theory (enable trailing-0-count))))




(define trailing-1-count ((x integerp))
  :parents (bitops)
  :short "Optimized trailing 0 count for integers."
  :long "<p>To make this fast, be sure and include the
\"std/bitsets/bignum-extract-opt\" book (reqires a ttag), which prevents
this (at least on CCL64) from needing to create new bignums when run on
bignums.</p>"
  :verify-guards nil
  :measure (integer-length x)
  :hints(("Goal" :in-theory (enable integer-length**)))
  (mbe :logic
       (if (or (eql x -1)
               (not (logbitp 0 x)))
           0
         (+ 1 (trailing-1-count (logcdr x))))
       :exec (if (eql -1 x)
                 0
               (trailing-1-count-rec x 0)))
  ///
  (defthm trailing-1-count-is-trailing-0-count-of-lognot
    (equal (trailing-1-count x)
           (trailing-0-count (lognot x)))
    :hints(("Goal" :in-theory (enable* trailing-0-count)
            :induct t
            :expand ((lognot x)))))

  (verify-guards trailing-1-count
    :hints(("Goal" :in-theory (enable trailing-0-count)))))

(define trailing-0-count-from-exec ((x integerp)
                                    (offset natp))
  :inline t
  :enabled t
  :verify-guards nil
  (b* ((offset (lnfix offset))
       (slice1-idx (logtail 5 offset)) ;; (floor offset 32)
       (slice1-offset (loghead 5 offset)) ;; (mod offset 32)
       (slice1 (bitsets::bignum-extract x slice1-idx))
       (slice1-tail (logtail slice1-offset slice1))
       ((when (not (eql 0 slice1-tail)))
        (trailing-0-count-32 slice1-tail))
       ;; What we want now is the trailing-0-count of (logtail x (* 32 (+ 1 slice-idx))).
       ;; This is just (trailing-0-count-rec x (+ 1 slice1-idx)),
       ;; but we need to make sure that this tail of x isn't 0 for the guard.
       ;; think of the case where offset = 0 and x = (ash -1 32) = ...FFFF0000000.
       ;; This has integer-length 32 and trailing-0-count 32
       (len (integer-length x))
       ((when (and (<= len (* 32 (+ 1 slice1-idx)))
                   (not (logbitp (* 32 (+ 1 slice1-idx)) x))))
        0)
       (count2 (trailing-0-count-rec x (+ 1 slice1-idx))))
    (- count2 offset))
  ///


  (local (defthm logtail-nonzero-by-integer-length
           (implies (and (< n (integer-length x))
                         (posp n))
                    (not (equal 0 (logtail n x))))
           :hints (("goal" :in-theory (enable* ihsext-recursive-redefs
                                               ihsext-inductions)))))

  (local (defthm nfix-of-subtract-nats
           (implies (and (natp x)
                         (natp y))
                    (<= (nfix (+ x (- y))) x))
           :hints(("Goal" :in-theory (enable nfix)))))

  (local (defthm logtail-not-zero-when-logbitp
           (implies (and (logbitp m x)
                         (<= (nfix n) (nfix m)))
                    (not (equal 0 (logtail n x))))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))

  (verify-guards trailing-0-count-from-exec$inline
    :hints(("Goal" :in-theory (enable bitsets::bignum-extract)))))

(define trailing-1-count-from-exec ((x integerp)
                               (offset natp))
  :verify-guards nil
  :inline t
  (b* ((offset (lnfix offset))
       (slice1-idx (logtail 5 offset)) ;; (floor offset 32)
       (slice1-offset (loghead 5 offset)) ;; (mod offset 32)
       (slice1 (bitsets::bignum-extract x slice1-idx))
       (slice1-tail (logtail slice1-offset slice1))
       ((when (not (eql slice1-tail (logmask (- 32 slice1-offset)))))
        (trailing-1-count-32 slice1-tail))
       ;; What we want now is the trailing-1-count of (logtail x (* 32 (+ 1 slice-idx))).
       ;; This is just (trailing-1-count-rec x (+ 1 slice1-idx)),
       ;; but we need to make sure that this tail of x isn't -1 for the guard.
       ;; think of the case where offset = 0 and x = (lognot (ash -1 32)) = ...0000FFFFFFFF.
       ;; This has integer-length 32 and trailing-1-count 32
       (len (integer-length x))
       ((when (and (<= len (* 32 (+ 1 slice1-idx)))
                   (logbitp (* 32 (+ 1 slice1-idx)) x)))
        0)
       (count2 (trailing-1-count-rec x (+ 1 slice1-idx))))
    (- count2 offset))
  ///
  (local (defthm logtail-not-neg1-by-integer-length
           (implies (and (< n (integer-length x))
                         (posp n))
                    (not (equal -1 (logtail n x))))
           :hints (("goal" :in-theory (enable* ihsext-recursive-redefs
                                               ihsext-inductions)))))

  (local (defthm nfix-of-subtract-nats
           (implies (and (natp x)
                         (natp y))
                    (<= (nfix (+ x (- y))) x))
           :hints(("Goal" :in-theory (enable nfix)))))

  (local (defthm logtail-not-neg1-when-logbitp
           (implies (and (not (logbitp m x))
                         (<= (nfix n) (nfix m)))
                    (not (equal -1 (logtail n x))))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))

  (local (defthm unsigned-byte-5-lte-32
           (implies (unsigned-byte-p 5 x)
                    (<= x 32))
           :hints(("Goal" :in-theory (enable unsigned-byte-p)))))

  (verify-guards trailing-1-count-from-exec$inline
    :hints(("Goal" :in-theory (enable bitsets::bignum-extract))))

  
  (local (defthm loghead-of-lognot-equal-0
           (equal (equal 0 (loghead n (lognot x)))
                  (equal (logmask n) (loghead n x)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))

  (local (defthm loghead-equal-logmask-dumb
           (implies (and (syntaxp (quotep mask))
                         (equal mask (logmask (integer-length mask)))
                         (<= (nfix n) (integer-length mask))
                         (not (equal (loghead n x) (logmask n))))
                    (not (equal (loghead n x) mask)))
           :hints (("goal" :cases ((equal (nfix n) (integer-length mask)))))))

  (local (defthm trailing-0-count-of-lognot-loghead
           (implies (not (equal (logmask n) (loghead n x)))
                    (equal (trailing-0-count (lognot (loghead n x)))
                           (trailing-0-count (lognot x))))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs
                                              trailing-0-count)))))

  (defthm trailing-1-count-from-exec-is-trailing-0-count-from-exec-of-lognot
    (equal (trailing-1-count-from-exec x offset)
           (trailing-0-count-from-exec (lognot x) offset))
    :hints(("Goal" :in-theory (enable trailing-0-count-from-exec
                                      bitsets::bignum-extract
                                      trailing-1-count-32)))))


(define trailing-0-count-from ((x integerp)
                               (offset natp))
  :verify-guards nil
  :enabled t
  (mbe :logic (trailing-0-count (logtail offset x))
       :exec
       (trailing-0-count-from-exec x offset))
  ///

  (local (in-theory (disable loghead-zero-compose)))

  (local (defthm trailing-0-count-of-logtail-props
           (implies (and (not (equal 0 (logtail n x)))
                         (natp n))
                    (let ((count (trailing-0-count (logtail n x))))
                      (and (logbitp (+ n count) x)
                           (implies (and (< (nfix idx) (+ n count))
                                         (<= n (nfix idx)))
                                    (not (logbitp idx x))))))
           :hints (("goal" :use ((:instance trailing-0-count-properties
                                  (x (logtail n x))
                                  (idx (- (nfix idx) n))))
                    :in-theory (disable trailing-0-count-properties)))))

  (defthm trailing-0-count-rec-bound
    (implies (not (equal 0 (logtail (* 32 (nfix slice-idx)) x)))
             (<= (* 32 (nfix slice-idx))
                 (trailing-0-count-rec x slice-idx)))
    :rule-classes ((:linear :trigger-terms ((trailing-0-count-rec x slice-idx)))))

  (defthm trailing-0-count-rec-props2
    (implies (not (equal 0 (logtail (* 32 (nfix slice-idx)) x)))
             (let ((ans (trailing-0-count-rec x slice-idx)))
               (and (logbitp ans x)
                    (equal (loghead (- ans (* 32 (nfix slice-idx)))
                                    (logtail (* 32 (nfix slice-idx)) x))
                           0)
                    ;; (implies (and (< (nfix idx) ans)
                    ;;               (<= (* 32 (nfix slice-idx)) (nfix idx)))
                    ;;          (not (logbitp idx x)))
                    )))
    :hints(("Goal" :in-theory (enable bitsets::bignum-extract)
            :induct (trailing-0-count-rec x slice-idx))
           (and stable-under-simplificationp
                '(:use ((:instance loghead-zero-compose
                         (m (+ -32 (- (* 32 (nfix slice-idx)))
                               (trailing-0-count-rec x (+ 1 (nfix slice-idx)))))
                         (n 32)
                         (x (logtail (* 32 (nfix slice-idx)) x))))
                  :in-theory (disable loghead-zero-compose)))))

  (defthmd trailing-0-count-rec-props3
    (implies (not (equal 0 (logtail (* 32 (nfix slice-idx)) x)))
             (let ((ans (trailing-0-count-rec x slice-idx)))
               (implies (and (< (nfix idx) ans)
                             (<= (* 32 (nfix slice-idx)) (nfix idx)))
                        (not (logbitp idx x)))))
    :hints(("Goal" :use (trailing-0-count-rec-props2
                         (:instance logbitp-of-loghead-split
                          (pos (- (nfix idx) (* 32 (nfix slice-idx))))
                          (size (- (trailing-0-count-rec x slice-idx)
                                   (* 32 (nfix slice-idx))))
                          (i (logtail (* 32 (nfix slice-idx)) x))))
            :in-theory (disable trailing-0-count-rec-props2
                                logbitp-when-bitmaskp)
            :do-not-induct t)))

  (local (in-theory (enable trailing-0-count-rec-props3)))

  (defthm trailing-0-count-rec-rw2
    (implies (not (equal 0 (logtail (* 32 (nfix slice-idx)) x)))
             (equal (trailing-0-count-rec x slice-idx)
                    (+ (* 32 (nfix slice-idx))
                       (trailing-0-count (logtail (* 32 (nfix slice-idx)) x)))))
     :hints (("goal" :in-theory (disable trailing-0-count-rec
                                         trailing-0-count-rec-properties
                                         trailing-0-count-properties
                                         trailing-0-count-of-logtail-props)
              :use ((:instance trailing-0-count-rec-props2)
                    (:instance trailing-0-count-rec-props3
                     (idx (+ (* 32 (nfix slice-idx))
                             (trailing-0-count (logtail (* 32 (nfix slice-idx)) x)))))
                    (:instance trailing-0-count-properties
                     (idx (- (trailing-0-count-rec x slice-idx) (* 32 (nfix slice-idx))))
                     (x (logtail (* 32 (nfix slice-idx)) x)))))))



  (local (defthm logtail-0-by-integer-length
           (implies (and (equal 0 (loghead m (logtail n x)))
                         (< (integer-length x) (+ m n))
                         (posp m) (natp n))
                    (equal (logtail n x) 0))))

  (local (defthm logtail-nonzero-by-integer-length
           (implies (and (< n (integer-length x))
                         (posp n))
                    (not (equal 0 (logtail n x))))
           :hints (("goal" :in-theory (enable* ihsext-recursive-redefs
                                               ihsext-inductions)))))

  (local (defthm logtail-0-when-loghead-0
           (implies (equal 0 (loghead n x))
                    (equal (equal 0 (logtail n x))
                           (zip x)))
           :hints (("goal" :in-theory (enable* ihsext-recursive-redefs
                                               ihsext-inductions)))))


  (local (in-theory (disable unsigned-byte-p)))

  (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

  (local (defthm offset-components
           (equal (+ (LOGHEAD 5 OFFSET)
                     (* 32 (LOGTAIL 5 OFFSET)))
                  (ifix offset))
           :hints(("Goal" :in-theory (enable loghead logtail mod)))
           :rule-classes (:rewrite :linear)))

  (local (defthm offset-components-2
           (implies (integerp offset)
                    (equal (+ offset (- (LOGHEAD 5 OFFSET)))
                           (* 32 (LOGTAIL 5 OFFSET))))
           :hints(("Goal" :in-theory (enable loghead logtail mod)))))

  (local (defthm offset-components-plus-rest
           (equal (+ (LOGHEAD 5 OFFSET)
                     (* 32 (LOGTAIL 5 OFFSET))
                     c)
                  (+ (ifix offset) c))
           :hints(("Goal" :in-theory (enable loghead logtail mod)))))

  (local (defthm offset-less-than-logtail-plus-32
           (> (+ 32 (* 32 (LOGTAIL 5 OFFSET)))
              (ifix offset))
           :hints(("Goal" :in-theory (enable loghead logtail mod)))
           :rule-classes :linear))

  (local (defthm loghead-5-lt-32
           (< (loghead 5 x) 32)
           :hints(("Goal" :in-theory (enable loghead)))
           :rule-classes :linear))

  (local (defthm loghead-0-when-integer-length-less
           (implies (< (integer-length x) (nfix n))
                    (equal (equal 0 (loghead n x))
                           (zip x)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))
           :otf-flg t))


  (local (defthmd trailing-0-count-of-logtail-when-loghead-0
           (implies (and (equal (loghead n x) 0)
                         (not (zip x)))
                    (equal (trailing-0-count (logtail n x))
                           (- (trailing-0-count x) (nfix n))))
           :hints(("Goal" :in-theory (enable* trailing-0-count
                                              ihsext-inductions
                                              ihsext-recursive-redefs)))))


  (local (defthmd trailing-0-count-unique
           (implies (and (equal 0 (loghead n x))
                         (logbitp n x)
                         (natp n))
                    (equal (equal (trailing-0-count x) n) t))
           :hints (("goal" :use ((:instance trailing-0-count-properties)
                                 (:instance logbitp-of-loghead-split
                                  (pos (trailing-0-count x))
                                  (size n) (i x))
                                 (:instance logbitp-of-loghead-split
                                  (pos n)
                                  (size (trailing-0-count x))
                                  (i x)))
                    :in-theory (enable natp)))))

  (local (defthm logtail-not-zero-when-logbitp
           (implies (and (logbitp m x)
                         (<= (nfix n) (nfix m)))
                    (not (equal 0 (logtail n x))))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))


  (local (defthm logtail-0-when-greater
           (implies (and (equal (logtail n x) 0)
                         (<= (nfix n) (nfix m)))
                    (equal (logtail m x) 0))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))

  (local (defthm loghead-0-when-integer-length-less-2
           (implies (and (<= (integer-length x) (nfix n))
                         (not (logbitp n x)))
                    (equal (equal 0 (loghead n x))
                           (zip x)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))
           :otf-flg t))


  (local (defthm offset-hack
           (implies (integerp offset)
                    (iff (< (+ 32 (- (LOGHEAD 5 OFFSET)))
                            (+ (- OFFSET) (INTEGER-LENGTH X)))
                         (< (+ 32 (* 32 (logtail 5 offset))) (integer-length x))))
           :hints (("goal" :use ((:instance offset-components))
                    :in-theory (disable offset-components
                                        offset-components-2
                                        offset-components-plus-rest)))))

  (defthm trailing-0-count-from-exec-is-trailing-0-count-from
    (equal (trailing-0-count-from-exec x offset)
           (trailing-0-count-from x offset))
    :hints(("Goal" :in-theory (enable bitsets::bignum-extract
                                      trailing-0-count-of-logtail-when-loghead-0))
           (and stable-under-simplificationp
                '(:use ((:instance trailing-0-count-of-logtail-when-loghead-0
                         (n (+ 32 (- (loghead 5 offset))))
                         (x (logtail offset x))))
                  :cases ((posp offset))))
           (and stable-under-simplificationp
                '(:use ((:instance loghead-0-when-integer-length-less-2
                         (x (logtail offset x))
                         (n (+ 32 (- (loghead 5 offset))))))
                  :cases ((zip x))))))

  (in-theory (disable trailing-0-count-from-exec))

  (verify-guards trailing-0-count-from))


(define trailing-1-count-from ((x integerp)
                               (offset natp))
  :enabled t
  (mbe :logic (trailing-1-count (logtail offset x))
       :exec
       (trailing-1-count-from-exec x offset)))










#||
(include-book
 "std/util/defconsts" :dir :system)

(include-book
 "centaur/misc/memory-mgmt" :dir :system)

(define gen-trailing-1-count-numbers ((n natp) (width posp) acc state)
  :prepwork ((local (in-theory (enable random$))))
  (b* (((when (zp n)) (mv acc state))
       ((mv nzeros state) (random$ width state))
       (acc (cons (loghead width (ash -1 nzeros)) acc)))
    (gen-trailing-1-count-numbers (1- n) width acc state)))

(defconsts (*tests* state) (gen-trailing-1-count-numbers 100000 3000 nil state))

(define take-trailing-1-counts ((tests integer-listp) acc)
  (if (atom tests)
      acc
    (take-trailing-1-counts
     (cdr tests)
     (let ((x (car tests)))
       (cons (if (eql x 0) 0 (trailing-1-count (car tests)))
             acc)))))

(value-triple (acl2::set-max-mem
               (* 10 (Expt 2 30))))

;; without optimization: 1.1 sec
(defconsts *res1* (take-trailing-1-counts *tests* nil))

(include-book
 "std/bitsets/bignum-extract-opt" :dir :system)

;; with optimization: 0.06 sec
(defconsts *res2* (take-trailing-1-counts *tests* nil))

||#
