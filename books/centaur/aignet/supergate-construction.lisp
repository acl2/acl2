; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2013 Centaur Technology
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

(in-package "AIGNET")

(include-book "supergate")
(include-book "construction")

(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/resize-list" :Dir :system))
(local (include-book "std/lists/repeat" :Dir :system))

(local (std::add-default-post-define-hook :fix))
             
(local #!satlink
       (fty::deflist lit-list :pred lit-listp :elt-type litp :true-listp t
         :parents (litp)
         :short "List of literals"))


(local (defthm nthcdr-of-len
         (implies (and (<= (len x) (nfix n))
                       (true-listp x))
                  (equal (nthcdr n x) nil))))
(local (defthm nth-of-lit-list-fix
         (implies (< (nfix n) (len x))
                  (equal (nth n (lit-list-fix x))
                         (nth-lit n x)))
         :hints(("Goal" :in-theory (enable nth nth-lit)))))
(local (defthmd equal-of-cons
         (equal (equal a (cons b c))
                (and (consp a)
                     (equal (car a) b)
                     (equal (cdr a) c)))))


(local (defthm len-equal0
         (equal (equal (len x) 0)
                (not (consp x)))))
(local (defthm append-take-nthcdr
         (implies (and (<= (nfix n) (len x))
                       (true-listp x))
                  (equal (append (take n x) (nthcdr n x))
                         x))))
(local (defthm litarr$ap-redef
         (equal (litarr$ap x)
                (lit-listp x))))
(local (defthmd take-of-update-nth-lemma
         (equal (take (+ 1 (nfix n)) (update-nth n v x))
                (append (take n x)
                        (list v)))
         :hints(("Goal" :in-theory (enable update-nth)))))
(local (defthm take-of-update-nth
         (implies (posp n)
                  (equal (take n (update-nth (+ -1 n) v x))
                         (append (take (+ -1 n) x) (list v))))
         :hints (("goal" :use ((:instance take-of-update-nth-lemma
                                (n (+ -1 n))))))))
(local (defthm nthcdr-of-update-nth
         (implies (< (nfix m) (nfix n))
                  (equal (nthcdr n (update-nth m v x))
                         (nthcdr n x)))
         :hints(("Goal" :in-theory (enable update-nth)))))

(define litarr-to-list ((n natp) litarr)
  :guard (<= n (lits-length litarr))
  :enabled t
  :guard-hints(("Goal" :in-theory (enable nthcdr litarr-to-list)))
  :prepwork ((local (in-theory (enable equal-of-cons
                                       nth-lit))))
  (mbe :logic (non-exec (nthcdr n (lit-list-fix litarr)))
       :exec (if (eql n (lits-length litarr))
                 nil
               (cons (get-lit n litarr)
                     (litarr-to-list (1+ (lnfix n)) litarr)))))

(define lit-list-to-litarr ((n natp) (x lit-listp) litarr)
  :guard (<= (+ n (len x)) (lits-length litarr))
  :returns new-litarr
  :enabled t
  :guard-hints (("goal" :in-theory (enable lit-list-to-litarr
                                           nth-lit update-nth-lit)
                 :expand ((update-nth n (car x) litarr))))
  :prepwork ()
  (mbe :logic (non-exec (append (take n litarr)
                                (lit-list-fix x)
                                (nthcdr (+ (len x) (nfix n)) litarr)))
       :exec (if (atom x)
                 litarr
               (let ((litarr (set-lit n (car x) litarr)))
                 (lit-list-to-litarr (1+ (lnfix n)) (cdr x) litarr)))))




(local (defun integer-greater-than-1 (x)
         (and (integerp x)
              (< 1 x))))
(local (defthm integer-greater-than-1-compound-rec
         (equal (integer-greater-than-1 x)
                (and (integerp x)
                     (< 1 x)))
         :rule-classes :compound-recognizer))

(local (defthm pos-fix-equal-1
         (equal (equal (pos-fix x) 1)
                (not (integer-greater-than-1 x)))
         :hints(("Goal" :in-theory (enable pos-fix)))))


(local (defthm lit->var-of-nth
         (equal (lit->var (nth n x))
                (lit->var (nth-lit n x)))
         :hints(("Goal" :in-theory (enable nth-lit)))))


(local (defthm aignet-lit-listp-of-nthcdr
         (implies (aignet-lit-listp x aignet)
                  (aignet-lit-listp (nthcdr n x) aignet))
         :hints(("Goal" :in-theory (enable nthcdr aignet-lit-listp)))))

(local (defthm nthcdr-of-take
         (implies (<= (nfix n) (nfix m))
                  (equal (nthcdr n (take m x))
                         (take (- (nfix m) (nfix n)) (nthcdr n x))))))

(local (defthm aignet-lit-listp-of-take-nthcdr-later
         (implies (and (natp count2) (natp count) (natp start)
                       (<= count2 count)
                       (aignet-lit-listp (take count (nthcdr start x)) aignet))
                  (aignet-lit-listp (take (+ count (- count2))
                                          (nthcdr (+ start count2) x)) aignet))
         :hints (("goal" :use ((:instance aignet-lit-listp-of-nthcdr
                                (x (take count (nthcdr start x)))
                                (n count2)))
                  :in-theory (disable aignet-lit-listp-of-nthcdr)))))

(local (defthm aignet-lit-listp-of-take-nthcdr-later2
         (implies (and (natp count2) (natp count) (natp start)
                       (<= count2 count)
                       (aignet-lit-listp (take count (nthcdr start x)) aignet))
                  (aignet-lit-listp (take (+ count (- count2))
                                          (nthcdr (+ count2 start) x)) aignet))
         :hints (("goal" :use ((:instance aignet-lit-listp-of-nthcdr
                                (x (take count (nthcdr start x)))
                                (n count2)))
                  :in-theory (disable aignet-lit-listp-of-nthcdr)))))

(local (defthm aignet-lit-listp-of-take
         (implies (and (aignet-lit-listp x aignet)
                       (< (nfix n) (len x)))
                  (aignet-lit-listp (take n x) aignet))
         :hints(("Goal" :in-theory (enable aignet-lit-listp)))))

(local (defthm aignet-lit-listp-of-take-less
         (implies (and (aignet-lit-listp (take n x) aignet)
                       (< (nfix m) (nfix n)))
                  (aignet-lit-listp (take m x) aignet))
         :hints(("Goal" :use ((:instance aignet-lit-listp-of-take
                               (x (take n x)) (n m)))
                 :in-theory (disable aignet-lit-listp-of-take)))))

(local (in-theory (enable bitops::logcdr-<-x-when-positive)))

(local (fty::deffixcong satlink::lit-list-equiv satlink::lit-list-equiv (take count x) x))
(local (fty::deffixcong satlink::lit-list-equiv satlink::lit-list-equiv (nthcdr count x) x
         :hints(("Goal" :in-theory (disable acl2::nthcdr-of-cdr)))))



(local (defthm nthcdr-of-nfix
         (equal (nthcdr (nfix n) x)
                (nthcdr n x))))

(local (defthm nth-under-lit-equiv
         (lit-equiv (nth n x)
                    (nth-lit n x))
         :hints(("Goal" :in-theory (enable nth-lit)))))


(local (defthm aignet-eval-conjunction-of-append
         (equal (aignet-eval-conjunction (append x y) invals regvals aignet)
                (b-and (aignet-eval-conjunction x invals regvals aignet)
                       (aignet-eval-conjunction y invals regvals aignet)))
         :hints(("Goal" :in-theory (enable aignet-eval-conjunction)
                 :induct t)
                (and stable-under-simplificationp
                     '(:in-theory (enable b-and))))))

(local (defthm aignet-eval-conjunction-take-decomp
         (implies (<= (nfix n) (len x))
                  (equal (b-and (aignet-eval-conjunction (take n x) invals regvals aignet)
                                (aignet-eval-conjunction (nthcdr n x) invals regvals aignet))
                         (aignet-eval-conjunction x invals regvals aignet)))
         :hints (("goal" :use ((:instance aignet-eval-conjunction-of-append
                                (x (take n (lit-list-fix x)))
                                (y (nthcdr n (lit-list-fix x)))))
                  :in-theory (disable aignet-eval-conjunction-of-append)))))

(local (defthm aignet-eval-conjunction-take-decomp-special
         (implies (and (natp firstcount)
                       (natp count)
                       (<= firstcount count))
                  (equal (b-and (aignet-eval-conjunction (take firstcount (nthcdr start litarr))
                                                         invals regvals aignet)
                                (aignet-eval-conjunction
                                 (take (+ count (- firstcount))
                                       (nthcdr (+ firstcount (nfix start)) litarr))
                                 invals regvals aignet))
                         (aignet-eval-conjunction
                          (take count (nthcdr start litarr))
                          invals regvals aignet)))
         :hints (("goal" :use ((:instance aignet-eval-conjunction-take-decomp
                                (x (take count (nthcdr start litarr)))
                                (n firstcount)))
                  :in-theory (disable aignet-eval-conjunction-take-decomp)))))


(local (defthm aignet-eval-parity-of-append
         (equal (aignet-eval-parity (append x y) invals regvals aignet)
                (b-xor (aignet-eval-parity x invals regvals aignet)
                       (aignet-eval-parity y invals regvals aignet)))
         :hints(("Goal" :in-theory (enable aignet-eval-parity)
                 :induct t)
                (and stable-under-simplificationp
                     '(:in-theory (enable b-xor))))))

(local (defthm aignet-eval-parity-take-decomp
         (implies (<= (nfix n) (len x))
                  (equal (b-xor (aignet-eval-parity (take n x) invals regvals aignet)
                                (aignet-eval-parity (nthcdr n x) invals regvals aignet))
                         (aignet-eval-parity x invals regvals aignet)))
         :hints (("goal" :use ((:instance aignet-eval-parity-of-append
                                (x (take n (lit-list-fix x)))
                                (y (nthcdr n (lit-list-fix x)))))
                  :in-theory (disable aignet-eval-parity-of-append)))))

(local (defthm aignet-eval-parity-take-decomp-special
         (implies (and (natp firstcount)
                       (natp count)
                       (<= firstcount count))
                  (equal (b-xor (aignet-eval-parity (take firstcount (nthcdr start litarr))
                                                         invals regvals aignet)
                                (aignet-eval-parity
                                 (take (+ count (- firstcount))
                                       (nthcdr (+ firstcount (nfix start)) litarr))
                                 invals regvals aignet))
                         (aignet-eval-parity
                          (take count (nthcdr start litarr))
                          invals regvals aignet)))
         :hints (("goal" :use ((:instance aignet-eval-parity-take-decomp
                                (x (take count (nthcdr start litarr)))
                                (n firstcount)))
                  :in-theory (disable aignet-eval-parity-take-decomp)))))

  
(define aignet-hash-and-supergate-aux ((start natp)
                                       (count posp)
                                       litarr
                                       (gatesimp gatesimp-p)
                                       strash aignet)
  :returns (mv (new-lit litp :rule-classes :type-prescription)
               new-strash new-aignet)
  :measure (pos-fix count)
  :guard (and (<= (+ start count) (lits-length litarr))
              (aignet-lit-listp (take count (litarr-to-list start litarr)) aignet))
  :verify-guards nil
  (b* ((count (lposfix count))
       ((when (eql count 1))
        (b* ((aignet (mbe :logic (non-exec (node-list-fix aignet))
                          :exec aignet)))
          (mv (get-lit start litarr) strash aignet)))
       (first-count (logcdr count))
       (second-count (- count first-count))
       ((mv first-lit strash aignet)
        (aignet-hash-and-supergate-aux start first-count litarr gatesimp strash aignet))
       ((mv second-lit strash aignet)
        (aignet-hash-and-supergate-aux
         (+ (lnfix start) first-count) second-count litarr gatesimp strash aignet)))
    (aignet-hash-and first-lit second-lit gatesimp strash aignet))
  ///



  (defret aignet-litp-of-<fn>
    (implies (aignet-lit-listp (take (pos-fix count) (nthcdr start litarr)) aignet)
             (aignet-litp new-lit new-aignet)))



  (def-aignet-preservation-thms aignet-hash-and-supergate-aux)

  (verify-guards aignet-hash-and-supergate-aux
    :hints (("goal" :do-not-induct t)))



  (defret eval-of-<fn>
    (implies (aignet-lit-listp (take (pos-fix count) (nthcdr start litarr)) aignet)
             (equal (lit-eval new-lit invals regvals new-aignet)
                    (aignet-eval-conjunction
                     (take (pos-fix count) (nthcdr start litarr))
                     invals regvals aignet)))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable pos-fix aignet-eval-conjunction)))))

  (def-aignet-preservation-thms aignet-hash-and-supergate-aux)

  
  (defret stype-counts-of-<fn>
    (implies (and (not (equal (stype-fix stype) :and))
                  (not (equal (stype-fix stype) :xor)))
             (equal (stype-count stype new-aignet)
                    (stype-count stype aignet)))))


(define aignet-hash-and-supergate ((lits lit-listp)
                                   (gatesimp gatesimp-p)
                                   strash aignet)
  :returns (mv (new-lit litp :rule-classes :type-prescription)
               new-strash new-aignet)
  :guard (aignet-lit-listp lits aignet)
  :guard-debug t
  (b* (((acl2::local-stobjs litarr)
        (mv new-lit strash aignet litarr))
       (len (len lits))
       ((when (eql len 0))
        (b* ((aignet (mbe :logic (non-exec (node-list-fix aignet))
                          :exec aignet)))
          (mv 1 strash aignet litarr)))
       (litarr (resize-lits len litarr))
       (litarr (lit-list-to-litarr 0 lits litarr))
       ((mv new-lit strash aignet)
        (aignet-hash-and-supergate-aux 0 len litarr gatesimp strash aignet)))
    (mv new-lit strash aignet litarr))
  ///
  (defret aignet-litp-of-<fn>
    (implies (aignet-lit-listp lits aignet)
             (aignet-litp new-lit new-aignet)))

  (defret eval-of-<fn>
    (implies (aignet-lit-listp lits aignet)
             (equal (lit-eval new-lit invals regvals new-aignet)
                    (aignet-eval-conjunction
                     lits invals regvals aignet)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable aignet-eval-conjunction)))))

  (def-aignet-preservation-thms aignet-hash-and-supergate)

  (defret stype-counts-of-<fn>
    (implies (and (not (equal (stype-fix stype) :and))
                  (not (equal (stype-fix stype) :xor)))
             (equal (stype-count stype new-aignet)
                    (stype-count stype aignet)))))




(define aignet-hash-xor-supergate-aux ((start natp)
                                       (count posp)
                                       litarr
                                       (gatesimp gatesimp-p)
                                       strash aignet)
  :returns (mv (new-lit litp :rule-classes :type-prescription)
               new-strash new-aignet)
  :measure (pos-fix count)
  :guard (and (<= (+ start count) (lits-length litarr))
              (aignet-lit-listp (take count (litarr-to-list start litarr)) aignet))
  :verify-guards nil
  (b* ((count (lposfix count))
       ((when (eql count 1))
        (b* ((aignet (mbe :logic (non-exec (node-list-fix aignet))
                          :exec aignet)))
          (mv (get-lit start litarr) strash aignet)))
       (first-count (logcdr count))
       (second-count (- count first-count))
       ((mv first-lit strash aignet)
        (aignet-hash-xor-supergate-aux start first-count litarr gatesimp strash aignet))
       ((mv second-lit strash aignet)
        (aignet-hash-xor-supergate-aux
         (+ (lnfix start) first-count) second-count litarr gatesimp strash aignet)))
    (aignet-hash-xor first-lit second-lit gatesimp strash aignet))
  ///



  (defret aignet-litp-of-<fn>
    (implies (aignet-lit-listp (take (pos-fix count) (nthcdr start litarr)) aignet)
             (aignet-litp new-lit new-aignet)))



  (def-aignet-preservation-thms aignet-hash-xor-supergate-aux)

  (verify-guards aignet-hash-xor-supergate-aux
    :hints (("goal" :do-not-induct t)))



  (defret eval-of-<fn>
    (implies (aignet-lit-listp (take (pos-fix count) (nthcdr start litarr)) aignet)
             (equal (lit-eval new-lit invals regvals new-aignet)
                    (aignet-eval-parity
                     (take (pos-fix count) (nthcdr start litarr))
                     invals regvals aignet)))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable pos-fix aignet-eval-parity)))))

  (def-aignet-preservation-thms aignet-hash-xor-supergate-aux)

  (defret stype-counts-of-<fn>
    (implies (and (not (equal (stype-fix stype) :and))
                  (not (equal (stype-fix stype) :xor)))
             (equal (stype-count stype new-aignet)
                    (stype-count stype aignet)))))


(define aignet-hash-xor-supergate ((lits lit-listp)
                                   (gatesimp gatesimp-p)
                                   strash aignet)
  :returns (mv (new-lit litp :rule-classes :type-prescription)
               new-strash new-aignet)
  :guard (aignet-lit-listp lits aignet)
  :guard-debug t
  (b* (((acl2::local-stobjs litarr)
        (mv new-lit strash aignet litarr))
       (len (len lits))
       ((when (eql len 0))
        (b* ((aignet (mbe :logic (non-exec (node-list-fix aignet))
                          :exec aignet)))
          (mv 0 strash aignet litarr)))
       (litarr (resize-lits len litarr))
       (litarr (lit-list-to-litarr 0 lits litarr))
       ((mv new-lit strash aignet)
        (aignet-hash-xor-supergate-aux 0 len litarr gatesimp strash aignet)))
    (mv new-lit strash aignet litarr))
  ///
  (defret aignet-litp-of-<fn>
    (implies (aignet-lit-listp lits aignet)
             (aignet-litp new-lit new-aignet)))

  (local (defthm posp-len
           (equal (posp (len x))
                  (consp x))))

  (local (defthm aignet-eval-parity-of-true-list-fix
           (equal (aignet-eval-parity (true-list-fix x) invals regvals aignet)
                  (aignet-eval-parity x invals regvals aignet))
           :hints(("Goal" :in-theory (enable aignet-eval-parity)))))

  (local (defthm aignet-lit-listp-of-true-list-fix
           (equal (aignet-lit-listp (true-list-fix x) aignet)
                  (aignet-lit-listp x aignet))
           :hints(("Goal" :in-theory (enable aignet-lit-listp)))))

  (defret eval-of-<fn>
    (implies (aignet-lit-listp lits aignet)
             (equal (lit-eval new-lit invals regvals new-aignet)
                    (aignet-eval-parity
                     lits invals regvals aignet)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable aignet-eval-parity)
                   :do-not-induct t))))

  (def-aignet-preservation-thms aignet-hash-xor-supergate)

  (defret stype-counts-of-<fn>
    (implies (and (not (equal (stype-fix stype) :and))
                  (not (equal (stype-fix stype) :xor)))
             (equal (stype-count stype new-aignet)
                    (stype-count stype aignet)))))




