; AIGNET - And-Inverter Graph Networks -- reference counting
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
(include-book "arrays")
(include-book "aignet-absstobj")
(include-book "centaur/misc/iter" :dir :system)
(local (include-book "clause-processors/just-expand" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))

(local (in-theory (disable nth update-nth
                           acl2::nth-with-large-index
                           true-listp-update-nth)))
(local (std::add-default-post-define-hook :fix))

(defstobj-clone aignet-refcounts u32arr :suffix "-COUNTS")
(defstobj-clone refcounts u32arr :prefix "REFCOUNTS-")

(defsection aignet-count-gate-refs

  (defiteration aignet-count-gate-refs (aignet-refcounts aignet)
    (declare (xargs :stobjs (aignet-refcounts aignet)
                    :guard (<= (num-fanins aignet) (u32-length aignet-refcounts))
                    :guard-hints ('(:do-not-induct t
                                    :in-theory (enable aignet-idp)))))
    (b* ((id n)
         (aignet-refcounts (if (mbt (< id (num-fanins aignet)))
                               (set-u32 id 0 aignet-refcounts)
                             aignet-refcounts)))
      (aignet-case
       (id->type id aignet)
       :gate  (b* ((id0 (lit-id (gate-id->fanin0 id aignet)))
                   (id1 (lit-id (gate-id->fanin1 id aignet)))
                   (aignet-refcounts
                    (set-u32 id0 (+ 1 (get-u32 id0 aignet-refcounts))
                                 aignet-refcounts)))
                (set-u32 id1 (+ 1 (get-u32 id1 aignet-refcounts))
                             aignet-refcounts))
       :in aignet-refcounts
       :const aignet-refcounts))
    :returns aignet-refcounts
    :index n
    :last (num-fanins aignet))

  (in-theory (disable aignet-count-gate-refs))
  (local (in-theory (enable aignet-count-gate-refs)))

  (defthm aignet-refcounts-sizedp-after-aignet-count-gate-refs-iter
    (implies (< (fanin-count aignet) (len aignet-refcounts))
             (equal (len (aignet-count-gate-refs-iter n aignet-refcounts aignet))
                    (len aignet-refcounts)))
    :hints((acl2::just-induct-and-expand
            (aignet-count-gate-refs-iter n aignet-refcounts aignet))))

  (defthm aignet-refcounts-sizedp-after-aignet-count-gate-refs
    (implies (< (fanin-count aignet) (len aignet-refcounts))
             (equal (len (aignet-count-gate-refs aignet-refcounts aignet))
                    (len aignet-refcounts))))

  (defthm aignet-count-gate-refs-iter-does-not-shrink-refcounts
    (<= (len aignet-refcounts)
        (len (aignet-count-gate-refs-iter n aignet-refcounts aignet)))
    :rule-classes :linear
    :hints(("Goal" :in-theory (enable aignet-count-gate-refs-iter))))

  (defthm aignet-count-gate-refs-does-not-shrink-refcounts
    (<= (len aignet-refcounts)
        (len (aignet-count-gate-refs aignet-refcounts aignet)))
    :rule-classes :linear)

  (fty::deffixequiv aignet-count-gate-refs-iter :args ((aignet aignet)))
  (fty::deffixequiv aignet-count-gate-refs$inline :args ((aignet aignet))))


(defsection aignet-count-po-refs
  (defiteration aignet-count-po-refs (aignet-refcounts aignet)
    (declare (xargs :stobjs (aignet-refcounts aignet)
                    :guard (<= (num-fanins aignet) (u32-length aignet-refcounts))))
    (b* ((fanin-id (lit->var (outnum->fanin n aignet))))
      (set-u32 fanin-id (+ 1 (get-u32 fanin-id aignet-refcounts)) aignet-refcounts))
    :returns aignet-refcounts
    :index n
    :last (num-outs aignet))

  (defthm aignet-refcounts-sizedp-after-aignet-count-po-refs-iter
    (implies (< (fanin-count aignet) (len aignet-refcounts))
             (equal (len (aignet-count-po-refs-iter n aignet-refcounts aignet))
                    (len aignet-refcounts)))
    :hints((acl2::just-induct-and-expand
            (aignet-count-po-refs-iter n aignet-refcounts aignet))))

  (defthm aignet-refcounts-sizedp-after-aignet-count-po-refs
    (implies (< (fanin-count aignet) (len aignet-refcounts))
             (equal (len (aignet-count-po-refs aignet-refcounts aignet))
                    (len aignet-refcounts))))

  (defthm aignet-count-po-refs-iter-does-not-shrink-refcounts
    (<= (len aignet-refcounts)
        (len (aignet-count-po-refs-iter n aignet-refcounts aignet)))
    :rule-classes :linear
    :hints(("Goal" :in-theory (enable aignet-count-po-refs-iter))))

  (defthm aignet-count-po-refs-does-not-shrink-refcounts
    (<= (len aignet-refcounts)
        (len (aignet-count-po-refs aignet-refcounts aignet)))
    :rule-classes :linear)

  (fty::deffixequiv aignet-count-po-refs-iter :args ((aignet aignet)))
  (fty::deffixequiv aignet-count-po-refs$inline :args ((aignet aignet))))

(defsection aignet-count-nxst-refs
  (defiteration aignet-count-nxst-refs (aignet-refcounts aignet)
    (declare (xargs :stobjs (aignet-refcounts aignet)
                    :guard (<= (num-fanins aignet) (u32-length aignet-refcounts))))
    (b* ((fanin-id (lit->var (regnum->nxst n aignet))))
      (set-u32 fanin-id (+ 1 (get-u32 fanin-id aignet-refcounts)) aignet-refcounts))
    :returns aignet-refcounts
    :index n
    :last (num-regs aignet))

  (defthm aignet-refcounts-sizedp-after-aignet-count-nxst-refs-iter
    (implies (< (fanin-count aignet) (len aignet-refcounts))
             (equal (len (aignet-count-nxst-refs-iter n aignet-refcounts aignet))
                    (len aignet-refcounts)))
    :hints((acl2::just-induct-and-expand
            (aignet-count-nxst-refs-iter n aignet-refcounts aignet))))

  (defthm aignet-refcounts-sizedp-after-aignet-count-nxst-refs
    (implies (< (fanin-count aignet) (len aignet-refcounts))
             (equal (len (aignet-count-nxst-refs aignet-refcounts aignet))
                    (len aignet-refcounts))))

  (defthm aignet-count-nxst-refs-iter-does-not-shrink-refcounts
    (<= (len aignet-refcounts)
        (len (aignet-count-nxst-refs-iter n aignet-refcounts aignet)))
    :rule-classes :linear
    :hints(("Goal" :in-theory (enable aignet-count-nxst-refs-iter))))

  (defthm aignet-count-nxst-refs-does-not-shrink-refcounts
    (<= (len aignet-refcounts)
        (len (aignet-count-nxst-refs aignet-refcounts aignet)))
    :rule-classes :linear)

  (fty::deffixequiv aignet-count-nxst-refs-iter :args ((aignet aignet)))
  (fty::deffixequiv aignet-count-nxst-refs$inline :args ((aignet aignet))))
  
                    

(define aignet-count-refs (refcounts aignet)
  :returns (new-refcounts)
  :guard (<= (num-fanins aignet) (u32-length refcounts))
  (b* ((refcounts (aignet-count-gate-refs refcounts aignet))
       (refcounts (aignet-count-po-refs refcounts aignet)))
    (aignet-count-nxst-refs refcounts aignet))
  ///
  (defret aignet-refcounts-sizedp-after-aignet-count-refs
    (implies (< (fanin-count aignet) (len refcounts))
             (equal (len new-refcounts)
                    (len refcounts))))

  (defret aignet-count-refs-does-not-shrink-refcounts
    (<= (len refcounts) (len new-refcounts))
    :rule-classes :linear)

  (fty::deffixequiv aignet-count-refs :args ((aignet aignet))))






(defsection aignet-count-supergate-pseudorefs

  (define pseudo-refcount ((lit litp) (parent-xor bitp) aignet)
    :guard (fanin-litp lit aignet)
    (b* ((id (lit->var lit)))
      (if (or (eql (lit->neg lit) 1)
              (and (eql (id->type id aignet) (gate-type))
                   (not (eql (id->regp id aignet) (lbfix parent-xor)))))
          2
        1)))


  (defiteration aignet-count-supergate-pseudorefs (aignet-refcounts aignet)
    (declare (xargs :stobjs (aignet-refcounts aignet)
                    :guard (<= (num-fanins aignet) (u32-length aignet-refcounts))
                    :guard-hints ('(:do-not-induct t
                                    :in-theory (enable aignet-idp)))))
    (b* ((id n)
         (aignet-refcounts (if (mbt (< id (num-fanins aignet)))
                               (set-u32 id 0 aignet-refcounts)
                             aignet-refcounts)))
      (aignet-case
       (id->type id aignet)
       :gate  (b* ((lit0 (gate-id->fanin0 id aignet))
                   (lit1 (gate-id->fanin1 id aignet))
                   (id0 (lit-id lit0))
                   (id1 (lit-id lit1))
                   (xor (id->regp id aignet))
                   (aignet-refcounts
                    (set-u32 id0 (+ (pseudo-refcount lit0 xor aignet)
                                    (get-u32 id0 aignet-refcounts))
                                 aignet-refcounts)))
                (set-u32 id1 (+ (pseudo-refcount lit1 xor aignet)
                                (get-u32 id1 aignet-refcounts))
                             aignet-refcounts))
       :in aignet-refcounts
       :const aignet-refcounts))
    :returns aignet-refcounts
    :index n
    :last (num-fanins aignet))

  (in-theory (disable aignet-count-supergate-pseudorefs))
  (local (in-theory (enable aignet-count-supergate-pseudorefs)))

  (defthm aignet-refcounts-sizedp-after-aignet-count-supergate-pseudorefs-iter
    (implies (< (fanin-count aignet) (len aignet-refcounts))
             (equal (len (aignet-count-supergate-pseudorefs-iter n aignet-refcounts aignet))
                    (len aignet-refcounts)))
    :hints((acl2::just-induct-and-expand
            (aignet-count-supergate-pseudorefs-iter n aignet-refcounts aignet))))

  (defthm aignet-refcounts-sizedp-after-aignet-count-supergate-pseudorefs
    (implies (< (fanin-count aignet) (len aignet-refcounts))
             (equal (len (aignet-count-supergate-pseudorefs aignet-refcounts aignet))
                    (len aignet-refcounts))))

  (defthm aignet-count-supergate-pseudorefs-iter-does-not-shrink-refcounts
    (<= (len aignet-refcounts)
        (len (aignet-count-supergate-pseudorefs-iter n aignet-refcounts aignet)))
    :rule-classes :linear
    :hints(("Goal" :in-theory (enable aignet-count-supergate-pseudorefs-iter))))

  (defthm aignet-count-supergate-pseudorefs-does-not-shrink-refcounts
    (<= (len aignet-refcounts)
        (len (aignet-count-supergate-pseudorefs aignet-refcounts aignet)))
    :rule-classes :linear)

  (fty::deffixequiv aignet-count-supergate-pseudorefs-iter :args ((aignet aignet)))
  (fty::deffixequiv aignet-count-supergate-pseudorefs$inline :args ((aignet aignet))))


(defsection aignet-count-po-superpseudorefs
  (defiteration aignet-count-po-superpseudorefs (aignet-refcounts aignet)
    (declare (xargs :stobjs (aignet-refcounts aignet)
                    :guard (<= (num-fanins aignet) (u32-length aignet-refcounts))))
    (b* ((fanin-id (lit->var (outnum->fanin n aignet))))
      (set-u32 fanin-id (+ 1 (get-u32 fanin-id aignet-refcounts)) aignet-refcounts))
    :returns aignet-refcounts
    :index n
    :last (num-outs aignet))

  (defthm aignet-refcounts-sizedp-after-aignet-count-po-superpseudorefs-iter
    (implies (< (fanin-count aignet) (len aignet-refcounts))
             (equal (len (aignet-count-po-superpseudorefs-iter n aignet-refcounts aignet))
                    (len aignet-refcounts)))
    :hints((acl2::just-induct-and-expand
            (aignet-count-po-superpseudorefs-iter n aignet-refcounts aignet))))

  (defthm aignet-refcounts-sizedp-after-aignet-count-po-superpseudorefs
    (implies (< (fanin-count aignet) (len aignet-refcounts))
             (equal (len (aignet-count-po-superpseudorefs aignet-refcounts aignet))
                    (len aignet-refcounts))))

  (defthm aignet-count-po-superpseudorefs-iter-does-not-shrink-refcounts
    (<= (len aignet-refcounts)
        (len (aignet-count-po-superpseudorefs-iter n aignet-refcounts aignet)))
    :rule-classes :linear
    :hints(("Goal" :in-theory (enable aignet-count-po-superpseudorefs-iter))))

  (defthm aignet-count-po-superpseudorefs-does-not-shrink-refcounts
    (<= (len aignet-refcounts)
        (len (aignet-count-po-superpseudorefs aignet-refcounts aignet)))
    :rule-classes :linear)

  (fty::deffixequiv aignet-count-po-superpseudorefs-iter :args ((aignet aignet)))
  (fty::deffixequiv aignet-count-po-superpseudorefs$inline :args ((aignet aignet))))

(defsection aignet-count-nxst-superpseudorefs
  (defiteration aignet-count-nxst-superpseudorefs (aignet-refcounts aignet)
    (declare (xargs :stobjs (aignet-refcounts aignet)
                    :guard (<= (num-fanins aignet) (u32-length aignet-refcounts))))
    (b* ((fanin-id (lit->var (regnum->nxst n aignet))))
      (set-u32 fanin-id (+ 1 (get-u32 fanin-id aignet-refcounts)) aignet-refcounts))
    :returns aignet-refcounts
    :index n
    :last (num-regs aignet))

  (defthm aignet-refcounts-sizedp-after-aignet-count-nxst-superpseudorefs-iter
    (implies (< (fanin-count aignet) (len aignet-refcounts))
             (equal (len (aignet-count-nxst-superpseudorefs-iter n aignet-refcounts aignet))
                    (len aignet-refcounts)))
    :hints((acl2::just-induct-and-expand
            (aignet-count-nxst-superpseudorefs-iter n aignet-refcounts aignet))))

  (defthm aignet-refcounts-sizedp-after-aignet-count-nxst-superpseudorefs
    (implies (< (fanin-count aignet) (len aignet-refcounts))
             (equal (len (aignet-count-nxst-superpseudorefs aignet-refcounts aignet))
                    (len aignet-refcounts))))

  (defthm aignet-count-nxst-superpseudorefs-iter-does-not-shrink-refcounts
    (<= (len aignet-refcounts)
        (len (aignet-count-nxst-superpseudorefs-iter n aignet-refcounts aignet)))
    :rule-classes :linear
    :hints(("Goal" :in-theory (enable aignet-count-nxst-superpseudorefs-iter))))

  (defthm aignet-count-nxst-superpseudorefs-does-not-shrink-refcounts
    (<= (len aignet-refcounts)
        (len (aignet-count-nxst-superpseudorefs aignet-refcounts aignet)))
    :rule-classes :linear)

  (fty::deffixequiv aignet-count-nxst-superpseudorefs-iter :args ((aignet aignet)))
  (fty::deffixequiv aignet-count-nxst-superpseudorefs$inline :args ((aignet aignet))))
  
                    

(define aignet-count-superpseudorefs (refcounts aignet)
  :returns (new-refcounts)
  :guard (<= (num-fanins aignet) (u32-length refcounts))
  (b* ((refcounts (aignet-count-supergate-pseudorefs refcounts aignet))
       (refcounts (aignet-count-po-superpseudorefs refcounts aignet)))
    (aignet-count-nxst-superpseudorefs refcounts aignet))
  ///
  (defret aignet-refcounts-sizedp-after-aignet-count-superpseudorefs
    (implies (< (fanin-count aignet) (len refcounts))
             (equal (len new-refcounts)
                    (len refcounts))))

  (defret aignet-count-superpseudorefs-does-not-shrink-refcounts
    (<= (len refcounts) (len new-refcounts))
    :rule-classes :linear)

  (fty::deffixequiv aignet-count-superpseudorefs :args ((aignet aignet))))

