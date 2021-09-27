; Copyright (C) 2020 Centaur Technology
; AIGNET - And-Inverter Graph Networks
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

(include-book "internal-observability-super")
(include-book "supergate-construction")
(include-book "literal-sort-aignet")
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (in-theory (disable nth update-nth)))
(std::make-returnspec-config :hints-sub-returnnames t)
(local (std::add-default-post-define-hook :fix))

(local #!satlink
       (fty::deflist lit-list :pred lit-listp :elt-type litp :true-listp t
         :parents (litp)
         :short "List of literals"))

(define remove-lits-above-id ((bound natp)
                              (lits lit-listp))
  :returns (new-lits lit-listp)
  (if (atom lits)
      nil
    (if (<= (lit->var (car lits)) (lnfix bound))
        (cons (lit-fix (car lits))
              (remove-lits-above-id bound (cdr lits)))
      (remove-lits-above-id bound (cdr lits))))
  ///
  (defthmd bound-when-member-remove-lits-above-id
    (implies (member lit (remove-lits-above-id bound lits))
             (<= (lit->var lit) (nfix bound)))))



(local
 (defthm aignet-eval-conjunction-toggle-of-cons
   (equal (aignet-eval-conjunction-toggle
           (cons x y) toggles invals regvals aignet)
          (b-and (lit-eval-toggle x toggles invals regvals aignet)
                 (aignet-eval-conjunction-toggle
                  y toggles invals regvals aignet)))
   :hints(("Goal" :in-theory (enable aignet-eval-conjunction-toggle)))))

(local
 (defthm aignet-eval-conjunction-toggle-of-atom
   (implies (not (consp x))
            (equal (aignet-eval-conjunction-toggle
                    x toggles invals regvals aignet)
                   1))
   :hints(("Goal" :in-theory (enable aignet-eval-conjunction-toggle)))))

(local
 (defthm aignet-eval-parity-toggle-of-cons
   (equal (aignet-eval-parity-toggle
           (cons x y) toggles invals regvals aignet)
          (b-xor (lit-eval-toggle x toggles invals regvals aignet)
                 (aignet-eval-parity-toggle
                  y toggles invals regvals aignet)))
   :hints(("Goal" :in-theory (enable aignet-eval-parity-toggle)))))

(local
 (defthm aignet-eval-parity-toggle-of-atom
   (implies (not (consp x))
            (equal (aignet-eval-parity-toggle
                    x toggles invals regvals aignet)
                   0))
   :hints(("Goal" :in-theory (enable aignet-eval-parity-toggle)))))


(define and-supergate-under-dominators ((lits lit-listp)
                                        (doms lit-listp))
  :measure (+ (len lits) (len doms))
  :returns (mv contradictionp
               (new-lits lit-listp))
  (b* (((when (atom lits))
        (mv nil nil))
       ((when (atom doms))
        (mv nil (lit-list-fix lits)))
       (lit (car lits))
       (dom (car doms))
       ((when (< (lit->var dom) (lit->var lit)))
        (and-supergate-under-dominators lits (cdr doms)))
       ((when (< (lit->var lit) (lit->var dom)))
        (b* (((mv contra rest) (and-supergate-under-dominators (cdr lits) doms))
             ((when contra) (mv contra nil)))
          (mv nil (cons (lit-fix lit) rest))))
       ((when (eql (lit->neg lit) (lit->neg dom)))
        (and-supergate-under-dominators (cdr lits) doms)))
    (mv t nil))
  ///
  (set-ignore-ok t)

  (local (defthm lit-eval-toggle-when-equal-lit-negate
           (implies (equal (lit-fix x) (lit-negate y))
                    (equal (lit-eval-toggle x toggles invals regvals aignet)
                           (b-not (lit-eval-toggle y toggles invals regvals aignet))))
           :hints (("goal" :expand ((lit-eval-toggle x toggles invals regvals aignet)
                                    (lit-eval-toggle y toggles invals regvals aignet))
                    :in-theory (enable b-xor)))))

  (defretd and-supergate-under-dominators-when-contra
    (implies (and contradictionp
                  (<= (lits-max-id-val lits) (nfix bound))
                  (equal (aignet-eval-conjunction-toggle
                          (remove-lits-above-id bound doms)
                          toggles invals regvals aignet) 1))
             (equal (aignet-eval-conjunction-toggle lits toggles invals regvals aignet) 0))
    :hints(("Goal" :induct <call>)
           (acl2::use-termhint
            (b* (((when (atom lits)) nil)
                 ((when (atom doms)) nil)
                 (lit (car lits))
                 (dom (car doms))
                 ((when (< (lit->var dom) (lit->var lit)))
                  '(:expand (;; (aignet-eval-conjunction-toggle doms toggles invals regvals aignet)
                             (remove-lits-above-id bound doms))))
                 ((when (< (lit->var lit) (lit->var dom)))
                  '(:expand (;; (aignet-eval-conjunction-toggle lits toggles invals regvals aignet)
                             (lits-max-id-val lits)))))
              '(:expand (;; (aignet-eval-conjunction-toggle lits toggles invals regvals aignet)
                         ;; (aignet-eval-conjunction-toggle doms toggles invals regvals aignet)
                         (remove-lits-above-id bound doms)
                         (lits-max-id-val lits)))))))


  (local (defthm less-than-equal-forward
           (implies (and (<= a b)
                         (<= b a)
                         (natp a) (natp b))
                    (equal a b))
           :rule-classes :forward-chaining))

  (defret and-supergate-under-dominators-eval-when-no-contra
    (implies (and (not contradictionp)
                  (<= (lits-max-id-val lits) (nfix bound))
                  (equal (aignet-eval-conjunction-toggle
                          (remove-lits-above-id bound doms)
                          toggles invals regvals aignet) 1))
             (equal (aignet-eval-conjunction-toggle new-lits toggles invals regvals aignet)
                    (aignet-eval-conjunction-toggle lits toggles invals regvals aignet)))
    :hints(("Goal" :induct <call>)
           (acl2::use-termhint
            (b* (((when (atom lits))
                  '(:expand (;; (aignet-eval-conjunction-toggle nil toggles invals regvals aignet)
                             ;; (aignet-eval-conjunction-toggle lits toggles invals regvals aignet)
                             (lits-max-id-val lits))))
                 ((when (atom doms)) nil)
                 (lit (car lits))
                 (dom (car doms))
                 ((when (< (lit->var dom) (lit->var lit)))
                  '(:expand (;; (aignet-eval-conjunction-toggle doms toggles invals regvals aignet)
                             (remove-lits-above-id bound doms))))
                 ((when (< (lit->var lit) (lit->var dom)))
                  '(:expand (;; (aignet-eval-conjunction-toggle lits toggles invals regvals aignet)
                             ;; (:free (a b)
                             ;;  (aignet-eval-conjunction-toggle (cons a b) toggles invals regvals aignet))
                             (lits-max-id-val lits)))))
              '(:expand (;; (aignet-eval-conjunction-toggle lits toggles invals regvals aignet)
                         ;; (aignet-eval-conjunction-toggle doms toggles invals regvals aignet)
                         (remove-lits-above-id bound doms)
                         (lits-max-id-val lits)))))))

  (defret aignet-lit-listp-of-<fn>
    (implies (aignet-lit-listp lits aignet)
             (aignet-lit-listp new-lits aignet)))

  (defret lits-max-id-val-of-<fn>
    (<= (lits-max-id-val new-lits) (lits-max-id-val lits))
    :hints(("Goal" :in-theory (enable lits-max-id-val)))
    :rule-classes :linear))





(define xor-supergate-under-dominators ((lits lit-listp)
                                        (doms lit-listp))
  :measure (+ (len lits) (len doms))
  :returns (mv negatep
               (new-lits lit-listp))
  (b* (((when (atom lits))
        (mv nil nil))
       ((when (atom doms))
        (mv nil (lit-list-fix lits)))
       (lit (car lits))
       (dom (car doms))
       ((when (< (lit->var dom) (lit->var lit)))
        (xor-supergate-under-dominators lits (cdr doms)))
       ((when (< (lit->var lit) (lit->var dom)))
        (b* (((mv negate rest) (xor-supergate-under-dominators (cdr lits) doms)))
          (mv negate (cons (lit-fix lit) rest))))
       ((when (eql (lit->neg lit) (lit->neg dom)))
        (b* (((mv negate rest) (xor-supergate-under-dominators (cdr lits) doms)))
          (mv (not negate) rest))))
    (xor-supergate-under-dominators (cdr lits) doms))
  ///
  (set-ignore-ok t)

  (local (defthm lit-eval-toggle-when-equal-lit-negate
           (implies (equal (lit-fix x) (lit-negate y))
                    (equal (lit-eval-toggle x toggles invals regvals aignet)
                           (b-not (lit-eval-toggle y toggles invals regvals aignet))))
           :hints (("goal" :expand ((lit-eval-toggle x toggles invals regvals aignet)
                                    (lit-eval-toggle y toggles invals regvals aignet))
                    :in-theory (enable b-xor)))))

  (local (defthm less-than-equal-forward
           (implies (and (<= a b)
                         (<= b a)
                         (natp a) (natp b))
                    (equal a b))
           :rule-classes :forward-chaining))

  (local (defthm not-equal-lit->neg-when-lit->var-equal
           (implies (and (not (equal (lit->neg x) (lit->neg y)))
                         (equal (lit->var x) (lit->var y)))
                    (equal (lit-fix x) (lit-negate y)))
           :rule-classes :forward-chaining))

  (local (in-theory (disable ACL2::SIMPLIFY-BIT-FUNCTIONS)))

  (defret xor-supergate-under-dominators-eval
    (implies (and (<= (lits-max-id-val lits) (nfix bound))
                  (equal (aignet-eval-conjunction-toggle
                          (remove-lits-above-id bound doms) toggles invals regvals aignet) 1))
             (equal (aignet-eval-parity-toggle new-lits toggles invals regvals aignet)
                    (b-xor (bool->bit negatep)
                           (aignet-eval-parity-toggle lits toggles invals regvals aignet))))
    :hints(("Goal" :induct <call>)
           (acl2::use-termhint
            (b* (((when (atom lits))
                  '(:expand ((lits-max-id-val lits))))
                 ((when (atom doms)) nil)
                 (lit (car lits))
                 (dom (car doms))
                 ((when (< (lit->var dom) (lit->var lit)))
                  '(:expand (;; (aignet-eval-conjunction-toggle doms toggles invals regvals aignet)
                             (remove-lits-above-id bound doms))))
                 ((when (< (lit->var lit) (lit->var dom)))
                  '(:expand (;; (aignet-eval-parity-toggle lits toggles invals regvals aignet)
                             ;; (:free (a b)
                             ;;  (aignet-eval-parity-toggle (cons a b) toggles invals regvals aignet))
                             (lits-max-id-val lits))
                    :in-theory (enable b-xor))))
              '(:expand ((lits-max-id-val lits)
                         (remove-lits-above-id bound doms)
                         ;; (aignet-eval-parity-toggle lits toggles invals regvals aignet)
                         ;; (aignet-eval-conjunction-toggle doms toggles invals regvals aignet)
                         ))))))

  (defret aignet-lit-listp-of-<fn>
    (implies (aignet-lit-listp lits aignet)
             (aignet-lit-listp new-lits aignet)))

  (defret lits-max-id-val-of-<fn>
    (<= (lits-max-id-val new-lits) (lits-max-id-val lits))
    :hints(("Goal" :in-theory (enable lits-max-id-val)))
    :rule-classes :linear))
    


(local
 (defthm aignet-lit-listp-of-lit-list-copies-when-aignet-copies-in-bounds
   (implies (aignet-copies-in-bounds copy aignet)
            (aignet-lit-listp (lit-list-copies lits copy) aignet))
   :hints(("Goal" :in-theory (enable lit-list-copies)))))

(local (defthm lits-max-id-val-bound-by-aignet-lit-listp-bind
         (implies (and (bind-free '((aignet . aignet)) (aignet))
                       (aignet-lit-listp lits aignet)
                       (<= (num-fanins aignet) y))
                  (< (lits-max-id-val lits) y))
         :hints(("Goal" :in-theory (enable lits-max-id-val aignet-idp)))))



(defsection lits-max-id-val-of-literal-sort
  (local (defthm lits-max-id-val-when-member
           (implies (member lit lits)
                    (<= (lit->var lit) (lits-max-id-val lits)))
           :hints(("Goal" :in-theory (enable lits-max-id-val)))))

  (local (defthm lits-max-id-val-when-subsetp
           (implies (subsetp x y)
                    (<= (lits-max-id-val x) (lits-max-id-val y)))
           :hints(("Goal" :in-theory (enable subsetp-equal lits-max-id-val)))))

  (local (defcong acl2::set-equiv equal (lits-max-id-val x) 1
           :hints(("Goal" :in-theory (enable acl2::set-equiv)
                   :cases ((< (lits-max-id-val x) (lits-max-id-val x-equiv))
                           (< (lits-max-id-val x-equiv) (lits-max-id-val x)))))))

  (defthm lits-max-id-val-of-literal-sort
    (equal (lits-max-id-val (literal-sort-insertsort x))
           (lits-max-id-val x))))





(define sweep-observability-dom-supergate ((n natp)
                                           refcounts
                                           obs-sdom-array
                                           aignet
                                           copy
                                           strash
                                           (gatesimp gatesimp-p)
                                           aignet2)
  :guard (and (id-existsp n aignet)
              (<= (num-fanins aignet) (u32-length refcounts))
              (<= (num-fanins aignet) (lits-length copy))
              (<= (num-fanins aignet) (sdominfo-length obs-sdom-array))
              (aignet-copies-in-bounds copy aignet2))
  :returns (mv new-copy new-strash new-aignet2)
  (b* ((aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                     :exec aignet2))
       ((unless (eql (id->type n aignet) (gate-type)))
        (mv copy strash aignet2))
       
       (xor (eql 1 (id->regp n aignet)))
       ((when (<= (get-u32 n refcounts) 1))
        ;; using appropriate refcounts, any reached node should have refcount >
        ;; 1.  But oh well, we'll still make copies for these because we can't
        ;; add toggles for them.
        (b* (((mv lit strash aignet2)
              (if xor
                  (aignet-hash-xor
                   (lit-copy (gate-id->fanin0 n aignet) copy)
                   (lit-copy (gate-id->fanin1 n aignet) copy)
                   gatesimp strash aignet2)
                (aignet-hash-and
                 (lit-copy (gate-id->fanin0 n aignet) copy)
                 (lit-copy (gate-id->fanin1 n aignet) copy)
                 gatesimp strash aignet2)))
             (copy (set-lit n lit copy)))
          (mv copy strash aignet2)))

       ((obs-sdom-info dominfo) (get-sdominfo n obs-sdom-array))
       ((unless dominfo.reached)
        (b* ((copy (set-lit n 0 copy)))
          (mv copy strash aignet2)))
       (supergate (literal-sort (gate-node-supergate n refcounts aignet)))
       ((when xor)
        (b* (((mv negate new-supergate)
              (xor-supergate-under-dominators supergate dominfo.doms))
             (new-supergate-copy (lit-list-copies new-supergate copy))
             ((mv new-lit1 strash aignet2)
              (aignet-hash-xor-supergate new-supergate-copy gatesimp strash aignet2))
             (new-lit (lit-negate-cond new-lit1 (bool->bit negate)))
             (copy (set-lit n new-lit copy)))
          (mv copy strash aignet2)))
       ((mv contra new-supergate)
        (and-supergate-under-dominators supergate dominfo.doms))
       ((when contra)
        (b* ((copy (set-lit n 0 copy)))
          (mv copy strash aignet2)))
       (new-supergate-copy (lit-list-copies new-supergate copy))
       ((mv new-lit strash aignet2)
        (aignet-hash-and-supergate new-supergate-copy gatesimp strash aignet2))
       (copy (set-lit n new-lit copy)))
    (mv copy strash aignet2))
  ///
  (def-aignet-preservation-thms sweep-observability-dom-supergate :stobjname aignet2)
  (defret copy-preserved-of-<fn>
    (implies (not (equal (nfix k) (nfix n)))
             (equal (nth-lit k new-copy)
                    (nth-lit k copy))))
  (defret copy-len-of-<fn>
    (implies (< (nfix n) (len copy))
             (equal (len new-copy)
                    (len copy))))

  (defret aignet-copies-in-bounds-of-<fn>
    (implies (aignet-copies-in-bounds copy aignet2)
             (aignet-copies-in-bounds new-copy new-aignet2)))

  (defret list-vals-of-<fn>
    (equal (list new-copy new-strash new-aignet2)
           <call>))

  (defret stype-counts-of-<fn>
    (and (equal (stype-count :pi new-aignet2) (stype-count :pi aignet2))
         (equal (stype-count :reg new-aignet2) (stype-count :reg aignet2))
         (equal (stype-count :po new-aignet2) (stype-count :po aignet2)))))




(define sweep-observability-dom-supergates-rec ((n natp)
                                                refcounts
                                                obs-sdom-array
                                                aignet
                                                copy
                                                strash
                                                (gatesimp gatesimp-p)
                                                aignet2)
  :guard (and (<= n (num-fanins aignet))
              (<= (num-fanins aignet) (u32-length refcounts))
              (<= (num-fanins aignet) (lits-length copy))
              (<= (num-fanins aignet) (sdominfo-length obs-sdom-array))
              (aignet-copies-in-bounds copy aignet2))
  :verify-guards nil
  :returns (mv new-copy new-strash new-aignet2)
  :measure (nfix n)
  :hooks ((:fix :omit (aignet2)))
  (b* (((when (zp n))
        (mv copy strash aignet2))
       ((mv copy strash aignet2)
        (sweep-observability-dom-supergates-rec
         (1- n) refcounts obs-sdom-array aignet copy strash gatesimp aignet2)))
    (sweep-observability-dom-supergate
     (1- n) refcounts obs-sdom-array aignet copy strash gatesimp aignet2))
  ///
  (def-aignet-preservation-thms sweep-observability-dom-supergates-rec :stobjname aignet2)
  (defret copy-preserved-of-<fn>
    (implies (<= (nfix n) (nfix k))
             (equal (nth-lit k new-copy)
                    (nth-lit k copy))))

  (defret copy-len-of-<fn>
    (implies (<= (nfix n) (len copy))
             (equal (len new-copy)
                    (len copy))))

  (defret aignet-copies-in-bounds-of-<fn>
    (implies (aignet-copies-in-bounds copy aignet2)
             (aignet-copies-in-bounds new-copy new-aignet2)))

  (verify-guards sweep-observability-dom-supergates-rec
    :hints (("goal" :in-theory (enable aignet-idp)
             :do-not-induct t)))

  (defret stype-counts-of-<fn>
    (and (equal (stype-count :pi new-aignet2) (stype-count :pi aignet2))
         (equal (stype-count :reg new-aignet2) (stype-count :reg aignet2))
         (equal (stype-count :po new-aignet2) (stype-count :po aignet2)))))


(define sweep-observability-dom-supergates-tailrec ((n natp)
                                                    refcounts
                                                    obs-sdom-array
                                                    aignet
                                                    copy
                                                    strash
                                                    (gatesimp gatesimp-p)
                                                    aignet2)
  :guard (and (<= n (num-fanins aignet))
              (<= (num-fanins aignet) (u32-length refcounts))
              (<= (num-fanins aignet) (lits-length copy))
              (<= (num-fanins aignet) (sdominfo-length obs-sdom-array))
              (aignet-copies-in-bounds copy aignet2))
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  :returns (mv new-copy new-strash new-aignet2)
  :measure (nfix (- (num-fanins aignet) (nfix n)))
  :hooks nil
  (b* (((when (mbe :logic (zp (- (num-fanins aignet) (nfix n)))
                   :exec (eql n (num-fanins aignet))))
        (mv copy strash aignet2))
       ((mv copy strash aignet2)
        (sweep-observability-dom-supergate
         n refcounts obs-sdom-array aignet copy strash gatesimp aignet2)))
    (sweep-observability-dom-supergates-tailrec
     (1+ (lnfix n)) refcounts obs-sdom-array aignet copy strash gatesimp aignet2))
  ///
  ;; (def-aignet-preservation-thms sweep-observability-dom-supergates :stobjname aignet2)
  ;; (defret copy-preserved-of-<fn>
  ;;   (implies (< (nfix k) (nfix n))
  ;;            (equal (nth-lit k new-copy)
  ;;                   (nth-lit k copy))))

  ;; (defret copy-len-of-<fn>
  ;;   (implies (<= (num-fanins aignet) (len copy))
  ;;            (equal (len new-copy)
  ;;                   (len copy))))

  ;; (defret aignet-copies-in-bounds-of-<fn>
  ;;   (implies (aignet-copies-in-bounds copy aignet2)
  ;;            (aignet-copies-in-bounds new-copy new-aignet2)))
  (local (defthm sweep-observability-dom-supergate-when-zp
           (implies (and (syntaxp (not (equal n ''0)))
                         (zp n))
                    (equal (sweep-observability-dom-supergate
                            n refcounts obs-sdom-array aignet copy strash gatesimp aignet2)
                           (sweep-observability-dom-supergate
                            0 refcounts obs-sdom-array aignet copy strash gatesimp aignet2)))
           :hints(("Goal" :in-theory (enable sweep-observability-dom-supergate)))))

  (set-ignore-ok t)
  (defthm sweep-observability-dom-supergates-tailrec-spec
    (equal (sweep-observability-dom-supergates-tailrec
            0 refcounts obs-sdom-array aignet copy strash gatesimp aignet2)
           (sweep-observability-dom-supergates-rec
            (num-fanins aignet) refcounts obs-sdom-array aignet copy strash gatesimp aignet2))
    :hints (("goal" :use ((:instance (:functional-instance acl2::iter-up-is-iter-down
                                      (acl2::iter-step
                                       (lambda (n aux val)
                                         (b* (((list refcounts obs-sdom-array aignet gatesimp) aux)
                                              ((mv copy strash aignet2) val)
                                              ((unless (natp n))
                                               (mv copy strash aignet2)))
                                           (sweep-observability-dom-supergate
                                            n refcounts obs-sdom-array aignet copy strash gatesimp aignet2))))
                                      (acl2::iter-first
                                       (lambda (aux val) 0))
                                      (acl2::iter-last
                                       (lambda (aux val)
                                         (b* (((list refcounts obs-sdom-array aignet gatesimp) aux))
                                           (num-fanins aignet))))
                                      (acl2::iter-fix-val
                                       (lambda (val)
                                         (b* (((mv copy strash aignet2) val))
                                           (mv copy strash aignet2))))
                                      (acl2::iter-up
                                       (lambda (n aux val)
                                         (b* (((list refcounts obs-sdom-array aignet gatesimp) aux)
                                              ((mv copy strash aignet2) val))
                                           (sweep-observability-dom-supergates-tailrec
                                            n refcounts obs-sdom-array aignet copy strash gatesimp aignet2))))
                                      (acl2::iter-down
                                       (lambda (n aux val)
                                         (b* (((list refcounts obs-sdom-array aignet gatesimp) aux)
                                              ((mv copy strash aignet2) val))
                                           (sweep-observability-dom-supergates-rec
                                            n refcounts obs-sdom-array aignet copy strash gatesimp aignet2)))))
                           (acl2::aux (list refcounts obs-sdom-array aignet gatesimp))
                           (acl2::val (mv copy strash aignet2))))
             :in-theory (enable nfix ifix)
             :expand ((:free (refcounts obs-sdom-array aignet copy strash gatesimp aignet2)
                       (sweep-observability-dom-supergates-rec
                        acl2::n refcounts obs-sdom-array aignet copy strash gatesimp aignet2))
                      (:free (refcounts obs-sdom-array aignet copy strash gatesimp aignet2)
                       (sweep-observability-dom-supergates-tailrec
                        acl2::n refcounts obs-sdom-array aignet copy strash gatesimp aignet2)))))))

(define sweep-observability-dom-supergates (refcounts
                                            obs-sdom-array
                                            aignet
                                            copy
                                            strash
                                            (gatesimp gatesimp-p)
                                            aignet2)
  :enabled t
  :guard (and (<= (num-fanins aignet) (u32-length refcounts))
              (<= (num-fanins aignet) (lits-length copy))
              (<= (num-fanins aignet) (sdominfo-length obs-sdom-array))
              (aignet-copies-in-bounds copy aignet2))
  (mbe :logic (non-exec
               (sweep-observability-dom-supergates-rec
                (num-fanins aignet) refcounts
                obs-sdom-array aignet copy strash gatesimp
                (node-list-fix aignet2)))
       :exec  (sweep-observability-dom-supergates-tailrec
               0 refcounts obs-sdom-array aignet copy strash gatesimp aignet2)))

;; bozo duplicated
(define nat-list-max-or-minus1 ((x nat-listp))
  (if (atom x)
      -1
    (max (lnfix (car x))
         (nat-list-max-or-minus1 (cdr x)))))


(define sweep-observability-dom-supergates-toggles ((n natp)
                                                    refcounts
                                                    invals
                                                    regvals
                                                    aignet
                                                    copy
                                                    aignet2)
  :returns (toggles nat-listp)
  :measure (nfix n)
  :guard (and (<= n (num-fanins aignet))
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals))
              (<= (num-fanins aignet) (u32-length refcounts))
              (<= (num-fanins aignet) (lits-length copy))
              (equal (num-ins aignet) (num-ins aignet2))
              (equal (num-regs aignet) (num-regs aignet2))
              (aignet-copies-in-bounds copy aignet2))
  :verify-guards nil
  (b* (((when (zp n)) nil)
       (n (1- n))
       (rest-toggles (sweep-observability-dom-supergates-toggles
                      n refcounts invals regvals aignet copy aignet2))
       ((unless (and (eql (id->type n aignet) (gate-type))
                     (< 1 (get-u32 n refcounts))
                     (not (eql (id-eval-toggle n rest-toggles invals regvals aignet)
                               (lit-eval (get-lit n copy) invals regvals aignet2)))))
        rest-toggles))
    (cons n rest-toggles))
  ///
  (defret ids-multiply-referenced-of-<fn>
    (ids-multiply-referenced toggles refcounts)
    :hints(("Goal" :in-theory (enable ids-multiply-referenced))))

  (defret nat-list-max-or-minus1-of-<fn>
    (< (nat-list-max-or-minus1 toggles) (nfix n))
    :hints(("Goal" :in-theory (enable nat-list-max-or-minus1)))
    :rule-classes :linear)

  (verify-guards sweep-observability-dom-supergates-toggles
    :hints(("Goal" :in-theory (enable aignet-idp)))
    :guard-debug t)

  (defthm sweep-observability-dom-supergates-toggles-of-extension
    (implies (and (aignet-extension-binding :new new-aignet2 :orig orig-aignet2)
                  (aignet-copies-in-bounds copy orig-aignet2))
             (equal (sweep-observability-dom-supergates-toggles
                     n refcounts invals regvals aignet copy new-aignet2)
                    (sweep-observability-dom-supergates-toggles
                     n refcounts invals regvals aignet copy orig-aignet2)))
    :hints (("goal" :induct
             (sweep-observability-dom-supergates-toggles
              n refcounts invals regvals aignet copy orig-aignet2))))

  (defthm sweep-observability-dom-supergates-toggles-of-set-copy
    (implies (<= (nfix n) (nfix m))
             (equal (sweep-observability-dom-supergates-toggles
                     n refcounts invals regvals aignet
                     (update-nth-lit m val copy) aignet2)
                    (sweep-observability-dom-supergates-toggles
                     n refcounts invals regvals aignet
                     copy aignet2)))
    :hints (("goal" :induct
             (sweep-observability-dom-supergates-toggles
              n refcounts invals regvals aignet copy aignet2))))


  (defret id-eval-toggle-of-<fn>-normalize
    (implies (and (equal idplus1 (+ 1 (nfix id)))
                  (syntaxp (not (equal idplus1 n)))
                  (<= idplus1 (nfix n)))
             (equal (id-eval-toggle id toggles invals regvals aignet)
                    (id-eval-toggle id
                                    (let ((n idplus1)) <call>)
                                    invals regvals aignet)))
    :hints (("Goal" :induct <call>
             :expand (<call>))
            (and stable-under-simplificationp
                 '(:cases ((< (nfix id) (+ -1 (nfix n))))))))

  (defret not-member-toggles-when-not-gate
    (implies (not (equal (ctype (stype (car (lookup-id k aignet)))) :gate))
             (not (member (nfix k) toggles))))

  (defret not-member-toggles-when-not-multiref
    (implies (<= (nfix (nth k refcounts)) 1)
             (not (member (nfix k) toggles)))
    :hints(("Goal" :in-theory (disable nth))))


  (defthm sweep-observability-dom-supergates-toggles-of-0
    (equal (sweep-observability-dom-supergates-toggles
            0 refcounts invals regvals aignet copy aignet2)
           nil)))

(defsection aignet-non-gates-copied
  (defun-sk aignet-non-gates-copied (aignet copy aignet2)
    (forall (n invals regvals)
            (implies (not (equal (ctype (stype (car (lookup-id n aignet)))) :gate))
                     (equal (lit-eval (nth-lit n copy) invals regvals aignet2)
                            (id-eval n invals regvals aignet))))
    :rewrite :direct)

  (in-theory (disable aignet-non-gates-copied))

  (defthm aignet-non-gates-copied-of-update-gate
    (implies (equal (ctype (stype (car (lookup-id n aignet)))) :gate)
             (iff (aignet-non-gates-copied aignet (update-nth-lit n val copy) aignet2)
                  (aignet-non-gates-copied aignet copy aignet2)))
    :hints ((acl2::use-termhint
             (b* ((new-copy (update-nth-lit n val copy))
                  ((mv witness-copy other-copy)
                   (if (aignet-non-gates-copied aignet new-copy aignet2)
                       (mv copy new-copy)
                     (mv new-copy copy)))
                  ((mv nw invalsw regvalsw) (aignet-non-gates-copied-witness aignet witness-copy aignet2)))
               `(:use ((:instance aignet-non-gates-copied-necc
                        (copy ,(acl2::hq other-copy))
                        (n ,(acl2::hq nw))
                        (invals ,(acl2::hq invalsw))
                        (regvals ,(acl2::hq regvalsw))))
                 :in-theory (disable aignet-non-gates-copied-necc)
                 :expand ((aignet-non-gates-copied aignet ,(acl2::hq witness-copy) aignet2)))))))

  (defthm aignet-non-gates-copied-of-extension
    (implies (and (aignet-extension-binding :new new-aignet2 :orig orig-aignet2)
                  (aignet-copies-in-bounds copy orig-aignet2))
             (iff (aignet-non-gates-copied aignet copy new-aignet2)
                  (aignet-non-gates-copied aignet copy orig-aignet2)))
    :hints ((acl2::use-termhint
             (b* (((mv witness-aignet2 other-aignet2)
                   (if (aignet-non-gates-copied aignet copy new-aignet2)
                       (mv orig-aignet2 new-aignet2)
                     (mv new-aignet2 orig-aignet2)))
                  ((mv nw invalsw regvalsw) (aignet-non-gates-copied-witness aignet copy witness-aignet2)))
               `(:use ((:instance aignet-non-gates-copied-necc
                        (aignet2 ,(acl2::hq other-aignet2))
                        (n ,(acl2::hq nw))
                        (invals ,(acl2::hq invalsw))
                        (regvals ,(acl2::hq regvalsw))))
                 :in-theory (disable aignet-non-gates-copied-necc)
                 :expand ((aignet-non-gates-copied aignet copy ,(acl2::hq witness-aignet2))))))))

  (defthm aignet-non-gates-copied-of-node-list-fix
    (iff (aignet-non-gates-copied aignet copy (node-list-fix aignet2))
         (aignet-non-gates-copied aignet copy aignet2))
    :hints ((acl2::use-termhint
             (b* ((new-aignet2 (node-list-fix aignet2))
                  ((mv witness-aignet2 other-aignet2)
                   (if (aignet-non-gates-copied aignet copy new-aignet2)
                       (mv aignet2 new-aignet2)
                     (mv new-aignet2 aignet2)))
                  ((mv nw invalsw regvalsw) (aignet-non-gates-copied-witness aignet copy witness-aignet2)))
               `(:use ((:instance aignet-non-gates-copied-necc
                        (aignet2 ,(acl2::hq other-aignet2))
                        (n ,(acl2::hq nw))
                        (invals ,(acl2::hq invalsw))
                        (regvals ,(acl2::hq regvalsw))))
                 :in-theory (disable aignet-non-gates-copied-necc)
                 :expand ((aignet-non-gates-copied aignet copy ,(acl2::hq witness-aignet2))))))))

  (local (defthm nth-lit-of-nil
           (equal (nth-lit n nil) 0)
           :hints(("Goal" :in-theory (enable nth-lit nth)))))

  (local (defthm nth-lit-of-repeat
           (equal (nth-lit n (acl2::repeat m 0)) 0)
           :hints(("Goal" :in-theory (enable nth-lit nth acl2::repeat)))))

  (defret aignet-non-gates-copied-of-<fn>
    (aignet-non-gates-copied aignet new-copy new-aignet2)
    :hints(("Goal" :in-theory (e/d (aignet-non-gates-copied
                                      init-copy-comb)
                                   (resize-list))
            :expand ((:free (lit neg invals regvals aignet)
                      (lit-eval (make-lit lit neg) invals regvals aignet))
                     (:free (id invals regvals)
                      (id-eval id invals regvals aignet)))))
    :fn init-copy-comb))


(defsection sweep-observability-invariant
  (local (in-theory (disable lookup-id-out-of-bounds
                             lookup-id-in-bounds-when-positive
                             default-car
                             lits-max-id-val-bound-by-aignet-lit-listp-bind
                             nth true-listp-lookup-id-of-node-listp
                             not)))


  (defun-sk sweep-observability-invariant (n refcounts invals regvals aignet copy aignet2)
    (forall id
            (implies (< (nfix id) (nfix n))
                     (b* ((toggles (sweep-observability-dom-supergates-toggles
                                    n refcounts invals regvals aignet copy aignet2)))
                       (equal (lit-eval (nth-lit id copy) invals regvals aignet2)
                              (id-eval-toggle id toggles invals regvals aignet)))))
    :rewrite :direct)
  (in-theory (disable sweep-observability-invariant))

  (defthm sweep-observability-invariant-of-lit-copy
    (implies (and (sweep-observability-invariant n refcounts invals regvals aignet copy aignet2)
                  (< (lit->var lit) (nfix n)))
             (b* ((toggles (sweep-observability-dom-supergates-toggles
                            n refcounts invals regvals aignet copy aignet2)))
               (equal (lit-eval (lit-copy lit copy) invals regvals aignet2)
                      (lit-eval-toggle lit toggles invals regvals aignet))))
    :hints (("goal" :expand ((:free (lit) (lit-eval lit invals regvals aignet2))
                             (:free (lit toggles)
                              (lit-eval-toggle lit toggles invals regvals aignet)))
             :use ((:instance sweep-observability-invariant-necc
                    (id (lit->var lit))))
             :in-theory (e/d (lit-copy) (sweep-observability-invariant-necc)))))
                    

  (defthm aignet-eval-conjunction-of-lit-list-copies-when-sweep-obs-invariant
    (implies (and (sweep-observability-invariant n refcounts invals regvals aignet copy aignet2)
                  (< (lits-max-id-val lits) (nfix n)))
             (b* ((toggles (sweep-observability-dom-supergates-toggles
                            n refcounts invals regvals aignet copy aignet2)))
               (equal (aignet-eval-conjunction (lit-list-copies lits copy) invals regvals aignet2)
                      (aignet-eval-conjunction-toggle lits toggles invals regvals aignet))))
    :hints(("Goal" :in-theory (enable aignet-eval-conjunction-toggle
                                      aignet-eval-conjunction
                                      lit-list-copies
                                      lits-max-id-val))))

  (defthm aignet-eval-parity-of-lit-list-copies-when-sweep-obs-invariant
    (implies (and (sweep-observability-invariant n refcounts invals regvals aignet copy aignet2)
                  (< (lits-max-id-val lits) (nfix n)))
             (b* ((toggles (sweep-observability-dom-supergates-toggles
                            n refcounts invals regvals aignet copy aignet2)))
               (equal (aignet-eval-parity (lit-list-copies lits copy) invals regvals aignet2)
                      (aignet-eval-parity-toggle lits toggles invals regvals aignet))))
    :hints(("Goal" :in-theory (enable aignet-eval-parity-toggle
                                      aignet-eval-parity
                                      lit-list-copies
                                      lits-max-id-val))))


  (local (defthm id-eval-toggle-of-non-gate
           (implies (not (equal (ctype (stype (car (lookup-id k aignet)))) :gate))
                    (equal (id-eval-toggle k toggles invals regvals aignet)
                           (b-xor (bool->bit (member-equal (nfix k)
                                                           (acl2::nat-list-fix toggles)))
                                  (id-eval k invals regvals aignet))))
           :hints(("Goal" :in-theory (enable id-eval-toggle id-eval)))))

  (local (in-theory (enable* acl2::arith-equiv-forwarding)))



  (local (in-theory (enable eval-and-of-lits-toggle
                            eval-xor-of-lits-toggle
                            lit-eval-toggle)))

  
  (local (defthm not-member-by-nat-list-max-or-minus1
           (implies (< (nat-list-max-or-minus1 x) i)
                    (not (member i (acl2::nat-list-fix x))))
           :hints(("Goal" :in-theory (enable acl2::nat-list-fix
                                             nat-list-max-or-minus1)))))

  (local (defthmd non-nat-member-of-nat-list
           (implies (and (nat-listp x)
                         (not (natp n)))
                    (not (member n x)))
           :hints(("Goal" :in-theory (enable nat-listp)))))

  (defthm n-not-member-of-sweep-observability-dom-supergate-toggles
    (not (member-equal n (sweep-observability-dom-supergates-toggles
                          n refcounts invals regvals aignet copy aignet2)))
    :hints (("goal" :use ((:instance not-member-by-nat-list-max-or-minus1
                           (i (nfix n))
                           (x (sweep-observability-dom-supergates-toggles
                               n refcounts invals regvals aignet copy aignet2))))
             :in-theory (e/d (non-nat-member-of-nat-list)
                             (not-member-by-nat-list-max-or-minus1))
             :cases ((natp n)))))

  (local (defthm id-eval-toggle-of-cons-self
           (implies (< (nat-list-max-or-minus1 toggles) (nfix i))
                    (equal (id-eval-toggle i (cons i toggles) invals regvals aignet)
                           (b-not (id-eval-toggle i toggles invals regvals aignet))))
           :hints(("Goal" :expand ((:free (toggles)
                                    (id-eval-toggle i toggles invals regvals aignet)))))))

  (set-ignore-ok t)

  (local (in-theory (enable gate-node-supergate)))


  (local (defthm b-xor-of-equal-b-xor
           (implies (equal a (b-xor b c))
                    (equal (b-xor b a)
                           (bfix c)))
           :hints(("Goal" :in-theory (enable b-xor)))))

  (local (defthm b-not-when-not-equal
           (implies (and (not (equal b c))
                         (bitp b) (bitp c))
                    (equal (b-not b) c))
           :hints(("Goal" :in-theory (enable b-not)))))

  (defret <fn>-preserves-invariant
    (implies (and (sweep-observability-invariant
                   n refcounts invals regvals aignet copy aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (aignet-non-gates-copied aignet copy aignet2))
             (sweep-observability-invariant
              (+ 1 (nfix n)) refcounts invals regvals aignet new-copy new-aignet2))
    :hints (("goal" :in-theory (enable <fn>))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))
            (and stable-under-simplificationp
                 (acl2::use-termhint
                  (b* ((n+1 (+ 1 (nfix n)))
                       (id (sweep-observability-invariant-witness
                            n+1 refcounts invals regvals aignet new-copy new-aignet2))
                       (expand1 `(:free (copy aignet2)
                                  (SWEEP-OBSERVABILITY-DOM-SUPERGATES-TOGGLES
                                   ,(acl2::hq n+1)
                                   REFCOUNTS
                                   INVALS REGVALS AIGNET COPY AIGNET2)))
                       ((when (< (nfix id) (nfix n)))
                        `(:expand (,expand1)))
                       ((when (<= (get-u32 n refcounts) 1))
                        `(:expand ((:free (toggles)
                                    (id-eval-toggle n toggles invals regvals aignet))
                                   ,expand1)))
                       ((obs-sdom-info dominfo) (get-sdominfo n obs-sdom-array))
                       ((unless dominfo.reached)
                        `(:use ((:instance acl2::mark-clause-is-true
                                 (x :unreach)))
                          :expand (,expand1)))
                       (xor (eql 1 (id->regp n aignet)))
                       (supergate (literal-sort (gate-node-supergate n refcounts aignet)))
                       (toggles (sweep-observability-dom-supergates-toggles
                                 n refcounts invals regvals aignet copy aignet2))
                       ((when xor)
                        `(:use ((:instance acl2::mark-clause-is-true
                                 (x :xor))
                                (:instance xor-supergate-under-dominators-eval
                                 (lits ,(acl2::hq supergate))
                                 (doms ,(acl2::hq dominfo.doms))
                                 (bound ,(acl2::hq (1- (nfix n))))
                                 (toggles ,(acl2::hq toggles))))
                          :in-theory (disable xor-supergate-under-dominators-eval)
                          :expand (,expand1)))
                       ((mv contra new-supergate)
                        (and-supergate-under-dominators supergate dominfo.doms))
                       ((when contra)
                        `(:use ((:instance acl2::mark-clause-is-true
                                 (x :contra)))
                          :expand (,expand1))))
                    `(:use ((:instance acl2::mark-clause-is-true
                             (x :and))
                            (:instance and-supergate-under-dominators-eval-when-no-contra
                             (lits ,(acl2::hq supergate))
                             (doms ,(acl2::hq dominfo.doms))
                             (bound ,(acl2::hq (1- (nfix n))))
                             (toggles ,(acl2::hq toggles))))
                      :in-theory (disable and-supergate-under-dominators-eval-when-no-contra)
                      :expand (,expand1))))))
    :fn sweep-observability-dom-supergate)

  (local (defthm sweep-observability-invariant-when-zp
           (implies (zp n)
                    (sweep-observability-invariant
                     n refcounts invals regvals aignet copy aignet2))
           :hints(("Goal" :in-theory (enable sweep-observability-invariant)))))




             

  (defret <fn>-preserves-aignet-non-gates-copied
    (implies (and (aignet-non-gates-copied aignet copy aignet2)
                  (aignet-copies-in-bounds copy aignet2))
             (aignet-non-gates-copied aignet new-copy new-aignet2))
    :hints(("Goal" :in-theory (enable <fn>)))
    :fn sweep-observability-dom-supergate)

  (defret <fn>-preserves-aignet-non-gates-copied
    (implies (and (aignet-non-gates-copied aignet copy aignet2)
                  (aignet-copies-in-bounds copy aignet2))
             (aignet-non-gates-copied aignet new-copy new-aignet2))
    :hints(("Goal" :in-theory (enable <fn>)))
    :fn sweep-observability-dom-supergates-rec)

  (defret <fn>-preserves-invariant
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (aignet-non-gates-copied aignet copy aignet2))
             (sweep-observability-invariant
              n refcounts invals regvals aignet new-copy new-aignet2))
    :hints (("goal" :induct <call>
             :in-theory (enable (:i <fn>))
             :expand (<call>))
            (acl2::use-termhint
             (b* (((when (zp n)) nil)
                  ((mv copy1 strash1 aignet21)
                   (sweep-observability-dom-supergates-rec
                    (1- n) refcounts obs-sdom-array aignet copy strash gatesimp aignet2)))
               `(:use ((:instance sweep-observability-dom-supergate-preserves-invariant
                        (n (+ -1 n))
                        (copy ,(acl2::hq copy1))
                        (strash ,(acl2::hq strash1))
                        (aignet2 ,(acl2::hq aignet21))))
                 :in-theory (disable sweep-observability-dom-supergate-preserves-invariant)))))
    :fn sweep-observability-dom-supergates-rec))


(define lits-find-0val-toggle ((lits lit-listp) (toggles nat-listp)
                               invals regvals aignet)
  :returns (0-lit litp :rule-classes :type-prescription)
  :guard (and (aignet-lit-listp lits aignet)
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  (if (atom lits)
      1
    (if (equal (lit-eval-toggle (car lits) toggles invals regvals aignet) 0)
        (lit-fix (car lits))
      (lits-find-0val-toggle (cdr lits) toggles invals regvals aignet)))
  ///
  (defret lits-find-0val-toggle-member-when-conjunction
    (implies (equal (aignet-eval-conjunction-toggle
                     lits toggles invals regvals aignet)
                    0)
             (member-equal 0-lit (lit-list-fix lits)))
    :hints(("Goal" :in-theory (enable aignet-eval-conjunction-toggle))))

  (defret lits-find-0val-toggle-member-lit-listp-when-conjunction
    (implies (and (equal (aignet-eval-conjunction-toggle
                          lits toggles invals regvals aignet)
                         0)
                  (lit-listp lits))
             (member-equal 0-lit lits))
    :hints(("Goal" :in-theory (enable aignet-eval-conjunction-toggle))))

  (defret lits-find-0val-toggle-eval-when-conjunction
    (implies (equal (aignet-eval-conjunction-toggle
                     lits toggles invals regvals aignet)
                    0)
             (equal (lit-eval-toggle 0-lit toggles invals regvals aignet) 0))
    :hints(("Goal" :in-theory (enable aignet-eval-conjunction-toggle))))

  (defthmd aignet-eval-conjunction-toggle-when-0-valued-lit
    (implies (and (equal (lit-eval-toggle lit toggles invals regvals aignet) 0)
                  (member-equal lit (lit-list-fix lits)))
             (equal (aignet-eval-conjunction-toggle lits toggles invals regvals aignet) 0))
    :hints(("Goal" :in-theory (enable aignet-eval-conjunction-toggle)))))


(defsection aignet-eval-parity-toggle-of-literal-sort
  (local (defthm aignet-eval-parity-toggle-of-literal-sort-insert
           (equal (aignet-eval-parity-toggle (literal-sort-insert k x)
                                             toggles invals regvals aignet)
                  (aignet-eval-parity-toggle (cons k x)
                                             toggles invals regvals aignet))
           :hints(("Goal" :in-theory (enable aignet-eval-parity-toggle
                                             literal-sort-insert)
                   :induct t)
                  (and stable-under-simplificationp
                       '(:in-theory (enable b-xor))))))

  (defthm aignet-eval-parity-toggle-of-literal-sort
    (equal (aignet-eval-parity-toggle (literal-sort-insertsort x)
                                      toggles invals regvals aignet)
           (aignet-eval-parity-toggle x toggles invals regvals aignet))
    :hints(("Goal" :in-theory (enable literal-sort-insertsort)))))


(defsection aignet-eval-conjunction-toggle-of-literal-sort
  (local (defthm aignet-eval-conjunction-toggle-of-literal-sort-insert
           (equal (aignet-eval-conjunction-toggle (literal-sort-insert k x)
                                             toggles invals regvals aignet)
                  (aignet-eval-conjunction-toggle (cons k x)
                                             toggles invals regvals aignet))
           :hints(("Goal" :in-theory (enable aignet-eval-conjunction-toggle
                                             literal-sort-insert)
                   :induct t)
                  (and stable-under-simplificationp
                       '(:in-theory (enable b-and))))))

  (defthm aignet-eval-conjunction-toggle-of-literal-sort
    (equal (aignet-eval-conjunction-toggle (literal-sort-insertsort x)
                                      toggles invals regvals aignet)
           (aignet-eval-conjunction-toggle x toggles invals regvals aignet))
    :hints(("Goal" :in-theory (enable literal-sort-insertsort)))))

(defsection sweep-observability-dom-supergate-correct
  

  (local (defthm not-member-by-nat-list-max-or-minus1
           (implies (< (nat-list-max-or-minus1 x) i)
                    (not (member i (acl2::nat-list-fix x))))
           :hints(("Goal" :in-theory (enable acl2::nat-list-fix
                                             nat-list-max-or-minus1)))))

  (local (defthm id-eval-toggle-of-cons-self
           (implies (< (nat-list-max-or-minus1 toggles) (nfix i))
                    (equal (id-eval-toggle i (cons i toggles) invals regvals aignet)
                           (b-not (id-eval-toggle i toggles invals regvals aignet))))
           :hints(("Goal" :expand ((:free (toggles)
                                    (id-eval-toggle i toggles invals regvals aignet)))))))


  (local (defthm member-of-remove-lits-above-id
           (implies (not (member lit (lit-list-fix lits)))
                    (not (member lit (remove-lits-above-id bound lits))))
           :hints(("Goal" :in-theory (enable remove-lits-above-id)))))

  (local (defthm subsetp-of-remove-lits-above-id
           (subsetp (remove-lits-above-id bound lits) (lit-list-fix lits))
           :hints(("Goal" :in-theory (enable remove-lits-above-id)))))

  (local (defthm subsetp-of-remove-lits-above-id-lit-listp
           (implies (lit-listp lits)
                    (subsetp (remove-lits-above-id bound lits) lits))
           :hints(("Goal" :in-theory (enable remove-lits-above-id)))))

  (local (defthmd lit-list-fix-when-subsetp
           (implies (and (subsetp x y)
                         (lit-listp y))
                    (equal (lit-list-fix x)
                           (true-list-fix x)))
           :hints(("Goal" :in-theory (enable lit-list-fix subsetp)))))

  (local (defthm member-of-lits-find-0val-toggle
           (implies (and (subsetp lits super-lits)
                         (equal (aignet-eval-conjunction-toggle
                                 lits toggles invals regvals aignet)
                                0)
                         (lit-listp super-lits))
                    (member-equal (lits-find-0val-toggle lits toggles invals regvals aignet)
                                  super-lits))
           :hints(("Goal" :use ((:instance lits-find-0val-toggle-member-when-conjunction))
                   :in-theory (e/d (lit-list-fix-when-subsetp)
                                   (lits-find-0val-toggle-member-when-conjunction))))))

  (local (defthm lits-find-0val-toggle-of-remove-lits-above-id-bound
           (implies (equal (aignet-eval-conjunction-toggle
                            (remove-lits-above-id bound lits)
                            toggles invals regvals aignet)
                           0)
                    (<= (lit->var (lits-find-0val-toggle
                                   (remove-lits-above-id bound lits)
                                   toggles invals regvals aignet))
                        (nfix bound)))
           :hints(("Goal" :use ((:instance bound-when-member-remove-lits-above-id
                                 (lit (lits-find-0val-toggle
                                   (remove-lits-above-id bound lits)
                                   toggles invals regvals aignet))))
                   :in-theory (disable bound-when-member-remove-lits-above-id)))
           :rule-classes :linear))



  (defthm toggle-does-not-affect-output-when-aignet-eval-conjunction-toggle
    (implies (and (obs-sdom-array-correct obs-sdom-array refcounts aignet)
                  ;; (member-equal lit (obs-sdom-info->doms (nth source obs-sdom-array)))
                  ;; (equal (lit-eval-toggle lit toggles invals regvals aignet) 0)
                  ;; (equal (lit-eval-toggle lit (cons source toggles) invals regvals aignet) 0)
                  (equal (aignet-eval-conjunction-toggle
                          (remove-lits-above-id (+ -1 source)
                                                (obs-sdom-info->doms
                                                 (nth source obs-sdom-array)))
                          toggles invals regvals aignet)
                         0)
                  (posp source)
                  (obs-sdom-info->reached (nth sink obs-sdom-array))
                  (equal (obs-sdom-info->doms (nth sink obs-sdom-array)) nil)
                  (< 1 (nfix (nth source refcounts)))
                  (ids-multiply-referenced toggles refcounts))
             (equal (id-eval-toggle sink (cons source toggles) invals regvals aignet)
                    (id-eval-toggle sink toggles invals regvals aignet)))
    :hints (("goal" :use ((:instance toggle-does-not-affect-output-when-sdom-false
                           (lit (lits-find-0val-toggle
                                 (remove-lits-above-id
                                  (1- (nfix source))
                                  (obs-sdom-info->doms
                                   (nth source obs-sdom-array)))
                                 toggles invals regvals aignet))))
             :in-theory (disable toggle-does-not-affect-output-when-sdom-false))))



  (local (defthm b-xor-of-equal-b-xor
           (implies (equal a (b-xor b c))
                    (equal (b-xor b a)
                           (bfix c)))
           :hints(("Goal" :in-theory (enable b-xor)))))

  (local (defthm b-not-when-not-equal
           (implies (and (not (equal b c))
                         (bitp b) (bitp c))
                    (equal (b-not b) c))
           :hints(("Goal" :in-theory (enable b-not)))))

  (local (defthm lit-eval-toggle-of-make-lit
           (equal (lit-eval-toggle (make-lit var neg) toggles invals regvals aignet)
                  (b-xor neg (id-eval-toggle var toggles invals regvals aignet)))
           :hints(("Goal" :in-theory (enable lit-eval-toggle)))))

  (local (in-theory (enable gate-node-supergate)))

  (set-ignore-ok t)

  (defret <fn>-preserves-id-eval-toggle
    (b* ((toggles1 (sweep-observability-dom-supergates-toggles
                    n refcounts invals regvals aignet copy aignet2))
         (toggles2 (sweep-observability-dom-supergates-toggles
                    (+ 1 (nfix n)) refcounts invals regvals aignet new-copy new-aignet2)))
      (implies (and (obs-sdom-array-correct obs-sdom-array refcounts aignet)
                    (obs-sdom-info->reached (nth sink obs-sdom-array))
                    (equal (obs-sdom-info->doms (nth sink obs-sdom-array)) nil)
                    (equal (id-eval-toggle sink toggles1 invals regvals aignet)
                           (id-eval sink invals regvals aignet))
                    (aignet-copies-in-bounds copy aignet2)
                    (aignet-non-gates-copied aignet copy aignet2)
                    (sweep-observability-invariant
                     n refcounts invals regvals aignet copy aignet2))
               (equal (id-eval-toggle sink toggles2 invals regvals aignet)
                      (id-eval sink invals regvals aignet))))
    :hints (("goal" :in-theory (enable <fn>)
             :expand ((:free (refcounts invals regvals aignet copy aignet2)
                       (sweep-observability-dom-supergates-toggles
                        (+ 1 (nfix n)) refcounts invals regvals aignet copy aignet2))
                      (:free (refcounts invals regvals aignet copy aignet2)
                       (sweep-observability-dom-supergates-toggles
                        (+ 1  n) refcounts invals regvals aignet copy aignet2))))
            (acl2::use-termhint
             (b* (((when (<= (get-u32 n refcounts) 1))
                   `(:use ((:instance acl2::mark-clause-is-true
                            (x :singleref)))))
                  ((obs-sdom-info dominfo) (get-sdominfo n obs-sdom-array))
                  ((unless dominfo.reached)
                   `(:use ((:instance acl2::mark-clause-is-true
                            (x :unreach)))))
                  (xor (eql 1 (id->regp n aignet)))
                  (supergate (literal-sort (gate-node-supergate n refcounts aignet)))
                  (toggles (sweep-observability-dom-supergates-toggles
                            n refcounts invals regvals aignet copy aignet2))
                  ((when xor)
                   `(:use ((:instance acl2::mark-clause-is-true
                            (x :xor))
                           (:instance xor-supergate-under-dominators-eval
                            (lits ,(acl2::hq supergate))
                            (doms ,(acl2::hq dominfo.doms))
                            (bound ,(acl2::hq (1- (nfix n))))
                            (toggles ,(acl2::hq toggles))))
                     :in-theory (disable xor-supergate-under-dominators-eval)))
                  ((mv contra new-supergate)
                   (and-supergate-under-dominators supergate dominfo.doms))
                  ((when contra)
                   `(:use ((:instance acl2::mark-clause-is-true
                            (x :contra))
                           (:instance and-supergate-under-dominators-when-contra
                            (lits ,(acl2::hq supergate))
                            (doms ,(acl2::hq dominfo.doms))
                            (bound ,(acl2::hq (1- (nfix n))))
                            (toggles ,(acl2::hq toggles))))
                     :in-theory (disable and-supergate-under-dominators-when-contra))))
               `(:use ((:instance acl2::mark-clause-is-true
                        (x :and))
                       (:instance and-supergate-under-dominators-eval-when-no-contra
                        (lits ,(acl2::hq supergate))
                        (doms ,(acl2::hq dominfo.doms))
                        (bound ,(acl2::hq (1- (nfix n))))
                        (toggles ,(acl2::hq toggles))))
                 :in-theory (disable and-supergate-under-dominators-eval-when-no-contra)))))
    :fn sweep-observability-dom-supergate)


  (defret <fn>-preserves-id-eval-toggle
    (b* ((toggles (sweep-observability-dom-supergates-toggles
                   n refcounts invals regvals aignet new-copy new-aignet2)))
      (implies (and (obs-sdom-array-correct obs-sdom-array refcounts aignet)
                    (obs-sdom-info->reached (nth sink obs-sdom-array))
                    (equal (obs-sdom-info->doms (nth sink obs-sdom-array)) nil)
                    (aignet-copies-in-bounds copy aignet2)
                    (aignet-non-gates-copied aignet copy aignet2))
               (equal (id-eval-toggle sink toggles invals regvals aignet)
                      (id-eval sink invals regvals aignet))))
    :hints (("goal" :induct <call>
             :in-theory (enable (:i <fn>))
             :expand (<call>))
            (acl2::use-termhint
             (b* (((when (zp n)) nil)
                  ((mv copy1 strash1 aignet21)
                   (sweep-observability-dom-supergates-rec
                    (1- n) refcounts obs-sdom-array aignet copy strash gatesimp aignet2)))
               `(:use ((:instance sweep-observability-dom-supergate-preserves-id-eval-toggle
                        (n (+ -1 n))
                        (copy ,(acl2::hq copy1))
                        (strash ,(acl2::hq strash1))
                        (aignet2 ,(acl2::hq aignet21))))
                 :in-theory (disable sweep-observability-dom-supergate-preserves-id-eval-toggle)))))
    :fn sweep-observability-dom-supergates-rec))


(define aignet-dom-supergates-sweep (aignet refcounts obs-sdom-array
                                            (gatesimp gatesimp-p)
                                            aignet2)
  :guard (and (eql (num-fanins aignet) (sdominfo-length obs-sdom-array))
              (<= (sdominfo-length obs-sdom-array) (u32-length refcounts)))
  :returns (new-aignet2)
  (b* (((local-stobjs copy strash)
        (mv copy strash aignet2))
       ((mv copy aignet2) (init-copy-comb aignet copy aignet2))
       ((acl2::hintcontext-bind ((copyi copy)
                                 (aignet2i aignet2)
                                 (strashi strash))))
       ((mv copy strash aignet2)
        (sweep-observability-dom-supergates
         refcounts obs-sdom-array aignet copy strash gatesimp aignet2))
       ((acl2::hintcontext-bind ((copys copy)
                                 (aignet2s aignet2)
                                 (strashs strash))))
       (aignet2 (aignet-copy-outs aignet copy aignet2))
       (aignet2 (aignet-copy-nxsts aignet copy aignet2))
       ((acl2::hintcontext :final)))
    (mv copy strash aignet2))
    
  ///
  (defret stype-counts-of-<fn>
    (and (equal (stype-count :pi new-aignet2) (stype-count :pi aignet))
         (equal (stype-count :reg new-aignet2) (stype-count :reg aignet))
         (equal (stype-count :po new-aignet2) (stype-count :po aignet))))

  (set-ignore-ok t)



  (defret <fn>-preserves-output-eval
    (B* ((sink (lit->var (fanin 0 (lookup-stype n :po aignet)))))
      (implies (and (obs-sdom-array-correct obs-sdom-array refcounts aignet)
                    (obs-sdom-info->reached (nth sink obs-sdom-array))
                    (equal (obs-sdom-info->doms (nth sink obs-sdom-array)) nil))
               (equal (output-eval n invals regvals new-aignet2)
                      (output-eval n invals regvals aignet))))
    :hints(("Goal" :in-theory (enable output-eval))
           (acl2::function-termhint
            <fn>
            (:final
             (if (< (nfix n) (num-outs aignet))
             ;; (b* ((toggles
             ;;       (sweep-observability-dom-supergates-toggles
             ;;        (num-fanins aignet)
             ;;        refcounts invals regvals aignet copys aignet2s)))
             `(:use ((:instance sweep-observability-dom-supergates-rec-preserves-invariant
                      (copy ,(acl2::hq copyi))
                      (aignet2 ,(acl2::hq (node-list-fix aignet2i)))
                      (strash ,(acl2::hq strashi))
                      (n ,(acl2::hq (num-fanins aignet)))))
               :in-theory (disable sweep-observability-dom-supergates-rec-preserves-invariant)
               :expand ((:free (lit toggles)
                         (lit-eval-toggle lit toggles invals regvals aignet))
                        (:free (lit)
                         (lit-eval lit invals regvals aignet))))
             nil)))))

  (defret <fn>-preserves-nxst-eval
    (B* ((sink (lit->var (lookup-reg->nxst n aignet))))
      (implies (and (obs-sdom-array-correct obs-sdom-array refcounts aignet)
                    (obs-sdom-info->reached (nth sink obs-sdom-array))
                    (equal (obs-sdom-info->doms (nth sink obs-sdom-array)) nil))
               (equal (nxst-eval n invals regvals new-aignet2)
                      (nxst-eval n invals regvals aignet))))
    :hints(("Goal" :in-theory (enable nxst-eval))
           (acl2::function-termhint
            <fn>
            (:final
             (if (< (nfix n) (num-regs aignet))
             ;; (b* ((toggles
             ;;       (sweep-observability-dom-supergates-toggles
             ;;        (num-fanins aignet)
             ;;        refcounts invals regvals aignet copys aignet2s)))
             `(:use ((:instance sweep-observability-dom-supergates-rec-preserves-invariant
                      (copy ,(acl2::hq copyi))
                      (aignet2 ,(acl2::hq (node-list-fix aignet2i)))
                      (strash ,(acl2::hq strashi))
                      (n ,(acl2::hq (num-fanins aignet)))))
               :in-theory (disable sweep-observability-dom-supergates-rec-preserves-invariant)
               :expand ((:free (lit toggles)
                         (lit-eval-toggle lit toggles invals regvals aignet))
                        (:free (lit)
                         (lit-eval lit invals regvals aignet))))
             '(:in-theory (enable lookup-reg->nxst-out-of-bounds)))))))

  (defret normalize-aignet2-of-<fn>
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal new-aignet2
                    (let ((aignet2 nil)) <call>)))))



(fty::defprod dom-supergates-sweep-config
  ((gatesimp gatesimp-p :default (make-gatesimp)))
  :tag :dom-supergates-sweep-config)

(define dom-supergates-sweep (aignet aignet2 (config dom-supergates-sweep-config-p))
  :returns (new-aignet2)
  :hooks ((:fix :omit (aignet))) ;; probably just need to fix aignet-record-levels
  (b* (((local-stobjs aignet-levels refcounts obs-sdom-array)
        (mv aignet-levels refcounts obs-sdom-array aignet2))
       (aignet-levels (resize-u32 (num-fanins aignet) aignet-levels))
       (refcounts (resize-u32 (num-fanins aignet) refcounts))
       (obs-sdom-array (resize-sdominfo (num-fanins aignet) obs-sdom-array))
       (aignet-levels (aignet-record-levels aignet aignet-levels))
       (refcounts (aignet-count-superpseudorefs refcounts aignet))
       (obs-sdom-array (aignet-compute-obs-sdom-info obs-sdom-array refcounts aignet-levels aignet))
       (gatesimp (dom-supergates-sweep-config->gatesimp config))
       (aignet2 (aignet-dom-supergates-sweep aignet refcounts obs-sdom-array gatesimp aignet2)))
    (mv aignet-levels refcounts obs-sdom-array aignet2))
  ///
  (defret stype-counts-of-<fn>
    (and (equal (stype-count :pi new-aignet2) (stype-count :pi aignet))
         (equal (stype-count :reg new-aignet2) (stype-count :reg aignet))
         (equal (stype-count :po new-aignet2) (stype-count :po aignet))))

  (local (defthm output-eval-out-of-bounds-split
           (implies (case-split (<= (num-outs aignet) (nfix n)))
                    (equal (output-eval n invals regvals aignet) 0))
           :hints(("Goal" :in-theory (enable output-eval)))))
  (local (defthm nxst-eval-out-of-bounds-split
           (implies (case-split (<= (num-regs aignet) (nfix n)))
                    (equal (nxst-eval n invals regvals aignet) 0))
           :hints(("Goal" :in-theory (enable nxst-eval lookup-reg->nxst)))))

  (defret comb-equiv-of-<fn>
    (comb-equiv new-aignet2 aignet)
    :hints(("Goal" :in-theory (enable comb-equiv outs-comb-equiv nxsts-comb-equiv))))

  (defret normalize-aignet2-of-<fn>
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal new-aignet2
                    (let ((aignet2 nil)) <call>)))))



(fty::defprod n-outputs-dom-supergates-sweep-config
  ((gatesimp gatesimp-p :default (make-gatesimp)))
  :tag :n-outputs-dom-supergates-sweep-config)

(define n-outputs-dom-supergates-sweep ((n natp) aignet aignet2 (config n-outputs-dom-supergates-sweep-config-p))
  :returns (new-aignet2)
  :guard (<= n (num-outs aignet))
  :hooks ((:fix :omit (aignet))) ;; probably just need to fix aignet-record-levels
  (b* (((local-stobjs aignet-levels refcounts obs-sdom-array)
        (mv aignet-levels refcounts obs-sdom-array aignet2))
       (aignet-levels (resize-u32 (num-fanins aignet) aignet-levels))
       (refcounts (resize-u32 (num-fanins aignet) refcounts))
       (obs-sdom-array (resize-sdominfo (num-fanins aignet) obs-sdom-array))
       (aignet-levels (aignet-record-levels aignet aignet-levels))
       (refcounts (aignet-count-superpseudorefs refcounts aignet))
       (obs-sdom-array (aignet-compute-obs-sdom-info-n-outputs
                        n obs-sdom-array refcounts aignet-levels aignet))
       (gatesimp (n-outputs-dom-supergates-sweep-config->gatesimp config))
       (aignet2 (aignet-dom-supergates-sweep aignet refcounts obs-sdom-array gatesimp aignet2)))
    (mv aignet-levels refcounts obs-sdom-array aignet2))
  ///
  (defret stype-counts-of-<fn>
    (and (equal (stype-count :pi new-aignet2) (stype-count :pi aignet))
         (equal (stype-count :reg new-aignet2) (stype-count :reg aignet))
         (equal (stype-count :po new-aignet2) (stype-count :po aignet))))

  (local (defthm output-eval-out-of-bounds-split
           (implies (case-split (<= (num-outs aignet) (nfix n)))
                    (equal (output-eval n invals regvals aignet) 0))
           :hints(("Goal" :in-theory (enable output-eval)))))
  (local (defthm nxst-eval-out-of-bounds-split
           (implies (case-split (<= (num-regs aignet) (nfix n)))
                    (equal (nxst-eval n invals regvals aignet) 0))
           :hints(("Goal" :in-theory (enable nxst-eval lookup-reg->nxst)))))

  (defret n-outputs-comb-equiv-of-<fn>
    (implies (and (< (nfix k) (nfix n))
                  ;; (< (nfix k) (stype-count :po aignet))
                  )
             (equal (output-eval k invals regvals new-aignet2)
                    (output-eval k invals regvals aignet))))

  (defret normalize-aignet2-of-<fn>
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal new-aignet2
                    (let ((aignet2 nil)) <call>)))))


