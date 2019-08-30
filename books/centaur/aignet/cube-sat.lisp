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
(include-book "cnf")
(include-book "copying")
(include-book "eval")
(include-book "centaur/satlink/top" :dir :system)
(include-book "std/util/termhints" :dir :system)
(include-book "transform-stub")
(local (include-book "std/lists/resize-list" :dir :system))
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable resize-list)))

#!satlink
(define cnf-assume-cube ((cube lit-listp)
                         (cnf lit-list-listp))
  :returns (new-cnf lit-list-listp)
  (if (atom cube)
      (lit-list-list-fix cnf)
    (cnf-assume-cube
     (cdr cube)
     (cons (list (lit-fix (car cube)))
           (lit-list-list-fix cnf))))
  ///
  (defthm eval-of-cnf-assume-cube
    (equal (eval-formula (cnf-assume-cube cube cnf) env)
           (b-and (eval-cube cube env)
                  (eval-formula cnf env)))
    :hints(("Goal" :in-theory (enable eval-formula eval-cube eval-clause)))))

(define aignet-sat-check-cube-aux ((cube lit-listp)
                                   (config satlink::config-p)
                                   aignet
                                   aignet-refcounts
                                   bitarr)
  :guard (and (aignet-lit-listp cube aignet)
              (<= (num-fanins aignet) (u32-length aignet-refcounts)))
  :returns (mv status new-bitarr)
  :prepwork ((local (defthmd lits-max-id-val-when-aignet-lit-listp
                      (implies (aignet-lit-listp x aignet)
                               (< (lits-max-id-val x) (num-fanins aignet)))
                      :hints(("Goal" :in-theory (enable aignet-lit-listp
                                                        aignet-idp
                                                        lits-max-id-val)))
                      :rule-classes :forward-chaining)))
  :guard-hints (("goal" :use ((:instance lits-max-id-val-when-aignet-lit-listp
                               (x cube)))))
  :hooks nil
  (b* (((acl2::local-stobjs sat-lits satlink::env$)
        (mv status bitarr sat-lits satlink::env$))
       (sat-lits (resize-aignet->sat (num-fanins aignet) sat-lits))
       ((mv sat-lits cnf) (aignet-lit-list->cnf cube t aignet-refcounts sat-lits aignet nil))
       (sat-cube (aignet-lits->sat-lits cube sat-lits))
       (cnf (satlink::cnf-assume-cube sat-cube cnf))
       ((acl2::hintcontext :sat))
       ((mv status env$)
        (satlink::sat cnf satlink::env$ :config config))
       ((unless (eq status :sat))
        (mv status bitarr sat-lits satlink::env$))
       (bitarr (resize-bits (num-fanins aignet) bitarr))
       (bitarr (cnf->aignet-vals bitarr satlink::env$ sat-lits aignet)))
    (mv status bitarr sat-lits satlink::env$))
  ///
  (set-ignore-ok t)

  (local (defthm cnf-for-aignet-implies-cnf-sat-when-cube-sat-rw
           (b* ((cnf-vals (aignet->cnf-vals
                           invals regvals cnf-vals sat-lits aignet)))
             (implies (and (sat-lits-wfp sat-lits aignet)
                           (bind-free
                            (case-match sat-lits
                              (('mv-nth ''0 x) `((cnf . (mv-nth '1 ,x))))
                              (& nil))
                            (cnf))
                           (cnf-for-aignet aignet cnf sat-lits)
                           (aignet-lit-listp cube aignet)
                           (aignet-lits-have-sat-vars cube sat-lits))
                      (equal (eval-cube
                              (aignet-lits->sat-lits cube sat-lits)
                              cnf-vals)
                             (aignet-eval-conjunction cube invals regvals aignet))))))

  (defret aignet-sat-check-cube-aux-unsat
    (implies (and (equal 1 (aignet-eval-conjunction cube invals regvals aignet))
                  (aignet-lit-listp (lit-list-fix cube) aignet))
             (not (equal status :unsat)))
    :hints (("goal" :do-not-induct t)
            (acl2::function-termhint
             aignet-sat-check-cube-aux
             (:sat
              (b* ((env (aignet->cnf-vals invals regvals nil sat-lits aignet)))
                `(:use ((:instance satlink::sat-when-unsat
                         (formula ,(acl2::hq cnf))
                         (env$ ,(acl2::hq satlink::env$))
                         (config ,(acl2::hq config))
                         (env ,(acl2::hq env))))
                  :in-theory (disable satlink::sat-when-unsat)))))))

  (defret bitarr-size-of-<fn>
    (implies (equal status :sat)
             (equal (len new-bitarr) (num-fanins aignet)))))

(define aignet-sat-check-cube ((cube lit-listp)
                               (config satlink::config-p)
                               aignet
                               bitarr)
  :guard (aignet-lit-listp cube aignet)
  :returns (mv status new-bitarr)
  :prepwork ((local (defthmd lits-max-id-val-when-aignet-lit-listp
                      (implies (aignet-lit-listp x aignet)
                               (< (lits-max-id-val x) (num-fanins aignet)))
                      :hints(("Goal" :in-theory (enable aignet-lit-listp
                                                        aignet-idp
                                                        lits-max-id-val)))
                      :rule-classes :forward-chaining)))
  :guard-hints (("goal" :use ((:instance lits-max-id-val-when-aignet-lit-listp
                               (x cube)))))
  :hooks nil
  (b* (((acl2::local-stobjs refcounts)
        (mv status bitarr refcounts))
       (refcounts (resize-u32 (num-fanins aignet) refcounts))
       (refcounts (aignet-count-refs refcounts aignet))
       ((mv status bitarr)
        (aignet-sat-check-cube-aux cube config aignet refcounts bitarr)))
    (mv status bitarr refcounts))
  ///

  (defret aignet-sat-check-cube-unsat
    (implies (and (equal 1 (aignet-eval-conjunction cube invals regvals aignet))
                  (aignet-lit-listp (lit-list-fix cube) aignet))
             (not (equal status :unsat)))
    :hints (("goal" :do-not-induct t)))

  (defret bitarr-size-of-<fn>
    (implies (equal status :sat)
             (equal (len new-bitarr) (num-fanins aignet)))))





(define aignet-copy-dfs-list ((lits lit-listp)
                              aignet
                              mark
                              copy
                              strash
                              (gatesimp gatesimp-p)
                              aignet2)
  :guard (and (aignet-lit-listp lits aignet)
              (<= (num-fanins aignet) (bits-length mark))
              (<= (num-fanins aignet) (lits-length copy))
              (ec-call (aignet-marked-copies-in-bounds copy mark aignet2))
              (ec-call (aignet-input-copies-in-bounds copy aignet aignet2)))
  :returns (mv new-mark new-copy new-strash new-aignet2)
  :verify-guards nil
  (if (atom lits)
      (b* ((aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                         :exec aignet2)))
        (mv mark copy strash aignet2))
    (b* (((mv mark copy strash aignet2)
          (aignet-copy-dfs-rec (lit->var (car lits)) aignet mark copy strash gatesimp aignet2)))
      (aignet-copy-dfs-list (cdr lits) aignet mark copy strash gatesimp aignet2)))
  ///
  
  (def-aignet-preservation-thms aignet-copy-dfs-list :stobjname aignet2)

  (defret mark-preserved-of-aignet-copy-dfs-list
    (implies (equal 1 (nth n mark))
             (equal (nth n new-mark) 1))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret mark-set-of-aignet-copy-dfs-list
    (implies (member-equal lit (lit-list-fix lits))
             (equal (nth (lit->var lit) new-mark) 1))
    :hints (("goal" :expand (<call>))))

  (defret nth-lit-mark-set-of-<fn>
    (implies (< (nfix n) (len lits))
             (equal (nth (lit->var (nth n lits)) new-mark) 1)))

  (defret copies-sized-of-aignet-copy-dfs-list
    (<= (len copy)
        (len new-copy))
    :hints ((acl2::just-induct-and-expand <call>))
    :rule-classes :linear)

  (defret mark-sized-of-aignet-copy-dfs-list
    (<= (len mark)
        (len new-mark))
    :hints ((acl2::just-induct-and-expand <call>))
    :rule-classes :linear)

  (defret stype-counts-preserved-of-aignet-copy-dfs-list
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2)))
    :hints ((acl2::just-induct-and-expand <call>)))

  ;; (defthm id-in-bounds-when-memo-tablep-bind-free
  ;;   (implies (and (bind-free '((aignet . aignet)) (aignet))
  ;;                 (< (fanin-count aignet) (len arr))
  ;;                 (double-rewrite (aignet-idp n aignet)))
  ;;            (id-in-bounds n arr)))

  ;; (defthm aignet-copies-ok-implies-special-bind-free
  ;;   (implies (and (bind-free '((aignet1 . aignet)) (aignet1))
  ;;                 (aignet-copies-in-bounds copy aignet)
  ;;                 (aignet-idp k aignet1))
  ;;            (aignet-litp (nth-lit k copy) aignet)))

  (local (in-theory (enable lit-negate-cond)))

  (defret aignet-input-copies-in-bounds-of-aignet-copy-dfs-list
    (implies (and ;; (aignet-idp id aignet)
              (aignet-input-copies-in-bounds copy aignet aignet2))
             (aignet-input-copies-in-bounds new-copy aignet new-aignet2))
    :hints ((acl2::just-induct-and-expand <call>)))

  (local (defthm input-when-not-gate-or-const
           (or (equal (stype (car (lookup-id id aignet))) :const)
               (equal (ctype (stype (car (lookup-id id aignet)))) :gate)
               (equal (ctype (stype (car (lookup-id id aignet)))) :input))
           :hints(("Goal" :in-theory (enable ctype)))
           :rule-classes ((:forward-chaining :trigger-terms ((stype (car (lookup-id id aignet))))))))

  (defret aignet-marked-copies-in-bounds-of-aignet-copy-dfs-list
    (implies (and ;; (aignet-idp id aignet)
              (aignet-marked-copies-in-bounds copy mark aignet2)
              (aignet-input-copies-in-bounds copy aignet aignet2))
             (aignet-marked-copies-in-bounds new-copy new-mark new-aignet2))
    :hints ((acl2::just-induct-and-expand <call>)))


  (defret aignet-copies-in-bounds-of-aignet-copy-dfs-list
    (implies (and ;; (aignet-idp id aignet)
              (aignet-copies-in-bounds copy aignet2))
             (aignet-copies-in-bounds new-copy new-aignet2))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret aignet-input-copies-in-bounds-of-aignet-copy-dfs-list-rw
    (implies (and ;; (aignet-idp id aignet)
              (equal (id->type n aignet) (in-type))
              (aignet-input-copies-in-bounds copy aignet aignet2))
             (aignet-litp (nth-lit n new-copy) new-aignet2))
    :hints (("goal" :use ((:instance aignet-input-copies-in-bounds-necc
                           (aignet2 new-aignet2)
                           (copy new-copy)
                           (n n)))
             :in-theory (e/d ()
                             (aignet-input-copies-in-bounds-necc
                              aignet-copy-dfs-list)))))

  (defret aignet-marked-copies-in-bounds-of-aignet-copy-dfs-list-rw
    (implies (and ;; (aignet-idp id aignet)
              (bit->bool (nth n new-mark))
              (aignet-marked-copies-in-bounds copy mark aignet2)
              (aignet-input-copies-in-bounds copy aignet aignet2))
             (aignet-litp (nth-lit n new-copy) new-aignet2))
    :hints (("goal" :use ((:instance aignet-marked-copies-in-bounds-necc
                           (aignet2 new-aignet2)
                           (copy new-copy)
                           (mark new-mark)
                           (n n)))
             :in-theory (e/d ()
                             (aignet-marked-copies-in-bounds-necc
                              aignet-copy-dfs-list)))))

  (verify-guards aignet-copy-dfs-list
    :hints((and stable-under-simplificationp
                '(:in-theory (enable aignet-idp)))))


  (defthm input-copy-values-of-aignet-copy-dfs-list
    (implies (aignet-input-copies-in-bounds copy aignet aignet2)
             (b* (((mv ?new-mark ?new-copy ?new-strash ?new-aignet2)
                   (aignet-copy-dfs-list lits aignet mark copy strash gatesimp aignet2)))
               (equal (input-copy-values n invals regvals aignet new-copy new-aignet2)
                      (input-copy-values n invals regvals aignet copy aignet2))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-list
              lits aignet mark copy
              strash gatesimp aignet2))))

  (defthm reg-copy-values-of-aignet-copy-dfs-list
    (implies (aignet-input-copies-in-bounds copy aignet aignet2)
             (b* (((mv ?new-mark ?new-copy ?new-strash ?new-aignet2)
                   (aignet-copy-dfs-list lits aignet mark copy strash gatesimp aignet2)))
               (equal (reg-copy-values n invals regvals aignet new-copy new-aignet2)
                      (reg-copy-values n invals regvals aignet copy aignet2))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-list
              lits aignet mark copy
              strash gatesimp aignet2))))

  (local (defthm dfs-copy-onto-invar-of-node-list-fix
           (implies (dfs-copy-onto-invar aignet mark copy aignet2)
                    (dfs-copy-onto-invar aignet mark copy (node-list-fix aignet2)))
           :hints (("goal" :expand ((dfs-copy-onto-invar aignet mark copy (node-list-fix aignet2)))))))

  (defthm dfs-copy-onto-invar-holds-of-aignet-copy-dfs-list
    (implies (and ;; (aignet-idp id aignet)
              (dfs-copy-onto-invar aignet mark copy aignet2)
              (aignet-input-copies-in-bounds copy aignet aignet2)
              (aignet-marked-copies-in-bounds copy mark aignet2))
             (b* (((mv mark copy ?strash aignet2)
                   (aignet-copy-dfs-list
                    lits aignet mark copy
                    strash gatesimp aignet2)))
               (dfs-copy-onto-invar aignet mark copy aignet2))))

  (defthm lit-eval-lit-copy-of-aignet-copy-dfs-list
    (implies (and (dfs-copy-onto-invar aignet mark copy aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2))
             (b* (((mv mark copy ?strash aignet2)
                   (aignet-copy-dfs-list
                    lits aignet mark copy
                    strash gatesimp aignet2)))
               (implies (equal 1 (get-bit (lit->var lit) mark))
                        (equal (lit-eval (lit-copy lit copy) invals regvals aignet2)
                               (lit-eval lit
                                         (input-copy-values 0 invals regvals aignet copy aignet2)
                                         (reg-copy-values 0 invals regvals aignet copy aignet2)
                                         aignet)))))
    :hints (("goal" :use ((:instance dfs-copy-onto-invar-holds-of-aignet-copy-dfs-list))
             :in-theory (e/d (lit-copy lit-eval)
                             (dfs-copy-onto-invar-holds-of-aignet-copy-dfs-list))
             :do-not-induct t)))

  (defthm lit-list-marked-preserved-by-aignet-copy-dfs-list
    (implies (lit-list-marked lits mark)
             (lit-list-marked lits (mv-nth 0 (aignet-copy-dfs-list lits1 aignet mark copy strash gatesimp aignet2))))
    :hints(("Goal" :in-theory (enable lit-list-marked)
            :induct (lit-list-marked lits mark))))

  (defthm lit-list-marked-of-aignet-copy-dfs-list
    (lit-list-marked lits (mv-nth 0 (aignet-copy-dfs-list lits aignet mark copy strash gatesimp aignet2)))
    :hints(("Goal" :in-theory (enable aignet-copy-dfs-list lit-list-marked))))

  (defthm aignet-lit-list-copies-in-bounds-of-aignet-copy-dfs-list
    (implies (and (aignet-input-copies-in-bounds copy aignet aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2))
             (b* (((mv ?mark copy ?strash aignet2)
                   (aignet-copy-dfs-list
                    lits aignet mark copy
                    strash gatesimp aignet2)))
               (aignet-lit-listp (lit-list-copies lits copy) aignet2)))
    :hints(("Goal" :in-theory (enable aignet-copy-dfs-list lit-list-copies aignet-lit-listp))))

  (defthm aignet-eval-conjunction-of-lit-list-copies
    (implies (and (dfs-copy-onto-invar aignet mark copy aignet2)
                  (lit-list-marked lits mark))
             (equal (aignet-eval-conjunction (lit-list-copies lits copy) invals regvals aignet2)
                    (aignet-eval-conjunction lits
                                             (input-copy-values 0 invals regvals aignet copy aignet2)
                                             (reg-copy-values 0 invals regvals aignet copy aignet2)
                                             aignet)))
    :hints(("Goal" :in-theory (enable aignet-eval-conjunction
                                      lit-list-marked
                                      lit-list-copies
                                      lit-copy)
            :expand ((:free (lit invals regvals) (lit-eval lit invals regvals aignet))))))

  (defthm aignet-eval-conjunction-of-lit-list-copies-dfs
    (implies (and (dfs-copy-onto-invar aignet mark copy aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2))
             (b* (((mv mark copy ?strash aignet2)
                   (aignet-copy-dfs-list
                    lits1 aignet mark copy
                    strash gatesimp aignet2)))
               (implies (lit-list-marked lits mark)
                        (equal (aignet-eval-conjunction (lit-list-copies lits copy) invals regvals aignet2)
                               (aignet-eval-conjunction lits
                                                        (input-copy-values 0 invals regvals aignet copy aignet2)
                                                        (reg-copy-values 0 invals regvals aignet copy aignet2)
                                                        aignet)))))
    :hints (("goal" :use ((:instance aignet-eval-conjunction-of-lit-list-copies
                           (mark (mv-nth 0 (aignet-copy-dfs-list
                                            lits1 aignet mark copy
                                            strash gatesimp aignet2)))
                           (copy (mv-nth 1 (aignet-copy-dfs-list
                                            lits1 aignet mark copy
                                            strash gatesimp aignet2)))
                           (aignet2 (mv-nth 3 (aignet-copy-dfs-list
                                               lits1 aignet mark copy
                                               strash gatesimp aignet2)))))
             :in-theory (disable aignet-eval-conjunction-of-lit-list-copies)))))



    

;; (define aignet-lit-list-copies-in-bounds ((lits lit-listp)
;;                                           (copy)
;;                                           (aignet2))
;;   :guard (< (lits-max-id-val lits) (lits-length copy))
;;   (if (atom lits)
;;       t
;;     (and (fanin-litp (lit-copy (car lits) copy) aignet2)
;;          (aignet-lit-list-copies-in-bounds (cdr lits) copy aignet2)))
;;   ///
;;   (defthm aignet-lit-list-copies-in-bounds-of-aignet-copy-dfs-list
;;     (implies (and (aignet-input-copies-in-bounds copy aignet aignet2)
;;                   (aignet-marked-copies-in-bounds copy mark aignet2))
;;              (b* (((mv ?mark copy ?strash aignet2)
;;                    (aignet-copy-dfs-list
;;                     lits aignet mark copy
;;                     strash gatesimp aignet2)))
;;                (aignet-lit-list-copies-in-bounds lits copy aignet2)))
;;     :hints(("Goal" :in-theory (enable aignet-copy-dfs-list))))
  
;;   (defthm aignet-lit-list-copies-in-bounds-of-extension
;;     (implies (and (aignet-extension-binding)
;;                   (aignet-lit-list-copies-in-bounds lits copy orig))
;;              (aignet-lit-list-copies-in-bounds lits copy new))))

;; (define aignet-add-copy-outputs ((lits lit-listp)
;;                                  (copy)
;;                                  (aignet2))
;;   :guard (and (< (lits-max-id-val lits) (lits-length copy))
;;               (aignet-lit-list-copies-in-bounds lits copy aignet2))
;;   :guard-hints (("goal" :in-theory (enable aignet-lit-list-copies-in-bounds)))
;;   :returns (new-aignet2)
;;   (b* (((when (atom lits))
;;         (mbe :logic (non-exec (node-list-fix aignet2))
;;              :exec aignet2))
;;        (aignet2 (aignet-add-out (lit-copy (car lits) copy) aignet2)))
;;     (aignet-add-copy-outputs (cdr lits) copy aignet2))
;;   ///
;;   (defret num-outputs-of-<fn>
;;     (equal (stype-count :po new-aignet2)
;;            (+ (len lits) (stype-count :po aignet2))))
;;   (defret stype-count-of-<fn>
;;     (implies (not (equal (stype-fix stype) :po))
;;              (equal (stype-count stype new-aignet2)
;;                     (stype-count stype aignet2))))
;;   (def-aignet-preservation-thms aignet-add-copy-outputs :stobjname aignet2)
  
;;   (defret lookup-po-of-<fn>
;;     (implies (aignet-lit-list-copies-in-bounds lits copy aignet2)
;;              (equal (fanin :co (lookup-stype n :po new-aignet2))
;;                     (cond ((< (nfix n) (stype-count :po aignet2))
;;                            (fanin :co (lookup-stype n :po aignet2)))
;;                           ((< (nfix n) (+ (len lits) (stype-count :po aignet2)))
;;                            (lit-copy (nth (- (nfix n) (stype-count :po aignet2)) lits) copy))
;;                           (t 0))))
;;     :hints (("goal" :induct <call>
;;              :expand ((:free (a b) (lookup-stype n :po (cons a b)))
;;                       (aignet-lit-list-copies-in-bounds lits copy aignet2)))))

;;   (local (defthm aignet-litp-of-lit-copy-nth-when-aignet-lit-list-copies-in-bounds
;;            (implies (and (aignet-lit-list-copies-in-bounds lits copy aignet2)
;;                          (< (nfix n) (len lits)))
;;                     (aignet-idp (lit->var (nth-lit (lit->var (nth n lits)) copy)) aignet2))
;;            :hints(("Goal" :in-theory (enable nth aignet-lit-list-copies-in-bounds)))))


;;   (defret output-eval-of-<fn>
;;     (implies (aignet-lit-list-copies-in-bounds lits copy aignet2)
;;              (equal (output-eval n invals regvals new-aignet2)
;;                     (cond ((< (nfix n) (stype-count :po aignet2))
;;                            (output-eval n invals regvals aignet2))
;;                           ((< (nfix n) (+ (len lits) (stype-count :po aignet2)))
;;                            (lit-eval (lit-copy (nth (- (nfix n) (stype-count :po aignet2)) lits) copy)
;;                                      invals regvals aignet2))
;;                           (t 0))))
;;     :hints(("Goal" :in-theory (enable output-eval aignet-lit-list-copies-in-bounds)
;;             :do-not-induct t))))




(define aignet-conjoin-copies ((conj-lit litp)
                               (lits lit-listp)
                               (copy)
                               (strash)
                               (aignet2))
  :guard (and (< (lits-max-id-val lits) (lits-length copy))
              (fanin-litp conj-lit aignet2)
              (aignet-lit-listp (lit-list-copies lits copy) aignet2))
  :guard-hints (("goal" :in-theory (enable lit-list-copies aignet-lit-listp)))
  :returns (mv (conj litp :rule-classes :type-prescription)
               new-strash
               new-aignet2)
  (b* (((when (atom lits))
        (b* ((aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                           :exec aignet2)))
          (mv (lit-fix conj-lit) strash aignet2)))
       ((mv conj-lit strash aignet2)
        (aignet-hash-and (lit-copy (car lits) copy) conj-lit (aignet::default-gatesimp) strash aignet2)))
    (aignet-conjoin-copies conj-lit (cdr lits) copy strash aignet2))
  ///
  (defret stype-count-of-<fn>
    (implies (and (not (equal (stype-fix stype) :and))
                  (not (equal (stype-fix stype) :xor)))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))
  (def-aignet-preservation-thms aignet-conjoin-copies :stobjname aignet2)

  

  (defret lit-eval-of-<fn>
    (implies (and (aignet-lit-listp (lit-list-copies lits copy) aignet2)
                  (aignet-litp conj-lit aignet2))
             (equal (lit-eval conj invals regvals new-aignet2)
                    (b-and (lit-eval conj-lit invals regvals aignet2)
                           (aignet-eval-conjunction (lit-list-copies lits copy) invals regvals aignet2))))
    :hints(("Goal" :in-theory (enable lit-list-copies
                                      aignet-lit-listp
                                      ;; aignet-lit-list-copies-in-bounds
                                      aignet-eval-conjunction)
            :induct <call>
            :expand (<call>))))

  (defret aignet-litp-of-<fn>
    (implies (aignet-litp conj-lit aignet2)
             (aignet-litp conj new-aignet2))))

(define aignet-copy-with-conjoined-output ((lits lit-listp)
                                           (aignet)
                                           (aignet2))
  :guard (aignet-lit-listp lits aignet)
  :guard-debug t
  :guard-hints (("goal" :do-not-induct t
                 :use ((:instance lits-max-id-val-when-aignet-lit-listp
                        (x lits)))))
  :returns (new-aignet2)
  :prepwork ((local (defthmd lits-max-id-val-when-aignet-lit-listp
                      (implies (aignet-lit-listp x aignet)
                               (< (lits-max-id-val x) (num-fanins aignet)))
                      :hints(("Goal" :in-theory (enable aignet-lit-listp
                                                        aignet-idp
                                                        lits-max-id-val)))
                      :rule-classes :forward-chaining)))
  (b* (((acl2::local-stobjs mark copy strash)
        (mv aignet2 mark copy strash))
       ((mv copy aignet2) (init-copy-comb aignet copy aignet2))
       (mark (resize-bits (num-fanins aignet) mark))
       ((mv mark copy strash aignet2)
        (aignet-copy-dfs-list lits aignet mark copy strash (default-gatesimp) aignet2))
       ((mv conjunction strash aignet2)
        (aignet-conjoin-copies 1 lits copy strash aignet2))
       (aignet2 (aignet-add-out conjunction aignet2)))
    (mv aignet2 mark copy strash))
  ///
  (defret stype-counts-of-<fn>
    (and (equal (stype-count :pi new-aignet2)
                (stype-count :pi aignet))
         (equal (stype-count :reg new-aignet2)
                (stype-count :reg aignet))
         (equal (stype-count :po new-aignet2)
                1)))

  (defret output-eval-of-<fn>
    (implies (aignet-lit-listp lits aignet)
             (equal (output-eval 0 invals regvals new-aignet2)
                    (aignet-eval-conjunction lits invals regvals aignet)))
    :hints (("goal" :do-not-induct t
             :in-theory (enable output-eval lookup-stype))))

  (defret output-lit-eval-of-<fn>
    (implies (aignet-lit-listp lits aignet)
             (equal (lit-eval (fanin :co (lookup-stype 0 :po new-aignet2)) invals regvals new-aignet2)
                    (aignet-eval-conjunction lits invals regvals aignet)))
    :hints (("goal" :do-not-induct t
             :use output-eval-of-aignet-copy-with-conjoined-output
             :in-theory (e/d (output-eval)
                             (output-eval-of-aignet-copy-with-conjoined-output
                              <fn>))))))
    

;; ;; BOZO doesn't hook up register inputs at all -- only for combinational use
;; (define aignet-copy-with-outputs ((lits lit-listp)
;;                                   (aignet)
;;                                   (aignet2))
;;   :guard (aignet-lit-listp lits aignet)
;;   :guard-debug t
;;   :guard-hints (("goal" :do-not-induct t
;;                  :use ((:instance lits-max-id-val-when-aignet-lit-listp
;;                         (x lits)))))
;;   :returns (new-aignet2)
;;   :prepwork ((local (defthmd lits-max-id-val-when-aignet-lit-listp
;;                       (implies (aignet-lit-listp x aignet)
;;                                (< (lits-max-id-val x) (num-fanins aignet)))
;;                       :hints(("Goal" :in-theory (enable aignet-lit-listp
;;                                                         aignet-idp
;;                                                         lits-max-id-val)))
;;                       :rule-classes :forward-chaining)))
;;   (b* (((acl2::local-stobjs mark copy strash)
;;         (mv aignet2 mark copy strash))
;;        ((mv copy aignet2) (init-copy-comb aignet copy aignet2))
;;        (mark (resize-bits (num-fanins aignet) mark))
;;        ((mv mark copy strash aignet2)
;;         (aignet-copy-dfs-list lits aignet mark copy strash (default-gatesimp) aignet2))
;;        (aignet2 (aignet-add-copy-outputs lits copy aignet2)))
;;     (mv aignet2 mark copy strash))
;;   ///
;;   (defret output-eval-of-<fn>
;;     (implies (aignet-lit-listp lits aignet)
;;              (equal (output-eval n invals regvals new-aignet2)
;;                     (if (< (nfix n) (len lits))
;;                         (lit-eval (nth n lits) invals regvals aignet)
;;                       0)))
;;     :hints (("goal" :do-not-induct t)))

;;   (defret output-lit-eval-of-<fn>
;;     (implies (aignet-lit-listp lits aignet)
;;              (equal (lit-eval (fanin :co (lookup-stype n :po new-aignet2)) invals regvals new-aignet2)
;;                     (if (< (nfix n) (len lits))
;;                         (lit-eval (nth n lits) invals regvals aignet)
;;                       0)))
;;     :hints (("goal" :do-not-induct t
;;              :use output-eval-of-aignet-copy-with-outputs
;;              :in-theory (e/d (output-eval)
;;                              (output-eval-of-aignet-copy-with-outputs
;;                               <fn>)))))

;;   (defret stype-counts-of-<fn>
;;     (and (equal (stype-count :pi new-aignet2) (stype-count :pi aignet))
;;          (equal (stype-count :reg new-aignet2) (stype-count :reg aignet))
;;          (equal (stype-count :po new-aignet2) (len lits)))))


;; (define aignet-outputs->cube ((n natp)
;;                               aignet
;;                               (cube lit-listp))
;;   :returns (new-cube lit-listp)
;;   :guard (<= n (num-outs aignet))
;;   :measure (nfix (- (num-outs aignet) (nfix n)))
;;   (b* (((when (mbe :logic (zp (- (num-outs aignet) (nfix n)))
;;                    :exec (eql (num-outs aignet) n)))
;;         (lit-list-fix cube)))
;;     (aignet-outputs->cube (1+ (lnfix n))
;;                           aignet
;;                           (cons (outnum->fanin n aignet)
;;                                 (lit-list-fix cube))))
;;   ///
;;   (fty::deffixequiv aignet-outputs->cube)

;;   (defret aignet-lit-listp-of-<fn>
;;     (implies (aignet-lit-listp cube aignet)
;;              (aignet-lit-listp new-cube aignet)))

;;   (local (defun-sk aignet-outputs->cube-norm-cond (n aignet)
;;            (forall cube
;;                    (implies (syntaxp (not (equal cube ''nil)))
;;                             (equal (aignet-outputs->cube n aignet cube)
;;                                    (append (aignet-outputs->cube n aignet nil)
;;                                            (lit-list-fix cube)))))
;;            :rewrite :direct))

;;   (local (in-theory (disable aignet-outputs->cube-norm-cond)))

;;   (local (defthm aignet-outputs->cube-norm-lemma
;;            (aignet-outputs->cube-norm-cond n aignet)
;;            :hints (("goal" :induct (aignet-outputs->cube n aignet cube))
;;                    (and stable-under-simplificationp
;;                         `(:expand (,(car (last clause))
;;                                    (:free (cube) (aignet-outputs->cube n aignet cube))))))))

;;   (defthm aignet-outputs->cube-norm
;;     (implies (syntaxp (not (equal cube ''nil)))
;;              (equal (aignet-outputs->cube n aignet cube)
;;                     (append (aignet-outputs->cube n aignet nil)
;;                             (lit-list-fix cube)))))

;;   (local (defthm aignet-eval-conjunction-of-append
;;            (equal (aignet-eval-conjunction (append x y) invals regvals aignet)
;;                   (b-and (aignet-eval-conjunction x invals regvals aignet)
;;                          (aignet-eval-conjunction y invals regvals aignet)))
;;            :hints(("Goal" :in-theory (enable aignet-eval-conjunction)))))

;;   (local (defthm aignet-eval-conjunction-of-cons
;;            (equal (aignet-eval-conjunction (cons x y) invals regvals aignet)
;;                   (b-and (lit-eval x invals regvals aignet)
;;                          (aignet-eval-conjunction y invals regvals aignet)))
;;            :hints(("Goal" :in-theory (enable aignet-eval-conjunction)))))
;;   (local (defthm aignet-eval-conjunction-of-nil
;;            (equal (aignet-eval-conjunction nil invals regvals aignet)
;;                   1)
;;            :hints(("Goal" :in-theory (enable aignet-eval-conjunction)))))

;;   (defret aignet-eval-conjunction-of-aignet-outputs->cube-under-comb-equiv
;;     (implies (and (outs-comb-equiv aignet aignet2)
;;                   (equal (stype-count :po aignet) (stype-count :po aignet2)))
;;              (equal (aignet-eval-conjunction
;;                      (aignet-outputs->cube n aignet nil)
;;                      invals regvals aignet)
;;                     (aignet-eval-conjunction
;;                      (aignet-outputs->cube n aignet2 nil)
;;                      invals regvals aignet2)))
;;     :hints (("goal" :induct <call>
;;              :expand ((:free (aignet) (aignet-outputs->cube n aignet nil))))
;;             (and stable-under-simplificationp
;;                  '(:use ((:instance outs-comb-equiv-necc))
;;                    :in-theory (e/d (output-eval)
;;                                    (outs-comb-equiv-necc
;;                                     OUTS-COMB-EQUIV-IMPLIES-EQUAL-OUTPUT-EVAL-4)))))
;;     :rule-classes nil)

;;   (defret aignet-eval-conjunction-of-aignet-outputs->cube-of-aignet-comb-transform!-stub
;;     (b* ((aignet2 (aignet-comb-transform!-stub aignet config)))
;;       (equal (aignet-eval-conjunction
;;               (aignet-outputs->cube n aignet2 nil)
;;               invals regvals aignet2)
;;              (aignet-eval-conjunction
;;               (aignet-outputs->cube n aignet nil)
;;               invals regvals aignet)))
;;     :hints (("goal" :use ((:instance aignet-eval-conjunction-of-aignet-outputs->cube-under-comb-equiv
;;                            (aignet (aignet-comb-transform!-stub aignet config))
;;                            (aignet2 aignet))))))

;;   (local (fty::deffixcong satlink::lit-list-equiv satlink::lit-list-equiv (nthcdr n x) x
;;            :hints(("Goal" :in-theory (enable nthcdr)))))

;;   (local (defthm nthcdr-of-nil
;;            (equal (nthcdr n nil) nil)))

;;   (local (defthm consp-of-nthcdr
;;            (iff (consp (nthcdr n x))
;;                 (< (nfix n) (len x)))
;;            :hints(("Goal" :in-theory (enable nthcdr len)))))

;;   (local (defthm car-of-nthcdr
;;            (equal (car (nthcdr n x))
;;                   (nth n x))
;;            :hints(("Goal" :in-theory (enable nthcdr nth)))))

;;   (local (defthm cdr-of-nthcdr
;;            (equal (cdr (nthcdr n x))
;;                   (nthcdr n (cdr x)))))

;;   (defret aignet-eval-conjunction-of-aignet-outputs->cube-of-aignet-copy-with-outputs
;;     (b* ((aignet2 (aignet-copy-with-outputs cube aignet aignet2)))
;;       (implies (aignet-lit-listp cube aignet)
;;                (equal (aignet-eval-conjunction
;;                        (aignet-outputs->cube n aignet2 nil)
;;                        invals regvals aignet2)
;;                       (aignet-eval-conjunction
;;                        (nthcdr n cube) invals regvals aignet))))
;;     :hints (("goal" :induct (aignet-outputs->cube n (aignet-copy-with-outputs cube aignet aignet2) nil)
;;              :expand ((:free (aignet) (aignet-outputs->cube n aignet nil))
;;                       (aignet-eval-conjunction (nthcdr n cube) invals regvals aignet))))))


(define aignet-vals-copy-pis ((n natp)
                              (vals) ;; values for aignet to copy from
                              (bitarr) ;; values for aignet2 to copy to
                              (aignet)
                              (aignet2))
  :guard (and (<= n (num-ins aignet))
              (<= (num-ins aignet) (num-ins aignet2))
              (<= (num-fanins aignet) (bits-length vals))
              (<= (num-fanins aignet2) (bits-length bitarr)))
  :returns (new-bitarr)
  :measure (nfix (- (num-ins aignet) (nfix n)))
  (b* (((when (mbe :logic (zp (- (num-ins aignet) (nfix n)))
                   :exec (eql (num-ins aignet) n)))
        bitarr)
       (id1 (innum->id n aignet))
       (id2 (innum->id n aignet2))
       (bitarr (set-bit id2 (get-bit id1 vals) bitarr)))
    (aignet-vals-copy-pis (1+ (lnfix n)) vals bitarr aignet aignet2))
  ///
  (defret len-of-<fn>
    (implies (<= (num-fanins aignet2) (len bitarr))
             (equal (len new-bitarr) (len bitarr))))

  (local (defthm stype-when-lookup-stype
           (implies (and (not (equal (ctype stype) (out-ctype))))
                    (equal (stype (car (lookup-id (fanin-count (lookup-stype n stype aignet)) aignet)))
                           (if (< (nfix n) (stype-count stype aignet))
                               (stype-fix stype)
                             :const)))
           :hints(("Goal" :in-theory (enable fanin-count lookup-stype lookup-id stype-count)))))

  (local (defthm stype-when-lookup-stype-rw
           (implies (and (equal (nfix i) (fanin-count (lookup-stype n stype aignet)))
                         (not (equal (ctype stype) (out-ctype))))
                    (equal (stype (car (lookup-id i aignet)))
                           (if (< (nfix n) (stype-count stype aignet))
                               (stype-fix stype)
                             :const)))
           :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))))

  (local (in-theory (disable nth update-nth)))

  (defret nth-of-<fn>
    (implies (<= (stype-count :pi aignet) (stype-count :pi aignet2))
             (equal (nth i new-bitarr)
                    (if (and (equal (stype (car (lookup-id i aignet2))) :pi)
                             (<= (nfix n) (stype-count :pi (cdr (lookup-id i aignet2))))
                             (< (stype-count :pi (cdr (lookup-id i aignet2))) 
                                (stype-count :pi aignet)))
                        (bfix (nth (fanin-count (lookup-stype (stype-count :pi (cdr (lookup-id i aignet2))) :pi aignet))
                                   vals))
                      (nth i bitarr))))
    :hints (("goal" :induct <call> :expand (<call>)
             :in-theory (e/d* (acl2::arith-equiv-forwarding)
                              ((:d <fn>)))))))

(define aignet-vals-copy-regs ((n natp)
                              (vals) ;; values for aignet to copy from
                              (bitarr) ;; values for aignet2 to copy to
                              (aignet)
                              (aignet2))
  :guard (and (<= n (num-regs aignet))
              (<= (num-regs aignet) (num-regs aignet2))
              (<= (num-fanins aignet) (bits-length vals))
              (<= (num-fanins aignet2) (bits-length bitarr)))
  :returns (new-bitarr)
  :measure (nfix (- (num-regs aignet) (nfix n)))
  (b* (((when (mbe :logic (zp (- (num-regs aignet) (nfix n)))
                   :exec (eql (num-regs aignet) n)))
        bitarr)
       (id1 (regnum->id n aignet))
       (id2 (regnum->id n aignet2))
       (bitarr (set-bit id2 (get-bit id1 vals) bitarr)))
    (aignet-vals-copy-regs (1+ (lnfix n)) vals bitarr aignet aignet2))
  ///
  (defret len-of-<fn>
    (implies (<= (num-fanins aignet2) (len bitarr))
             (equal (len new-bitarr) (len bitarr))))

  (local (defthm stype-when-lookup-stype
           (implies (and (not (equal (ctype stype) (out-ctype))))
                    (equal (stype (car (lookup-id (fanin-count (lookup-stype n stype aignet)) aignet)))
                           (if (< (nfix n) (stype-count stype aignet))
                               (stype-fix stype)
                             :const)))
           :hints(("Goal" :in-theory (enable fanin-count lookup-stype lookup-id stype-count)))))

  (local (defthm stype-when-lookup-stype-rw
           (implies (and (equal (nfix i) (fanin-count (lookup-stype n stype aignet)))
                         (not (equal (ctype stype) (out-ctype))))
                    (equal (stype (car (lookup-id i aignet)))
                           (if (< (nfix n) (stype-count stype aignet))
                               (stype-fix stype)
                             :const)))
           :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))))

  (local (in-theory (disable nth update-nth)))

  (defret nth-of-<fn>
    (implies (<= (stype-count :reg aignet) (stype-count :reg aignet2))
             (equal (nth i new-bitarr)
                    (if (and (equal (stype (car (lookup-id i aignet2))) :reg)
                             (<= (nfix n) (stype-count :reg (cdr (lookup-id i aignet2))))
                             (< (stype-count :reg (cdr (lookup-id i aignet2))) 
                                (stype-count :reg aignet)))
                        (bfix (nth (fanin-count (lookup-stype (stype-count :reg (cdr (lookup-id i aignet2))) :reg aignet))
                                   vals))
                      (nth i bitarr))))
    :hints (("goal" :induct <call> :expand (<call>)
             :in-theory (e/d* (acl2::arith-equiv-forwarding)
                              ((:d <fn>)))))))

(local (in-theory (disable w)))

(define aignet-transform-sat-check-cube ((cube lit-listp)
                                         (sat-config satlink::config-p)
                                         (xform-config)
                                         aignet
                                         bitarr
                                         state)
  :guard (aignet-lit-listp cube aignet)
  :returns (mv status new-bitarr new-state)
  :hooks nil
  (b* (((acl2::local-stobjs aignet2 vals)
        ;; NOTE: bitarr will be the original aignet version of the satisfying assign
        ;; vals the transformed aignet2's version
        ;; 
        (mv status bitarr state aignet2 vals))
       (aignet2 (aignet-copy-with-conjoined-output cube aignet aignet2))
       ((mv aignet2 state) (aignet-comb-transform!-stub aignet2 xform-config state))
       (new-cube (list (outnum->fanin 0 aignet2)))
       ((acl2::hintcontext :sat))
       ((mv status vals)
        (aignet-sat-check-cube new-cube sat-config aignet2 vals))
       ((unless (eq status :sat))
        (mv status bitarr state aignet2 vals))
       (bitarr (resize-bits (num-fanins aignet) bitarr))
       (bitarr (aignet-vals-copy-pis 0 vals bitarr aignet2 aignet))
       (bitarr (aignet-vals-copy-regs 0 vals bitarr aignet2 aignet))
       (bitarr (aignet-eval bitarr aignet)))
    (mv :sat bitarr state aignet2 vals))
       
       
  ///
  (set-ignore-ok t)

  (local (defthm lit-eval-output-to-output-eval
           (equal (lit-eval (fanin :co (lookup-stype n :po aignet))
                            invals regvals aignet)
                  (output-eval n invals regvals aignet))
           :hints(("Goal" :in-theory (enable output-eval)))))

  (defret aignet-transform-sat-check-cube-unsat
    (implies (and (equal 1 (aignet-eval-conjunction cube invals regvals aignet))
                  (aignet-lit-listp (lit-list-fix cube) aignet))
             (not (eq status :unsat)))
    :hints (("goal" :do-not-induct t)
            (acl2::function-termhint
             aignet-transform-sat-check-cube
             (:sat
              `(:use ((:instance aignet-sat-check-cube-unsat
                       (cube ,(acl2::hq new-cube))
                       (config ,(acl2::hq sat-config))
                       (aignet ,(acl2::hq aignet2))
                       (bitarr ,(acl2::hq vals))
                       (invals invals)
                       (regvals regvals)))
                  :in-theory (e/d (aignet-eval-conjunction)
                                  (aignet-sat-check-cube-unsat)))))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))

