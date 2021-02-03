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
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))








(define collect-unreachable-nodes ((n natp) refcounts obs-sdom-array)
  :measure (nfix (- (sdominfo-length obs-sdom-array) (nfix n)))
  :guard (<= (sdominfo-length obs-sdom-array) (u32-length refcounts))
  (if (<= (sdominfo-length obs-sdom-array) (lnfix n))
      nil
    (if (and (< 1 (get-u32 n refcounts))
             (not (obs-sdom-info->reached (get-sdominfo n obs-sdom-array))))
        (cons (lnfix n)
              (collect-unreachable-nodes (1+ (lnfix n)) refcounts obs-sdom-array))
      (collect-unreachable-nodes (1+ (lnfix n)) refcounts obs-sdom-array))))


(define mark-unreachable-nodes ((n natp) refcounts obs-sdom-array mark)
  :returns (new-mark)
  :measure (nfix (- (sdominfo-length obs-sdom-array) (nfix n)))
  :guard (and (<= n (sdominfo-length obs-sdom-array))
              (<= (sdominfo-length obs-sdom-array) (u32-length refcounts))
              (<= (sdominfo-length obs-sdom-array) (bits-length mark)))
  (b* (((when (mbe :logic (zp (- (sdominfo-length obs-sdom-array) (nfix n)))
                   :exec (eql (sdominfo-length obs-sdom-array) n)))
        mark)
       ((unless (and (< 1 (get-u32 n refcounts))
                     (not (obs-sdom-info->reached (get-sdominfo n obs-sdom-array)))))
        (mark-unreachable-nodes (1+ (lnfix n)) refcounts obs-sdom-array mark))
       (mark (set-bit n 1 mark)))
    (mark-unreachable-nodes (1+ (lnfix n)) refcounts obs-sdom-array mark))
  ///
  (defret nth-bit-of-<fn>
    (equal (nth i new-mark)
           (if (and (<= (nfix n) (nfix i))
                    (< (nfix i) (len obs-sdom-array))
                    (< 1 (nfix (nth i refcounts)))
                    (not (obs-sdom-info->reached (nth i obs-sdom-array))))
               1
             (nth i mark))))

  (defret length-of-<fn>
    (implies (<= (len obs-sdom-array) (len mark))
             (equal (len new-mark) (len mark)))))


(define init-unreachable-node-copies ((n natp) refcounts obs-sdom-array copy)
  :returns (new-copy)
  :measure (nfix (- (sdominfo-length obs-sdom-array) (nfix n)))
  :guard (and (<= n (sdominfo-length obs-sdom-array))
              (<= (sdominfo-length obs-sdom-array) (u32-length refcounts))
              (<= (sdominfo-length obs-sdom-array) (lits-length copy)))
  (b* (((when (mbe :logic (zp (- (sdominfo-length obs-sdom-array) (nfix n)))
                   :exec (eql (sdominfo-length obs-sdom-array) n)))
        copy)
       ((unless (and (< 1 (get-u32 n refcounts))
                     (not (obs-sdom-info->reached (get-sdominfo n obs-sdom-array)))))
        (init-unreachable-node-copies (1+ (lnfix n)) refcounts obs-sdom-array copy))
       (copy (set-lit n 0 copy)))
    (init-unreachable-node-copies (1+ (lnfix n)) refcounts obs-sdom-array copy))
  ///
  (defret nth-lit-of-<fn>
    (equal (nth-lit i new-copy)
           (if (and (<= (nfix n) (nfix i))
                    (< (nfix i) (len obs-sdom-array))
                    (< 1 (nfix (nth i refcounts)))
                    (not (obs-sdom-info->reached (nth i obs-sdom-array))))
               0
             (nth-lit i copy))))

  (defret length-of-<fn>
    (implies (<= (len obs-sdom-array) (len copy))
             (equal (len new-copy) (len copy))))

  (defret aignet-copies-in-bounds-of-<fn>
    (implies (aignet-copies-in-bounds copy aignet2)
             (aignet-copies-in-bounds new-copy aignet2))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defret aignet-input-copies-in-bounds-of-<fn>
    (implies (aignet-input-copies-in-bounds copy aignet aignet2)
             (aignet-input-copies-in-bounds new-copy aignet aignet2))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defret aignet-marked-copies-in-bounds-of-<fn>
    (implies (aignet-marked-copies-in-bounds copy mark aignet2)
             (aignet-marked-copies-in-bounds new-copy 
                                             (mark-unreachable-nodes n refcounts obs-sdom-array mark)
                                             aignet2))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause))))))))


(define nat-list-max-or-minus1 ((x nat-listp))
  (if (atom x)
      -1
    (max (lnfix (car x))
         (nat-list-max-or-minus1 (cdr x)))))

(define unreachable-node-toggles ((n natp) refcounts obs-sdom-array invals regvals aignet)
  :returns (toggles nat-listp)
  :measure (nfix n)
  :guard (and (<= n (num-fanins aignet))
              (<= (num-fanins aignet) (sdominfo-length obs-sdom-array))
              (<= (num-fanins aignet) (u32-length refcounts))
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  :verify-guards nil
  (b* (((when (zp n)) nil)
       (n (1- n))
       ((unless (and (< 1 (get-u32 n refcounts))
                     (not (obs-sdom-info->reached (get-sdominfo n obs-sdom-array)))))
        (unreachable-node-toggles n refcounts obs-sdom-array invals regvals aignet))
       (rest (unreachable-node-toggles n refcounts obs-sdom-array invals regvals aignet))
       (toggledp (eql (id-eval-toggle n rest invals regvals aignet) 1)))
    (if toggledp (cons n rest) rest))
  ///
  (verify-guards unreachable-node-toggles
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defret ids-multiply-referenced-of-<fn>
    (ids-multiply-referenced toggles refcounts)
    :hints(("Goal" :in-theory (enable ids-multiply-referenced))))

  (defret nat-list-max-or-minus1-of-<fn>
    (< (nat-list-max-or-minus1 toggles) (nfix n))
    :hints(("Goal" :in-theory (enable nat-list-max-or-minus1)))
    :rule-classes :linear)

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

  ;; (defthm id-eval-toggle-of-cons-greater
  ;;   (implies (< (nfix i) (nfix n))
  ;;            (equal (id-eval-toggle i (cons n toggles) invals regvals aignet)
  ;;                   (id-eval-toggle i toggles invals regvals aignet))))

  (defret id-eval-toggle-of-<fn>
    (implies (and (obs-sdom-array-correct obs-sdom-array refcounts aignet)
                  (obs-sdom-info->reached (nth sink obs-sdom-array))
                  (equal (obs-sdom-info->doms (nth sink obs-sdom-array)) nil))
             (equal (id-eval-toggle sink toggles invals regvals aignet)
                    (id-eval sink invals regvals aignet)))
    :hints (("goal" :induct <call>)))

  (defret lit-eval-toggle-of-<fn>
    (implies (and (obs-sdom-array-correct obs-sdom-array refcounts aignet)
                  (obs-sdom-info->reached (nth (lit->var lit) obs-sdom-array))
                  (equal (obs-sdom-info->doms (nth (lit->var lit) obs-sdom-array)) nil))
             (equal (lit-eval-toggle lit toggles invals regvals aignet)
                    (lit-eval lit invals regvals aignet)))
    :hints(("Goal" :in-theory (e/d (lit-eval-toggle lit-eval)
                                   (<fn>)))))

  (defret id-eval-toggle-of-unreachable-node-of-<fn>
    (implies (and (< (nfix i) (nfix n))
                  (< 1 (nfix (nth i refcounts)))
                  (not (obs-sdom-info->reached (nth i obs-sdom-array))))
             (equal (id-eval-toggle i toggles invals regvals aignet) 0))
    :hints (("goal" :induct <call>)
            (and stable-under-simplificationp
                 '(:cases ((equal (nfix i) (+ -1 n)))))))

  (defret member-of-<fn>-when-not-refcounts
    (implies (<= (nfix (nth i refcounts)) 1)
             (not (member-equal i toggles)))
    :hints (("goal" :induct <call>)))

  (defret member-of-<fn>-when-reached
    (implies (obs-sdom-info->reached (nth i obs-sdom-array))
             (not (member-equal i toggles)))
    :hints (("goal" :induct <call>)))

  (defret member-of-<fn>-when-greater
    (implies (<= (nfix n) (nfix i))
             (not (member-equal i toggles))))

  (defret member-of-<fn>-when-non-gate
    (implies (not (equal (ctype (stype (car (lookup-id i aignet)))) :gate))
             (iff (member-equal i toggles)
                  (and (equal (id-eval i invals regvals aignet) 1)
                       (< 1 (nfix (nth i refcounts)))
                       (not (obs-sdom-info->reached (nth i obs-sdom-array)))
                       (< (nfix i) (nfix n)))))
    :hints(("Goal" :in-theory (enable id-eval-toggle id-eval)))))
       
       




(define ids-marked ((x nat-listp) mark)
  (if (atom x)
      t
    (and (mbe :logic (equal 1 (get-bit (car x) mark))
              :exec (and (< (car x) (bits-length mark))
                         (eql 1 (get-bit (car x) mark))))
         (ids-marked (cdr x) mark)))
  ///
  (defthmd member-implies-marked-when-ids-marked
    (implies (and (ids-marked x mark)
                  (member-equal n x))
             (equal (nth n mark) 1)))

  (defthmd member-nat-list-fix-implies-marked-when-ids-marked
    (implies (and (ids-marked x mark)
                  (member-equal (nfix n) (acl2::nat-list-fix x)))
             (equal (nth n mark) 1))
    :hints(("Goal" :in-theory (enable acl2::nat-list-fix)))))

(define ids-marked-badguy ((x nat-listp) mark)
  :returns (badguy)
  (if (atom x)
      0
    (if (mbe :logic (equal 1 (get-bit (car x) mark))
             :exec (and (< (car x) (bits-length mark))
                        (eql 1 (get-bit (car x) mark))))
        (ids-marked-badguy (cdr x) mark)
      (lnfix (car x))))
  ///
  (defret ids-not-marked-implies-badguy
    (implies (not (ids-marked x mark))
             (and (member-equal badguy (acl2::nat-list-fix x))
                  (not (equal (nth badguy mark) 1))))
    :hints(("Goal" :in-theory (enable ids-marked)))))


(defsection aignet-copy-dfs-rec-unreachable
  

  (defun-sk dfs-copy-toggle-invar (aignet mark copy toggles invals regvals aignet2)
    (forall id
            (implies (or (equal 1 (get-bit id mark))
                         (equal (ctype (stype (car (lookup-id id aignet)))) :input))
                     (equal (lit-eval (nth-lit id copy) invals regvals aignet2)
                            (id-eval-toggle id toggles
                                            ;; (input-copy-values 0 invals regvals aignet copy aignet2)
                                            ;; (reg-copy-values 0 invals regvals aignet copy aignet2)
                                            invals regvals
                                            aignet))))
    :rewrite :direct)

  (in-theory (disable dfs-copy-toggle-invar))

  (local (defthm equal-b-xor
           (implies (equal (b-xor a b) c)
                    (equal (b-xor a c) (bfix b)))
           :hints(("Goal" :in-theory (enable b-xor)))))

  (local (defthm b-xor-nest
           (equal (b-xor a (b-xor a b))
                  (bfix b))
           :hints(("Goal" :in-theory (enable b-xor)))))

  (local (defthm dfs-copy-toggle-invar-implies-id-eval
           (implies (and (dfs-copy-toggle-invar aignet mark copy toggles invals regvals aignet2)
                         ;; (aignet-idp id aignet)
                         (equal 1 (get-bit id mark)))
                    (equal (id-eval (lit->var (nth-lit id copy)) invals regvals aignet2)
                           (b-xor (lit->neg (nth-lit id copy))
                                  (id-eval-toggle id toggles
                                                  invals regvals
                                                  ;; (input-copy-values 0 invals regvals aignet copy aignet2)
                                                  ;; (reg-copy-values 0 invals regvals aignet copy aignet2)
                                                  aignet))))
           :hints (("goal" :use dfs-copy-toggle-invar-necc
                    :in-theory (e/d (lit-eval lit-eval-toggle) (dfs-copy-toggle-invar-necc))))))

  (defthm dfs-copy-toggle-invar-implies-eval-lit-copy
    (implies (and (dfs-copy-toggle-invar aignet mark copy toggles invals regvals aignet2)
                  ;; (aignet-idp id aignet)
                  (equal 1 (get-bit (lit->var lit) mark)))
             (equal (lit-eval (lit-copy lit copy) invals regvals aignet2)
                    (lit-eval-toggle lit toggles
                                     invals regvals
                                     ;; (input-copy-values 0 invals regvals aignet copy aignet2)
                                     ;; (reg-copy-values 0 invals regvals aignet copy aignet2)
                                     aignet)))
    :hints (("goal" :use ((:instance dfs-copy-toggle-invar-necc
                           (id (lit->var lit))))
             :in-theory (e/d (lit-eval lit-eval-toggle lit-copy) (dfs-copy-toggle-invar-necc)))))

  (defthm aignet-copy-dfs-rec-preserves-ids-marked
    (implies (ids-marked x mark)
             (b* (((mv mark ?copy ?strash ?aignet2)
                   (aignet-copy-dfs-rec
                    id aignet mark copy
                    strash gatesimp aignet2)))
               (ids-marked x mark)))
    :hints (("goal" :in-theory (enable ids-marked))))


  (local (in-theory (enable (:i aignet-copy-dfs-rec))))
  

  (defthm dfs-copy-toggle-invar-holds-of-aignet-copy-dfs-rec
    (implies (and ;; (aignet-idp id aignet)
              (dfs-copy-toggle-invar aignet mark copy toggles invals regvals aignet2)
              (ids-marked toggles mark)
              (aignet-input-copies-in-bounds copy aignet aignet2)
              (aignet-marked-copies-in-bounds copy mark aignet2))
             (b* (((mv mark copy ?strash aignet2)
                   (aignet-copy-dfs-rec
                    id aignet mark copy
                    strash gatesimp aignet2)))
               (dfs-copy-toggle-invar aignet mark copy toggles invals regvals aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-rec
              id aignet mark copy
              strash gatesimp aignet2))
            (and stable-under-simplificationp
                 (let ((last (car (last clause))))
                   `(:computed-hint-replacement
                     ((let ((witness (acl2::find-call-lst
                                      'dfs-copy-toggle-invar-witness
                                      clause)))
                        `(:clause-processor
                          (acl2::simple-generalize-cp
                           clause '((,witness . witness-id))))))
                     :expand (,last)
                     :do-not '(generalize fertilize eliminate-destructors)
                     :do-not-induct t)))
            ;; (and stable-under-simplificationp
            ;;      '(:expand ((:free (invals regvals)
            ;;                  (id-eval-toggle id toggles invals regvals aignet)))
            ;;        :in-theory (enable member-nat-list-fix-implies-marked-when-ids-marked
            ;;                           eval-xor-of-lits-toggle
            ;;                           eval-and-of-lits-toggle)))
            (and stable-under-simplificationp
                 (acl2::use-termhint
                  (acl2::termhint-seq
                   '(:expand ((:free (invals regvals) (id-eval-toggle id toggles invals regvals aignet)))
                     :in-theory (enable eval-xor-of-lits-toggle
                                        eval-and-of-lits-toggle
                                        member-nat-list-fix-implies-marked-when-ids-marked))
                   (b* ((suff (lookup-id id aignet)))
                     (case (stype (car suff))
                       (:and (b* ((f0 (fanin 0 suff))
                                  ((mv mark1 copy1 & aignet21)
                                   (aignet-copy-dfs-rec (lit->var f0) aignet mark copy strash gatesimp aignet2)))
                               (and (equal (lit-copy f0 copy1) 0)
                                    `(:use ((:instance dfs-copy-toggle-invar-implies-eval-lit-copy
                                             (lit ,(acl2::hq f0))
                                             (mark ,(acl2::hq mark1))
                                             (copy ,(acl2::hq copy1))
                                             (aignet2 ,(acl2::hq aignet21))))
                                      :in-theory (disable dfs-copy-toggle-invar-implies-eval-lit-copy)))))
                       (:pi `(:use ((:instance acl2::mark-clause-is-true (x :pi)))))
                       (:reg `(:use ((:instance acl2::mark-clause-is-true (x :reg)))))
                       (:xor `(:use ((:instance acl2::mark-clause-is-true (x :xor)))))
                       (:const `(:use ((:instance acl2::mark-clause-is-true (x :const))))))))))))

  (defthm aignet-copy-dfs-outs-iter-preserves-ids-marked
    (implies (ids-marked toggles mark)
             (b* (((mv mark ?copy ?strash ?aignet2)
                   (aignet-copy-dfs-outs-iter
                    n aignet mark copy
                    strash gatesimp aignet2)))
               (ids-marked toggles mark)))
    :hints(("Goal" :in-theory (enable aignet-copy-dfs-outs-iter))))
  
  (defthm aignet-copy-dfs-outs-iter-preserves-input-copies-in-bounds
    (implies (aignet-input-copies-in-bounds copy aignet aignet2)
             (b* (((mv ?mark ?copy ?strash ?aignet2)
                   (aignet-copy-dfs-outs-iter
                    n aignet mark copy
                    strash gatesimp aignet2)))
               (aignet-input-copies-in-bounds copy aignet aignet2)))
    :hints(("Goal" :in-theory (enable aignet-copy-dfs-outs-iter))))


  (defthm aignet-copy-dfs-outs-iter-preserves-marked-copies-in-bounds
    (implies (and (aignet-marked-copies-in-bounds copy mark aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2))
             (b* (((mv ?mark ?copy ?strash ?aignet2)
                   (aignet-copy-dfs-outs-iter
                    n aignet mark copy
                    strash gatesimp aignet2)))
               (aignet-marked-copies-in-bounds copy mark aignet2)))
    :hints(("Goal" :in-theory (enable aignet-copy-dfs-outs-iter))))

  

  (defthm aignet-copy-dfs-outs-iter-preserves-dfs-copy-toggle-invar
    (implies (and
              (dfs-copy-toggle-invar aignet mark copy toggles invals regvals aignet2)
              (ids-marked toggles mark)
              (aignet-input-copies-in-bounds copy aignet aignet2)
              (aignet-marked-copies-in-bounds copy mark aignet2))
             (b* (((mv mark copy ?strash aignet2)
                   (aignet-copy-dfs-outs-iter
                    n aignet mark copy
                    strash gatesimp aignet2)))
               (dfs-copy-toggle-invar aignet mark copy toggles invals regvals aignet2)))
    :hints(("Goal" :in-theory (enable aignet-copy-dfs-outs-iter))))

  (defthm aignet-copy-dfs-outs-preserves-dfs-copy-toggle-invar
    (implies (and
              (dfs-copy-toggle-invar aignet mark copy toggles invals regvals aignet2)
              (ids-marked toggles mark)
              (aignet-input-copies-in-bounds copy aignet aignet2)
              (aignet-marked-copies-in-bounds copy mark aignet2))
             (b* (((mv mark copy ?strash aignet2)
                   (aignet-copy-dfs-outs
                    aignet mark copy
                    strash gatesimp aignet2)))
               (dfs-copy-toggle-invar aignet mark copy toggles invals regvals aignet2)))
    :hints(("Goal" :in-theory (enable aignet-copy-dfs-outs))))

  (defthm aignet-copy-dfs-regs-iter-preserves-ids-marked
    (implies (ids-marked toggles mark)
             (b* (((mv mark ?copy ?strash ?aignet2)
                   (aignet-copy-dfs-regs-iter
                    n aignet mark copy
                    strash gatesimp aignet2)))
               (ids-marked toggles mark)))
    :hints(("Goal" :in-theory (enable aignet-copy-dfs-regs-iter))))

  (defthm aignet-copy-dfs-regs-iter-preserves-input-copies-in-bounds
    (implies (aignet-input-copies-in-bounds copy aignet aignet2)
             (b* (((mv ?mark ?copy ?strash ?aignet2)
                   (aignet-copy-dfs-regs-iter
                    n aignet mark copy
                    strash gatesimp aignet2)))
               (aignet-input-copies-in-bounds copy aignet aignet2)))
    :hints(("Goal" :in-theory (enable aignet-copy-dfs-regs-iter))))


  (defthm aignet-copy-dfs-regs-iter-preserves-marked-copies-in-bounds
    (implies (and (aignet-marked-copies-in-bounds copy mark aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2))
             (b* (((mv ?mark ?copy ?strash ?aignet2)
                   (aignet-copy-dfs-regs-iter
                    n aignet mark copy
                    strash gatesimp aignet2)))
               (aignet-marked-copies-in-bounds copy mark aignet2)))
    :hints(("Goal" :in-theory (enable aignet-copy-dfs-regs-iter))))

  (defthm aignet-copy-dfs-regs-iter-preserves-dfs-copy-toggle-invar
    (implies (and
              (dfs-copy-toggle-invar aignet mark copy toggles invals regvals aignet2)
              (ids-marked toggles mark)
              (aignet-input-copies-in-bounds copy aignet aignet2)
              (aignet-marked-copies-in-bounds copy mark aignet2))
             (b* (((mv mark copy ?strash aignet2)
                   (aignet-copy-dfs-regs-iter
                    n aignet mark copy
                    strash gatesimp aignet2)))
               (dfs-copy-toggle-invar aignet mark copy toggles invals regvals aignet2)))
    :hints(("Goal" :in-theory (enable aignet-copy-dfs-regs-iter))))

  (defthm aignet-copy-dfs-regs-preserves-dfs-copy-toggle-invar
    (implies (and
              (dfs-copy-toggle-invar aignet mark copy toggles invals regvals aignet2)
              (ids-marked toggles mark)
              (aignet-input-copies-in-bounds copy aignet aignet2)
              (aignet-marked-copies-in-bounds copy mark aignet2))
             (b* (((mv mark copy ?strash aignet2)
                   (aignet-copy-dfs-regs
                    aignet mark copy
                    strash gatesimp aignet2)))
               (dfs-copy-toggle-invar aignet mark copy toggles invals regvals aignet2)))
    :hints(("Goal" :in-theory (enable aignet-copy-dfs-regs))))

  (defthm aignet-copy-dfs-outs-and-regs-preserves-dfs-copy-toggle-invar
    (implies (and
              (dfs-copy-toggle-invar aignet mark copy toggles invals regvals aignet2)
              (ids-marked toggles mark)
              (aignet-input-copies-in-bounds copy aignet aignet2)
              (aignet-marked-copies-in-bounds copy mark aignet2))
             (b* (((mv mark copy ?strash aignet2)
                   (aignet-copy-dfs-outs
                    aignet mark copy
                    strash gatesimp aignet2))
                  ((mv mark copy ?strash aignet2)
                   (aignet-copy-dfs-regs
                    aignet mark copy
                    strash gatesimp aignet2)))
               (dfs-copy-toggle-invar aignet mark copy toggles invals regvals aignet2))))


  (std::defret-mutual <fn>-of-cons-po-node
    (defret <fn>-of-cons-po-node
      (equal (let ((aignet (cons (po-node outlit) aignet))) <call>)
             val)
      :hints ((and stable-under-simplificationp
                   '(:expand ((:free (aignet) <call>)))))
      :fn id-eval)
    (defret <fn>-of-cons-po-node
      (equal (let ((aignet (cons (po-node outlit) aignet))) <call>)
             val)
      :hints ((and stable-under-simplificationp
                   '(:expand ((:free (aignet) <call>)))))
      :fn lit-eval)
    (defret <fn>-of-cons-po-node
      (equal (let ((aignet (cons (po-node outlit) aignet))) <call>)
             val)
      :hints ((and stable-under-simplificationp
                   '(:expand ((:free (aignet) <call>)))))
      :fn eval-xor-of-lits)
    (defret <fn>-of-cons-po-node
      (equal (let ((aignet (cons (po-node outlit) aignet))) <call>)
             val)
      :hints ((and stable-under-simplificationp
                   '(:expand ((:free (aignet) <call>)))))
      :fn eval-and-of-lits)
    :mutual-recursion id-eval)

  (std::defret-mutual <fn>-of-cons-nxst-node
    (defret <fn>-of-cons-nxst-node
      (equal (let ((aignet (cons (nxst-node nxst reg) aignet))) <call>)
             val)
      :hints ((and stable-under-simplificationp
                   '(:expand ((:free (aignet) <call>)))))
      :fn id-eval)
    (defret <fn>-of-cons-nxst-node
      (equal (let ((aignet (cons (nxst-node nxst reg) aignet))) <call>)
             val)
      :hints ((and stable-under-simplificationp
                   '(:expand ((:free (aignet) <call>)))))
      :fn lit-eval)
    (defret <fn>-of-cons-nxst-node
      (equal (let ((aignet (cons (nxst-node nxst reg) aignet))) <call>)
             val)
      :hints ((and stable-under-simplificationp
                   '(:expand ((:free (aignet) <call>)))))
      :fn eval-xor-of-lits)
    (defret <fn>-of-cons-nxst-node
      (equal (let ((aignet (cons (nxst-node nxst reg) aignet))) <call>)
             val)
      :hints ((and stable-under-simplificationp
                   '(:expand ((:free (aignet) <call>)))))
      :fn eval-and-of-lits)
    :mutual-recursion id-eval)

  (defthm dfs-copy-toggle-invar-preserved-by-cons-po-node
    (implies (dfs-copy-toggle-invar aignet mark copy toggles invals regvals aignet2)
             (dfs-copy-toggle-invar aignet mark copy toggles invals regvals
                                    (cons (po-node lit)
                                          (node-list-fix aignet2))))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm dfs-copy-toggle-invar-preserved-by-cons-nxst-node
    (implies (dfs-copy-toggle-invar aignet mark copy toggles invals regvals aignet2)
             (dfs-copy-toggle-invar aignet mark copy toggles invals regvals
                                    (cons (nxst-node lit reg)
                                          (node-list-fix aignet2))))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm aignet-copy-outs-iter-preserves-dfs-toggle-invar
    (implies (dfs-copy-toggle-invar aignet mark copy toggles invals regvals aignet2)
             (b* ((aignet2 (aignet-copy-outs-iter n aignet copy aignet2)))
               (dfs-copy-toggle-invar aignet mark copy toggles invals regvals aignet2)))
    :hints(("Goal" :in-theory (enable aignet-copy-outs-iter)
            :induct (aignet-copy-outs-iter n aignet copy aignet2))))

  (defthm aignet-copy-outs-preserves-dfs-toggle-invar
    (implies (dfs-copy-toggle-invar aignet mark copy toggles invals regvals aignet2)
             (b* ((aignet2 (aignet-copy-outs aignet copy aignet2)))
               (dfs-copy-toggle-invar aignet mark copy toggles invals regvals aignet2)))
    :hints(("Goal" :in-theory (enable aignet-copy-outs))))

  (defthm aignet-copy-nxsts-iter-preserves-dfs-toggle-invar
    (implies (dfs-copy-toggle-invar aignet mark copy toggles invals regvals aignet2)
             (b* ((aignet2 (aignet-copy-nxsts-iter n aignet copy aignet2)))
               (dfs-copy-toggle-invar aignet mark copy toggles invals regvals aignet2)))
    :hints(("Goal" :in-theory (enable aignet-copy-nxsts-iter))))

  (defthm aignet-copy-nxsts-preserves-dfs-toggle-invar
    (implies (dfs-copy-toggle-invar aignet mark copy toggles invals regvals aignet2)
             (b* ((aignet2 (aignet-copy-nxsts aignet copy aignet2)))
               (dfs-copy-toggle-invar aignet mark copy toggles invals regvals aignet2)))
    :hints(("Goal" :in-theory (enable aignet-copy-nxsts))))
  )
                             

;; (define aignet-remove-unreachable-setup (aignet refcounts obs-sdom-array copy mark aignet2)
;;   :returns (mv new-mark new-copy new-aignet2)
;;   :guard (and (eql (num-fanins aignet) (sdominfo-length obs-sdom-array))
;;               (<= (sdominfo-length obs-sdom-array) (u32-length refcounts)))
  

(define aignet-remove-unreachable (aignet refcounts obs-sdom-array aignet2)
  :guard (and (eql (num-fanins aignet) (sdominfo-length obs-sdom-array))
              (<= (sdominfo-length obs-sdom-array) (u32-length refcounts)))
  :returns (new-aignet2)
  :hooks nil
  (b* (((acl2::local-stobjs copy mark strash)
        (mv mark copy strash aignet2))
       ((mv copy aignet2) (init-copy-comb aignet copy aignet2))
       (mark (resize-bits (num-fanins aignet) mark))
       (mark (mark-unreachable-nodes 0 refcounts obs-sdom-array mark))
       (copy (init-unreachable-node-copies 0 refcounts obs-sdom-array copy))
       ((acl2::hintcontext-bind ((marki mark)
                                 (copyi copy)
                                 (aignet2i aignet2)
                                 (strashi strash))))
       ((mv mark copy strash aignet2)
        (aignet-copy-dfs-outs aignet mark copy strash (make-gatesimp) aignet2))
       ((mv mark copy strash aignet2)
        (aignet-copy-dfs-regs aignet mark copy strash (make-gatesimp) aignet2))
       ((acl2::hintcontext-bind ((markd mark)
                                 (copyd copy)
                                 (aignet2d aignet2)
                                 (strashd strash))))
       (aignet2 (aignet-copy-outs aignet copy aignet2))
       ((acl2::hintcontext-bind ((aignet2n aignet2))))
       (aignet2 (aignet-copy-nxsts aignet copy aignet2))
       ((acl2::hintcontext-bind ((markf mark)
                                 (copyf copy)
                                 (aignet2f aignet2)
                                 (strashf strash))))
       ((acl2::hintcontext :final)))
    (mv mark copy strash aignet2))
  ///
  (local (defthm ids-marked-of-unreachable-node-toggles
           (implies (equal n (+ 1 (fanin-count aignet)))
                    (ids-marked (unreachable-node-toggles n
                                                          refcounts obs-sdom-array invals regvals aignet)
                                (mark-unreachable-nodes 0 refcounts obs-sdom-array mark)))
           :hints ((acl2::use-termhint
                    (b* ((n (+ 1 (fanin-count aignet)))
                         (toggles (unreachable-node-toggles
                                   n refcounts obs-sdom-array invals regvals aignet))
                         (new-mark (mark-unreachable-nodes 0 refcounts obs-sdom-array mark))
                         (badguy (ids-marked-badguy toggles new-mark)))
                      `(:use ((:instance member-of-unreachable-node-toggles-when-reached
                               (n ,(acl2::hq n))
                               (i ,(acl2::hq badguy)))
                              (:instance member-of-unreachable-node-toggles-when-not-refcounts
                               (n ,(acl2::hq n))
                               (i ,(acl2::hq badguy)))
                              (:instance ids-not-marked-implies-badguy
                               (x ,(acl2::hq toggles))
                               (mark ,(acl2::hq new-mark))))
                        :in-theory (disable member-of-unreachable-node-toggles-when-reached
                                            member-of-unreachable-node-toggles-when-not-refcounts
                                            ids-not-marked-implies-badguy)))))))

  (local (defthm lit-eval-of-init-copy-comb
           (b* (((mv copy aignet2) (init-copy-comb aignet copy aignet2)))
             (implies (equal (ctype (stype (car (lookup-id id aignet)))) :input)
                      (equal (lit-eval (nth-lit id copy) invals regvals aignet2)
                             (id-eval id invals regvals aignet))))
           :hints(("Goal" :in-theory (enable init-copy-comb lit-eval)
                   :expand ((id-eval id invals regvals aignet))))))


  (local (defthm dfs-copy-toggle-invar-of-init-unreachable
           (implies (equal (len obs-sdom-array) (+ 1 (fanin-count aignet)))
                    (b* ((mark (acl2::repeat (len obs-sdom-array) 0))
                         (mark (mark-unreachable-nodes 0 refcounts obs-sdom-array mark))
                         ((mv copy aignet2) (init-copy-comb aignet copy aignet2))
                         (copy (init-unreachable-node-copies 0 refcounts obs-sdom-array copy))
                         (toggles (unreachable-node-toggles (len obs-sdom-array)
                                                            refcounts obs-sdom-array invals regvals aignet)))
                      (dfs-copy-toggle-invar aignet mark copy toggles invals regvals aignet2)))
           :hints(("Goal" :in-theory (enable dfs-copy-toggle-invar aignet-idp)
                   :do-not-induct t)
                  (and stable-under-simplificationp
                       '(:expand ((:free (mark copy toggles aignet2)
                                   (id-eval (dfs-copy-toggle-invar-witness
                                             aignet mark copy toggles invals regvals aignet2)
                                            invals regvals aignet))
                                  (:free (mark copy toggles aignet2)
                                   (id-eval-toggle
                                    (dfs-copy-toggle-invar-witness
                                     aignet mark copy toggles invals regvals aignet2)
                                    toggles invals regvals aignet))))))
           :otf-flg t))
  (set-ignore-ok t)

  (defret po-eval-of-<fn>
    (implies (and (obs-sdom-array-correct obs-sdom-array refcounts aignet)
                  (equal (len obs-sdom-array) (+ 1 (fanin-count aignet)))
                  (equal (nth (lit->var (fanin 0 (lookup-stype n :po aignet))) obs-sdom-array)
                         nil)
                  (< (nfix n) (stype-count :po aignet)))
             (equal (output-eval n invals regvals new-aignet2)
                    (output-eval n invals regvals aignet)))
    :hints(;; ("Goal" :in-theory (e/d (output-eval)
           ;;                         (AIGNET-EXTENSION-P-OF-AIGNET-COPY-NXSTS)))
           (acl2::function-termhint
            <fn>
            (:final
             (b* ((toggles (unreachable-node-toggles (+ 1 (fanin-count aignet))
                                                     refcounts obs-sdom-array invals regvals aignet)))
               `(:use ((:instance aignet-copy-dfs-outs-preserves-dfs-copy-toggle-invar
                        (aignet aignet)
                        (mark ,(acl2::hq marki))
                        (copy ,(acl2::hq copyi))
                        (toggles ,(acl2::hq toggles))
                        (aignet2 ,(acl2::hq aignet2i))
                        (strash ,(acl2::hq strashi))
                        (gatesimp ,(make-gatesimp)))
                       (:instance aignet-copy-dfs-outs-and-regs-preserves-dfs-copy-toggle-invar
                        (aignet aignet)
                        (mark ,(acl2::hq marki))
                        (copy ,(acl2::hq copyi))
                        (toggles ,(acl2::hq toggles))
                        (aignet2 ,(acl2::hq aignet2i))
                        (strash ,(acl2::hq strashi))
                        (gatesimp ,(make-gatesimp))))
                 :in-theory (e/d (output-eval)
                                 (aignet-copy-dfs-outs-preserves-dfs-copy-toggle-invar
                                  aignet-copy-dfs-outs-and-regs-preserves-dfs-copy-toggle-invar
                                  aignet-copy-dfs-outs-iter-preserves-dfs-copy-toggle-invar
                                  aignet-copy-dfs-regs-preserves-dfs-copy-toggle-invar
                                  aignet-copy-dfs-regs-iter-preserves-dfs-copy-toggle-invar
                                  lit-eval-preserved-by-extension))))))))


  (defret nxst-eval-of-<fn>
    (implies (and (obs-sdom-array-correct obs-sdom-array refcounts aignet)
                  (equal (len obs-sdom-array) (+ 1 (fanin-count aignet)))
                  (equal (nth (lit->var (lookup-reg->nxst n aignet)) obs-sdom-array)
                         nil)
                  (< (nfix n) (stype-count :reg aignet)))
             (equal (nxst-eval n invals regvals new-aignet2)
                    (nxst-eval n invals regvals aignet)))
    :hints(;; ("Goal" :in-theory (e/d (output-eval)
           ;;                         (AIGNET-EXTENSION-P-OF-AIGNET-COPY-NXSTS)))
           (acl2::function-termhint
            <fn>
            (:final
             (b* ((toggles (unreachable-node-toggles (+ 1 (fanin-count aignet))
                                                     refcounts obs-sdom-array invals regvals aignet)))
               `(:use ((:instance aignet-copy-dfs-outs-preserves-dfs-copy-toggle-invar
                        (aignet aignet)
                        (mark ,(acl2::hq marki))
                        (copy ,(acl2::hq copyi))
                        (toggles ,(acl2::hq toggles))
                        (aignet2 ,(acl2::hq aignet2i))
                        (strash ,(acl2::hq strashi))
                        (gatesimp ,(make-gatesimp)))
                       (:instance aignet-copy-dfs-outs-and-regs-preserves-dfs-copy-toggle-invar
                        (aignet aignet)
                        (mark ,(acl2::hq marki))
                        (copy ,(acl2::hq copyi))
                        (toggles ,(acl2::hq toggles))
                        (aignet2 ,(acl2::hq aignet2i))
                        (strash ,(acl2::hq strashi))
                        (gatesimp ,(make-gatesimp))))
                 :in-theory (e/d (nxst-eval)
                                 (aignet-copy-dfs-outs-preserves-dfs-copy-toggle-invar
                                  aignet-copy-dfs-outs-and-regs-preserves-dfs-copy-toggle-invar
                                  aignet-copy-dfs-outs-iter-preserves-dfs-copy-toggle-invar
                                  aignet-copy-dfs-regs-preserves-dfs-copy-toggle-invar
                                  aignet-copy-dfs-regs-iter-preserves-dfs-copy-toggle-invar
                                  lit-eval-preserved-by-extension))))))))

  (defret stype-counts-of-<fn>
    (and (equal (stype-count :pi new-aignet2) (stype-count :pi aignet))
         (equal (stype-count :reg new-aignet2) (stype-count :reg aignet))
         (equal (stype-count :po new-aignet2) (stype-count :po aignet))))

  (defret normalize-aignet2-of-<fn>
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal new-aignet2
                    (let ((aignet2 nil)) <call>)))))


(fty::defprod unreachability-config
  ()
  :tag :unreachability-config)

(define unreachability (aignet aignet2 (config unreachability-config-p))
  (declare (ignorable config))
  :returns (new-aignet2)
  :hooks nil
  (b* (((local-stobjs aignet-levels refcounts obs-sdom-array)
        (mv aignet-levels refcounts obs-sdom-array aignet2))
       (aignet-levels (resize-u32 (num-fanins aignet) aignet-levels))
       (refcounts (resize-u32 (num-fanins aignet) refcounts))
       (obs-sdom-array (resize-sdominfo (num-fanins aignet) obs-sdom-array))
       (aignet-levels (aignet-record-levels aignet aignet-levels))
       (refcounts (aignet-count-refs refcounts aignet))
       (obs-sdom-array (aignet-compute-obs-sdom-info obs-sdom-array refcounts aignet-levels aignet))
       (aignet2 (aignet-remove-unreachable aignet refcounts obs-sdom-array aignet2)))
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

(define unreachability! (aignet (config unreachability-config-p))
  :enabled t
  :hooks nil
  (mbe :logic (non-exec (unreachability aignet (acl2::create-aignet) config))
       :exec
       (b* (((acl2::local-stobjs aignet2)
             (mv aignet aignet2))
            (aignet2 (unreachability aignet aignet2 config)))
         (swap-stobjs aignet aignet2))))


(fty::defprod n-outputs-unreachability-config
  ()
  :tag :n-outputs-unreachability-config)

(define n-outputs-unreachability ((n natp) aignet aignet2 (config n-outputs-unreachability-config-p))
  (declare (ignorable config))
  :returns (new-aignet2)
  :hooks nil
  :guard (<= n (num-outs aignet))
  (b* (((local-stobjs aignet-levels refcounts obs-sdom-array)
        (mv aignet-levels refcounts obs-sdom-array aignet2))
       (aignet-levels (resize-u32 (num-fanins aignet) aignet-levels))
       (refcounts (resize-u32 (num-fanins aignet) refcounts))
       (obs-sdom-array (resize-sdominfo (num-fanins aignet) obs-sdom-array))
       (aignet-levels (aignet-record-levels aignet aignet-levels))
       (refcounts (aignet-count-refs refcounts aignet))
       (obs-sdom-array (aignet-compute-obs-sdom-info-n-outputs n obs-sdom-array refcounts aignet-levels aignet))
       (aignet2 (aignet-remove-unreachable aignet refcounts obs-sdom-array aignet2)))
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
