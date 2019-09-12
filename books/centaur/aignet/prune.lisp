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
(include-book "copying")
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "centaur/aignet/bit-lemmas" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "std/lists/take" :dir :system))
;(local (include-book "data-structures/list-defthms" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))
(local (in-theory (disable nth update-nth
                           acl2::nfix-when-not-natp
                           resize-list
                           ;; acl2::resize-list-when-empty
                           ;; acl2::make-list-ac-redef
                           ;; set::double-containment
                           ;; set::sets-are-true-lists
                           make-list-ac)))
(local (acl2::use-trivial-ancestors-check))
(local (in-theory (disable id-eval
                           true-listp
                           acl2::nfix-when-not-natp
                           ;; acl2::nth-with-large-index
                           acl2::natp-when-integerp)))



;(defsection aignet-copy-dfs






(defsection aignet-ins-copied

  (in-theory (disable aignet-copy-ins))

  (local (in-theory (enable aignet-copy-ins)))

  (defun-sk aignet-ins-copied (aignet copy aignet2)
    (forall (id invals regvals)
            (implies (and (aignet-idp id aignet)
                          (equal (id->type id aignet) (in-type))
                          (equal (id->regp id aignet) 0))
                     (equal (lit-eval (nth-lit id copy)
                                      invals regvals aignet2)
                            (id-eval id invals regvals aignet))))
    :rewrite :direct)

  (in-theory (disable aignet-ins-copied))

  (defthm aignet-ins-copied-of-aignet-copy-ins
    (implies (equal 0 (num-ins aignet2))
             (b* (((mv copy aignet2)
                   (aignet-copy-ins aignet copy aignet2)))
               (aignet-ins-copied aignet copy aignet2)))
    :hints (("goal" :in-theory (e/d (aignet-ins-copied lit-eval id-eval)))))

  (defthm aignet-copy-regs-preserves-aignet-ins-copied
    (implies (and (aignet-ins-copied aignet copy aignet2)
                  (aignet-copies-in-bounds copy aignet2))
             (b* (((mv copy aignet2)
                   (aignet-copy-regs aignet copy aignet2)))
               (aignet-ins-copied aignet copy aignet2)))
    :hints(("Goal" :in-theory (enable aignet-copy-regs))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause))))))))

(defsection aignet-regs-copied

  (in-theory (disable aignet-copy-regs))

  (local (in-theory (enable aignet-copy-regs)))

  (defun-sk aignet-regs-copied (aignet copy aignet2)
    (forall (id invals regvals)
            (implies (and (aignet-idp id aignet)
                          (equal (id->type id aignet) (in-type))
                          (equal (id->regp id aignet) 1))
                     (equal (lit-eval (nth-lit id copy)
                                      invals regvals aignet2)
                            (id-eval id invals regvals aignet))))
    :rewrite :direct)

  (in-theory (disable aignet-regs-copied))

  (defthm aignet-regs-copied-of-aignet-copy-regs
    (implies (equal 0 (num-regs aignet2))
             (b* (((mv copy aignet2)
                   (aignet-copy-regs aignet copy aignet2)))
               (aignet-regs-copied aignet copy aignet2)))
    :hints (("goal" :in-theory (e/d (aignet-regs-copied lit-eval id-eval)))))

  (defthm aignet-copy-ins-preserves-aignet-regs-copied
    (implies (and (aignet-regs-copied aignet copy aignet2)
                  (aignet-copies-in-bounds copy aignet2))
             (b* (((mv copy aignet2)
                   (aignet-copy-ins aignet copy aignet2)))
               (aignet-regs-copied aignet copy aignet2)))
    :hints(("Goal" :in-theory (enable aignet-copy-ins))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause))))))))

(defsection aignet-cis-copied
  (defun-sk aignet-cis-copied (aignet copy aignet2)
    (forall (id invals regvals)
            (implies (and (aignet-idp id aignet)
                          (equal (id->type id aignet) (in-type)))
                     (equal (lit-eval (nth-lit id copy)
                                      invals regvals aignet2)
                            (id-eval id invals regvals aignet))))
    :rewrite :direct)

  (defthm aignet-cis-copied-when-aignet-ins/regs-copied
    (implies (and (aignet-ins-copied aignet copy aignet2)
                  (aignet-regs-copied aignet copy aignet2))
             (aignet-cis-copied aignet copy aignet2))
    :hints (("goal" :cases ((equal 1 (id->regp
                                      (MV-NTH 0 (AIGNET-CIS-COPIED-WITNESS
                                                 AIGNET COPY AIGNET2))
                                      aignet))))))

  (in-theory (disable aignet-cis-copied))

  (defthm aignet-cis-copied-of-aignet-copy-ins/regs
    (implies (and (equal 0 (num-ins aignet2))
                  (equal 0 (num-regs aignet2))
                  (aignet-copies-in-bounds copy aignet2))
             (b* (((mv copy aignet2)
                   (aignet-copy-ins aignet copy aignet2))
                  ((mv copy aignet2)
                   (aignet-copy-regs aignet copy aignet2)))
               (aignet-cis-copied aignet copy aignet2)))))


(defsection aignet-copy-dfs-simple-invar
  (local (in-theory (disable lookup-id-in-bounds-when-positive
                             default-car
                             aignet-copy-dfs-rec-preserves-copy-when-marked
                             lookup-id-out-of-bounds
                             acl2::nth-when-zp
                             satlink::equal-of-lit-negate-component-rewrites
                             satlink::equal-of-lit-negate-cond-component-rewrites
                             aignet-copy-dfs-rec-preserves-ci-copies)))
  (defun-sk aignet-copy-dfs-simple-invar (aignet mark copy aignet2)
    (forall (id invals regvals)
            (implies (and (aignet-idp id aignet)
                          (equal 1 (get-bit id mark)))
                     (equal (lit-eval (nth-lit id copy)
                                      invals regvals aignet2)
                            (id-eval id invals regvals aignet))))
    :rewrite :direct)

  (in-theory (disable aignet-copy-dfs-simple-invar))

  (local (in-theory (enable (:induction aignet-copy-dfs-rec))))

  (local (in-theory (disable acl2::b-xor lit-negate-cond)))

  (defthm aignet-copy-dfs-rec-preserves-aignet-cis-copied
    (implies (and (aignet-cis-copied aignet copy aignet2)
                  (aignet-copies-in-bounds copy aignet2))
             (b* (((mv & copy & aignet2)
                   (aignet-copy-dfs-rec
                    id aignet mark copy strash gatesimp aignet2)))
               (aignet-cis-copied aignet copy aignet2)))
    :hints (("goal" :in-theory (enable aignet-copy-dfs-rec-preserves-ci-copies))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (local
   (defthm aignet-copy-dfs-simple-invar-necc-rewrite
     (b* (((mv mark copy & aignet2)
           (aignet-copy-dfs-rec
            id aignet mark copy
            strash gatesimp aignet2)))
       (implies (and (aignet-copy-dfs-simple-invar
                      aignet mark copy aignet2)
                     (aignet-cis-copied aignet copy aignet2)
                     (aignet-idp id aignet))
                (equal (lit-eval
                        (nth-lit id copy)
                        invals regvals aignet2)
                       (id-eval id invals regvals aignet))))
     :hints (("goal" :do-not-induct t))))

  (defthm aignet-copy-dfs-simple-invar-necc-of-lit-copy
    (implies (and (aignet-copy-dfs-simple-invar
                   aignet mark copy aignet2)
                  (equal 1 (get-bit (lit->var lit) mark))
                  (aignet-idp (lit->var lit) aignet))
             (equal (lit-eval (lit-copy lit copy)
                              invals regvals aignet2)
                    (lit-eval lit invals regvals aignet)))
    :hints (("Goal" 
             :in-theory (enable lit-copy lit-eval)
             :do-not-induct t)))

  ;; (local (defthm equal-mk-lit-rw
  ;;          (equal (equal (mk-lit id neg) val)
  ;;                 (and (litp val)
  ;;                      (equal (nfix id) (lit-id val))
  ;;                      (equal (bfix neg) (lit-neg val))))
  ;;          ;; :hints(("Goal" :in-theory (disable satlink::make-lit-identity)
  ;;          ;;         :use ((:instance mk-lit-identity (lit val)))))
  ;;          ))
  (local (in-theory (enable satlink::equal-of-make-lit)))

  (local (include-book "std/util/termhints" :dir :system))

  (defthm aignet-copy-dfs-simple-invar-holds-of-aignet-copy-dfs-rec
    (implies (and (aignet-idp id aignet)
                  (aignet-copy-dfs-simple-invar aignet mark copy aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (aignet-cis-copied aignet copy aignet2))
             (b* (((mv mark copy ?strash aignet2)
                   (aignet-copy-dfs-rec
                    id aignet mark copy
                    strash gatesimp aignet2)))
               (aignet-copy-dfs-simple-invar aignet mark copy aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-rec
              id aignet mark copy
              strash gatesimp aignet2))
            (and stable-under-simplificationp
                 (let ((last (car (last clause))))
                   `(:expand (,last)
                     :do-not '(generalize fertilize eliminate-destructors)
                     :do-not-induct t)))
            (and stable-under-simplificationp
                 (let ((witness (acl2::find-call-lst
                                 'aignet-copy-dfs-simple-invar-witness
                                 clause)))
                  `(:clause-processor
                    (acl2::simple-generalize-cp
                     clause '(((mv-nth '0 ,witness) . id2)
                              ((mv-nth '1 ,witness) . invals)
                              ((mv-nth '2 ,witness) . regvals))))))
            (and stable-under-simplificationp
                 '(:in-theory (enable eval-and-of-lits eval-xor-of-lits
                                      lit-negate-cond)
                   :expand ((:free (invals regvals)
                             (id-eval id invals regvals aignet)))))
            (and stable-under-simplificationp
                 ((lambda (hint1 hint2)
                    `(:computed-hint-replacement
                      (,hint2)
                      . ,hint1))
                  '(:in-theory (enable lit-eval))
                  '(acl2::use-termhint
                    (b* ((suff (lookup-id id aignet)))
                      (and (equal (stype (car suff)) :and)
                           (b* ((fanin (fanin :gate0 suff))
                                ((mv mark1 copy1 & aignet21)
                                 (aignet-copy-dfs-rec (lit->var fanin) aignet mark copy strash gatesimp aignet2)))
                   `(:use ((:instance aignet-copy-dfs-simple-invar-necc-of-lit-copy
                            (lit  ,(acl2::hq fanin))
                            (mark ,(acl2::hq mark1))
                            (copy ,(acl2::hq copy1))
                            (aignet2 ,(acl2::hq aignet21))))
                     :in-theory (e/d (lit-negate-cond lit-eval)
                                     (aignet-copy-dfs-simple-invar-necc
                                      aignet-copy-dfs-simple-invar-necc-rewrite
                                      aignet-copy-dfs-simple-invar-necc-of-lit-copy))))))))))
    :otf-flg t)

  (defthm lit-eval-in-aignet-copy-dfs-rec
    (implies (and (aignet-idp id aignet)
                  (aignet-copies-in-bounds copy aignet2)
                  (aignet-copy-dfs-simple-invar aignet mark copy aignet2)
                  (aignet-cis-copied aignet copy aignet2)
                  (equal (nth-lit 0 copy) 0))
             (b* (((mv mark copy ?strash aignet2)
                   (aignet-copy-dfs-rec
                    id aignet mark copy strash gatesimp aignet2)))
               (implies (and (aignet-idp id2 aignet)
                             (equal 1 (nth id2 mark)))
                        (equal (lit-eval (nth-lit id2 copy)
                                         invals regvals aignet2)
                               (id-eval id2 invals regvals aignet)))))
    :hints (("goal" :use aignet-copy-dfs-simple-invar-holds-of-aignet-copy-dfs-rec
             :in-theory (disable aignet-copy-dfs-simple-invar-holds-of-aignet-copy-dfs-rec)))))

(defsection aignet-copy-dfs-outs
  (defthm aignet-copy-dfs-rec-is-list-of-mv-nths
    (let ((x (aignet-copy-dfs-rec
              id aignet mark copy strash gatesimp aignet2)))
      (equal (list (mv-nth 0 x) (mv-nth 1 x) (mv-nth 2 x) (mv-nth 3 x))
             x))
    :hints('(:in-theory (enable (:induction aignet-copy-dfs-rec)))
           (and stable-under-simplificationp
                (acl2::just-induct-and-expand
                 (aignet-copy-dfs-rec
                  id aignet mark copy strash gatesimp aignet2)))))

  (defiteration aignet-copy-dfs-outs
    (aignet mark copy strash gatesimp aignet2)
    (declare (xargs :stobjs (aignet mark copy strash aignet2)
                    :guard (and (gatesimp-p gatesimp)
                                (<= (num-fanins aignet) (bits-length mark))
                                (<= (num-fanins aignet) (lits-length copy))
                                (aignet-copies-in-bounds copy aignet2))))
    (b* ((out-fanin (outnum->fanin n aignet)))
      (aignet-copy-dfs-rec
      (lit->var out-fanin) aignet mark copy strash gatesimp aignet2))
    :returns (mv mark copy strash aignet2)
    :index n
    :last (num-outs aignet))

  (def-aignet-preservation-thms aignet-copy-dfs-outs-iter
    :stobjname aignet2)

  (defthm memo-tablep-of-aignet-copy-dfs-outs-iter-copy
    (<= (len copy)
        (len (mv-nth 1 (aignet-copy-dfs-outs-iter
                        n aignet mark copy strash gatesimp aignet2))))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-dfs-outs-iter
             n aignet mark copy strash gatesimp
             aignet2)))
    :rule-classes :linear)

  (defthm memo-tablep-of-aignet-copy-dfs-outs-iter-mark
    (<= (len mark)
        (len (mv-nth 0 (aignet-copy-dfs-outs-iter
                        n aignet mark copy strash gatesimp aignet2))))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-dfs-outs-iter
             n aignet mark copy strash gatesimp
             aignet2)))
    :rule-classes :linear)

  (defthm aignet-copy-dfs-outs-iter-preserves-marked
    (implies (equal 1 (nth id mark))
             (equal (nth id (mv-nth 0 (aignet-copy-dfs-outs-iter
                                       n aignet mark copy strash gatesimp
                                       aignet2)))
                    1))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-dfs-outs-iter
             n aignet mark copy strash gatesimp
             aignet2))))

  (defthm aignet-copy-dfs-outs-iter-preserves-marked-lits
    (implies (equal 1 (nth id mark))
             (equal (nth-lit id (mv-nth 1 (aignet-copy-dfs-outs-iter
                                           n aignet mark copy strash gatesimp
                                           aignet2)))
                    (nth-lit id copy)))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-dfs-outs-iter
             n aignet mark copy strash gatesimp
             aignet2))))

  (defthm aignet-copy-dfs-outs-iter-preserves-marked-lit-copies
    (implies (equal 1 (nth (lit->var lit) mark))
             (equal (lit-copy lit (mv-nth 1 (aignet-copy-dfs-outs-iter
                                             n aignet mark copy strash gatesimp
                                             aignet2)))
                    (lit-copy lit copy)))
    :hints(("Goal" :in-theory (enable lit-copy))))

  (defthm aignet-copy-dfs-outs-iter-preserves-ci-copy
    (implies (equal (id->type id aignet) (in-type))
             (equal (nth-lit id (mv-nth 1 (aignet-copy-dfs-outs-iter
                                           n aignet mark copy strash gatesimp
                                           aignet2)))
                    (nth-lit id copy)))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-dfs-outs-iter
             n aignet mark copy strash gatesimp
             aignet2))))

  (defthm aignet-copies-ok-of-aignet-copy-dfs-outs-iter
    (implies (and (<= (nfix n) (num-outs aignet))
                  (aignet-copies-in-bounds copy aignet2))
             (b* (((mv & copy & aignet2)
                   (aignet-copy-dfs-outs-iter
                    n aignet mark copy strash gatesimp aignet2)))
               (aignet-copies-in-bounds
                                 copy aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-outs-iter
              n aignet mark copy strash gatesimp aignet2))))

  (defthm aignet-copy-dfs-outs-iter-preserves-aignet-cis-copied
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (aignet-cis-copied aignet copy aignet2)
                  (<= (nfix n) (num-outs aignet)))
             (b* (((mv & copy & aignet2)
                   (aignet-copy-dfs-outs-iter
                    n aignet mark copy strash gatesimp aignet2)))
               (aignet-cis-copied aignet copy aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-outs-iter
              n aignet mark copy strash gatesimp aignet2))))

  (local (defthm decr-less-when-lte
           (implies (<= n m)
                    (and (< (+ -1 n) m)
                         (<= (+ -1 n) m)))))

  (defthm aignet-copy-dfs-outs-iter-preserves-aignet-copy-dfs-simple-invar
    (implies (and (aignet-copy-dfs-simple-invar aignet mark copy aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (aignet-cis-copied aignet copy aignet2)
                  (<= (nfix n) (num-outs aignet)))
             (b* (((mv mark copy ?strash aignet2)
                   (aignet-copy-dfs-outs-iter
                    n aignet mark copy strash gatesimp aignet2)))
               (aignet-copy-dfs-simple-invar aignet mark copy aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-outs-iter
              n aignet mark copy strash gatesimp aignet2))))

  (defthm fanin-marked-of-aignet-copy-dfs-outs-iter
    (implies (< (nfix m) (nfix n))
             (equal (nth (lit->var (fanin :co (lookup-stype m (po-stype) aignet)))
                         (mv-nth 0 (aignet-copy-dfs-outs-iter
                                    n aignet mark copy strash gatesimp aignet2)))
                    1))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-outs-iter
              n aignet mark copy strash gatesimp aignet2))))

  (defthm stype-counts-preserved-of-aignet-copy-dfs-outs-iter
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype (mv-nth 3 (aignet-copy-dfs-outs-iter
                                                  n aignet mark copy
                                                  strash gatesimp aignet2)))
                    (stype-count stype aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-outs-iter
              n aignet mark copy
              strash gatesimp aignet2))))

  (defthm stype-counts-preserved-of-aignet-copy-dfs-outs
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype (mv-nth 3 (aignet-copy-dfs-outs
                                                  aignet mark copy
                                                  strash gatesimp aignet2)))
                    (stype-count stype aignet2))))

  (defthm lit-eval-po-copy-of-aignet-copy-dfs-outs-iter
    (implies (and (aignet-copy-dfs-simple-invar aignet mark copy aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (aignet-cis-copied aignet copy aignet2)
                  (<= (nfix n) (num-outs aignet)))
             (b* (((mv ?mark copy ?strash aignet2)
                   (aignet-copy-dfs-outs-iter
                    n aignet mark copy strash gatesimp aignet2)))
               (implies (< (nfix m) (nfix n))
                        (equal (lit-eval (lit-copy (fanin :co (lookup-stype m :po aignet)) copy)
                                         invals regvals aignet2)
                               (output-eval m invals regvals aignet)))))
    :hints(("Goal" :in-theory (e/d (output-eval)
                                   (aignet-copy-dfs-outs-iter-preserves-aignet-copy-dfs-simple-invar))
            :do-not-induct t
            :use aignet-copy-dfs-outs-iter-preserves-aignet-copy-dfs-simple-invar)))

)


(defsection aignet-copy-dfs-regs
  (defiteration aignet-copy-dfs-regs
    (aignet mark copy strash gatesimp aignet2)
    (declare (xargs :stobjs (aignet mark copy strash aignet2)
                    :guard (and (gatesimp-p gatesimp)
                                (<= (num-fanins aignet) (bits-length mark))
                                (<= (num-fanins aignet) (lits-length copy))
                                (aignet-copies-in-bounds copy aignet2))))
    (b* ((fanin (regnum->nxst n aignet)))
      (aignet-copy-dfs-rec
       (lit->var fanin) aignet mark copy strash gatesimp aignet2))
    :returns (mv mark copy strash aignet2)
    :index n
    :last (num-regs aignet))

  (def-aignet-preservation-thms aignet-copy-dfs-regs-iter
    :stobjname aignet2)

  (defthm memo-tablep-of-aignet-copy-dfs-regs-iter-copy
    (<= (len copy)
        (len (mv-nth 1 (aignet-copy-dfs-regs-iter
                        n aignet mark copy strash gatesimp aignet2))))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-dfs-regs-iter
             n aignet mark copy strash gatesimp
             aignet2)))
    :rule-classes :linear)

  (defthm memo-tablep-of-aignet-copy-dfs-regs-iter-mark
    (<= (len mark)
        (len (mv-nth 0 (aignet-copy-dfs-regs-iter
                        n aignet mark copy strash gatesimp aignet2))))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-dfs-regs-iter
             n aignet mark copy strash gatesimp
             aignet2)))
    :rule-classes :linear)

  (defthm aignet-copy-dfs-regs-iter-preserves-marked
    (implies (equal 1 (nth id mark))
             (equal (nth id (mv-nth 0 (aignet-copy-dfs-regs-iter
                                       n aignet mark copy strash gatesimp
                                       aignet2)))
                    1))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-dfs-regs-iter
             n aignet mark copy strash gatesimp
             aignet2))))

  (defthm aignet-copy-dfs-regs-iter-preserves-marked-lits
    (implies (equal 1 (nth id mark))
             (equal (nth-lit id (mv-nth 1 (aignet-copy-dfs-regs-iter
                                           n aignet mark copy strash gatesimp
                                           aignet2)))
                    (nth-lit id copy)))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-dfs-regs-iter
             n aignet mark copy strash gatesimp
             aignet2))))

  (defthm aignet-copy-dfs-regs-iter-preserves-marked-lit-copies
    (implies (equal 1 (nth (lit->var lit) mark))
             (equal (lit-copy lit (mv-nth 1 (aignet-copy-dfs-regs-iter
                                             n aignet mark copy strash gatesimp
                                             aignet2)))
                    (lit-copy lit copy)))
    :hints(("Goal" :in-theory (enable lit-copy))))

  (defthm aignet-copy-dfs-regs-iter-preserves-ci-copy
    (implies (equal (id->type id aignet) (in-type))
             (equal (nth-lit id (mv-nth 1 (aignet-copy-dfs-regs-iter
                                           n aignet mark copy strash gatesimp
                                           aignet2)))
                    (nth-lit id copy)))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-dfs-regs-iter
             n aignet mark copy strash gatesimp
             aignet2))))

  (defthm aignet-copies-ok-of-aignet-copy-dfs-regs-iter
    (implies (and (<= (nfix n) (num-regs aignet))
                  (aignet-copies-in-bounds copy aignet2))
             (b* (((mv & copy & aignet2)
                   (aignet-copy-dfs-regs-iter
                    n aignet mark copy strash gatesimp aignet2)))
               (aignet-copies-in-bounds
                                 copy aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-regs-iter
              n aignet mark copy strash gatesimp aignet2))))

  (defthm aignet-copy-dfs-regs-iter-preserves-aignet-cis-copied
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (aignet-cis-copied aignet copy aignet2)
                  (<= (nfix n) (num-regs aignet)))
             (b* (((mv & copy & aignet2)
                   (aignet-copy-dfs-regs-iter
                    n aignet mark copy strash gatesimp aignet2)))
               (aignet-cis-copied aignet copy aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-regs-iter
              n aignet mark copy strash gatesimp aignet2))))

  (local (defthm decr-less-when-lte
           (implies (<= n m)
                    (and (< (+ -1 n) m)
                         (<= (+ -1 n) m)))))

  (defthm aignet-copy-dfs-regs-iter-preserves-aignet-copy-dfs-simple-invar
    (implies (and (aignet-copy-dfs-simple-invar aignet mark copy aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (aignet-cis-copied aignet copy aignet2)
                  (<= (nfix n) (num-regs aignet)))
             (b* (((mv mark copy ?strash aignet2)
                   (aignet-copy-dfs-regs-iter
                    n aignet mark copy strash gatesimp aignet2)))
               (aignet-copy-dfs-simple-invar aignet mark copy aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-regs-iter
              n aignet mark copy strash gatesimp aignet2))))

  (defthm fanin-marked-of-aignet-copy-dfs-regs-iter
    (implies (< (nfix m) (nfix n))
             (equal (nth (lit->var (lookup-reg->nxst m aignet))
                         (mv-nth 0 (aignet-copy-dfs-regs-iter
                                    n aignet mark copy strash gatesimp aignet2)))
                    1))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-regs-iter
              n aignet mark copy strash gatesimp aignet2))))

  (defthm stype-counts-preserved-of-aignet-copy-dfs-regs-iter
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype (mv-nth 3 (aignet-copy-dfs-regs-iter
                                                  n aignet mark copy
                                                  strash gatesimp aignet2)))
                    (stype-count stype aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-regs-iter
              n aignet mark copy
              strash gatesimp aignet2))))

  (defthm stype-counts-preserved-of-aignet-copy-dfs-regs
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype (mv-nth 3 (aignet-copy-dfs-regs
                                                  aignet mark copy
                                                  strash gatesimp aignet2)))
                    (stype-count stype aignet2))))

  (defthm lit-eval-nxst-copy-of-aignet-copy-dfs-regs-iter
    (implies (and (aignet-copy-dfs-simple-invar aignet mark copy aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (aignet-cis-copied aignet copy aignet2)
                  (<= (nfix n) (num-regs aignet)))
             (b* (((mv ?mark copy ?strash aignet2)
                   (aignet-copy-dfs-regs-iter
                    n aignet mark copy strash gatesimp aignet2)))
               (implies (< (nfix m) (nfix n))
                        (equal (lit-eval (lit-copy (lookup-reg->nxst m aignet) copy)
                                         invals regvals aignet2)
                               (nxst-eval m invals regvals aignet)))))
    :hints(("Goal" :in-theory (e/d (nxst-eval)
                                   (aignet-copy-dfs-regs-iter-preserves-aignet-copy-dfs-simple-invar))
            :do-not-induct t
            :use aignet-copy-dfs-regs-iter-preserves-aignet-copy-dfs-simple-invar))))




(defsection aignet-copy-dfs

  (local (in-theory (disable acl2::resize-list-when-atom)))
  

  (defund aignet-copy-dfs-setup (aignet mark copy aignet2)
    (declare (xargs :stobjs (aignet mark copy aignet2)))
    (b* ((aignet2 (aignet-init (lnfix (num-outs aignet))
                               (lnfix (num-regs aignet))
                               (lnfix (num-ins aignet))
                               (lnfix (num-fanins aignet))
                               aignet2))
         (mark (bitarr-clear mark))
         (mark (resize-bits (num-fanins aignet) mark))
         (copy (litarr-clear copy))
         (copy (resize-lits (num-fanins aignet) copy))
         ((mv copy aignet2)
          (aignet-copy-ins aignet copy aignet2))
         ((mv copy aignet2)
          (aignet-copy-regs aignet copy aignet2)))
      (mv mark copy aignet2)))

  (local (in-theory (enable aignet-copy-dfs-setup)))

  (defthm aignet-copy-dfs-setup-normalize
    (implies (syntaxp (not (and (equal mark ''nil)
                                (equal copy ''nil)
                                (equal aignet2 ''nil))))
             (equal (aignet-copy-dfs-setup aignet mark copy
                                           aignet2)
                    (aignet-copy-dfs-setup aignet nil nil nil))))

  (defthm aignet-copy-dfs-setup-arrays-sized
    (b* (((mv mark copy ?aignet2)
          (aignet-copy-dfs-setup aignet mark copy
                                 aignet2)))
      (and (< (fanin-count aignet) (len mark))
           (< (fanin-count aignet) (len copy))))
    :rule-classes :linear)

  (defthm aignet-copy-dfs-setup-well-formed
    (b* (((mv ?mark copy aignet2)
          (aignet-copy-dfs-setup aignet mark copy
                                 aignet2)))
      (aignet-copies-in-bounds copy aignet2)))

  (defthm num-outs-of-aignet-copy-dfs-setup
    (equal (stype-count (po-stype)
                        (mv-nth 2 (aignet-copy-dfs-setup
                                   aignet mark copy aignet2)))
           0))

  (defthm num-regs-of-aignet-copy-dfs-setup
    (equal (stype-count (reg-stype)
                        (mv-nth 2 (aignet-copy-dfs-setup
                                   aignet mark copy aignet2)))
           (stype-count (reg-stype) aignet)))

  (defun aignet-copy-dfs (aignet aignet2 gatesimp)
    (declare (xargs :stobjs (aignet aignet2)
                    :guard (gatesimp-p gatesimp)))
    (b* (((local-stobjs mark copy strash)
          (mv mark copy strash aignet2))
         ((mv mark copy aignet2)
          (aignet-copy-dfs-setup aignet mark copy aignet2))
         ((mv mark copy strash aignet2)
          (aignet-copy-dfs-regs aignet mark copy strash
                                gatesimp aignet2))
         ((mv mark copy strash aignet2)
          (aignet-copy-dfs-outs aignet mark copy strash
                                gatesimp aignet2))
         (aignet2 (aignet-copy-outs aignet copy aignet2))
         (aignet2 (aignet-copy-nxsts aignet copy aignet2)))
      (mv mark copy strash aignet2)))

  (local (in-theory (disable aignet-copy-ins aignet-copy-regs)))

  (defthm initial-marks-empty
    (not (equal (nth n (resize-list nil m 0)) 1)))

  (defthm aignet-copy-dfs-simple-invar-of-aignet-copy-dfs-setup-lemma
    (mv-let (mark copy aignet2)
      (aignet-copy-dfs-setup aignet nil nil aignet2)
      (implies (and (aignet-idp id aignet)
                    (equal (nth id mark) 1))
               (equal (lit-eval (nth-lit id copy)
                                invals regvals aignet2)
                      (id-eval id invals regvals aignet))))
    :hints(("Goal" :in-theory (e/d ())
            :cases ((equal (id->type id aignet) 0)))
           '(:cases ((equal (id->regp id aignet) 1)))
           ;; :expand ((:free (copy aignet2)
           ;;           (lit-eval (nth-lit (id-val id) copy)
           ;;                     invals regvals aignet2))
           ;;          (id-eval id invals regvals aignet))
           ))


  (defthm aignet-copy-dfs-simple-invar-of-aignet-copy-dfs-setup
    (mv-let (mark copy aignet2)
      (aignet-copy-dfs-setup aignet nil nil aignet2)
      (aignet-copy-dfs-simple-invar aignet mark copy aignet2))
    :hints(("Goal" :in-theory (e/d (aignet-copy-dfs-simple-invar)
                                   (aignet-copy-dfs-setup)))))

  (defthm aignet-cis-copied-of-aignet-copy-dfs-setup
    (b* (((mv ?mark copy aignet2)
          (aignet-copy-dfs-setup aignet nil nil aignet2)))
      (aignet-cis-copied aignet copy aignet2)))

  (defthm nth-0-copy-of-aignet-copy-dfs-setup
    (b* (((mv ?mark copy ?aignet2)
          (aignet-copy-dfs-setup aignet nil nil aignet2)))
      (equal (nth-lit 0 copy) 0)))



  (defthm num-outs-of-aignet-copy-outs-iter
    (equal (stype-count (po-stype) (aignet-copy-outs-iter
                                    n aignet copy aignet2))
           (+ (nfix n) (stype-count (po-stype) aignet2)))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-outs-iter n aignet copy aignet2))))


  (defthm output-eval-of-aignet-copy-outs
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (< (nfix m) (num-outs aignet))
                  (zp (num-outs aignet2)))
             (let ((aignet2-new (aignet-copy-outs aignet copy aignet2)))
               (equal (output-eval m invals regvals aignet2-new)
                      (lit-eval (lit-copy (fanin :co (lookup-stype m (po-stype) aignet))
                                          copy)
                                invals regvals aignet2))))
    :hints(("Goal" :in-theory (enable output-eval))))


  (defthm aignet-copy-dfs-simple-invar-necc-out-special
    (b* (((mv mark copy & aignet2)
          (aignet-copy-dfs-outs-iter n aignet mark copy strash gatesimp
                                     aignet2)))
      (implies
       (aignet-copy-dfs-simple-invar aignet mark copy aignet2)
       (implies (and (aignet-idp id aignet)
                     (equal 1 (get-bit id mark)))
                (equal (lit-eval (nth-lit id copy)
                                 invals regvals aignet2)
                       (id-eval id invals regvals aignet))))))


  (defthm output-eval-of-aignet-copy-dfs
    (let ((aignet2 (aignet-copy-dfs aignet aignet2 gatesimp)))
      (equal (output-eval n invals regvals aignet2)
             (output-eval n invals regvals aignet)))
    :hints(("Goal" :in-theory (e/d* (fanin-count-lookup-stype-when-out-of-bounds)
                                    (aignet-copy-dfs-setup))
            :cases ((< (nfix n) (num-outs aignet))))
           (and stable-under-simplificationp
                '(:in-theory (enable output-eval)))))


  (defthm nxst-eval-of-aignet-copy-nxsts
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (< (nfix m) (num-regs aignet))
                  (<= (num-regs aignet) (num-regs aignet2)))
             (let ((aignet2-new (aignet-copy-nxsts aignet copy aignet2)))
               (equal (nxst-eval m invals regvals aignet2-new)
                      (lit-eval (lit-copy (lookup-reg->nxst m aignet)
                                          copy)
                                invals regvals aignet2))))
    :hints(("Goal" :in-theory (enable nxst-eval))))


  (defthm aignet-copy-dfs-simple-invar-necc-nxst-special
    (b* (((mv mark copy & aignet2)
          (aignet-copy-dfs-regs-iter n aignet mark copy strash gatesimp
                                      aignet2)))
      (implies
       (aignet-copy-dfs-simple-invar aignet mark copy aignet2)
       (implies (and (aignet-idp id aignet)
                     (equal 1 (get-bit id mark)))
                (equal (lit-eval (nth-lit id copy)
                                 invals regvals aignet2)
                       (id-eval id invals regvals aignet))))))

  (defthm eval-regin-of-aignet-copy-dfs
    (let ((aignet2 (aignet-copy-dfs aignet aignet2 gatesimp)))
      (equal (lit-eval (lookup-reg->nxst n aignet2)
                       invals regvals aignet2)
             (lit-eval (lookup-reg->nxst n aignet)
                       invals regvals aignet)))
    :hints(("Goal" :in-theory (e/d* (fanin-count-lookup-stype-when-out-of-bounds
                                     lookup-reg->nxst-out-of-bounds
                                     nxst-eval)
                                    (aignet-copy-dfs-setup))
            :cases ((< (nfix n) (num-regs aignet))))))


  (defthm nxst-eval-of-aignet-copy-dfs
    (let ((aignet2 (aignet-copy-dfs aignet aignet2 gatesimp)))
      (equal (nxst-eval n invals regvals aignet2)
             (nxst-eval n invals regvals aignet)))
    :hints(("Goal" :in-theory (e/d* (fanin-count-lookup-stype-when-out-of-bounds
                                     lookup-reg->nxst-out-of-bounds)
                                    (aignet-copy-dfs-setup))
            :cases ((< (nfix n) (num-regs aignet))))
           (and stable-under-simplificationp
                '(:in-theory (enable nxst-eval)))))

  (defthm num-outs-of-aignet-copy-dfs
    (equal (stype-count (po-stype) (aignet-copy-dfs aignet aignet2 gatesimp))
           (stype-count (po-stype) aignet)))

  (defthm num-regs-of-aignet-copy-dfs
    (equal (stype-count (reg-stype) (aignet-copy-dfs aignet aignet2 gatesimp))
           (stype-count (reg-stype) aignet)))


  (defthm aignet-copy-dfs-comb-equiv
    (comb-equiv (aignet-copy-dfs aignet aignet2 gatesimp)
                aignet)
    :hints(("Goal" :in-theory (e/d (comb-equiv
                                    nxsts-comb-equiv
                                    outs-comb-equiv)
                                   (aignet-copy-dfs))))))



(defsection aignet-mark-measure
  (local (defun aignet-mark-measure-ind (i n mark)
           (if (zp i)
               (list n mark)
             (aignet-mark-measure-ind (1- i) (1- (nfix n)) (cdr mark)))))

  (local (defthm aignet-mark-measure-lemma
           (implies (and (< (nfix i) (nfix n))
                         (not (equal 1 (nth i mark))))
                    (< (acl2::count-listp 1 mark n)
                       (acl2::count-listp 1 (update-nth i 1 mark) n)))
           :hints (("goal" :induct (aignet-mark-measure-ind i n mark)
                    :in-theory (e/d (update-nth nth)
                                    (acl2::zp-when-gt-0))))
           :rule-classes :linear))

  (local (defthm count-listp-<=-end
           (<= (acl2::count-listp a x e) (nfix e))
           :rule-classes :linear))

  (defund-nx aignet-mark-measure (mark aignet)
    (- (+ 1 (fanin-count aignet))
       (acl2::count-listp 1 mark (+ 1 (fanin-count aignet)))))

  (defthm natp-aignet-mark-measure
    (natp (aignet-mark-measure mark aignet))
    :hints(("Goal" :in-theory (enable aignet-mark-measure)))
    :rule-classes :type-prescription)

  ;; the above is stronger than the automatic type-prescription
  (in-theory (disable (:type-prescription aignet-mark-measure)))

  (defthm aignet-mark-measure-decr
    (implies (and (aignet-idp id aignet)
                  (not (equal 1 (nth id mark))))
             (< (aignet-mark-measure (update-nth id 1 mark) aignet)
                (aignet-mark-measure mark aignet)))
    :hints(("Goal" :in-theory (enable aignet-mark-measure
                                      aignet-idp)))
    :rule-classes (:rewrite :linear)))

(defsection aignet-mark-dfs-rec

  (local (in-theory (disable lookup-id-in-bounds-when-positive
                             lookup-id-out-of-bounds
                             default-car
                             fanin-count-of-lookup-id-when-consp
                             acl2::nth-when-zp)))

  (defund aignet-mark-dfs-rec (id mark aignet)
    (declare (type (integer 0 *) id)
             (xargs :stobjs (mark aignet)
                    :guard (and (<= (num-fanins aignet) (bits-length mark))
                                (id-existsp id aignet))
                    :verify-guards nil
                    :measure (aignet-mark-measure mark aignet)))
    (b* (((when (mbe :logic
                     (or (not (id-existsp id aignet))
                         (int= 1 (get-bit id mark)))
                     :exec (int= 1 (get-bit id mark))))
          mark)
         (mark (set-bit id 1 mark))
         (type (id->type id aignet))
         ((when (or (int= type (in-type))
                    (int= type (const-type))))
          mark))
      (mbe :logic
           (non-exec
            (b* ((mark1 (aignet-mark-dfs-rec
                                 (lit-id (gate-id->fanin0 id aignet))
                                 mark aignet))
                 ((unless (<= (aignet-mark-measure mark1 aignet)
                              (aignet-mark-measure mark aignet)))
                  mark1))
              (aignet-mark-dfs-rec
               (lit-id (gate-id->fanin1 id aignet))
               mark1 aignet)))
           :exec
           (b* ((mark (aignet-mark-dfs-rec
                               (lit-id (gate-id->fanin0 id aignet))
                               mark aignet)))
             (aignet-mark-dfs-rec
              (lit-id (gate-id->fanin1 id aignet))
              mark aignet)))))

  (local (in-theory (enable aignet-mark-dfs-rec)))

  (defthm aignet-mark-dfs-rec-preserves-mark
    (implies (equal 1 (nth n mark))
             (equal (nth n (aignet-mark-dfs-rec id mark aignet)) 1)))

  (defthm aignet-mark-dfs-rec-preserves-memo-tablep
    (<= (len mark)
        (len (aignet-mark-dfs-rec id mark aignet)))
    :rule-classes :linear)

  (defthm aignet-mark-dfs-rec-decreases-measure-weak
    (<= (aignet-mark-measure (aignet-mark-dfs-rec id mark aignet) aignet)
        (aignet-mark-measure mark aignet))
    :rule-classes (:rewrite :linear))

  (defthm id-marked-of-aignet-mark-dfs-rec
    (implies (aignet-idp id aignet)
             (equal (nth id (aignet-mark-dfs-rec id mark aignet))
                    1)))

  (local (in-theory (disable len)))

  (defthm len-of-update-nth
    (<= (len x)
        (len (update-nth n v x)))
    :rule-classes :linear)

  (local (in-theory (disable ;; acl2::len-update-nth1
                             acl2::len-update-nth)))

  (verify-guards aignet-mark-dfs-rec
    :guard-debug t
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable aignet-idp))))))


(defsection aignet-mark-comb-invar
  (local (in-theory (disable acl2::nth-when-zp
                             lookup-id-out-of-bounds
                             acl2::nfix-equal-to-nonzero
                             acl2::zp-when-integerp)))

  (defmacro gate-fanins-marked (id aignet mark)
    `(let ((look (lookup-id ,id ,aignet)))
       (and (equal (nth (lit-id (fanin :gate0 look))
                        ,mark)
                   1)
            (equal (nth (lit-id (fanin :gate1 look))
                        ,mark)
                   1))))

  (defmacro co-fanin-marked (n aignet mark)
    `(let ((look (lookup-stype ,n :po ,aignet)))
       (equal (nth (lit-id (fanin :co look))
                   ,mark)
              1)))


  ;; The non-inductive, nicer invariant:
  ;;  -- For all nodes that are marked, their fanins are also marked.
  (defun-sk aignet-mark-comb-invar (mark aignet)
    (forall id
            (implies
             (and (equal 1 (get-bit id mark))
                  (equal (id->type id aignet) (gate-type)))
             (gate-fanins-marked id aignet mark)))
    :rewrite :direct)

  (in-theory (disable aignet-mark-comb-invar))


  (local
   (defsection aignet-mark-comb-invar-inductive

     ;; The inductive invariant:
     ;; -- All nodes marked in the original are marked in the result
     ;; -- For all nodes marked in the result that were not
     ;;    marked in the original, their fanins are also marked
     ;;    in the result.
     (defun-sk aignet-mark-comb-invar1 (mark1 mark2 aignet)
       (forall
        id
        (and
         (implies
          (and (not (equal 1 (get-bit id mark1)))
               (equal 1 (get-bit id mark2))
               (equal (id->type id aignet) (gate-type)))
          (gate-fanins-marked id aignet mark2))
         (implies (equal 1 (get-bit id mark1))
                  (equal (nth id mark2) 1))))
       :rewrite :direct)

     (in-theory (disable aignet-mark-comb-invar1))

     (defthm aignet-mark-comb-invar1-mark-preserved
       (implies (and (aignet-mark-comb-invar1 mark1 mark2 aignet)
                     (equal 1 (get-bit id mark1)))
                (equal (nth id mark2) 1)))


     (defthmd aignet-mark-comb-invar1-transitive-lemma
       (implies (and (aignet-mark-comb-invar1 mark2 mark3 aignet)
                     (aignet-mark-comb-invar1 mark1 mark2 aignet))
                (and
                 (implies
                  (and (not (equal 1 (get-bit id mark1)))
                       (equal 1 (get-bit id mark3))
                       (equal (id->type id aignet) (gate-type)))
                  (gate-fanins-marked id aignet mark3))
                 (implies (equal 1 (get-bit id mark1))
                          (equal (nth id mark3) 1))))
       :hints (("goal" :in-theory (disable aignet-mark-comb-invar1-necc)
                :use ((:instance aignet-mark-comb-invar1-necc)
                      (:instance aignet-mark-comb-invar1-necc
                       (mark1 mark2) (mark2 mark3))))))

     (defthm aignet-mark-comb-invar1-transitive
       (implies (and (aignet-mark-comb-invar1 mark1 mark2 aignet)
                     (aignet-mark-comb-invar1 mark2 mark3 aignet))
                (aignet-mark-comb-invar1 mark1 mark3 aignet))
       :hints (("goal" :in-theory (enable
                                   aignet-mark-comb-invar1-transitive-lemma)
                :expand ((aignet-mark-comb-invar1 mark1 mark3 aignet)))))


     (defthmd aignet-mark-comb-invar-special-gate-lemma
       (implies (and (aignet-mark-comb-invar1
                      (update-nth id1 1 mark1)
                      mark2 aignet)
                     (equal (id->type id1 aignet) (gate-type))
                     (gate-fanins-marked id1 aignet mark2))
                (and
                 (implies
                  (and (not (equal 1 (get-bit id mark1)))
                       (equal 1 (get-bit id mark2))
                       (equal (id->type id aignet) (gate-type)))
                  (gate-fanins-marked id aignet mark2))
                 (implies (equal 1 (get-bit id mark1))
                          (equal (nth id mark2) 1))))
       :hints (("goal"
                :in-theory (disable aignet-mark-comb-invar1-necc)
                :use
                ((:instance aignet-mark-comb-invar1-necc
                  (mark1 (update-nth id1 1 mark1)))))))


     (defthm aignet-mark-comb-invar-special-gate
       (implies (and (bind-free '((id1 . id)) (id1))
                     (aignet-mark-comb-invar1
                      (update-nth id1 1 mark1)
                      mark2 aignet)
                     (equal (id->type id1 aignet) (gate-type))
                     (gate-fanins-marked id1 aignet mark2))
                (aignet-mark-comb-invar1 mark1 mark2 aignet))
       :hints (("goal"
                :expand ((aignet-mark-comb-invar1 mark1 mark2 aignet))
                :in-theory (enable aignet-mark-comb-invar-special-gate-lemma)))
       :rule-classes ((:rewrite :backchain-limit-lst (nil 1 nil nil))))


     (defthm aignet-mark-comb-invar1-self
       (aignet-mark-comb-invar1 mark mark aignet)
       :hints (("goal" :in-theory (enable aignet-mark-comb-invar1))))

     (defthm aignet-mark-comb-invar1-mark-non-gate
       (implies (not (equal (id->type id aignet) (gate-type)))
                (aignet-mark-comb-invar1 mark (update-nth id 1 mark) aignet))
       :hints (("goal" :in-theory (enable aignet-mark-comb-invar1))))

     (defthm aignet-mark-comb-invar1-mark-const
       (implies (equal (id->type id aignet) (const-type))
                (aignet-mark-comb-invar1 mark (update-nth id 1 mark) aignet))
       :hints (("goal" :in-theory (enable aignet-mark-comb-invar1))))

     (local (defthm stype-possibilities-comb
              (implies (and (not (equal (ctype (stype x)) (gate-ctype)))
                            (not (equal (ctype (stype x)) (in-ctype)))
                            (not (equal (ctype (stype x)) (out-ctype))))
                       (equal (stype x) (const-stype)))
              :hints(("Goal" :in-theory (enable stype stype-fix stypep)))))


     (defthm aignet-mark-comb-invar1-of-aignet-mark-dfs-rec
       (aignet-mark-comb-invar1
        mark
        (aignet-mark-dfs-rec id mark aignet)
        aignet)
       :hints (("goal" :induct (aignet-mark-dfs-rec id mark aignet)
                :in-theory (enable (:induction aignet-mark-dfs-rec))
                :expand ((aignet-mark-dfs-rec id mark aignet)))
               (and stable-under-simplificationp
                    '(:cases ((equal (id->type id aignet) 1))))))


     (defthmd aignet-mark-comb-invar-by-aignet-mark-comb-invar1-lemma
       (implies (and (aignet-mark-comb-invar mark1 aignet)
                     (aignet-mark-comb-invar1 mark1 mark2 aignet))
                (implies
                 (and (equal 1 (get-bit id mark2))
                      (equal (id->type id aignet) (gate-type)))
                 (gate-fanins-marked id aignet mark2)))
       :hints (("goal" :use ((:instance aignet-mark-comb-invar-necc
                              (mark mark1))
                             (:instance aignet-mark-comb-invar1-necc))
                :in-theory (disable aignet-mark-comb-invar1-necc
                                    aignet-mark-comb-invar-necc))))

     (defthm aignet-mark-comb-invar-by-aignet-mark-comb-invar1
       (implies (and (aignet-mark-comb-invar mark1 aignet)
                     (aignet-mark-comb-invar1 mark1 mark2 aignet))
                (aignet-mark-comb-invar mark2 aignet))
       :hints (("goal" :expand ((aignet-mark-comb-invar mark2 aignet))
                :in-theory
                (enable
                 aignet-mark-comb-invar-by-aignet-mark-comb-invar1-lemma))))))

  (local (defthm bit-equiv-of-equal-1
           (implies (and (bit-equiv x (double-rewrite y))
                         (syntaxp (not (equal x y))))
                    (equal (equal 1 y)
                           (equal 1 x)))))

  (defcong bits-equiv equal (aignet-mark-comb-invar mark aignet) 1
    :hints(("goal" :cases ((aignet-mark-comb-invar mark aignet)))
           (and stable-under-simplificationp
                (let* ((term (assoc 'aignet-mark-comb-invar clause))
                       (other-var (if (eq (cadr term) 'mark)
                                      'mark-equiv
                                    'mark)))
                  `(:expand (,term)
                    :use ((:instance aignet-mark-comb-invar-necc
                           (mark ,other-var)
                           (id ,(cons 'aignet-mark-comb-invar-witness
                                      (cdr term))))))))))

  (defthm aignet-mark-comb-invar-of-empty
    (aignet-mark-comb-invar nil aignet)
    :hints(("Goal" :in-theory (enable aignet-mark-comb-invar))))


  (defthm aignet-mark-comb-invar-preserved-by-aignet-mark-dfs-rec
    (implies (aignet-mark-comb-invar mark aignet)
             (aignet-mark-comb-invar
              (aignet-mark-dfs-rec id mark aignet)
              aignet)))

  (defthm aignet-mark-comb-invar-of-aignet-copy-dfs-setup
    (aignet-mark-comb-invar
     (mv-nth 0 (aignet-copy-dfs-setup aignet mark copy aignet2))
     aignet)
    :hints(("Goal" :in-theory (enable aignet-mark-comb-invar
                                      aignet-copy-dfs-setup)))))


(defsection aignet-mark-dfs-comb
  (defiteration aignet-mark-dfs-outs (mark aignet)
    (declare (xargs :stobjs (mark aignet)
                    :guard (and (<= (num-fanins aignet) (bits-length mark)))))
    (aignet-mark-dfs-rec (lit->var (outnum->fanin n aignet)) mark aignet)
    :returns mark
    :index n
    :last (num-outs aignet))

  (in-theory (disable aignet-mark-dfs-outs))
  (local (in-theory (enable aignet-mark-dfs-outs)))

  (defthm outputs-marked-of-aignet-mark-dfs-outs-iter
    (implies (and (< (nfix n) (nfix m))
                  (<= (nfix m) (stype-count (po-stype) aignet)))
             (equal (nth (lit->var (fanin :co (lookup-stype n (po-stype) aignet)))
                         (aignet-mark-dfs-outs-iter m mark aignet))
                    1))
    :hints((acl2::just-induct-and-expand
            (aignet-mark-dfs-outs-iter m mark aignet))))

  (defthm aignet-mark-comb-invar-preserved-by-aignet-mark-dfs-outs-iter
    (implies (and (aignet-mark-comb-invar mark aignet))
             (aignet-mark-comb-invar
              (aignet-mark-dfs-outs-iter m mark aignet)
              aignet))
    :hints((acl2::just-induct-and-expand
            (aignet-mark-dfs-outs-iter m mark aignet))))

  (defthm aignet-mark-dfs-outs-iter-preserves-mark
    (implies (equal 1 (nth n mark))
             (equal (nth n (aignet-mark-dfs-outs-iter m mark aignet)) 1))
    :hints ((acl2::just-induct-and-expand
             (aignet-mark-dfs-outs-iter m mark aignet))))

  (defthm aignet-mark-dfs-outs-iter-preserves-memo-tablep
    (<= (len mark)
        (len (aignet-mark-dfs-outs-iter m mark aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet-mark-dfs-outs-iter m mark aignet)))
    :rule-classes :linear)

  (defthm outputs-marked-of-aignet-mark-dfs-outs
    (implies (and (< (nfix n) (stype-count (po-stype) aignet)))
             (equal (nth (lit->var (fanin :co (lookup-stype n (po-stype) aignet)))
                         (aignet-mark-dfs-outs mark aignet))
                    1)))

  (defthm aignet-mark-comb-invar-preserved-by-aignet-mark-dfs-outs
    (implies (and (aignet-mark-comb-invar mark aignet))
             (aignet-mark-comb-invar
              (aignet-mark-dfs-outs mark aignet)
              aignet)))

  (defthm aignet-mark-dfs-outs-preserves-mark
    (implies (equal 1 (nth n mark))
             (equal (nth n (aignet-mark-dfs-outs mark aignet)) 1)))

  (defthm aignet-mark-dfs-outs-preserves-memo-tablep
    (<= (len mark)
        (len (aignet-mark-dfs-outs mark aignet)))
    :rule-classes :linear)


  (defiteration aignet-mark-dfs-nxsts (mark aignet)
    (declare (xargs :stobjs (mark aignet)
                    :guard (and (<= (num-fanins aignet) (bits-length mark)))))
    (aignet-mark-dfs-rec (lit->var (regnum->nxst n aignet)) mark aignet)
    :returns mark
    :index n
    :last (num-regs aignet))

  (in-theory (disable aignet-mark-dfs-nxsts))
  (local (in-theory (enable aignet-mark-dfs-nxsts
                            (:induction aignet-mark-dfs-nxsts-iter))))

  (defthm nxsts-marked-of-aignet-mark-dfs-nxsts-iter
    (implies (and (< (nfix n) (nfix m))
                  (<= (nfix m) (stype-count (reg-stype) aignet)))
             (equal (nth (lit->var (lookup-reg->nxst n aignet))
                         (aignet-mark-dfs-nxsts-iter m mark aignet))
                    1))
    :hints((acl2::just-induct-and-expand
            (aignet-mark-dfs-nxsts-iter m mark aignet))))

  (defthm aignet-mark-comb-invar-preserved-by-aignet-mark-dfs-nxsts-iter
    (implies (and (aignet-mark-comb-invar mark aignet))
             (aignet-mark-comb-invar
              (aignet-mark-dfs-nxsts-iter m mark aignet)
              aignet))
    :hints((acl2::just-induct-and-expand
            (aignet-mark-dfs-nxsts-iter m mark aignet))))

  (defthm aignet-mark-dfs-nxsts-iter-preserves-mark
    (implies (equal 1 (nth n mark))
             (equal (nth n (aignet-mark-dfs-nxsts-iter m mark aignet)) 1))
    :hints ((acl2::just-induct-and-expand
             (aignet-mark-dfs-nxsts-iter m mark aignet))))

  (defthm aignet-mark-dfs-nxsts-iter-preserves-memo-tablep
    (<= (len mark)
        (len (aignet-mark-dfs-nxsts-iter m mark aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet-mark-dfs-nxsts-iter m mark aignet)))
    :rule-classes :linear)

  (defthm nxsts-marked-of-aignet-mark-dfs-nxsts
    (implies (and (< (nfix n) (stype-count (reg-stype) aignet)))
             (equal (nth (lit->var (lookup-reg->nxst n aignet))
                         (aignet-mark-dfs-nxsts mark aignet))
                    1)))

  (defthm aignet-mark-comb-invar-preserved-by-aignet-mark-dfs-nxsts
    (implies (and (aignet-mark-comb-invar mark aignet))
             (aignet-mark-comb-invar
              (aignet-mark-dfs-nxsts mark aignet)
              aignet)))

  (defthm aignet-mark-dfs-nxsts-preserves-mark
    (implies (equal 1 (nth n mark))
             (equal (nth n (aignet-mark-dfs-nxsts mark aignet)) 1)))

  (defthm aignet-mark-dfs-nxsts-preserves-memo-tablep
    (<= (len mark)
        (len (aignet-mark-dfs-nxsts mark aignet)))
    :rule-classes :linear)

  (local (in-theory (disable aignet-mark-dfs-outs
                             aignet-mark-dfs-nxsts)))

  (defund aignet-mark-dfs-comb (mark aignet)
    (declare (xargs :stobjs (mark aignet)
                    :guard (and (<= (num-fanins aignet) (bits-length mark)))))
    (b* ((mark (aignet-mark-dfs-outs mark aignet)))
      (aignet-mark-dfs-nxsts mark aignet)))

  (local (in-theory (enable aignet-mark-dfs-comb)))


  (defthm nxsts-marked-of-aignet-mark-dfs-comb
    (implies (and (< (nfix n) (stype-count (reg-stype) aignet)))
             (equal (nth (lit->var
                          (lookup-reg->nxst n aignet))
                         (aignet-mark-dfs-comb mark aignet))
                    1)))

  (defthm outputs-marked-of-aignet-mark-dfs-comb
    (implies (and (< (nfix n) (stype-count (po-stype) aignet)))
             (equal (nth (lit->var (fanin :co (lookup-stype n (po-stype) aignet)))
                         (aignet-mark-dfs-comb mark aignet))
                    1)))

  (defthm aignet-mark-comb-invar-preserved-by-aignet-mark-dfs-comb
    (implies (and (aignet-mark-comb-invar mark aignet))
             (aignet-mark-comb-invar
              (aignet-mark-dfs-comb mark aignet)
              aignet)))

  (defthm aignet-mark-dfs-comb-preserves-mark
    (implies (equal 1 (nth n mark))
             (equal (nth n (aignet-mark-dfs-comb mark aignet)) 1)))

  (defthm aignet-mark-dfs-comb-preserves-memo-tablep
    (<= (len mark)
        (len (aignet-mark-dfs-comb mark aignet)))
    :rule-classes :linear))



(defsection aignet-copy-marked


  ;; Copy all CIs as well as any marked nodes, to maintain combinational equivalence
  (defiteration aignet-copy-marked (aignet mark copy strash gatesimp aignet2)
    (declare (xargs :stobjs (mark copy aignet strash aignet2)
                    :guard (and (<= (num-fanins aignet) (bits-length mark))
                                (<= (num-fanins aignet) (lits-length copy))
                                (aignet-copies-in-bounds copy aignet2)
                                (gatesimp-p gatesimp))
                    :guard-hints (("goal" :in-theory (enable aignet-idp)))))
    (b* ((id n)
         (copyp (int= (get-bit id mark) 1))
         ((unless copyp)
          (mv copy strash aignet2))
         (slot0 (id->slot id 0 aignet))
         (type (snode->type slot0)))
      (aignet-case
       type
       :gate (b* ((lit0 (snode->fanin slot0))
                  (slot1 (id->slot id 1 aignet))
                  (lit1 (snode->fanin slot1))
                  (xor (snode->regp slot1))
                  (c0 (lit-copy lit0 copy))
                  (c1 (lit-copy lit1 copy))
                  ((mv lit strash aignet2)
                   (if (eql 1 xor)
                       (aignet-hash-xor c0 c1 gatesimp strash aignet2)
                     (aignet-hash-and c0 c1 gatesimp strash aignet2)))
                  (copy (set-lit id lit copy)))
               (mv copy strash aignet2))
       ;; assumes inputs already taken care of
       :in (mv copy strash aignet2)
       :const (b* ((copy (set-lit id 0 copy)))
                (mv copy strash aignet2))))
    :returns (mv copy strash aignet2)
    :index n
    :last (num-fanins aignet))

  (in-theory (disable aignet-copy-marked))
  (local (in-theory (enable aignet-copy-marked)))

  (def-aignet-preservation-thms aignet-copy-marked-iter
    :stobjname aignet2)

  (def-aignet-preservation-thms aignet-copy-marked
    :stobjname aignet2)


  (defthm stype-counts-preserved-of-aignet-copy-marked-iter
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count
                     stype
                     (mv-nth 2
                             (aignet-copy-marked-iter
                              n aignet mark copy strash gatesimp aignet2)))
                    (stype-count stype aignet2)))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-marked-iter
                              n aignet mark copy strash gatesimp aignet2))))

  (defthm stype-counts-preserved-of-aignet-copy-marked
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count
                     stype
                     (mv-nth 2
                             (aignet-copy-marked
                              aignet mark copy strash gatesimp aignet2)))
                    (stype-count stype aignet2))))

  (defthm len-copies-of-aignet-copy-marked-iter
    (<= (len copy)
        (len (mv-nth 0 (aignet-copy-marked-iter
                        n aignet mark copy strash gatesimp aignet2))))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-marked-iter
             n aignet mark copy strash gatesimp aignet2)))
    :rule-classes :linear)

  (defthm len-copies-of-aignet-copy-marked
    (<= (len copy)
        (len (mv-nth 0 (aignet-copy-marked
                        aignet mark copy strash gatesimp aignet2))))
    :rule-classes :linear)


  (defthm nth-copy-preserved-by-aignet-copy-marked-iter
    (implies (or (equal (id->type idn aignet) (in-type))
                 (<= (nfix n) (nfix idn)))
             (b* (((mv copy1 & &)
                   (aignet-copy-marked-iter n aignet mark copy strash gatesimp aignet2)))
               (equal (nth-lit idn copy1)
                      (nth-lit idn copy))))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-marked-iter n aignet mark copy strash gatesimp
                                          aignet2))))

  (defthm input-copies-preserved-by-aignet-copy-marked
    (implies (equal (id->type idn aignet) (in-type))
             (b* (((mv copy1 & &)
                   (aignet-copy-marked aignet mark copy strash gatesimp aignet2)))
               (equal (nth-lit idn copy1)
                      (nth-lit idn copy)))))

  (defthm aignet-copy-marked-iter-preserves-aignet-copies-ok
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (<= (nfix n) (+ 1 (fanin-count aignet))))
             (b* (((mv copy1 & aignet2)
                   (aignet-copy-marked-iter n aignet mark copy strash gatesimp aignet2)))
               (aignet-copies-in-bounds copy1 aignet2)))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-marked-iter n aignet mark copy strash gatesimp
                                          aignet2))))

  (defthm aignet-copy-marked-preserves-aignet-copies-ok
    (implies (and (aignet-copies-in-bounds copy aignet2))
             (b* (((mv copy1 & aignet2)
                   (aignet-copy-marked aignet mark copy strash gatesimp aignet2)))
               (aignet-copies-in-bounds copy1 aignet2))))

  (defun-sk aignet-copy-marked-iter-invar (n aignet mark copy aignet2)
    (forall (id invals regvals)
            (implies (and (aignet-idp id aignet)
                          (equal (nth id mark) 1)
                          (or (equal (id->type id aignet) (in-type))
                              (< (nfix id) (nfix n))))
                     (and (aignet-idp (lit-id (nth-lit id copy)) aignet2)
                          (equal (lit-eval (nth-lit id copy)
                                           invals regvals aignet2)
                                 (id-eval id invals regvals aignet)))))
    :rewrite :direct)

  (in-theory (disable aignet-copy-marked-iter-invar))

  (defthm aignet-copy-marked-iter-invar-necc-lit-copy
    (implies (and (aignet-copy-marked-iter-invar n aignet mark copy aignet2)
                  (aignet-litp lit aignet)
                  (equal (nth (lit->var lit) mark) 1)
                  (or (equal (id->type (lit->var lit) aignet) (in-type))
                      (< (lit->var lit) (nfix n))))
             (equal (lit-eval (lit-copy lit copy) invals regvals aignet2)
                    (lit-eval lit invals regvals aignet)))
    :hints(("Goal" :in-theory (enable lit-copy)
            :expand ((lit-eval lit invals regvals aignet)))))
  ;; (local (defthm lit-eval-of-mk-lit-of-lit-id
  ;;          (equal (lit-eval (mk-lit (lit-id lit) neg) invals regvals aignet)
  ;;                 (b-xor (b-xor neg (lit-neg lit))
  ;;                        (lit-eval lit invals regvals aignet)))
  ;;          :hints(("Goal" :expand ((:free (lit) (lit-eval lit invals regvals aignet)))))))

  (local (in-theory (disable
                             nth-copy-preserved-by-aignet-copy-marked-iter)))




  (defthm aignet-copy-marked-invar-of-aignet-copy-dfs-setup
    (mv-let (mark copy aignet2)
      (aignet-copy-dfs-setup aignet nil nil aignet2)
      (declare (ignore mark))
      (aignet-copy-marked-iter-invar
       0 aignet mark2 copy aignet2))
    :hints(("Goal" :in-theory (e/d (aignet-copy-marked-iter-invar
                                    lit-eval id-eval
                                    aignet-copy-dfs-setup)))))

  (defthm aignet-copy-marked-iter-invar-preserved
    (implies (and (aignet-mark-comb-invar mark aignet)
                  (aignet-copy-marked-iter-invar 0 aignet mark copy
                                                      aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (<= (nfix n) (num-fanins aignet)))
             (b* (((mv copy & aignet2)
                   (aignet-copy-marked-iter n aignet mark copy strash gatesimp aignet2)))
               (aignet-copy-marked-iter-invar n aignet mark copy
                                                   aignet2)))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-marked-iter n aignet mark copy strash gatesimp
                                          aignet2))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause)))
                  :do-not-induct t
                  :do-not '(generalize fertilize eliminate-destructors)))
           (and stable-under-simplificationp
                (let ((witness (acl2::find-call-lst
                                'aignet-copy-marked-iter-invar-witness
                                clause)))
                  `(:clause-processor
                    (acl2::simple-generalize-cp
                     clause '(((mv-nth '0 ,witness) . id)
                              ((mv-nth '1 ,witness) . invals)
                              ((mv-nth '2 ,witness) . regvals))))))
           (and stable-under-simplificationp
                '(:cases ((< (nfix id) (+ -1 n)))
                  :expand ((id-eval id invals regvals aignet)
                           (id-eval (+ -1 n) invals regvals aignet))
                  :in-theory (enable lit-eval eval-and-of-lits eval-xor-of-lits)))))

  (defthm aignet-copy-marked-invar-preserved
    (implies (and (aignet-mark-comb-invar mark aignet)
                  (aignet-copy-marked-iter-invar 0 aignet mark copy
                                                      aignet2)
                  (aignet-copies-in-bounds copy aignet2))
             (b* (((mv copy & aignet2)
                   (aignet-copy-marked aignet mark copy strash gatesimp aignet2)))
               (aignet-copy-marked-iter-invar
                (+ 1 (fanin-count aignet)) aignet mark copy aignet2))))

  (defthm aignet-copy-marked-invar-preserved-rw
    (implies (and (aignet-mark-comb-invar mark aignet)
                  (aignet-copy-marked-iter-invar 0 aignet mark copy
                                                      aignet2)
                  (aignet-copies-in-bounds copy aignet2))
             (b* (((mv copy & aignet2)
                   (aignet-copy-marked aignet mark copy strash gatesimp
                                            aignet2)))
               (implies (and (aignet-idp id aignet)
                             (equal (nth id mark) 1))
                        (equal (lit-eval (nth-lit id copy)
                                         invals regvals aignet2)
                               (id-eval id invals regvals aignet)))))
    :hints (("goal" :use aignet-copy-marked-invar-preserved
             :in-theory (e/d (aignet-idp)
                             (aignet-copy-marked-invar-preserved
                              aignet-copy-marked)))))

  (defthm aignet-copy-marked-invar-preserved-rw-lit-copy
    (implies (and (aignet-mark-comb-invar mark aignet)
                  (aignet-copy-marked-iter-invar 0 aignet mark copy
                                                      aignet2)
                  (aignet-copies-in-bounds copy aignet2))
             (b* (((mv copy & aignet2)
                   (aignet-copy-marked aignet mark copy strash gatesimp
                                            aignet2)))
               (implies (and (aignet-litp lit aignet)
                             (equal (nth (lit->var lit) mark) 1))
                        (equal (lit-eval (lit-copy lit copy)
                                         invals regvals aignet2)
                               (lit-eval lit invals regvals aignet)))))
    :hints (("goal" :use aignet-copy-marked-invar-preserved
             :in-theory (e/d (aignet-idp)
                             (aignet-copy-marked-invar-preserved
                              aignet-copy-marked))))))


(defsection aignet-prune-comb

  (local (defthm stype-when-out-of-bounds
           (implies (< (fanin-count aignet) (nfix id))
                    (equal (stype (car (lookup-id id aignet)))
                           (const-stype)))
           :hints(("Goal" :in-theory (enable lookup-id)))))

  (defthm aignet-copy-marked-iter-invar-of-aignet-copy-outs
    (implies (aignet-copy-marked-iter-invar
              (+ 1 (fanin-count aignet))
              aignet mark copy aignet2)
             (aignet-copy-marked-iter-invar
              (+ 1 (fanin-count aignet))
              aignet mark copy
              (aignet-copy-outs aignet copy aignet2)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm aignet-copy-marked-iter-invar-of-aignet-copy-nxsts
    (implies (aignet-copy-marked-iter-invar
              (+ 1 (fanin-count aignet))
              aignet mark copy aignet2)
             (aignet-copy-marked-iter-invar
              (+ 1 (fanin-count aignet))
              aignet mark copy
              (aignet-copy-nxsts aignet copy aignet2)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))
            ;; (and stable-under-simplificationp
            ;;      (let ((witness (acl2::find-call-lst
            ;;                      'aignet-copy-marked-iter-invar-witness
            ;;                      clause)))
            ;;        `(:clause-processor
            ;;          (acl2::simple-generalize-cp
            ;;           clause '(((mv-nth '0 ,witness) . id)
            ;;                    ((mv-nth '1 ,witness) . invals)
            ;;                    ((mv-nth '2 ,witness) . regvals))))))
            ))

  (define aignet-prune-comb-aux (mark copy aignet
                                      (gatesimp gatesimp-p)
                                      strash aignet2)
    (b* (((mv mark copy aignet2)
          (aignet-copy-dfs-setup aignet mark copy aignet2))
         (mark (aignet-mark-dfs-outs mark aignet))
         (mark (aignet-mark-dfs-nxsts mark aignet))
         ((mv copy strash aignet2)
          (aignet-copy-marked
           aignet mark copy strash gatesimp aignet2))
         (aignet2 (aignet-copy-outs aignet copy aignet2))
         (aignet2 (aignet-copy-nxsts aignet copy aignet2)))
      (mv mark copy strash aignet2))

    ///

    (defthm normalize-inputs-of-aignet-prune-comb-aux
      (implies (syntaxp (not (and (equal mark ''nil)
                                  (equal copy ''nil)
                                  (equal aignet2 ''nil))))
               (equal (aignet-prune-comb-aux mark copy aignet gatesimp strash aignet2)
                      (aignet-prune-comb-aux nil nil aignet gatesimp strash nil))))

    (defthm aignet-copy-marked-invar-of-aignet-prune-comb-aux
      (b* (((mv mark copy & aignet2)
            (aignet-prune-comb-aux
             mark copy aignet gatesimp strash aignet2)))
        (aignet-copy-marked-iter-invar
         (+ 1 (fanin-count aignet))
         aignet mark copy aignet2)))

    (defthm aignet-outs-marked-of-aignet-prune-comb-aux
      (b* (((mv mark ?copy & ?aignet2)
            (aignet-prune-comb-aux
             mark copy aignet gatesimp strash aignet2)))
        (implies (< (nfix n) (num-outs aignet))
                 (let ((id (lit->var (fanin :co (lookup-stype n (po-stype) aignet)))))
                   (equal (nth id mark) 1)))))

    (defthm aignet-nxsts-marked-of-aignet-prune-comb-aux
      (b* (((mv mark ?copy & ?aignet2)
            (aignet-prune-comb-aux
             mark copy aignet gatesimp strash aignet2)))
        (implies (< (nfix n) (num-regs aignet))
                 (let ((id (lit->var
                            (lookup-reg->nxst n aignet))))
                   (equal (nth id mark) 1)))))

    (defthm aignet-copies-ok-of-aignet-prune-comb-aux
      (b* (((mv ?mark ?copy & ?aignet2)
            (aignet-prune-comb-aux
             mark copy aignet gatesimp strash aignet2)))
        (aignet-copies-in-bounds copy aignet2)))


    (defthm output-eval-of-aignet-prune-comb-aux
      (b* (((mv ?mark ?copy & ?aignet2)
            (aignet-prune-comb-aux
             mark copy aignet gatesimp strash aignet2)))
        (equal (output-eval n invals regvals aignet2)
               (output-eval n invals regvals aignet)))
      :hints (("goal" :cases ((< (nfix n) (num-outs aignet))))
              (and stable-under-simplificationp
                   '(:in-theory (enable output-eval)))))

    (defthm nxst-eval-of-aignet-prune-comb-aux
      (b* (((mv ?mark ?copy & ?aignet2)
            (aignet-prune-comb-aux
             mark copy aignet gatesimp strash aignet2)))
        (equal (nxst-eval n invals regvals aignet2)
               (nxst-eval n invals regvals aignet)))
      :hints (("goal" :cases ((< (nfix n) (num-regs aignet))))
              (and stable-under-simplificationp
                   '(:in-theory (enable nxst-eval)))))



    (defthm stype-counts-of-aignet-prune-comb-aux
      (b* (((mv ?mark ?copy & ?aignet2)
            (aignet-prune-comb-aux
             mark copy aignet gatesimp strash aignet2)))
        (implies (member stype (list (po-stype)
                                     (pi-stype)
                                     (reg-stype)))
                 (equal (stype-count stype aignet2)
                        (stype-count stype aignet))))
      :hints ((and stable-under-simplificationp
                   '(:in-theory (enable aignet-copy-dfs-setup)))))

    (defthm comb-equiv-of-aignet-prune-comb-aux
      (b* (((mv ?mark ?copy & ?aignet2)
            (aignet-prune-comb-aux
             mark copy aignet gatesimp strash aignet2)))
        (comb-equiv aignet2 aignet))
      :hints(("Goal" :in-theory (e/d (comb-equiv
                                      outs-comb-equiv
                                      nxsts-comb-equiv)
                                     (aignet-prune-comb-aux))))))


  (define aignet-prune-comb (aignet aignet2 (gatesimp gatesimp-p))
    (b* (((local-stobjs mark copy strash)
          (mv mark copy strash aignet2)))
      (aignet-prune-comb-aux mark copy aignet gatesimp strash aignet2))

    ///
    (defthm normalize-inputs-of-aignet-prune-comb
      (implies (syntaxp (not (equal aignet2 ''nil)))
               (equal (aignet-prune-comb aignet aignet2 gatesimp)
                      (aignet-prune-comb aignet nil gatesimp))))

    (defthm output-eval-of-aignet-prune-comb
      (b* ((aignet2
            (aignet-prune-comb aignet aignet2 gatesimp)))
        (equal (output-eval n invals regvals aignet2)
               (output-eval n invals regvals aignet))))

    (defthm nxst-eval-of-aignet-prune-comb
      (b* ((aignet2
            (aignet-prune-comb aignet aignet2 gatesimp)))
        (equal (nxst-eval n invals regvals aignet2)
               (nxst-eval n invals regvals aignet))))

    

    (defthm stype-counts-of-aignet-prune-comb
      (implies (member stype (list (po-stype)
                                   (pi-stype)
                                   (reg-stype)))
               (equal (stype-count stype (aignet-prune-comb
                                          aignet aignet2 gatesimp))
                      (stype-count stype aignet))))

    (defthm comb-equiv-of-aignet-prune-comb
      (comb-equiv (aignet-prune-comb aignet aignet2 gatesimp)
                  aignet))))






(defsection aignet-mark-dfs-seq-rec
  (local (in-theory (disable lookup-id-in-bounds-when-positive
                             lookup-id-out-of-bounds
                             default-car
                             fanin-count-of-lookup-id-when-consp
                             acl2::nth-when-zp
                             acl2::zp-when-integerp)))

  (defund aignet-mark-dfs-seq-rec (id mark aignet)
    (declare (type (integer 0 *) id)
             (xargs :stobjs (mark aignet)
                    :guard (and (<= (num-fanins aignet) (bits-length mark))
                                (id-existsp id aignet))
                    :verify-guards nil
                    :measure (aignet-mark-measure mark aignet)))
    (b* (((when (mbe :logic
                     (or (not (id-existsp id aignet))
                         (int= 1 (get-bit id mark)))
                     :exec (int= 1 (get-bit id mark))))
          mark)
         (mark (set-bit id 1 mark))
         (type (id->type id aignet)))
      (aignet-case
       type (id->regp id aignet)
       :const mark
       :pi mark
       :reg (aignet-mark-dfs-seq-rec
             (lit->var (snode->fanin^ (id->slot0 id aignet)))
             mark aignet)
       :gate
       (mbe :logic
            (non-exec
             (b* ((mark1 (aignet-mark-dfs-seq-rec
                          (lit-id (gate-id->fanin0 id aignet))
                          mark aignet))
                  ((unless (<= (aignet-mark-measure mark1 aignet)
                               (aignet-mark-measure mark aignet)))
                   mark1))
               (aignet-mark-dfs-seq-rec
                (lit-id (gate-id->fanin1 id aignet))
                mark1 aignet)))
            :exec
            (b* ((mark (aignet-mark-dfs-seq-rec
                        (lit-id (gate-id->fanin0 id aignet))
                        mark aignet)))
              (aignet-mark-dfs-seq-rec
               (lit-id (gate-id->fanin1 id aignet))
               mark aignet))))))

  (local (in-theory (enable aignet-mark-dfs-seq-rec)))

  (defthm aignet-mark-dfs-seq-rec-preserves-mark
    (implies (equal 1 (nth n mark))
             (equal (nth n (aignet-mark-dfs-seq-rec id mark aignet)) 1)))

  (defthm aignet-mark-dfs-seq-rec-preserves-memo-tablep
    (<= (len mark)
        (len (aignet-mark-dfs-seq-rec id mark aignet)))
    :rule-classes :linear)

  (defthm aignet-mark-dfs-seq-rec-decreases-measure-weak
    (<= (aignet-mark-measure (aignet-mark-dfs-seq-rec id mark aignet) aignet)
        (aignet-mark-measure mark aignet))
    :rule-classes (:rewrite :linear))

  (defthm id-marked-of-aignet-mark-dfs-seq-rec
    (implies (aignet-idp id aignet)
             (equal (nth id (aignet-mark-dfs-seq-rec id mark aignet))
                    1)))

  (local (in-theory (disable len)))

  (defthm len-of-update-nth
    (<= (len x)
        (len (update-nth n v x)))
    :rule-classes :linear)

  (local (in-theory (disable ;; acl2::len-update-nth1
                             acl2::len-update-nth)))

  (verify-guards aignet-mark-dfs-seq-rec
    :guard-debug t
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable aignet-idp))))))



(defsection aignet-mark-seq-invar
  (local (in-theory (disable acl2::nth-when-zp
                             acl2::zp-when-integerp
                             acl2::zp-open
                             lookup-id-out-of-bounds)))
  ;; (defmacro gate-fanins-marked (id aignet mark)
  ;;   `(let ((look (lookup-id ,id ,aignet)))
  ;;      (and (equal (nth (lit-id
  ;;                        (aignet-lit-fix
  ;;                         (gate-node->fanin0 (car look))
  ;;                         (cdr look)))
  ;;                       ,mark)
  ;;                  1)
  ;;           (equal (nth (lit-id
  ;;                        (aignet-lit-fix
  ;;                         (gate-node->fanin1 (car look))
  ;;                         (cdr look)))
  ;;                       ,mark)
  ;;                  1))))

  ;; (defmacro co-fanin-marked (id aignet mark)
  ;;   `(let ((look (lookup-id ,id ,aignet)))
  ;;      (equal (nth (lit-id
  ;;                   (aignet-lit-fix
  ;;                    (co-node->fanin (car look))
  ;;                    (cdr look)))
  ;;                  ,mark)
  ;;             1)))

  (defmacro reg-nxst-marked (id aignet mark)
    `(let* ((nxst (lit->var
                    (lookup-reg->nxst
                     (stype-count :reg (cdr (lookup-id ,id ,aignet))) ,aignet))))
       (equal (nth nxst ,mark) 1)))


  ;; The non-inductive, nicer invariant:
  ;;  -- For all nodes that are marked, their fanins are also marked.
  (defun-sk aignet-mark-seq-invar (mark aignet)
    (forall id
            (implies
             (and (equal 1 (get-bit id mark)))
             (and (implies (equal (id->type id aignet) (gate-type))
                           (gate-fanins-marked id aignet mark))
                  (implies (equal (stype (car (lookup-id id aignet)))
                                  (reg-stype))
                           (reg-nxst-marked id aignet mark)))))
    :rewrite :direct)

  (in-theory (disable aignet-mark-seq-invar))


  (defthm aignet-mark-seq-invar-implies-reg
    (implies (and (aignet-mark-seq-invar mark aignet)
                  (< (nfix n) (stype-count :reg aignet))
                  (equal 1 (nth (fanin-count (lookup-stype n :reg aignet)) mark)))
             (equal (nth (lit->var (lookup-reg->nxst n aignet)) mark) 1))
    :hints (("goal" :use ((:instance aignet-mark-seq-invar-necc
                           (id (fanin-count (lookup-stype n :reg aignet)))))
             :in-theory (disable aignet-mark-seq-invar-necc))))

  (defthm aignet-mark-seq-invar-implies-aignet-mark-comb-invar
    (implies (aignet-mark-seq-invar mark aignet)
             (aignet-mark-comb-invar mark aignet))
    :hints (("goal" :expand ((aignet-mark-comb-invar mark aignet)))))



;;  (local
   (defsection aignet-mark-seq-invar-inductive

     ;; The inductive invariant:
     ;; -- All nodes marked in the original are marked in the result
     ;; -- For all nodes marked in the result that were not
     ;;    marked in the original, their fanins are also marked
     ;;    in the result.
     (defun-sk aignet-mark-seq-invar1 (mark1 mark2 aignet)
       (forall
        id
        (and
         (implies
          (and (not (equal 1 (get-bit id mark1)))
               (equal 1 (get-bit id mark2)))
          (and (implies (equal (id->type id aignet) (gate-type))
                        (gate-fanins-marked id aignet mark2))
               (implies (equal (stype (car (lookup-id id aignet)))
                               (reg-stype))
                        (reg-nxst-marked id aignet mark2))))
         (implies (and (equal 1 (get-bit id mark1)))
                  (equal (nth id mark2) 1))))
       :rewrite :direct)

     (in-theory (disable aignet-mark-seq-invar1
                         aignet-mark-seq-invar1-necc))

     (local (in-theory (enable aignet-mark-seq-invar1-necc)))

     (defthmd aignet-mark-seq-invar1-mark-preserved
       (implies (and (aignet-mark-seq-invar1 mark1 mark2 aignet)
                     (equal 1 (get-bit id mark1)))
                (equal (nth id mark2) 1)))

     (local (in-theory (enable aignet-mark-seq-invar1-mark-preserved)))


     (defthmd aignet-mark-seq-invar1-transitive-lemma
       (implies (and (aignet-mark-seq-invar1 mark2 mark3 aignet)
                     (aignet-mark-seq-invar1 mark1 mark2 aignet))
                (and
                 (implies
                  (and (not (equal 1 (get-bit id mark1)))
                       (equal 1 (get-bit id mark3)))
                  (and (implies (equal (id->type id aignet) (gate-type))
                                (gate-fanins-marked id aignet mark3))
                       (implies (equal (stype (car (lookup-id id aignet)))
                                       (reg-stype))
                                (reg-nxst-marked id aignet mark3))))
                 (implies (equal 1 (get-bit id mark1))
                          (equal (nth id mark3) 1))))
       :hints (("goal" :in-theory (disable aignet-mark-seq-invar1-necc)
                :use ((:instance aignet-mark-seq-invar1-necc)
                      (:instance aignet-mark-seq-invar1-necc
                       (mark1 mark2) (mark2 mark3))))))

     (defthm aignet-mark-seq-invar1-transitive
       (implies (and (aignet-mark-seq-invar1 mark1 mark2 aignet)
                     (aignet-mark-seq-invar1 mark2 mark3 aignet))
                (aignet-mark-seq-invar1 mark1 mark3 aignet))
       :hints (("goal" :in-theory (enable
                                   aignet-mark-seq-invar1-transitive-lemma)
                :expand ((aignet-mark-seq-invar1 mark1 mark3 aignet)))))


     (defthmd aignet-mark-seq-invar-special-gate-lemma
       (implies (and (aignet-mark-seq-invar1
                      (update-nth id1 1 mark1)
                      mark2 aignet)
                     (equal (id->type id1 aignet) (gate-type))
                     (gate-fanins-marked id1 aignet mark2))
                (and
                 (implies
                  (and (not (equal 1 (get-bit id mark1)))
                       (equal 1 (get-bit id mark2)))
                  (and (implies (equal (id->type id aignet) (gate-type))
                                (gate-fanins-marked id aignet mark2))
                       (implies (equal (stype (car (lookup-id id aignet)))
                                       (reg-stype))
                                (reg-nxst-marked id aignet mark2))))
                 (implies (and ;; (aignet-idp id aignet)
                               (equal 1 (get-bit id mark1)))
                          (equal (nth id mark2) 1))))
       :hints (("goal"
                :in-theory (disable aignet-mark-seq-invar1-necc)
                :use
                ((:instance aignet-mark-seq-invar1-necc
                  (mark1 (update-nth id1 1 mark1)))))))


     (defthm aignet-mark-seq-invar-special-gate
       (implies (and (bind-free '((id1 . id)) (id1))
                     (aignet-mark-seq-invar1
                      (update-nth id1 1 mark1)
                      mark2 aignet)
                     (equal (id->type id1 aignet) (gate-type))
                     (gate-fanins-marked id1 aignet mark2))
                (aignet-mark-seq-invar1 mark1 mark2 aignet))
       :hints (("goal"
                :expand ((aignet-mark-seq-invar1 mark1 mark2 aignet))
                :in-theory (enable aignet-mark-seq-invar-special-gate-lemma)))
       :rule-classes ((:rewrite :backchain-limit-lst (nil 1 nil nil))))

     (defthmd aignet-mark-seq-invar-special-reg-lemma
       (implies (and (aignet-mark-seq-invar1
                      (update-nth id1 1 mark1)
                      mark2 aignet)
                     (equal (stype (car (lookup-id id1 aignet)))
                            (reg-stype))
                     (reg-nxst-marked id1 aignet mark2))
                (and
                 (implies
                  (and (not (equal 1 (get-bit id mark1)))
                       (equal 1 (get-bit id mark2)))
                  (and (implies (equal (id->type id aignet) (gate-type))
                                (gate-fanins-marked id aignet mark2))
                       (implies (equal (stype (car (lookup-id id aignet)))
                                       (reg-stype))
                                (reg-nxst-marked id aignet mark2))))
                 (implies (and ;; (aignet-idp id aignet)
                               (equal 1 (get-bit id mark1)))
                          (equal (nth id mark2) 1))))
       :hints (("goal"
                :in-theory (disable aignet-mark-seq-invar1-necc)
                :use
                ((:instance aignet-mark-seq-invar1-necc
                  (mark1 (update-nth id1 1 mark1)))))))


     (defthm aignet-mark-seq-invar-special-reg
       (implies (and (bind-free '((id1 . id)) (id1))
                     (aignet-mark-seq-invar1
                      (update-nth id1 1 mark1)
                      mark2 aignet)
                     (equal (stype (car (lookup-id id1 aignet)))
                            (reg-stype))
                     (reg-nxst-marked id1 aignet mark2))
                (aignet-mark-seq-invar1 mark1 mark2 aignet))
       :hints (("goal"
                :expand ((aignet-mark-seq-invar1 mark1 mark2 aignet))
                :in-theory (enable aignet-mark-seq-invar-special-reg-lemma)))
       :rule-classes ((:rewrite :backchain-limit-lst (nil 1 nil nil))))

     (defthm aignet-mark-seq-invar1-self
       (aignet-mark-seq-invar1 mark mark aignet)
       :hints (("goal" :in-theory (enable aignet-mark-seq-invar1))))

     (defthm aignet-mark-seq-invar1-mark-non-gate/co/reg
       (implies (and (not (equal (id->type id aignet) (gate-type)))
                     (not (equal (stype (car (lookup-id id aignet))) (reg-stype))))
                (aignet-mark-seq-invar1 mark (update-nth id 1 mark) aignet))
       :hints (("goal" :in-theory (enable aignet-mark-seq-invar1))))

     (defthm aignet-mark-seq-invar1-mark-const
       (implies (equal (id->type id aignet) (const-type))
                (aignet-mark-seq-invar1 mark (update-nth id 1 mark) aignet))
       :hints (("goal" :in-theory (enable aignet-mark-seq-invar1))))

     (local (defthm stype-possibilities-comb
              (implies (and (not (equal (ctype (stype x)) (gate-ctype)))
                            (not (equal (ctype (stype x)) (in-ctype)))
                            (not (equal (ctype (stype x)) (out-ctype))))
                       (equal (stype x) (const-stype)))
              :hints(("Goal" :in-theory (enable stype stype-fix stypep)))))


     (defthm aignet-mark-seq-invar1-of-aignet-mark-dfs-seq-rec
       (aignet-mark-seq-invar1
        mark
        (aignet-mark-dfs-seq-rec id mark aignet)
        aignet)
       :hints (("goal" :induct (aignet-mark-dfs-seq-rec id mark aignet)
                :in-theory (enable (:induction aignet-mark-dfs-seq-rec))
                :expand ((aignet-mark-dfs-seq-rec id mark aignet)))
               (and stable-under-simplificationp
                    '(:cases ((equal (id->type id aignet) 1))))))


     (defthmd aignet-mark-seq-invar-by-aignet-mark-seq-invar1-lemma
       (implies (and (aignet-mark-seq-invar mark1 aignet)
                     (aignet-mark-seq-invar1 mark1 mark2 aignet))
                (implies
                 (and (equal 1 (get-bit id mark2)))
                 (and (implies (equal (id->type id aignet) (gate-type))
                               (gate-fanins-marked id aignet mark2))
                      (implies (equal (stype (car (lookup-id id aignet)))
                                      (reg-stype))
                               (reg-nxst-marked id aignet mark2)))))
       :hints (("goal" :use ((:instance aignet-mark-seq-invar-necc
                              (mark mark1))
                             (:instance aignet-mark-seq-invar1-necc))
                :in-theory (disable aignet-mark-seq-invar1-necc
                                    aignet-mark-seq-invar-necc))))

     (defthm aignet-mark-seq-invar-by-aignet-mark-seq-invar1
       (implies (and (aignet-mark-seq-invar mark1 aignet)
                     (aignet-mark-seq-invar1 mark1 mark2 aignet))
                (aignet-mark-seq-invar mark2 aignet))
       :hints (("goal" :expand ((aignet-mark-seq-invar mark2 aignet))
                :in-theory
                (enable
                 aignet-mark-seq-invar-by-aignet-mark-seq-invar1-lemma)))))

  (local (defthm bit-equiv-of-equal-1
           (implies (and (bit-equiv x (double-rewrite y))
                         (syntaxp (not (equal x y))))
                    (equal (equal 1 y)
                           (equal 1 x)))))

  (defcong bits-equiv equal (aignet-mark-seq-invar mark aignet) 1
    :hints(("goal" :cases ((aignet-mark-seq-invar mark aignet)))
           (and stable-under-simplificationp
                (let* ((term (assoc 'aignet-mark-seq-invar clause))
                       (other-var (if (eq (cadr term) 'mark)
                                      'mark-equiv
                                    'mark)))
                  `(:expand (,term)
                    :use ((:instance aignet-mark-seq-invar-necc
                           (mark ,other-var)
                           (id ,(cons 'aignet-mark-seq-invar-witness
                                      (cdr term))))))))))

  (defthm aignet-mark-seq-invar-of-empty
    (aignet-mark-seq-invar nil aignet)
    :hints(("Goal" :in-theory (enable aignet-mark-seq-invar))))


  (defthm aignet-mark-seq-invar-preserved-by-aignet-mark-dfs-seq-rec
    (implies (aignet-mark-seq-invar mark aignet)
             (aignet-mark-seq-invar
              (aignet-mark-dfs-seq-rec id mark aignet)
              aignet)))

  (defthm aignet-mark-seq-invar-of-aignet-copy-dfs-setup
    (aignet-mark-seq-invar
     (mv-nth 0 (aignet-copy-dfs-setup aignet mark copy aignet2))
     aignet)
    :hints(("Goal" :in-theory (enable aignet-mark-seq-invar
                                      aignet-copy-dfs-setup)))))


(defsection aignet-mark-dfs-seq
  (defiteration aignet-mark-dfs-seq (mark aignet)
    (declare (xargs :stobjs (mark aignet)
                    :guard (and (<= (num-fanins aignet) (bits-length mark)))))
    (aignet-mark-dfs-seq-rec (lit->var (outnum->fanin n aignet)) mark aignet)
    :returns mark
    :index n
    :last (num-outs aignet))

  (in-theory (disable aignet-mark-dfs-seq))
  (local (in-theory (enable aignet-mark-dfs-seq)))

  (defthm outputs-marked-of-aignet-mark-dfs-seq-iter
    (implies (and (< (nfix n) (nfix m))
                  (<= (nfix m) (stype-count (po-stype) aignet)))
             (equal (nth (lit->var (fanin :co (lookup-stype n (po-stype) aignet)))
                         (aignet-mark-dfs-seq-iter m mark aignet))
                    1))
    :hints((acl2::just-induct-and-expand
            (aignet-mark-dfs-seq-iter m mark aignet))))

  (defthm aignet-mark-seq-invar-preserved-by-aignet-mark-dfs-seq-iter
    (implies (and (aignet-mark-seq-invar mark aignet))
             (aignet-mark-seq-invar
              (aignet-mark-dfs-seq-iter m mark aignet)
              aignet))
    :hints((acl2::just-induct-and-expand
            (aignet-mark-dfs-seq-iter m mark aignet))))

  (defthm aignet-mark-dfs-seq-iter-preserves-mark
    (implies (equal 1 (nth n mark))
             (equal (nth n (aignet-mark-dfs-seq-iter m mark aignet)) 1))
    :hints ((acl2::just-induct-and-expand
             (aignet-mark-dfs-seq-iter m mark aignet))))

  (defthm aignet-mark-dfs-seq-iter-preserves-memo-tablep
    (<= (len mark)
        (len (aignet-mark-dfs-seq-iter m mark aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet-mark-dfs-seq-iter m mark aignet)))
    :rule-classes :linear)

  (defthm outputs-marked-of-aignet-mark-dfs-seq
    (implies (and (< (nfix n) (stype-count (po-stype) aignet)))
             (equal (nth (lit->var (fanin :co (lookup-stype n (po-stype) aignet)))
                         (aignet-mark-dfs-seq mark aignet))
                    1)))

  (defthm aignet-mark-seq-invar-preserved-by-aignet-mark-dfs-seq
    (implies (and (aignet-mark-seq-invar mark aignet))
             (aignet-mark-seq-invar
              (aignet-mark-dfs-seq mark aignet)
              aignet)))

  (defthm aignet-mark-dfs-seq-preserves-mark
    (implies (equal 1 (nth n mark))
             (equal (nth n (aignet-mark-dfs-seq mark aignet)) 1)))

  (defthm aignet-mark-dfs-seq-preserves-memo-tablep
    (<= (len mark)
        (len (aignet-mark-dfs-seq mark aignet)))
    :rule-classes :linear))





(defsection input-copy-values

  (defthm len-of-input-copy-values
    (equal (len (input-copy-values n invals regvals aignet copy aignet2))
           (nfix (- (num-ins aignet) (nfix n))))
    :hints(("Goal" :in-theory (enable input-copy-values))))

  (local (set-default-hints
          '((and stable-under-simplificationp
                 (acl2::equal-by-nths-hint)))))

  ;; (defthm input-copy-values-of-update-non-pi
  ;;   (implies (not (equal (stype (car (lookup-id id aignet))) :pi))
  ;;            (equal (input-copy-values
  ;;                    invals regvals aignet2
  ;;                    (update-nth-lit id lit copy) aignet)
  ;;                   (input-copy-values
  ;;                    invals regvals aignet2
  ;;                    copy aignet))))

  (defthm input-copy-values-after-copy-marked-iter
    (b* (((mv aignet-copy2 & aignet22)
          (aignet-copy-marked-iter m aignet mark copy gatesimp strash aignet2)))
      (implies (aignet-copies-in-bounds copy aignet2)
               (equal (input-copy-values
                       n aignet-invals aignet-regvals aignet aignet-copy2
                       aignet22)
                      (input-copy-values
                       n aignet-invals aignet-regvals aignet copy
                       aignet2))))
    :hints(("Goal" :in-theory (e/d () (aignet-copy-marked-iter)))))

  (defthm input-copy-values-after-copy-marked-copy
    (b* (((mv aignet-copy2 & aignet22)
          (aignet-copy-marked aignet mark copy gatesimp strash aignet2)))
      (implies (aignet-copies-in-bounds copy aignet2)
               (equal (input-copy-values
                       n aignet-invals aignet-regvals aignet aignet-copy2
                       aignet22)
                      (input-copy-values
                       n aignet-invals aignet-regvals aignet copy
                       aignet2))))
    :hints(("Goal" :in-theory (e/d (aignet-copy-marked) (aignet-copy-marked-iter))))))



(defsection reg-copy-values

  (defthm len-of-reg-copy-values
    (equal (len (reg-copy-values n invals regvals aignet copy aignet2))
           (nfix (- (num-regs aignet) (nfix n))))
    :hints(("Goal" :in-theory (enable reg-copy-values))))

  (local (set-default-hints
          '((and stable-under-simplificationp
                 (acl2::equal-by-nths-hint)))))

  ;; (defthm reg-copy-values-of-update-non-reg
  ;;   (implies (not (equal (stype (car (lookup-id id aignet))) :reg))
  ;;            (equal (reg-copy-values
  ;;                         invals regvals aignet2
  ;;                         (update-nth-lit id lit copy) aignet)
  ;;                        (reg-copy-values
  ;;                         invals regvals aignet2
  ;;                         copy aignet))))

  (defthm reg-copy-values-after-copy-marked-iter
    (b* (((mv aignet-copy2 & aignet22)
          (aignet-copy-marked-iter n aignet mark copy gatesimp strash aignet2)))
      (implies (aignet-copies-in-bounds copy aignet2)
               (equal
                (reg-copy-values
                 m aignet-invals aignet-regvals aignet aignet-copy2 aignet22)
                (reg-copy-values
                 m aignet-invals aignet-regvals aignet copy aignet2))))
    :hints(("Goal" :in-theory (e/d ()
                                   (aignet-copy-marked-iter)))))

  (defthm reg-copy-values-after-copy-marked-copy
    (b* (((mv aignet-copy2 & aignet22)
          (aignet-copy-marked aignet mark copy gatesimp strash aignet2)))
      (implies (aignet-copies-in-bounds copy aignet2)
               (equal
                (reg-copy-values
                 n aignet-invals aignet-regvals aignet aignet-copy2 aignet22)
                (reg-copy-values
                 n aignet-invals aignet-regvals aignet copy aignet2))))
    :hints(("Goal" :in-theory (e/d (aignet-copy-marked)
                                   (aignet-copy-marked-iter))))))


(defsection aignet-copy-marked-gen-invar
  (local (in-theory (disable lookup-id-in-bounds-when-positive
                             default-car
                             ;; fanin-if-co-id-lte-max-fanin
                             lookup-id-out-of-bounds
                             fanin-count-of-atom
                             nth-copy-preserved-by-aignet-copy-marked-iter)))
                             
  (defun-sk aignet-copy-marked-gen-invar (n aignet mark copy aignet2)
    (forall (id invals regvals)
            (implies (and (equal (nth id mark) 1)
                          (< (nfix id) (nfix n)))
                     (equal (lit-eval (nth-lit id copy) invals regvals aignet2)
                            (id-eval id
                                     (input-copy-values
                                      0 invals regvals aignet copy aignet2)
                                     (reg-copy-values
                                      0 invals regvals aignet copy aignet2)
                                     aignet))))
    :rewrite :direct)

  (in-theory (disable aignet-copy-marked-gen-invar))


  (defthm aignet-copy-marked-gen-invar-necc-lit-copy
    (implies (and (aignet-copy-marked-gen-invar n aignet mark copy aignet2)
                  (equal (nth (lit->var lit) mark) 1)
                  (< (lit->var lit) (nfix n)))
             (equal (lit-eval (lit-copy lit copy) invals regvals aignet2)
                    (lit-eval lit
                             (input-copy-values
                              0 invals regvals aignet copy aignet2)
                             (reg-copy-values
                              0 invals regvals aignet copy aignet2)
                             aignet)))
    :hints(("Goal" :in-theory (enable lit-copy)
            :expand ((:free (invals regvals) (lit-eval lit invals regvals aignet))))))


  ; (local (in-theory (enable aignet-idp)))

  ;; (local (defthm decr-less-lemma
  ;;          (implies (<= n m)
  ;;                   (<= (+ -1 n) m))))

  (local (defthm aignet-copy-marked-gen-invar-special
           (b* (((mv copy1 & aignet21)
                 (aignet-copy-marked-iter
                  n aignet mark copy strash gatesimp aignet2)))
             (implies (and
                       (aignet-copy-marked-gen-invar
                        n aignet mark copy1 aignet21)
                       (aignet-copies-in-bounds copy aignet2)
                       (equal (nth id mark) 1)
                       (< (nfix id) (nfix n)))
                      (equal (lit-eval (nth-lit id copy1) invals regvals aignet21)
                             (id-eval id
                                      (input-copy-values
                                       0 invals regvals aignet copy aignet2)
                                      (reg-copy-values
                                       0 invals regvals aignet copy aignet2)
                                      aignet))))
           :hints (("goal" :use ((:instance aignet-copy-marked-gen-invar-necc
                                  (copy (mv-nth 0 (aignet-copy-marked-iter
                                                   n aignet mark copy strash
                                                   gatesimp aignet2)))
                                  (aignet2 (mv-nth 2 (aignet-copy-marked-iter
                                                      n aignet mark copy strash
                                                      gatesimp aignet2)))))
                    :in-theory (disable aignet-copy-marked-gen-invar-necc)))))

  ;; (defthm greater-than-n-copy-preserved-by-aignet-copy-marked-iter
  ;;   (implies (<= (nfix n) (nfix idn))
  ;;            (b* (((mv copy1 & &)
  ;;                  (aignet-copy-marked-iter
  ;;                   n aignet
  ;;                   mark copy strash gatesimp aignet2)))
  ;;              (equal (nth-lit idn copy1)
  ;;                     (nth-lit idn copy)))))

  ;; (local (in-theory (disable nth-copy-preserved-by-aignet-copy-marked-iter)))

  (local (in-theory (disable aignet-copy-marked-gen-invar-necc)))

  (defthm aignet-copy-marked-gen-invar-of-aignet-copy-marked-iter
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (aignet-mark-comb-invar mark aignet)
                  (<= (nfix n) (num-fanins aignet)))
             (b* (((mv copy1 & aignet21)
                   (aignet-copy-marked-iter
                    n aignet mark copy strash gatesimp aignet2)))
               (aignet-copy-marked-gen-invar
                n aignet mark copy1 aignet21)))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-marked-iter
             n aignet mark copy strash gatesimp aignet2))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause)))))
           (and stable-under-simplificationp
                (let ((witness (acl2::find-call-lst
                                'aignet-copy-marked-gen-invar-witness
                                clause)))
                  `(:clause-processor
                    (acl2::simple-generalize-cp
                     clause '(((mv-nth '0 ,witness) . id)
                              ((mv-nth '1 ,witness) . invals)
                              ((mv-nth '2 ,witness) . regvals)
                              ;; ((mv-nth '3 ,witness) . ins1)
                              ;; ((mv-nth '4 ,witness) . regs1)
                              )))))
           (and stable-under-simplificationp
                '(:cases ((< (nfix id) (+ -1 n)))))
           (and stable-under-simplificationp
                '(:expand ((:free (invals regvals)
                            (id-eval (+ -1 n) invals regvals aignet))
                           (:free (invals regvals)
                            (id-eval id invals regvals aignet)))
                  :in-theory (enable lit-eval eval-and-of-lits eval-xor-of-lits
                                     aignet-idp)))
           (and stable-under-simplificationp
                '(:in-theory (enable nth-copy-preserved-by-aignet-copy-marked-iter)))))


  (defthm aignet-copy-marked-gen-invar-of-aignet-copy-marked
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (aignet-mark-comb-invar mark aignet))
             (b* (((mv copy1 & aignet21)
                   (aignet-copy-marked
                    aignet mark copy strash gatesimp aignet2)))
               (aignet-copy-marked-gen-invar
                (+ 1 (fanin-count aignet)) aignet mark copy1 aignet21)))
    :hints(("Goal" :in-theory (enable aignet-copy-marked))))

  (defthm aignet-copy-marked-rewrite
    (b* (((mv copy1 & aignet21)
          (aignet-copy-marked
           aignet mark copy strash gatesimp aignet2)))
      (implies (and
                (aignet-copies-in-bounds copy aignet2)
                (aignet-mark-comb-invar mark aignet)
                (aignet-idp id aignet)
                (equal (nth id mark) 1))
               (equal (lit-eval (nth-lit id copy1) invals regvals aignet21)
                      (id-eval id
                               (input-copy-values
                                0 invals regvals aignet copy aignet2)
                               (reg-copy-values
                                0 invals regvals aignet copy aignet2)
                               aignet))))
    :hints (("goal" :use ((:instance aignet-copy-marked-gen-invar-necc
                           (copy (mv-nth 0 (aignet-copy-marked
                                            aignet mark copy strash gatesimp
                                            aignet2)))
                           (aignet2 (mv-nth 2 (aignet-copy-marked
                                            aignet mark copy strash gatesimp
                                            aignet2)))
                           (n (num-fanins aignet))))
             :in-theory (e/d (aignet-idp)
                             (aignet-copy-marked-gen-invar-necc))))))



(define marked-reg-count ((n :type (integer 0 *))
                           mark aignet)
  :guard (and (<= n (num-regs aignet))
              (<= (num-fanins aignet) (bits-length mark)))
  (b* (((when (zp n)) 0)
       (n (1- n))
       (reg (regnum->id n aignet)))
    (+ (get-bit reg mark)
       (marked-reg-count n mark aignet)))
  ///
  (defcong nat-equiv equal (marked-reg-count n mark aignet) 1)
  (defcong bits-equiv equal (marked-reg-count n mark aignet) 2)

  (defthm marked-reg-count-monotonic
    (implies (<= (nfix n) (nfix m))
             (<= (marked-reg-count n mark aignet)
                 (marked-reg-count m mark aignet))))

  (defthm marked-reg-count-monotonic-strong
    (implies (and (< (nfix n) (nfix m))
                  (equal 1 (nth (fanin-count (lookup-stype n :reg aignet)) mark)))
             (< (marked-reg-count n mark aignet)
                (marked-reg-count m mark aignet)))
    :hints (("goal" :use ((:instance marked-reg-count-monotonic
                           (n (+ 1 (nfix n)))))
             :expand ((marked-reg-count (+ 1 (nfix n)) mark aignet))
             :in-theory (e/d () (marked-reg-count-monotonic))))
    :rule-classes (:rewrite :linear))

  (defthm marked-reg-count-max
    (implies (<= (nfix n) (stype-count :reg aignet))
             (<= (marked-reg-count n mark aignet)
                 (marked-reg-count (stype-count :reg aignet) mark aignet)))
    :rule-classes :linear)

  (defthm marked-reg-count-max-strong
    (implies (and (< (nfix n) (stype-count :reg aignet))
                  (equal 1 (nth (fanin-count (lookup-stype n :reg aignet)) mark)))
             (< (marked-reg-count n mark aignet)
                (marked-reg-count (stype-count :reg aignet) mark aignet)))
    :hints (("goal" :use ((:instance marked-reg-count-monotonic-strong
                           (m (stype-count :reg aignet))))))
    :rule-classes :linear)

  (defthm marked-reg-count-unique
    (implies (and (equal (nth (regnum->id n aignet) mark) 1)
                  (equal (nth (regnum->id m aignet) mark) 1))
             (equal (equal (marked-reg-count n mark aignet)
                           (marked-reg-count m mark aignet))
                    (equal (nfix n) (nfix m))))
    :hints (("goal" :use ((:instance marked-reg-count-monotonic-strong)
                          (:instance marked-reg-count-monotonic-strong
                           (n m) (m n))))))

  (defthm marked-reg-count-0
    (equal (marked-reg-count 0 mark aignet) 0)))

(define lookup-marked-reg-aux ((n :type (integer 0 *))
                               (m :type (integer 0 *))
                               (count :type (integer 0 *))
                               mark aignet)
  (declare (xargs :guard (and (<= m (num-regs aignet))
                              (<= (num-fanins aignet) (bits-length mark)))
                  :measure (nfix (- (num-regs aignet) (nfix m)))))
  (b* (((when (mbe :logic (zp (- (num-regs aignet) (nfix m)))
                   :exec (int= (num-regs aignet) m)))
        0)
       (reg-id (regnum->id m aignet))
       (markval (get-bit reg-id mark))
       ((when (and (int= (lnfix n) (lnfix count))
                   (int= markval 1)))
        reg-id)
       (count (+ markval (lnfix count))))
    (lookup-marked-reg-aux n (+ 1 (lnfix m)) count mark aignet))

  ///

  (defcong nat-equiv equal (lookup-marked-reg-aux n m count mark aignet) 1)

  (local (defthm consp-lookup-stype
           (iff (consp (lookup-stype m stype aignet))
                (< (nfix m) (stype-count stype aignet)))
           :hints(("Goal" :in-theory (enable lookup-stype)))))

  (defthm marked-reg-count-of-lookup-marked-reg-aux
    (implies (and (< (nfix n) (marked-reg-count (num-regs aignet) mark aignet))
                  (<= (nfix m) (num-regs aignet))
                  (equal (nfix count) (marked-reg-count m mark aignet))
                  (<= (nfix count) (nfix n)))
             (let* ((id (lookup-marked-reg-aux n m count mark aignet))
                    (look (lookup-id id aignet)))
               (and (consp look)
                    (equal (stype (car look)) :reg)
                    (equal (nth id mark) 1)
                    (equal (marked-reg-count (stype-count :reg (cdr look)) mark
                                             aignet)
                           (nfix n)))))
    :hints(("Goal" :in-theory (enable marked-reg-count)
            :induct (lookup-marked-reg-aux n m count mark aignet))
           (and stable-under-simplificationp
                '(:use ((:instance marked-reg-count-monotonic
                         (n m) (m (num-regs aignet))))
                  :in-theory (disable marked-reg-count-monotonic)))))

  (defthm lookup-marked-reg-aux-out-of-bounds
    (implies (and (>= (nfix n) (marked-reg-count (num-regs aignet) mark aignet))
                  (<= (nfix m) (num-regs aignet))
                  (equal (nfix count) (marked-reg-count m mark aignet)))
             (equal (lookup-marked-reg-aux n m count mark aignet)
                    0))
    :hints(("Goal" :in-theory (enable marked-reg-count)
            :induct (lookup-marked-reg-aux n m count mark aignet))))

  (defthm lookup-marked-reg-aux-of-marked-reg-count
    (implies (and (<= (nfix n) (num-regs aignet))
                  (equal (nth (fanin-count (lookup-stype n :reg aignet))
                              mark)
                         1)
                  (<= (nfix m) (nfix n))
                  (equal (nfix count)
                         (marked-reg-count m mark aignet)))
             (equal (lookup-marked-reg-aux
                     (marked-reg-count n mark aignet)
                     m count mark aignet)
                    (fanin-count (lookup-stype n :reg aignet))))
    :hints((acl2::just-induct-and-expand
            (lookup-marked-reg-aux
                     (marked-reg-count n mark aignet)
                     m count mark aignet))
           (and stable-under-simplificationp
                '(:expand ((marked-reg-count
                            (+ 1 (nfix m)) mark aignet)))))))


(define lookup-marked-reg ((n :type (integer 0 *))
                           mark aignet)
  :guard (<= (num-fanins aignet) (bits-length mark))
  :non-executable t
  (lookup-id (lookup-marked-reg-aux
              n 0 0 mark aignet)
             aignet)
  ///

  (defcong nat-equiv equal (lookup-marked-reg n mark aignet) 1)

  (defthm lookup-marked-reg-consp
    (iff (consp (lookup-marked-reg n mark aignet))
         (< (nfix n) (marked-reg-count (num-regs aignet) mark aignet))))

  (defthm marked-reg-count-of-lookup-marked-reg
    (implies (< (nfix n) (marked-reg-count (num-regs aignet) mark aignet))
             (let ((look (lookup-marked-reg n mark aignet)))
               (and (equal (stype (car look)) :reg)
                    (equal (nth (fanin-count look) mark) 1)
                    (equal (marked-reg-count
                            (stype-count :reg (cdr look))
                            mark aignet)
                           (nfix n))))))

  (defthm lookup-marked-reg-of-marked-reg-count
    (implies (and (bind-free
                   (match-equiv-or-refinement
                    'acl2::nat-equiv$inline 'm '(marked-reg-count n mark aignet)
                    mfc state))
                  (nat-equiv m (marked-reg-count n mark aignet))
                  (< (nfix n) (num-regs aignet))
                  (equal (nth (fanin-count (lookup-stype n :reg aignet))
                              mark)
                         1))
             (equal (lookup-marked-reg m mark aignet)
                    (lookup-stype n :reg aignet)))
    :hints(("Goal" :in-theory (disable nat-equiv)))))



(defsection aignet-copy-marked-regs

  ;; Adds a aignet2 reg for every reg of aignet, and sets the copy
  (defiteration aignet-copy-marked-regs (aignet mark copy aignet2)
    (declare (xargs :stobjs (aignet mark copy aignet2)
                    :guard (and (<= (num-fanins aignet) (lits-length copy))
                                (<= (num-fanins aignet) (bits-length mark)))))
    (b* ((ro (regnum->id n aignet))
         ((unless (int= (get-bit ro mark) 1))
          (mv copy aignet2))
         (reglit (mk-lit (num-fanins aignet2) 0))
         (aignet2 (aignet-add-reg aignet2))
         (copy (set-lit ro reglit copy)))
      (mv copy aignet2))
    :returns (mv copy aignet2)
    :last (num-regs aignet)
    :index n
    :package aignet::bla)


  (in-theory (disable aignet-copy-marked-regs))
  (local (in-theory (enable (:induction aignet-copy-marked-regs-iter)
                            aignet-copy-marked-regs)))

  (def-aignet-preservation-thms aignet-copy-marked-regs-iter :stobjname aignet2)

  (local (set-default-hints
          '((acl2::just-induct-and-expand
             (aignet-copy-marked-regs-iter n aignet mark copy aignet2)
             :expand-others
             ((:free (aignet) (aignet-copy-marked-regs-iter n aignet mark copy aignet2))
              (:free (copy) (aignet-copy-marked-regs-iter n aignet mark copy aignet2))
              (:free (aignet2) (aignet-copy-marked-regs-iter n aignet mark copy
                                                      aignet2))))
            '(:do-not-induct t))))

  (defthm stype-counts-preserved-of-aignet-copy-marked-regs-iter
    (implies (not (equal (stype-fix stype) (reg-stype)))
             (equal (stype-count stype (mv-nth 1 (aignet-copy-marked-regs-iter
                                                  n aignet mark copy aignet2)))
                    (stype-count stype aignet2))))

  (defthm aignet-copy-size-of-aignet-copy-marked-regs-iter
    (implies (<= (num-fanins aignet) (lits-length copy))
             (< (fanin-count aignet)
                (len (mv-nth 0 (aignet-copy-marked-regs-iter n aignet mark copy
                                                      aignet2)))))
    :rule-classes :linear)

  (defthm aignet-copies-ok-of-aignet-copy-marked-regs-iter
    (implies (aignet-copies-in-bounds copy aignet2)
             (mv-let (copy aignet2)
               (aignet-copy-marked-regs-iter n aignet mark copy aignet2)
               (aignet-copies-in-bounds
                copy aignet2))))

  (local (defthmd dumb-num-regs-lemma
           (implies (<= n (stype-count (reg-stype) aignet))
                    (< (+ -1 n) (stype-count (reg-stype) aignet)))))


  (defthm num-regs-of-aignet-copy-marked-regs-iter
    (implies (<= (nfix n) (num-regs aignet))
             (equal (stype-count (reg-stype) (mv-nth 1 (aignet-copy-marked-regs-iter
                                                        n aignet mark copy aignet2)))
                    (+ (marked-reg-count n mark aignet)
                       (stype-count (reg-stype) aignet2))))
    :hints(("Goal" :in-theory (enable marked-reg-count))))


  ;; (defthm fanin-count-of-aignet-copy-marked-regs-iter
  ;;   (implies (<= (nfix n) (num-regs aignet))
  ;;            (equal (fanin-count (mv-nth 1 (aignet-copy-marked-regs-iter
  ;;                                          n aignet mark copy aignet2)))
  ;;                   (+ (if (zp n)
  ;;                          0
  ;;                        (marked-reg-count mark (lookup-stype (1- n) (reg-stype) aignet)))
  ;;                      (fanin-count aignet2))))
  ;;   :hints(("Goal" :in-theory (enable marked-reg-count-of-lookup-stype))))

  (local (defthm <-of-minus-1
           (implies (<= n a)
                    (not (< a (+ -1 n))))))

  (local (defthm lookup-stype-of-new-node
           (implies (and (equal (nfix n) (stype-count stype aignet))
                         (equal (stype new-node) stype))
                    (equal (lookup-stype n
                                         stype
                                         (cons new-node aignet))
                           (cons (node-fix new-node)
                                 (node-list-fix aignet))))
           :hints(("Goal" :in-theory (enable lookup-stype stype-count)))))

  (defthm lookup-copy-of-aignet-copy-marked-regs-iter
    (implies (and (aignet-idp id aignet)
                  (<= (nfix n) (num-regs aignet)))
             (b* (((mv aignet-copy-new ?aignet2-new)
                   (aignet-copy-marked-regs-iter n aignet mark copy aignet2)))
               (equal (nth-lit id aignet-copy-new)
                      (if (or (not (equal (id->type id aignet) (in-type)))
                              (not (equal (id->regp id aignet) 1))
                              (not (equal (nth id mark) 1))
                              (<= (nfix n) (ci-id->ionum id aignet)))
                          (get-lit id copy)
                        (mk-lit
                         (regnum->id (+ (marked-reg-count
                                         (ci-id->ionum id aignet) mark aignet)
                                        (num-regs aignet2))
                                     aignet2-new)
                         0)))))
    :hints ((and stable-under-simplificationp
                 '(:expand ((aignet-copy-marked-regs-iter
                             0 aignet mark copy aignet2))
                   :in-theory (enable lookup-stype-in-bounds)
                   :do-not nil
                   :do-not-induct t)))
    :otf-flg t)

  (local (set-default-hints nil))

  (def-aignet-preservation-thms aignet-copy-marked-regs :stobjname aignet2)

  (defthm stype-counts-preserved-of-aignet-copy-marked-regs
    (implies (not (equal (stype-fix stype) (reg-stype)))
             (equal (stype-count stype (mv-nth 1 (aignet-copy-marked-regs
                                                  aignet mark copy aignet2)))
                    (stype-count stype aignet2))))

  (defthm aignet-copy-size-of-aignet-copy-marked-regs
    (implies (<= (num-fanins aignet) (lits-length copy))
             (< (fanin-count aignet)
                (len (mv-nth 0 (aignet-copy-marked-regs aignet mark copy
                                                 aignet2)))))
    :rule-classes :linear)

  (defthm aignet-copies-ok-of-aignet-copy-marked-regs
    (implies (aignet-copies-in-bounds copy aignet2)
             (mv-let (copy aignet2)
               (aignet-copy-marked-regs aignet mark copy aignet2)
               (aignet-copies-in-bounds
                copy aignet2))))

  (defthm num-regs-of-aignet-copy-marked-regs
    (equal (stype-count (reg-stype) (mv-nth 1 (aignet-copy-marked-regs
                                               aignet mark copy aignet2)))
           (+ (marked-reg-count (num-regs aignet) mark aignet)
              (stype-count (reg-stype) aignet2))))

  (defthm lookup-copy-of-aignet-copy-marked-regs
    (implies (aignet-idp id aignet)
             (b* (((mv aignet-copy-new ?aignet2-new)
                   (aignet-copy-marked-regs aignet mark copy aignet2)))
               (equal (nth-lit id aignet-copy-new)
                      (if (or (not (equal (id->type id aignet) (in-type)))
                              (not (equal (id->regp id aignet) 1))
                              (not (equal (nth id mark) 1)))
                          (get-lit id copy)
                        (mk-lit
                         (regnum->id (+ (marked-reg-count
                                         (ci-id->ionum id aignet) mark aignet)
                                        (num-regs aignet2))
                                     aignet2-new)
                         0))))))

  (defthm input-copy-values-of-aignet-copy-marked-regs
    (b* (((mv copy1 aignet21)
          (aignet-copy-marked-regs aignet mark copy aignet2)))
      (implies (aignet-copies-in-bounds copy aignet2)
               (bits-equiv (input-copy-values
                            0 invals regvals aignet copy1 aignet21)
                           (input-copy-values
                            0 invals regvals aignet copy aignet2))))
    :hints(("Goal" :in-theory (e/d (nth-of-input-copy-values-split)
                                   (aignet-copy-marked-regs)))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause))))))))


(defsection aignet-copy-marked-nxsts

  ;; Adds a aignet2 next state for every nextstate of aignet, and sets the copy
  (defiteration aignet-copy-marked-nxsts (aignet mark copy aignet2)
    (declare (xargs :stobjs (aignet mark copy aignet2)
                    :guard (and (<= (num-fanins aignet) (lits-length copy))
                                (<= (num-fanins aignet) (bits-length mark))
                                (<= (marked-reg-count (num-regs aignet) mark aignet)
                                    (num-regs aignet2))
                                (aignet-copies-in-bounds copy aignet2))
                    :verify-guards nil))
    (b* ((ro (regnum->id n aignet))
         (next-reg (mbe :logic (marked-reg-count n mark aignet)
                        :exec next-reg))
         ((unless (int= (get-bit ro mark) 1))
          (mv next-reg aignet2))
         (nxst (snode->fanin^ (id->slot0 ro aignet)))
         (fanin (lit-copy nxst copy))
         (aignet2 (aignet-set-nxst fanin next-reg aignet2)))
      (mv (+ 1 next-reg) aignet2))
    :init-vals ((next-reg 0))
    :returns (mv next-reg aignet2)
    :iter-guard (eql next-reg (marked-reg-count n mark aignet))
    :top-returns aignet2
    :last (num-regs aignet)
    :index n
    :package aignet::bla)

  (in-theory (disable aignet-copy-marked-nxsts))
  (local (in-theory (enable aignet-copy-marked-nxsts)))

  (verify-guards aignet-copy-marked-nxsts-step$inline
    :hints (("goal" :use ((:instance marked-reg-count-monotonic-strong
                           (n n) (m (stype-count :reg aignet))))
             :in-theory (disable marked-reg-count-monotonic-strong)
             :do-not-induct t)))


  (verify-guards aignet-copy-marked-nxsts-tailrec
    :hints (("goal" :expand ((marked-reg-count (+ 1 n) mark aignet)))))

  (verify-guards aignet-copy-marked-nxsts$inline
    :hints (("goal" :expand ((marked-reg-count 0 mark aignet)))))

  (def-aignet-preservation-thms aignet-copy-marked-nxsts-iter
    :stobjname aignet2)
  (def-aignet-preservation-thms aignet-copy-marked-nxsts
    :stobjname aignet2)

  (defthm stype-counts-preserved-of-aignet-copy-marked-nxsts-iter
    (implies (not (equal (stype-fix stype) (nxst-stype)))
             (equal (stype-count stype (mv-nth 1 (aignet-copy-marked-nxsts-iter
                                                  n nxtreg aignet mark copy aignet2)))
                    (stype-count stype aignet2)))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-marked-nxsts-iter n nxtreg aignet mark copy
                                           aignet2))))

  (defthm stype-counts-preserved-of-aignet-copy-marked-nxsts
    (implies (not (equal (stype-fix stype) (nxst-stype)))
             (equal (stype-count stype (aignet-copy-marked-nxsts
                                        aignet mark copy aignet2))
                    (stype-count stype aignet2))))


  (defthm nxtreg-of-aignet-copy-marked-nxsts-iter
    (equal (mv-nth 0 (aignet-copy-marked-nxsts-iter
                      n 0 aignet mark copy aignet2))
           (marked-reg-count n mark aignet))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-marked-nxsts-iter
             n 0 aignet mark copy aignet2))
           (and stable-under-simplificationp
                '(:expand ((marked-reg-count n mark aignet)
                           (marked-reg-count 0 mark aignet))))))

  (defthm lookup-nxst-of-aignet-copy-marked-nxsts-iter
    (implies (and ;; (aignet-extension-p aignet2 orig)
                  (aignet-copies-in-bounds copy aignet2)
                  (<= (nfix n) (num-regs aignet))
                  (<= (marked-reg-count (num-regs aignet) mark aignet)
                      (num-regs aignet2))
                  (< (nfix m) (marked-reg-count n mark aignet)))
             (b* (((mv ?nxtreg aignet21)
                   (aignet-copy-marked-nxsts-iter
                    n 0 aignet mark copy aignet2))
                  ;; (regid2 (fanin-count (lookup-stype m (reg-stype) orig)))
                  (regnum1 (stype-count :reg (cdr (lookup-marked-reg m mark aignet))))
                  (mth-nxst-look2 (lookup-reg->nxst m aignet21))
                  (mth-nxst-look (lookup-reg->nxst regnum1 aignet))
                  (fanin (lit-copy mth-nxst-look copy)))
               (and (equal mth-nxst-look2 fanin)
                    ;; (consp mth-nxst-look2)
                    ;; (equal (car mth-nxst-look2)
                    ;;        (nxst-node fanin regid2))
                    ;; (aignet-litp fanin (cdr mth-nxst-look2))
                    ;; (aignet-idp regid2 (cdr mth-nxst-look2))
                    )))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-marked-nxsts-iter
             n 0 aignet mark copy aignet2))
           (and stable-under-simplificationp
                `(:expand ((:free (x a b)
                            (lookup-reg->nxst x (cons a b)))
                           (marked-reg-count n mark aignet))
                  :in-theory (enable lookup-stype-in-bounds)))))

  (defthm lookup-nxst-of-aignet-copy-marked-nxsts
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  ;; (aignet-extension-p aignet2 orig)
                  ;; (equal (num-regs orig) (num-regs aignet2))
                  (<= (marked-reg-count (num-regs aignet) mark aignet)
                      (num-regs aignet2))
                  (< (nfix m) (marked-reg-count (num-regs aignet) mark aignet)))
             (b* ((aignet21
                   (aignet-copy-marked-nxsts aignet mark copy aignet2))
                  ;; (regid2 (fanin-count (lookup-stype m (reg-stype) orig)))
                  (regnum1 (stype-count :reg (cdr (lookup-marked-reg m mark aignet))))
                  (mth-nxst-look2 (lookup-reg->nxst m aignet21))
                  (mth-nxst-look (lookup-reg->nxst regnum1 aignet))
                  (fanin (lit-copy mth-nxst-look copy)))
               (and (equal mth-nxst-look2 fanin)
                    ;; (consp mth-nxst-look2)
                    ;; (equal (car mth-nxst-look2)
                    ;;        (nxst-node fanin regid2))
                    ;; (aignet-litp fanin (cdr mth-nxst-look2))
                    ;; (aignet-idp regid2 (cdr mth-nxst-look2))
                    ))))

  (defthm nth-frame-regval-of-aignet-copy-marked-nxsts
    (implies (and (<= (marked-reg-count (num-regs aignet) mark aignet)
                      (num-regs aignet2))
                  (< (nfix n) (marked-reg-count (num-regs aignet) mark aignet))
                  (aignet-copies-in-bounds
                                    copy aignet2))
             (equal (nth n (frame-regvals k frames initsts
                                          (aignet-copy-marked-nxsts
                                           aignet mark copy aignet2)))
                    (if (zp k)
                        (bfix (nth n initsts))
                      (lit-eval-seq (1- k)
                                    (lit-copy
                                     (lookup-reg->nxst
                                      (stype-count :reg (cdr (lookup-marked-reg
                                                              n mark aignet)))
                                      aignet)
                                     copy)
                                    frames initsts
                                    (aignet-copy-marked-nxsts
                                     aignet mark copy aignet2)))))
    :hints (("goal" :in-theory (enable id-eval-seq reg-eval-seq)))))



(defsection marked-regs-agree
  (defun-sk marked-regs-agree (vals1 vals2 mark aignet)
    (forall n
            (implies (and (< (nfix n) (num-regs aignet))
                          (equal (nth (regnum->id n aignet) mark) 1))
                     (bit-equiv (nth n vals1)
                                (nth n vals2)))))

  (in-theory (disable marked-regs-agree
                      marked-regs-agree-necc))

  (defthmd id-eval-with-marked-regs-agree
    (implies (and (marked-regs-agree vals1 vals2 mark aignet)
                  (aignet-mark-comb-invar mark aignet)
                  (equal (nth id mark) 1))
             (equal (id-eval id invals vals1 aignet)
                    (id-eval id invals vals2 aignet)))
    :hints (("goal" :induct (id-eval-ind id aignet)
             :expand ((:free (vals) (id-eval id invals vals aignet)))
             :in-theory (enable lit-eval eval-and-of-lits eval-xor-of-lits))
            (and stable-under-simplificationp
                 '(:use ((:instance marked-regs-agree-necc
                          (n (stype-count :reg (cdr (lookup-id id aignet))))))))))

  (defthm lit-eval-with-marked-regs-agree
    (implies (and (marked-regs-agree vals1 vals2 mark aignet)
                  (aignet-mark-comb-invar mark aignet)
                  (equal (nth (lit->var lit) mark) 1))
             (equal (lit-eval lit invals vals1 aignet)
                    (lit-eval lit invals vals2 aignet)))
    :hints (("goal" :use ((:instance id-eval-with-marked-regs-agree
                           (id (lit->var lit))))
             :expand ((:free (regvals) (lit-eval lit invals regvals aignet)))))))


(define aignet-prune-seq-aux (aignet
                              mark copy
                              (gatesimp gatesimp-p)
                              strash
                              aignet2)
  :prepwork ((local (defthm resize-list-0
                      (equal (resize-list x 0 d)
                             nil)
                      :hints(("Goal" :in-theory (enable resize-list)))))
             (local (in-theory (disable acl2::resize-list-when-atom)))
             (local (defthm strash-lemma
                      (implies (and (true-listp strash)
                                    (equal (len strash) 1))
                               (equal (update-nth 0 nil strash)
                                      '(nil)))
                      :hints (("goal" :in-theory (enable update-nth))))))
  (b* ((mark (resize-bits 0 mark))
       (mark (resize-bits (num-fanins aignet) mark))
       (copy (resize-lits 0 copy))
       (copy (resize-lits (num-fanins aignet) copy))
       (strash (mbe :logic (non-exec '(nil))
                    :exec (strashtab-init (num-gates aignet) nil nil strash)))
       (mark (aignet-mark-dfs-seq mark aignet))
       (nregs (marked-reg-count (num-regs aignet) mark aignet))
       (aignet2 (aignet-init (num-outs aignet)
                             nregs
                             (num-ins aignet)
                             (num-fanins aignet)
                             aignet2))
       ((mv copy aignet2) (aignet-copy-ins aignet copy aignet2))
       ((mv copy aignet2) (aignet-copy-marked-regs aignet mark copy aignet2))
       ((mv copy strash aignet2)
        (aignet-copy-marked aignet mark copy strash gatesimp aignet2))
       (aignet2 (aignet-copy-marked-nxsts aignet mark copy aignet2))
       (aignet2 (aignet-copy-outs aignet copy aignet2)))
    (mv mark copy strash aignet2))

  ///

  (defthm aignet-prune-seq-normalize
    (implies (syntaxp (not (and (equal mark ''nil)
                                (equal copy ''nil)
                                (equal strash ''(nil))
                                (equal aignet2 ''nil))))
             (equal (aignet-prune-seq-aux
                     aignet mark copy gatesimp strash aignet2)
                    (aignet-prune-seq-aux
                     aignet nil nil gatesimp '(nil) nil))))

  ;; (local (defthm id-eval-of-po
  ;;          (implies (equal (stype (car (lookup-id id aignet))) :po)
  ;;                   (equal (id-eval id invals regvals aignet)
  ;;                          (lit-eval (co-id->fanin id aignet)
  ;;                                    invals regvals aignet)))
  ;;          :hints(("Goal" :in-theory (enable id-eval)))))

  (defthm aignet-mark-seq-invar-of-resize-nil
    (aignet-mark-seq-invar (resize-list nil n 0) aignet)
    :hints(("Goal" :in-theory (enable aignet-mark-seq-invar
                                      acl2::nth-of-resize-list))))

  (defthm output-node-of-aignet-prune-seq-aux
    (b* (((mv ?mark ?copy ?strash ?aignet2)
          (aignet-prune-seq-aux aignet nil nil gatesimp strash aignet2)))
      (implies (< (nfix n) (stype-count :po aignet))
               (b* ((look2 (lookup-stype n :po aignet2))
                    (look1 (lookup-stype n :po aignet))
                    (fanin (lit-copy (fanin :co look1) copy)))
                 (and (equal (fanin :co look2) fanin)
                      ;; (equal (car look2)
                      ;;        (po-node fanin))
                      ;; (aignet-litp fanin (cdr look2))
                      (equal (nth (lit->var (fanin :co look1)) mark) 1))))))

  ;; (equal (id-eval (fanin-count (lookup-stype n :po aignet2))
  ;;                 invals regvals aignet2)
  ;;        (id-eval (fanin-count (lookup-stype n :po aignet))
  ;;                 (input-copy-values
  ;;                  invals regvals aignet2 copy aignet)
  ;;                 (aignet-copy-comb-reg-vals
  ;;                  invals regvals aignet2 copy aignet)
  ;;                 aignet)))))

  (defthm eval-marked-of-aignet-prune-seq-aux
    (b* (((mv ?mark ?copy ?strash ?aignet2)
          (aignet-prune-seq-aux aignet nil nil gatesimp strash aignet2)))
      (implies (and (equal 1 (nth id mark))
                    (aignet-idp id aignet))
               (equal (lit-eval (nth-lit id copy)
                                invals regvals aignet2)
                      (id-eval id
                               (input-copy-values
                                0 invals regvals aignet copy aignet2)
                               (reg-copy-values
                                0 invals regvals aignet copy aignet2)
                               aignet)))))

  (defthm eval-marked-of-aignet-prune-seq-aux-lit-copy
    (b* (((mv ?mark ?copy ?strash ?aignet2)
          (aignet-prune-seq-aux aignet nil nil gatesimp strash aignet2)))
      (implies (and (equal 1 (nth (lit->var lit) mark))
                    (aignet-idp (lit->var lit) aignet))
               (equal (lit-eval (lit-copy lit copy)
                                invals regvals aignet2)
                      (lit-eval lit
                               (input-copy-values
                                0 invals regvals aignet copy aignet2)
                               (reg-copy-values
                                0 invals regvals aignet copy aignet2)
                               aignet))))
    :hints(("Goal" :in-theory (enable lit-copy)
            :expand ((:free (invals regvals) (lit-eval lit invals regvals aignet))))))

  (local
   (defthm id-eval-of-lookup-reg
     (implies (< (nfix regnum) (num-regs aignet))
              (equal (id-eval (fanin-count (lookup-stype regnum :reg aignet))
                              invals regvals aignet)
                     (bfix (nth regnum regvals))))
     :hints(("Goal" :expand ((id-eval (fanin-count (lookup-stype regnum :reg
                                                                aignet))
                                      invals regvals aignet))))))

  (defthm reg-copy-of-aignet-prune-seq-aux
    (b* (((mv ?mark ?copy ?strash ?aignet2)
          (aignet-prune-seq-aux aignet nil nil gatesimp strash aignet2)))
      (implies (and (equal (nth (fanin-count (lookup-stype regnum :reg aignet))
                                mark)
                           1)
                    (< (nfix regnum) (num-regs aignet)))
               (equal (lit-eval
                       (nth-lit (fanin-count (lookup-stype regnum :reg aignet))
                                copy)
                       invals regvals aignet2)
                      (bfix (nth (marked-reg-count regnum mark aignet) regvals)))))
    :hints(("Goal" :in-theory (e/d (lit-eval)
                                   (eval-marked-of-aignet-prune-seq-aux)))))

  (defthm aignet-mark-seq-invar-of-aignet-prune-seq-aux
    (aignet-mark-seq-invar
     (mv-nth 0 (aignet-prune-seq-aux
                aignet nil nil gatesimp strash aignet2))
     aignet))

  (defthm num-ins-of-aignet-prune-seq-aux
    (equal (stype-count :pi (mv-nth 3 (aignet-prune-seq-aux
                                       aignet nil nil gatesimp strash
                                       aignet2)))
           (stype-count :pi aignet)))

  (defthm num-outs-of-aignet-prune-seq-aux
    (equal (stype-count :po (mv-nth 3 (aignet-prune-seq-aux
                                       aignet nil nil gatesimp strash
                                       aignet2)))
           (stype-count :po aignet)))


  (defthm input-copy-values-of-aignet-prune-seq-aux
    (b* (((mv ?mark ?copy ?strash ?aignet2)
          (aignet-prune-seq-aux aignet nil nil gatesimp strash aignet2)))
      (bits-equiv (input-copy-values
                   0 ins regs aignet copy aignet2)
                  (take (num-ins aignet) ins)))
    :hints(("Goal" :in-theory (enable aignet-prune-seq-aux
                                      lit-eval))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause)))))))

  (defthm nth-frame-regval-of-aignet-prune-seq-aux
    (b* (((mv ?mark ?copy ?strash ?aignet2)
          (aignet-prune-seq-aux aignet nil nil gatesimp strash aignet2)))
      (implies (< (nfix n) (marked-reg-count (num-regs aignet) mark aignet))
               (equal (nth n (frame-regvals k frames initsts aignet2))
                      (if (zp k)
                          (bfix (nth n initsts))
                        (lit-eval-seq (1- k)
                                      (lit-copy
                                       (lookup-reg->nxst
                                        (stype-count :reg (cdr (lookup-marked-reg
                                                                n mark aignet)))
                                        aignet)
                                       copy)
                                      frames initsts
                                      aignet2)))))
    :hints(("Goal" :in-theory (enable aignet-prune-seq-aux
                                      id-eval-seq
                                      reg-eval-seq))))


  ;; (defthm eval-frame-regval-of-aignet-prune-seq-aux
  ;;   (b* (((mv ?mark ?copy ?strash ?aignet2)
  ;;         (aignet-prune-seq-aux aignet nil nil gatesimp strash aignet2)))
  ;;     (implies (and (< (nfix regnum) (num-regs aignet))
  ;;                   (equal (nth (fanin-count (lookup-stype regnum :reg aignet))
  ;;                               mark)
  ;;                          1))
  ;;              (equal
  ;;               (lit-eval
  ;;                (nth-lit (fanin-count (lookup-stype regnum :reg aignet))
  ;;                         copy)
  ;;                nil (frame-regvals k frames nil aignet2) aignet2)
  ;;               (bfix (nth regnum (frame-regvals k frames nil aignet))))))
  ;;   :hints(("Goal" :in-theory (e/d (lit-eval aignet-prune-seq-aux)
  ;;                                  (nth-of-frame-regvals)))
  ;;          (and stable-under-simplificationp
  ;;               '(:in-theory (enable nth-of-frame-regvals)))))


  (mutual-recursion
   (defun prune-seq-eval-case (k lit frames aignet gatesimp strash aignet2)
     (declare (xargs :measure (acl2::two-nats-measure k 1)
                     :stobjs (aignet strash aignet2)
                     :verify-guards nil)
              (ignorable lit))
     (let ((val (non-exec (prune-seq-frame-case k frames aignet gatesimp strash
                                                aignet2))))
       val))
   (defun prune-seq-frame-case (k frames aignet gatesimp strash aignet2)
     (declare (xargs :measure (acl2::two-nats-measure k 0)
                     :stobjs (aignet strash aignet2)
                     :ruler-extenders :all))
     (let ((val (non-exec
                 (if (zp k)
                     (list frames aignet)
                   (let* ((regnum
                           (b* (((mv ?mark ?copy ?strash ?aignet2)
                                 (aignet-prune-seq-aux aignet nil nil gatesimp strash aignet2)))
                             (marked-regs-agree-witness
                              (reg-copy-values
                               0 (nth k (stobjs::2darr->rows frames)) (frame-regvals k frames nil aignet2) aignet copy
                               aignet2)
                              (frame-regvals k frames nil aignet)
                              mark aignet))))
                     (prune-seq-eval-case
                      (1- k)
                      (lookup-reg->nxst regnum aignet)
                      frames aignet gatesimp strash aignet2))))))
       val)))

  (flag::make-flag prune-seq-flg prune-seq-eval-case
                   :flag-mapping ((prune-seq-eval-case . eval)
                                  (prune-seq-frame-case . frame))
                   :ruler-extenders :all)

  (local (in-theory (disable aignet-prune-seq-aux
                             ;; LOOKUP-REG->NXST-OF-LOOKUP-STYPE-IS-LOOKUP-REGNUM->NXST
                             )))

  (defthm-prune-seq-flg
    (defthm lit-eval-seq-of-aignet-prune-seq-aux
      (b* (((mv ?mark ?copy ?strash ?aignet2)
            (aignet-prune-seq-aux aignet nil nil gatesimp strash aignet2)))
        (implies (and (equal 1 (nth (lit->var lit) mark))
                      (aignet-idp (lit->var lit) aignet))
                 (equal (lit-eval-seq k (lit-copy lit copy)
                                      frames nil aignet2)
                        (lit-eval-seq k lit frames nil aignet))))
      :hints('(:in-theory (enable lit-eval-seq-in-terms-of-lit-eval)))
      :flag eval)
    (defthm frame-regvals-of-aignet-prune-seq-aux
      (b* (((mv ?mark ?copy ?strash ?aignet2)
            (aignet-prune-seq-aux aignet nil nil gatesimp strash aignet2)))
        (marked-regs-agree
         (reg-copy-values
          0 (nth k (stobjs::2darr->rows frames))
          (frame-regvals k frames nil aignet2) aignet copy
          aignet2)
         (frame-regvals k frames nil aignet)
         mark aignet))
      :hints ('(:in-theory (e/d (lit-eval reg-eval-seq)
                                (eval-marked-of-aignet-prune-seq-aux
                                 ;; acl2::take-when-atom
                                 )))
              (and stable-under-simplificationp
                   `(:expand (,(car (last clause)))))
              (and stable-under-simplificationp
                   (let ((witness (acl2::find-call-lst
                                   'marked-regs-agree-witness
                                   clause)))
                     `(:clause-processor
                       (acl2::simple-generalize-cp
                        clause '((,witness . regnum)))))))
      :flag frame))




  (defthm seq-eval-output-of-aignet-prune-seq-aux-seq
    (b* (((mv ?mark ?copy ?strash ?aignet2)
          (aignet-prune-seq-aux aignet nil nil gatesimp strash aignet2)))
      (equal (lit-eval-seq k (fanin :co (lookup-stype n :po aignet2))
                          frames nil aignet2)
             (lit-eval-seq k (fanin :co (lookup-stype n :po aignet))
                          frames nil aignet)))
    :hints (("goal" :expand
             (;; (:free (aignet2)
              ;;  (id-eval-seq k (fanin-count (lookup-stype n :po aignet2))
              ;;               frames nil aignet2))
              (:free (aignet2)
               (lit-eval-seq k 0 frames nil aignet2))
              (:free (aignet2)
               (id-eval-seq k 0 frames nil aignet2)))
             :cases ((< (nfix n) (num-outs aignet)))
             :in-theory (enable fanin-count-lookup-stype-when-out-of-bounds))))


  (defthm seq-equiv-of-aignet-prune-seq-aux
    (seq-equiv (mv-nth 3 (aignet-prune-seq-aux
                          aignet nil nil gatesimp strash aignet2))
               aignet)
    :hints(("Goal" :in-theory (enable seq-equiv output-eval-seq)))))



(define aignet-prune-seq (aignet
                          (gatesimp gatesimp-p)
                          aignet2)
  (b* (((local-stobjs copy mark strash)
        (mv mark copy strash aignet2)))
    (aignet-prune-seq-aux aignet mark copy gatesimp strash aignet2))

  ///

  (defthm normalize-aignet-prune-seq
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal (aignet-prune-seq aignet gatesimp aignet2)
                    (aignet-prune-seq aignet gatesimp nil))))

  (defthm num-ins-of-aignet-prune-seq
    (equal (stype-count :pi (aignet-prune-seq aignet gatesimp aignet2))
           (stype-count :pi aignet)))

  (defthm num-outs-of-aignet-prune-seq
    (equal (stype-count :po (aignet-prune-seq aignet gatesimp aignet2))
           (stype-count :po aignet)))

  (defthm eval-output-of-aignet-prune-seq
    (let ((aignet2 (aignet-prune-seq aignet gatesimp aignet2)))
      (equal (lit-eval-seq k (fanin :co (lookup-stype n :po aignet2))
                           frames nil aignet2)
             (lit-eval-seq k (fanin :co (lookup-stype n :po aignet))
                           frames nil aignet))))

  (defthm seq-equiv-of-aignet-prune-seq
    (seq-equiv (aignet-prune-seq aignet gatesimp aignet2)
               aignet)))
