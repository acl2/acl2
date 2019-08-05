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

(include-book "cuts4")
(include-book "rwlib")
(include-book "statsmgr")
(include-book "centaur/aignet/transform-utils" :dir :system)
(include-book "centaur/aignet/prune" :dir :system)
(include-book "centaur/aignet/refcounts" :dir :system)
(include-book "centaur/aignet/sweep" :dir :system)
(include-book "centaur/misc/nth-nat-equiv" :dir :system)

(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))
(local (include-book "std/lists/update-nth" :dir :system))
(local (include-book "std/util/termhints" :dir :system))
(local (in-theory (disable acl2::update-nth-when-zp)))



(local (acl2::use-trivial-ancestors-check))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable nth update-nth unsigned-byte-p)))

(std::defenum rewrite-eval-method-p
  (:build :nobuild)
  :parents (rewrite-config))


(fty::defprod rewrite-config
  ((cuts4-config cuts4-config-p :default '(make-cuts4-config))
   (cut-tries-limit acl2::maybe-natp :rule-classes :type-prescription :default 5)
   (zero-cost-replace booleanp :rule-classes :type-prescription)
   (evaluation-method rewrite-eval-method-p :default :nobuild)
   (gatesimp gatesimp-p :default (default-gatesimp)
             "Gate simplification parameters.  Warning: This transform will do
              nothing good if hashing is turned off."))
  :parents (rewrite comb-transform)
  :short "Configuration object for the @(see rewrite) aignet transform."
  :tag :rewrite-config)

;; note: these are needed for fixequivs as long as the config is empty...
(local (in-theory (disable (rewrite-config)
                           rewrite-config-fix-when-rewrite-config)))

(local (defrefinement nat-equiv lit-equiv
         :hints(("Goal" :in-theory (enable lit-fix)))))

(local (defrefinement lit-equiv nat-equiv
         :hints(("Goal" :in-theory (enable lit-fix)))))

(defstatsmgr rewrite-stats
  (cuts-checked :desc "cuts checked" :abbrev "cuts")
  (tries :desc "candidates tried" :abbrev "tries")
  (repls :desc "replacements"     :abbrev "repls")
  (zero  :desc "zero cost"        :abbrev "zero")
  (savings :desc "savings computed" :abbrev "savings"))



;; bozo redundant with balance.lisp
(defstobj-clone refcounts2 u32arr :prefix "REFCOUNTS2-")
;; (defstobj-clone rwlib rwlib :prefix "RWLIB-")

;; (defstobj-clone smm acl2::smm :strsubst (("abcd" . "abcd")))
(defstobj-clone eba2 eba :suffix "2")
(defstobj-clone eba3 eba :suffix "3")
(defstobj-clone eba4 eba :suffix "4")



;; (local (defthm cutsdb-ok-implies-truth-p-of-truth
;;          (implies (and (cutsdb-ok cutsdb)
;;                        (cutp$ cut cutsdb)
;;                        (< cut (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
;;                   (truth::truth4-p (cut-datai (+ 1 cut) cutsdb)))
;;          :hints (("goal" :use ((:instance cutsdb-ok-implies-cutsdb-cut-ok
;;                                 (n cut)))
;;                   :in-theory (e/d (cutsdb-cut-ok cut-next$ cut-next)
;;                                   (cutsdb-ok-implies-cutsdb-cut-ok))))))

(local (defthm bound-when-truth4-p
         (implies (truth::truth4-p x)
                  (< x #x10000))
         :hints(("Goal" :in-theory (enable truth::truth4-p unsigned-byte-p)))))

(defsection empty-bitarr-p
  (defun-sk empty-bitarr-p (x)
    (forall idx
            (bit-equiv (nth idx x) 0))
    :rewrite :direct)

  (local (include-book "std/lists/nth" :dir :system))

  (defthm empty-bitarr-p-of-repeat
    (empty-bitarr-p (acl2::repeat n 0)))

  (in-theory (Disable empty-bitarr-p))

  (defthm aignet-marked-copies-in-bounds-of-empty-bitarr
    (implies (empty-bitarr-p x)
             (aignet-marked-copies-in-bounds copy x aignet2))
    :hints(("Goal" :in-theory (enable aignet-marked-copies-in-bounds)))))

(define cut-initialize-copy ((cut natp)
                             (copy2 "mapping from dsd aig indices to aignet2 indices -- writing this here")
                             (cutsdb cutsdb-ok)
                             (rwlib rwlib-wfp))
  :returns (new-copy2)
  :guard (and (< cut (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (b* (((acl2::stobj-get ok)
                    ((aignet-tmp (rwlib->aigs rwlib)))
                    (<= (num-fanins aignet-tmp) (lits-length copy2))))
                ok))
  :prepwork (;; (local (defthm cut-data-bounded-by-cut-nnodes
             ;;          (implies (and (cutsdb-ok cutsdb)
             ;;                        (natp cut)
             ;;                        (< cut (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
             ;;                        (natp idx)
             ;;                        (< idx (cutinfo->size (cut-infoi cut cutsdb))))
             ;;                   (< (cut-leavesi (+ (* 4 cut) idx) cutsdb) (cut-nnodes cutsdb)))
             ;;          :hints (("goal" :use ((:instance cutsdb-ok-implies-cuts-bounded-by-nnodes
             ;;                                 (bound (cut-nnodes cutsdb)) (cut cut)))
             ;;                   :in-theory (e/d (cut-leaves-bounded
             ;;                                    leaves-bounded-implies-compare)
             ;;                                   (cutsdb-ok-implies-cuts-bounded-by-nnodes))
             ;;                   :cases ((equal (cut-nnodes cutsdb) 0))))
             ;;          :rule-classes :linear))

             (local (defthm cut-leaf-lit-idp-by-cut-nnodes
                      (implies (and (cutsdb-lit-idsp aignet cutsdb)
                                    (natp cut)
                                    (< cut (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                                    (natp idx)
                                    (< idx (cutinfo->size (cut-infoi cut cutsdb))))
                               (aignet-idp (cut-leavesi (+ (* 4 cut) idx) cutsdb)
                                            aignet))
                      :hints (("goal" :use ((:instance cutsdb-lit-idsp-implies-cut-leaves-lit-idsp))
                               :in-theory (e/d (cut-leaves-lit-idsp
                                                leaves-lit-idsp-implies)))))))
  (b* (((cutinfo cutinf) (cut-infoi cut cutsdb))
       ((acl2::stobj-get npn)
        ((truth::npn4arr (rwlib->npns rwlib)))
        (truth::get-npn4 cutinf.truth truth::npn4arr))
       ((truth::npn4 npn))
       ((acl2::fun (idx-lit idx perm polarity cutinf.size cut cutsdb))
        (b* ((perm-idx (truth::perm4-index idx perm))
             (node (if (< perm-idx cutinf.size) (cut-leavesi (+ perm-idx (* 4 (lnfix cut))) cutsdb) 0)))
          (make-lit node (logbit idx polarity))))
       ((acl2::stobj-get copy2)
        ((aignet-tmp (rwlib->aigs rwlib)))
        (b* ((copy2 (set-lit (innum->id 0 aignet-tmp)
                             (idx-lit 0 npn.perm npn.polarity cutinf.size cut cutsdb)
                             copy2))
             (copy2 (set-lit (innum->id 1 aignet-tmp)
                             (idx-lit 1 npn.perm npn.polarity cutinf.size cut cutsdb)
                             copy2))
             (copy2 (set-lit (innum->id 2 aignet-tmp)
                             (idx-lit 2 npn.perm npn.polarity cutinf.size cut cutsdb)
                             copy2))
             (copy2 (set-lit (innum->id 3 aignet-tmp)
                             (idx-lit 3 npn.perm npn.polarity cutinf.size cut cutsdb)
                             copy2)))
          copy2)))
    copy2)
  ///
  (defret lookup-of-cut-initialize-copy
    (implies (and (< (nfix n) 4)
                  (rwlib-wfp rwlib))
             (equal (nth-lit (fanin-count (lookup-stype n :pi (rwlib->aigs rwlib)))
                             new-copy2)
                    (b* (((cutinfo cutinf) (cut-infoi cut cutsdb))
                         ((truth::npn4 npn) (truth::get-npn4 cutinf.truth (rwlib->npns rwlib)))
                         (perm-idx (truth::index-perm
                                    0 (truth::perm4-index-list npn.perm) n 4))
                         (node (if (< perm-idx cutinf.size)
                                   (cut-leavesi (+ perm-idx (* 4 (nfix cut))) cutsdb)
                                 0)))
                      (make-lit node (logbit n npn.polarity)))))
    :hints (("Goal" :cases ((equal (nfix n) 0)
                            (equal (nfix n) 1)
                            (equal (nfix n) 2)
                            (equal (nfix n) 3)))))

  (local (defthmd stype-when-stype-count-is-zero
           (implies (and (equal (stype-count stype aignet) 0)
                         (not (equal stype (const-stype))))
                    (not (equal (stype (car (lookup-id id aignet))) stype)))
           :hints(("Goal" :in-theory (enable stype-count lookup-id)))))

  (defretd lookup-of-cut-initialize-copy-when-input
    (implies (and (rwlib-wfp rwlib)
                  (equal (ctype (stype (car (lookup-id id (rwlib->aigs rwlib))))) :input))
             (equal (nth-lit id
                             new-copy2)
                    (b* ((n (stype-count :pi (cdr (lookup-id id (rwlib->aigs rwlib)))))
                         ((cutinfo cutinf) (cut-infoi cut cutsdb))
                         ((truth::npn4 npn) (truth::get-npn4 cutinf.truth (rwlib->npns rwlib)))
                         (perm-idx (truth::index-perm
                                    0 (truth::perm4-index-list npn.perm) n 4))
                         (node (if (< perm-idx cutinf.size)
                                   (cut-leavesi (+ perm-idx (* 4 (nfix cut))) cutsdb)
                                 0)))
                      (make-lit node (logbit n npn.polarity)))))
    :hints (("goal" :in-theory (e/d (ctype
                                     stype-when-stype-count-is-zero)
                                    (cut-initialize-copy
                                        lookup-of-cut-initialize-copy))
             :expand ((stype-count :pi (lookup-id id (rwlib->aigs rwlib))))
             :use ((:instance lookup-of-cut-initialize-copy
                    (n (stype-count :pi (cdr (lookup-id id (rwlib->aigs rwlib))))))))))

  (defret aignet-copies-in-bounds-of-cut-initialize-copy
    (implies (and (aignet-copies-in-bounds copy2 aignet2)
                  (cutsdb-lit-idsp aignet2 cutsdb)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (aignet-copies-in-bounds new-copy2 aignet2)))

  (defret aignet-input-copies-in-bounds-of-cut-initialize-copy
    (implies (and (cutsdb-lit-idsp aignet2 cutsdb)
                  (rwlib-wfp rwlib)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (aignet-input-copies-in-bounds new-copy2
                                            (rwlib->aigs rwlib)
                                            aignet2))
    :hints(("Goal" :in-theory (e/d (aignet-input-copies-in-bounds
                                    lookup-of-cut-initialize-copy-when-input)
                                   (cut-initialize-copy)))))

  (defret length-of-cut-initialize-copy
    (implies (and (<= (num-fanins (rwlib->aigs rwlib)) (len copy2))
                  (rwlib-wfp rwlib))
             (equal (len new-copy2) (len copy2)))))
       
(define cut-impl-index-ok ((cut natp)
                           (impl-idx natp)
                           (cutsdb cutsdb-ok)
                           (rwlib rwlib-wfp))
  :guard (< cut (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  (b* (((cutinfo cutinf) (cut-infoi cut cutsdb))
       ((acl2::stobj-get ok)
        ((truth::npn4arr (rwlib->npns rwlib))
         (acl2::smm   (rwlib->cands rwlib)))
        (b* (((truth::npn4 npn) (truth::get-npn4 cutinf.truth truth::npn4arr)))
          (< (lnfix impl-idx) (acl2::smm-block-size npn.truth-idx acl2::smm)))))
    ok))
       
(define smm-read-lit ((block natp)
                      (idx natp)
                      (smm))
  :guard (and (< block (smm-nblocks smm))
              (< idx (smm-block-size block smm)))
  :enabled t
  :inline t
  :prepwork ((local (defthm nat-listp-when-u32-listp
                      (implies (acl2::u32-listp x)
                               (nat-listp x))))
             (local (defthm nat-listp-nth-of-u32-list-listp
                      (implies (and (Acl2::u32-list-listp x)
                                    (< (nfix n) (len x)))
                               (nat-listp (nth n x)))
                      :hints(("Goal" :in-theory (enable nth)))))
             (local (defthm litp-nth-of-nat-listp
                      (implies (and (nat-listp x)
                                    (< (nfix n) (len x)))
                               (litp (nth n x)))
                      :hints(("Goal" :in-theory (enable nth)))))
             (local (defthm natp-nth-of-nat-listp
                      (implies (and (nat-listp x)
                                    (< (nfix n) (len x)))
                               (natp (nth n x)))
                      :hints(("Goal" :in-theory (enable nth))))))
  (mbe :logic (lit-fix (smm-read block idx smm))
       :exec (smm-read block idx smm)))


(defthm impl-lit-bound-when-rwlib-wfp
  (implies (and (rwlib-wfp rwlib)
                (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                (cutsdb-ok cutsdb)
                (cut-impl-index-ok cut impl-idx cutsdb rwlib))
           (<= (lit->var (nth impl-idx
                              (nth (truth::npn4->truth-idx (nth (cutinfo->truth (cut-infoi cut cutsdb))
                                                                (rwlib->npns rwlib)))
                                   (rwlib->cands rwlib))))
               (fanin-count (rwlib->aigs rwlib))))
  :hints(("Goal" :in-theory (enable cut-impl-index-ok)))
  :rule-classes (:rewrite :linear))


(defsection cutsdb-correct
  (defun-sk cutsdb-correct (cutsdb aignet)
    (forall (vals invals regvals)
            (cutsdb-consistent cutsdb (aignet-record-vals vals invals regvals aignet)))
    :rewrite :direct)

  (in-theory (disable cutsdb-correct))
  (defthm cutsdb-correct-of-aignet-derive-cuts
    (cutsdb-correct (mv-nth 1 (aignet-derive-cuts aignet config refcounts cutsdb)) aignet)
    :hints(("Goal" :in-theory (enable cutsdb-correct))))

  (defthm cutsdb-correct-of-aignet-derive-cuts-aux
    (implies (and (cutsdb-correct cutsdb aignet)
                  (cutsdb-ok cutsdb))
             (cutsdb-correct (mv-nth 1 (aignet-derive-cuts-aux aignet count config refcounts cutsdb)) aignet))
    :hints((and stable-under-simplificationp
                `(:expand (,(car (last clause)))))))

  (fty::deffixequiv cutsdb-correct :args ((aignet aignet))
    :hints(("Goal" :in-theory (disable cutsdb-correct)
            :cases ((cutsdb-correct cutsdb aignet)))
           (and stable-under-simplificationp
                (b* ((lit (assoc 'cutsdb-correct clause))
                     (other (cadr (assoc 'not clause))))
                  `(:expand (,lit)
                    :in-theory (disable cutsdb-correct-necc)
                    :use ((:instance cutsdb-correct-necc
                           (cutsdb ,(cadr other))
                           (aignet ,(caddr other))
                           (vals (mv-nth 0 (cutsdb-correct-witness . ,(cdr lit))))
                           (invals (mv-nth 1 (cutsdb-correct-witness . ,(cdr lit))))
                           (regvals (mv-nth 2 (cutsdb-correct-witness . ,(cdr lit))))))))))))

(defsection cutsdb-correct-of-aignet-extension
  ;; (local (defthm cut-data-bounded-by-cut-nnodes
  ;;          (implies (and (cutsdb-ok cutsdb)
  ;;                        (natp cut)
  ;;                        (< cut (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  ;;                        (natp idx)
  ;;                        (< idx (cutinfo->size (cut-infoi cut cutsdb))))
  ;;                   (< (cut-leavesi (+ (* 4 cut) idx) cutsdb) (cut-nnodes cutsdb)))
  ;;          :hints (("goal" :use ((:instance cutsdb-ok-implies-cuts-bounded-by-nnodes
  ;;                                 (bound (cut-nnodes cutsdb)) (cut cut)))
  ;;                   :in-theory (e/d (cut-leaves-bounded
  ;;                                    leaves-bounded-implies-compare)
  ;;                                   (cutsdb-ok-implies-cuts-bounded-by-nnodes))
  ;;                   :cases ((equal (cut-nnodes cutsdb) 0))))
  ;;          :rule-classes :linear))

  (local (defthm leaves-bounded-when-cutsdb-ok
           (implies (and (cutsdb-ok cutsdb)
                         (natp cut)
                         (< cut (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
                    (leaves-bounded (* 4 cut)
                                    (cutinfo->size (cut-infoi cut cutsdb))
                                    (cut-nnodes cutsdb)
                                    cutsdb))
           :hints (("goal" :use ((:instance cutsdb-ok-implies-cuts-bounded-by-nnodes
                                  (bound (cut-nnodes cutsdb)) (cut cut)))
                    :in-theory (e/d (cut-leaves-bounded)
                                    (cutsdb-ok-implies-cuts-bounded-by-nnodes))))))


  (local (defthm leaves-truthenv-of-record-vals-of-aignet-extension
           (implies (and (aignet-extension-binding)
                         (leaves-bounded data size (cut-nnodes cutsdb) cutsdb)
                         (<= (cut-nnodes cutsdb) (num-fanins orig)))
                    (equal (leaves-truthenv data size bit-idx cutsdb
                                            (aignet-record-vals vals invals regvals new))
                           (leaves-truthenv data size bit-idx cutsdb
                                            (aignet-record-vals vals invals regvals orig))))
           :hints(("Goal" :in-theory (enable leaves-truthenv leaves-bounded
                                             aignet-idp)))))

  (local (defthm cut-value-of-record-vals-of-aignet-extension
           (implies (and (aignet-extension-binding)
                         (cutsdb-ok cutsdb)
                         (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                         (<= (cut-nnodes cutsdb) (num-fanins orig)))
                    (equal (cut-value cut cutsdb (aignet-record-vals vals invals regvals new))
                           (cut-value cut cutsdb (aignet-record-vals vals invals regvals orig))))
           :hints(("Goal" :in-theory (e/d (cut-value cut-leaves-bounded)
                                          (cutsdb-ok-implies-cuts-bounded-by-nnodes))
                   :use ((:instance cutsdb-ok-implies-cuts-bounded-by-nnodes
                          (bound (Cut-nnodes cutsdb))))))))

  (local (defthm cuts-consistent-of-record-vals-of-aignet-extension
           (implies (and (aignet-extension-binding)
                         (cutsdb-ok cutsdb)
                         (<= (nfix max) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                         (<= (cut-nnodes cutsdb) (num-fanins orig)))
                    (equal (cuts-consistent cut max value cutsdb (aignet-record-vals vals invals regvals new))
                           (cuts-consistent cut max value cutsdb (aignet-record-vals vals invals regvals orig))))
           :hints(("Goal" :in-theory (enable cuts-consistent)))))

  (local (defthm node-cuts-consistent-of-record-vals-of-aignet-extension
           (implies (and (aignet-extension-binding)
                         (cutsdb-ok cutsdb)
                         (< (nfix node) (cut-nnodes cutsdb))
                         (<= (cut-nnodes cutsdb) (num-fanins orig)))
                    (equal (node-cuts-consistent node cutsdb (aignet-record-vals vals invals regvals new))
                           (node-cuts-consistent node cutsdb (aignet-record-vals vals invals regvals orig))))
           :hints(("Goal" :in-theory (enable node-cuts-consistent aignet-idp)))))

  (local (defthm cutsdb-consistent-of-record-vals-of-aignet-extension
           (implies (and (aignet-extension-binding)
                         (cutsdb-ok cutsdb)
                         (<= (cut-nnodes cutsdb) (num-fanins orig))
                         (cutsdb-consistent cutsdb (aignet-record-vals vals invals regvals orig)))
                    (cutsdb-consistent cutsdb (aignet-record-vals vals invals regvals new)))
           :hints ((and stable-under-simplificationp
                        `(:expand (,(car (last clause))))))))

  (defthm cutsdb-correct-of-aignet-extension
    (implies (and (aignet-extension-binding)
                  (cutsdb-correct cutsdb orig)
                  (cutsdb-ok cutsdb)
                  (<= (cut-nnodes cutsdb) (num-fanins orig)))
             (cutsdb-correct cutsdb new))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause))))))))



;; (defsection nth-of-input-copy-values-split
;;   (local (in-theory (enable input-copy-values)))
;;   (local (include-book "std/lists/nth" :dir :system))

;;   (local (defret nth-of-input-copy-values-split-lemma
;;            (implies (<= (nfix n) (nfix m))
;;                     (equal (nth (- (nfix m) (nfix n)) input-vals)
;;                            (and (< (nfix m) (num-ins aignet))
;;                                 (lit-eval (nth-lit (innum->id m aignet) copy)
;;                                           invals regvals aignet2))))
;;            :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)
;;                    :induct <call>
;;                    :expand ((:free (cons m a b) (nth m (cons a b))))))
;;            :fn input-copy-values))

;;   (defret nth-of-input-copy-values-split
;;     (equal (nth m input-vals)
;;            (and (< (+ (nfix m) (nfix n)) (num-ins aignet))
;;                 (lit-eval (nth-lit (innum->id (+ (nfix m) (nfix n)) aignet) copy)
;;                           invals regvals aignet2)))
;;     :hints(("Goal" :use ((:instance nth-of-input-copy-values-split-lemma
;;                           (m (+ (nfix m) (nfix n)))))
;;             :in-theory (disable nth-of-input-copy-values-split-lemma
;;                                 input-copy-values)))
;;     :fn input-copy-values))


(local (defthmd cut-leaves-bounded-implies-compare
         (implies (and (cut-leaves-bounded cut bound cutsdb)
                       (natp cut) (natp idx) (natp bound)
                       (< idx (cutinfo->size (cut-infoi cut cutsdb))))
                  (< (cut-leavesi (+ idx (* 4 cut)) cutsdb) bound))
         :hints(("Goal" :in-theory (enable cut-leaves-bounded
                                           leaves-bounded-implies-compare)))
         :rule-classes (:rewrite :linear)))

;; (local
;;  (defthmd cut-leaves-lit-idsp-implies
;;    (implies (and (cut-leaves-lit-idsp cut aignet cutsdb)
;;                  (natp cut) (natp idx)
;;                  (< idx (cutinfo->size (cut-infoi cut cutsdb))))
;;             (b* ((leaf (cut-leavesi (+ idx (* 4 cut)) cutsdb)))
;;               (and (aignet-idp leaf aignet)
;;                    (not (equal (ctype (stype (car (lookup-id leaf aignet)))) :output))
;;                    (not (equal (stype (car (lookup-id leaf aignet))) :po))
;;                    (not (equal (stype (car (lookup-id leaf aignet))) :nxst)))))
;;    :hints(("Goal" :in-theory (enable cut-leaves-lit-idsp
;;                                      leaves-lit-idsp-implies)))))



(defthm input-copy-values-of-cut-initialize-copy
  (implies (and ;; (aignet-copy-is-comb-equivalent node aignet copy aignet2)
                ;; (aignet-copies-in-bounds copy aignet2)
                ;; (cutsdb-lit-idsp aignet2 cutsdb)
            ;; (posp node)
                ;; (cut-leaves-bounded cut node cutsdb)
            (< (nfix n) 4)
            (rwlib-wfp rwlib)
            ;; (cutsdb-ok cutsdb)
            ;; (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
            ;; (rwlib-correct rwlib)
            )
           (iff (truth::env-lookup n
                                   (permuted-env-from-aignet-invals
                                    (nth (cutinfo->truth (cut-infoi cut cutsdb))
                                         (rwlib->npns rwlib))
                                    (INPUT-COPY-VALUES 0 INVALS
                                                       REGVALS (RWLIB->AIGS RWLIB)
                                                       (CUT-INITIALIZE-COPY CUT COPY2 CUTSDB RWLIB)
                                                       AIGNET2)))
                (and (< (nfix n) (cutinfo->size (cut-infoi cut cutsdb)))
                     (acl2::bit->bool 
                      (id-eval (cut-leavesi (+ (* 4 (nfix cut)) (nfix n)) cutsdb)
                               invals regvals aignet2)))))
  :hints(("Goal" :in-theory (enable ;; cut-leaves-bounded-implies-compare
                                    ;; cut-leaves-lit-idsp-implies
                                    ;; cutsdb-lit-idsp-implies-cut-leaves-lit-idsp
                                    )
          :expand ((:free (id neg) (lit-eval (make-lit id neg) invals regvals aignet2)))
          ;; :use ((:instance cutsdb-cut-lit-idsp-implies-nodes-lit-idsp
          ;;        (n cut)
          ;;        (i (+ 2 cut (nfix n)))))
          )))

;; (local (defthmd cut-leaves-bounded-implies-compare-strong
;;          (implies (and (equal cut1 (double-rewrite cut))
;;                        (bind-free (case-match cut1
;;                                     (('nfix cut2) `((cut2 . ,cut2)))
;;                                     (& `((cut2 . ,cut1))))
;;                                   (cut2))
;;                        (equal (nfix cut2) cut1)
;;                        (syntaxp (or (cw "cut2: ~x0~%" cut2) t))
;;                        (cut-leaves-bounded cut2 bound cutsdb)
;;                        (syntaxp (or (cw "bound: ~x0~%" bound) t))
;;                        (natp cut1) (natp idx) (natp bound)
;;                        (<= bound bound2)
;;                        (< idx (cutinfo->size (cut-infoi cut1 cutsdb))))
;;                   (< (cut-leavesi (+ idx (* 4 cut)) cutsdb) bound2))
;;          :hints(("Goal" :in-theory (enable cut-leaves-bounded
;;                                            leaves-bounded-implies-compare)))
;;          :rule-classes (:rewrite :linear)))

(defthm permuted-env-of-input-copy-values-is-truthenv
  (implies (and ;; (aignet-copy-is-comb-equivalent node aignet copy aignet2)
                ;; (aignet-copies-in-bounds copy aignet2)
            ;; (cutsdb-lit-idsp aignet2 cutsdb)
                ;; (posp node)
            (cut-leaves-bounded cut (num-fanins aignet2) cutsdb)
            (< (nfix n) 4)
            (rwlib-wfp rwlib)
            ;; (cutsdb-ok cutsdb)
            ;; (<= node (num-fanins aignet))
            ;; (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
            ;; (rwlib-correct rwlib)
            )
           (iff (truth::env-lookup n
                                   (permuted-env-from-aignet-invals
                                    (nth (cutinfo->truth (cut-infoi cut cutsdb))
                                         (rwlib->npns rwlib))
                                    (INPUT-COPY-VALUES 0 INVALS
                                                       REGVALS (RWLIB->AIGS RWLIB)
                                                       (CUT-INITIALIZE-COPY CUT COPY2 CUTSDB RWLIB)
                                                       AIGNET2)))
                (truth::env-lookup
                 n
                 (leaves-truthenv (* 4 (nfix cut)) (cutinfo->size (cut-infoi cut cutsdb))
                                  0 cutsdb
                                  (aignet-record-vals nil invals regvals aignet2)))))
  :hints(("Goal" :in-theory (e/d (aignet-idp
                                  ;; cut-leaves-lit-idsp-implies
                                  cut-leaves-bounded-implies-compare ;;-strong
                                  ;; cut-leaves-lit-idsp-implies
                                  ;; cutsdb-lit-idsp-implies-cut-leaves-lit-idsp
                                  )))))


(defsection eval-with-permuted-env-of-input-copy-values-is-truthenv
  (local #!truth
         (defret eval-match-when-no-env-mismatch
           (implies (and (natp numvars)
                         (case-split (implies (< var (nfix numvars))
                                              (iff (env-lookup var env1)
                                                   (env-lookup var env2)))))
                    (equal (equal (truth-eval truth env1 numvars)
                                  (truth-eval truth env2 numvars))
                           t))
           :hints (("goal" :use truth::env-mismatch-when-eval-mismatch))
           :fn truth::env-mismatch))
  (defthm eval-with-permuted-env-of-input-copy-values-is-truthenv
    (implies (and ;; (aignet-copy-is-comb-equivalent node aignet copy aignet2)
                  ;; (aignet-copies-in-bounds copy aignet2)
                  ;; (cutsdb-lit-idsp aignet cutsdb)
                  ;; (posp node)
                  (cut-leaves-bounded cut (num-fanins aignet2) cutsdb)
                  (rwlib-wfp rwlib)
                  ;; (cutsdb-ok cutsdb)
                  ;; (<= node (num-fanins aignet))
                  ;; (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  ;; (rwlib-correct rwlib)
                  )
             (equal (truth::truth-eval truth
                                       (permuted-env-from-aignet-invals
                                        (nth (cutinfo->truth (cut-infoi cut cutsdb))
                                             (rwlib->npns rwlib))
                                        (INPUT-COPY-VALUES 0 INVALS
                                                           REGVALS (RWLIB->AIGS RWLIB)
                                                           (CUT-INITIALIZE-COPY CUT COPY2 CUTSDB RWLIB)
                                                           AIGNET2))
                                       4)
                    (truth::truth-eval truth
                                       ;; (node-cut-truthenv (+ 2 cut) (cut-datai cut cutsdb)
                                       ;;                    0 cutsdb
                                       ;;                    (aignet-record-vals nil invals regvals aignet))
                                       (leaves-truthenv (* 4 (nfix cut)) (cutinfo->size (cut-infoi cut cutsdb))
                                                        0 cutsdb
                                                        (aignet-record-vals nil invals regvals aignet2))
                                       4)))))





(define aignet-build-cut ((cut natp)
                          (impl-idx natp)
                          (eba "mark for copied nodes")
                          (copy2 "mapping from dsd aig indices to aignet2 indices -- writing this here")
                          (cutsdb cutsdb-ok)
                          (rwlib rwlib-wfp)
                          (gatesimp gatesimp-p)
                          (strash2)
                          (aignet2))
  :guard (and ;; (<= (cut-nnodes cutsdb) (lits-length copy))
              ;; (aignet-copies-in-bounds copy aignet2)
          (cutsdb-lit-idsp aignet2 cutsdb)
          (< cut (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
          (b* (((acl2::stobj-get ok)
                ((aignet-tmp (rwlib->aigs rwlib)))
                (and (<= (num-fanins aignet-tmp) (lits-length copy2))
                     (<= (num-fanins aignet-tmp) (eba-length eba)))))
            ok)
          (cut-impl-index-ok cut impl-idx cutsdb rwlib))
  :guard-hints (("goal" :in-theory (enable cut-impl-index-ok)))
  :returns (mv (lit litp :rule-classes :type-prescription)
               (new-copy2)
               (new-eba)
               (new-strash2)
               (new-aignet2))
  (b* ((copy2 (cut-initialize-copy cut copy2 cutsdb rwlib))
       ((cutinfo cutinf) (cut-infoi cut cutsdb))
       ((acl2::stobj-get lit copy2 eba strash2 aignet2)
        ((truth::npn4arr (rwlib->npns rwlib))
         (smm   (rwlib->cands rwlib))
         (aignet-tmp  (rwlib->aigs rwlib)))
        (b* (((truth::npn4 npn) (truth::get-npn4 cutinf.truth truth::npn4arr))
             (lit (smm-read-lit npn.truth-idx impl-idx smm))
             (eba (eba-clear eba))
             ((mv eba copy2 strash2 aignet2)
              (aignet-copy-dfs-eba-rec (lit-id lit) aignet-tmp eba copy2 strash2 gatesimp aignet2))
             (new-lit (lit-negate-cond (lit-copy lit copy2) npn.negate)))
          (mv new-lit copy2 eba strash2 aignet2))))
    (mv lit copy2 eba strash2 aignet2))
  ///
  (def-aignet-preservation-thms aignet-build-cut :stobjname aignet2)

  

  (local (defthm b-xor-identity
           (equal (b-xor a (b-xor a b))
                  (bfix b))
           :hints(("Goal" :in-theory (enable b-xor)))))

  (local
   (defret eval-of-aignet-build-cut-lemma
     (implies (and ;; (aignet-copy-is-comb-equivalent node aignet copy aignet2)
                   (rwlib-correct rwlib)
                   ;; (cutsdb-ok cutsdb)
                   (cutsdb-lit-idsp aignet2 cutsdb)
                   (rwlib-wfp rwlib)
                   ;; (aignet-copies-in-bounds copy2 aignet2)
                   ;; (aignet-copies-in-bounds copy aignet2)
                   ;; (posp node)
                   (cut-leaves-bounded cut (num-fanins aignet2) cutsdb)
                   ;; (<= node (num-fanins aignet))
                   ;; (< node (cut-nnodes cutsdb))
                   ;; (< node (cut-nnodes cutsdb))
                   ;; (<= (nodecut-indicesi node cutsdb) cut)
                   ;; (< cut (nodecut-indicesi (+ 1 node) cutsdb))
                   (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                   (cut-impl-index-ok cut impl-idx cutsdb rwlib))
              (equal (lit-eval lit invals regvals new-aignet2)
                     ;; (b-xor 
                     ;;  (truth::npn4->negate (nth (cut-datai (+ 1 cut) cutsdb)
                     ;;                            (rwlib->npns rwlib)))
                      ;; (id-eval node invals regvals aignet)
                      (acl2::bool->bit
                       (cut-value cut cutsdb 
                                  (aignet-record-vals nil invals regvals aignet2)))))
     :hints(("Goal" :in-theory (e/d (cut-impl-index-ok cut-value))
             :do-not-induct t))))

  (local (defthm cutsdb-ok-implies-cuts-bounded-by-greater
           (implies (and (cutsdb-ok cutsdb)
                         (<= (cut-nnodes cutsdb) (nfix bound))
                         (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
                    (cut-leaves-bounded cut bound cutsdb))
           :hints (("goal" :use ((:instance cutsdb-ok-implies-cuts-bounded-by-nnodes
                                  (bound (cut-nnodes cutsdb))))
                    :in-theory (e/d (cut-leaves-bounded
                                     leaves-bounded-when-bounded-lesser)
                                    (cutsdb-ok-implies-cuts-bounded-by-nnodes))))))

  (defret eval-of-aignet-build-cut
    (implies (and ;; (aignet-copy-is-comb-equivalent node aignet copy aignet2)
                  (rwlib-correct rwlib)
                  (cutsdb-ok cutsdb)
                  (cutsdb-lit-idsp aignet2 cutsdb)
                  (rwlib-wfp rwlib)
                  ;; (aignet-copies-in-bounds copy2 aignet2)
                  ;; (aignet-copies-in-bounds copy aignet2)
                  (posp node)
                  ;; (cut-leaves-bounded cut node cutsdb)
                  (< node (cut-nnodes cutsdb))
                  (<= (cut-nnodes cutsdb) (num-fanins aignet2))
                  ;; (not (equal (ctype (stype (car (lookup-id node aignet2)))) :output))
                  (<= (nodecut-indicesi node cutsdb) (nfix cut))
                  (< (nfix cut) (nodecut-indicesi (+ 1 node) cutsdb))
                  (cut-impl-index-ok cut impl-idx cutsdb rwlib)
                  (cutsdb-correct cutsdb aignet2))
             (equal (lit-eval lit invals regvals new-aignet2)
                    (id-eval node invals regvals aignet2)
                     ;; (acl2::bool->bit
                     ;;  (cut-value cut cutsdb 
                     ;;             (aignet-record-vals nil invals regvals aignet)))
                     ))
    :hints(("Goal" :in-theory (e/d (aignet-idp)
                                   (aignet-build-cut))
            :use ((:instance cutsdb-consistent-implies-cut-value
                   (bitarr (aignet-record-vals nil invals regvals aignet2))
                   (node node))))))

  (defret aignet-litp-of-aignet-build-cut
    (implies (and (cutsdb-lit-idsp aignet2 cutsdb)
                  ;; (cutsdb-ok cutsdb)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (cut-impl-index-ok cut impl-idx cutsdb rwlib)
                  (rwlib-wfp rwlib))
             (aignet-litp lit new-aignet2))
    :hints(("Goal" :in-theory (enable cut-impl-index-ok)
            :do-not-induct t)))

  (defret lit-id-lte-max-fanin-of-aignet-build-cut
    (implies (and ;; (aignet-copies-in-bounds copy aignet2)
                  (cutsdb-lit-idsp aignet2 cutsdb)
                  ;; (cutsdb-ok cutsdb)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (cut-impl-index-ok cut impl-idx cutsdb rwlib)
                  (rwlib-wfp rwlib))
             (<= (lit-id lit) (fanin-count new-aignet2)))
    :hints(("Goal" :use aignet-litp-of-aignet-build-cut
            :in-theory (e/d (aignet-idp)
                            (aignet-build-cut aignet-litp-of-aignet-build-cut))))
    :rule-classes (:rewrite :linear))

  ;; (defret aignet-copies-in-bounds-of-aignet-build-cut-copy2
  ;;   (implies (and ;; (aignet-copies-in-bounds copy aignet2)
  ;;                 (cutsdb-lit-idsp aignet2 cutsdb)
  ;;                 ;; (cutsdb-ok cutsdb)
  ;;                 (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  ;;                 (cut-impl-index-ok cut impl-idx cutsdb rwlib)
  ;;                 (rwlib-wfp rwlib))
  ;;            (aignet-copies-in-bounds new-copy2 new-aignet2))
  ;;   :hints(("Goal" :in-theory (enable cut-impl-index-ok))))

  (defret copy2-length-of-aignet-build-cut
    (implies (and (<= (num-fanins (rwlib->aigs rwlib)) (len copy2))
                  (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (cut-impl-index-ok cut impl-idx cutsdb rwlib))
             (equal (len new-copy2) (len copy2)))
    :hints(("Goal" :in-theory (enable cut-impl-index-ok))))

  (defret eba-length-of-aignet-build-cut
    (implies (and (<= (num-fanins (rwlib->aigs rwlib)) (len eba))
                  (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (cut-impl-index-ok cut impl-idx cutsdb rwlib))
             (equal (len new-eba) (len eba)))
    :hints(("Goal" :in-theory (enable cut-impl-index-ok))))

  (defret stype-counts-of-aignet-build-cut
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2)))))





;; ==========================================================================================
;; Evaluation method 1: Actually build each truth-table implementation and
;; count how many nodes it adds/newly references; revert the AIG after each
;; test.
;; ==========================================================================================


(define aignet-build-cut-tmp ((cut natp)
                              (impl-idx natp)
                              (eba "mark for copied nodes")
                              (copy2 "mapping from dsd aig indices to aignet2 indices -- writing this here")
                              (cutsdb cutsdb-ok)
                              (rwlib rwlib-wfp)
                              (gatesimp gatesimp-p)
                              (strash2)
                              (aignet2))
  :guard (and ;; (<= (cut-nnodes cutsdb) (lits-length copy))
              ;; (aignet-copies-in-bounds copy aignet2)
          (cutsdb-lit-idsp aignet2 cutsdb)
          (< cut (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
          (b* (((acl2::stobj-get ok)
                ((aignet-tmp (rwlib->aigs rwlib)))
                (and (<= (num-fanins aignet-tmp) (lits-length copy2))
                     (<= (num-fanins aignet-tmp) (eba-length eba))
                     (ec-call (aignet-input-copies-in-bounds copy2 aignet-tmp aignet2))
                     (ec-call (aignet-marked-copies-in-bounds copy2 eba aignet2)))))
            ok)
          (cut-impl-index-ok cut impl-idx cutsdb rwlib))
  :guard-hints (("goal" :in-theory (enable cut-impl-index-ok)))
  :returns (mv (lit litp :rule-classes :type-prescription)
               (new-copy2)
               (new-eba)
               (new-strash2)
               (new-aignet2))
  (b* (((cutinfo cutinf) (cut-infoi cut cutsdb))
       ((acl2::stobj-get lit copy2 eba strash2 aignet2)
        ((truth::npn4arr (rwlib->npns rwlib))
         (smm   (rwlib->cands rwlib))
         (aignet-tmp  (rwlib->aigs rwlib)))
        (b* (((truth::npn4 npn) (truth::get-npn4 cutinf.truth truth::npn4arr))
             (lit (smm-read-lit npn.truth-idx impl-idx smm))
             ((mv eba copy2 strash2 aignet2)
              (aignet-copy-dfs-eba-rec (lit-id lit) aignet-tmp eba copy2 strash2 gatesimp aignet2))
             (new-lit (lit-negate-cond (lit-copy lit copy2) npn.negate)))
          (mv new-lit copy2 eba strash2 aignet2))))
    (mv lit copy2 eba strash2 aignet2))
  ///
  (def-aignet-preservation-thms aignet-build-cut-tmp :stobjname aignet2)

  (defret aignet-litp-of-aignet-build-cut-tmp
    (implies (and (aignet-input-copies-in-bounds copy2 (rwlib->aigs rwlib) aignet2)
                  (aignet-marked-copies-in-bounds copy2 eba aignet2)
                  (cutsdb-lit-idsp aignet2 cutsdb)
                  ;; (cutsdb-ok cutsdb)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (cut-impl-index-ok cut impl-idx cutsdb rwlib)
                  (rwlib-wfp rwlib))
             (aignet-litp lit new-aignet2))
    :hints(("Goal" :in-theory (enable cut-impl-index-ok)
            :do-not-induct t)))

  (defret lit-id-lte-max-fanin-of-aignet-build-cut-tmp
    (implies (and (aignet-input-copies-in-bounds copy2 (rwlib->aigs rwlib) aignet2)
                  (aignet-marked-copies-in-bounds copy2 eba aignet2)
                  ;; (aignet-copies-in-bounds copy aignet2)
                  (cutsdb-lit-idsp aignet2 cutsdb)
                  ;; (cutsdb-ok cutsdb)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (cut-impl-index-ok cut impl-idx cutsdb rwlib)
                  (rwlib-wfp rwlib))
             (<= (lit-id lit) (fanin-count new-aignet2)))
    :hints(("Goal" :use aignet-litp-of-aignet-build-cut-tmp
            :in-theory (e/d (aignet-idp)
                            (aignet-build-cut-tmp))))
    :rule-classes (:rewrite :linear))

  (defret aignet-input-copies-in-bounds-of-aignet-build-cut-tmp-copy2
    (implies (and (aignet-input-copies-in-bounds copy2 (rwlib->aigs rwlib) aignet2)
                  ;; (aignet-copies-in-bounds copy aignet2)
                  (cutsdb-lit-idsp aignet2 cutsdb)
                  ;; (cutsdb-ok cutsdb)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (cut-impl-index-ok cut impl-idx cutsdb rwlib)
                  (rwlib-wfp rwlib))
             (aignet-input-copies-in-bounds new-copy2 (rwlib->aigs rwlib) new-aignet2))
    :hints(("Goal" :in-theory (enable cut-impl-index-ok))))

  (defret aignet-marked-copies-in-bounds-of-aignet-build-cut-tmp-copy2
    (implies (and (aignet-input-copies-in-bounds copy2 (rwlib->aigs rwlib) aignet2)
                  (aignet-marked-copies-in-bounds copy2 eba aignet2)
                  ;; (aignet-copies-in-bounds copy aignet2)
                  (cutsdb-lit-idsp aignet2 cutsdb)
                  ;; (cutsdb-ok cutsdb)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (cut-impl-index-ok cut impl-idx cutsdb rwlib)
                  (rwlib-wfp rwlib))
             (aignet-marked-copies-in-bounds new-copy2 new-eba new-aignet2))
    :hints(("Goal" :in-theory (enable cut-impl-index-ok))))

  (defret copy2-length-of-aignet-build-cut-tmp
    (implies (and (<= (num-fanins (rwlib->aigs rwlib)) (len copy2))
                  (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (cut-impl-index-ok cut impl-idx cutsdb rwlib))
             (equal (len new-copy2) (len copy2)))
    :hints(("Goal" :in-theory (enable cut-impl-index-ok))))

  (defret eba-length-of-aignet-build-cut-tmp
    (implies (and (<= (num-fanins (rwlib->aigs rwlib)) (len eba))
                  (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (cut-impl-index-ok cut impl-idx cutsdb rwlib))
             (equal (len new-eba) (len eba)))
    :hints(("Goal" :in-theory (enable cut-impl-index-ok))))

  (defret stype-counts-of-aignet-build-cut-tmp
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2)))))


(define maybe-grow-refcounts ((n natp) refcounts)
  :returns (new-refcounts)
  (if (< (u32-length refcounts) (lnfix n))
      (resize-u32 (max 16 (* 2 (lnfix n))) refcounts)
    refcounts)
  ///
  (defret length-of-maybe-grow-refcounts
    (<= (nfix n) (len new-refcounts))
    :rule-classes :linear)

  (local (include-book "std/lists/nth" :dir :system))
  (local (in-theory (enable acl2::nth-when-too-large)))

  (defret nth-nat-equiv-of-maybe-grow-refcounts
    (acl2::nth-nat-equiv new-refcounts refcounts)
    :hints(("Goal" :in-theory (e/d* (acl2::nth-nat-equiv
                                     acl2::arith-equiv-forwarding)
                                    (acl2::inequality-with-nfix-hyp-1
                                     acl2::inequality-with-nfix-hyp-2
                                     acl2::nfix-equal-to-zero))))))

(define maybe-grow-eba ((n natp) eba)
  :returns (new-eba)
  (if (< (eba-length eba) (lnfix n))
      (eba-grow n eba)
    eba)
  ///
  (defret length-of-maybe-grow-eba
    (<= (nfix n) (len new-eba))
    :rule-classes :linear))


(define aignet-count-unreferenced-cone ((n natp)
                                        (aignet)
                                        (eba "marks visited nodes")
                                        (refcounts))
  :guard (and (id-existsp n aignet)
              (not (eql (id->type n aignet) (out-type)))
              (<= (num-fanins aignet) (eba-length eba))
              (<= (num-fanins aignet) (u32-length refcounts)))
  :returns (mv (count natp :rule-classes :type-prescription)
               new-eba)
  :verify-guards nil
  :measure (nfix n)
  
  :prepwork ((local (in-theory (disable lookup-id-in-bounds-when-positive
                                        acl2::update-nth-of-nth-free
                                        bound-when-aignet-idp
                                        lookup-id-implies-aignet-idp
                                        acl2::nfix-equal-to-nonzero
                                        acl2::nth-of-update-nth-diff
                                        acl2::update-nth-of-update-nth-diff
                                        default-car
                                        lookup-id-out-of-bounds
                                        fanin-count-of-atom
                                        acl2::zp-open))))
  (b* (((unless (eql 0 (eba-get-bit n eba)))
        (mv 0 eba))
       (slot0 (id->slot n 0 aignet))
       ((unless (eql (snode->type slot0) (gate-type)))
        (mv 0 eba))
       (refs (get-u32 n refcounts))
       ((unless (eql refs 0))
        (mv 0 eba))
       (eba (eba-set-bit n eba))
       (child0 (lit-id (snode->fanin slot0)))
       (child1 (lit-id (gate-id->fanin1 n aignet)))
       ((mv count1 eba) (aignet-count-unreferenced-cone child1 aignet eba refcounts))
       ((mv count0 eba) (aignet-count-unreferenced-cone child0 aignet eba refcounts)))
    (mv (+ 1 count1 count0) eba))
  ///
  (local (defthmd less-than-max-fanin-when-not-output
           (implies (and (aignet-idp n aignet)
                         (not (eql (id->type n aignet) (out-type))))
                    (<= (nfix n) (fanin-count aignet)))
           :hints (("goal" :in-theory (enable aignet-idp)))))
           
                                     

  (defret eba-length-of-aignet-count-unreferenced-cone
    (implies (and (id-existsp n aignet)
                  (not (eql (id->type n aignet) (out-type)))
                  (<= (num-fanins aignet) (len eba)))
             (equal (len new-eba) (len eba)))
    :hints (("goal" :induct <call>
             :in-theory (e/d ()
                             ((:d aignet-count-unreferenced-cone)
                              acl2::nfix-equal-to-zero
                              POSP-WHEN-CONSP-OF-LOOKUP-ID))
             :expand (<call>))
            (and stable-under-simplificationp
                 '(:use ((:instance less-than-max-fanin-when-not-output))))))

  (verify-guards aignet-count-unreferenced-cone
    :hints ((and stable-under-simplificationp
                 '(:use ((:instance less-than-max-fanin-when-not-output)))))))




(define eval-cut-implementation ((cut natp)
                                 (impl-idx natp)
                                 (eba "mark for copied nodes")
                                 (copy2 "mapping from dsd aig indices to aignet2 indices -- writing this here")
                                 (cutsdb cutsdb-ok)
                                 (rwlib rwlib-wfp)
                                 (gatesimp gatesimp-p)
                                 (strash2)
                                 (aignet2)
                                 (eba2 "scratch for counting unreferenced nodes in aignet2")
                                 (refcounts2 "refcounts for aignet2")
                                 ;; (rewrite-stats)
                                 ;; (config rewrite-config-p)
                                 )
  :guard (and ;; (<= (cut-nnodes cutsdb) (lits-length copy))
              ;; (aignet-copies-in-bounds copy aignet2)
              (cutsdb-lit-idsp aignet2 cutsdb)
              (< cut (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (b* (((acl2::stobj-get ok)
                    ((aignet-tmp (rwlib->aigs rwlib)))
                    (and (<= (num-fanins aignet-tmp) (lits-length copy2))
                         (<= (num-fanins aignet-tmp) (eba-length eba))
                         (ec-call (aignet-input-copies-in-bounds copy2 aignet-tmp aignet2))
                         (ec-call (aignet-marked-copies-in-bounds copy2 eba aignet2)))))
                ok)
              (cut-impl-index-ok cut impl-idx cutsdb rwlib))
  :returns (mv (cost natp :rule-classes :type-prescription)
               (new-eba2)
               (new-refcounts2 (acl2::nth-nat-equiv new-refcounts2 refcounts2))
               (new-eba)
               (new-copy2)
               (new-strash2)
               (new-aignet2))
  ;; :verify-guards nil
  (b* (((mv lit copy2 eba strash2 aignet2)
        (aignet-build-cut-tmp cut impl-idx eba copy2 cutsdb rwlib gatesimp strash2 aignet2))
       (refcounts2 (maybe-grow-refcounts (num-fanins aignet2) refcounts2))
       (eba2 (maybe-grow-eba (num-fanins aignet2) eba2))
       (eba2 (eba-clear eba2))
       ((mv count eba2) (aignet-count-unreferenced-cone (lit-id lit) aignet2 eba2 refcounts2)))
    (mv count eba2 refcounts2 eba copy2 strash2 aignet2))
  ///
  (def-aignet-preservation-thms eval-cut-implementation :stobjname aignet2)

  ;; (defret aignet-litp-of-eval-cut-implementation
  ;;   (implies (and (aignet-copies-in-bounds copy2 aignet2)
  ;;                 (cutsdb-lit-idsp aignet2 cutsdb)
  ;;                 ;; (cutsdb-ok cutsdb)
  ;;                 (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  ;;                 (cut-impl-index-ok cut impl-idx cutsdb rwlib)
  ;;                 (rwlib-wfp rwlib))
  ;;            (aignet-litp lit new-aignet2))
  ;;   :hints(("Goal" :in-theory (enable cut-impl-index-ok)
  ;;           :do-not-induct t)))

  ;; (defret lit-id-lte-max-fanin-of-eval-cut-implementation
  ;;   (implies (and (aignet-copies-in-bounds copy2 aignet2)
  ;;                 ;; (aignet-copies-in-bounds copy aignet2)
  ;;                 (cutsdb-lit-idsp aignet2 cutsdb)
  ;;                 ;; (cutsdb-ok cutsdb)
  ;;                 (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  ;;                 (cut-impl-index-ok cut impl-idx cutsdb rwlib)
  ;;                 (rwlib-wfp rwlib))
  ;;            (<= (lit-id lit) (fanin-count new-aignet2)))
  ;;   :hints(("Goal" :use aignet-litp-of-eval-cut-implementation
  ;;           :in-theory (disable eval-cut-implementation)))
  ;;   :rule-classes (:rewrite :linear))

  (defret aignet-copies-in-bounds-of-eval-cut-implementation-copy2
    (implies (and (aignet-input-copies-in-bounds copy2 (rwlib->aigs rwlib) aignet2)
                  ;; (aignet-copies-in-bounds copy aignet2)
                  (cutsdb-lit-idsp aignet2 cutsdb)
                  ;; (cutsdb-ok cutsdb)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (cut-impl-index-ok cut impl-idx cutsdb rwlib)
                  (rwlib-wfp rwlib))
             (and (aignet-input-copies-in-bounds new-copy2 (rwlib->aigs rwlib) new-aignet2)
                  (implies (aignet-marked-copies-in-bounds copy2 eba aignet2)
                           (aignet-marked-copies-in-bounds new-copy2 new-eba new-aignet2))))
    :hints(("Goal" :in-theory (enable cut-impl-index-ok))))

  (defret copy2-length-of-eval-cut-implementation
    (implies (and (<= (num-fanins (rwlib->aigs rwlib)) (len copy2))
                  (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (cut-impl-index-ok cut impl-idx cutsdb rwlib))
             (equal (len new-copy2) (len copy2)))
    :hints(("Goal" :in-theory (enable cut-impl-index-ok))))

  (defret eba-length-of-eval-cut-implementation
    (implies (and (<= (num-fanins (rwlib->aigs rwlib)) (len eba))
                  (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (cut-impl-index-ok cut impl-idx cutsdb rwlib))
             (equal (len new-eba) (len eba)))
    :hints(("Goal" :in-theory (enable cut-impl-index-ok))))

  (defret stype-counts-of-eval-cut-implementation
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))

  (defret refcounts-length-of-eval-cut-implementation
    (< (fanin-count new-aignet2) (len new-refcounts2))
    :rule-classes :linear))

(define eval-cut-implementations ((cut natp)
                                  (impl-idx natp)
                                  (blocksize natp)
                                  (eba "mark for copied nodes")
                                  (copy2 "mapping from dsd aig indices to aignet2 indices -- writing this here")
                                  (cutsdb cutsdb-ok)
                                  (rwlib rwlib-wfp)
                                  (strash2)
                                  (aignet2)
                                  (eba2 "scratch for counting unreferenced nodes in aignet2")
                                  (refcounts2 "refcounts for aignet2")
                                  (rewrite-stats)
                                  (config rewrite-config-p)
                                  )
  :guard (and ;; (<= (cut-nnodes cutsdb) (lits-length copy))
              ;; (aignet-copies-in-bounds copy aignet2)
              (cutsdb-lit-idsp aignet2 cutsdb)
              (< cut (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (< impl-idx blocksize)
              (b* (((cutinfo cutinf) (cut-infoi cut cutsdb))
                   ((acl2::stobj-get ok)
                    ((aignet-tmp (rwlib->aigs rwlib))
                     (npn4arr (rwlib->npns rwlib))
                     (smm (rwlib->cands rwlib)))
                    (b* (((truth::npn4 npn) (get-npn4 cutinf.truth npn4arr)))
                      (and (<= (num-fanins aignet-tmp) (lits-length copy2))
                           (<= (num-fanins aignet-tmp) (eba-length eba))
                           (equal blocksize (smm-block-size npn.truth-idx smm))
                           (ec-call (aignet-input-copies-in-bounds copy2 aignet-tmp aignet2))
                           (ec-call (aignet-marked-copies-in-bounds copy2 eba aignet2))))))
                ok))
  :returns (mv (best-impl natp)
               (cost natp :rule-classes :type-prescription)
               (new-eba2)
               (new-refcounts2 (acl2::nth-nat-equiv new-refcounts2 refcounts2))
               (new-eba)
               (new-copy2)
               (new-strash2)
               (new-aignet2)
               (new-rewrite-stats))
  :measure (b* (((cutinfo cutinf) (cut-infoi cut cutsdb))
                ((acl2::stobj-get size)
                 ((npn4arr (rwlib->npns rwlib))
                  (smm (rwlib->cands rwlib)))
                 (b* (((truth::npn4 npn) (get-npn4 cutinf.truth npn4arr)))
                   (smm-block-size npn.truth-idx smm))))
             (nfix (- size (nfix impl-idx))))
  :verify-guards nil
  (b* ((blocksize (mbe :logic (b* (((cutinfo cutinf) (cut-infoi cut cutsdb))
                                   ((acl2::stobj-get size)
                                    ((npn4arr (rwlib->npns rwlib))
                                     (smm (rwlib->cands rwlib)))
                                    (b* (((truth::npn4 npn) (get-npn4 cutinf.truth npn4arr)))
                                      (smm-block-size npn.truth-idx smm))))
                                size)
                       :exec blocksize))
       (impl-idx (lnfix impl-idx))
       (rewrite-stats (incr-rewrite-stats-tries rewrite-stats))
       ((rewrite-config config))
       ((mv cost eba2 refcounts2 eba copy2 strash2 aignet2)
        (eval-cut-implementation cut impl-idx eba copy2 cutsdb rwlib config.gatesimp strash2 aignet2 eba2 refcounts2))
       (next (1+ impl-idx))
       ((when (or (eql next config.cut-tries-limit)
                  (mbe :logic (zp (- blocksize next))
                       :exec (eql next blocksize))))
        (mv impl-idx cost eba2 refcounts2 eba copy2 strash2 aignet2 rewrite-stats))
       ((mv best-impl best-cost eba2 refcounts2 eba copy2 strash2 aignet2 rewrite-stats)
        (eval-cut-implementations cut next blocksize eba copy2 cutsdb rwlib strash2 aignet2 eba2 refcounts2 rewrite-stats config))
       ((when (<= cost best-cost))
        (mv impl-idx cost eba2 refcounts2 eba copy2 strash2 aignet2 rewrite-stats)))
    (mv best-impl best-cost eba2 refcounts2 eba copy2 strash2 aignet2 rewrite-stats))
  ///
  (verify-guards eval-cut-implementations
    :hints(("Goal" :in-theory (enable cut-impl-index-ok))))

  (def-aignet-preservation-thms eval-cut-implementations :stobjname aignet2)


  (defret aignet-copies-in-bounds-of-eval-cut-implementations-copy2
    (implies (and (aignet-input-copies-in-bounds copy2 (rwlib->aigs rwlib) aignet2)
                  ;; (aignet-copies-in-bounds copy aignet2)
                  (cutsdb-lit-idsp aignet2 cutsdb)
                  ;; (cutsdb-ok cutsdb)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (cut-impl-index-ok cut impl-idx cutsdb rwlib)
                  (rwlib-wfp rwlib))
             (and (aignet-input-copies-in-bounds new-copy2 (rwlib->aigs rwlib) new-aignet2)
                  (implies (aignet-marked-copies-in-bounds copy2 eba aignet2)
                           (aignet-marked-copies-in-bounds new-copy2 new-eba new-aignet2))))
    :hints(("Goal" :in-theory (enable cut-impl-index-ok))))

  (defret copy2-length-of-eval-cut-implementations
    (implies (and (<= (num-fanins (rwlib->aigs rwlib)) (len copy2))
                  (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (cut-impl-index-ok cut impl-idx cutsdb rwlib))
             (equal (len new-copy2) (len copy2)))
    :hints(("Goal" :in-theory (enable cut-impl-index-ok))))

  (defret eba-length-of-eval-cut-implementations
    (implies (and (<= (num-fanins (rwlib->aigs rwlib)) (len eba))
                  (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (cut-impl-index-ok cut impl-idx cutsdb rwlib))
             (equal (len new-eba) (len eba)))
    :hints(("Goal" :in-theory (enable cut-impl-index-ok))))

  (defret stype-counts-of-eval-cut-implementations
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))

  (defret refcounts-length-of-eval-cut-implementations
    (< (fanin-count new-aignet2) (len new-refcounts2))
    :rule-classes ((:linear :trigger-terms ((len new-refcounts2)))))

  (defret eval-cut-implementations-best-impl-lower-bound
    (<= (nfix impl-idx) best-impl)
    :rule-classes :linear)

  (defret eval-cut-implementations-best-impl-bound
    (b* (((cutinfo cutinf) (cut-infoi cut cutsdb))
         ((acl2::stobj-get size)
          ((npn4arr (rwlib->npns rwlib))
           (smm (rwlib->cands rwlib)))
          (b* (((truth::npn4 npn) (get-npn4 cutinf.truth npn4arr)))
            (smm-block-size npn.truth-idx smm))))
      (implies (< (nfix impl-idx) size)
               (< best-impl size)))
    :rule-classes :linear))
             

(define strash-delete-nodes-above ((n natp) (strash) (aignet))
  :guard (<= n (num-fanins aignet))
  :measure (nfix (- (num-fanins aignet) (nfix n)))
  :returns (new-strash)
  :guard-hints (("goal" :in-theory (enable aignet-idp)))

  :prepwork ((local (defthmd unsigned-byte-p-of-lit-when-lit->var
                      (implies (and (unsigned-byte-p (+ -1 n) (lit->var lit))
                                    (litp lit)
                                    (posp n))
                               (unsigned-byte-p n lit))
                      :hints(("Goal" :in-theory (enable lit->var)))
                      :rule-classes ((:rewrite :backchain-limit-lst (3 nil nil)))))

             (local (defthm unsigned-byte-p-of-lit->var-when-aignet-litp
                      (implies (and (aignet-litp lit aignet)
                                    (< (fanin-count aignet) #x1fffffff))
                               (unsigned-byte-p 29 (lit->var lit)))
                      :hints(("Goal" :in-theory (enable unsigned-byte-p aignet-idp)))))
             
             (local (defthm unsigned-byte-p-when-aignet-litp
                      (implies (and (aignet-litp lit aignet)
                                    (litp lit)
                                    (< (fanin-count aignet) #x1fffffff))
                               (unsigned-byte-p 30 lit))
                      :hints(("Goal" :in-theory (enable unsigned-byte-p-of-lit-when-lit->var)))))

             (local (defthm unsigned-byte-p-of-fanin
                      (implies (< (fanin-count aignet) #x1fffffff)
                               (unsigned-byte-p 30 (fanin type (lookup-id id aignet))))
                      :hints(("Goal" :use ((:instance unsigned-byte-p-when-aignet-litp
                                            (lit (fanin type (lookup-id id aignet)))))
                              :in-theory (disable unsigned-byte-p-when-aignet-litp))))))
  (b* (((when (mbe :logic (zp (- (num-fanins aignet) (nfix n)))
                   :exec (eql (num-fanins aignet) n)))
        strash)
       (slot0 (id->slot n 0 aignet))
       (type (snode->type slot0))
       ((unless (eql type (gate-type)))
        (strash-delete-nodes-above (1+ (lnfix n)) strash aignet))
       (key (aignet-addr-combine (snode->fanin slot0)
                                 (gate-id->fanin1 n aignet)))
       (strash (strashtab-rem key strash)))
    (strash-delete-nodes-above (1+ (lnfix n)) strash aignet)))

;; (local (defthm stype-count-of-lookup-fanin-count
;;          (implies (not (equal (ctype stype) (out-ctype)))
;;                   (equal (stype-count stype (lookup-id (fanin-count aignet) aignet))
;;                          (stype-count stype aignet)))
;;          :hints(("Goal" :in-theory (enable stype-count lookup-id fanin-count fanin-node-p)))))

(local (defthm lookup-fanin-count-when-no-cos
         (implies (and (equal (stype-count :po aignet) 0)
                       (equal (stype-count :nxst aignet) 0))
                  (equal (lookup-id (fanin-count aignet) aignet)
                         (node-list-fix aignet)))
         :hints(("Goal" :in-theory (enable stype-count lookup-id fanin-count fanin-node-p ctype)))))

(define eval-cut-build ((cut natp)
                        (node natp)
                        (eba "mark for copied nodes")
                        (copy2 "mapping from dsd aig indices to aignet2 indices -- writing this here")
                        (cutsdb cutsdb-ok)
                        (rwlib rwlib-wfp)
                        (strash2)
                        (aignet2)
                        (eba2 "scratch for counting unreferenced nodes in aignet2")
                        (refcounts2 "refcounts for aignet2")
                        (rewrite-stats)
                        (config rewrite-config-p)
                        )
  :guard (and ;; (<= (cut-nnodes cutsdb) (lits-length copy))
              ;; (aignet-copies-in-bounds copy aignet2)
              (cutsdb-lit-idsp aignet2 cutsdb)
              (< cut (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (equal (num-nxsts aignet2) 0)
              (equal (num-outs aignet2) 0)
              (b* (((acl2::stobj-get ok)
                    ((aignet-tmp (rwlib->aigs rwlib)))
                    (and (<= (num-fanins aignet-tmp) (lits-length copy2))
                         (<= (num-fanins aignet-tmp) (eba-length eba)))))
                ok))
  :returns (mv (ok)
               (best-impl natp)
               (cost natp :rule-classes :type-prescription)
               (new-eba2)
               (new-refcounts2 (acl2::nth-nat-equiv new-refcounts2 refcounts2))
               (new-eba)
               (new-copy2)
               (new-strash2)
               (new-aignet2)
               (new-rewrite-stats))
  :guard-hints (("goal" :in-theory (enable cut-impl-index-ok)))
  (b* (((cutinfo cutinf) (cut-infoi cut cutsdb))
       (aignet2 (mbe :logic (non-exec (lookup-id (fanin-count aignet2) aignet2))
                     :exec aignet2))
       ((when (and (eql cutinf.size 0)
                   (cut-impl-index-ok cut 0 cutsdb rwlib)))
        ;; shortcut for const0 node
        (mv t 0 0 eba2 refcounts2 eba copy2 strash2 aignet2 rewrite-stats))
       ((unless (and cutinf.valid
                     (cut-leaves-bounded cut node cutsdb)
                     (cut-impl-index-ok cut 0 cutsdb rwlib)))
        (mv nil 0 0 eba2 refcounts2 eba copy2 strash2 aignet2 rewrite-stats))
       (copy2 (cut-initialize-copy cut copy2 cutsdb rwlib))
       (eba (eba-clear eba))
       (nnodes (num-fanins aignet2))
       ((acl2::stobj-get blocksize)
        ((npn4arr (rwlib->npns rwlib))
         (smm (rwlib->cands rwlib)))
        (b* (((truth::npn4 npn) (get-npn4 cutinf.truth npn4arr)))
          (smm-block-size npn.truth-idx smm)))
       ((mv impl cost eba2 refcounts2 eba copy2 strash2 aignet2 rewrite-stats)
        (eval-cut-implementations cut 0 blocksize eba copy2 cutsdb
                                  rwlib strash2 aignet2 eba2 refcounts2 rewrite-stats config))
       (strash2 (strash-delete-nodes-above nnodes strash2 aignet2))
       (aignet2 (aignet-rollback nnodes aignet2)))
    (mv t impl cost eba2 refcounts2 eba copy2 strash2 aignet2 rewrite-stats))
  ///

  (defretd eval-cut-build-ok-implies-cut-leaves-bounded
    (implies ok
             (cut-leaves-bounded cut node cutsdb))
    :hints((and stable-under-simplificationp
                '(:in-theory (enable cut-leaves-bounded leaves-bounded)))))

  (defret eval-cut-build-ok-implies-cut-impl-index-ok
    (implies ok
             (cut-impl-index-ok cut best-impl cutsdb rwlib))
    :hints(("Goal" :in-theory (enable cut-impl-index-ok))))

  (defret eval-cut-build-returns-same-aignet2
    (equal new-aignet2
           (lookup-id (fanin-count aignet2) aignet2))
    :hints(("Goal" :in-theory (enable aignet$a::aignet-rollback
                                      aignet-idp))))

  ;; (defret aignet-copies-in-bounds-of-eval-cut-build-copy2
  ;;   (implies (and (aignet-copies-in-bounds copy2 aignet2)
  ;;                 ;; (aignet-copies-in-bounds copy aignet2)
  ;;                 (cutsdb-lit-idsp aignet2 cutsdb)
  ;;                 ;; (cutsdb-ok cutsdb)
  ;;                 (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  ;;                 (cut-impl-index-ok cut impl-idx cutsdb rwlib)
  ;;                 (rwlib-wfp rwlib))
  ;;            (aignet-copies-in-bounds new-copy2 new-aignet2))
  ;;   :hints(("Goal" :in-theory (enable cut-impl-index-ok))))

  (defret copy2-length-of-eval-cut-build
    (implies (and (<= (num-fanins (rwlib->aigs rwlib)) (len copy2))
                  (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  ;; (cut-impl-index-ok cut impl-idx cutsdb rwlib)
                  )
             (equal (len new-copy2) (len copy2)))
    :hints(("Goal" :in-theory (enable cut-impl-index-ok))))

  (defret eba-length-of-eval-cut-build
    (implies (and (<= (num-fanins (rwlib->aigs rwlib)) (len eba))
                  (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  ;; (cut-impl-index-ok cut impl-idx cutsdb rwlib)
                  )
             (equal (len new-eba) (len eba)))
    :hints(("Goal" :in-theory (enable cut-impl-index-ok))))

  (defret refcounts-length-of-eval-cut-build
    (implies (< (fanin-count aignet2) (len refcounts2))
             (< (fanin-count aignet2) (len new-refcounts2)))
    :rule-classes :linear))


(define choose-implementation-cuts-build ((cuts-start natp)
                                          (cuts-end natp)
                                          (node natp)
                                          (cutsdb cutsdb-ok)
                                          (rwlib rwlib-wfp)
                                          (eba)
                                          (eba2)
                                          (copy2)
                                          (strash2 "strash for aignet2")
                                          (aignet2 "destination")
                                          (refcounts2 "refcounts for aignet2")
                                          (rewrite-stats)
                                          (config rewrite-config-p))
  :guard (and (<= cuts-start cuts-end)
              (<= cuts-end (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (cutsdb-lit-idsp aignet2 cutsdb)
              (equal (num-nxsts aignet2) 0)
              (equal (num-outs aignet2) 0)
              (stobj-let ((aignet (rwlib->aigs rwlib)))
                         (ok)
                         (and (<= (num-fanins aignet) (lits-length copy2))
                              (<= (num-fanins aignet) (eba-length eba)))
                         ok))
  :verify-guards nil
  :returns (mv (ok "if nil, no qualifiying cuts")
               (score natp :rule-classes :type-prescription)
               (cut-index natp :rule-classes :type-prescription)
               (impl-index natp :rule-classes :type-prescription)
               (new-refcounts2 (acl2::nth-nat-equiv new-refcounts2 refcounts2))
               (new-eba)
               (new-eba2)
               (new-copy2)
               (new-strash2)
               (new-aignet2 (equal new-aignet2 (lookup-id (fanin-count aignet2) aignet2)))
               (new-rewrite-stats))
  :measure (nfix (- (nfix cuts-end) (nfix cuts-start)))
  (b* ((aignet2 (mbe :logic (non-exec (lookup-id (fanin-count aignet2) aignet2))
                     :exec aignet2))
       ((when (mbe :logic (zp (- (lnfix cuts-end) (nfix cuts-start)))
                   :exec (eql cuts-start cuts-end)))
        (mv nil 0 0 0 refcounts2 eba eba2 copy2 strash2 aignet2 rewrite-stats))
       ((mv ok1 impl-idx1 score1 eba2 refcounts2 eba copy2 strash2 aignet2 rewrite-stats)
        (eval-cut-build cuts-start node eba copy2 cutsdb rwlib strash2 aignet2 eba2 refcounts2 rewrite-stats config))
       ((when (and ok1 (eql score1 0)))
        ;; early out for 0-cost
        (mv t 0 (lnfix cuts-start) impl-idx1 refcounts2 eba eba2 copy2 strash2 aignet2 rewrite-stats))
       ((unless ok1)
        (choose-implementation-cuts-build
         (1+ (lnfix cuts-start)) cuts-end node cutsdb rwlib
         eba eba2 copy2 strash2 aignet2 refcounts2 rewrite-stats config))
       ((mv ok-rest best-score best-cut-idx best-impl-idx
            refcounts2 eba eba2 copy2 strash2 aignet2 rewrite-stats)
        (choose-implementation-cuts-build
         (1+ (lnfix cuts-start)) cuts-end node cutsdb rwlib
         eba eba2 copy2 strash2 aignet2 refcounts2 rewrite-stats config))
       ((when (or (not ok-rest)
                  (< score1 best-score)))
        (mv ok1 score1 (lnfix cuts-start) impl-idx1 refcounts2 eba eba2 copy2 strash2 aignet2 rewrite-stats)))
    (mv t best-score best-cut-idx best-impl-idx refcounts2 eba eba2 copy2 strash2 aignet2 rewrite-stats))
  ///
  (verify-guards choose-implementation-cuts-build
    :hints(("Goal" :in-theory (enable cut-impl-index-ok))))

  (defret cut-impl-index-ok-of-choose-implementation-cuts-build
    (implies ok
             (and (cut-impl-index-ok cut-index impl-index cutsdb rwlib)
                  (cut-leaves-bounded cut-index node cutsdb)))
    :hints(("Goal" :induct t)
           (and stable-under-simplificationp
                '(:use ((:instance eval-cut-build-ok-implies-cut-leaves-bounded
                         (cut (nfix cuts-start))
                         (aignet2 (lookup-id (fanin-count aignet2) aignet2))))))
           ))

  ;; (defret cutp-of-choose-implemenation-cuts
  ;;   (implies (cutsdb-ok cutsdb)
  ;;            (cutp cut-index cutsdb)))

  (defret cut-bound-of-choose-implemenation-cuts
    (implies ok
             (< cut-index (nfix cuts-end)))
    :rule-classes :linear)

  (defret cut-lower-bound-of-choose-implementation-cuts-build
    (implies ok
             (<= (nfix cuts-start) cut-index))
    :rule-classes :linear)

  
  ;; (defret refcounts-length-of-choose-implementation-cut
  ;;   (implies (and (cutsdb-lit-idsp aignet2 cutsdb)
  ;;                 (<= (nfix cuts-end) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  ;;                 (<= (num-fanins aignet2) (len refcounts2)))
  ;;            (equal (len new-refcounts2) (len refcounts2))))

  (defret refcounts-length-of-choose-implementation-cut
    (implies (< (fanin-count aignet2) (len refcounts2))
             (< (fanin-count aignet2) (len new-refcounts2)))
    :rule-classes :linear)

  (defret copy2-length-of-choose-implementation-cuts-build
    (implies (and (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (<= (nfix cuts-end) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (num-fanins (rwlib->aigs rwlib)) (len copy2)))
             (equal (len new-copy2) (len copy2)))
    :hints(("Goal" :in-theory (e/d (cut-impl-index-ok)
                                   (len)))))

  ;; (defret copy2-in-bounds-of-choose-implementation-cuts-build
  ;;   (implies (and (cutsdb-lit-idsp aignet2 cutsdb)
  ;;                 (<= (nfix cuts-end) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  ;;                 (aignet-copies-in-bounds copy2 aignet2))
  ;;            (aignet-copies-in-bounds new-copy2 aignet2)))

  (defret eba-length-of-choose-implementation-cuts-build
    (implies (and (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (<= (nfix cuts-end) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (num-fanins (rwlib->aigs rwlib)) (len eba)))
             (equal (len new-eba) (len eba)))
    :hints(("Goal" :in-theory (e/d (cut-impl-index-ok)
                                   (len)))))

  ;; (defret eba2-length-of-choose-implementation-cuts-build
  ;;   (implies (and (rwlib-wfp rwlib)
  ;;                 (cutsdb-ok cutsdb)
  ;;                 (<= (nfix cuts-end) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  ;;                 (<= (num-fanins (rwlib->aigs rwlib)) (len eba2)))
  ;;            (equal (len new-eba2) (len eba2)))
  ;;   :hints(("Goal" :in-theory (e/d (cut-impl-index-ok)
  ;;                                  (len)))))
  )



;; ==========================================================================================
;; End Evaluation method 1.
;; ==========================================================================================






  


(define aignet-delete-mffc ((n natp)
                            (aignet)
                            (refcounts))
  ;; MFFC is Maximum Fanout Free Cone.  We traverse the AIG from node n,
  ;; decrementing the number of references at each node we traverse.  But we
  ;; only move on to a node's fanins if that node's reference count decreased
  ;; to 0.  Think of this as garbage collection: we are deleting a reference to
  ;; n, so if its reference count reaches 0 we also remove a reference from
  ;; each of its children.
  :measure (nfix n)
  :returns (mv (mffc-count natp :rule-classes :type-prescription
                           "Number of nodes deleted")
               (new-refcounts))
  :guard (and (id-existsp n aignet)
              (not (eql (id->type n aignet) (out-type)))
              (<= (num-fanins aignet) (u32-length refcounts)))
  :verify-guards nil

  :prepwork ((local (in-theory (disable lookup-id-in-bounds-when-positive
                                        acl2::update-nth-of-nth-free
                                        bound-when-aignet-idp
                                        lookup-id-implies-aignet-idp
                                        acl2::nfix-equal-to-nonzero
                                        acl2::nth-of-update-nth-diff
                                        acl2::update-nth-of-update-nth-diff
                                        default-car
                                        lookup-id-out-of-bounds
                                        fanin-count-of-atom
                                        acl2::zp-open))))
  (b* ((slot0 (id->slot n 0 aignet))
       ((unless (eql (snode->type slot0) (gate-type)))
        (mv 0 refcounts))
       (refs (get-u32 n refcounts))
       ((when (eql refs 0))
        (cw "Programming error -- traversing ~x0 gate with reference count 0~%" n)
        (break$)
        (mv 0 refcounts))
       (new-refs (1- refs))
       (refcounts (set-u32 n new-refs refcounts))
       ((unless (eql new-refs 0))
        (mv 0 refcounts))
       (child0 (lit-id (snode->fanin slot0)))
       (child1 (lit-id (gate-id->fanin1 n aignet)))
       ((mv count0 refcounts) (aignet-delete-mffc child0 aignet refcounts))
       ((mv count1 refcounts) (aignet-delete-mffc child1 aignet refcounts)))
    (mv (+ 1 count0 count1) refcounts))
  ///
  (defret refcounts-length-of-aignet-delete-mffc
    (implies (< (nfix n) (len refcounts))
             (equal (len new-refcounts) (len refcounts))))

  (defret refcounts-length-nondecr-of-aignet-delete-mffc
    (>= (len new-refcounts) (len refcounts))
    :rule-classes :linear)

  (verify-guards aignet-delete-mffc
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defret lookup-greater-of-aignet-delete-mffc
    (implies (< (nfix n) (nfix m))
             (equal (nth m new-refcounts)
                    (nth m refcounts))))

  (defret update-greater-of-aignet-delete-mffc
    (implies (< (nfix n) (nfix m))
             (equal (mv-nth 1 (aignet-delete-mffc n aignet (update-nth m val refcounts)))
                    (update-nth m val (mv-nth 1 (aignet-delete-mffc n aignet refcounts)))))
    :hints(("Goal" :in-theory (enable acl2::update-nth-of-update-nth-diff))))


  (defthm aignet-delete-mffc-nth-nat-equiv-congruence
    (implies (acl2::nth-nat-equiv refcounts refcounts1)
             (acl2::nth-nat-equiv (mv-nth 1 (aignet-delete-mffc n aignet refcounts))
                                  (mv-nth 1 (aignet-delete-mffc n aignet refcounts1))))
    :rule-classes :congruence))


(define aignet-refcounts-ok-rec ((n natp)
                                 (aignet)
                                 (refcounts))
  :measure (nfix n)
  :returns (ok)
  :guard (and (id-existsp n aignet)
              (not (eql (id->type n aignet) (out-type)))
              (<= (num-fanins aignet) (u32-length refcounts)))
  :prepwork ((local (in-theory (disable lookup-id-in-bounds-when-positive
                                        default-car
                                        lookup-id-out-of-bounds))))
  :guard-hints(("Goal" :in-theory (enable aignet-idp)))
  (non-exec
   (b* ((slot0 (id->slot n 0 aignet))
        ((unless (eql (snode->type slot0) (gate-type)))
         t)
        (refs (get-u32 n refcounts))
        ((when (eql refs 0))
         nil)
        (refcounts (set-u32 n (1- refs) refcounts))
        (child0 (lit-id (snode->fanin slot0)))
        (child1 (lit-id (gate-id->fanin1 n aignet))))
     (and (aignet-refcounts-ok-rec child0 aignet refcounts)
          (aignet-refcounts-ok-rec child1 aignet
                                    (mv-nth 1 (aignet-delete-mffc child0 aignet refcounts))))))
  ///
  (defcong acl2::nth-nat-equiv equal (aignet-refcounts-ok-rec n aignet refcounts) 3))

(define aignet-restore-mffc ((n natp)
                             (nrefs natp)
                             (aignet)
                             (refcounts))
  ;; Restore a deleted mffc by incrementing each node's refcount, traversing
  ;; its children if its refcount was 0 to start.
  :measure (nfix n)
  :returns (mv (mffc-count natp :rule-classes :type-prescription)
               (new-refcounts))
  :guard (and (id-existsp n aignet)
              (not (eql (id->type n aignet) (out-type)))
              (<= (num-fanins aignet) (u32-length refcounts)))
  :verify-guards nil
  :prepwork ((local (in-theory (disable lookup-id-in-bounds-when-positive
                                        acl2::update-nth-of-nth-free
                                        bound-when-aignet-idp
                                        lookup-id-implies-aignet-idp
                                        acl2::nfix-equal-to-nonzero
                                        acl2::nth-of-update-nth-diff
                                        acl2::update-nth-of-update-nth-diff
                                        default-car
                                        lookup-id-out-of-bounds
                                        fanin-count-of-atom
                                        acl2::zp-open))))
  (b* ((slot0 (id->slot n 0 aignet))
       ((unless (eql (snode->type slot0) (gate-type)))
        (mv 0 refcounts))
       (refs (get-u32 n refcounts))
       (new-refs (+ (lnfix nrefs) refs))
       (refcounts (set-u32 n new-refs refcounts))
       ((unless (and (eql refs 0) (not (eql new-refs 0))))
        (mv 0 refcounts))
       (child0 (lit-id (snode->fanin slot0)))
       (child1 (lit-id (gate-id->fanin1 n aignet)))
       ((mv count1 refcounts) (aignet-restore-mffc child1 1 aignet refcounts))
       ((mv count0 refcounts) (aignet-restore-mffc child0 1 aignet refcounts)))
    (mv (+ 1 count1 count0) refcounts))
  ///
  (defret refcounts-length-of-aignet-restore-mffc
    (implies (< (nfix n) (len refcounts))
             (equal (len new-refcounts) (len refcounts))))

  (defret refcounts-length-nondecr-of-aignet-restore-mffc
    (>= (len new-refcounts) (len refcounts))
    :rule-classes :linear)

  (verify-guards aignet-restore-mffc
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defthm aignet-restore-mffc-nth-equiv-congruence-refcounts
    (implies (acl2::nth-nat-equiv refcounts refcounts1)
             (acl2::nth-nat-equiv (mv-nth 1 (aignet-restore-mffc n nrefs aignet refcounts))
                                  (mv-nth 1 (aignet-restore-mffc n nrefs aignet refcounts1))))
    :rule-classes :congruence)

  (defret lookup-greater-of-aignet-restore-mffc
    (implies (< (nfix n) (nfix m))
             (equal (nth m new-refcounts)
                    (nth m refcounts))))

  (defret lookup-greater-of-aignet-restore-mffc
    (implies (< (nfix n) (nfix m))
             (equal (nth m new-refcounts)
                    (nth m refcounts))))

  ;; (defun-nx aignet-restore-of-delete-ind (n aignet refcounts)
  ;;   (declare (xargs :measure (nfix n)))
  ;;   (b* ((refs (get-u32 n refcounts))
  ;;        ((when (eql refs 0))
  ;;         (list n aignet refcounts))
  ;;        (new-refs (1- refs))
  ;;        (refcounts (set-u32 n new-refs refcounts))
  ;;        (slot0 (id->slot n 0 aignet))
  ;;        ((unless (and (eql new-refs 0)
  ;;                      (eql (snode->type slot0) (gate-type))))
  ;;         (list n aignet refcounts))
  ;;        (child0 (lit-id (snode->fanin slot0)))
  ;;        (child1 (lit-id (gate-id->fanin1 n aignet)))
  ;;        (?ign1 (aignet-restore-of-delete-ind child0 aignet refcounts))
  ;;        ((mv & refcounts) (aignet-delete-mffc child0 aignet refcounts))
  ;;        (refcounts (set-u32 n refs refcounts)))
  ;;     (aignet-restore-of-delete-ind child1 aignet refcounts)))

  (defret update-greater-of-aignet-restore-mffc
    (implies (< (nfix n) (nfix m))
             (equal (mv-nth 1 (aignet-restore-mffc n nrefs aignet (update-nth m val refcounts)))
                    (update-nth m val (mv-nth 1 (aignet-restore-mffc n nrefs aignet refcounts)))))
    :hints(("Goal" :in-theory (enable acl2::update-nth-of-update-nth-diff))))
    

  (defthm nth-nat-equiv-of-update-when-equiv
    (implies (nat-equiv (nth n x) (nth n y))
             (iff (acl2::nth-nat-equiv (update-nth n v x) (update-nth n v y))
                  (acl2::nth-nat-equiv x y)))
    :hints ((acl2::use-termhint
             (b* ((x1 (update-nth n v x))
                  (y1 (update-nth n v y)))
               (if (acl2::nth-nat-equiv x1 y1)
                   `'(:expand ((acl2::nth-nat-equiv x y))
                      :use ((:instance acl2::nth-nat-equiv-necc
                             (n (acl2::nth-nat-equiv-witness x y))
                             (x ,(hq x1))
                             (y ,(hq y1))))
                      :in-theory (e/d* (acl2::arith-equiv-forwarding)
                                       (acl2::nth-nat-equiv-necc
                                        acl2::nth-nat-equiv-implies-nat-equiv-nth-2)))
                 `'(:expand ((acl2::nth-nat-equiv ,(hq x1) ,(hq y1)))))))))
                  

  (defthm aignet-delete-mffc-of-aignet-restore-mffc
    (acl2::nth-nat-equiv (mv-nth 1 (aignet-delete-mffc n aignet (mv-nth 1 (aignet-restore-mffc n 1 aignet refcounts))))
                         refcounts)
    :hints(("Goal" :in-theory (e/d* ((:i aignet-restore-mffc)
                                     acl2::arith-equiv-forwarding)
                                    ((:d aignet-restore-mffc)))
            :induct (aignet-restore-mffc n 1 aignet refcounts)
            :expand ((aignet-restore-mffc n 1 aignet refcounts)
                     (:free (refcounts) (aignet-delete-mffc n aignet refcounts))))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause)))))))

  (defthm aignet-restore-mffc-of-aignet-delete-mffc
    (implies (aignet-refcounts-ok-rec n aignet refcounts)
             (acl2::nth-nat-equiv (mv-nth 1 (aignet-restore-mffc n 1 aignet (mv-nth 1 (aignet-delete-mffc n aignet refcounts))))
                                  refcounts))
    :hints(("Goal" :in-theory (e/d* ((:i aignet-delete-mffc)
                                     acl2::arith-equiv-forwarding)
                                    (aignet-restore-mffc))
            :induct (aignet-delete-mffc n aignet refcounts)
            :expand ((aignet-delete-mffc n aignet refcounts)
                     (aignet-refcounts-ok-rec n aignet refcounts)
                     (:free (refcounts) (aignet-restore-mffc n 1 aignet refcounts))))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause))))))))



;; (define my-aignet-delete-mffc ((n natp)
;;                                (aignet)
;;                                (refcounts))
;;   ;; MFFC is Maximum Fanout Free Cone.  We traverse the AIG from node n,
;;   ;; decrementing the number of references at each node we traverse.  But we
;;   ;; only move on to a node's fanins if that node's reference count decreased
;;   ;; to 0.  Think of this as garbage collection: we are deleting a reference to
;;   ;; n, so if its reference count reaches 0 we also remove a reference from
;;   ;; each of its children.
;;   :measure (nfix n)
;;   :guard (and (id-existsp n aignet)
;;               (not (eql (id->type n aignet) (out-type)))
;;               (<= (num-fanins aignet) (u32-length refcounts)))
;;   :verify-guards nil
;;   (b* ((slot0 (id->slot n 0 aignet))
;;        ((unless (eql (snode->type slot0) (gate-type)))
;;         (mv 0 refcounts))
;;        (refs (get-u32 n refcounts))
;;        ((when (eql refs 0))
;;         (cw "Programming error -- traversing ~x0 gate with reference count 0~%" n)
;;         (break$)
;;         (mv 0 refcounts))
;;        (new-refs (1- refs))
;;        (refcounts (set-u32 n new-refs refcounts))
;;        ((unless (eql new-refs 0))
;;         (mv 0 refcounts))
;;        (child0 (lit-id (snode->fanin slot0)))
;;        (child1 (lit-id (gate-id->fanin1 n aignet)))
;;        ((mv count0 refcounts) (my-aignet-delete-mffc child0 aignet refcounts))
;;        ((mv count1 refcounts) (my-aignet-delete-mffc child1 aignet refcounts)))
;;     (mv (+ 1 count0 count1) refcounts))
;;   ///
;;   (skip-proofs
;;    (defthm my-aignet-delete-mffc-equals
;;      (equal (my-aignet-delete-mffc n aignet refcounts)
;;             (aignet-delete-mffc n aignet refcounts))
;;      :hints(("Goal" :in-theory (enable aignet-delete-mffc)))))

;;   (verify-guards my-aignet-delete-mffc
;;     :hints(("Goal" :in-theory (enable aignet-idp aignet-litp)
;;             :use ((:instance id-less-than-max-fanin-when-aignet-litp
;;                    (lit (mk-lit n 0))))))))

;; (define my-aignet-restore-mffc ((n natp)
;;                                 (nrefs natp)
;;                             (aignet)
;;                             (refcounts))
;;   ;; Restore a deleted mffc by incrementing each node's refcount, traversing
;;   ;; its children if its refcount was 0 to start.
;;   :measure (nfix n)
;;   :guard (and (id-existsp n aignet)
;;               (not (eql (id->type n aignet) (out-type)))
;;               (<= (num-fanins aignet) (u32-length refcounts)))
;;   :verify-guards nil
;;   (b* ((slot0 (id->slot n 0 aignet))
;;        ((unless (eql (snode->type slot0) (gate-type)))
;;         (mv 1 refcounts))
;;        (refs (get-u32 n refcounts))
;;        (new-refs (+ (lnfix nrefs) refs))
;;        (refcounts (set-u32 n new-refs refcounts))
;;        ((unless (and (eql refs 0) (not (eql new-refs 0))))
;;         (mv 0 refcounts))
;;        (child0 (lit-id (snode->fanin slot0)))
;;        (child1 (lit-id (gate-id->fanin1 n aignet)))
;;        ((mv count1 refcounts) (my-aignet-restore-mffc child1 1 aignet refcounts))
;;        ((mv count0 refcounts) (my-aignet-restore-mffc child0 1 aignet refcounts)))
;;     (mv (+ 1 count1 count0) refcounts))
;;   ///
;;   (skip-proofs
;;    (defthm my-aignet-restore-mffc-equals
;;      (equal (my-aignet-restore-mffc n nrefs aignet refcounts)
;;             (aignet-restore-mffc n nrefs aignet refcounts))
;;      :hints(("Goal" :in-theory (enable aignet-restore-mffc)))))

;;   (verify-guards my-aignet-restore-mffc
;;     :hints(("Goal" :in-theory (enable aignet-idp aignet-litp)
;;             :use ((:instance id-less-than-max-fanin-when-aignet-litp
;;                    (lit (mk-lit n 0))))))))






;; (define aignet-and-gate-simp/strash-check ((x0 litp)
;;                                            (x1 litp)
;;                                            (gatesimp gatesimp-p :type (unsigned-byte 6))
;;                                            (strash)
;;                                            (aignet))
;;   :guard (and (fanin-litp x0 aignet)
;;               (fanin-litp x1 aignet))
;;   :enabled t
;;   :guard-hints (("goal" :in-theory (enable unsigned-byte-p)))
;;   (mbe :logic (aignet-and-gate-simp/strash x0 x1 gatesimp strash aignet)
;;        :exec (if (and (<= x0 #x3fffffff)
;;                       (<= x1 #x3fffffff))
;;                  (aignet-and-gate-simp/strash x0 x1 gatesimp strash aignet)
;;                (ec-call (aignet-and-gate-simp/strash x0 x1 gatesimp strash aignet)))))

;; (define aignet-xor-gate-simp/strash-check ((x0 litp)
;;                                            (x1 litp)
;;                                            (gatesimp gatesimp-p :type (unsigned-byte 6))
;;                                            (strash)
;;                                            (aignet))
;;   :guard (and (fanin-litp x0 aignet)
;;               (fanin-litp x1 aignet))
;;   :enabled t
;;   :guard-hints (("goal" :in-theory (enable unsigned-byte-p)))
;;   (mbe :logic (aignet-xor-gate-simp/strash x0 x1 gatesimp strash aignet)
;;        :exec (if (and (<= x0 #x3fffffff)
;;                       (<= x1 #x3fffffff))
;;                  (aignet-xor-gate-simp/strash x0 x1 gatesimp strash aignet)
;;                (ec-call (aignet-xor-gate-simp/strash x0 x1 gatesimp strash aignet)))))







  

;; ==========================================================================================
;; Evaluation method 2:  Don't build any new nodes onto the AIG while evaluating implementations,
;; but track which implememetation nodes correspond to existing AIG nodes and count
;; the nonexistent implementation nodes plus the existing but unreferenced ones.
;; ==========================================================================================

;; (local (defthm unsigned-byte-of-lit-negate-cond
;;          (implies (unsigned-byte-p 30 (lit-fix lit))
;;                   (unsigned-byte-p 30 (lit-negate-cond lit neg)))
;;          :hints(("Goal" :in-theory (enable lit-negate-cond make-lit lit->var lit->neg lit-fix))
;;                 (and stable-under-simplificationp
;;                      '(:in-theory (enable b-xor))))))

(local (in-theory (disable aignet-mark-comb-invar-necc
                           aignet-mark-seq-invar-necc)))

(define eval-cut-implementation-copy-rec ((lit litp "node to copy from the rwlib aignet")
                                          (aignet "rwlib aignet -- source of the copy")
                                          (eba "mark nodes we've already attempted to copy")
                                          (eba2 "mark nodes with valid copies")
                                          (copy2 "mapping from aignet to aignet2")
                                          (gatesimp gatesimp-p)
                                          (strash2 "strash for aignet2")
                                          (aignet2 "destination"))
  :guard (and (fanin-litp lit aignet)
              (ec-call (aignet-marked-copies-in-bounds copy2 eba2 aignet2))
              (ec-call (aignet-input-copies-in-bounds copy2 aignet aignet2))
              (<= (num-fanins aignet) (lits-length copy2))
              (<= (num-fanins aignet) (eba-length eba))
              (<= (num-fanins aignet) (eba-length eba2)))
  :returns (mv (new-eba)
               (new-eba2)
               (new-copy2))
  :measure (lit-id lit)
  :verify-guards nil
  :prepwork ((local (in-theory (disable lookup-id-in-bounds-when-positive
                                        default-car
                                        lookup-id-out-of-bounds
                                        acl2::natp-posp
                                        fanin-count-of-atom))))
  (b* ((id (lit-id lit))
       ((when (eql 1 (eba-get-bit id eba)))
        (mv eba eba2 copy2))
       (slot0 (id->slot id 0 aignet))
       (gatep (eql (snode->type slot0) (gate-type)))
       ((unless gatep)
        (b* ((eba (eba-set-bit id eba))
             (eba2 (eba-set-bit id eba2))
             (copy2 (if (eql (snode->type slot0) (const-type))
                        (set-lit id 0 copy2)
                      copy2)))
          (mv eba eba2 copy2)))
       (fanin0 (snode->fanin slot0))
       (slot1 (id->slot id 1 aignet))
       (fanin1 (snode->fanin slot1))
       ((mv eba eba2 copy2)
        (eval-cut-implementation-copy-rec fanin0 aignet eba eba2 copy2 gatesimp strash2 aignet2))
       ((mv eba eba2 copy2)
        (eval-cut-implementation-copy-rec fanin1 aignet eba eba2 copy2 gatesimp strash2 aignet2))
       (eba (eba-set-bit id eba))
       (fanin-copy0 (lit-copy fanin0 copy2))
       (fanin-copy1 (lit-copy fanin1 copy2))
       (xor (eql 1 (snode->regp slot1)))
       ((when (and (not xor)
                   (or (and (eql fanin-copy0 0) (eql 1 (eba-get-bit (lit-id fanin0) eba2)))
                       (and (eql fanin-copy1 0) (eql 1 (eba-get-bit (lit-id fanin1) eba2))))))
        (b* ((copy2 (set-lit id 0 copy2))
             (eba2 (eba-set-bit id eba2)))
          (mv eba eba2 copy2)))
       ((unless (and (eql 1 (eba-get-bit (lit-id fanin0) eba2))
                     (eql 1 (eba-get-bit (lit-id fanin1) eba2))))
        (mv eba eba2 copy2))
       ((mv code ?key lit1 ?lit2)
        (if xor
            (aignet-xor-gate-simp/strash fanin-copy0 fanin-copy1 gatesimp strash2 aignet2)
          (aignet-and-gate-simp/strash fanin-copy0 fanin-copy1 gatesimp strash2 aignet2)))
       ((unless (eql 1 (simpcode->identity code)))
        (mv eba eba2 copy2))
       (copy2 (set-lit id (lit-negate-cond lit1 (simpcode->neg code)) copy2))
       (eba2 (eba-set-bit id eba2)))
    (mv eba eba2 copy2))
  ///
  (local (in-theory (disable (:d eval-cut-implementation-copy-rec))))

  (defret eval-cut-implementation-copy-rec-preserves-eba-marks
    (implies (equal 1 (nth n eba))
             (equal (nth n new-eba) 1))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret eval-cut-implementation-copy-rec-preserves-eba2-marks
    (implies (equal 1 (nth n eba2))
             (equal (nth n new-eba2) 1))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret eval-cut-implementation-copy-rec-sets-eba-marks
    (equal (nth (lit->var lit) new-eba) 1)
    :hints (("goal" :expand (<call>))))

  (defret eval-cut-implementation-copy-rec-preserves-eba-marked-lits
    (implies (equal 1 (nth n eba))
             (equal (nth-lit n new-copy2)
                    (nth-lit n copy2)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret eval-cut-implementation-copy-rec-preserves-eba-marked-eba2-bits
    (implies (equal 1 (nth n eba))
             (equal (nth n new-eba2)
                    (nth n eba2)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret eval-cut-implementation-copy-rec-preserves-input-lits
    (implies (equal (id->type n aignet) (in-type))
             (equal (nth-lit n new-copy2)
                    (nth-lit n copy2)))
    :hints (("goal" :induct <call> :expand (<call>))))

  
  (local (defthm stype-lookup-possibilities-comb
              (let ((stype (stype (Car (lookup-id id aignet)))))
                (or (equal (ctype stype) (gate-ctype))
                    (equal (ctype stype) (in-ctype))
                    (equal stype (const-stype))))
              :rule-classes ((:forward-chaining :trigger-terms ((stype (Car (lookup-id id aignet))))))))

  (defret aignet-in/marked-copies-in-bounds-of-eval-cut-implementation-copy-rec
    (implies (and (aignet-input-copies-in-bounds copy2 aignet aignet2)
                  (aignet-litp lit aignet))
             (and (aignet-input-copies-in-bounds new-copy2 aignet aignet2)
                  (implies (aignet-marked-copies-in-bounds copy2 eba2 aignet2)
                           (aignet-marked-copies-in-bounds new-copy2 new-eba2 aignet2))))
    :hints (("goal" :induct <call>
             :expand (<call>))
            ;; (and stable-under-simplificationp
            ;;      '(;; :expand ((aignet-litp lit aignet))
            ;;        :in-theory (enable ctype)))
            ))

  (defret aignet-litp-of-copy-lit-of-eval-cut-implementation-copy-rec
    (implies (and (aignet-input-copies-in-bounds copy2 aignet aignet2)
                  (aignet-marked-copies-in-bounds copy2 eba2 aignet2)
                  (aignet-litp lit aignet)
                  (equal 1 (nth n new-eba2)))
             (aignet-litp (nth-lit n new-copy2) aignet2))
    :hints (("goal" :use aignet-in/marked-copies-in-bounds-of-eval-cut-implementation-copy-rec
             :in-theory (disable aignet-in/marked-copies-in-bounds-of-eval-cut-implementation-copy-rec))))

  (defret copy2-length-of-eval-cut-implementation-copy-rec
    (implies (and (aignet-litp lit aignet)
                  (<= (num-fanins aignet) (len copy2)))
             (equal (len new-copy2) (len copy2)))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :in-theory (enable aignet-idp))))

  (defret eba-length-of-eval-cut-implementation-copy-rec
    (implies (and (aignet-litp lit aignet)
                  (<= (num-fanins aignet) (len eba)))
             (equal (len new-eba) (len eba)))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :in-theory (enable aignet-idp))))

  (defret eba2-length-of-eval-cut-implementation-copy-rec
    (implies (and (aignet-litp lit aignet)
                  (<= (num-fanins aignet) (len eba2)))
             (equal (len new-eba2) (len eba2)))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :in-theory (enable aignet-idp))))


  (local (in-theory (disable len-update-nth
                             acl2::len-of-update-nth)))

  (local (defthm lit->var-of-aignet-and-gate-simp/strash-upper-bound
           (b* (((mv existing & & &) (aignet-and-gate-simp/strash lit0 lit1 gatesimp strash aignet)))
             (implies (aignet-litp existing aignet)
                      (<= (lit->var existing) (fanin-count aignet))))
           :hints(("Goal" :in-theory (enable aignet-idp)))
           :rule-classes :linear))
  ;; (local (defthm lit->var-upper-bound-by-aignet-litp
  ;;          (implies (aignet-litp lit aignet2)
  ;;                   (<= (lit->var lit) (fanin-count aignet2)))
  ;;          :rule-classes :linear))

  (verify-guards eval-cut-implementation-copy-rec
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable aignet-idp))))
    :guard-debug t))


(define cut-impl-find-copies-rec ((lit litp "node to copy from the rwlib aignet")
                                  (aignet "rwlib aignet -- source of the copy")
                                  ;; (eba "mark already visited aignet nodes")
                                  (eba2 "mark aignet nodes whose copy entries are valid")
                                  (eba3 "mark aignet nodes whose cones have already been counted")
                                  (eba4 "mark aignet2 nodes whose cones have already been counted")
                                  (copy2 "mapping from aignet to aignet2")
                                  (aignet2 "destination")
                                  (refcounts2 "refcounts for aignet2"))
  :guard (and (fanin-litp lit aignet)
              (ec-call (aignet-input-copies-in-bounds copy2 aignet aignet2))
              (ec-call (aignet-marked-copies-in-bounds copy2 eba2 aignet2))
              (<= (num-fanins aignet) (lits-length copy2))
              (<= (num-fanins aignet2) (u32-length refcounts2))
              (<= (num-fanins aignet) (eba-length eba2))
              (<= (num-fanins aignet) (eba-length eba3))
              (<= (num-fanins aignet2) (eba-length eba4)))
  :returns (mv (count natp :rule-classes :type-prescription)
               (new-eba3)
               (new-eba4))
  :measure (lit-id lit)
  :verify-guards nil
  :prepwork ((local (in-theory (disable lookup-id-in-bounds-when-positive
                                        default-car
                                        lookup-id-out-of-bounds
                                        acl2::natp-posp
                                        fanin-count-of-atom))))
  (b* ((id (lit-id lit))
       (slot0 (id->slot id 0 aignet))
       ((when (eql 1 (eba-get-bit id eba3)))
        (mv 0 eba3 eba4))
       (eba3 (eba-set-bit id eba3))
       (type (snode->type slot0))
       ((unless (eql type (gate-type)))
        ;; input/const cones are already counted (and marked as referenced) at the cut level
        ;; we know all inputs have to be used because the truth table depends on them all.
        (mv 0 eba3 eba4))
       ((when (eql 1 (eba-get-bit id eba2)))
        (b* ((cone-id (lit-id (get-lit id copy2)))
             ((mv count eba4) (aignet-count-unreferenced-cone cone-id aignet2 eba4 refcounts2)))
          (mv count eba3 eba4)))
       (fanin0 (snode->fanin slot0))
       (fanin1 (gate-id->fanin1 id aignet))
       ((mv count0 eba3 eba4)
        (cut-impl-find-copies-rec fanin0 aignet eba2 eba3 eba4 copy2 aignet2 refcounts2))
       ((mv count1 eba3 eba4)
        (cut-impl-find-copies-rec fanin1 aignet eba2 eba3 eba4 copy2 aignet2 refcounts2)))
    (mv (+ 1 count0 count1) eba3 eba4))
  ///
  (local (in-theory (disable (:d cut-impl-find-copies-rec))))

  (local (defthm input-ctype-when-not-gate-or-const
           (implies (and (not (equal (stype (car (lookup-id id aignet))) (and-stype)))
                         (not (equal (stype (car (lookup-id id aignet))) (xor-stype)))
                         (not (equal (stype (car (lookup-id id aignet))) (const-stype))))
                    (equal (ctype (stype (car (lookup-id id aignet))))
                           :input))
           :hints(("Goal" :in-theory (enable ctype)))))

  (defret eba3-length-of-cut-impl-find-copies-rec
    (implies (and (aignet-litp lit aignet)
                  (<= (num-fanins aignet) (len eba3)))
             (equal (len new-eba3) (len eba3)))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :in-theory (enable aignet-idp))))

  (defret eba4-length-of-cut-impl-find-copies-rec
    (implies (and (aignet-marked-copies-in-bounds copy2 eba2 aignet2)
                  (aignet-input-copies-in-bounds copy2 aignet aignet2)
                  (<= (num-fanins aignet2) (len eba4))
                  (aignet-litp lit aignet))
             (equal (len new-eba4) (len eba4)))
    :hints (("goal" :induct <call>
             :expand (<call>))))

  (local (defthm max-gte-1
           (<= x (max x y))
           :rule-classes :linear))
  (local (defthm max-gte-2
           (<= y (max x y))
           :rule-classes :linear))

  (verify-guards cut-impl-find-copies-rec
    :hints(("Goal" :in-theory (e/d () (max)))
           (and stable-under-simplificationp
                '(:in-theory (enable aignet-idp))))))





(define eval-cut-implementation-nobuild ((lit litp "node to copy from the rwlib aignet")
                                         (aignet "rwlib aignet -- source of the copy")
                                         (eba "mark nodes we've already attempted to copy")
                                         (eba2 "mark nodes with valid copies")
                                         (eba3 "scratch to mark aignet nodes whose cones have already been counted")
                                         (eba4 "scratch to mark aignet2 nodes whose cones have already been counted")
                                         (copy2 "mapping from aignet to aignet2")
                                         (gatesimp gatesimp-p)
                                         (strash2 "strash for aignet2")
                                         (aignet2 "destination")
                                         (refcounts2 "refcounts for aignet2"))
  :guard (and (fanin-litp lit aignet)
              (ec-call (aignet-input-copies-in-bounds copy2 aignet aignet2))
              (ec-call (aignet-marked-copies-in-bounds copy2 eba2 aignet2))
              (<= (num-fanins aignet) (lits-length copy2))
              (<= (num-fanins aignet2) (u32-length refcounts2))
              (<= (num-fanins aignet) (eba-length eba))
              (<= (num-fanins aignet) (eba-length eba2))
              (<= (num-fanins aignet) (eba-length eba3))
              (<= (num-fanins aignet2) (eba-length eba4)))
  :returns (mv (count natp :rule-classes :type-prescription
                      "The count returned here is complicated.  What we want is
                       the count of the implementation nodes that don't yet have
                       copies in aignet2, plus the count of all unreferenced nodes
                       in aignet2 in the cones of the copies for nodes that do have
                       them.")
               (new-eba)
               (new-eba2)
               (new-copy2)
               (new-eba3)
               (new-eba4))
  (b* (((mv eba eba2 copy2)
        (eval-cut-implementation-copy-rec lit aignet eba eba2 copy2 gatesimp strash2 aignet2))
       (eba3 (eba-clear eba3))
       (eba4 (eba-clear eba4))
       ((mv count eba3 eba4)
        (cut-impl-find-copies-rec lit aignet eba2 eba3 eba4 copy2 aignet2 refcounts2)))
    (mv count eba eba2 copy2 eba3 eba4))
  ///
  
  (defret aignet-in/marked-copies-in-bounds-of-eval-cut-implementation-nobuild
    (implies (and (aignet-input-copies-in-bounds copy2 aignet aignet2)
                  (aignet-litp lit aignet))
             (and (aignet-input-copies-in-bounds new-copy2 aignet aignet2)
                  (implies (aignet-marked-copies-in-bounds copy2 eba2 aignet2)
                           (aignet-marked-copies-in-bounds new-copy2 new-eba2 aignet2)))))

  (defret copy2-length-of-eval-cut-implementation-nobuild
    (implies (and (aignet-litp lit aignet)
                  (<= (num-fanins aignet) (len copy2)))
             (equal (len new-copy2) (len copy2))))

  (defret eba-length-of-eval-cut-implementation-nobuild
    (implies (and (aignet-litp lit aignet)
                  (<= (num-fanins aignet) (len eba)))
             (equal (len new-eba) (len eba))))

  (defret eba2-length-of-eval-cut-implementation-nobuild
    (implies (and (aignet-litp lit aignet)
                  (<= (num-fanins aignet) (len eba2)))
             (equal (len new-eba2) (len eba2))))

  (defret eba3-length-of-eval-cut-implementation-nobuild
    (implies (and (aignet-litp lit aignet)
                  (<= (num-fanins aignet) (len eba3)))
             (equal (len new-eba3) (len eba3))))

  (defret eba4-length-of-eval-cut-implementation-nobuild
    (implies (and (aignet-marked-copies-in-bounds copy2 eba2 aignet2)
                  (aignet-input-copies-in-bounds copy2 aignet aignet2)
                  (<= (num-fanins aignet2) (len eba4))
                  (aignet-litp lit aignet))
             (equal (len new-eba4) (len eba4)))))

(encapsulate nil
  (local (include-book "std/lists/nth" :dir :system))
;  (local (in-theory (enable acl2::nth-when-too-large)))
  (defthm smm-contains-aignet-lits-necc-easier
    (implies (and (smm-contains-aignet-lits smm aignet)
                  (< (nfix idx) (len (nth block smm))))
             (aignet-litp (nth idx (nth block smm)) aignet))
    :hints (("goal" :cases ((< (nfix block) (len smm)))))))


(define eval-implementations ((n natp "impl index")
                              (block natp "smm block")
                              (smm "implementation pointer array")
                              (aignet "rwlib aignet -- source of the copy")
                              (eba "mark nodes we've already attempted to copy")
                              (eba2 "mark nodes with valid copies")
                              (eba3 "scratch to mark aignet nodes whose cones have already been counted")
                              (eba4 "scratch to mark aignet2 nodes whose cones have already been counted")
                              (copy2 "mapping from aignet to aignet2")
                              (strash2 "strash for aignet2")
                              (aignet2 "destination")
                              (refcounts2 "refcounts for aignet2")
                              (rewrite-stats)
                              (config rewrite-config-p))
  :guard (and (< block (acl2::smm-nblocks smm))
              (< n (acl2::smm-block-size block smm))
              (ec-call (smm-contains-aignet-lits smm aignet))
              (ec-call (aignet-input-copies-in-bounds copy2 aignet aignet2))
              (ec-call (aignet-marked-copies-in-bounds copy2 eba2 aignet2))
              (<= (num-fanins aignet) (lits-length copy2))
              (<= (num-fanins aignet2) (u32-length refcounts2))
              (<= (num-fanins aignet) (eba-length eba))
              (<= (num-fanins aignet) (eba-length eba2))
              (<= (num-fanins aignet) (eba-length eba3))
              (<= (num-fanins aignet2) (eba-length eba4)))
  :measure (nfix (- (acl2::smm-block-size block smm) (nfix n)))
  :returns (mv (best-index natp :rule-classes :type-prescription)
               (best-cost natp :rule-classes :type-prescription)
               (new-eba)
               (new-eba2)
               (new-copy2)
               (new-eba3)
               (new-eba4)
               (new-rewrite-stats))
  :prepwork ((local (defthm nat-listp-when-u32-listp
                      (implies (acl2::u32-listp x)
                               (nat-listp x))))
             (local (defthm nat-listp-nth-of-u32-list-listp
                      (implies (and (Acl2::u32-list-listp x)
                                    (< (nfix n) (len x)))
                               (nat-listp (nth n x)))
                      :hints(("Goal" :in-theory (enable nth)))))
             (local (defthm litp-nth-of-nat-listp
                      (implies (and (nat-listp x)
                                    (< (nfix n) (len x)))
                               (litp (nth n x)))
                      :hints(("Goal" :in-theory (enable nth))))))
  :verify-guards nil
  (b* ((impl-lit (acl2::smm-read block n smm))
       (rewrite-stats (incr-rewrite-stats-tries rewrite-stats))
       ((rewrite-config config))
       ((mv cost eba eba2 copy2 eba3 eba4)
        (eval-cut-implementation-nobuild impl-lit aignet eba eba2 eba3 eba4 copy2 config.gatesimp strash2 aignet2 refcounts2))
       (next (+ 1 (lnfix n)))
       ((when (or ;; (and (not (eql (lnfix block) 1))
               (eql next config.cut-tries-limit)
               (mbe :logic (zp (- (acl2::smm-block-size block smm) next))
                    :exec (eql next (acl2::smm-block-size block smm)))))
        (mv (lnfix n) cost eba eba2 copy2 eba3 eba4 rewrite-stats))
       ((mv best-n best-cost eba eba2 copy2 eba3 eba4 rewrite-stats)
        (eval-implementations next block smm aignet eba eba2 eba3 eba4 copy2 strash2 aignet2 refcounts2 rewrite-stats config)))
    (if (< cost best-cost)
        (mv (lnfix n) cost eba eba2 copy2 eba3 eba4 rewrite-stats)
      (mv best-n best-cost eba eba2 copy2 eba3 eba4 rewrite-stats)))
  ///
  (verify-guards eval-implementations)

  
  (defret copy2-length-of-eval-implementations
    (implies (and (smm-contains-aignet-lits smm aignet)
                  (< (nfix n) (acl2::smm-block-size block smm))
                  (<= (num-fanins aignet) (len copy2)))
             (equal (len new-copy2) (len copy2))))

  (defret aignet-in/marked-copies-in-bounds-of-eval-implementations
    (implies (and (aignet-input-copies-in-bounds copy2 aignet aignet2)
                  (smm-contains-aignet-lits smm aignet)
                  (< (nfix n) (acl2::smm-block-size block smm)))
             (and (aignet-input-copies-in-bounds new-copy2 aignet aignet2)
                  (implies (aignet-marked-copies-in-bounds copy2 eba2 aignet2)
                           (aignet-marked-copies-in-bounds new-copy2 new-eba2 aignet2)))))

  (defret eba-length-of-eval-implementations
    (implies (and (smm-contains-aignet-lits smm aignet)
                  (< (nfix n) (acl2::smm-block-size block smm))
                  (<= (num-fanins aignet) (len eba)))
             (equal (len new-eba) (len eba))))

  (defret eba2-length-of-eval-implementations
    (implies (and (smm-contains-aignet-lits smm aignet)
                  (< (nfix n) (acl2::smm-block-size block smm))
                  (<= (num-fanins aignet) (len eba2)))
             (equal (len new-eba2) (len eba2))))

  (defret eba3-length-of-eval-implementations
    (implies (and (smm-contains-aignet-lits smm aignet)
                  (< (nfix n) (acl2::smm-block-size block smm))
                  (<= (num-fanins aignet) (len eba3)))
             (equal (len new-eba3) (len eba3))))

  (defret eba4-length-of-eval-implementations
    (implies (and (aignet-marked-copies-in-bounds copy2 eba2 aignet2)
                  (aignet-input-copies-in-bounds copy2 aignet aignet2)
                  (<= (num-fanins aignet2) (len eba4))
                  (smm-contains-aignet-lits smm aignet)
                  (< (nfix n) (acl2::smm-block-size block smm)))
             (equal (len new-eba4) (len eba4))))

  (defret impl-index-ok-of-eval-implementations
    (implies (< (nfix n) (len (nth block smm)))
             (< best-index (len (nth block smm))))
    :rule-classes (:rewrite :linear)))



(define cut-restore-mffcs ((n natp)
                           (size natp)
                           (cutsdb cutsdb-ok)
                           ;; (copy "mapping from cutsdb nodes (aka original aignet nodes) to aignet nodes")
                           (aignet)
                           (refcounts))
  :returns (mv (mffc-count natp :rule-classes :type-prescription)
               (new-refcounts))
  :guard (and (<= (+ n size) (cut-leaves-length cutsdb))
              (leaves-lit-idsp n size aignet cutsdb)
              ;; (aignet-copies-in-bounds copy aignet)
              ;; (<= (cut-nnodes cutsdb) (lits-length copy))
              (<= (num-fanins aignet) (u32-length refcounts)))
  :verify-guards nil
  (b* (((when (zp size))
        (mv 0 refcounts))
       (id (cut-leavesi n cutsdb))
       ;; (lit (get-lit id copy))
       ((mv size1 refcounts) (aignet-restore-mffc id 1 aignet refcounts))
       ((mv rest-size refcounts) (cut-restore-mffcs (1+ (lnfix n)) (1- size) cutsdb aignet refcounts)))
    (mv (+ size1 rest-size) refcounts))
  ///
  (verify-guards cut-restore-mffcs
    :hints (("goal" :expand ((leaves-lit-idsp n size aignet cutsdb))
             :in-theory (enable aignet-idp))))

  ;; (local (defthm lit->var-upper-bound-by-aignet-litp
  ;;          (implies (aignet-litp lit aignet)
  ;;                   (<= (lit->var lit) (fanin-count aignet)))
  ;;          :rule-classes nil))

  ;; (local (defthm lit->var-of-copy-upper-bound-when-aignet-copies-in-bounds
  ;;          (implies (aignet-copies-in-bounds copy aignet)
  ;;                   (<= (lit->var (nth-lit n copy)) (fanin-count aignet)))
  ;;          :hints (("goal" :use ((:instance lit->var-upper-bound-by-aignet-litp
  ;;                                 (lit (nth-lit n copy))))))
  ;;          :rule-classes :linear))


  (defret refcounts-length-of-cut-restore-mffcs
    (implies (and (leaves-lit-idsp n size aignet cutsdb)
                  (<= (num-fanins aignet) (len refcounts)))
             (equal (len new-refcounts) (len refcounts)))
    :hints (("goal" :induct <call> :expand (<call>)
             :in-theory (enable leaves-lit-idsp aignet-idp))))

  (defret refcounts-length-nondecr-of-cut-restore-mffcs
    (>= (len new-refcounts) (len refcounts))
    :rule-classes :linear)

  (defthm cut-restore-mffcs-nth-equiv-congruence-refcounts
    (implies (acl2::nth-nat-equiv refcounts refcounts1)
             (acl2::nth-nat-equiv (mv-nth 1 (cut-restore-mffcs n size cutsdb aignet refcounts))
                                  (mv-nth 1 (cut-restore-mffcs n size cutsdb aignet refcounts1))))
    :rule-classes :congruence))




(define cut-delete-mffcs ((n natp)
                           (size natp)
                           (cutsdb cutsdb-ok)
                           (aignet)
                           (refcounts))
  :returns (mv (mffc-count natp :rule-classes :type-prescription)
               (new-refcounts))
  :guard (and (<= (+ n size) (cut-leaves-length cutsdb))
              (leaves-lit-idsp n size aignet cutsdb)
              ;; (aignet-copies-in-bounds copy aignet)
              ;; (<= (cut-nnodes cutsdb) (lits-length copy))
              (<= (num-fanins aignet) (u32-length refcounts)))
  :verify-guards nil
  (b* (((when (zp size))
        (mv 0 refcounts))
       (id (cut-leavesi n cutsdb))
       ((mv rest-size refcounts) (cut-delete-mffcs (1+ (lnfix n)) (1- size) cutsdb aignet refcounts))
       ((mv size1 refcounts) (aignet-delete-mffc id aignet refcounts)))
    (mv (+ size1 rest-size) refcounts))
  ///

  ;; (local (defthm lit->var-of-copy-upper-bound-when-aignet-copies-in-bounds
  ;;          (implies (aignet-copies-in-bounds copy aignet)
  ;;                   (<= (lit->var (nth-lit n copy)) (fanin-count aignet)))
  ;;          :hints (("goal" :use ((:instance lit->var-upper-bound-by-aignet-litp
  ;;                                 (lit (nth-lit n copy))))))
  ;;          :rule-classes :linear))


  (defret refcounts-length-of-cut-delete-mffcs
    (implies (and (leaves-lit-idsp n size aignet cutsdb)
                  (<= (num-fanins aignet) (len refcounts)))
             (equal (len new-refcounts) (len refcounts)))
    :hints (("goal" :induct <call> :expand (<call>)
             :in-theory (enable leaves-lit-idsp aignet-idp))))


  (defret refcounts-length-nondecr-of-cut-delete-mffcs
    (>= (len new-refcounts) (len refcounts))
    :rule-classes :linear)

  (verify-guards cut-delete-mffcs
    :hints (("goal" :expand ((leaves-lit-idsp n size aignet cutsdb)))))

  (defthm cut-delete-mffcs-nth-equiv-congruence-refcounts
    (implies (acl2::nth-nat-equiv refcounts refcounts1)
             (acl2::nth-nat-equiv (mv-nth 1 (cut-delete-mffcs n size cutsdb aignet refcounts))
                                  (mv-nth 1 (cut-delete-mffcs n size cutsdb aignet refcounts1))))
    :rule-classes :congruence)

  (defthm cut-delete-mffcs-of-cut-restore-mffcs
    (acl2::nth-nat-equiv (mv-nth 1 (cut-delete-mffcs
                                    n size cutsdb aignet
                                    (mv-nth 1 (cut-restore-mffcs
                                               n size cutsdb aignet refcounts))))
                         refcounts)
    :hints(("Goal" :in-theory (enable cut-restore-mffcs)))))

(define eval-cut ((cut natp)
                  (node natp)
                  (cutsdb cutsdb-ok)
                  (rwlib rwlib-wfp)
                  (eba)
                  (eba2)
                  (eba3)
                  (eba4)
                  (copy2)
                  (strash2 "strash for aignet2")
                  (aignet2 "destination")
                  (refcounts2 "refcounts for aignet2")
                  (rewrite-stats)
                  (config rewrite-config-p))
  :guard (and (cutsdb-lit-idsp aignet2 cutsdb)
              ;; (<= (cut-nnodes cutsdb) (lits-length copy))
              (< cut (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (<= (num-fanins aignet2) (u32-length refcounts2))
              (<= (num-fanins aignet2) (eba-length eba4))
              (stobj-let ((aignet (rwlib->aigs rwlib)))
                         (ok)
                         (and 
                          (<= (num-fanins aignet) (lits-length copy2))
                          (<= (num-fanins aignet) (eba-length eba))
                          (<= (num-fanins aignet) (eba-length eba2))
                          (<= (num-fanins aignet) (eba-length eba3)))
                         ok))
  :returns (mv (ok "if nil, disqualify this cut")
               (score natp :rule-classes :type-prescription)
               (impl-idx natp :rule-classes :type-prescription)
               (new-eba)
               (new-eba2)
               (new-copy2)
               (new-eba3)
               (new-eba4)
               (new-refcounts2 (acl2::nth-nat-equiv new-refcounts2 refcounts2))
               (new-rewrite-stats))
  :prepwork (;; (local (defthm cutsdb-data-nodes-bounded-when-bounded-lesser-special
             ;;          (implies (and (cutsdb-data-nodes-bounded n size (cut-nnodes cutsdb) cutsdb)
             ;;                        (<= (cut-nnodes cutsdb) (nfix bound)))
             ;;                   (cutsdb-data-nodes-bounded n size bound cutsdb))
             ;;          :hints(("Goal" :in-theory (enable cutsdb-data-nodes-bounded-when-bounded-lesser)))))
             (local (defthm leaves-bounded-when-cut-leaves-bounded
                      (implies (and (cut-leaves-bounded cut (cut-nnodes cutsdb) cutsdb)
                                    (<= (cut-nnodes cutsdb) (nfix bound))
                                    (equal cut1 (nfix cut)))
                               (leaves-bounded (* 4 cut1) (cutinfo->size (cut-infoi cut cutsdb)) bound cutsdb))
                      :hints(("Goal" :in-theory (enable cut-leaves-bounded
                                                        leaves-bounded-when-bounded-lesser)))))
             (local (defthm leaves-lit-idsp-when-cut-leaves-lit-idsp
                      (implies (and (cut-leaves-lit-idsp cut aignet cutsdb)
                                    (equal cut1 (nfix cut)))
                               (leaves-lit-idsp (* 4 cut1) (cutinfo->size (cut-infoi cut cutsdb)) aignet cutsdb))
                      :hints(("Goal" :in-theory (enable cut-leaves-lit-idsp)))))
             (local (defthm cutsdb-ok-implies-cut-data-less-than-length
                      (implies (and (cutsdb-ok cutsdb)
                                    (natp cut1)
                                    (< cut1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                                    (natp offset))
                               (and (implies (<= offset (cutinfo->size (cut-infoi cut1 cutsdb)))
                                             (<= (+ (* 4 cut1) offset) (cut-leaves-length cutsdb)))
                                    (implies (< offset (cutinfo->size (cut-infoi cut1 cutsdb)))
                                             (< (+ (* 4 cut1) offset) (cut-leaves-length cutsdb)))))
                      ;; :hints (("goal" :use ((:instance cutsdb-ok-implies-cutsdb-cut-ok
                      ;;                        (n cut)))
                      ;;          :in-theory (e/d (cutsdb-cut-ok cut-next$ cut-next)
                      ;;                          (cutsdb-ok-implies-cutsdb-cut-ok))))
                      )))
  :guard-hints (("goal" :in-theory (enable cut-impl-index-ok
                                           cutsdb-lit-idsp-implies-cut-leaves-lit-idsp)))

  (b* (((cutinfo cutinf) (cut-infoi cut cutsdb))
       ((when (and (eql cutinf.size 0)
                   (cut-impl-index-ok cut 0 cutsdb rwlib)))
        ;; shortcut for const0 node
        (mv t 0 0 eba eba2 copy2 eba3 eba4 refcounts2 rewrite-stats))
       ((unless (and cutinf.valid
                     (cut-leaves-bounded cut node cutsdb)))
        (mv nil 0 0 eba eba2 copy2 eba3 eba4 refcounts2 rewrite-stats))
       ((unless (cut-impl-index-ok cut 0 cutsdb rwlib))
        (cw "Programming error -- nontrivial cut has no implementations?~%")
        (break$)
        (mv nil 0 0 eba eba2 copy2 eba3 eba4 refcounts2 rewrite-stats))
       ((mv base-cost refcounts2) (cut-restore-mffcs (* 4 (lnfix cut)) cutinf.size cutsdb aignet2 refcounts2))
       (copy2 (cut-initialize-copy cut copy2 cutsdb rwlib))
       (eba (eba-clear eba))
       (eba2 (eba-clear eba2))
       ((acl2::stobj-get impl-index impl-cost eba eba2 copy2 eba3 eba4 rewrite-stats)
        ((aignet (rwlib->aigs rwlib))
         (smm    (rwlib->cands rwlib))
         (truth::npn4arr (rwlib->npns rwlib)))
        (b* (((truth::npn4 npn) (truth::get-npn4 cutinf.truth truth::npn4arr)))
          (eval-implementations 0 npn.truth-idx smm aignet eba eba2 eba3 eba4 copy2 strash2 aignet2 refcounts2 rewrite-stats config)))
       ((mv & refcounts2) (cut-delete-mffcs (* 4 (lnfix cut)) cutinf.size cutsdb aignet2 refcounts2)))
    (mv t (+ base-cost impl-cost)
        impl-index eba eba2 copy2 eba3 eba4 refcounts2 rewrite-stats))
  ///
  (defret eval-cut-impl-index-ok
    (implies ok
             (cut-impl-index-ok cut impl-idx cutsdb rwlib))
    :hints(("Goal" :in-theory (enable cut-impl-index-ok))))

  (defret refcounts-length-of-eval-cut
    (implies (and (cutsdb-lit-idsp aignet2 cutsdb)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (num-fanins aignet2) (len refcounts2)))
             (equal (len new-refcounts2) (len refcounts2)))
    :hints(("Goal" :in-theory (enable cutsdb-lit-idsp-implies-cut-leaves-lit-idsp))))

  (defret copy2-length-of-eval-cut
    (implies (and (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (num-fanins (rwlib->aigs rwlib)) (len copy2)))
             (equal (len new-copy2) (len copy2)))
    :hints(("Goal" :in-theory (e/d (cut-impl-index-ok)
                                   (len)))))

  ;; (defret copy2-in-bounds-of-eval-cut
  ;;   (implies (and (cutsdb-lit-idsp aignet2 cutsdb)
  ;;                 (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  ;;                 (aignet-copies-in-bounds copy2 aignet2))
  ;;            (aignet-copies-in-bounds new-copy2 aignet2))
  ;;   :hints(("Goal" :in-theory (enable cutsdb-lit-idsp-implies-cut-leaves-lit-idsp))))
    

  (defret eba-length-of-eval-cut
    (implies (and (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (num-fanins (rwlib->aigs rwlib)) (len eba)))
             (equal (len new-eba) (len eba)))
    :hints(("Goal" :in-theory (e/d (cut-impl-index-ok)
                                   (len)))))

  (defret eba2-length-of-eval-cut
    (implies (and (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (num-fanins (rwlib->aigs rwlib)) (len eba2)))
             (equal (len new-eba2) (len eba2)))
    :hints(("Goal" :in-theory (e/d (cut-impl-index-ok)
                                   (len)))))

  (defret eba3-length-of-eval-cut
    (implies (and (rwlib-wfp rwlib)
                  (<= (num-fanins (rwlib->aigs rwlib)) (len eba3)))
             (equal (len new-eba3) (len eba3)))
    :hints(("Goal" :in-theory (enable cut-impl-index-ok))))

  (defret eba4-length-of-eval-cut
    (implies (and (<= (num-fanins aignet2) (len eba4))
                  (cutsdb-lit-idsp aignet2 cutsdb)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (rwlib-wfp rwlib))
             (equal (len new-eba4) (len eba4)))
    :hints(("Goal" :in-theory (enable cut-impl-index-ok))))

  (defretd eval-cut-ok-implies-cut-bounded
    (implies ok
             (cut-leaves-bounded cut node cutsdb))
    :hints ((acl2::use-termhint
             (and (equal (cutinfo->size (cut-infoi cut cutsdb)) 0)
                  ''(:expand ((cut-leaves-bounded cut node cutsdb)
                              (:free (n) (leaves-bounded n 0 node cutsdb)))))))))

       

                 
(define choose-implementation-cuts-nobuild ((cuts-start natp)
                                            (cuts-end natp)
                                            (node natp)
                                            (cutsdb cutsdb-ok)
                                            (rwlib rwlib-wfp)
                                            (eba)
                                            (eba2)
                                            (eba3)
                                            (eba4)
                                            (copy2)
                                            (strash2 "strash for aignet2")
                                            (aignet2 "destination")
                                            (refcounts2 "refcounts for aignet2")
                                            (rewrite-stats)
                                            (config rewrite-config-p))
  :guard (and (<= cuts-start cuts-end)
              (<= cuts-end (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (cutsdb-lit-idsp aignet2 cutsdb)
              (<= (num-fanins aignet2) (u32-length refcounts2))
              (<= (num-fanins aignet2) (eba-length eba4))
              (stobj-let ((aignet (rwlib->aigs rwlib)))
                         (ok)
                         (and (<= (num-fanins aignet) (lits-length copy2))
                              (<= (num-fanins aignet) (eba-length eba))
                              (<= (num-fanins aignet) (eba-length eba2))
                              (<= (num-fanins aignet) (eba-length eba3)))
                         ok))
  :verify-guards nil
  :returns (mv (ok "if nil, no qualifiying cuts")
               (score natp :rule-classes :type-prescription)
               (cut-index natp :rule-classes :type-prescription)
               (impl-index natp :rule-classes :type-prescription)
               (new-eba)
               (new-eba2)
               (new-copy2)
               (new-eba3)
               (new-eba4)
               (new-refcounts2 (acl2::nth-nat-equiv new-refcounts2 refcounts2))
               (new-rewrite-stats))
  :measure (nfix (- (nfix cuts-end) (nfix cuts-start)))
  (b* (((when (mbe :logic (zp (- (lnfix cuts-end) (nfix cuts-start)))
                   :exec (eql cuts-start cuts-end)))
        (mv nil 0 0 0 eba eba2 copy2 eba3 eba4 refcounts2 rewrite-stats))
       ((mv ok1 score1 impl-idx1 eba eba2 copy2 eba3 eba4 refcounts2 rewrite-stats)
        (eval-cut cuts-start node cutsdb rwlib eba eba2 eba3 eba4 copy2 strash2 aignet2 refcounts2 rewrite-stats config))
       ((when (and ok1 (eql score1 0)))
        ;; early out for 0-cost
        (mv t 0 (lnfix cuts-start) impl-idx1 eba eba2 copy2 eba3 eba4 refcounts2 rewrite-stats))
       ((unless ok1)
        (choose-implementation-cuts-nobuild (1+ (lnfix cuts-start)) cuts-end node cutsdb rwlib
                                    eba eba2 eba3 eba4 copy2 strash2 aignet2 refcounts2 rewrite-stats config))
       ((mv ok-rest best-score best-cut-idx best-impl-idx eba eba2 copy2 eba3 eba4 refcounts2 rewrite-stats)
        (choose-implementation-cuts-nobuild (1+ (lnfix cuts-start)) cuts-end node cutsdb rwlib
                                    eba eba2 eba3 eba4 copy2 strash2 aignet2 refcounts2 rewrite-stats config))
       ((when (or (not ok-rest)
                  (< score1 best-score)))
        (mv ok1 score1 (lnfix cuts-start) impl-idx1 eba eba2 copy2 eba3 eba4 refcounts2 rewrite-stats)))
    (mv t best-score best-cut-idx best-impl-idx eba eba2 copy2 eba3 eba4 refcounts2 rewrite-stats))
  ///
  (verify-guards choose-implementation-cuts-nobuild)

  (defret cut-impl-index-ok-of-choose-implementation-cuts-nobuild
    (implies ok
             (and (cut-impl-index-ok cut-index impl-index cutsdb rwlib)
                  (cut-leaves-bounded cut-index node cutsdb)))
    :hints(("Goal" :induct t)
           (and stable-under-simplificationp
                '(:use ((:instance eval-cut-ok-implies-cut-bounded
                         (cut (nfix cuts-start))))))))

  ;; (defret cutp-of-choose-implemenation-cuts
  ;;   (implies (cutsdb-ok cutsdb)
  ;;            (cutp cut-index cutsdb)))

  (defret cut-bound-of-choose-implementation-cuts-nobuild
    (implies ok
             (< cut-index (nfix cuts-end)))
    :rule-classes :linear)

  (defret cut-lower-bound-of-choose-implementation-cuts-nobuild
    (implies ok
             (<= (nfix cuts-start) cut-index))
    :rule-classes :linear)

  
  (defret refcounts-length-of-choose-implementation-cuts-nobuild
    (implies (and (cutsdb-lit-idsp aignet2 cutsdb)
                  (<= (nfix cuts-end) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (num-fanins aignet2) (len refcounts2)))
             (equal (len new-refcounts2) (len refcounts2))))

  (defret copy2-length-of-choose-implementation-cuts-nobuild
    (implies (and (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (<= (nfix cuts-end) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (num-fanins (rwlib->aigs rwlib)) (len copy2)))
             (equal (len new-copy2) (len copy2)))
    :hints(("Goal" :in-theory (e/d (cut-impl-index-ok)
                                   (len)))))

  (defret eba-length-of-choose-implementation-cuts-nobuild
    (implies (and (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (<= (nfix cuts-end) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (num-fanins (rwlib->aigs rwlib)) (len eba)))
             (equal (len new-eba) (len eba)))
    :hints(("Goal" :in-theory (e/d (cut-impl-index-ok)
                                   (len)))))

  (defret eba2-length-of-choose-implementation-cuts-nobuild
    (implies (and (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (<= (nfix cuts-end) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (num-fanins (rwlib->aigs rwlib)) (len eba2)))
             (equal (len new-eba2) (len eba2)))
    :hints(("Goal" :in-theory (e/d (cut-impl-index-ok)
                                   (len)))))

  (defret eba3-length-of-choose-implementation-cuts-nobuild
    (implies (and (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (<= (nfix cuts-end) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (num-fanins (rwlib->aigs rwlib)) (len eba3)))
             (equal (len new-eba3) (len eba3)))
    :hints(("Goal" :in-theory (e/d (cut-impl-index-ok)
                                   (len)))))

  (defret eba4-length-of-choose-implementation-cuts-nobuild
    (implies (and (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (cutsdb-lit-idsp aignet2 cutsdb)
                  (<= (nfix cuts-end) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (num-fanins aignet2) (len eba4)))
             (equal (len new-eba4) (len eba4)))
    :hints(("Goal" :in-theory (e/d (cut-impl-index-ok)
                                   (len))))))


;; ==========================================================================================
;; End Evaluation method 2.
;; ==========================================================================================


(define choose-implementation-cuts ((cuts-start natp)
                                    (cuts-end natp)
                                    (node natp)
                                    (cutsdb cutsdb-ok)
                                    (rwlib rwlib-wfp)
                                    (eba)
                                    (eba2)
                                    (eba3)
                                    (eba4)
                                    (copy2)
                                    (strash2 "strash for aignet2")
                                    (aignet2 "destination")
                                    (refcounts2 "refcounts for aignet2")
                                    (rewrite-stats)
                                    (config rewrite-config-p))
  :guard (and (<= cuts-start cuts-end)
              (<= cuts-end (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (cutsdb-lit-idsp aignet2 cutsdb)
              (equal (num-nxsts aignet2) 0)
              (equal (num-outs aignet2) 0)
              (b* ((width (stobj-let ((aignet (rwlib->aigs rwlib)))
                                     (width)
                                     (+ -1 (num-fanins aignet))
                                     width)))
                (and (< width (lits-length copy2))
                     (< width (eba-length eba))
                     (or (eq (rewrite-config->evaluation-method config) :build)
                         (and (<= (num-fanins aignet2) (u32-length refcounts2))
                              (<= (num-fanins aignet2) (eba-length eba4))
                              (< width (eba-length eba2))
                              (< width (eba-length eba3)))))))
  :verify-guards nil
  :returns (mv (ok "if nil, no qualifiying cuts")
               (score natp :rule-classes :type-prescription)
               (cut-index natp :rule-classes :type-prescription)
               (impl-index natp :rule-classes :type-prescription)
               (new-eba)
               (new-eba2)
               (new-copy2)
               (new-eba3)
               (new-eba4)
               (new-strash2)
               (new-aignet2 (equal new-aignet2 (node-list-fix aignet2)))
               (new-refcounts2 (acl2::nth-nat-equiv new-refcounts2 refcounts2))
               (new-rewrite-stats))
  (b* (((rewrite-config config)))
    (if (eq config.evaluation-method :build)
        (mbe :logic
             (non-exec
              (b* (((mv ok score cut-index impl-index refcounts2 eba eba2 copy2 strash2 & rewrite-stats)
                    (choose-implementation-cuts-build
                     cuts-start cuts-end node cutsdb rwlib eba eba2 copy2 strash2 aignet2 refcounts2 rewrite-stats config)))
                (mv ok score cut-index impl-index eba eba2 copy2 eba3 eba4 strash2
                    (node-list-fix aignet2)
                    refcounts2 rewrite-stats)))
             :exec
             (b* (((mv ok score cut-index impl-index refcounts2 eba eba2 copy2 strash2 aignet2 rewrite-stats)
                   (choose-implementation-cuts-build
                    cuts-start cuts-end node cutsdb rwlib eba eba2 copy2 strash2 aignet2 refcounts2 rewrite-stats config)))
               (mv ok score cut-index impl-index eba eba2 copy2 eba3 eba4 strash2 aignet2 refcounts2 rewrite-stats)))
      (b* (((mv ok score cut-index impl-index eba eba2 copy2 eba3 eba4 refcounts2 rewrite-stats)
            (choose-implementation-cuts-nobuild
             cuts-start cuts-end node cutsdb rwlib eba eba2 eba3 eba4 copy2 strash2 aignet2 refcounts2 rewrite-stats config))
           (aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                         :exec aignet2)))
        (mv ok score cut-index impl-index eba eba2 copy2 eba3 eba4 strash2 aignet2 refcounts2 rewrite-stats))))
  ///
  
 
  (verify-guards choose-implementation-cuts)

  (defret cut-impl-index-ok-of-choose-implementation-cuts
    (implies ok
             (and (cut-impl-index-ok cut-index impl-index cutsdb rwlib)
                  (cut-leaves-bounded cut-index node cutsdb))))

  ;; (defret cutp-of-choose-implemenation-cuts
  ;;   (implies (cutsdb-ok cutsdb)
  ;;            (cutp cut-index cutsdb)))

  (defret cut-bound-of-choose-implementation-cuts
    (implies ok
             (< cut-index (nfix cuts-end)))
    :rule-classes :linear)

  (defret cut-lower-bound-of-choose-implementation-cuts
    (implies ok
             (<= (nfix cuts-start) cut-index))
    :rule-classes :linear)

  
  (defret refcounts-length-of-choose-implementation-cuts
    (implies (and (cutsdb-lit-idsp aignet2 cutsdb)
                  (<= (nfix cuts-end) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (num-fanins aignet2) (len refcounts2)))
             (< (fanin-count aignet2) (len new-refcounts2))))

  (defret copy2-length-of-choose-implementation-cuts
    (implies (and (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (<= (nfix cuts-end) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (num-fanins (rwlib->aigs rwlib)) (len copy2)))
             (equal (len new-copy2) (len copy2))))

  (defret eba-length-of-choose-implementation-cuts
    (implies (and (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (<= (nfix cuts-end) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (num-fanins (rwlib->aigs rwlib)) (len eba)))
             (equal (len new-eba) (len eba))))

  (defret eba2-length-of-choose-implementation-cuts
    (implies (and (not (equal (rewrite-config->evaluation-method config) :build))
                  (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (<= (nfix cuts-end) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (num-fanins (rwlib->aigs rwlib)) (len eba2)))
             (equal (len new-eba2) (len eba2))))

  (defret eba3-length-of-choose-implementation-cuts
    (implies (and (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (<= (nfix cuts-end) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (num-fanins (rwlib->aigs rwlib)) (len eba3)))
             (equal (len new-eba3) (len eba3))))

  (defret eba4-length-of-choose-implementation-cuts
    (implies (and (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (cutsdb-lit-idsp aignet2 cutsdb)
                  (<= (nfix cuts-end) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (num-fanins aignet2) (len eba4)))
             (equal (len new-eba4) (len eba4)))
    :hints(("Goal" :in-theory (e/d (cut-impl-index-ok)
                                   (len))))))





;; (define rewrite-choose-implementation ((n natp)
;;                                        (cutsdb cutsdb-ok)
;;                                        (rwlib rwlib-wfp)
;;                                        (aignet2)
;;                                        (copy)
;;                                        (strash2)
;;                                        (refcounts)
;;                                        (rewrite-stats)
;;                                        (config rewrite-config-p))
;;   :guard (and (<= n (+ -1 (num-fanins aignet)))
;;               (<= cuts-start cuts-end)
;;               (<= cuts-end (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
;;               (<= (num-fanins aignet) (cut-nnodes cutsdb))
;;               (<= (num-fanins aignet) (lits-length copy))
;;               (aignet-copies-in-bounds copy aignet2)
;;               (equal (num-ins aignet) (num-ins aignet2))
;;               (equal (num-regs aignet) (num-regs aignet2))
;;               (<= (num-fanins aignet) (u32s-length refcounts)))
;;   :ignore-ok t
;;   :irrelevant-formals-ok t
;;   :returns (mv replacep
;;                (cut-index natp :rule-classes :type-prescription)
;;                (impl-index natp :rule-classes :type-prescription))
;;   (dumb-choose-implementation-cuts
  
;;   ///
;;   (defret rewrite-choose-implementation-in-bounds
;;     (implies (and replacep
;;                   (cutsdb-ok cutsdb)
;;                   (rwlib-wfp rwlib))
;;              (and (cutp cut-index cutsdb)
;;                   (< cut-index (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
;;                   (b* ((truth (cut-datai (+ 1 cut-index) cutsdb))
;;                        ((npn4 npn) (nth truth (rwlib->npns rwlib))))
;;                     (< impl-index (len (nth npn.truth-idx (rwlib->cands rwlib))))))))

;;   (defret rewrite-choose-implementation-correct
;;     (implies (and replacep
;;                   (cutsdb-ok cutsdb)
;;                   (rwlib-wfp rwlib)
;;                   (rwlib-correct rwlib))
;;              (b* ((truth (cut-datai (+ 1 cut-index) cutsdb))
;;                   ((npn4 npn) (nth truth (rwlib->npns rwlib)))
;;                   (impl-lit (nth impl-index (nth npn.truth-idx (rwlib->cands rwlib)))))
;;                (equal (lit-eval impl-lit invals regvals (rwlib->aigs rwlib))
;;                       (bool->bit (truth-eval (nth npn.truth-idx truth4arr)
;;                                              (truth4-env-from-aignet-invals invals)
;;                                              4))
;;                       (bool->bit (truth::truth-eval truth
;;                                                     (permuted-env-from-aignet-invals npn invals))))))))

(defsection aignet-count-gate-refs-step

  (defthm aignet-update-refs-step-preserves-length
    (implies (and (<= (num-fanins aignet) (len refcounts))
                  (natp n))
             (let ((new-refcounts (aignet-count-gate-refs-step n refcounts aignet)))
               (equal (len new-refcounts) (len refcounts))))
    :hints(("Goal" :in-theory (enable aignet-count-gate-refs-step)))))

(local (in-theory (disable aignet-count-gate-refs-step)))
                                  
(define aignet-update-gate-refs ((n natp)
                                 (refcounts)
                                 (aignet))
  :guard (and (< n (num-fanins aignet))
              (<= (num-fanins aignet) (u32-length refcounts)))
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  :returns (new-refcounts)
  (b* ((refcounts (if (<= (lnfix n) (+ -1 (num-fanins aignet)))
                      (set-u32 n 0 refcounts)
                    refcounts))
       (slot0 (id->slot n 0 aignet))
       ((unless (eql (snode->type slot0) (gate-type)))
        refcounts)
       (child0 (lit->var (snode->fanin slot0)))
       (child1 (lit->var (gate-id->fanin1 n aignet)))
       ((mv & refcounts)
        (aignet-restore-mffc child0 1 aignet refcounts))
       ((mv & refcounts)
        (aignet-restore-mffc child1 1 aignet refcounts)))
    refcounts)
  ///
  (defret refcounts-len-of-aignet-update-gate-refs
    (implies (<= (num-fanins aignet) (len refcounts))
             (equal (len new-refcounts) (len refcounts)))))
       

                
(define aignet-update-refs-aux ((n natp)
                                (refcounts)
                                (aignet))
  :guard (and (<= n (num-fanins aignet))
              (<= (num-fanins aignet) (u32-length refcounts)))
  :measure (nfix (- (num-fanins aignet) (nfix n)))
  :returns (new-refcounts)
  :prepwork ((local (in-theory (disable fanin-count-of-atom
                                        acl2::update-nth-of-nth-free
                                        true-listp-update-nth
                                        lookup-id-out-of-bounds
                                        default-car))))
  
  (b* (((when (mbe :logic (zp (- (num-fanins aignet) (nfix n)))
                   :exec (eql (num-fanins aignet) n)))
        refcounts)
       (refcounts (aignet-update-gate-refs n refcounts aignet)))
    (aignet-update-refs-aux (+ 1 (lnfix n)) refcounts aignet))
  ///
  ;; (local (defthm bound-when-output
  ;;          (implies (and (equal (ctype (stype (car (lookup-id n aignet)))) :output)
  ;;                        (natp n))
  ;;                   (< (fanin-count aignet) n))
  ;;          :hints (("goal" :use ((:instance aignet-litp-implies-id-lte-max-fanin
  ;;                                 (lit (mk-lit n 0))))
  ;;                   :in-theory (disable aignet-litp-implies-id-lte-max-fanin)))))

  (defret aignet-update-refs-aux-preserves-length
    (implies (<= (num-fanins aignet) (len refcounts))
             (equal (len new-refcounts) (len refcounts)))))

(define aignet-update-refs ((n natp)
                            (refcounts)
                            (aignet))
  :guard (<= n (num-fanins aignet))
  :returns (new-refcounts)
  (b* ((refcounts (if (<= (u32-length refcounts) (+ -1 (num-fanins aignet)))
                      (resize-u32 (max 16 (* 2 (+ -1 (num-fanins aignet)))) refcounts)
                    refcounts)))
    (aignet-update-refs-aux n refcounts aignet))
  ///
  (defret length-of-aignet-update-refs
    (< (fanin-count aignet) (len new-refcounts))
    :rule-classes :linear))




;; (define my-aignet-and-gate-simp/strash ((lit1 litp)
;;                                        (lit2 litp)
;;                                        (gatesimp natp)
;;                                        (strash)
;;                                        (aignet))
;;   :enabled t
;;   :guard (and (fanin-litp lit1 aignet)
;;               (fanin-litp lit2 aignet))
;;   (aignet-and-gate-simp/strash lit1 lit2 gatesimp strash aignet))



(define rewrite-default-copy-deref-and-cost ((flit1 litp)
                                             (flit2 litp)
                                             (code simpcode-p)
                                             (lit1 litp)
                                             (lit2 litp)
                                             (aignet2)
                                             (refcounts2))
  :returns (mv (cost natp :rule-classes :type-prescription)
               (new-refcounts2))
  :guard (and (<= (num-fanins aignet2) (u32-length refcounts2))
              (fanin-litp flit1 aignet2)
              (fanin-litp flit2 aignet2)
              (fanin-litp lit1 aignet2)
              (fanin-litp lit2 aignet2))
  (b* (((mv cost0 refcounts2) (aignet-delete-mffc (lit-id flit1) aignet2 refcounts2))
       ((mv cost1 refcounts2) (aignet-delete-mffc (lit-id flit2) aignet2 refcounts2))
       (existing (eql 1 (simpcode->identity code)))
       ((when (and (not existing)
                   (or (and (lit-equiv lit1 flit1) (lit-equiv lit2 flit2))
                       (and (lit-equiv lit1 flit2) (lit-equiv lit2 flit1)))))
        (mv (+ 1 cost0 cost1) refcounts2))
       ((when existing)
        (b* (((mv cost refcounts2) (aignet-restore-mffc (lit-id lit1) 1 aignet2 refcounts2))
             ((mv & refcounts2) (aignet-delete-mffc (lit-id lit1) aignet2 refcounts2)))
          (mv cost refcounts2)))
       ((mv cost1 refcounts2) (aignet-restore-mffc (lit-id lit2) 1 aignet2 refcounts2))
       ((mv cost0 refcounts2) (aignet-restore-mffc (lit-id lit1) 1 aignet2 refcounts2))
       ((mv & refcounts2) (aignet-delete-mffc (lit-id lit1) aignet2 refcounts2))
       ((mv & refcounts2) (aignet-delete-mffc (lit-id lit2) aignet2 refcounts2)))
    (mv (+ 1 cost0 cost1) refcounts2))
  ///
  (defret refcounts-length-of-rewrite-default-copy-deref-and-cost
    (implies (and (<= (num-fanins aignet2) (len refcounts2))
                  (aignet-litp flit1 aignet2)
                  (aignet-litp flit2 aignet2)
                  (aignet-litp lit1 aignet2)
                  (aignet-litp lit2 aignet2)
                  (or (not existing)
                      (aignet-litp existing aignet2)))
             (equal (len new-refcounts2) (len refcounts2)))
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defret refcounts-length-nondecr-of-rewrite-default-copy-deref-and-cost
    (>= (len new-refcounts2) (len refcounts2))
    :hints(("Goal" :in-theory (disable refcounts-length-of-aignet-delete-mffc
                                       refcounts-length-of-aignet-restore-mffc)))
    :rule-classes :linear))

(local (defthmd unsigned-byte-p-of-lit-when-lit->var
         (implies (and (unsigned-byte-p (+ -1 n) (lit->var lit))
                       (litp lit)
                       (posp n))
                  (unsigned-byte-p n lit))
         :hints(("Goal" :in-theory (enable lit->var)))
         :rule-classes ((:rewrite :backchain-limit-lst (3 nil nil)))))
                  

(local (defthm unsigned-byte-p-of-lit->var-when-aignet-litp
         (implies (and (aignet-idp id aignet)
                       (< (fanin-count aignet) #x1fffffff))
                  (and (implies (natp id)
                                (unsigned-byte-p 29 id))
                       (unsigned-byte-p 29 (nfix id))))
         :hints(("Goal" :in-theory (enable unsigned-byte-p aignet-idp)))))

(local (defthm unsigned-byte-p-when-aignet-litp
         (implies (and (aignet-litp lit aignet)
                       (litp lit)
                       (< (fanin-count aignet) #x1fffffff))
                  (unsigned-byte-p 30 lit))
         :hints(("Goal" :in-theory (enable unsigned-byte-p-of-lit-when-lit->var)))))


(define rewrite-copy-node ((n natp "index in original aig")
                           (aignet "original aig")
                           (aignet2 "new aig being constructed")
                           (cutsdb cutsdb-ok)
                           (copy "mapping from original to new aig nodes")
                           (strash2 "strash table for aignet2")
                           (refcounts2 "refcounts for aignet2, including replacements")
                           (rewrite-stats)
                           (config rewrite-config-p))
  :guard (and (<= n (+ -1 (num-fanins aignet)))
              (<= (cut-nnodes cutsdb) (num-fanins aignet2))
              (eql (id->type n aignet) (gate-type))
              (<= (num-fanins aignet) (lits-length copy))
              (aignet-copies-in-bounds copy aignet2)
              (equal (num-ins aignet) (num-ins aignet2))
              (equal (num-regs aignet) (num-regs aignet2))
              (<= (num-fanins aignet2) (u32-length refcounts2)))
  
  :returns (mv (lit litp :rule-classes :type-prescription)
               (build-cost natp :rule-classes :type-prescription)
               new-cutsdb
               new-aignet2
               new-strash2
               new-refcounts2
               new-rewrite-stats)
  :prepwork ((local (defthm unsigned-byte-p-when-aignet-litp-bind
                      (implies (and (bind-free '((aignet . aignet2)) (aignet))
                                    (aignet-litp lit aignet)
                                    (litp lit)
                                    (< (fanin-count aignet) #x1fffffff))
                               (unsigned-byte-p 30 lit))
                      :hints(("Goal" :in-theory (enable unsigned-byte-p-of-lit-when-lit->var))))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable aignet-idp))))
                                    
  (b* ((n (lnfix n))
       (lit0 (gate-id->fanin0 n aignet))
       (lit1 (gate-id->fanin1 n aignet))
       
       (flit0-copy (lit-copy lit0 copy))
       (flit1-copy (lit-copy lit1 copy))
       ((rewrite-config config))
       ((mv code key lit0-copy lit1-copy)
        (if (eql 1 (id->regp n aignet))
            (aignet-xor-gate-simp/strash flit0-copy flit1-copy config.gatesimp strash2 aignet2)
          (aignet-and-gate-simp/strash flit0-copy flit1-copy config.gatesimp strash2 aignet2)))
       ((mv lit strash2 aignet2)
        (aignet-install-gate code key lit0-copy lit1-copy config.gatesimp strash2 aignet2))
       (refcounts2 (maybe-grow-refcounts (num-fanins aignet2) refcounts2))

       ;; Note: It's a little weird to do this here, but it seems heuristically
       ;; slightly better to evaluate cuts with the inputs to the new node
       ;; referenced, rather than after derefing them below.  That's the only
       ;; reason to derive cuts here rather than in reimplement-node or elsewhere.
       ((mv cuts-checked cutsdb) (aignet-derive-cuts-aux aignet2 0 config.cuts4-config refcounts2 cutsdb))
       (rewrite-stats (incr-rewrite-stats-cuts-checked rewrite-stats cuts-checked))

       ((mv build-cost refcounts2)
        (rewrite-default-copy-deref-and-cost
         flit0-copy flit1-copy code lit0-copy lit1-copy aignet2 refcounts2)))

    (mv lit build-cost cutsdb aignet2 strash2 refcounts2 rewrite-stats))

  ///
  
  (def-aignet-preservation-thms rewrite-copy-node :stobjname aignet2)

  (defret stype-counts-of-rewrite-copy-node
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))

  (defret rewrite-copy-node-refcounts2-len-greater
    (< (fanin-count new-aignet2) (len new-refcounts2))
    :rule-classes :linear)

  (defret aignet-litp-lit-of-rewrite-copy-node
    (implies (aignet-copies-in-bounds copy aignet2)
             (aignet-litp lit new-aignet2)))

  (defret eval-of-rewrite-copy-node
    (implies (and (aignet-copy-is-comb-equivalent n aignet copy aignet2)
                  (equal (id->type n aignet) (gate-type)))
             (equal (lit-eval lit invals regvals new-aignet2)
                    (id-eval n invals regvals aignet)))
    :hints (("goal" :expand ((id-eval n invals regvals aignet))
             :in-theory (enable eval-and-of-lits eval-xor-of-lits lit-eval))))

  
  (defret cutsdb-lit-idsp-of-rewrite-copy-node
    (implies (and (cutsdb-ok cutsdb)
                  (cutsdb-lit-idsp aignet2 cutsdb))
             (cutsdb-lit-idsp new-aignet2 new-cutsdb)))

  (defret cutsdb-ok-of-rewrite-copy-node
    (implies (cutsdb-ok cutsdb)
             (cutsdb-ok new-cutsdb)))

  
  (defret cut-nnodes-lte-max-fanin-of-rewrite-copy-node
    (implies (<= (cut-nnodes cutsdb) (+ 1 (fanin-count aignet2)))
             (equal (cut-nnodes new-cutsdb) (+ 1 (fanin-count new-aignet2)))))

  
  (defret cutsdb-correct-of-rewrite-copy-node
    (implies (and (cutsdb-correct cutsdb aignet2)
                  (cutsdb-ok cutsdb)
                  (<= (cut-nnodes cutsdb) (+ 1 (fanin-count aignet2))))
             (cutsdb-correct new-cutsdb new-aignet2))))

(local

 (defsection cutsdb-lit-idsp-of-node-list-fix
   (defthm leaves-lit-idsp-of-node-list-fix
     (iff (leaves-lit-idsp n size (node-list-fix aignet) cutsdb)
          (leaves-lit-idsp n size aignet cutsdb))
     :hints(("Goal" :in-theory (enable leaves-lit-idsp))))

   (defthm cut-leaves-lit-idsp-of-node-list-fix
     (iff (cut-leaves-lit-idsp n (node-list-fix aignet) cutsdb)
          (cut-leaves-lit-idsp n aignet cutsdb))
     :hints(("Goal" :in-theory (enable cut-leaves-lit-idsp))))

   (defthm cutsdb-leaves-lit-idsp-of-node-list-fix
     (iff (cutsdb-leaves-lit-idsp n (node-list-fix aignet) cutsdb)
          (cutsdb-leaves-lit-idsp n aignet cutsdb))
     :hints(("Goal" :in-theory (enable cutsdb-leaves-lit-idsp))))

   (defthm cutsdb-lit-idsp-of-node-list-fix
     (iff (cutsdb-lit-idsp (node-list-fix aignet) cutsdb)
          (cutsdb-lit-idsp aignet cutsdb))
     :hints(("Goal" :in-theory (enable cutsdb-lit-idsp))))))



(define rewrite-reimplement-node ((lit litp "lit to replicate")
                                  (build-cost natp)
                                  (cutsdb cutsdb-ok)
                                  (rwlib rwlib-wfp)
                                  aignet2
                                  eba
                                  eba2
                                  eba3
                                  eba4
                                  copy2
                                  strash2
                                  refcounts2
                                  rewrite-stats
                                  (config rewrite-config-p))
  :guard (and (fanin-litp lit aignet2)
              (equal (cut-nnodes cutsdb) (num-fanins aignet2))
              (cutsdb-lit-idsp aignet2 cutsdb)
              (<= (num-fanins aignet2) (u32-length refcounts2))
              (equal (num-nxsts aignet2) 0)
              (equal (num-outs aignet2) 0)
              (b* ((width (stobj-let ((aignet (rwlib->aigs rwlib)))
                                     (width)
                                     (+ -1 (num-fanins aignet))
                                     width)))
                (and (< width (lits-length copy2))
                     (< width (eba-length eba))
                     (or (eq (rewrite-config->evaluation-method config) :build)
                         (and (<= (num-fanins aignet2) (eba-length eba4))
                              (< width (eba-length eba2))
                              (< width (eba-length eba3)))))))
  :returns (mv (new-lit litp :rule-classes :type-prescription)
               new-aignet2
               ;; new-cutsdb
               new-eba
               new-eba2
               new-copy2
               new-eba3
               new-eba4
               new-strash2
               new-refcounts2
               new-rewrite-stats)

  :prepwork ((local (in-theory (disable nodecut-indicesi-updater-independence
                                        stype-by-ctype
                                        fanin-count-of-atom))))
  :guard-hints (("goal" :do-not-induct t
                 :in-theory (enable aignet-idp)))
  (b* (((rewrite-config config))
       (build-cost (lnfix build-cost))
       ((when (or (and (not config.zero-cost-replace)
                       (eql 0 build-cost))
                  (eql (lit-id lit) 0)))
        (b* ((rewrite-stats (incr-rewrite-stats-zero rewrite-stats))
             (aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                           :exec aignet2)))
          (mv (lit-fix lit) aignet2 eba eba2 copy2 eba3 eba4 strash2 refcounts2 rewrite-stats)))

       ;; ((mv cuts-checked cutsdb) (aignet-derive-cuts-aux aignet2 0 config.cuts4-config refcounts2 cutsdb))
       ;; (rewrite-stats (incr-rewrite-stats-cuts-checked rewrite-stats cuts-checked))

       ((mv replacep cut-cost cut-index impl-index eba eba2 copy2 eba3 eba4 strash2 aignet2 refcounts2 rewrite-stats)
        (choose-implementation-cuts
                     (nodecut-indicesi (lit-id lit) cutsdb)
                     (nodecut-indicesi (+ 1 (lit-id lit)) cutsdb)
                     (lit-id lit) cutsdb rwlib eba eba2 eba3 eba4 copy2 strash2 aignet2 refcounts2 rewrite-stats config))
       ((when (and replacep (if config.zero-cost-replace (<= cut-cost build-cost) (< cut-cost build-cost))))
        (b* ((rewrite-stats (incr-rewrite-stats-repls rewrite-stats))
             (rewrite-stats (incr-rewrite-stats-zero-cond (eql cut-cost build-cost) rewrite-stats))
             (rewrite-stats (incr-rewrite-stats-savings rewrite-stats (- build-cost cut-cost)))
             ((mv new-lit copy2 eba strash2 aignet2)
              (aignet-build-cut cut-index impl-index eba copy2 cutsdb rwlib config.gatesimp strash2 aignet2))

             (refcounts2 (maybe-grow-refcounts (num-fanins aignet2) refcounts2)))
          (mv (lit-negate-cond new-lit (lit-neg lit))
              aignet2 eba eba2 copy2 eba3 eba4 strash2 refcounts2 rewrite-stats)))
       (aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                     :exec aignet2)))
    (mv (lit-fix lit) aignet2 eba eba2 copy2 eba3 eba4 strash2 refcounts2 rewrite-stats))
  ///
  (def-aignet-preservation-thms rewrite-reimplement-node :stobjname aignet2)

  ;; (defret rewrite-reimplement-node-copies-in-bounds
  ;;   (implies (and (cutsdb-lit-idsp aignet2 cutsdb)
  ;;                 (cutsdb-ok cutsdb)
  ;;                 (<= (cut-nnodes cutsdb) (num-fanins aignet2))
  ;;                 (aignet-litp lit aignet2)
  ;;                 (aignet-copies-in-bounds copy2 aignet2)
  ;;                 (rwlib-wfp rwlib))
  ;;            (aignet-copies-in-bounds new-copy2 new-aignet2)))

  (defret aignet-litp-of-rewrite-reimplement-node
    (implies (and (cutsdb-lit-idsp aignet2 cutsdb)
                  (cutsdb-ok cutsdb)
                  (equal (cut-nnodes cutsdb) (num-fanins aignet2))
                  (aignet-litp lit aignet2)
                  (rwlib-wfp rwlib))
             (aignet-litp new-lit new-aignet2))
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defret stype-counts-of-rewrite-reimplement-node
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))

  (defret rewrite-reimplement-node-preserves-refcounts2-len-greater
    (implies (and (< (fanin-count aignet2) (len refcounts2))
                  (cutsdb-lit-idsp aignet2 cutsdb)
                  ;; (aignet-copies-in-bounds copy2 aignet2)
                  (cutsdb-ok cutsdb)
                  (aignet-litp lit aignet2)
                  (equal (cut-nnodes cutsdb) (num-fanins aignet2)))
             (< (fanin-count new-aignet2) (len new-refcounts2)))
    :hints(("Goal" :in-theory (enable aignet-idp)))
    :rule-classes (:rewrite :linear))


  (defret copy2-length-of-rewrite-reimplement-node
    (implies (and (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (<= (num-fanins (rwlib->aigs rwlib)) (len copy2))
                  (aignet-litp lit aignet2)
                  (equal (cut-nnodes cutsdb) (num-fanins aignet2)))
             (equal (len new-copy2) (len copy2)))
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defret eba-length-of-rewrite-reimplement-node
    (implies (and (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (<= (num-fanins (rwlib->aigs rwlib)) (len eba))
                  (aignet-litp lit aignet2)
                  (equal (cut-nnodes cutsdb) (num-fanins aignet2)))
             (equal (len new-eba) (len eba)))
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defret eba2-length-of-rewrite-reimplement-node
    (implies (and (not (equal (rewrite-config->evaluation-method config) :build))
                  (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (<= (num-fanins (rwlib->aigs rwlib)) (len eba2))
                  (aignet-litp lit aignet2)
                  (equal (cut-nnodes cutsdb) (num-fanins aignet2)))
             (equal (len new-eba2) (len eba2)))
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (local (defret eval-of-aignet-build-cut-rw
           (implies (and ;; (aignet-copy-is-comb-equivalent node aignet copy aignet2)
                     (rwlib-correct rwlib)
                     (cutsdb-ok cutsdb)
                     (cutsdb-lit-idsp aignet2 cutsdb)
                     (rwlib-wfp rwlib)
                     (bind-free '((node . (satlink::lit->var$inline lit))) (node))
                     ;; (aignet-copies-in-bounds copy aignet2)
                     (posp node)
                     ;; (cut-leaves-bounded cut node cutsdb)
                     (< node (cut-nnodes cutsdb))
                     (<= (cut-nnodes cutsdb) (num-fanins aignet2))
                     ;; (not (equal (ctype (stype (car (lookup-id node aignet2)))) :output))
                     (<= (nodecut-indicesi node cutsdb) (nfix cut))
                     (< (nfix cut) (nodecut-indicesi (+ 1 node) cutsdb))
                     (cut-impl-index-ok cut impl-idx cutsdb rwlib)
                     (cutsdb-correct cutsdb aignet2))
                    (equal (lit-eval lit invals regvals new-aignet2)
                           (id-eval node invals regvals aignet2)
                           ;; (acl2::bool->bit
                           ;;  (cut-value cut cutsdb 
                           ;;             (aignet-record-vals nil invals regvals aignet)))
                           ))
           :hints (("goal" :use eval-of-aignet-build-cut
                    :in-theory (disable eval-of-aignet-build-cut)))
           :fn aignet-build-cut))

  (defret eval-of-rewrite-reimplement-node
    (implies (and (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (rwlib-correct rwlib)
                  (cutsdb-correct cutsdb aignet2)
                  (cutsdb-lit-idsp aignet2 cutsdb)
                  (equal (cut-nnodes cutsdb) (num-fanins aignet2))
                  (aignet-litp lit aignet2))
             (equal (lit-eval new-lit invals regvals new-aignet2)
                    (lit-eval lit invals regvals aignet2)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable lit-eval aignet-idp)))))

  ;; (defret cutsdb-lit-idsp-of-rewrite-reimplement-node
  ;;   (implies (and (cutsdb-ok cutsdb)
  ;;                 (cutsdb-lit-idsp aignet2 cutsdb))
  ;;            (cutsdb-lit-idsp new-aignet2 new-cutsdb)))

  ;; (defret cutsdb-ok-of-rewrite-reimplement-node
  ;;   (implies (cutsdb-ok cutsdb)
  ;;            (cutsdb-ok new-cutsdb)))

  
  ;; (defret cut-nnodes-lte-max-fanin-of-rewrite-reimplement-node
  ;;   (implies (<= (cut-nnodes cutsdb) (+ 1 (fanin-count aignet2)))
  ;;            (<= (cut-nnodes new-cutsdb) (+ 1 (fanin-count new-aignet2)))))

  
  ;; (defret cutsdb-correct-of-rewrite-reimplement-node
  ;;   (implies (and (cutsdb-correct cutsdb aignet2)
  ;;                 (cutsdb-ok cutsdb)
  ;;                 (<= (cut-nnodes cutsdb) (+ 1 (fanin-count aignet2))))
  ;;            (cutsdb-correct new-cutsdb new-aignet2)))

  (defret eba3-length-of-rewrite-reimplement-node
    (implies (and (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (aignet-litp lit aignet2)
                  (equal (cut-nnodes cutsdb) (+ 1 (fanin-count aignet2)))
                  (<= (num-fanins (rwlib->aigs rwlib)) (len eba3)))
             (equal (len new-eba3) (len eba3)))
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defret eba4-length-of-rewrite-reimplement-node
    (implies (and (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (aignet-litp lit aignet2)
                  (equal (cut-nnodes cutsdb) (+ 1 (fanin-count aignet2)))
                  (cutsdb-lit-idsp aignet2 cutsdb)
                  (<= (num-fanins aignet2) (len eba4)))
             (equal (len new-eba4) (len eba4)))
    :hints(("Goal" :in-theory (e/d (cut-impl-index-ok aignet-idp)
                                   (len))))))



(define rewrite-sweep-node ((n natp "index in original aig")
                            (aignet "original aig")
                            (cutsdb cutsdb-ok "cuts for original aig")
                            (rwlib rwlib-wfp "precomputed truth table mappings and implementations")
                            (aignet2 "new aig being constructed")
                            (eba "scratch bits sized to rwlib aignet")
                            (eba2 "scratch bits sized to rwlib aignet")
                            (eba3 "scratch bits sized to rwlib aignet")
                            (eba4 "scratch bits sized to aignet2")
                            (copy "mapping from original to new aig nodes")
                            (copy2 "scratch mappings from rwlib aigs to new nodes")
                            (strash2 "strash table for aignet2")
                            (refcounts "refcounts for original aig")
                            (refcounts2 "refcounts for aignet2, including replacements")
                            (rewrite-stats)
                            (config rewrite-config-p))
  :returns (mv new-aignet2
               new-cutsdb
               new-eba
               new-eba2
               new-copy 
               new-copy2
               new-eba3
               new-eba4
               new-strash2
               new-refcounts2
               new-rewrite-stats)
  :guard (and (<= n (+ -1 (num-fanins aignet)))
              (<= (cut-nnodes cutsdb) (num-fanins aignet2))
              (<= (num-fanins aignet) (lits-length copy))
              (aignet-copies-in-bounds copy aignet2)
              (cutsdb-lit-idsp aignet2 cutsdb)
              (equal (num-ins aignet) (num-ins aignet2))
              (equal (num-regs aignet) (num-regs aignet2))
              (<= (num-fanins aignet) (u32-length refcounts))
              (<= (num-fanins aignet2) (u32-length refcounts2))
              (equal (num-nxsts aignet2) 0)
              (equal (num-outs aignet2) 0)
              (stobj-let
               ((aignet-tmp (rwlib->aigs rwlib)))
               (ok)
               (and (<= (num-fanins aignet-tmp) (lits-length copy2))
                    (<= (num-fanins aignet-tmp) (eba-length eba))
                    (or (eq (rewrite-config->evaluation-method config) :build)
                        (and (<= (num-fanins aignet-tmp) (eba-length eba2))
                             (<= (num-fanins aignet-tmp) (eba-length eba3)))))
               ok))
  ;; :guard-debug t
  :ignore-ok t
  :verify-guards nil
  (b* ((n (lnfix n))
       (aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                     :exec aignet2))
       ((unless (eql (id->type n aignet) (gate-type)))
        (mv aignet2 cutsdb eba eba2 copy copy2 eba3 eba4 strash2 refcounts2 rewrite-stats))
       ((mv lit build-cost cutsdb aignet2 strash2 refcounts2 rewrite-stats)
        (rewrite-copy-node n aignet aignet2 cutsdb copy strash2 refcounts2 rewrite-stats config))
       (eba4 (maybe-grow-eba (num-fanins aignet2) eba4))
       
       ((mv new-lit aignet2 eba eba2 copy2 eba3 eba4 strash2 refcounts2 rewrite-stats)
        (rewrite-reimplement-node
         lit build-cost cutsdb rwlib aignet2 eba eba2 eba3 eba4 copy2 strash2 refcounts2 rewrite-stats config))

       ((mv & refcounts2) (aignet-restore-mffc (lit-id new-lit) (get-u32 n refcounts) aignet2 refcounts2))

       (copy (set-lit n new-lit copy)))
    (mv aignet2 cutsdb eba eba2 copy copy2 eba3 eba4 strash2 refcounts2 rewrite-stats))

  ///
  (def-aignet-preservation-thms rewrite-sweep-node :stobjname aignet2)

  ;; (local (defthm lit->var-lte-fanin-count-when-aignet-litp
  ;;          (implies (aignet-litp lit aignet)
  ;;                   (<= (lit-id lit) (fanin-count aignet)))
  ;;          :hints(("Goal" :in-theory (enable aignet-litp)))))

  (verify-guards rewrite-sweep-node
    :hints (("goal" :do-not-induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable aignet-idp)))))

  (defret rewrite-sweep-node-copies-in-bounds
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (cutsdb-lit-idsp aignet2 cutsdb)
                  (cutsdb-ok cutsdb)
                  (<= (cut-nnodes cutsdb) (num-fanins aignet2))
                  (rwlib-wfp rwlib))
             (aignet-copies-in-bounds new-copy new-aignet2))
    :hints (("goal" :do-not-induct t)))

  (defret stype-counts-of-rewrite-sweep-node
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))

  (defret rewrite-sweep-node-preserves-non-gate-copies
    (implies (and (not (equal (stype (car (lookup-id m aignet))) (xor-stype)))
                  (not (equal (stype (car (lookup-id m aignet))) (and-stype))))
             (equal (nth-lit m new-copy)
                    (nth-lit m copy))) ;; for termhint below
    :hints(("Goal" :in-theory (enable ctype))))

  ;; (defret aignet-lits-comb-equivalent-of-extension

  (defret rewrite-sweep-node-preserves-comb-equiv-for-non-gates
    (implies (and (aignet-copy-is-comb-equivalent-for-non-gates m aignet copy aignet2)
                  (aignet-copies-in-bounds copy aignet2))
             (aignet-copy-is-comb-equivalent-for-non-gates m aignet new-copy new-aignet2))
    :hints(("Goal" :in-theory (e/d (aignet-copy-is-comb-equivalent-for-non-gates)
                                   (rewrite-sweep-node))
            :induct (aignet-copy-is-comb-equivalent-for-non-gates m aignet copy aignet2))))


  (defret rewrite-sweep-node-preserves-refcounts2-len-greater
    (implies (and (< (fanin-count aignet2) (len refcounts2))
                  (cutsdb-lit-idsp aignet2 cutsdb)
                  (aignet-copies-in-bounds copy aignet2)
                  (cutsdb-ok cutsdb)
                  (<= (cut-nnodes cutsdb) (num-fanins aignet2)))
             (< (fanin-count new-aignet2) (len new-refcounts2)))
    :rule-classes (:rewrite :linear))

  (defret copy-length-of-rewrite-sweep-node
    (implies (< (nfix n) (len copy))
             (equal (len new-copy) (len copy))))
  
  (defret copy2-length-of-rewrite-sweep-node
    (implies (and (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (<= (num-fanins (rwlib->aigs rwlib)) (len copy2))
                  (<= (cut-nnodes cutsdb) (num-fanins aignet2))
                  (aignet-copies-in-bounds copy aignet2))
             (equal (len new-copy2) (len copy2))))

  (defret eba-length-of-rewrite-sweep-node
    (implies (and (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (<= (num-fanins (rwlib->aigs rwlib)) (len eba))
                  (<= (cut-nnodes cutsdb) (num-fanins aignet2))
                  (aignet-copies-in-bounds copy aignet2))
             (equal (len new-eba) (len eba))))

  (defret eba2-length-of-rewrite-sweep-node
    (implies (and (not (equal (rewrite-config->evaluation-method config) :build))
                  (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (<= (num-fanins (rwlib->aigs rwlib)) (len eba2))
                  (<= (cut-nnodes cutsdb) (num-fanins aignet2))
                  (aignet-copies-in-bounds copy aignet2))
             (equal (len new-eba2) (len eba2))))

  
  (defret eba3-length-of-rewrite-sweep-node
    (implies (and (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (aignet-copies-in-bounds copy aignet2)
                  (<= (cut-nnodes cutsdb) (+ 1 (fanin-count aignet2)))
                  (<= (num-fanins (rwlib->aigs rwlib)) (len eba3)))
             (equal (len new-eba3) (len eba3))))

  (set-ignore-ok t)

  (defret rewrite-sweep-node-correct
    (implies (and (equal (nfix nn) (+ 1 (nfix n)))
                  (aignet-copy-is-comb-equivalent n aignet copy aignet2)
                  (aignet-copy-is-comb-equivalent-for-non-gates (num-fanins aignet)
                                                                aignet copy aignet2)
                  (rwlib-correct rwlib)
                  (cutsdb-ok cutsdb)
                  (cutsdb-lit-idsp aignet2 cutsdb)
                  (rwlib-wfp rwlib)
                  (aignet-copies-in-bounds copy aignet2)
                  (< (nfix n) (num-fanins aignet))
                  ;; (< (nfix n) (cut-nnodes cutsdb))
                  (<= (cut-nnodes cutsdb) (num-fanins aignet2))
                  (cutsdb-correct cutsdb aignet2))
             (aignet-copy-is-comb-equivalent nn aignet new-copy new-aignet2))
    :hints (;; (and stable-under-simplificationp
            ;;      `(:expand (,(car (last clause))
            ;;                 (:free (lit invals regvals)
            ;;                  (lit-eval (make-lit lit 0) invals regvals aignet)))
            ;;        :in-theory (enable aignet-lits-comb-equivalent
            ;;                           aignet-idp)))
            (acl2::use-termhint
             (b* (((acl2::termhint-seq
                    '`(:expand (,(car (last clause))
                                (:free (lit invals regvals)
                                 (lit-eval (make-lit lit 0) invals regvals aignet)))
                       :in-theory (enable aignet-lits-comb-equivalent
                                          aignet-idp)))))
               nil))))

  (defret cutsdb-ok-of-rewrite-sweep-node
    (implies (cutsdb-ok cutsdb)
             (cutsdb-ok new-cutsdb)))

  (defret cutsdb-lit-idsp-of-rewrite-sweep-node
    (implies (and (cutsdb-lit-idsp aignet2 cutsdb)
                  (cutsdb-ok cutsdb))
             (cutsdb-lit-idsp new-aignet2 new-cutsdb)))

  (defret cut-nnodes-lte-max-fanin-of-rewrite-sweep-node
    (implies (<= (cut-nnodes cutsdb) (+ 1 (fanin-count aignet2)))
             (<= (cut-nnodes new-cutsdb) (+ 1 (fanin-count new-aignet2)))))

  (defret cutsdb-correct-of-rewrite-sweep-node
    (implies (and (cutsdb-correct cutsdb aignet2)
                  (cutsdb-ok cutsdb)
                  (<= (cut-nnodes cutsdb) (+ 1 (fanin-count aignet2))))
             (cutsdb-correct new-cutsdb new-aignet2))))


               ;;    (n (lnfix n))
               ;;    (slot0 (id->slot n 0 aignet))
               ;;    (type (snode->type slot0))
               ;;    ((unless (eql type (gate-type)))
               ;;     nil)
               ;;    (lit0 (snode->fanin slot0))
               ;;    (slot1 (id->slot n 1 aignet))
               ;;    (lit1 (snode->fanin slot1))
               ;;    (flit0-copy (lit-copy lit0 copy))
               ;;    (flit1-copy (lit-copy lit1 copy))
               ;;    ((mv existing key lit0-copy lit1-copy)
               ;;     (aignet-and-gate-simp/strash flit0-copy flit1-copy (default-gatesimp) strash2 aignet2))
               ;;    ((mv build-cost refcounts2)
               ;;     (rewrite-default-copy-deref-and-cost
               ;;      flit0-copy flit1-copy existing lit0-copy lit1-copy aignet2 refcounts2))
               ;;    ((rewrite-config config))
               ;;    ((when (and (not config.zero-cost-replace)
               ;;                (eql 0 build-cost)))
               ;;     ''(:expand ((:free (invals regvals) (id-eval n invals regvals aignet)))
               ;;        :in-theory (enable eval-and-of-lits lit-eval)))
               ;;    ((mv replacep cut-cost cut-index impl-index refcounts2 eba eba2 copy2)
               ;;     (choose-implementation-cuts
               ;;      (nodecut-indicesi n cutsdb)
               ;;      (nodecut-indicesi (+ 1 n) cutsdb)
               ;;      n cutsdb rwlib eba eba2 copy copy2 strash2 aignet2 refcounts2 rewrite-stats))

               ;;    (nodes-before (num-fanins aignet2))
               ;;    ((when (and replacep (if config.zero-cost-replace (<= cut-cost build-cost) (< cut-cost build-cost))))
               ;;     nil))
               ;; ''(:expand ((:free (invals regvals) (id-eval n invals regvals aignet)))
               ;;    :in-theory (enable eval-and-of-lits lit-eval)))))))


(define rewrite-sweep ((n natp "index in original aig")
                       (aignet "original aig")
                       (cutsdb cutsdb-ok "cuts for original aig")
                       (rwlib rwlib-wfp "precomputed truth table mappings and implementations")
                       (aignet2 "new aig being constructed")
                       (eba "scratch bits sized to rwlib aignet")
                       (eba2 "scratch bits sized to rwlib aignet")
                       (eba3 "scratch bits sized to rwlib aignet")
                       (eba4 "scratch bits sized to aignet2")
                       (copy "mapping from original to new aig nodes")
                       (copy2 "scratch mappings from rwlib aigs to new nodes")
                       (strash2 "strash table for aignet2")
                       (refcounts "refcounts for original aig")
                       (refcounts2 "refcounts for aignet2, including replacements")
                       (rewrite-stats)
                       (config rewrite-config-p))
  :returns (mv new-aignet2
               new-cutsdb
               new-eba
               new-eba2
               new-copy
               new-copy2
               new-eba3
               new-eba4
               new-strash2
               new-refcounts2
               new-rewrite-stats)
  :guard (and (<= n (num-fanins aignet))
              (<= (cut-nnodes cutsdb) (num-fanins aignet2))
              (<= (num-fanins aignet) (lits-length copy))
              (aignet-copies-in-bounds copy aignet2)
              (cutsdb-lit-idsp aignet2 cutsdb)
              (equal (num-ins aignet) (num-ins aignet2))
              (equal (num-regs aignet) (num-regs aignet2))
              (<= (num-fanins aignet) (u32-length refcounts))
              (<= (num-fanins aignet2) (u32-length refcounts2))
              (equal (num-nxsts aignet2) 0)
              (equal (num-outs aignet2) 0)
              (stobj-let
               ((aignet-tmp (rwlib->aigs rwlib)))
               (ok)
               (and (<= (num-fanins aignet-tmp) (lits-length copy2))
                    (<= (num-fanins aignet-tmp) (eba-length eba))
                    (or (eq (rewrite-config->evaluation-method config) :build)
                        (and (<= (num-fanins aignet-tmp) (eba-length eba2))
                             (<= (num-fanins aignet-tmp) (eba-length eba3)))))
               ok))
  :verify-guards nil
  :measure (nfix (- (num-fanins aignet) (nfix n)))
  (b* (((when (mbe :logic (zp (- (num-fanins aignet) (nfix n)))
                   :exec (eql n (num-fanins aignet))))
        (b* ((aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                           :exec aignet2)))
          (mv aignet2 cutsdb eba eba2 copy copy2 eba3 eba4 strash2 refcounts2 rewrite-stats)))
       ((mv aignet2 cutsdb eba eba2 copy copy2 eba3 eba4 strash2 refcounts2 rewrite-stats)
        (rewrite-sweep-node n aignet cutsdb rwlib aignet2 eba eba2 eba3 eba4 copy copy2 strash2 refcounts refcounts2 rewrite-stats config)))
    (rewrite-sweep (+ 1 (lnfix n)) aignet cutsdb rwlib aignet2 eba eba2 eba3 eba4 copy copy2 strash2 refcounts refcounts2 rewrite-stats config))
  ///
  
  (defret rewrite-sweep-copies-in-bounds
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (cutsdb-lit-idsp aignet2 cutsdb)
                  (cutsdb-ok cutsdb)
                  (<= (cut-nnodes cutsdb) (num-fanins aignet2))
                  (rwlib-wfp rwlib))
             (and (aignet-copies-in-bounds new-copy new-aignet2))))

  (defret stype-counts-of-rewrite-sweep
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))


  (defret rewrite-sweep-preserves-non-gate-copies
    (implies (and (not (equal (stype (car (lookup-id m aignet))) (xor-stype)))
                  (not (equal (stype (car (lookup-id m aignet))) (and-stype))))
             (equal (nth-lit m new-copy)
                    (nth-lit m copy))))

  (defret rewrite-sweep-preserves-comb-equiv-for-non-gates
    (implies (and (aignet-copy-is-comb-equivalent-for-non-gates m aignet copy aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (cutsdb-lit-idsp aignet2 cutsdb)
                  (cutsdb-ok cutsdb)
                  (<= (cut-nnodes cutsdb) (num-fanins aignet2))
                  (rwlib-wfp rwlib))
             (aignet-copy-is-comb-equivalent-for-non-gates m aignet new-copy new-aignet2)))

  (defret rewrite-sweep-correct
    (implies (and (aignet-copy-is-comb-equivalent n aignet copy aignet2)
                  (aignet-copy-is-comb-equivalent-for-non-gates (num-fanins aignet)
                                                                aignet copy aignet2)
                  (rwlib-correct rwlib)
                  (cutsdb-ok cutsdb)
                  (cutsdb-lit-idsp aignet2 cutsdb)
                  (rwlib-wfp rwlib)
                  (aignet-copies-in-bounds copy aignet2)
                  (<= (nfix n) (num-fanins aignet))
                  (<= (cut-nnodes cutsdb) (num-fanins aignet2))
                  (cutsdb-correct cutsdb aignet2))
             (aignet-copy-is-comb-equivalent (+ 1 (fanin-count aignet))
                                             aignet new-copy new-aignet2))
    :hints (("goal" :induct t :in-theory (enable aignet-idp))))
            ;; (and stable-under-simplificationp
            ;;      `(:expand (,(car (last clause))

  (defret rewrite-sweep-preserves-refcounts2-len-greater
    (implies (and (< (fanin-count aignet2) (len refcounts2))
                  (cutsdb-lit-idsp aignet2 cutsdb)
                  (aignet-copies-in-bounds copy aignet2)
                  (cutsdb-ok cutsdb)
                  (rwlib-wfp rwlib)
                  (<= (cut-nnodes cutsdb) (num-fanins aignet2)))
             (< (fanin-count new-aignet2) (len new-refcounts2)))
    :rule-classes (:rewrite :linear))

  (defret copy-length-of-rewrite-sweep
    (implies (<= (num-fanins aignet) (len copy))
             (equal (len new-copy) (len copy))))

  (defret copy2-length-of-rewrite-sweep
    (implies (and (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (<= (num-fanins (rwlib->aigs rwlib)) (len copy2))
                  (<= (cut-nnodes cutsdb) (num-fanins aignet2))
                  (aignet-copies-in-bounds copy aignet2)
                  (cutsdb-lit-idsp aignet2 cutsdb))
             (equal (len new-copy2) (len copy2))))

  (defret eba-length-of-rewrite-sweep
    (implies (and (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (<= (num-fanins (rwlib->aigs rwlib)) (len eba))
                  (<= (cut-nnodes cutsdb) (num-fanins aignet2))
                  (aignet-copies-in-bounds copy aignet2)
                  (cutsdb-lit-idsp aignet2 cutsdb))
             (equal (len new-eba) (len eba))))

  (defret eba2-length-of-rewrite-sweep
    (implies (and (not (equal (rewrite-config->evaluation-method config) :build))
                  (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (<= (num-fanins (rwlib->aigs rwlib)) (len eba2))
                  (<= (cut-nnodes cutsdb) (num-fanins aignet2))
                  (aignet-copies-in-bounds copy aignet2)
                  (cutsdb-lit-idsp aignet2 cutsdb))
             (equal (len new-eba2) (len eba2))))

  (defret eba3-length-of-rewrite-sweep
    (implies (and (rwlib-wfp rwlib)
                  (cutsdb-ok cutsdb)
                  (cutsdb-lit-idsp aignet2 cutsdb)
                  (aignet-copies-in-bounds copy aignet2)
                  (<= (cut-nnodes cutsdb) (+ 1 (fanin-count aignet2)))
                  (<= (num-fanins (rwlib->aigs rwlib)) (len eba3)))
             (equal (len new-eba3) (len eba3))))

  (defret cutsdb-ok-of-rewrite-sweep
    (implies (cutsdb-ok cutsdb)
             (cutsdb-ok new-cutsdb)))

  (defret cutsdb-lit-idsp-of-rewrite-sweep
    (implies (and (cutsdb-lit-idsp aignet2 cutsdb)
                  (cutsdb-ok cutsdb))
             (cutsdb-lit-idsp new-aignet2 new-cutsdb)))

  (defret cut-nnodes-lte-max-fanin-of-rewrite-sweep
    (implies (<= (cut-nnodes cutsdb) (+ 1 (fanin-count aignet2)))
             (<= (cut-nnodes new-cutsdb) (+ 1 (fanin-count new-aignet2)))))

  (defret cutsdb-correct-of-rewrite-sweep
    (implies (and (cutsdb-correct cutsdb aignet2)
                  (cutsdb-ok cutsdb)
                  (<= (cut-nnodes cutsdb) (+ 1 (fanin-count aignet2))))
             (cutsdb-correct new-cutsdb new-aignet2)))

  (Verify-guards rewrite-sweep))


(fty::deffixequiv aignet-count-gate-refs-iter :args ((aignet aignet))
  :hints(("Goal" :in-theory (enable aignet-count-gate-refs-iter
                                    aignet-count-gate-refs-step))))

(fty::deffixequiv aignet-count-gate-refs$inline :args ((aignet aignet))
  :hints(("Goal" :in-theory (enable aignet-count-gate-refs))))

(define rewrite-copy-core ((aignet "Input aignet")
                           (copy "Mapping from aignet IDs to aignet2 lits -- overwritten")
                           (aignet2)
                           (config rewrite-config-p))
  :returns (mv new-copy new-aignet2)
  :prepwork ((local (in-theory (disable acl2::resize-list-when-atom resize-list
                                        (rwlib-init-abc))))
             (local (defthm cut-leaves-length-when-cutsdb-ok
                      (implies (cutsdb-ok cutsdb)
                               (<= 0 (cut-leaves-length cutsdb)))
                      :hints(("Goal" :in-theory (enable cutsdb-ok))))))
  :guard-debug t
  (b* (((acl2::local-stobjs
         cutsdb
         rwlib
         eba
         eba2
         eba3
         eba4
         copy2
         strash2
         refcounts
         refcounts2
         rewrite-stats)
        (mv copy aignet2
            cutsdb rwlib eba eba2 copy2 eba3 eba4 strash2
            refcounts refcounts2 rewrite-stats))
       (rwlib (rwlib-init-abc rwlib))
       (refcounts (resize-u32 (num-fanins aignet) refcounts))
       (refcounts (aignet-count-gate-refs refcounts aignet))
       ;; (strash (aignet-populate-strash 0 strash aignet))
       ((mv copy aignet2) (init-copy-comb aignet copy aignet2))
       ((acl2::stobj-get eba eba2 eba3 copy2)
        ((aignet-tmp (rwlib->aigs rwlib)))
        (b* ((size (num-fanins aignet-tmp))
             (eba (resize-eba size eba))
             (eba2 (resize-eba size eba2))
             (eba3 (resize-eba size eba3))
             (copy2 (resize-lits size copy2)))
          (mv eba eba2 eba3 copy2)))
       (refcounts2 (resize-u32 (* 2 (num-fanins aignet2)) refcounts2))
       ((mv cuts-checked cutsdb)
        (aignet-derive-cuts aignet2
                            (rewrite-config->cuts4-config config)
                            refcounts2
                            cutsdb))
       (rewrite-stats (incr-rewrite-stats-cuts-checked rewrite-stats cuts-checked))
       ;; (ncuts (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
       ;; (- (cw "; rewrite -- Total cuts: ~x0 (~x1 per node)~%"
       ;;        ncuts (ceiling ncuts (num-fanins aignet)))
       ;;    (cw "; rewrite -- Number of cuts evaluated: ~x0 (~x1 per node)~%"
       ;;        cuts-checked (ceiling cuts-checked (num-fanins aignet))))
       ((mv aignet2 cutsdb eba eba2 copy copy2 eba3 eba4 strash2 refcounts2 rewrite-stats)
        (time$
         (rewrite-sweep 0 aignet cutsdb rwlib aignet2 eba eba2 eba3 eba4 copy copy2 strash2 refcounts refcounts2
                        rewrite-stats config)
         :msg "; rewrite -- sweep: ~st sec, ~sa bytes~%"))
       (- (cw "Rewrite stats:~%")
          (print-rewrite-stats rewrite-stats)))
    (mv copy aignet2
        cutsdb rwlib eba eba2 copy2 eba3 eba4 strash2
        refcounts refcounts2 rewrite-stats))
  ///
  (defret rewrite-copy-core-copies-in-bounds
    (aignet-copies-in-bounds new-copy new-aignet2))

  (defret stype-counts-of-rewrite-copy-core
    (and (equal (stype-count :pi new-aignet2) (stype-count :pi aignet))
         (equal (stype-count :reg new-aignet2) (stype-count :reg aignet))
         (equal (stype-count :po new-aignet2) 0)
         (equal (stype-count :nxst new-aignet2) 0)))

  (defret len-copy-of-rewrite-copy-core
    (equal (len new-copy)
           (num-fanins aignet)))

  (defret rewrite-copy-core-correct
    (aignet-copy-is-comb-equivalent (+ 1 (fanin-count aignet))
                                    aignet new-copy new-aignet2))

  (defthm rewrite-copy-core-normalize-inputs
    (implies (syntaxp (not (and (equal aignet2 ''nil)
                                (equal copy ''nil))))
             (equal (rewrite-copy-core aignet copy aignet2 config)
                    (rewrite-copy-core aignet nil nil config)))))


(define rewrite-core ((aignet "Input aignet")
                      (aignet2 "New aignet -- overwritten")
                      (config rewrite-config-p))
  :returns (new-aignet2)
  (b* (((acl2::local-stobjs copy)
        (mv copy aignet2))
       ;; (- (acl2::sneaky-clear))
       ((mv copy aignet2)
        (rewrite-copy-core aignet copy aignet2 config))
       (aignet2 (finish-copy-comb aignet copy aignet2)))
    ;; (with-local-state
    ;;   (mv-let (ans state)
    ;;     (acl2::sneaky-alist state)
    ;;     (cw "sneaky-alist: ~x0~%" ans)))
    (mv copy aignet2))
  ///
  (defret stype-counts-of-rewrite-core
    (and (equal (stype-count :pi new-aignet2) (stype-count :pi aignet))
         (equal (stype-count :reg new-aignet2) (stype-count :reg aignet))
         (equal (stype-count :po new-aignet2) (stype-count :po aignet))))
                 
  (defret rewrite-core-correct
    (comb-equiv new-aignet2 aignet))

  (defthm rewrite-core-normalize-inputs
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal (rewrite-core aignet aignet2 config)
                    (rewrite-core aignet nil config)))))


(define rewrite ((aignet "Input aignet")
                 (aignet2 "New aignet -- overwritten")
                 (config rewrite-config-p))
  :parents (aignet-comb-transforms)
  :short "Apply DAG-aware rewriting to the network."
  :returns (new-aignet2)
  (b* (((acl2::local-stobjs aignet-tmp)
        (mv aignet2 aignet-tmp))
       (aignet-tmp (rewrite-core aignet aignet-tmp config))
       (aignet2 (aignet-prune-comb aignet-tmp aignet2 (rewrite-config->gatesimp config))))
    (mv aignet2 aignet-tmp))
  ///
  (defret stype-counts-of-rewrite
    (and (equal (stype-count :pi new-aignet2) (stype-count :pi aignet))
         (equal (stype-count :reg new-aignet2) (stype-count :reg aignet))
         (equal (stype-count :po new-aignet2) (stype-count :po aignet))))
                 
  (defret rewrite-correct
    (comb-equiv new-aignet2 aignet))

  (defthm rewrite-normalize-inputs
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal (rewrite aignet aignet2 config)
                    (rewrite aignet nil config)))))


(define rewrite! ((aignet "Input aignet -- overwritten")
                 (config rewrite-config-p))
  :parents (aignet-comb-transforms)
  :short "Apply DAG-aware rewriting to the network."
  :long "<p>Note: This implementation is heavily based on the one in
ABC, developed and maintained at Berkeley by Alan Mishchenko.</p>

<p>Settings for the transform can be tweaked using the @('config') input, which
is a @(see rewrite-config) object.</p>"
  :returns (new-aignet)
  (b* (((acl2::local-stobjs aignet-tmp)
        (mv aignet aignet-tmp))
       (aignet-tmp (rewrite-core aignet aignet-tmp config))
       (aignet (aignet-prune-comb aignet-tmp aignet (rewrite-config->gatesimp config))))
    (mv aignet aignet-tmp))
  ///
  (defret stype-counts-of-rewrite!
    (and (equal (stype-count :pi new-aignet) (stype-count :pi aignet))
         (equal (stype-count :reg new-aignet) (stype-count :reg aignet))
         (equal (stype-count :po new-aignet) (stype-count :po aignet))))
                 
  (defret rewrite!-correct
    (comb-equiv new-aignet aignet)))
