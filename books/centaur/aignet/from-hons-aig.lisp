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
(include-book "construction")
(include-book "misc/hons-help" :dir :system)
(include-book "centaur/aig/aig-vars-fast" :dir :system)
(include-book "centaur/aig/aig-base" :dir :system)
(include-book "centaur/aig/aig-vars" :dir :system)
(include-book "std/lists/index-of" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))
(local (include-book "centaur/aig/accumulate-nodes-vars" :dir :system))

(local (in-theory (disable nth update-nth
                           acl2::nfix-when-not-natp
                           resize-list
                           acl2::nthcdr-of-cdr
                           acl2::resize-list-when-empty
                           acl2::make-list-ac-redef
                           set::double-containment
                           set::sets-are-true-lists
                           make-list-ac)))

(local (in-theory (disable true-listp-update-nth
                           acl2::nth-with-large-index
                           acl2::aig-env-lookup)))


;; Functions for translating between aignet bitarrs and hons-aig envs:



(define env-to-bitarr (vars env)
  (if (atom vars)
      nil
    (cons (if (acl2::aig-env-lookup (car vars) env) 1 0)
          (env-to-bitarr (cdr vars) env)))
  ///
  (defthm nth-in-env-to-bitarr
    (implies (< (nfix n) (len vars))
             (equal (nth n (env-to-bitarr vars env))
                    (if (acl2::aig-env-lookup (nth n vars) env) 1 0)))
    :hints(("Goal" :in-theory (enable nth env-to-bitarr)))))

(define env-update-bitarr-aux ((n natp) vars env bitarr)
  :guard (<= (+ (nfix n) (len vars)) (bits-length bitarr))
  :returns (new-bitarr)
  (if (atom vars)
      bitarr
    (b* ((bitarr (set-bit n (acl2::bool->bit (acl2::aig-env-lookup (car vars) env)) bitarr)))
      (env-update-bitarr-aux (1+ (lnfix n)) (cdr vars) env bitarr)))
  ///
  (local (defthm take-n-plus-one
           (Equal (take (+ 1 (nfix n)) x)
                  (append (take n x) (list (nth n x))))
           :hints(("Goal" :in-theory (e/d (nth acl2::repeat)
                                          (acl2::take-of-too-many
                                           ;; acl2::take-when-atom
                                           acl2::take-of-1
                                           acl2::take-of-zero))))))

  (local (defthm take-of-update-nth
           (equal (take n (update-nth n val x))
                  (take n x))
           :hints(("Goal" :in-theory (enable update-nth)))))

  (local (defthm nthcdr-of-update-nth
           (equal (nthcdr n (update-nth m v x))
                  (if (<= (nfix n) (nfix m))
                      (update-nth (- (nfix m) (nfix n)) v (nthcdr n x))
                    (nthcdr n x)))
           :hints(("Goal" :in-theory (enable update-nth)))))

  (std::defret env-update-bitarr-aux-elim
    (implies (<= (+ (nfix n) (len vars)) (len bitarr))
             (equal new-bitarr
                    (append (take n bitarr)
                            (env-to-bitarr vars env)
                            (nthcdr (+ (nfix n) (len vars)) bitarr))))
    :hints(("Goal" :in-theory (e/d (env-to-bitarr) (acl2::take-redefinition nthcdr (force)))))))

(define env-update-bitarr (vars env bitarr)
  :enabled t
  (mbe :logic (non-exec (env-to-bitarr vars env))
       :exec (b* ((bitarr (resize-bits (len vars) bitarr)))
               (env-update-bitarr-aux 0 vars env bitarr))))
 

(local (defthm hons-assoc-equal-in-pairlis
         (equal (hons-assoc-equal v (pairlis$ vars vals))
                (and (member v vars)
                     (cons v (nth (acl2::index-of v vars) vals))))
         :hints(("Goal" :in-theory (enable pairlis$ acl2::index-of nth)))))

(define bits-to-bools-aux ((i natp) bitarr)
  :guard (<= i (bits-length bitarr))
  :measure (nfix (- (bits-length bitarr) (nfix i)))
  (b* (((when (mbe :logic (zp (- (bits-length bitarr) (nfix i)))
                   :exec (eql (bits-length bitarr) i)))
        nil))
    (cons (equal (get-bit i bitarr) 1)
          (bits-to-bools-aux (1+ (lnfix i)) bitarr))))

(define bits-to-bools (bitarr)
  :verify-guards nil
  (mbe :logic (non-exec (let ((x bitarr))
                          (if (atom x)
                              nil
                            (cons (if (eql (bfix (car x)) 1) t nil)
                                  (bits-to-bools (cdr x))))))
       :exec (bits-to-bools-aux 0 bitarr))
  ///
  (defthm nth-of-bits-to-bools
    (Equal (nth n (bits-to-bools x))
           (equal (nth n x) 1))
    :hints(("Goal" :in-theory (enable nth))))

  (local 
   (defthm bits-to-bools-aux-is-bits-to-bools
     (equal (bits-to-bools-aux i bitarr)
            (bits-to-bools (nthcdr i bitarr)))
     :hints(("Goal" :in-theory (e/d (bits-to-bools-aux nthcdr acl2::cdr-over-nthcdr))
             :induct t
             :expand (bits-to-bools (nthcdr i bitarr))))))

  (verify-guards bits-to-bools
    :hints(("Goal" :in-theory (disable (bits-to-bools))))))


(define aignet-bitarr-to-aig-env ((vars true-listp) bitarr)
  :returns (env)
  (pairlis$ vars (bits-to-bools bitarr))
  ///
  (std::defret hons-assoc-equal-in-aignet-bitarr-to-aig-env
    (equal (hons-assoc-equal v env)
           (and (member v vars)
                (cons v (equal 1 (nth (acl2::index-of v vars) bitarr))))))

  (std::defret aig-env-lookup-in-aignet-bitarr-to-aig-env
    (equal (acl2::aig-env-lookup v env)
           (or (not (member v vars))
               (equal 1 (nth (acl2::index-of v vars) bitarr))))
    :hints(("Goal" :in-theory (enable acl2::aig-env-lookup)))))





(define frame-to-bools-aux ((n natp) (i natp) frames)
  :guard (and (< n (frames-nrows frames))
              (<= i (frames-ncols frames)))
  :measure (nfix (- (len (nth n (stobjs::2darr->rows frames))) (nfix i)))
  (b* (((when (mbe :logic (non-exec (zp (- (len (nth n (stobjs::2darr->rows frames))) (nfix i))))
                   :exec (eql (frames-ncols frames) i)))
        nil))
    (cons (equal (frames-get2 n i frames) 1)
          (frame-to-bools-aux n (1+ (lnfix i)) frames))))

(define frame-to-bools ((n natp) frames)
  :verify-guards nil
  :guard (< n (frames-nrows frames))
  :enabled t
  (mbe :logic (non-exec (bits-to-bools (nth n (stobjs::2darr->rows frames))))
       :exec (frame-to-bools-aux n 0 frames))
  ///

  (local 
   (defthm frame-to-bools-aux-is-frame-to-bools
     (equal (frame-to-bools-aux n i frames)
            (bits-to-bools (nthcdr i (nth n (stobjs::2darr->rows frames)))))
     :hints(("Goal" :in-theory (enable frame-to-bools-aux nthcdr acl2::cdr-over-nthcdr)
             :induct t
             :expand ((bits-to-bools (nthcdr i (nth n (stobjs::2darr->rows frames)))))))))

  (verify-guards frame-to-bools
    :hints(("Goal" :in-theory (disable (frame-to-bools))))))



(define aignet-frames-to-aig-envs-aux ((n natp) frames (invars true-listp))
  :guard (and (<= n (frames-nrows frames))
              (equal (len invars) (frames-ncols frames)))
  :measure (nfix (- (frames-nrows frames) (nfix n)))
  (b* (((when (mbe :logic (zp (- (frames-nrows frames) (nfix n)))
                   :exec (eql (frames-nrows frames) n)))
        nil))
    (cons (pairlis$ invars (frame-to-bools n frames))
          (aignet-frames-to-aig-envs-aux (1+ (lnfix n)) frames invars))))
       

(define aignet-frame-array-to-aig-envs (frame-arr (invars true-listp))
  :non-executable t
  :verify-guards nil
  :returns (envs)
  (if (atom frame-arr)
      nil
    (cons (aignet-bitarr-to-aig-env invars (car frame-arr))
          (aignet-frame-array-to-aig-envs (cdr frame-arr) invars)))
  ///
  (defthm lookup-in-aignet-frame-array-to-aig-envs
    (implies (< (nfix n) (len frame-arr))
             (equal (nth n (aignet-frame-array-to-aig-envs frame-arr invars))
                    (aignet-bitarr-to-aig-env invars (nth n frame-arr))))
    :hints(("Goal" :in-theory (enable nth))))

  (std::defret len-of-aignet-frame-array-to-aig-envs
    (equal (len envs) (len frame-arr)))

  (defthm aignet-frames-to-aig-envs-aux-in-terms-of-aignet-frame-array-to-aig-envs
    (equal (aignet-frames-to-aig-envs-aux n frames invars)
           (aignet-frame-array-to-aig-envs (nthcdr n (stobjs::2darr->rows frames)) invars))
    :hints(("Goal" :in-theory (enable aignet-frames-to-aig-envs-aux
                                      aignet-bitarr-to-aig-env)
            :induct t
            :expand ((aignet-frame-array-to-aig-envs (nthcdr n (stobjs::2darr->rows frames)) invars))))))

(define aignet-frames-to-aig-envs (frames (invars true-listp))
  :returns (envs)
  :guard (equal (len invars) (frames-ncols frames))
  :enabled t
  (mbe :logic (non-exec (aignet-frame-array-to-aig-envs (stobjs::2darr->rows frames) invars))
       :exec (aignet-frames-to-aig-envs-aux 0 frames invars))
  ///
  (verify-guards aignet-frames-to-aig-envs))






;; Translating from Hons AIGs to aignets.

;; We need a memoization table so that we don't revisit AIG nodes we've already
;; seen.



;; An xmemo is a fast alist mapping hons AIGs to literals.  It's well-formed if
;; all literals are in bounds.
(defsection xmemo-well-formedp
  (defun xmemo-well-formedp (xmemo aignet)
    (declare (xargs :stobjs aignet))
    (b* (((when (atom xmemo)) t)
         ((when (atom (car xmemo)))
          (xmemo-well-formedp (cdr xmemo) aignet))
         (val (cdar xmemo)))
      (and (litp val)
           (fanin-litp val aignet)
           (xmemo-well-formedp (cdr xmemo) aignet))))

  (defthm xmemo-well-formedp-lookup
    (let ((look (hons-assoc-equal aig xmemo)))
      (implies (and look
                    (xmemo-well-formedp xmemo aignet))
               (and (aignet-litp (cdr look) aignet)
                    (litp (cdr look)))))
    :hints(("Goal" :in-theory (enable hons-assoc-equal))))

  (defthm xmemo-well-formedp-of-extension
    (implies (and (aignet-extension-binding)
                  (xmemo-well-formedp xmemo orig))
             (xmemo-well-formedp xmemo new))))

;; (retroactive-add-aignet-preservation-thm-local
;;  xmemo-well-formedp-preserved
;;  :vars (xmemo)
;;  :body `(implies (xmemo-well-formedp xmemo ,orig-stobj)
;;                  (xmemo-well-formedp xmemo ,new-stobj))
;;  :hints `(("Goal" :in-theory (e/d (xmemo-well-formedp) (,fn$))
;;            :induct (xmemo-well-formedp xmemo ,orig-stobj))))




;; we also need a mapping from hons AIG variables to AIGNET lits.
(defsection good-varmap-p

  (defund good-varmap-p (varmap aignet)
    (declare (xargs :stobjs aignet))
    (if (atom varmap)
        t
      (and (or (atom (car varmap))
               (and (acl2::aig-var-p (caar varmap))
                    (litp (cdar varmap))
                    (fanin-litp (cdar varmap) aignet)))
           (good-varmap-p (cdr varmap) aignet))))

  (local (in-theory (enable good-varmap-p)))

  (fty::deffixequiv good-varmap-p :args ((aignet aignet)))

  (defthm lookup-when-good-varmap-p
    (implies (and (good-varmap-p varmap aignet)
                  (hons-assoc-equal var varmap))
             (and (aignet-litp (cdr (hons-assoc-equal var varmap)) aignet)
                  (litp (cdr (hons-assoc-equal var varmap)))))
    :hints(("Goal" :in-theory (enable hons-assoc-equal))))

  (defthm good-varmap-p-of-extension
    (implies (and (aignet-extension-binding)
                  (good-varmap-p varmap orig))
             (good-varmap-p varmap new))))

;; (retroactive-add-aignet-preservation-thm-local
;;  good-varmap-p-preserved
;;  :vars (varmap)
;;  :body `(implies (good-varmap-p varmap ,orig-stobj)
;;                  (good-varmap-p varmap ,new-stobj))
;;  :hints `(("Goal" :in-theory (e/d (good-varmap-p) (,fn$))
;;            :induct (good-varmap-p varmap ,orig-stobj))))






(define aig-to-aignet ((x "hons aig")
                       (xmemo "memo table (fast alist)")
                       (varmap "input variable mapping")
                       (gatesimp gatesimp-p)
                       strash
                       aignet)
  :returns (mv (lit litp :rule-classes (:rewrite :type-prescription))
               xmemo strash aignet)
  :guard (and (good-varmap-p varmap aignet)
              (xmemo-well-formedp xmemo aignet))
  :verify-guards nil
  (aig-cases
   x
   :true (mv 1 xmemo strash aignet)
   :false (mv 0 xmemo strash aignet)
   :var (b* ((look (hons-get x varmap)))
          (mv (if look
                  (lit-fix (cdr look))
                ;; For missing variables, produce TRUE to match semantics of
                ;; aig-eval.
                1)
              xmemo strash aignet))
   :inv (b* (((mv lit xmemo strash aignet)
              (aig-to-aignet (car x) xmemo varmap gatesimp strash aignet)))
          (mv (lit-negate lit) xmemo strash aignet))
   :and (b* ((look (hons-get x xmemo))
             ((when look)
              (mv (lit-fix (cdr look)) xmemo strash aignet))
             ((mv lit1 xmemo strash aignet)
              (aig-to-aignet (car x) xmemo varmap gatesimp strash aignet))
             ((when (int= (lit-fix lit1) 0))
              (mv 0 (hons-acons x 0 xmemo) strash aignet))
             ((mv lit2 xmemo strash aignet)
              (aig-to-aignet (cdr x) xmemo varmap gatesimp strash aignet))
             ((mv lit strash aignet)
              (aignet-hash-and lit1 lit2 gatesimp strash aignet))
             (xmemo (hons-acons x lit xmemo)))
          (mv lit xmemo strash aignet)))
  ///

  (def-aignet-preservation-thms aig-to-aignet)

  (defthm aig-to-aignet-well-formed
    (implies (and (good-varmap-p varmap (double-rewrite aignet))
                  (xmemo-well-formedp xmemo (double-rewrite aignet)))
             (b* (((mv lit xmemo ?strash aignet)
                   (aig-to-aignet x xmemo varmap gatesimp strash aignet)))
               (and (aignet-litp lit aignet)
                    (xmemo-well-formedp xmemo aignet))))
    :hints (("goal" :induct (aig-to-aignet x xmemo varmap gatesimp strash aignet)
             :expand ((aig-to-aignet x xmemo varmap gatesimp strash aignet)
                      (aig-to-aignet nil xmemo varmap gatesimp strash aignet)
                      (aig-to-aignet t xmemo varmap gatesimp strash aignet))
             :in-theory (e/d ()
                             ((:definition aig-to-aignet))))))

  (verify-guards aig-to-aignet)

  (defthm stype-count-of-aig-to-aignet
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count
                     stype
                     (mv-nth 3 (aig-to-aignet
                                x xmemo varmap gatesimp strash aignet)))
                    (stype-count stype aignet)))
    :hints((acl2::just-induct-and-expand
            (aig-to-aignet x xmemo varmap gatesimp strash aignet))))
  )





(defsection xmemo-ok
  ;; ;; Correctness condition for the xmemo table.
  ;; (defun reverse-varmap (varmap)
  ;;   (b* (((when (atom varmap))
  ;;         nil)
  ;;        ((when (atom (car varmap)))
  ;;         (reverse-varmap (cdr varmap)))
  ;;        ((cons aig-node lit) (car varmap))
  ;;        ((when (consp aig-node))
  ;;         (reverse-varmap (cdr varmap))))
  ;;     (cons (cons (lit-id lit) aig-node)
  ;;           (reverse-varmap (cdr varmap)))))

  (local (in-theory (disable id-eval)))

  (defun-nx aignet-eval-to-env (varmap in-vals reg-vals aignet)
    (b* (((when (atom varmap))
          nil)
         ((when (atom (car varmap)))
          (aignet-eval-to-env (cdr varmap) in-vals reg-vals aignet))
         ((cons aig-var lit) (car varmap))
         (val (= 1 (lit-eval lit in-vals reg-vals aignet))))
      (cons (cons aig-var val)
            (aignet-eval-to-env (cdr varmap) in-vals reg-vals aignet))))

  (defthm aignet-eval-to-env-of-extension
    (implies (and (aignet-extension-binding)
                  (good-varmap-p varmap orig))
             (equal (aignet-eval-to-env varmap invals regvals new)
                    (aignet-eval-to-env varmap invals regvals orig)))
    :hints(("Goal" :in-theory (enable good-varmap-p))))


  (defthm present-in-aignet-eval-to-env
    (iff (hons-assoc-equal
          x (aignet-eval-to-env varmap in-vals reg-vals aignet))
         (hons-assoc-equal x varmap)))

  (defthm not-present-in-aignet-eval-to-env
    (implies (not (hons-assoc-equal x varmap))
             (not (hons-assoc-equal
                   x (aignet-eval-to-env varmap in-vals reg-vals aignet)))))

  (defthm lookup-in-aignet-eval-to-env
    (implies (hons-assoc-equal x varmap)
             (equal (cdr (hons-assoc-equal x (aignet-eval-to-env varmap in-vals reg-vals aignet)))
                    (= 1 (lit-eval (cdr (hons-assoc-equal x varmap))
                                   in-vals reg-vals aignet))))
    :hints(("Goal"
            :induct (aignet-eval-to-env varmap in-vals reg-vals aignet))))

  (defthm aig-env-lookup-of-aignet-eval-to-env
    (implies (hons-assoc-equal v varmap)
             (equal (acl2::aig-env-lookup v (aignet-eval-to-env varmap in-vals reg-vals aignet))
                    (= 1 (lit-eval (cdr (hons-assoc-equal v varmap)) in-vals reg-vals aignet))))
    :hints(("Goal" :in-theory (enable aignet-eval-to-env acl2::aig-env-lookup))))

  (defun-nx xmemo-ok (xmemo varmap in-vals reg-vals aignet)
    (b* (((when (atom xmemo)) t)
         ((when (atom (car xmemo)))
          (xmemo-ok (cdr xmemo) varmap in-vals reg-vals aignet))
         ((cons aig lit) (car xmemo))
         (env (aignet-eval-to-env varmap in-vals reg-vals aignet)))
      (and (equal (aig-eval aig env)
                  (= 1 (lit-eval lit in-vals reg-vals aignet)))
           (xmemo-ok (cdr xmemo) varmap in-vals reg-vals aignet))))

  (in-theory (disable xmemo-ok))
  (local (in-theory (enable xmemo-ok)))

  ;;(defun-sk xmemo-ok (xmemo varmap in-vals reg-vals aignet)
  ;;  (forall
  ;;   (aig)
  ;;   (let ((look   (hons-assoc-equal aig xmemo))
  ;;         (rvarmap (reverse-varmap varmap)))
  ;;     (implies look
  ;;              (equal (id-eval (lit-id (cdr look)) in-vals reg-vals aignet)
  ;;                     (xor (lit-negp (cdr look))
  ;;                          (aig-eval aig (aignet-eval-to-env in-vals reg-vals rvarmap)))))))
  ;;  :rewrite :direct)

  (local (defthmd equal-1-to-bitp
           (implies (not (equal x 0))
                    (equal (equal x 1)
                           (acl2::bitp x)))
           :hints(("Goal" :in-theory (enable acl2::bitp)))))

  (defthm xmemo-ok-lookup
    (implies (and (xmemo-ok xmemo varmap in-vals reg-vals aignet)
                  (hons-assoc-equal aig xmemo))
             (equal (lit-eval (cdr (hons-assoc-equal aig xmemo))
                             in-vals reg-vals aignet)
                    (acl2::bool->bit
                     (aig-eval aig (aignet-eval-to-env
                                    varmap in-vals reg-vals aignet)))))
    :hints(("Goal" :in-theory (enable equal-1-to-bitp))))

  (defthm xmemo-ok-lookup-bind-free
    (implies (and (bind-free '((varmap . varmap)))
                  (xmemo-ok xmemo varmap in-vals reg-vals aignet)
                  (hons-assoc-equal aig xmemo))
             (equal (lit-eval (cdr (hons-assoc-equal aig xmemo))
                              in-vals reg-vals aignet)
                    (acl2::bool->bit
                     (aig-eval aig (aignet-eval-to-env
                                    varmap in-vals reg-vals aignet))))))

  ;;(defmacro xmemo-ok-preserved-hint ()
  ;;  '(and stable-under-simplificationp
  ;;        (b* (((mv ok1 conclsubst)
  ;;              (find-unifying-lit '(xmemo-ok xmemo varmap in-vals reg-vals aignet) clause))
  ;;             ((unless ok1) nil)
  ;;             (conclaignet (cdr (assoc 'aignet conclsubst))))
  ;;          `(:computed-hint-replacement
  ;;            ((and stable-under-simplificationp
  ;;                  (b* (((mv ok2 hypsubst)
  ;;                        (find-unifying-lit '(not (xmemo-ok xmemo varmap in-vals reg-vals aignet))
  ;;                                           clause))
  ;;                       ((unless ok2) nil)
  ;;                       (hypaignet (cdr (assoc 'aignet hypsubst))))
  ;;                    `(:use ((:instance xmemo-ok-necc
  ;;                             (aignet ,hypaignet)
  ;;                             (aig (xmemo-ok-witness xmemo varmap in-vals reg-vals ,',conclaignet))))
  ;;                      :in-theory (e/d () (xmemo-ok-necc xmemo-ok))))))
  ;;            :expand ((xmemo-ok xmemo varmap in-vals reg-vals ,conclaignet))))))

  ;; (defthmd xmemo-ok-frame
  ;;   (implies (and (not (equal n *objsi))
  ;;                 (not (equal n *num-objs*)))
  ;;            (iff (xmemo-ok xmemo varmap in-vals reg-vals (update-nth n v aignet))
  ;;                 (xmemo-ok xmemo varmap in-vals reg-vals aignet)))
  ;;   :hints(("Goal" :in-theory (e/d* (aignet-frame-thms)))))


  ;; (add-to-ruleset aignet-frame-thms xmemo-ok-frame)

  ;; (defcong nth-equiv iff (xmemo-ok xmemo varmap in-vals reg-vals aignet) 4
  ;;   :hints(("Goal" :in-theory (e/d (nfix)))))

  (defthm xmemo-ok-of-acons
    (equal (xmemo-ok (cons (cons aig lit) xmemo)
                     varmap in-vals reg-vals aignet)
           (and (xmemo-ok xmemo varmap in-vals reg-vals aignet)
                (equal (lit-eval lit in-vals reg-vals aignet)
                       (acl2::bool->bit
                        (aig-eval aig (aignet-eval-to-env
                                       varmap in-vals reg-vals aignet))))))
    :hints(("Goal" :in-theory (enable equal-1-to-bitp))))

  (defthm xmemo-ok-of-extension
    (implies (and (aignet-extension-binding)
                  (good-varmap-p varmap orig)
                  (xmemo-well-formedp xmemo orig))
             (iff (xmemo-ok xmemo varmap invals regvals new)
                  (xmemo-ok xmemo varmap invals regvals orig))))

  (defthm xmemo-ok-of-nil
    (xmemo-ok nil varmap in-vals reg-vals aignet)
    :hints(("Goal" :in-theory (enable xmemo-ok)))))




(defsection aig-to-aignet-correct

  (local (in-theory (disable aignet-add-in)))

  ;; (defthm equal-of-xors
  ;;   (iff (equal (xor a b) (xor a c))
  ;;        (iff b c)))



  (local (defthm id-eval-1
           (implies (not (equal (id-eval n in-vals reg-vals aignet) 0))
                    (equal (id-eval n in-vals reg-vals aignet) 1))
           :hints (("goal" :use bitp-of-id-eval
                    :in-theory (e/d (acl2::bitp)
                                    (bitp-of-id-eval))))))

  (defthm aig-to-aignet-correct

; binds both
;   (1) Network Input IDs to Hons-AIG Variables, and
;   (2) Network Reg  IDs to Hons-AIG Variables.

    (implies (and (good-varmap-p varmap (double-rewrite aignet))
                  (xmemo-well-formedp xmemo1 (double-rewrite aignet))
                  (xmemo-ok xmemo1 varmap in-vals reg-vals (double-rewrite aignet)))

             ;; What do we need to know about xmemo?
             ;; Xmemo binds some aig nodes to literals.
             ;; So we need to know everything bound in it evaluates correctly w.r.t.
             ;; the.

             ;; Strash binds (hash lit1 lit2) --> gate-name
             ;; For each binding we need to know
             ;;    Lookup(gate-name) = { lit1, lit2 }


             (b* (((mv lit xmemo ?strash aignet1)
                   (aig-to-aignet x xmemo1 varmap strash1 gatesimp aignet)))
               (and (xmemo-ok xmemo varmap in-vals reg-vals aignet1)
                    (equal (lit-eval lit in-vals reg-vals aignet1)
                           (acl2::bool->bit
                            (aig-eval x (aignet-eval-to-env
                                         varmap in-vals reg-vals aignet))))
                    (equal (aignet-eval-to-env varmap in-vals reg-vals aignet1)
                           (aignet-eval-to-env varmap in-vals reg-vals aignet)))))
    :hints(("Goal"
            :in-theory (e/d ((:induction aig-to-aignet)
                             aignet-eval-to-env
                             ; nth-aignet-of-aig-to-aignet
                             eval-and-of-lits
                             acl2::aig-env-lookup)
                            (aig-eval xmemo-ok
                                      acl2::nth-with-large-index
                                      xmemo-well-formedp
                                      ;; aignet-fix-when-aignetp
                                      aignet-eval-to-env
                                      id-eval
                                      id-eval-1
                                      default-car default-cdr
                                      acl2::b-xor))
            :induct t
            :do-not-induct t
            :do-not '(generalize fertilize eliminate-destructors)
            :expand ((:free (env) (aig-eval x env))
                     (:free (env) (aig-eval nil env))
                     (:free (env) (aig-eval t env))
                     (aig-to-aignet x xmemo1 varmap strash1 gatesimp aignet)
                     (aig-to-aignet nil xmemo1 varmap strash1 gatesimp aignet)
                     (aig-to-aignet t xmemo1 varmap strash1 gatesimp
                                 aignet)
                     ;; (:free (aignet a x v s g n)
                     ;;  (lit-eval (mv-nth 0 (aig-to-aignet a x v s g n))
                     ;;            in-vals reg-vals aignet))
                     ))
           (and stable-under-simplificationp
                '(:in-theory (e/d (id-eval-1) ()))))
    :otf-flg t))




(defsection aiglist-to-aignet

  (local (in-theory (disable id-eval
                             acl2::nth-with-large-index
                             set::double-containment)))

  (defund aiglist-to-aignet-aux (x xmemo varmap gatesimp strash aignet lits)
    (declare (xargs :stobjs (aignet strash)
                    :guard (and (gatesimp-p gatesimp)
                                (good-varmap-p varmap aignet)
                                (xmemo-well-formedp xmemo aignet)
                                (true-listp lits))
                    :verify-guards nil))
    (b* (((when (atom x))
          (mv (reverse lits) xmemo strash aignet))
         ((mv lit xmemo strash aignet)
          (aig-to-aignet (car x) xmemo varmap gatesimp strash aignet)))
      (aiglist-to-aignet-aux (cdr x) xmemo varmap gatesimp strash aignet
                             (cons lit lits))))

  ;; just puts the gates in and adds inputs/regs as needed, doesn't set up
  ;; outputs or reg inputs
  (defund aiglist-to-aignet (x xmemo varmap gatesimp strash aignet)
    (declare (xargs :stobjs (aignet strash)
                    :guard (and (gatesimp-p gatesimp)
                                (good-varmap-p varmap aignet)
                                (xmemo-well-formedp xmemo aignet))
                    :verify-guards nil))
    (mbe :logic (b* (((when (atom x))
                      (mv nil xmemo strash aignet))
                     ((mv lit xmemo strash aignet)
                      (aig-to-aignet (car x) xmemo varmap gatesimp strash aignet))
                     ((mv rest xmemo strash aignet)
                      (aiglist-to-aignet (cdr x) xmemo varmap gatesimp strash aignet)))
                  (mv (cons lit rest)
                      xmemo strash aignet))
         :exec
         (aiglist-to-aignet-aux x xmemo varmap gatesimp strash aignet nil)))

  (local (in-theory (enable aiglist-to-aignet
                            aiglist-to-aignet-aux)))

  (defthm aiglist-to-aignet-aux-elim
    (implies (true-listp lits)
             (equal (aiglist-to-aignet-aux x xmemo varmap gatesimp strash aignet lits)
                    (mv-let (rest-lits xmemo strash aignet)
                      (aiglist-to-aignet x xmemo varmap gatesimp strash aignet)
                      (mv (revappend lits rest-lits) xmemo strash aignet)))))

  (def-aignet-preservation-thms aiglist-to-aignet)

  (defthm lit-listp-aiglist-to-aignet-lits
    (lit-listp (mv-nth 0 (aiglist-to-aignet x xmemo varmap gatesimp strash aignet))))


  (defthm aiglist-to-aignet-well-formed
    (implies (and (good-varmap-p varmap (double-rewrite aignet))
                  (xmemo-well-formedp xmemo (double-rewrite aignet)))
             (b* (((mv lits xmemo ?strash aignet)
                   (aiglist-to-aignet x xmemo varmap gatesimp strash aignet)))
               (and (aignet-lit-listp lits aignet)
                    (xmemo-well-formedp xmemo aignet)))))

  (defthm len-lits-of-aiglist-to-aignet
    (b* (((mv lits ?xmemo ?strash ?aignet)
                   (aiglist-to-aignet x xmemo varmap gatesimp strash aignet)))
      (equal (len lits) (len x))))

  (defthm aignet-litp-nth-of-aignet-lit-list
    (implies (and (aignet-lit-listp lits aignet)
                  (< (nfix n) (len lits)))
             (aignet-litp (nth n lits) aignet))
    :hints(("Goal" :in-theory (enable nth))))

  (defthm aignet-litp-nth-of-aiglist-to-aignet
    (implies (and (good-varmap-p varmap (double-rewrite aignet))
                  (xmemo-well-formedp xmemo (double-rewrite aignet))
                  (< (nfix n) (len x)))
             (b* (((mv lits ?xmemo ?strash aignet)
                   (aiglist-to-aignet x xmemo varmap gatesimp strash aignet)))
               (aignet-litp (nth n lits) aignet))))

  (defthm aignet-litp-nth-of-aiglist-to-aignet-ext
    (implies (and (good-varmap-p varmap (double-rewrite aignet))
                  (xmemo-well-formedp xmemo (double-rewrite aignet))
                  (< (nfix n) (len x)))
             (b* (((mv lits ?xmemo ?strash new-aignet)
                   (aiglist-to-aignet x xmemo varmap gatesimp strash aignet)))
               (implies (aignet-extension-p aignet-ext new-aignet)
                        (aignet-litp (nth n lits) aignet-ext)))))
    

  (defun bools->bits (x)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (cons (acl2::bool->bit (car x))
            (bools->bits (cdr x)))))

  (defthm aiglist-to-aignet-correct
    (implies (and (good-varmap-p varmap aignet)
                  (xmemo-well-formedp xmemo1 aignet)
                  (xmemo-ok xmemo1 varmap in-vals reg-vals aignet))

             (b* (((mv lits xmemo ?strash aignet1)
                   (aiglist-to-aignet x xmemo1 varmap strash1 gatesimp aignet)))
               (and (xmemo-ok xmemo varmap in-vals reg-vals aignet1)
                    (equal (lit-eval-list lits in-vals reg-vals aignet1)
                           (bools->bits
                            (acl2::aig-eval-list
                             x (aignet-eval-to-env varmap in-vals reg-vals aignet))))
                    (equal (aignet-eval-to-env varmap in-vals reg-vals aignet1)
                           (aignet-eval-to-env varmap in-vals reg-vals aignet))))))

  (local (defthm lit-eval-of-nth-in-terms-of-lit-eval-list
           (implies (< (nfix n) (len lst))
                    (equal (lit-eval (nth n lst) in-vals reg-vals aignet)
                           (nth n (lit-eval-list lst in-vals reg-vals aignet))))
           :hints(("Goal" :in-theory (enable nth lit-eval-list)))))

  (defthm nth-of-bools->bits
    (implies (< (nfix n) (len x))
             (Equal (nth n (bools->bits x))
                    (acl2::bool->bit (nth n x))))
    :hints(("Goal" :in-theory (enable nth))))

  (defthm nth-of-aig-eval-list
    (Equal (nth n (acl2::aig-eval-list x env))
           (aig-eval (nth n x) env))
    :hints(("Goal" :in-theory (enable nth))))

  (defthm aiglist-to-aignet-nth-correct
    (implies (and (good-varmap-p varmap aignet)
                  (xmemo-well-formedp xmemo1 aignet)
                  (xmemo-ok xmemo1 varmap in-vals reg-vals aignet)
                  (< (nfix n) (len x)))
             (b* (((mv lits ?xmemo ?strash aignet1)
                   (aiglist-to-aignet x xmemo1 varmap strash1 gatesimp aignet)))
               (equal (lit-eval (nth n lits) in-vals reg-vals aignet1)
                      (acl2::bool->bit
                       (aig-eval
                        (nth n x)
                        (aignet-eval-to-env varmap in-vals reg-vals aignet)))))))

  (verify-guards aiglist-to-aignet-aux)
  (verify-guards aiglist-to-aignet)

  (defun aiglist-to-aignet-top (x varmap gatesimp strash aignet)
    (declare (xargs :stobjs (aignet strash)
                    :guard (and (gatesimp-p gatesimp)
                                (good-varmap-p varmap aignet))))
    (b* (((mv lits xmemo strash aignet)
          (aiglist-to-aignet x nil varmap gatesimp strash aignet)))
      (fast-alist-free xmemo)
      (mv lits strash aignet)))

  (defthm len-aiglist-to-aignet
    (equal (len (mv-nth 0 (aiglist-to-aignet x xmemo varmap gmemo gatesimp aignet)))
           (len x))
    :hints(("Goal" :in-theory (enable aiglist-to-aignet))))

  (defthm stype-count-of-aiglist-to-aignet
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count
                     stype
                     (mv-nth 3 (aiglist-to-aignet
                                x xmemo varmap gatesimp strash aignet)))
                    (stype-count stype aignet)))
    :hints(("goal" :in-theory (enable (:i aiglist-to-aignet))
            :induct
            (aiglist-to-aignet x xmemo varmap gatesimp strash aignet)
            :expand
            ((aiglist-to-aignet x xmemo varmap gatesimp strash aignet))))))






(defsection keys-bound

  (defund keys-bound (keys al)
    (declare (xargs :guard t))
    (if (atom keys)
        t
      (and (hons-get (car keys) al)
           (keys-bound (cdr keys) al))))

  (local (in-theory (enable keys-bound acl2::accumulate-aig-vars)))

  (defthm keys-bound-of-add-extra
    (implies (keys-bound keys al)
             (keys-bound keys (cons x al)))
    :hints(("Goal" :in-theory (enable hons-assoc-equal))))

  (defthm keys-bound-of-add
    (implies (keys-bound keys al)
             (keys-bound (cons x keys) (cons (cons x y) al)))
    :hints(("Goal" :in-theory (enable hons-assoc-equal))))

  (defthmd member-when-keys-bound
    (implies (and (keys-bound keys al)
                  (not (hons-assoc-equal x al)))
             (not (member x keys))))

  (defthm keys-bound-of-accumulate-aig-vars
    (implies (keys-bound acc nodetable)
             (mv-let (nodetable acc)
               (acl2::accumulate-aig-vars x nodetable acc)
               (keys-bound acc nodetable))))

  (defthm no-duplicatesp-of-accumulate-aig-vars
    (implies (and (no-duplicatesp acc)
                  (keys-bound acc nodetable))
             (mv-let (nodetable acc)
               (acl2::accumulate-aig-vars x nodetable acc)
               (declare (ignore nodetable))
               (no-duplicatesp acc)))
    :hints(("Goal" :in-theory (enable member-when-keys-bound)))))


(define fanin-id-range-p ((start natp) (n natp) aignet)
  :measure (nfix n)
  (if (zp n)
      t
    (and (fanin-litp (mk-lit start 0) aignet)
         (fanin-id-range-p (+ 1 (lnfix start)) (1- n) aignet)))
  ///
  
  (std::set-define-current-function aignet-add-ins)
  (local (std::defret fanin-id-range-p-of-aignet-add-ins-lemma
           (fanin-id-range-p (+ 1 (node-count aignet)) n new-aignet)
           :hints(("Goal" :in-theory (enable aignet-add-ins)))))

  (std::defret fanin-id-range-p-of-aignet-add-ins
    (implies (equal id (+ 1 (node-count aignet)))
             (fanin-id-range-p id n new-aignet))
    :hints(("Goal" :in-theory (enable aignet-add-ins))))

  (std::defret aignet-add-ins-preserves-fanin-id-range-p
    (implies (fanin-id-range-p id count aignet)
             (fanin-id-range-p id count new-aignet))
    :hints(("Goal" :in-theory (enable aignet-add-ins))))

  (std::set-define-current-function aignet-add-regs)
  (local (std::defret fanin-id-range-p-of-aignet-add-regs-lemma
           (fanin-id-range-p (+ 1 (node-count aignet)) n new-aignet)
           :hints(("Goal" :in-theory (enable aignet-add-regs)))))

  (std::defret fanin-id-range-p-of-aignet-add-regs
    (implies (equal id (+ 1 (node-count aignet)))
             (fanin-id-range-p id n new-aignet))
    :hints(("Goal" :in-theory (enable aignet-add-regs))))

  (std::defret aignet-add-regs-preserves-fanin-id-range-p
    (implies (fanin-id-range-p id count aignet)
             (fanin-id-range-p id count new-aignet))
    :hints(("Goal" :in-theory (enable aignet-add-regs)))))



(define consecutive-vars-to-varmap ((n natp) vars varmap)
  :returns (new-varmap)
  (b* (((when (atom vars)) varmap)
       (varmap (hons-acons (car vars) (mk-lit n 0) varmap)))
    (consecutive-vars-to-varmap (1+ (lnfix n)) (cdr vars) varmap))
  ///
  (std::defret lookup-in-consecutive-vars-to-varmap-under-iff
    (iff (hons-assoc-equal v new-varmap)
         (or (member v vars) (hons-assoc-equal v varmap))))

  (std::defret lookup-in-consecutive-vars-to-varmap-when-not-var
    (implies (double-rewrite (not (member v vars)))
             (equal (hons-assoc-equal v new-varmap)
                    (hons-assoc-equal v varmap))))

  (std::defret lookup-in-consecutive-vars-to-varmap-when-var
    (implies (and (double-rewrite (member v vars))
                  (no-duplicatesp vars))
             (equal (hons-assoc-equal v new-varmap)
                    (cons v (mk-lit (+ (nfix n) (acl2::index-of v vars)) 0))))
    :hints(("Goal" :in-theory (enable acl2::index-of))))

  (std::defret good-varmap-p-of-consecutive-vars-to-varmap
    (implies (and (good-varmap-p varmap aignet)
                  (acl2::aig-var-listp vars)
                  (fanin-id-range-p n (len vars) aignet))
             (good-varmap-p new-varmap aignet))
    :hints(("Goal" :in-theory (enable fanin-id-range-p good-varmap-p)))))





                        
           
                



;; (defsection make-varmap

;;   (define make-varmap (vars regp acc aignet)
;;     (declare (xargs :stobjs aignet))
;;     :returns (mv varmap new-aignet)
;;     (if (atom vars)
;;         (mv acc aignet)
;;       (b* ((lit (mk-lit (num-nodes aignet) 0))
;;            (aignet (if regp
;;                        (aignet-add-reg aignet)
;;                      (aignet-add-in aignet)))
;;            (acc (hons-acons (car vars) lit acc)))
;;         (make-varmap (cdr vars) regp acc aignet)))
;;     ///

;;     (local (in-theory (enable make-varmap)))

;;     (defthm true-listp-make-varmap
;;       (equal (true-listp (mv-nth 0 (make-varmap vars regp acc aignet)))
;;              (true-listp acc))
;;       :rule-classes
;;       (:rewrite
;;        (:type-prescription
;;         :corollary
;;         (implies (true-listp acc)
;;                  (true-listp (mv-nth 0 (make-varmap vars regp acc aignet)))))))

;;     (def-aignet-preservation-thms make-varmap)

;;     (defthm alistp-make-varmap
;;       (equal (alistp (mv-nth 0 (make-varmap vars regp acc aignet)))
;;              (alistp acc)))

;;     (defthm len-make-varmap
;;       (equal (len (mv-nth 0 (make-varmap vars regp acc aignet)))
;;              (+ (len vars) (len acc))))

;;     (defthm alist-keys-of-make-varmap
;;       (equal (alist-keys (mv-nth 0 (make-varmap vars regp acc aignet)))
;;              (revappend vars (alist-keys acc)))
;;       :hints(("Goal" :in-theory (enable alist-keys))))

;;     (defun non-bool-atom-listp (x)
;;       (declare (xargs :guard t))
;;       (if (atom x)
;;           t
;;         (and (atom (car x))
;;              (not (booleanp (car x)))
;;              (acl2::aig-var-listp (cdr x)))))

;;     (defthm good-varmap-p-of-make-varmap
;;       (implies (and (good-varmap-p acc aignet)
;;                     (acl2::aig-var-listp vars))
;;                (mv-let (acc aignet)
;;                  (make-varmap vars regp acc aignet)
;;                  (good-varmap-p acc aignet)))
;;       :hints(("Goal" :in-theory (enable good-varmap-p))))

;;     (local (defthm litp-integerp
;;              (implies (litp lit)
;;                       (and (integerp lit)
;;                            (<= 0 lit)))))

;;     (defun bound-to-regs-in-varmap (names varmap aignet)
;;       (declare (xargs :stobjs aignet
;;                       :guard-debug t
;;                       :guard (good-varmap-p varmap aignet)))
;;       (if (atom names)
;;           t
;;         (and (hons-assoc-equal (car names) varmap)
;;              (int= (id->type (lit-id (cdr (hons-assoc-equal (car names) varmap)))
;;                              aignet)
;;                    (in-type))
;;              (int= (io-id->regp (lit-id (cdr (hons-assoc-equal (car names) varmap)))
;;                                 aignet)
;;                    1)
;;              (bound-to-regs-in-varmap (cdr names) varmap aignet))))

;;     (local (in-theory (disable litp-integerp)))

;;     (defthm bound-to-regs-in-varmap-of-aignet-extension
;;       (implies (and (aignet-extension-binding)
;;                     (good-varmap-p varmap orig))
;;                (equal (bound-to-regs-in-varmap names varmap new)
;;                       (bound-to-regs-in-varmap names varmap orig))))

;;     (defthm bound-to-regs-in-varmap-preserved-by-varmap-add-reg
;;       (implies (and (bound-to-regs-in-varmap vars1 acc aignet)
;;                     (equal (id->type (lit-id lit) aignet) (in-type))
;;                     (equal (io-id->regp (lit-id lit) aignet) 1))
;;                (bound-to-regs-in-varmap
;;                 vars1
;;                 (cons (cons v lit) acc)
;;                 aignet)))



;;     (defthm make-varmap-preserves-inp
;;       (implies (and (good-varmap-p varmap aignet)
;;                     (acl2::aig-var-listp vars)
;;                     (hons-assoc-equal x varmap)
;;                     (equal (id->type (lit-id (cdr (hons-assoc-equal x varmap)))
;;                                      aignet)
;;                            (in-type)))
;;                (mv-let (varmap aignet)
;;                  (make-varmap vars f varmap aignet)
;;                  (equal (ctype
;;                          (stype (car (lookup-id (lit-id (cdr (hons-assoc-equal x varmap)))
;;                                                 aignet))))
;;                         (in-ctype))))
;;       :hints(("Goal" :in-theory (enable good-varmap-p))))

;;     (defthm make-varmap-preserves-regp
;;       (implies (and (good-varmap-p varmap aignet)
;;                     (acl2::aig-var-listp vars)
;;                     (hons-assoc-equal x varmap)
;;                     (equal (io-id->regp (lit-id (cdr (hons-assoc-equal x varmap)))
;;                                         aignet)
;;                            1))
;;                (mv-let (varmap aignet)
;;                  (make-varmap vars t varmap aignet)
;;                  (equal (regp
;;                          (stype (car (lookup-id (lit-id (cdr (hons-assoc-equal x varmap)))
;;                                                 aignet))))
;;                         1)))
;;       :hints(("Goal" :in-theory (enable good-varmap-p))))

;;     (defthm make-varmap-preserves-bound-to-regs
;;       (implies (and (good-varmap-p varmap aignet)
;;                     (acl2::aig-var-listp vars)
;;                     (bound-to-regs-in-varmap names varmap aignet))
;;                (mv-let (varmap aignet)
;;                  (make-varmap vars t varmap aignet)
;;                  (bound-to-regs-in-varmap
;;                   names varmap aignet)))
;;       :hints(("Goal" :in-theory (enable good-varmap-p))))

;;     (defthm make-varmap-preserves-lookup
;;       (implies (hons-assoc-equal x varmap)
;;                (hons-assoc-equal x (mv-nth 0 (make-varmap vars f varmap aignet)))))

;;     (defthm make-varmap-bound-to-regs
;;       (implies (and (good-varmap-p varmap aignet)
;;                     (acl2::aig-var-listp vars))
;;                (mv-let (varmap aignet)
;;                  (make-varmap vars t varmap aignet)
;;                  (bound-to-regs-in-varmap
;;                   vars varmap aignet)))
;;       :hints(("Goal" :in-theory (e/d (good-varmap-p)

;; ; Matt K. mod 5/2016 (type-set bit for {1}): type-set of bit allowed linear
;; ; arithmetic to make progress that sent proof in a different direction.

;;                                      ((:t regp))))))

;;     (defthm num-ins-of-make-varmap
;;       (equal (stype-count (pi-stype) (mv-nth 1 (make-varmap vars nil acc aignet)))
;;              (+ (stype-count (pi-stype) aignet)
;;                 (len vars)))
;;       :hints(("Goal" :in-theory (enable make-varmap))))

;;     (defthm num-reg-of-make-varmap
;;       (equal (stype-count :reg (mv-nth 1 (make-varmap vars t acc aignet)))
;;              (+ (stype-count :reg aignet)
;;                 (len vars)))
;;       :hints(("Goal" :in-theory (enable make-varmap))))

;;     (defthm stype-count-of-make-varmap
;;       (implies (not (equal (stype-fix stype) :pi))
;;                (equal (stype-count stype (mv-nth 1 (make-varmap vars nil acc aignet)))
;;                       (stype-count stype aignet)))
;;       :hints(("Goal" :in-theory (enable make-varmap))))

;;     (defthm stype-count-of-make-varmap-regp
;;       (implies (not (equal (stype-fix stype) :reg))
;;                (equal (stype-count stype (mv-nth 1 (make-varmap vars t acc aignet)))
;;                       (stype-count stype aignet)))
;;       :hints(("Goal" :in-theory (enable make-varmap))))

;;     (std::defret lookup-in-make-varmap-under-iff
;;       (iff (hons-assoc-equal v varmap)
;;            (or (member v vars) (hons-assoc-equal v acc))))

;;     (std::defret lookup-in-make-varmap-when-not-in-vars
;;       (implies (not (member v vars))
;;                (equal (hons-assoc-equal v varmap)
;;                       (hons-assoc-equal v acc))))

;;     (std::defret lookup-in-make-varmap
;;       (implies (and regp
;;                     (member v vars))
;;                (and (equal (lit-neg (cdr (hons-assoc-equal v varmap))) 0)
;;                     (equal (car (lookup-id (lit-id (cdr (hons-assoc-equal v varmap))) new-aignet))
;;                            (reg-node))
;;                     (implies (no-duplicatesp vars)
;;                              (equal (stype-count :reg (cdr (lookup-id (lit-id (cdr (hons-assoc-equal v varmap))) new-aignet)))
;;                                     (+ (acl2::index-of v vars)
;;                                        (stype-count :reg aignet))))))
;;       :hints(("Goal" :in-theory (enable acl2::index-of))))))


;; (local (include-book "centaur/misc/alist-equiv" :dir :system))


;; (local
;;  (defsection set-difference


;;    (defthm hons-sd1-is-set-difference
;;      (equal (acl2::hons-sd1 a b)
;;             (set-difference-equal a (alist-keys b)))
;;      :hints(("Goal" :in-theory (enable alist-keys set-difference-equal))))

;;    (defthm set-difference-of-cons-non-member
;;      (implies (not (member k x))
;;               (equal (set-difference$ x (cons k y))
;;                      (set-difference$ x y)))
;;      :hints(("Goal" :in-theory (enable set-difference$))))))

;; (defsection add-to-varmap

;;   (define add-to-varmap (vars regp acc aignet)
;;     (declare (xargs :stobjs aignet))
;;     :returns (mv new-varmap new-aignet)
;;     (if (atom vars)
;;         (mv acc aignet)
;;       (if (hons-get (car vars) acc)
;;           (add-to-varmap (cdr vars) regp acc aignet)
;;         (b* ((lit (mk-lit (num-nodes aignet) 0))
;;              (aignet (if regp
;;                          (aignet-add-reg aignet)
;;                        (aignet-add-in aignet)))
;;              (acc (hons-acons (car vars) lit acc)))
;;           (add-to-varmap
;;            (cdr vars) regp acc aignet))))
;;     ///

;;     (local (in-theory (enable add-to-varmap)))

;;     (def-aignet-preservation-thms add-to-varmap)

;;     (defthm true-listp-add-to-varmap
;;       (equal (true-listp (mv-nth 0 (add-to-varmap vars regp acc aignet)))
;;              (true-listp acc))
;;       :rule-classes (:rewrite
;;                      (:type-prescription
;;                       :corollary
;;                       (implies (true-listp acc)
;;                                (true-listp (mv-nth 0 (add-to-varmap vars regp acc aignet)))))))

;;     (defthm alistp-add-to-varmap
;;       (equal (alistp (mv-nth 0 (add-to-varmap vars regp acc aignet)))
;;              (alistp acc)))

;;     (defthm alist-keys-of-add-to-varmap
;;       (implies (no-duplicatesp vars)
;;                (equal (alist-keys (mv-nth 0 (add-to-varmap vars regp acc aignet)))
;;                       (revappend (acl2::hons-sd1 vars acc) (alist-keys acc))))
;;       :hints(("Goal" :in-theory (enable set-difference$
;;                                         alist-keys)
;;               :induct (add-to-varmap vars regp acc aignet))))

;;     (local (defthmd len-alist-keys
;;              (implies (alistp x)
;;                       (equal (len (alist-keys x))
;;                              (len x)))
;;              :hints(("Goal" :in-theory (enable alist-keys)))))




;;     (defthm len-add-to-varmap
;;       (implies (and (no-duplicatesp vars)
;;                     (alistp acc)) ;; shouldn't be necessary, just a shortcut
;;                (equal (len (mv-nth 0 (add-to-varmap vars regp acc aignet)))
;;                       (+ (len (acl2::hons-sd1 vars acc))
;;                          (len acc))))
;;       :hints (("goal" :use ((:instance len-alist-keys
;;                              (x (mv-nth 0 (add-to-varmap vars regp acc aignet))))
;;                             (:instance len-alist-keys
;;                              (x acc))))))

;;     (defthm good-varmap-p-of-add-to-varmap
;;       (implies (and (good-varmap-p acc aignet)
;;                     (acl2::aig-var-listp vars))
;;                (mv-let (acc aignet)
;;                  (add-to-varmap vars regp acc aignet)
;;                  (good-varmap-p acc aignet)))
;;       :hints(("Goal" :in-theory (enable good-varmap-p))))

;;     (std::defret num-outs-of-add-to-varmap
;;       (equal (stype-count :po new-aignet)
;;              (stype-count :po aignet)))

;;     (std::defret num-nxsts-of-add-to-varmap
;;       (equal (stype-count :nxst new-aignet)
;;              (stype-count :nxst aignet)))

;;     (std::defret num-ins-of-add-to-varmap
;;       (equal (stype-count :pi new-aignet)
;;              (if regp
;;                  (stype-count :pi aignet)
;;                (+ (stype-count :pi aignet)
;;                   (- (len new-varmap)
;;                      (len acc))))))

;;     (std::defret num-regs-of-add-to-varmap
;;       (equal (stype-count :reg new-aignet)
;;              (if regp
;;                  (+ (stype-count :reg aignet)
;;                   (- (len new-varmap)
;;                      (len acc)))
;;                (stype-count :reg aignet))))))



;; (defsection first-n-rev-alist-keys
;;   (defund first-n-rev-alist-keys (n alist acc)
;;     (declare (xargs :guard (and (natp n)
;;                                 (alistp alist)
;;                                 (<= n (len alist)))
;;                     :measure (nfix n)))
;;     (if (zp n)
;;         acc
;;       (first-n-rev-alist-keys
;;        (1- (lnfix n)) (cdr alist)
;;        (cons (caar alist) acc))))

;;   (local (in-theory (enable first-n-rev-alist-keys
;;                             set-difference$)))
;;   (local (include-book "centaur/misc/lists" :dir :system))
;;   (local (in-theory (disable acl2::take-redefinition)))

;;   (defthm first-n-rev-def
;;     (implies (and (alistp alist)
;;                   (<= (nfix n) (len alist)))
;;              (equal (first-n-rev-alist-keys n alist acc)
;;                     (revappend (take n (alist-keys alist)) acc)))
;;     :hints(("Goal" :in-theory (enable alist-keys))))

;;   (local (defthm take-of-append-len-of-first
;;            (implies (and (equal n (len a))
;;                          (true-listp a))
;;                     (equal (take n (append a b))
;;                            a))
;;            :hints(("Goal" :in-theory (e/d (alist-keys))))))


;;   (defthm first-n-rev-is-hons-sd1
;;     (b* (((mv varmap &)
;;           (make-varmap vars1 regp1 nil aignet1))
;;          ((mv varmap &) (add-to-varmap vars2 regp2 varmap aignet2))
;;          (nins (- (len varmap) (len vars1))))
;;       (implies (no-duplicatesp vars2)
;;                (equal (first-n-rev-alist-keys nins varmap nil)
;;                       (set-difference$ vars2 vars1))))
;;     :hints(("Goal" :in-theory (disable append acl2::rev))))

;;   (in-theory (disable first-n-rev-def))

;;   (defthm true-listp-first-n-rev-alist-key
;;     (equal (true-listp (first-n-rev-alist-keys n alist acc))
;;            (true-listp acc))))



(local (defthm member-implies-natp-index-of-strong
         (implies (double-rewrite (member k x))
                  (natp (acl2::index-of k x)))))

(local (defthm member-implies-index-of-less-strong
         (implies (double-rewrite (member k x))
                  (< (acl2::index-of k x)
                     (len x)))
         :rule-classes (:rewrite :linear)))



(defsection aig-fsm-prepare-aignet/varmap
  (local (in-theory (enable length)))


  (defthm aiglist-vars-of-append
    (equal (acl2::aiglist-vars (append a b))
           (set::union (acl2::aiglist-vars a)
                       (acl2::aiglist-vars b)))
    :hints(("Goal" :in-theory (enable acl2::aiglist-vars))))

  ;; (local (defthm aig-vars-of-append-is-aig-vars-of-cons
  ;;          (implies (true-listp x)
  ;;                   (equal (aig-vars (append x y))
  ;;                          (aig-vars (cons x y))))))

  (local (defthm no-duplicatesp-of-set-diff
           (implies (no-duplicatesp x)
                    (no-duplicatesp (set-difference$ x y)))
           :hints(("Goal" :in-theory (enable set-difference$)))))

  ;; (local (defthm no-duplicatesp-remove
  ;;          (implies (no-duplicatesp x)
  ;;                   (no-duplicatesp (remove k x)))))

  ;; (local (defthm set-equiv-of-remove-car
  ;;          (implies (and (acl2::set-equiv x y)
  ;;                        (no-duplicatesp x)
  ;;                        (consp x))
  ;;                   (acl2::set-equiv (cdr x) (remove (car x) y)))
  ;;          :hints (("Goal" :in-theory (enable acl2::set-unequal-witness-rw)))))

  ;; (local (defun len-under-set-equiv-when-no-duplicatesp-ind (x new-x)
  ;;          (if (atom x)
  ;;              new-x
  ;;            (len-under-set-equiv-when-no-duplicatesp-ind
  ;;             (cdr x) (remove (car x) new-x)))))

  ;; (local (defthm len-under-set-equiv-when-no-duplicatesp
  ;;          (implies (and (no-duplicatesp x)
  ;;                        (acl2::set-equiv new-x (double-rewrite x))
  ;;                        (syntaxp (not (subtermp new-x x)))
  ;;                        (no-duplicatesp new-x))
  ;;                   (equal (len x) (len new-x)))
  ;;          :hints (("goal" :induct (len-under-set-equiv-when-no-duplicatesp-ind x new-x)))))

  (define aig-fsm-prepare-aignet/varmap (reg-alist out-list max-nodes aignet)
    (declare (xargs :stobjs aignet
                    :guard (posp max-nodes)
                    :guard-debug t))
    :returns (mv varmap input-vars reg-vars new-aignet)
    (b* ((reg-aigs (alist-vals reg-alist))
         (all-vars (acl2::aig-vars-unordered-list
                    (append reg-aigs out-list)))
         (reg-vars (alist-keys reg-alist))
         (in-vars (acl2::hons-set-diff all-vars reg-vars))
         (nregs    (len reg-vars))
         (nins (len in-vars))
         (nouts (len out-list))
         (max-nodes (mbe :logic (if (posp max-nodes)
                                    max-nodes
                                  1000)
                         :exec max-nodes))
         (aignet (aignet-init nouts nregs nins max-nodes aignet))
;; ; (reg-lits (lits-of-type 0 nregs (reg-type)))
;; ; (varmap    (make-fast-alist (pairlis$ reg-vars reg-lits)))
;;          ((mv varmap aignet) (make-varmap reg-vars t nil aignet))
;; ; (input-vars (acl2::hons-sd1 all-vars varmap))
;; ; (nins     (length input-vars))
;; ; (- (cw "ins: ~x0~%" nins))
;; ; (inp-lits (lits-of-type 0 nins (input-type)))
;; ; (varmap    (acl2::make-fal (pairlis$ input-vars inp-lits) varmap))
;;          ((mv varmap aignet)   (add-to-varmap all-vars nil varmap aignet))
         
         (aignet (aignet-add-ins nins aignet))
         (aignet (aignet-add-regs nregs aignet))

         (varmap (consecutive-vars-to-varmap 1 in-vars nil))
         (varmap (consecutive-vars-to-varmap (+ 1 nins) reg-vars varmap)))
      (mv varmap in-vars reg-vars aignet))
    ///

    (local (in-theory (enable aig-fsm-prepare-aignet/varmap)))

    (defthm true-listp-of-aig-fsm-prepare-aignet/varmap-invars
      (true-listp (mv-nth 1 (aig-fsm-prepare-aignet/varmap reg-alist out-list
                                                           max-gates aignet)))
      :rule-classes (:rewrite :type-prescription))

    (defthm true-listp-of-aig-fsm-prepare-aignet/varmap-regvars
      (true-listp (mv-nth 2 (aig-fsm-prepare-aignet/varmap reg-alist out-list
                                                           max-gates aignet)))
      :rule-classes (:rewrite :type-prescription))

    ;; (defthm aignet-nodes-ok-of-aig-fsm-prepare-aignet/varmap
    ;;   (aignet-nodes-ok (mv-nth 3 (aig-fsm-prepare-aignet/varmap
    ;;                               reg-alist out-list max-nodes aignet))))

    (std::defret num-outs-of-aig-fsm-prepare-aignet/varmap
      (equal (stype-count :po new-aignet) 0))

    (std::defret num-nxsts-of-aig-fsm-prepare-aignet/varmap
      (equal (stype-count :nxst new-aignet) 0))

    ;; (defthm len-first-n-rev-alist-keys
    ;;   (equal (len (first-n-rev-alist-keys n x acc))
    ;;          (+ (nfix n) (len acc)))
    ;;   :hints(("Goal" :in-theory (enable first-n-rev-alist-keys))))

    (std::defret num-ins-of-aig-fsm-prepare-aignet/varmap
      (equal (stype-count :pi new-aignet)
             (len input-vars)))

    (std::defret num-regs-of-aig-fsm-prepare-aignet/varmap
      (equal (stype-count :reg new-aignet)
             (len (alist-keys reg-alist))))

    (std::defret reg-vars-of-aig-fsm-prepare-aignet/varmap
      (equal reg-vars (alist-keys reg-alist)))

    (std::defret in-vars-of-aig-fsm-prepare-aignet/varmap
      (acl2::set-equiv input-vars
                       (set-difference$ (acl2::aiglist-vars (append (alist-vals reg-alist) out-list))
                                        (alist-keys reg-alist))))

    (std::defret aig-fsm-prepare-input-varmap-lookup
      (implies (and (member v (acl2::aiglist-vars (append (alist-vals reg-alist) out-list)))
                    (not (hons-assoc-equal v reg-alist)))
               (b* ((index (acl2::index-of v input-vars))
                    (input-id (node-count (lookup-stype index :pi new-aignet))))
                 (equal (hons-assoc-equal v varmap)
                        (cons v (mk-lit input-id 0))))))

    ;; (std::defretd input-id-of-aig-fsm-prepare-input-varmap-lookup
    ;;   (implies (and (member v (aig-vars (append (alist-vals reg-alist) out-list)))
    ;;                 (not (hons-assoc-equal v reg-alist)))
    ;;            (b* ((index (acl2::index-of v input-vars))
    ;;                 (input-id (node-count (lookup-stype index :pi new-aignet))))
    ;;              (equal input-id (+ 1 index)))))

    (std::defret aig-fsm-prepare-reg-varmap-lookup
      (implies (and (member v (acl2::aiglist-vars (append (alist-vals reg-alist) out-list)))
                    (hons-assoc-equal v reg-alist)
                    (no-duplicatesp (alist-keys reg-alist)))
               (b* ((index (acl2::index-of v (alist-keys reg-alist)))
                    (reg-id (node-count (lookup-stype index :reg new-aignet))))
                 (equal (hons-assoc-equal v varmap)
                        (cons v (mk-lit reg-id 0))))))


    (defthm aig-var-listp-of-accumulate-aig-vars
      (equal (acl2::aig-var-listp
              (mv-nth 1 (acl2::accumulate-aig-vars x nodetable acc)))
             (acl2::aig-var-listp acc))
      :hints(("Goal" :in-theory (enable acl2::accumulate-aig-vars))))


    (defthm aig-var-listp-of-set-difference
      (implies (acl2::aig-var-listp x)
               (acl2::aig-var-listp (set-difference$ x y)))
      :hints(("Goal" :in-theory (enable set-difference$))))


    (defthm aig-var-listp-of-accumulate-aig-vars-list
      (iff (acl2::aig-var-listp (mv-nth 1 (acl2::accumulate-aig-vars-list x nodetable acc)))
           (acl2::aig-var-listp acc))
      :hints(("Goal" :in-theory (enable acl2::accumulate-aig-vars-list))))

    (std::defret good-varmap-p-of-aig-fsm-prepare-aignet/varmap
      (implies (acl2::aig-var-listp (alist-keys reg-alist))
               (good-varmap-p varmap new-aignet)))

    ;; (std::defretd reg-id-of-aig-fsm-prepare-reg-varmap-lookup
    ;;   (implies (and (member v (aig-vars (append (alist-vals reg-alist) out-list)))
    ;;                 (hons-assoc-equal v reg-alist)
    ;;                 (no-duplicatesp (alist-keys reg-alist)))
    ;;            (b* ((index (acl2::index-of v (alist-keys reg-alist)))
    ;;                 (reg-id (node-count (lookup-stype index :reg new-aignet))))
    ;;              (equal reg-id (+ 1 (len index))))))
    ))


  ;;(defthmd outs-length-of-aig-fsm-prepare-aignet/varmap
  ;;  (equal (len (nth *outsi* (mv-nth 3 (aig-fsm-prepare-aignet/varmap
  ;;                                      regs outs max-gates aignet))))
  ;;         (len outs))
  ;;  :hints(("Goal" :in-theory (e/d* (aignet-frame-thms)
  ;;                                  (len (len))))))

  ;;(defthmd regs-length-of-aig-fsm-prepare-aignet/varmap
  ;;  (equal (len (nth *regsi* (mv-nth 3 (aig-fsm-prepare-aignet/varmap
  ;;                                      regs outs max-gates aignet))))
  ;;         (len (alist-keys regs)))
  ;;  :hints(("Goal" :in-theory (e/d* (aignet-frame-thms)
  ;;                                  (len (len))))))





;; (defsection good-varmap-p-of-aig-fsm-prepare-aignet/varmap
;;   (local (in-theory (enable good-varmap-p)))
;;   (local (include-book "arithmetic/top-with-meta" :dir :system))


;;   (defthm non-bool-atom-listp-of-accumulate-aig-vars
;;     (equal (acl2::aig-var-listp
;;             (mv-nth 1 (acl2::accumulate-aig-vars x nodetable acc)))
;;            (acl2::aig-var-listp acc)))

;;   (defthm non-bool-atom-listp-of-aig-vars-unordered
;;     (acl2::aig-var-listp (acl2::aig-vars-unordered x))
;;     :hints(("Goal" :in-theory (enable aig-vars-unordered))))


;;   (defthm non-bool-atom-listp-of-set-difference
;;     (implies (acl2::aig-var-listp x)
;;              (acl2::aig-var-listp (set-difference$ x y)))
;;     :hints(("Goal" :in-theory (enable set-difference$))))

;;   ;; (defthm good-varmap-p-of-make-varmap
;;   ;;   (implies (and (acl2::aig-var-listp vars)
;;   ;;                 (<= (+ (nfix start) (len vars))
;;   ;;                     (nfix (nth *num-regs* aignet))))
;;   ;;            (equal (good-varmap-p (make-varmap start vars (reg-type) acc) aignet)
;;   ;;                   (good-varmap-p acc aignet)))
;;   ;;   :hints(("Goal" :in-theory (enable make-varmap
;;   ;;                                     aignet-id-in-bounds
;;   ;;                                     id-in-bounds)
;;   ;;           :induct (make-varmap start vars (reg-type) acc))))


;;   ;; (defthm good-varmap-p-of-add-to-varmap
;;   ;;   (implies (and (acl2::aig-var-listp vars)
;;   ;;                 (no-duplicatesp vars)
;;   ;;                 (<= (+ (nfix start) (len (set-difference$ vars (alist-keys acc))))
;;   ;;                     (nfix (nth *num-inputs* aignet))))
;;   ;;            (equal (good-varmap-p (add-to-varmap start vars (input-type) acc) aignet)
;;   ;;                   (good-varmap-p acc aignet)))
;;   ;;   :hints(("Goal" :in-theory (enable add-to-varmap
;;   ;;                                     set-difference$
;;   ;;                                     aignet-id-in-bounds
;;   ;;                                     id-in-bounds)
;;   ;;           :induct (add-to-varmap start vars (input-type) acc))))


;;   ;; (defthm good-varmap-p-of-make-fal
;;   ;;   (implies (and (good-varmap-p a aignet)
;;   ;;                 (good-varmap-p b aignet))
;;   ;;            (good-varmap-p (acl2::make-fal a b) aignet)))

;;   ;; (defthm good-varmap-p-of-increase
;;   ;;   (implies (and (good-varmap-p varmap aignet)
;;   ;;                 (<= (nfix (nth *num-inputs* aignet))
;;   ;;                     (nfix (nth *num-inputs* aignet2)))
;;   ;;                 (<= (nfix (nth *num-regs* aignet))
;;   ;;                     (nfix (nth *num-regs* aignet2))))
;;   ;;            (good-varmap-p varmap aignet2))
;;   ;;   :hints(("Goal" :in-theory (enable good-varmap-p
;;   ;;                                     aignet-id-in-bounds
;;   ;;                                     id-in-bounds))))

;;   ;; (local (defun tmpind (n invars)
;;   ;;          (if (atom invars)
;;   ;;              n
;;   ;;            (tmpind (+ 1 (nfix n)) (cdr invars)))))

;;   ;; (local (defthmd good-varmap-p-of-pairlis-inputs1
;;   ;;          (implies (and (acl2::aig-var-listp invars)
;;   ;;                        (<= (+ (nfix n) (len invars))
;;   ;;                            (nfix (nth *num-inputs* aignet))))
;;   ;;                   (good-varmap-p (pairlis$ invars
;;   ;;                                            (lits-of-type n (+ (nfix n) (len invars)) (input-type)))
;;   ;;                                  aignet))
;;   ;;          :hints (("goal" :induct (tmpind n invars)
;;   ;;                   :in-theory (enable pairlis$ id-in-bounds aignet-id-in-bounds)
;;   ;;                   :expand ((:free (max type) (lits-of-type n max type)))))))

;;   ;; (defthm good-varmap-p-of-pairlis-inputs
;;   ;;   (implies (and (acl2::aig-var-listp invars)
;;   ;;                 (<= (len invars) (nfix (nth *num-inputs* aignet))))
;;   ;;            (good-varmap-p
;;   ;;             (pairlis$ invars (lits-of-type 0 (len invars) (input-type)))
;;   ;;             aignet))
;;   ;;   :hints (("goal" :use ((:instance good-varmap-p-of-pairlis-inputs1
;;   ;;                          (n 0))))))

;;   ;; (local (defthmd good-varmap-p-of-pairlis-regs1
;;   ;;          (implies (and (acl2::aig-var-listp invars)
;;   ;;                        (<= (+ (nfix n) (len invars))
;;   ;;                            (nfix (nth *num-regs* aignet))))
;;   ;;                   (good-varmap-p (pairlis$ invars
;;   ;;                                            (lits-of-type n (+ (nfix n) (len invars)) (reg-type)))
;;   ;;                                  aignet))
;;   ;;          :hints (("goal" :induct (tmpind n invars)
;;   ;;                   :in-theory (enable pairlis$ id-in-bounds aignet-id-in-bounds)
;;   ;;                   :expand ((:free (max type) (lits-of-type n max type)))))))

;;   ;; (defthm good-varmap-p-of-pairlis-regs
;;   ;;   (implies (and (acl2::aig-var-listp invars)
;;   ;;                 (<= (len invars) (nfix (nth *num-regs* aignet))))
;;   ;;            (good-varmap-p
;;   ;;             (pairlis$ invars (lits-of-type 0 (len invars) (reg-type)))
;;   ;;             aignet))
;;   ;;   :hints (("goal" :use ((:instance good-varmap-p-of-pairlis-regs1
;;   ;;                          (n 0))))))

;;   (local (in-theory (disable aignet-init)))

;;   (defthm good-varmap-p-of-aig-fsm-prepare-aignet/varmap
;;     (implies (acl2::aig-var-listp (alist-keys reg-alist))
;;              (b* (((mv varmap & & aignet)
;;                    (aig-fsm-prepare-aignet/varmap
;;                     reg-alist out-lits max-gates aignet)))
;;                (good-varmap-p varmap aignet)))
;;     :hints(("Goal" :in-theory (e/d* (aig-fsm-prepare-aignet/varmap)
;;                                     (aig-vars aignet-init))))))



(local (defthm lit-listp-of-take
         (implies (and (lit-listp x)
                       (<= (nfix n) (len x)))
                  (lit-listp (take n x)))
         :hints(("Goal" :in-theory (enable take
                                           acl2::replicate)))))

(local (defthm lit-listp-of-nthcdr
         (implies (lit-listp x)
                  (lit-listp (nthcdr n x)))
         :hints(("Goal" :in-theory (enable nthcdr)))))

(local (defthm len-alist-vals
         (equal (len (alist-vals x))
                (len (alist-keys x)))
         :hints(("Goal" :in-theory (enable alist-keys alist-vals)))))


(local (defthm aignet-lit-listp-of-take
         (implies (and (aignet-lit-listp x aignet)
                       (<= (nfix n) (len x)))
                  (aignet-lit-listp (take n x) aignet))
         :hints(("Goal" :in-theory (enable aignet-lit-listp
                                           take
                                           acl2::replicate)))))

(local (defthm aignet-lit-listp-of-nthcdr
         (implies (aignet-lit-listp x aignet)
                  (aignet-lit-listp (nthcdr n x) aignet))
         :hints(("Goal" :in-theory (enable aignet-lit-listp nthcdr)))))

;; (defthm set-outs-logic-preserves-aignet-lit-listp
;;   (equal (aignet-lit-listp lits (set-outs-logic nouts aignet))
;;          (aignet-lit-listp lits aignet)))

;; (defthm set-regs-logic-preserves-aignet-lit-listp
;;   (implies (and (aignet-lit-listp lits aignet)
;;                 (<= (nfix (nth *num-regs* aignet)) (nfix n)))
;;            (aignet-lit-listp lits (set-regs-logic n aignet))))

(defthm lit-eval-list-of-take
  (implies (<= (nfix n) (len x))
           (equal (lit-eval-list (take n x) in-vals reg-vals aignet)
                  (take n (lit-eval-list x in-vals reg-vals aignet))))
  :hints(("Goal" :in-theory (enable take acl2::replicate
                                    acl2::nfix))))

(defthm aig-eval-list-of-append
  (equal (acl2::aig-eval-list (append a b) env)
         (append (acl2::aig-eval-list a env)
                 (acl2::aig-eval-list b env))))

(local (defthm nthcdr-nil
         (equal (nthcdr n nil) nil)))

(defthm lit-eval-list-of-nthcdr
  (equal (lit-eval-list (nthcdr n x) in-vals reg-vals aignet)
         (nthcdr n (lit-eval-list x in-vals reg-vals aignet)))
  :hints(("Goal" :in-theory (enable nthcdr))))

(defthm nthcdr-of-append
  (implies (equal (nfix n) (len a))
           (equal (nthcdr n (append a b))
                  b))
  :hints(("Goal" :in-theory (enable nthcdr)
          :induct (nthcdr n a))))

;; (defthm lit-eval-list-of-nfix-list
;;   (equal (lit-eval-list (nfix-list lits) in-vals reg-vals aignet)
;;          (lit-eval-list lits in-vals reg-vals aignet)))


(encapsulate nil
  (local
   (progn
     ;; no longer necessary with std/lists/update-nth
     ;; (defthm nthcdr-of-update-nth
     ;;   (equal (nthcdr n (update-nth n v x))
     ;;          (cons v
     ;;                (nthcdr (1+ (nfix n)) x)))
     ;;   :hints(("Goal" :in-theory (e/d (update-nth)))))
     (defthm nthcdr-empty
       (implies (and (true-listp lst)
                     (<= (len lst) (nfix n)))
                (equal (nthcdr n lst) nil))))))

;; (local
;;  (progn
;;    (defthm lit-eval-list-of-set-outs
;;      (equal (lit-eval-list lits1 in-vals reg-vals (set-outs-logic lits aignet))
;;             (lit-eval-list lits1 in-vals reg-vals aignet))
;;      :hints(("Goal" :in-theory (e/d (lit-eval-list)
;;                                     (set-outs-logic)))))

;;    (defthm lit-eval-list-of-set-regs
;;      (equal (lit-eval-list lits1 in-vals reg-vals (set-regs-logic lits aignet))
;;             (lit-eval-list lits1 in-vals reg-vals aignet))
;;      :hints(("Goal" :in-theory (e/d (lit-eval-list)
;;                                     (set-regs-logic)))))

;;    (defthm len-of-aig-eval-list
;;      (equal (len (acl2::aig-eval-list x env))
;;             (len x)))

;;    (defthm take-redundant
;;      (implies (and (equal (nfix n) (len x))
;;                    (true-listp x))
;;               (equal (take n x) x))
;;      :hints(("Goal" :in-theory (enable take))))

;;    (defthm take-0
;;      (equal (take 0 x) nil)
;;      :hints(("Goal" :in-theory (enable take))))

;;    (defthm set-regs-logic-preserves-good-varmap-p
;;      (equal (good-varmap-p varmap (set-regs-logic lits aignet))
;;             (good-varmap-p varmap aignet))
;;      :hints(("Goal" :in-theory (enable good-varmap-p
;;                                        id-in-bounds
;;                                        aignet-id-in-bounds))))
;;    (defthm set-outs-logic-preserves-good-varmap-p
;;      (equal (good-varmap-p varmap (set-outs-logic lits aignet))
;;             (good-varmap-p varmap aignet))
;;      :hints(("Goal" :in-theory (enable good-varmap-p
;;                                        id-in-bounds
;;                                        aignet-id-in-bounds))))))


(defsection aig-fsm-to-aignet

  (local (in-theory (enable alist-keys aignet-lit-listp)))

  (local (in-theory (enable good-varmap-p)))

  (local (defthm litp-integerp
           (implies (litp lit)
                    (and (integerp lit)
                         (<= 0 lit)))))

  (defthm car-nonnil-forward
    (implies (not (equal (car x) nil))
             (consp x))
    :rule-classes ((:forward-chaining :trigger-terms ((car x)))))

  (defthm stype-count-of-cdr-extension
    (implies (and (aignet-extension-bind-inverse)
                  (consp orig)
                  (equal (stype (car orig))
                         (stype-fix stype)))
             (< (stype-count stype (cdr orig))
                (stype-count stype new)))
    :rule-classes ((:linear :trigger-terms ((stype-count stype (cdr orig))))))


  (define aig-fsm-set-nxsts (regnum reg-lits aignet)
    (declare (xargs :stobjs aignet
                    :guard (and (lit-listp reg-lits)
                                (aignet-lit-listp reg-lits aignet)
                                (natp regnum)
                                (<= (+ (nfix regnum) (len reg-lits))
                                    (num-regs aignet)))))
    :returns (new-aignet)
    (b* (((when (atom reg-lits)) aignet)
         (reg-id (regnum->id regnum aignet))
         (aignet (aignet-set-nxst (car reg-lits) reg-id aignet)))
      (aig-fsm-set-nxsts (1+ (lnfix regnum)) (cdr reg-lits) aignet))
    ///
    (def-aignet-preservation-thms aig-fsm-set-nxsts)

    
    (std::defret other-stype-count-of-aig-fsm-set-nxsts
      (implies (not (equal (stype-fix stype) :nxst))
               (equal (stype-count stype new-aignet)
                      (stype-count stype aignet))))

    ;; (local (defun-nx aig-fsm-set-nxsts-nth-ind (n regnum reg-lits aignet)
    ;;          (b* (((when (atom reg-lits)) (list n aignet))
    ;;               (reg-id (regnum->id regnum aignet))
    ;;               (aignet (aignet-set-nxst (car reg-lits) reg-id aignet)))
    ;;            (aig-fsm-set-nxsts-nth-ind (1- (nfix n)) (1+ (lnfix regnum)) (cdr reg-lits) aignet))))
    
    (std::defret lookup-nxst-fanin-of-aig-fsm-set-nxsts
      (implies (And (aignet-lit-listp reg-lits aignet)
                    (< (nfix n) (+ (stype-count :nxst aignet) (len reg-lits))))
               (equal (fanin-if-co (lookup-stype n :nxst new-aignet))
                      (if (< (nfix n) (stype-count :nxst aignet))
                          (fanin-if-co (lookup-stype n :nxst  aignet))
                        (lit-fix (nth (- (nfix n) (stype-count :nxst aignet)) reg-lits)))))
      :hints(("Goal" :in-theory (e/d (nth lookup-stype))
              :induct t :do-not-induct t)))

    (std::defret lookup-non-nxst-of-aig-fsm-set-nxsts
      (implies (not (equal (stype-fix stype) :nxst))
               (equal (lookup-stype n stype new-aignet)
                      (lookup-stype n stype aignet))))

    (std::defret lookup-of-aig-fsm-set-nxsts-is-extension
      (implies (and (<= (stype-count :nxst aignet) (nfix n))
                    (< (nfix n) (+ (stype-count :nxst aignet) (len reg-lits)))
                    (aignet-extension-p aignet orig))
               (and (aignet-extension-p (cdr (lookup-stype n :nxst new-aignet)) orig)
                    (aignet-extension-p (lookup-stype n :nxst new-aignet) orig)))
      :hints(("Goal" :in-theory (enable lookup-stype))))

    (std::defret nxst-count-of-aig-fsm-set-nxsts
      (equal (stype-count :nxst new-aignet)
             (+ (len reg-lits)
                (stype-count :nxst aignet))))

    (std::defret lookup-regnum->nxst-of-aig-fsm-set-nxsts
      ;; (b* ((n (stype-count :reg (cdr (lookup-id reg-id aignet)))))
        (implies (and (< (nfix n) (+ (nfix regnum) (len reg-lits)))
                      (<= (+ (nfix regnum) (len reg-lits)) (num-regs aignet)))
                 (equal (lookup-regnum->nxst n new-aignet)
                        (if (<= (nfix regnum) (nfix n))
                            (lookup-stype (+ (stype-count :nxst aignet)
                                             (- (nfix n) (nfix regnum)))
                                          :nxst new-aignet)
                          (lookup-regnum->nxst n aignet))))
      :hints(("Goal" :in-theory (enable* lookup-regnum->nxst
                                         lookup-stype
                                         acl2::arith-equiv-forwarding)
              :induct t
              :do-not-induct t))))
  


  ;; (define aig-fsm-set-nxsts (reg-alist reg-lits varmap aignet)
  ;;   (declare (xargs :stobjs aignet
  ;;                   :guard (and (lit-listp reg-lits)
  ;;                               (aignet-lit-listp reg-lits aignet)
  ;;                               (equal (len reg-lits) (len (alist-keys
  ;;                                                           reg-alist)))
  ;;                               (good-varmap-p varmap aignet)
  ;;                               (bound-to-regs-in-varmap
  ;;                                (alist-keys reg-alist) varmap aignet))
  ;;                   :guard-hints (("goal" :expand ((aignet-lit-listp reg-lits
  ;;                                                                    aignet)
  ;;                                                  (lit-listp reg-lits)
  ;;                                                  (alist-keys reg-alist))))))
  ;;   :returns (mv new-varmap new-aignet)
  ;;   (b* (((when (atom reg-alist)) (mv varmap aignet))
  ;;        ((when (atom (car reg-alist)))
  ;;         (aig-fsm-set-nxsts (cdr reg-alist) reg-lits varmap aignet))
  ;;        ((when (or (consp (caar reg-alist))
  ;;                   (booleanp (caar reg-alist))))
  ;;         (aig-fsm-set-nxsts (cdr reg-alist) (cdr reg-lits) varmap aignet))
  ;;        (regname (caar reg-alist))
  ;;        (fanin (car reg-lits))
  ;;        (rolook (hons-get regname varmap))
  ;;        ((mv ro-lit varmap aignet)
  ;;         (if rolook
  ;;             (mv (cdr rolook) varmap aignet)
  ;;           (b* ((ro-lit (mk-lit (num-nodes aignet) 0))
  ;;                (aignet (aignet-add-reg aignet))
  ;;                (varmap (hons-acons regname ro-lit varmap)))
  ;;             (mv ro-lit varmap aignet))))
  ;;        (ro-id (lit-id ro-lit))
  ;;        (regp (int= 1 (io-id->regp ro-id aignet)))
  ;;        (- (and (not regp) (cw "~x0 mapping not a register output~%"
  ;;                               regname)))
  ;;        (ro-unconnected (and regp (int= ro-id
  ;;                                        (regnum->id (io-id->ionum ro-id aignet) aignet))))
  ;;        (aignet (if ro-unconnected
  ;;                    (aignet-set-nxst fanin ro-id aignet)
  ;;                  (prog2$ (cw "Failed to add register input for ~x0~%" regname)
  ;;                          aignet))))
  ;;     (aig-fsm-set-nxsts (cdr reg-alist) (cdr reg-lits) varmap aignet))
  ;;   ///

  ;;   (def-aignet-preservation-thms aig-fsm-set-nxsts)


  ;;   (defthm good-varmap-p-of-aig-fsm-set-nxsts
  ;;     (implies (and (aignet-lit-listp reg-lits aignet)
  ;;                   (equal (len reg-lits) (len (alist-keys reg-alist)))
  ;;                   (good-varmap-p varmap aignet)
  ;;                   (bound-to-regs-in-varmap (alist-keys reg-alist) varmap aignet))
  ;;              (mv-let (varmap aignet)
  ;;                (aig-fsm-set-nxsts reg-alist reg-lits varmap aignet)
  ;;                (good-varmap-p varmap aignet)))
  ;;     :hints(("Goal" :in-theory (enable aig-fsm-set-nxsts good-varmap-p)
  ;;             :induct (aig-fsm-set-nxsts reg-alist reg-lits varmap aignet))))

  ;;   (std::defret num-outs-of-aig-fsm-set-nxsts
  ;;     (equal (stype-count :po new-aignet)
  ;;            (stype-count :po aignet)))

  ;;   (std::defret num-ins-of-aig-fsm-set-nxsts
  ;;     (equal (stype-count :pi new-aignet)
  ;;            (stype-count :pi aignet)))

  ;;   (local (defthm aignet-lit-fix-of-nil
  ;;            (equal (aignet-lit-fix nil aignet)
  ;;                   0)
  ;;            :hints(("Goal" :in-theory (enable aignet-lit-fix)))))

  ;;   (std::defret lookup-nxst-of-aig-fsm-set-nxsts
  ;;     (implies (and (aignet-lit-listp reg-lits aignet)
  ;;                   (acl2::aig-var-listp (alist-keys reg-alist))
  ;;                   (good-varmap-p varmap aignet)
  ;;                   (bound-to-regs-in-varmap
  ;;                    (alist-keys reg-alist) varmap aignet)
  ;;                   (alistp reg-alist)
  ;;                   (< (nfix n) (+ (stype-count :nxst aignet) (len (alist-keys reg-alist)))))
  ;;              (equal (car (lookup-stype n :nxst new-aignet))
  ;;                     (if (< (nfix n) (stype-count :nxst aignet))
  ;;                         (car (lookup-stype n :nxst  aignet))
  ;;                       (nxst-node
  ;;                        (lit-fix (nth (- (nfix n) (stype-count :nxst aignet)) reg-lits))
  ;;                        (lit-id (cdr (hons-assoc-equal (car (nth (- (nfix n) (stype-count :nxst aignet)) reg-alist))
  ;;                                                       varmap)))))))
  ;;     :hints(("Goal" :in-theory (enable nth lookup-stype alist-keys alistp
  ;;                                       bound-to-regs-in-varmap))))

  ;;   (std::defret lookup-non-output-of-aig-fsm-set-nxsts
  ;;     (implies (and (not (equal (stype-fix stype) :nxst))
  ;;                   (good-varmap-p varmap aignet)
  ;;                   (bound-to-regs-in-varmap
  ;;                    (alist-keys reg-alist) varmap aignet))
  ;;              (equal (lookup-stype n stype new-aignet)
  ;;                     (lookup-stype n stype aignet)))
  ;;     :hints(("Goal" :in-theory (enable lookup-stype))))

  ;;   (std::defret varmap-preserved-of-aig-fsm-set-nxsts
  ;;     (implies (and (good-varmap-p varmap aignet)
  ;;                   (bound-to-regs-in-varmap
  ;;                    (alist-keys reg-alist) varmap aignet))
  ;;              (equal new-varmap varmap)))

  

  ;;   (std::defret lookup-of-aig-fsm-set-nxsts-is-extension
  ;;     (implies (and (alistp reg-alist)
  ;;                   (acl2::aig-var-listp (alist-keys reg-alist))
  ;;                   (good-varmap-p varmap aignet)
  ;;                   (bound-to-regs-in-varmap
  ;;                    (alist-keys reg-alist) varmap aignet)
  ;;                   (<= (stype-count :nxst aignet) (nfix n))
  ;;                   (< (nfix n) (+ (stype-count :nxst aignet) (len (alist-keys reg-alist))))
  ;;                   (aignet-extension-p aignet orig))
  ;;              (and (aignet-extension-p (cdr (lookup-stype n :nxst new-aignet)) orig)
  ;;                   (aignet-extension-p (lookup-stype n :nxst new-aignet) orig)))
  ;;     :hints(("Goal" :in-theory (enable lookup-stype))))

  ;;   (std::defret nxst-count-of-aig-fsm-set-nxsts
  ;;     (implies (and (acl2::aig-var-listp (alist-keys reg-alist))
  ;;                   (good-varmap-p varmap aignet)
  ;;                   (bound-to-regs-in-varmap
  ;;                    (alist-keys reg-alist) varmap aignet))
  ;;              (equal (stype-count :nxst new-aignet)
  ;;                     (+ (len (alist-keys reg-alist))
  ;;                        (stype-count :nxst aignet)))))

  ;;   (defret lookup-reg->nxst-of-aig-fsm-set-nxsts
  ;;     (implies (and (acl2::aig-var-listp (alist-keys reg-alist))
  ;;                   (good-varmap-p varmap aignet)
  ;;                   (bound-to-regs-in-varmap
  ;;                    (alist-keys reg-alist) varmap aignet)
  ;;                   (hons-assoc-equal reg reg-alist)
  ;;                   (equal (stype (lookup-id (lit-id (cdr (hons-assoc-equal reg varmap))) aignet)) :reg))
  ;;              (equal (node-count (lookup-reg->nxst (lit-id (cdr (hons-assoc-equal reg varmap))) new-aignet))


  (define aig-fsm-add-outs (out-lits aignet)
    (declare (xargs :stobjs aignet
                    :guard (and (lit-listp out-lits)
                                (aignet-lit-listp out-lits aignet))))
    :returns (new-aignet)
    (if (atom out-lits)
        aignet
      (b* ((aignet (aignet-add-out (car out-lits) aignet)))
        (aig-fsm-add-outs (cdr out-lits) aignet)))
    ///

    (def-aignet-preservation-thms aig-fsm-add-outs)

    (defthm good-varmap-p-of-aig-fsm-add-outs
      (implies (good-varmap-p varmap aignet)
               (good-varmap-p varmap (aig-fsm-add-outs out-lits aignet)))
      :hints (("goal" :induct (aig-fsm-add-outs out-lits aignet))))

    (local (defthm lit-listp-true-listp
             (implies (lit-listp x)
                      (true-listp x))))

    (std::defret num-outs-of-aig-fsm-add-outs
      (equal (stype-count :po new-aignet)
             (+ (len out-lits) (stype-count :po aignet)))
      :hints (("goal" :induct t :do-not-induct t)))

    (std::defret other-stype-count-of-aig-fsm-add-outs
      (implies (not (equal (stype-fix stype) :po))
               (equal (stype-count stype new-aignet)
                      (stype-count stype aignet))))

    (std::defret lookup-output-fanin-of-aig-fsm-add-outs
      (implies (aignet-lit-listp out-lits aignet)
               (equal (fanin :co (lookup-stype n :po new-aignet))
                      ;;
                      (cond ((< (nfix n) (stype-count :po aignet))
                             (fanin :co (lookup-stype n :po aignet)))
                            ((< (nfix n) (+ (stype-count :po aignet) (len out-lits)))
                             (lit-fix (nth (- (nfix n) (stype-count :po aignet)) out-lits)))
                            (t 0))
                      ;; (cond ((< (nfix n) (stype-count :po aignet))
                      ;;        (car (lookup-stype n :po  aignet)))
                      ;;       ((< (nfix n) (+ (stype-count :po aignet) (len out-lits)))
                      ;;        (po-node (lit-fix (nth (- (nfix n) (stype-count :po aignet)) out-lits))))
                      ;;       (t nil))
                      ))
      :hints(("Goal" :in-theory (enable nth lookup-stype)
              :induct t :do-not-induct t)))

    (std::defret lookup-of-aig-fsm-add-outs-is-extension
      (implies (and (<= (stype-count :po aignet) (nfix n))
                    (< (nfix n) (+ (stype-count :po aignet) (len out-lits)))
                    (aignet-extension-p aignet orig))
               (and (aignet-extension-p (cdr (lookup-stype n :po new-aignet)) orig)
                    (aignet-extension-p (lookup-stype n :po new-aignet) orig)))
      :hints(("Goal" :in-theory (enable lookup-stype))))

    (std::defret lookup-non-output-of-aig-fsm-add-outs
      (implies (not (equal (stype-fix stype) :po))
               (equal (lookup-stype n stype new-aignet)
                      (lookup-stype n stype aignet)))
      :hints(("Goal" :in-theory (enable lookup-stype)))))
  


  ;; (defthm add-to-varmap-preserves-lookup
  ;;   (implies (hons-assoc-equal x varmap)
  ;;            (let ((varmap1 (mv-nth 0 (add-to-varmap vars f varmap aignet))))
  ;;              (equal (cdr (hons-assoc-equal x varmap1))
  ;;                     (cdr (hons-assoc-equal x varmap)))))
  ;;   :hints(("Goal" :in-theory (enable add-to-varmap))))

  ;; (defthm aignet-add-in-preserves-bound-to-regs
  ;;   (implies (and (bound-to-regs-in-varmap names varmap aignet)
  ;;                 (good-varmap-p varmap aignet))
  ;;            (bound-to-regs-in-varmap names varmap (mv-nth 1 (aignet-add-in aignet)))))

  ;; (defthm bound-to-regs-in-varmap-preserved-by-varmap-add-other
  ;;   (implies (and (bound-to-regs-in-varmap vars1 acc aignet)
  ;;                 (not (hons-assoc-equal v acc)))
  ;;            (bound-to-regs-in-varmap
  ;;             vars1
  ;;             (cons (cons v lit) acc)
  ;;             aignet)))

  ;; (defthm add-to-varmap-preserves-bound-to-regs
  ;;   (implies (and (bound-to-regs-in-varmap names varmap aignet)
  ;;                 (good-varmap-p varmap aignet)
  ;;                 (acl2::aig-var-listp vars))
  ;;            (mv-let (varmap aignet)
  ;;              (add-to-varmap vars f varmap aignet)
  ;;              (bound-to-regs-in-varmap names varmap aignet)))
  ;;   :hints(("Goal" :in-theory (enable add-to-varmap good-varmap-p))))

  ;; (defthm bound-to-regs-in-varmap-of-prepare-aignet/varmap
  ;;   (implies (acl2::aig-var-listp (alist-keys reg-alist))
  ;;            (bound-to-regs-in-varmap
  ;;             (alist-keys reg-alist)
  ;;             (mv-nth 0 (aig-fsm-prepare-aignet/varmap reg-alist out-list max-nodes aignet))
  ;;             (mv-nth 3 (aig-fsm-prepare-aignet/varmap reg-alist out-list max-nodes aignet))))
  ;;   :hints(("Goal" :in-theory (enable aig-fsm-prepare-aignet/varmap)
  ;;           :do-not-induct t)))

  ;; (defthm bound-to-regs-in-varmap-of-aiglist-to-aignet
  ;;   (implies (and (bound-to-regs-in-varmap names varmap aignet)
  ;;                 (good-varmap-p varmap aignet))
  ;;            (bound-to-regs-in-varmap
  ;;             names varmap
  ;;             (mv-nth 3 (aiglist-to-aignet aigs xmemo varmap gatesimp strash aignet)))))

  ;; (defthm non-bool-atom-listp-keys-of-hons-shrink-alist
  ;;   (implies (and (acl2::aig-var-listp (alist-keys acc))
  ;;                 (acl2::aig-var-listp (alist-keys a)))
  ;;            (acl2::aig-var-listp
  ;;             (alist-keys (hons-shrink-alist a acc)))))

  (define aig-fsm-to-aignet (reg-alist out-list max-nodes gatesimp aignet)
    (declare (xargs :stobjs aignet
                    :guard (and (posp max-nodes)
                                (gatesimp-p gatesimp)
                                (acl2::aig-var-listp (alist-keys reg-alist)))
                    :verify-guards nil
                    ;;:guard-hints (("goal" :do-not-induct t
                    ;;               :in-theory (e/d (nth-of-aiglist-to-aignet)
                    ;;                               (aig-vars))))
                    ))
    :returns (mv (new-aignet)
                 (varmap)
                 (invars)
                 (regvars))
    (b* (((acl2::local-stobjs strash)
          (mv aignet varmap invars regvars strash))
         (reg-aigs (alist-vals reg-alist))
         ((mv varmap invars regvars aignet)
          (aig-fsm-prepare-aignet/varmap reg-alist out-list max-nodes aignet))
         (strash    (if (gatesimp->hashp gatesimp)
                        (strashtab-init max-nodes nil nil strash)
                      strash))
         ((mv lits strash aignet)
          (cwtime
           (aiglist-to-aignet-top (append reg-aigs out-list)
                                  varmap gatesimp strash aignet)))
         (nregs (length reg-aigs))
         (out-lits (nthcdr nregs lits))
         (reg-lits (take nregs lits))
         ;;((mv out-lits xmemo strash aignet)
         ;; ;; This adds all the gates we need to drive all the outputs, but
         ;; ;; doesn't initialize the regs or outs arrays
         ;; (aiglist-to-aignet out-list nil varmap gatesimp strash aignet))
         ;;((mv reg-lits ?xmemo strash aignet)
         ;; ;; This adds all the gates we need to drive all the register
         ;; ;; updates, but doesn't initialize the regs or outs arrays
         ;; (aiglist-to-aignet reg-aigs xmemo varmap gatesimp strash aignet))
         (aignet (aig-fsm-set-nxsts 0 reg-lits aignet))
         (aignet (aig-fsm-add-outs out-lits aignet)))
      ;; (fast-alist-free xmemo)
      (mv aignet varmap invars regvars strash))
    ///

    (local (in-theory (enable aig-fsm-to-aignet)))

    (local (defthm true-listp-when-lit-listp-rw
             (implies (lit-listp x)
                      (true-listp x))))

    (verify-guards aig-fsm-to-aignet
      ;; :hints ((and stable-under-simplificationp
      ;;              '(:in-theory (enable* aignet-frame-thms))))
      :guard-debug t)

    ;; (defthm aignet-nodes-ok-of-aig-fsm-to-aignet
    ;;   (implies (acl2::aig-var-listp (alist-keys regs))
    ;;            (aignet-nodes-ok
    ;;             (mv-nth 0 (aig-fsm-to-aignet regs outs max-gates gatesimp
    ;;                                          aignet)))))

    (defthm true-listp-aig-fsm-to-aignet-invars
      (true-listp (mv-nth 2 (aig-fsm-to-aignet regs outs max-gates gatesimp aignet)))
      :rule-classes (:Rewrite :type-prescription))

    (defthm true-listp-aig-fsm-to-aignet-regvars
      (true-listp (mv-nth 3 (aig-fsm-to-aignet regs outs max-gates gatesimp aignet)))
      :rule-classes (:Rewrite :type-prescription))

    ;; (local (include-book "arithmetic/top-with-meta" :dir :system))


    (local (defthm aignet-litp-of-co-node->fanin-of-po
             (implies (and (aignet-nodes-ok aignet)
                           (< (nfix n) (stype-count (po-stype) aignet))
                           (aignet-extension-p aignet2 (cdr (lookup-stype n (po-stype) aignet))))
                      (aignet-litp (co-node->fanin
                                    (car (lookup-stype n (po-stype) aignet)))
                                   aignet2))
             :hints (("goal":use ((:instance co-fanin-aignet-litp-when-aignet-nodes-ok
                                   (id (node-count (lookup-stype n (po-stype) aignet)))))))))
    

    (defthm aig-fsm-to-aignet-output-correct
      (b* (((mv aignet varmap ?invars ?regvars)
            (aig-fsm-to-aignet reg-alist out-list max-gates gatesimp aignet))
           (env (aignet-eval-to-env varmap in-vals reg-vals aignet)))
        (implies (and (acl2::aig-var-listp (alist-keys reg-alist))
                      (< (nfix n) (len out-list)))
                 (equal (lit-eval (fanin :co (lookup-stype n (po-stype) aignet))
                                  in-vals reg-vals aignet)
                        (acl2::bool->bit (aig-eval (nth n out-list) env)))))
      :hints (("goal" :do-not-induct t
               :expand ((:free (aignet1 aignet2)
                         (id-eval (node-count (lookup-stype n (po-stype) aignet1))
                                  in-vals reg-vals aignet2))))))

    ;; (defthm aig-fsm-to-aignet-nxst-correct
    ;;   (b* (((mv aignet varmap ?invars ?regvars)
    ;;         (aig-fsm-to-aignet reg-alist out-list max-gates gatesimp aignet))
    ;;        (env (aignet-eval-to-env varmap in-vals reg-vals aignet)))
    ;;     (implies (and (acl2::aig-var-listp (alist-keys reg-alist))
    ;;                   (< (nfix n) (len (alist-keys reg-alist))))
    ;;              (equal (lit-eval (node-count (lookup-stype n (nxst-stype) aignet))
    ;;                              in-vals reg-vals aignet)
    ;;                     (acl2::bool->bit (aig-eval (nth n (alist-vals reg-alist)) env)))))
    ;;   :hints (("goal" :do-not-induct t
    ;;            :expand ((:free (aignet1 aignet2)
    ;;                      (id-eval (node-count (lookup-stype n (nxst-stype) aignet1))
    ;;                               in-vals reg-vals aignet2))))))

    ;; (defthm aig-fsm-to-aignet-reg-update-correct
    ;;   (b* (((mv aignet ?varmap ?invars ?regvars)
    ;;         (aig-fsm-to-aignet reg-alist out-list max-gates gatesimp aignet)))
    ;;     (implies (and (acl2::aig-var-listp (alist-keys reg-alist))
    ;;                   (< (nfix n) (len (alist-keys reg-alist))))
    ;;              (equal (node-count (lookup-reg->nxst (node-count (lookup-stype n (reg-stype) aignet)) aignet))
    ;;                     (node-count (lookup-stype n (nxst-stype) aignet)))))
    ;;   :hints (("goal" :do-not-induct t)))

    (defthm aig-fsm-to-aignet-nxst-correct
      (b* (((mv aignet varmap ?invars ?regvars)
            (aig-fsm-to-aignet reg-alist out-list max-gates gatesimp aignet))
           (env (aignet-eval-to-env varmap in-vals reg-vals aignet)))
        (implies (and (acl2::aig-var-listp (alist-keys reg-alist))
                      (< (nfix n) (len (alist-keys reg-alist))))
                 (equal (lit-eval (fanin-if-co (lookup-regnum->nxst n aignet))
                                  in-vals reg-vals aignet)
                        (acl2::bool->bit (aig-eval (nth n (alist-vals reg-alist)) env)))))
    :hints (("goal" :do-not-induct t)))
      ;; :hints (("goal" :do-not-induct t
      ;;          :in-theory (disable aig-fsm-to-aignet)
      ;;          ;; :expand ((:free (aignet1 aignet2)
      ;;          ;;           (id-eval (node-count (lookup-stype n (nxst-stype) aignet1))
      ;;          ;;                   in-vals reg-vals aignet2)))
      ;;          )))


    (local (defthm alist-keys-of-aignet-eval-to-env
             (Equal (alist-keys (aignet-eval-to-env varmap in-vals reg-vals aignet))
                    (alist-keys varmap))
             :hints(("Goal" :in-theory (enable aignet-eval-to-env)))))

    (local (defthm alist-keys-of-consecutive-vars-to-varmap
             (equal (alist-keys (consecutive-vars-to-varmap n vars varmap))
                    (append (acl2::rev (acl2::list-fix vars)) (alist-keys varmap)))
             :hints(("Goal" :in-theory (enable consecutive-vars-to-varmap alist-keys)))))


    (local (defthm acl2-numberp-of-index-of-when-member
             (implies (double-rewrite (member x lst))
                      (acl2-numberp (acl2::index-of x lst)))))

    (local (defthm no-duplicatesp-of-set-diff
             (implies (no-duplicatesp a)
                      (no-duplicatesp (set-difference$ a b)))
             :hints(("Goal" :in-theory (enable set-difference$)))))


    (defthm aignet-eval-to-env-of-varmap-lookup
      (b* (((mv ?aignet varmap invars regvars)
            (aig-fsm-to-aignet reg-alist out-list max-gates gatesimp aignet))
           (env (aignet-eval-to-env varmap in-vals reg-vals aignet)))
        (implies (and (no-duplicatesp (alist-keys reg-alist))
                      (acl2::aig-var-listp (alist-keys reg-alist)))
                 (and (iff (hons-assoc-equal var env)
                           (hons-assoc-equal var (append (aignet-bitarr-to-aig-env regvars reg-vals)
                                                         (aignet-bitarr-to-aig-env invars in-vals))))
                      (equal (cdr (hons-assoc-equal var env))
                             (cdr (hons-assoc-equal var (append (aignet-bitarr-to-aig-env regvars reg-vals)
                                                                (aignet-bitarr-to-aig-env invars in-vals))))))))
      :hints(("Goal" :in-theory (e/d (aignet-eval-to-env
                                      aignet-bitarr-to-aig-env
                                      aig-fsm-prepare-aignet/varmap
                                      aignet-idp
                                      acl2::hons-assoc-equal-iff-member-alist-keys)
                                     (acl2::alist-keys-member-hons-assoc-equal))
              :do-not-induct t
              :expand ((:free (n aignet)
                        (lit-eval (make-lit (+ 1 n) 0) in-vals reg-vals aignet))
                       (:free (n aignet)
                        (id-eval (+ 1 n) in-vals reg-vals aignet))))))

    (local (defthmd equal-of-hons-assoc-equal
             (equal (equal (hons-assoc-equal k x) y)
                    (if (hons-assoc-equal k x)
                        (and (consp y)
                             (equal (car y) k)
                             (equal (cdr y) (cdr (hons-assoc-equal k x))))
                      (not y)))
             :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

    (defthm aignet-eval-to-env-of-varmap-lookup-alist-equiv
      (b* (((mv ?aignet varmap invars regvars)
            (aig-fsm-to-aignet reg-alist out-list max-gates gatesimp aignet))
           (env (aignet-eval-to-env varmap in-vals reg-vals aignet)))
        (implies (and (no-duplicatesp (alist-keys reg-alist))
                      (acl2::aig-var-listp (alist-keys reg-alist)))
                 (acl2::alist-equiv env
                                    (append (aignet-bitarr-to-aig-env regvars reg-vals)
                                            (aignet-bitarr-to-aig-env invars in-vals)))))
      :hints(("Goal" :in-theory (e/d (acl2::alist-equiv-iff-agree-on-bad-guy
                                      equal-of-hons-assoc-equal)
                                     (AIG-FSM-TO-AIGNET)))))


    (defthm good-varmap-p-of-aig-fsm-to-aignet
      (implies (acl2::aig-var-listp (alist-keys regs))
               (good-varmap-p (mv-nth 1 (aig-fsm-to-aignet regs outs max-gates
                                                           gatesimp aignet))
                              (mv-nth 0 (aig-fsm-to-aignet regs outs max-gates
                                                           gatesimp aignet))))
      :hints(("Goal" :in-theory (e/d* ()
                                      (aiglist-to-aignet
                                       lit-eval-list
                                       acl2::aig-eval-list
                                       aignet-eval-to-env
                                       aig-vars
                                       acl2::hons-sd1
                                       len
                                       pairlis$
                                       hons-assoc-equal
                                       acl2::make-fal
                                       set::double-containment
                                       resize-list))
              :do-not-induct t)))

    (std::defret outputs-of-aig-fsm-to-aignet
      (equal (stype-count :po new-aignet)
             (len out-list)))

    (std::defret inputs-of-aig-fsm-to-aignet
      (equal (stype-count :pi new-aignet)
             (len invars)))


    
    (std::defret aig-fsm-to-aignet-input-varmap-lookup
      (implies (and (member v (acl2::aiglist-vars (append (alist-vals reg-alist) out-list)))
                    (not (hons-assoc-equal v reg-alist)))
               (b* ((index (acl2::index-of v invars))
                    (input-id (node-count (lookup-stype index :pi new-aignet))))
                 (equal (hons-assoc-equal v varmap)
                        (cons v (mk-lit input-id 0))))))

    ;; (std::defretd input-id-of-aig-fsm-prepare-input-varmap-lookup
    ;;   (implies (and (member v (acl2::aiglist-vars (append (alist-vals reg-alist) out-list)))
    ;;                 (not (hons-assoc-equal v reg-alist)))
    ;;            (b* ((index (acl2::index-of v input-vars))
    ;;                 (input-id (node-count (lookup-stype index :pi new-aignet))))
    ;;              (equal input-id (+ 1 index)))))

    (std::defret aig-fsm-to-aignet-reg-varmap-lookup
      (implies (and (member v (acl2::aiglist-vars (append (alist-vals reg-alist) out-list)))
                    (hons-assoc-equal v reg-alist)
                    (no-duplicatesp (alist-keys reg-alist)))
               (b* ((index (acl2::index-of v (alist-keys reg-alist)))
                    (reg-id (node-count (lookup-stype index :reg new-aignet))))
                 (equal (hons-assoc-equal v varmap)
                        (cons v (mk-lit reg-id 0))))))

    (std::defret in-vars-of-aig-fsm-to-aignet
      (acl2::set-equiv invars
                       (set-difference$ (acl2::aiglist-vars (append (alist-vals reg-alist) out-list))
                                        (alist-keys reg-alist))))

    (std::defret reg-vars-of-aig-fsm-to-aignet
      (equal regvars (alist-keys reg-alist)))

    (std::defret reg-count-of-aig-fsm-to-aignet
      (equal (stype-count :reg new-aignet) (len (alist-keys reg-alist))))

    (std::defret in-count-of-aig-fsm-to-aignet
      (equal (stype-count :pi new-aignet) (len invars)))))







  








(define aig-fsm-frame-env ((regs "alist")
                           (curr-st "bindings to t/nil")
                           (in "bindings to t/nil"))
  (append (fast-alist-free
           (with-fast-alist curr-st
             (acl2::aig-env-extract (alist-keys regs) curr-st)))
          in)
  ///
  (defthm lookup-in-aig-fsm-frame-env
    (equal (acl2::aig-env-lookup v (aig-fsm-frame-env regs curr-st in))
           (if (hons-assoc-equal v regs)
               (acl2::aig-env-lookup v curr-st)
             (acl2::aig-env-lookup v in)))
    :hints(("Goal" :in-theory (enable acl2::aig-env-lookup))))

  (defthm hons-assoc-equal-in-aig-fsm-frame-env
    (equal (hons-assoc-equal v (aig-fsm-frame-env regs curr-st in))
           (if (hons-assoc-equal v regs)
               (cons v (acl2::aig-env-lookup v curr-st))
             (hons-assoc-equal v in)))
    :hints(("Goal" :in-theory (enable acl2::aig-env-lookup)))))

(define aig-fsm-frame-outs ((outputs "aig list")
                            (regs "alist")
                            (curr-st "bindings to t/nil")
                            (in "bindings to t/nil"))
  (b* ((env (aig-fsm-frame-env regs curr-st in)))
    (acl2::aig-eval-list outputs env))
  ///
  (defthm nth-of-aig-fsm-frame-outs
    (equal (nth n (aig-fsm-frame-outs outputs regs curr-st in))
           (aig-eval (nth n outputs) (aig-fsm-frame-env regs curr-st in)))))

(define aig-fsm-frame-nextst ((regs "alist")
                              (curr-st "bindings to t/nil")
                              (in "bindings to t/nil"))
  :returns (nextst)
  (b* ((env (aig-fsm-frame-env regs curr-st in)))
    (acl2::aig-eval-alist regs env))
  ///
  (std::defret aig-env-lookup-in-aig-fsm-frame-nextst
    (implies (hons-assoc-equal v regs)
             (equal (acl2::aig-env-lookup v nextst)
                    (aig-eval (cdr (hons-assoc-equal v regs))
                              (aig-fsm-frame-env regs curr-st in))))
    :hints(("Goal" :in-theory (enable acl2::aig-env-lookup)))))

(define aig-fsm-run ((outputs "aig list")
                     (regs "alist")
                     (curr-st "bindings to t/nil")
                     (ins "list of bindings to t/nil"))
  :returns (result-list "list of bool lists")
  (if (atom ins)
      nil
    (b* ((env ;; apply curr-st to (car ins)
          (aig-fsm-frame-env regs curr-st (car ins))))
      (mbe :logic
           (b* ((outs (acl2::aig-eval-list outputs env))
                (next-st (acl2::aig-eval-alist regs env)))
             (cons outs (aig-fsm-run outputs regs next-st (cdr ins))))
           :exec
           (if (atom (cdr ins))
               (with-fast-alist env
                 (list (acl2::aig-eval-list outputs env)))
             (b* (((mv outs next-st)
                   (with-fast-alist env
                     (b* ((outs (acl2::aig-eval-list outputs env))
                          (next-st (acl2::aig-eval-alist regs env)))
                       (mv outs next-st)))))
               (cons outs (aig-fsm-run outputs regs next-st (cdr ins))))))))
  ///
  (defthm aig-fsm-run-of-cons
    (equal (aig-fsm-run outputs regs curr-st (cons in1 rest-ins))
           (cons (aig-fsm-frame-outs outputs regs curr-st in1)
                 (aig-fsm-run outputs regs
                              (aig-fsm-frame-nextst regs curr-st in1)
                              rest-ins)))
    :hints(("Goal" :in-theory (enable aig-fsm-frame-outs
                                      aig-fsm-frame-nextst))))

  (defthm car-of-aig-fsm-run
    (Equal (car (aig-fsm-run outputs regs curr-st ins))
           (and (consp ins)
                (aig-fsm-frame-outs outputs regs curr-st (car ins)))))

  (defthm cdr-of-aig-fsm-run
    (Equal (cdr (aig-fsm-run outputs regs curr-st ins))
           (and (consp ins)
                (aig-fsm-run outputs regs
                             (aig-fsm-frame-nextst regs curr-st (car ins))
                             (cdr ins))))))

(define aig-fsm-states ((regs "alist")
                        (curr-st "bindings to t/nil")
                        (ins "list of bindings to t/nil"))
  (b* (((when (atom ins)) nil)
       (next-st (aig-fsm-frame-nextst regs curr-st (car ins))))
    (cons next-st (aig-fsm-states regs next-st (cdr ins))))
  ///
  (defthm nth-of-aig-fsm-run
    (implies (< (nfix n) (len ins))
             (equal (nth n (aig-fsm-run outputs regs curr-st ins))
                    (aig-fsm-frame-outs outputs regs
                                        (if (zp n)
                                            curr-st
                                          (nth (1- n) (aig-fsm-states regs curr-st ins)))
                                        (nth n ins))))
    :hints(("Goal" :in-theory (enable aig-fsm-states nth)))))


(defthm aig-fsm-run-in-terms-of-aig-eval
  (implies (< (nfix k) (len ins))
           (equal (nth n (nth k (aig-fsm-run outputs regs curr-st ins)))
                  (aig-eval (nth n outputs)
                                  (aig-fsm-frame-env
                                   regs
                                   (if (zp k)
                                       curr-st
                                     (nth (1- k) (aig-fsm-states regs curr-st ins)))
                                   (nth k ins))))))

(local (defun aig-fsm-state-ind (k regs curr-st ins)
         (if (zp k)
             (list regs curr-st ins)
           (aig-fsm-state-ind (1- k) regs (aig-fsm-frame-nextst regs curr-st (car ins)) (cdr ins)))))

(defthm aig-fsm-state-in-terms-of-aig-eval
  (implies (and (hons-assoc-equal v regs)
                (< (nfix k) (len ins)))
           (equal (acl2::aig-env-lookup v (nth k (aig-fsm-states regs curr-st ins)))
                  (aig-eval (cdr (hons-assoc-equal v regs))
                            (aig-fsm-frame-env
                             regs
                             (if (zp k)
                                 curr-st
                               (nth (1- k) (aig-fsm-states regs curr-st ins)))
                             (nth k ins)))))
  :hints(("Goal" :in-theory (e/d (aig-fsm-states nth) (acl2::aig-env-lookup))
          :induct (aig-fsm-state-ind k regs curr-st ins)
          :expand ((aig-fsm-states regs curr-st ins)))))


;; (defthm aig-eval-of-extract-vars-removal
;;   (implies (Subsetp (acl2::aiglist-vars x) vars)
;;            (equal (aig-eval x (acl2::aig-env-extract vars env))
;;                   (aig-eval x env)))
;;   :hints(("Goal" :in-theory (enable aig-eval))))

;; (defthm aig-env-extract-of-aig-env-extract
;;   (implies (subsetp vars1 vars2)
;;            (Equal (acl2::aig-env-extract vars1 (acl2::aig-env-extract vars2 env))
;;                   (acl2::aig-env-extract vars1 env)))
;;   :hints(("Goal" :in-theory (enable acl2::aig-env-extract))))

;; (defmacro bind-aig-env-extract-env (vars env new-env)
;;   `(and (equal extract-vars-tmp-vars ,vars)
;;         (equal extract-vars-tmp-env (acl2::aig-env-extract extract-vars-tmp-vars ,env))
;;         (bind-free
;;          (and (not (subtermp ,env extract-vars-tmp-env))
;;               (case-match extract-vars-tmp-env
;;                 (('acl2::aig-env-extract vars1 env1)
;;                  (if (equal vars1 extract-vars-tmp-vars)
;;                      `((,',new-env . ,env1))
;;                    `((,',new-env . ,extract-vars-tmp-env))))
;;                 (& `((,',new-env . ,extract-vars-tmp-env)))))
;;          (,new-env))
;;         (equal extract-vars-tmp-env
;;                (acl2::aig-env-extract extract-vars-tmp-vars ,new-env))))
        
;; (defthm aig-eval-of-extract-vars-propagate
;;   (implies (bind-aig-env-extract-env (acl2::aiglist-vars x) env new-env)
;;            (equal (aig-eval x env)
;;                   (aig-eval x new-env)))
;;   :hints (("goal" :use ((:instance aig-eval-of-extract-vars-removal
;;                          (vars (acl2::aiglist-vars x)) (env env))
;;                         (:instance aig-eval-of-extract-vars-removal
;;                          (vars (acl2::aiglist-vars x)) (env new-env)))
;;            :in-theory (disable aig-eval-of-extract-vars-removal))))


(defun-sk reg-vals-equivalent (regs aignet-frame aig-currst)
  (forall v
          (implies (hons-assoc-equal v regs)
                   (equal (nth (acl2::index-of v (alist-keys regs)) aignet-frame)
                          (acl2::bool->bit (acl2::aig-env-lookup v aig-currst)))))
  :rewrite :direct)

(in-theory (disable reg-vals-equivalent))

(defun-sk aig-envs-agree (vars x y)
  (forall v
          (implies (member v vars)
                   (equal (acl2::aig-env-lookup v x)
                          (acl2::aig-env-lookup v y))))
  :rewrite :direct)

(in-theory (disable aig-envs-agree))


(local (defthmd equal-of-aig-env-extract-when-aig-envs-agree
         (implies (and (aig-envs-agree vars1 x y)
                       (subsetp vars vars1))
                  (equal (acl2::aig-env-extract vars x) (acl2::aig-env-extract vars y)))
         :hints(("Goal" :in-theory (enable acl2::aig-env-extract)))))

(local (defthmd not-equal-of-aig-env-extract-when-witness
         (implies (and (member v vars)
                       (not (equal (acl2::aig-env-lookup v x) (acl2::aig-env-lookup v y))))
                  (not (equal (acl2::aig-env-extract vars x) (acl2::aig-env-extract vars y))))
         :hints(("Goal" :in-theory (enable acl2::aig-env-extract)))))

(local (defthmd equal-of-aig-env-extract-by-aig-envs-agree
         (iff (equal (acl2::aig-env-extract vars x) (acl2::aig-env-extract vars y))
              (aig-envs-agree vars x y))
         :hints(("Goal" :in-theory (enable equal-of-aig-env-extract-when-aig-envs-agree))
                (and stable-under-simplificationp
                     '(:in-theory (enable aig-envs-agree
                                          not-equal-of-aig-env-extract-when-witness))))))

(defthm reg-vals-equivalent-implies-rewrite-aig-fsm-frame-env
  (implies (reg-vals-equivalent regs aignet-frame aig-currst)
           (equal (aig-fsm-frame-env regs
                                     (aignet-bitarr-to-aig-env (alist-keys regs) aignet-frame)
                                     ins)
                  (aig-fsm-frame-env regs aig-currst ins)))
  :hints(("Goal" :in-theory (e/d (aig-fsm-frame-env acl2::aig-env-extract alist-keys
                                    equal-of-aig-env-extract-by-aig-envs-agree
                                    aig-envs-agree)
                                 (acl2::aig-env-lookup))
          :do-not-induct t)))

;; (defstub ??? () nil)


(defthm lit-eval-of-aignet-input
  (implies (< (nfix n) (stype-count :pi aignet))
           (equal (lit-eval (mk-lit (node-count (lookup-stype n :pi aignet))
                                    neg)
                            in-vals reg-vals aignet)
                  (b-xor neg (nth n in-vals))))
  :hints(("Goal" :in-theory (enable lit-eval id-eval))))

(defthm lit-eval-of-aignet-reg
  (implies (< (nfix n) (stype-count :reg aignet))
           (equal (lit-eval (mk-lit (node-count (lookup-stype n :reg aignet))
                                    neg)
                            in-vals reg-vals aignet)
                  (b-xor neg (nth n reg-vals))))
  :hints(("Goal" :in-theory (enable lit-eval id-eval))))

(local (defthm index-of-less-than-len
         (implies (double-rewrite (member v x))
                  (< (nfix (acl2::index-of v x)) (len x)))))

;; (local (in-theory (disable acl2::aig-env-lookup)))

(local (defthm aig-env-lookup-of-aignet-eval-to-env-of-aig-fsm-to-aignet
         (b* (((mv aignet ?varmap ?invars ?regvars)
               (aig-fsm-to-aignet regs outs max-gates gatesimp aignet)))
           (implies (and (no-duplicatesp (alist-keys regs))
                         (member v (acl2::aiglist-vars (append (alist-vals regs) outs))))
                    (equal (acl2::aig-env-lookup v (aignet-eval-to-env varmap in-vals reg-vals aignet))
                           (if (hons-assoc-equal v regs)
                               (equal 1 (nth (acl2::index-of v regvars) reg-vals))
                             (equal 1 (nth (acl2::index-of v invars) in-vals))))))))



(local (defthm aig-eval-of-aignet-eval-to-env-of-aig-fsm-to-aignet
         (b* (((mv aignet ?varmap ?invars ?regvars)
               (aig-fsm-to-aignet regs outs max-gates gatesimp aignet)))
           (implies (and (subsetp-equal (aig-vars x) (acl2::aiglist-vars (append (alist-vals regs) outs)))
                         (no-duplicatesp (alist-keys regs)))
                    (Equal (aig-eval x (aignet-eval-to-env varmap in-vals reg-vals aignet))
                           (aig-eval x (aig-fsm-frame-env regs
                                                          (aignet-bitarr-to-aig-env (alist-keys regs) reg-vals)
                                                          (aignet-bitarr-to-aig-env invars in-vals))))))
         :hints(("Goal" :in-theory (e/d (aig-eval) (acl2::aig-env-lookup))
                 :induct (aig-vars x)))))




(acl2::defines reg-eval-of-aig-fsm-to-aignet-ind
  :verify-guards nil
  (define frame-regvals-of-aig-fsm-to-aignet-ind (k regs outs max-gates gatesimp aignet0 frames initsts)
    :non-executable t
    :measure (* 2 (nfix k))
    (b* (((when (zp k)) (list regs outs max-gates gatesimp aignet0 frames initsts))
         ((mv aignet ?varmap ?invars ?regvars)
          (aig-fsm-to-aignet regs outs max-gates gatesimp aignet0))
         (regvals (frame-regvals k frames initsts aignet))
         (frame-st (nth (1- k) (aig-fsm-states regs
                                           (aignet-bitarr-to-aig-env (alist-keys regs) initsts)
                                           (aignet-frames-to-aig-envs frames invars))))
         (reg-name (reg-vals-equivalent-witness regs regvals frame-st))
         (regnum (acl2::index-of reg-name (alist-keys regs)))
         ;; (nxst (node-count (lookup-reg->nxst (regnum->id regnum aignet) aignet)))
         )
      (reg-eval-of-aig-fsm-to-aignet-ind regnum (1- k) regs outs max-gates gatesimp aignet0 frames initsts)))

  (define reg-eval-of-aig-fsm-to-aignet-ind (n k regs outs max-gates gatesimp aignet0 frames initsts)
    :non-executable t
    :measure (+ 1 (* 2 (nfix k)))
    (frame-regvals-of-aig-fsm-to-aignet-ind k regs outs max-gates gatesimp aignet0 frames initsts))
  ///

  (local (in-theory (enable lit-eval-seq-in-terms-of-lit-eval)))

  (local (defthm subsetp-vars-of-nth-reg
           (subsetp (aig-vars (nth n regvals))
                    (acl2::aiglist-vars (append regvals outs)))
           :hints(("Goal" :in-theory (enable nth aig-vars acl2::aiglist-vars)))))

  (local (in-theory (disable acl2::aig-env-lookup)))

  (local (defthm nth-index-of-alist-keys-in-alist-vals
           (implies (hons-assoc-equal v x)
                    (equal (nth (acl2::index-of v (alist-keys x)) (alist-vals x))
                           (cdr (hons-assoc-equal v x))))
           :hints(("Goal" :in-theory (enable hons-assoc-equal nth acl2::index-of alist-keys alist-vals)))))

  (local (defthm subsetp-vars-of-nth
           (subsetp (aig-vars (nth n x))
                    (acl2::aiglist-vars x))
           :hints(("Goal" :in-theory (enable aig-vars nth acl2::aiglist-vars)))))

  (local (defthm subsetp-vars-of-nth-out
           (subsetp (aig-vars (nth n outs))
                    (acl2::aiglist-vars (append regvals outs)))
           :hints(("Goal" :in-theory (enable aig-vars append acl2::aiglist-vars)))))

  (local (defthm bits-to-bools-of-take
           (Equal (bits-to-bools (take n x))
                  (take n (bits-to-bools x)))
           :hints(("Goal" :in-theory (e/d (bits-to-bools (:i nthcdr))
                                          (acl2::take-of-too-many
                                           acl2::take-when-atom))
                   :induct (nthcdr n x)))))

  (local (defthm pairlis$-of-take-len
           (equal (pairlis$ x (take (len x) y))
                  (pairlis$ x y))
           :hints(("Goal" :in-theory (enable pairlis$)))))

  (local (defthm aignet-bitarr-to-aig-env-of-take
           (equal (aignet-bitarr-to-aig-env vars (take (len vars) bitarr))
                  (aignet-bitarr-to-aig-env vars bitarr))
           :hints(("Goal" :in-theory (enable aignet-bitarr-to-aig-env)))))

  (defthm-reg-eval-of-aig-fsm-to-aignet-ind-flag
    (defthm frame-regvals-of-aig-fsm-to-aignet
      (b* (((mv aignet ?varmap ?invars ?regvars)
            (aig-fsm-to-aignet regs outs max-gates gatesimp aignet0))
           (aig-ins (aignet-frames-to-aig-envs frames invars))
           (aig-initst (aignet-bitarr-to-aig-env (alist-keys regs) initsts)))
        (implies (and (< (nfix k) (len (stobjs::2darr->rows frames)))
                      (acl2::aig-var-listp (alist-keys regs))
                      (no-duplicatesp (alist-keys regs)))
                 (reg-vals-equivalent regs (frame-regvals k frames initsts aignet)
                                      (if (zp k)
                                          aig-initst
                                        (nth (1- k) (aig-fsm-states regs aig-initst aig-ins))))))
      :hints ((and stable-under-simplificationp
                   `(:expand (,(car (last clause)))
                     :in-theory (enable reg-eval-seq))))
      :flag frame-regvals-of-aig-fsm-to-aignet-ind)

    (defthm reg-eval-of-aig-fsm-to-aignet
      (b* (((mv aignet ?varmap ?invars ?regvars)
            (aig-fsm-to-aignet regs outs max-gates gatesimp aignet0))
           (aig-ins (aignet-frames-to-aig-envs frames invars))
           (aig-initst (aignet-bitarr-to-aig-env (alist-keys regs) initsts)))
        (implies (and (< (nfix n) (len (alist-keys regs)))
                      (< (nfix k) (len (stobjs::2darr->rows frames)))
                      (acl2::aig-var-listp (alist-keys regs))
                      (no-duplicatesp (alist-keys regs)))
                 (equal (lit-eval-seq k (fanin-if-co (lookup-regnum->nxst n aignet))
                                     frames initsts aignet)
                        (acl2::bool->bit (aig-eval (nth n (alist-vals regs))
                                                   (aig-fsm-frame-env
                                                    regs
                                                    (if (zp k)
                                                        aig-initst
                                                      (nth (1- k) (aig-fsm-states regs aig-initst aig-ins)))
                                                    (nth k aig-ins)))))))
      :flag reg-eval-of-aig-fsm-to-aignet-ind))

  (defthm out-eval-of-aig-fsm-to-aignet
    (b* (((mv aignet ?varmap ?invars ?regvars)
          (aig-fsm-to-aignet regs outs max-gates gatesimp aignet0))
         (aig-ins (aignet-frames-to-aig-envs frames invars))
         (aig-initst (aignet-bitarr-to-aig-env (alist-keys regs) initsts)))
      (implies (and (< (nfix n) (len outs))
                    (< (nfix k) (len (stobjs::2darr->rows frames)))
                    (acl2::aig-var-listp (alist-keys regs))
                    (no-duplicatesp (alist-keys regs)))
               (equal (lit-eval-seq k (fanin :co (lookup-stype n :po aignet))
                                    frames initsts aignet)
                      (acl2::bool->bit (nth n (nth k (aig-fsm-run outs regs aig-initst aig-ins)))))))
    :hints (("Goal" :use ((:instance frame-regvals-of-aig-fsm-to-aignet))
             :in-theory (disable frame-regvals-of-aig-fsm-to-aignet)))))


(define frames-row-fix ((ncols natp)
                        (row))
  :verify-guards nil
  :returns (new-row (and (framese-datap new-row)
                         (equal (len new-row) (nfix ncols))))
  (if (zp ncols)
      nil
    (cons (bfix (car row))
          (frames-row-fix (1- ncols) (cdr row))))
  ///
  (std::defret frames-row-fix-when-framese-datap
    (implies (and (framese-datap row)
                  (equal (len row) (nfix ncols)))
             (equal new-row row)))

  (local (defun nth-of-frames-row-fix-ind (n ncols row)
           (if (zp ncols)
               (list n row)
             (nth-of-frames-row-fix-ind (1- (nfix n)) (1- ncols) (cdr row)))))

  (std::defret nth-of-frames-row-fix
    (equal (nth n new-row)
           (and (< (nfix n) (nfix ncols))
                (bfix (nth n row))))
    :hints(("Goal" :in-theory (enable nth)
            :induct (nth-of-frames-row-fix-ind n ncols row)
            :expand ((:free (x) (nth n x)))))))

(define frames-fix-row ((row natp) frames)
  :guard (< row (frames-nrows frames))
  :returns (new-frames stobjs::2darr-p :hyp (stobjs::2darr-p frames))
  (mbe :logic (non-exec
               (b* ((rows (stobjs::2darr->rows frames))
                    (ncols (stobjs::2darr->ncols frames))
                    (nth-row (nth row rows))
                    (new-rows (update-nth row (frames-row-fix ncols nth-row) rows)))
                 (stobjs::2darr ncols new-rows)))
       :exec frames)
  ///
  (std::defret ncols-of-frames-fix-row
    (equal (stobjs::2darr->ncols new-frames)
           (stobjs::2darr->ncols frames)))

  (std::defret nth-of-frames-fix-row
    (equal (nth n (stobjs::2darr->rows new-frames))
           (if (equal (nfix n) (nfix row))
               (frames-row-fix (stobjs::2darr->ncols frames) (nth row (stobjs::2darr->rows frames)))
             (nth n (stobjs::2darr->rows frames)))))

  (std::defret nrows-of-frames-fix-row
    (implies (< (nfix row) (len (stobjs::2darr->rows frames)))
             (equal (len (stobjs::2darr->rows new-frames))
                    (len (stobjs::2darr->rows frames)))))

  (fty::deffixcong nat-equiv equal (frames-fix-row row frames) row))
                 

;; (define frames-arr-fix ((ncols natp)
;;                         (arr))
;;   :verify-guards nil
;;   :returns (new-arr (framesl-arr2-data-wfp new-arr ncols))
;;   (if (atom arr)
;;       nil
;;     (cons (frames-row-fix ncols (car arr))
;;           (frames-arr-fix ncols (cdr arr))))
;;   ///
;;   (std::defret frames-arr-fix-whne-framesl-arr2-data-wfp
;;     (implies (framesl-arr2-data-wfp arr ncols)
;;              (equal new-arr arr)))

;;   (std::defret len-of-frames-arr-fix
;;     (equal (len new-arr) (len arr))))
    

;; (define frames-fix (frames)
;;   :non-executable t
;;   :verify-guards nil
;;   :returns (new-frames framesl-arr2-wfp
;;                        :hyp (<= (* (stobjs::2darr->ncols frames)
;;                                    (len (stobjs::2darr->rows frames)))
;;   (b* ((ncols (stobjs::2darr->ncols frames))
;;        (arr (stobjs::2darr->rows frames)))
;;     (stobjs::2darr ncols
;;                    (frames-arr-fix ncols arr)))
;;   ///
;;   (std::defret frames-fix-when-framesl-arr2-wfp
;;     (implies (framesl-arr2-wfp frames)
;;              (equal new-frames frames)))

;;   (std::defret ncols-of-frames-fix
;;     (equal (stobjs::2darr->ncols new-frames)
;;            (stobjs::2darr->ncols frames))))

(define env-to-frame-aux ((n natp) (i natp) vars env frames)
  :guard (and (< n (frames-nrows frames))
              (<= i (frames-ncols frames))
              (equal (len vars) (- (frames-ncols frames) i)))
  :returns (new-frames stobjs::2darr-p :hyp (stobjs::2darr-p frames))
  (if (atom vars)
      (frames-fix-row n frames)
    (b* ((val (acl2::bool->bit (acl2::aig-env-lookup (car vars) env)))
         (frames (frames-set2 n i val frames)))
      (env-to-frame-aux n (1+ (lnfix i)) (cdr vars) env frames)))
  ///
  (local (in-theory (disable acl2::aig-env-lookup)))

  (std::defret env-to-frame-aux-preserves-ncols
    (equal (stobjs::2darr->ncols new-frames)
           (stobjs::2darr->ncols frames)))

  ;; (std::defret env-to-frame-aux-preserves-other-row
  ;;   (implies (not (equal (nfix n) (nfix m)))
  ;;            (equal (nth m (stobjs::2darr->rows new-frames))
  ;;                   (nth m (stobjs::2darr->rows frames)))))

  ;; (std::defret env-to-frame-aux-lookup
  ;;   (equal (nth j (nth n (stobjs::2darr->rows new-frames)))
  ;;          (if (and (<= (nfix i) (nfix j))
  ;;                   (< (nfix j) (+ (len vars) (nfix i))))
  ;;              (acl2::bool->bit (acl2::aig-env-lookup (nth (- (nfix j) (nfix i)) vars) env))
  ;;            (nth j (nth n (stobjs::2darr->rows frames)))))
  ;;   :hints(("Goal" :in-theory (e/d (nth) (acl2::aig-env-lookup)))))

  (local (defthm frames-row-fix-of-append-when-first-len
           (implies (equal (len a) (nfix n))
                    (equal (Frames-row-fix n (append a b))
                           (frames-row-fix n a)))
           :hints(("Goal" :in-theory (enable frames-row-fix)))))

  (local (defthm frames-row-fix-of-take-n
           (implies (equal (nfix i) (nfix n))
                    (equal (Frames-row-fix n (take i x))
                           (frames-row-fix n x)))
           :hints(("Goal" :in-theory (enable frames-row-fix)))))

  (local (defthm take-n-plus-one
           (Equal (take (+ 1 (nfix n)) x)
                  (append (take n x) (list (nth n x))))
           :hints(("Goal" :in-theory (e/d (nth acl2::repeat)
                                          (acl2::take-of-too-many
                                           ;; acl2::take-when-atom
                                           acl2::take-of-1
                                           acl2::take-of-zero))))))

  (local (defthm take-of-update-nth
           (equal (take n (update-nth n val x))
                  (take n x))
           :hints(("Goal" :in-theory (enable update-nth)))))

  (std::defretd env-to-frame-aux-is-update-nth
    (implies (equal (len vars) (- (frames-ncols frames) (nfix i)))
             (equal (stobjs::2darr->rows new-frames)
                    (update-nth n
                                (frames-row-fix (frames-ncols frames)
                                                (append (take i (nth n (stobjs::2darr->rows frames)))
                                                        (env-to-bitarr vars env)))
                                (stobjs::2darr->rows frames))))
    :hints(("Goal" :in-theory (enable frames-fix-row env-to-bitarr))))

  (std::defret nth-of-env-to-frame-aux
    (implies (equal (len vars) (- (frames-ncols frames) (nfix i)))
             (equal (nth m (stobjs::2darr->rows new-frames))
                    (if (equal (nfix n) (nfix m))
                        (frames-row-fix (frames-ncols frames)
                                        (append (take i (nth n (stobjs::2darr->rows frames)))
                                                (env-to-bitarr vars env)))
                      (nth m (stobjs::2darr->rows frames)))))
    :hints(("Goal" :in-theory (e/d (env-to-frame-aux-is-update-nth)
                                   (env-to-frame-aux)))))

  (std::defret len-rows-of-env-to-frame-aux
    (implies (< (nfix n) (len (stobjs::2darr->rows frames)))
             (equal (len (stobjs::2darr->rows new-frames))
                    (len (stobjs::2darr->rows frames)))))

  (fty::deffixcong nat-equiv equal (env-to-frame-aux n i vars env frames) n))



(define env-to-frame ((n natp) vars env frames)
  :guard (and (< n (frames-nrows frames))
              (equal (len vars) (frames-ncols frames)))
  :returns (new-frames stobjs::2darr-p :hyp (stobjs::2darr-p frames))
  (env-to-frame-aux n 0 vars env frames)
  ///
  (std::defret env-to-frame-preserves-ncols
    (equal (stobjs::2darr->ncols new-frames)
           (stobjs::2darr->ncols frames)))

  ;; (std::defret env-to-frame-preserves-other-row
  ;;   (implies (not (equal (nfix n) (nfix m)))
  ;;            (equal (nth m (stobjs::2darr->rows new-frames))
  ;;                   (nth m (stobjs::2darr->rows frames)))))

  ;; (std::defret env-to-frame-lookup
  ;;   (equal (nth j (nth n (stobjs::2darr->rows new-frames)))
  ;;          (if (< (nfix j) (len vars))
  ;;              (acl2::bool->bit (acl2::aig-env-lookup (nth j vars) env))
  ;;            (nth j (nth n (stobjs::2darr->rows frames)))))
  ;;   :hints(("Goal" :in-theory (disable acl2::aig-env-lookup))))

  (local (defthm frames-row-fix-of-env-to-bitarr
           (implies (equal n (len vars))
                    (Equal (frames-row-fix n (env-to-bitarr vars env))
                           (env-to-bitarr vars env)))
           :hints (("goal" :induct (nthcdr n vars)
                    :in-theory (enable env-to-bitarr frames-row-fix)))))

  (std::defret env-to-frame-is-update-nth
    (implies (equal (len vars) (frames-ncols frames))
             (equal (stobjs::2darr->rows new-frames)
                    (update-nth n (env-to-bitarr vars env)
                                (stobjs::2darr->rows frames))))
    :hints(("Goal" :in-theory (enable env-to-frame-aux-is-update-nth))))

  (std::defretd nth-of-env-to-frame
    (implies (equal (len vars) (frames-ncols frames))
             (equal (nth m (stobjs::2darr->rows new-frames))
                    (if (equal (nfix n) (nfix m))
                        (env-to-bitarr vars env)
                      (nth m (stobjs::2darr->rows frames)))))
    :hints(("Goal" :in-theory (e/d (env-to-frame-is-update-nth) (env-to-frame)))))

  (std::defret len-rows-of-env-to-frame
    (implies (< (nfix n) (len (stobjs::2darr->rows frames)))
             (equal (len (stobjs::2darr->rows new-frames))
                    (len (stobjs::2darr->rows frames)))))

  (fty::deffixcong nat-equiv equal (env-to-frame n vars env frames) n))

(define envs-to-bitarrs (vars envs)
  :returns (bitarrs)
  (if (atom envs)
      nil
    (cons (env-to-bitarr vars (car envs))
          (envs-to-bitarrs vars (cdr envs))))
  ///
  (std::defret len-of-envs-to-bitarrs
    (equal (len bitarrs) (len envs)))

  (std::defret consp-of-envs-to-bitarrs
    (equal (consp bitarrs) (consp envs))))
           

(define aig-envs-to-aignet-frames-aux ((n natp) vars envs frames)
  :guard (and (<= (+ n (len envs)) (frames-nrows frames))
              (equal (len vars) (frames-ncols frames)))
  :returns (new-frames stobjs::2darr-p :hyp (stobjs::2darr-p frames))
  :prepwork ((local (defthm len-equal-0
                      (equal (equal (len x) 0) (not (consp x))))))
  :verify-guards nil
  (if (atom envs)
      frames
    (b* ((frames (env-to-frame n vars (car envs) frames)))
      (aig-envs-to-aignet-frames-aux (1+ (lnfix n)) vars (cdr envs) frames)))
  ///
  (std::defret aig-envs-to-aignet-frames-aux-preserves-ncols
    (equal (stobjs::2darr->ncols new-frames)
           (stobjs::2darr->ncols frames)))

  (local (defthm take-n-plus-one
           (Equal (take (+ 1 (nfix n)) x)
                  (append (take n x) (list (nth n x))))
           :hints(("Goal" :in-theory (e/d (nth acl2::repeat)
                                          (acl2::take-of-too-many
                                           ;; acl2::take-when-atom
                                           acl2::take-of-1
                                           acl2::take-of-zero))))))

  (local (defthm take-of-update-nth
           (equal (take n (update-nth n val x))
                  (take n x))
           :hints(("Goal" :in-theory (enable update-nth)))))

  (local (defthm nthcdr-of-update-nth
           (equal (nthcdr n (update-nth m v x))
                  (if (<= (nfix n) (nfix m))
                      (update-nth (- (nfix m) (nfix n)) v (nthcdr n x))
                    (nthcdr n x)))
           :hints(("Goal" :in-theory (enable update-nth)))))

  (std::defretd rows-of-aig-envs-to-aignet-frames-aux
    (implies (and (equal (len vars) (frames-ncols frames))
                  (<= (+ (nfix n) (len envs)) (frames-nrows frames)))
             (equal (stobjs::2darr->rows new-frames)
                    (append (take n (stobjs::2darr->rows frames))
                            (envs-to-bitarrs vars envs)
                            (nthcdr (+ (nfix n) (len envs)) (stobjs::2darr->rows frames)))))
    :hints(("Goal" :in-theory (e/d (envs-to-bitarrs
                                    env-to-frame-is-update-nth)
                                   (acl2::take-redefinition nthcdr (force))))))

  (std::defret aig-envs-to-aignet-frames-aux-lookup
    (implies (equal (len vars) (frames-ncols frames))
             (equal (nth m (stobjs::2darr->rows new-frames))
                    (if (and (<= (nfix n) (nfix m))
                             (< (nfix m) (+ (nfix n) (len envs))))
                        (env-to-bitarr vars (nth (- (nfix m) (nfix n)) envs))
                      (nth m (stobjs::2darr->rows frames)))))
    :hints(("Goal" :in-theory (enable nth))))

  (std::defret len-rows-of-aig-envs-to-aignet-frames-aux
    (implies (<= (+ (nfix n) (len envs)) (len (stobjs::2darr->rows frames)))
             (equal (len (stobjs::2darr->rows new-frames))
                    (len (stobjs::2darr->rows frames)))))


  (fty::deffixcong nat-equiv equal (aig-envs-to-aignet-frames-aux n vars env frames) n)

  (verify-guards aig-envs-to-aignet-frames-aux))
  

(define aig-envs-to-aignet-frames (vars envs frames)
  :enabled t
  :prepwork ((local (defthm equal-of-2darr
                      (equal (equal (stobjs::2darr a b) c)
                             (and (stobjs::2darr-p c)
                                  (equal (nfix a) (stobjs::2darr->ncols c))
                                  (equal (acl2::list-fix b) (stobjs::2darr->rows c))))
                      :hints(("Goal" :in-theory (enable stobjs::2darr
                                                        stobjs::2darr-p
                                                        stobjs::2darr->ncols
                                                        stobjs::2darr->rows))))))
  :guard-hints (("goal" :in-theory (enable rows-of-aig-envs-to-aignet-frames-aux)))
  (mbe :logic (non-exec (stobjs::2darr (len vars)
                                       (envs-to-bitarrs vars envs)))
       :exec (b* ((frames (frames-resize-rows 0 frames))
                  (frames (frames-resize-cols (len vars) frames))
                  (frames (frames-resize-rows (len envs) frames)))
               (aig-envs-to-aignet-frames-aux 0 vars envs frames))))



;; (defthm aignet-frames-to-aig-envs-of-aig-envs-to-aignet-frames
;;   (implies (and (member v vars)
;;                 (< (nfix n) (len envs)))
;;            (equal (acl2::aig-env-lookup v (nth n (aignet::aignet-frames-to-aig-envs
;;                                                   (aignet::aig-envs-to-aignet-frames vars envs frames)
;;                                                   vars)))
;;                   (acl2::aig-env-lookup v (nth n envs)))))

;; (local (defthm aig-fsm-run-redef
;;          (equal (aig-fsm-run outputs regs curr-st ins)
;;                 (if (atom ins)
;;                     nil
;;                   (cons (aig-fsm-frame-outs outputs regs curr-st (car ins))
;;                         (aig-fsm-run outputs regs (aig-fsm-frame-nextst regs curr-st (car ins))
;;                                      (cdr ins)))))
;;          :hints ((and stable-under-simplificationp
;;                       (member-equal '(consp ins) clause)
;;                       '(:expand ((aig-fsm-run outputs regs curr-st ins)))))
;;          :rule-classes ((:definition :controller-alist ((aig-fsm-run nil nil nil t))))))



(defthm aig-eval-of-aig-fsm-frame-env-of-bitarr-to-aig-env-of-env-to-bitarr
  (implies (subsetp (aig-vars x) (append vars (alist-keys regs)))
           (equal (aig-eval x (aig-fsm-frame-env regs curr-st
                                                 (aignet-bitarr-to-aig-env vars
                                                                           (env-to-bitarr vars ins))))
                  (aig-eval x (aig-fsm-frame-env regs curr-st ins))))
  :hints(("Goal" :in-theory (enable aig-fsm-frame-env aig-eval acl2::aig-env-lookup))))

(defthm aig-eval-list-of-aig-fsm-frame-env-of-bitarr-to-aig-env-of-env-to-bitarr
  (implies (subsetp (acl2::aiglist-vars x) (append vars (alist-keys regs)))
           (equal (acl2::aig-eval-list x (aig-fsm-frame-env regs curr-st
                                                      (aignet-bitarr-to-aig-env vars
                                                                                (env-to-bitarr vars ins))))
                  (acl2::aig-eval-list x (aig-fsm-frame-env regs curr-st ins))))
  :hints(("Goal" :in-theory (enable acl2::aig-eval-list acl2::aiglist-vars))))

(defthm aig-eval-alist-of-aig-fsm-frame-env-of-bitarr-to-aig-env-of-env-to-bitarr
  (implies (subsetp (acl2::aiglist-vars (alist-vals x)) (append vars (alist-keys regs)))
           (equal (acl2::aig-eval-alist x (aig-fsm-frame-env regs curr-st
                                                      (aignet-bitarr-to-aig-env vars
                                                                                (env-to-bitarr vars ins))))
                  (acl2::aig-eval-alist x (aig-fsm-frame-env regs curr-st ins))))
  :hints(("Goal" :in-theory (enable acl2::aig-eval-alist acl2::aiglist-vars))))

(Defthm aig-fsm-frame-outs-of-bitarr-to-aig-env-of-env-to-bitarr
  (implies (subsetp (acl2::aiglist-vars outputs) (append vars (Alist-keys regs)))
           (equal (aig-fsm-frame-outs outputs regs curr-st
                                      (aignet-bitarr-to-aig-env vars
                                                                (env-to-bitarr vars ins)))
                  (aig-fsm-frame-outs outputs regs curr-st ins)))
  :hints(("Goal" :in-theory (enable aig-fsm-frame-outs))))

(Defthm aig-fsm-frame-nextst-of-bitarr-to-aig-env-of-env-to-bitarr
  (implies (subsetp (acl2::aiglist-vars (alist-vals regs)) (append vars (Alist-keys regs)))
           (equal (aig-fsm-frame-nextst regs curr-st
                                      (aignet-bitarr-to-aig-env vars
                                                                (env-to-bitarr vars ins)))
                  (aig-fsm-frame-nextst regs curr-st ins)))
  :hints(("Goal" :in-theory (enable aig-fsm-frame-nextst))))

(local (defthm aig-fsm-run-of-atom
         (implies (atom ins)
                  (equal (aig-fsm-run outputs regs curr-st ins) nil))
         :hints(("Goal" :in-theory (enable aig-fsm-run)))))

(defthm aig-fsm-run-of-frames-to-envs-of-envs-to-frames
  (implies (and (subsetp (acl2::aiglist-vars outputs)
                         (append vars (alist-keys regs)))
                (subsetp (acl2::aiglist-vars (alist-vals regs))
                         (append vars (alist-keys regs))))
           (equal (aig-fsm-run outputs regs curr-st
                               (aignet-frame-array-to-aig-envs
                                (envs-to-bitarrs vars ins)
                                vars))
                  (aig-fsm-run outputs regs curr-st ins)))
  :hints (("goal" :in-theory (e/d (envs-to-bitarrs
                                     aignet-frame-array-to-aig-envs
                                     (:i aig-fsm-states)))
           :induct (aig-fsm-states regs curr-st ins))))

(defthm aig-fsm-states-of-frames-to-envs-of-envs-to-frames
  (implies (subsetp (acl2::aiglist-vars (alist-vals regs))
                    (append vars (alist-keys regs)))
           (equal (aig-fsm-states regs curr-st
                               (aignet-frame-array-to-aig-envs
                                (envs-to-bitarrs vars ins)
                                vars))
                  (aig-fsm-states regs curr-st ins)))
  :hints (("goal" :in-theory (e/d (envs-to-bitarrs
                                   aignet-frame-array-to-aig-envs
                                   aig-fsm-states))
           :induct (aig-fsm-states regs curr-st ins))))



;; Conversion between AIG envs and AIGNET bitarrs/frames:

;; Env to bitarr: exec: env-update-bitarr
;;               logic: env-to-bitarr

;; Envs to frames: exec: aig-envs-to-aignet-frames
;;                logic: envs-to-bitarrs

;; Bitarr to list of Booleans: bits-to-bools

;; Bitarr to env: aignet-bitarr-to-aig-env

;; Frames to envs: exec: aignet-frames-to-aig-envs
;;                logic: aignet-frame-array-to-aig-envs
