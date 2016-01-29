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
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))

;; Translating from Hons AIGs to aignets.

;; We need a memoization table so that we don't revisit AIG nodes we've already
;; seen.

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
                           acl2::nth-with-large-index)))
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
                    (litp (cdr look))))))

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
               (and (atom (caar varmap))
                    (not (booleanp (caar varmap)))
                    (litp (cdar varmap))
                    (fanin-litp (cdar varmap) aignet)))
           (good-varmap-p (cdr varmap) aignet))))

  (local (in-theory (enable good-varmap-p)))


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
                       (gatesimp natp)
                       strash
                       aignet)
  :returns (mv (lit litp)
               xmemo strash aignet)
  :guard (and (good-varmap-p varmap aignet)
              (xmemo-well-formedp xmemo aignet))
  :verify-guards nil
  (aig-cases
   x
   :true (mv (to-lit 1) xmemo strash aignet)
   :false (mv (to-lit 0) xmemo strash aignet)
   :var (b* ((look (hons-get x varmap)))
          (mv (if look
                  (lit-fix (cdr look))
                ;; For missing variables, produce TRUE to match semantics of
                ;; aig-eval.
                (to-lit 1))
              xmemo strash aignet))
   :inv (b* (((mv lit xmemo strash aignet)
              (aig-to-aignet (car x) xmemo varmap gatesimp strash aignet)))
          (mv (lit-negate lit) xmemo strash aignet))
   :and (b* ((look (hons-get x xmemo))
             ((when look)
              (mv (lit-fix (cdr look)) xmemo strash aignet))
             ((mv lit1 xmemo strash aignet)
              (aig-to-aignet (car x) xmemo varmap gatesimp strash aignet))
             ((when (int= (lit-val lit1) 0))
              (mv (to-lit 0) (hons-acons x (to-lit 0) xmemo) strash aignet))
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
    (implies (not (equal (stype-fix stype) (gate-stype)))
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

  (defthm lookup-in-aignet-eval-to-env
    (implies (hons-assoc-equal x varmap)
             (equal (cdr (hons-assoc-equal x (aignet-eval-to-env varmap in-vals reg-vals aignet)))
                    (= 1 (lit-eval (cdr (hons-assoc-equal x varmap))
                                   in-vals reg-vals aignet))))
    :hints(("Goal"
            :induct (aignet-eval-to-env varmap in-vals reg-vals aignet))))

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
                    :guard (and (natp gatesimp)
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
                    :guard (and (natp gatesimp)
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

  (verify-guards aiglist-to-aignet-aux)
  (verify-guards aiglist-to-aignet)

  (defun aiglist-to-aignet-top (x varmap gatesimp strash aignet)
    (declare (xargs :stobjs (aignet strash)
                    :guard (and (natp gatesimp)
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
    (implies (not (equal (stype-fix stype) (gate-stype)))
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

  (local (in-theory (enable keys-bound)))

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


(defsection make-varmap

  (define make-varmap (vars regp acc aignet)
    (declare (xargs :stobjs aignet))
    :returns (mv varmap new-aignet)
    (if (atom vars)
        (mv acc aignet)
      (b* ((lit (mk-lit (num-nodes aignet) 0))
           (aignet (if regp
                       (aignet-add-reg aignet)
                     (aignet-add-in aignet)))
           (acc (hons-acons (car vars) lit acc)))
        (make-varmap (cdr vars) regp acc aignet)))
    ///

    (local (in-theory (enable make-varmap)))

    (defthm true-listp-make-varmap
      (equal (true-listp (mv-nth 0 (make-varmap vars regp acc aignet)))
             (true-listp acc))
      :rule-classes
      (:rewrite
       (:type-prescription
        :corollary
        (implies (true-listp acc)
                 (true-listp (mv-nth 0 (make-varmap vars regp acc aignet)))))))

    (def-aignet-preservation-thms make-varmap)

    (defthm alistp-make-varmap
      (equal (alistp (mv-nth 0 (make-varmap vars regp acc aignet)))
             (alistp acc)))

    (defthm len-make-varmap
      (equal (len (mv-nth 0 (make-varmap vars regp acc aignet)))
             (+ (len vars) (len acc))))

    (defthm alist-keys-of-make-varmap
      (equal (alist-keys (mv-nth 0 (make-varmap vars regp acc aignet)))
             (revappend vars (alist-keys acc)))
      :hints(("Goal" :in-theory (enable alist-keys))))

    (defun non-bool-atom-listp (x)
      (declare (xargs :guard t))
      (if (atom x)
          t
        (and (atom (car x))
             (not (booleanp (car x)))
             (non-bool-atom-listp (cdr x)))))

    (defthm good-varmap-p-of-make-varmap
      (implies (and (good-varmap-p acc aignet)
                    (non-bool-atom-listp vars))
               (mv-let (acc aignet)
                 (make-varmap vars regp acc aignet)
                 (good-varmap-p acc aignet)))
      :hints(("Goal" :in-theory (enable good-varmap-p))))

    (local (defthm litp-integerp
             (implies (litp lit)
                      (and (integerp lit)
                           (<= 0 lit)))))

    (defun bound-to-regs-in-varmap (names varmap aignet)
      (declare (xargs :stobjs aignet
                      :guard-debug t
                      :guard (good-varmap-p varmap aignet)))
      (if (atom names)
          t
        (and (hons-assoc-equal (car names) varmap)
             (int= (id->type (lit-id (cdr (hons-assoc-equal (car names) varmap)))
                             aignet)
                   (in-type))
             (int= (io-id->regp (lit-id (cdr (hons-assoc-equal (car names) varmap)))
                                aignet)
                   1)
             (bound-to-regs-in-varmap (cdr names) varmap aignet))))

    (local (in-theory (disable litp-integerp)))

    (defthm bound-to-regs-in-varmap-of-aignet-extension
      (implies (and (aignet-extension-binding)
                    (good-varmap-p varmap orig))
               (equal (bound-to-regs-in-varmap names varmap new)
                      (bound-to-regs-in-varmap names varmap orig))))

    (defthm bound-to-regs-in-varmap-preserved-by-varmap-add-reg
      (implies (and (bound-to-regs-in-varmap vars1 acc aignet)
                    (equal (id->type (lit-id lit) aignet) (in-type))
                    (equal (io-id->regp (lit-id lit) aignet) 1))
               (bound-to-regs-in-varmap
                vars1
                (cons (cons v lit) acc)
                aignet)))



    (defthm make-varmap-preserves-inp
      (implies (and (good-varmap-p varmap aignet)
                    (non-bool-atom-listp vars)
                    (hons-assoc-equal x varmap)
                    (equal (id->type (lit-id (cdr (hons-assoc-equal x varmap)))
                                     aignet)
                           (in-type)))
               (mv-let (varmap aignet)
                 (make-varmap vars f varmap aignet)
                 (equal (ctype
                         (stype (car (lookup-id (lit-id (cdr (hons-assoc-equal x varmap)))
                                                aignet))))
                        (in-ctype))))
      :hints(("Goal" :in-theory (enable good-varmap-p))))

    (defthm make-varmap-preserves-regp
      (implies (and (good-varmap-p varmap aignet)
                    (non-bool-atom-listp vars)
                    (hons-assoc-equal x varmap)
                    (equal (io-id->regp (lit-id (cdr (hons-assoc-equal x varmap)))
                                        aignet)
                           1))
               (mv-let (varmap aignet)
                 (make-varmap vars t varmap aignet)
                 (equal (regp
                         (stype (car (lookup-id (lit-id (cdr (hons-assoc-equal x varmap)))
                                                aignet))))
                        1)))
      :hints(("Goal" :in-theory (enable good-varmap-p))))

    (defthm make-varmap-preserves-bound-to-regs
      (implies (and (good-varmap-p varmap aignet)
                    (non-bool-atom-listp vars)
                    (bound-to-regs-in-varmap names varmap aignet))
               (mv-let (varmap aignet)
                 (make-varmap vars t varmap aignet)
                 (bound-to-regs-in-varmap
                  names varmap aignet)))
      :hints(("Goal" :in-theory (enable good-varmap-p))))

    (defthm make-varmap-preserves-lookup
      (implies (hons-assoc-equal x varmap)
               (hons-assoc-equal x (mv-nth 0 (make-varmap vars f varmap aignet)))))

    (defthm make-varmap-bound-to-regs
      (implies (and (good-varmap-p varmap aignet)
                    (non-bool-atom-listp vars))
               (mv-let (varmap aignet)
                 (make-varmap vars t varmap aignet)
                 (bound-to-regs-in-varmap
                  vars varmap aignet)))
      :hints(("Goal" :in-theory (enable good-varmap-p))))

    (defthm num-ins-of-make-varmap
      (equal (stype-count (pi-stype) (mv-nth 1 (make-varmap vars nil acc aignet)))
             (+ (stype-count (pi-stype) aignet)
                (len vars)))
      :hints(("Goal" :in-theory (enable make-varmap))))

    (defthm num-reg-of-make-varmap
      (equal (stype-count :reg (mv-nth 1 (make-varmap vars t acc aignet)))
             (+ (stype-count :reg aignet)
                (len vars)))
      :hints(("Goal" :in-theory (enable make-varmap))))

    (defthm stype-count-of-make-varmap
      (implies (not (equal (stype-fix stype) :pi))
               (equal (stype-count stype (mv-nth 1 (make-varmap vars nil acc aignet)))
                      (stype-count stype aignet)))
      :hints(("Goal" :in-theory (enable make-varmap))))

    (defthm stype-count-of-make-varmap-regp
      (implies (not (equal (stype-fix stype) :reg))
               (equal (stype-count stype (mv-nth 1 (make-varmap vars t acc aignet)))
                      (stype-count stype aignet)))
      :hints(("Goal" :in-theory (enable make-varmap))))))


(local (include-book "centaur/misc/alist-equiv" :dir :system))


(local
 (defsection set-difference


   (defthm hons-sd1-is-set-difference
     (equal (acl2::hons-sd1 a b)
            (set-difference-equal a (alist-keys b)))
     :hints(("Goal" :in-theory (enable alist-keys set-difference-equal))))

   (defthm set-difference-of-cons-non-member
     (implies (not (member k x))
              (equal (set-difference$ x (cons k y))
                     (set-difference$ x y)))
     :hints(("Goal" :in-theory (enable set-difference$))))))

(defsection add-to-varmap

  (define add-to-varmap (vars regp acc aignet)
    (declare (xargs :stobjs aignet))
    :returns (mv new-varmap new-aignet)
    (if (atom vars)
        (mv acc aignet)
      (if (hons-get (car vars) acc)
          (add-to-varmap (cdr vars) regp acc aignet)
        (b* ((lit (mk-lit (num-nodes aignet) 0))
             (aignet (if regp
                         (aignet-add-reg aignet)
                       (aignet-add-in aignet)))
             (acc (hons-acons (car vars) lit acc)))
          (add-to-varmap
           (cdr vars) regp acc aignet))))
    ///

    (local (in-theory (enable add-to-varmap)))

    (def-aignet-preservation-thms add-to-varmap)

    (defthm true-listp-add-to-varmap
      (equal (true-listp (mv-nth 0 (add-to-varmap vars regp acc aignet)))
             (true-listp acc))
      :rule-classes (:rewrite
                     (:type-prescription
                      :corollary
                      (implies (true-listp acc)
                               (true-listp (mv-nth 0 (add-to-varmap vars regp acc aignet)))))))

    (defthm alistp-add-to-varmap
      (equal (alistp (mv-nth 0 (add-to-varmap vars regp acc aignet)))
             (alistp acc)))

    (defthm alist-keys-of-add-to-varmap
      (implies (no-duplicatesp vars)
               (equal (alist-keys (mv-nth 0 (add-to-varmap vars regp acc aignet)))
                      (revappend (acl2::hons-sd1 vars acc) (alist-keys acc))))
      :hints(("Goal" :in-theory (enable set-difference$
                                        alist-keys)
              :induct (add-to-varmap vars regp acc aignet))))

    (local (defthmd len-alist-keys
             (implies (alistp x)
                      (equal (len (alist-keys x))
                             (len x)))
             :hints(("Goal" :in-theory (enable alist-keys)))))




    (defthm len-add-to-varmap
      (implies (and (no-duplicatesp vars)
                    (alistp acc)) ;; shouldn't be necessary, just a shortcut
               (equal (len (mv-nth 0 (add-to-varmap vars regp acc aignet)))
                      (+ (len (acl2::hons-sd1 vars acc))
                         (len acc))))
      :hints (("goal" :use ((:instance len-alist-keys
                             (x (mv-nth 0 (add-to-varmap vars regp acc aignet))))
                            (:instance len-alist-keys
                             (x acc))))))

    (defthm good-varmap-p-of-add-to-varmap
      (implies (and (good-varmap-p acc aignet)
                    (non-bool-atom-listp vars))
               (mv-let (acc aignet)
                 (add-to-varmap vars regp acc aignet)
                 (good-varmap-p acc aignet)))
      :hints(("Goal" :in-theory (enable good-varmap-p))))

    (std::defret num-outs-of-add-to-varmap
      (equal (stype-count :po new-aignet)
             (stype-count :po aignet)))

    (std::defret num-ins-of-add-to-varmap
      (equal (stype-count :pi new-aignet)
             (if regp
                 (stype-count :pi aignet)
               (+ (stype-count :pi aignet)
                  (- (len new-varmap)
                     (len acc))))))))



(defsection first-n-rev-alist-keys
  (defund first-n-rev-alist-keys (n alist acc)
    (declare (xargs :guard (and (natp n)
                                (alistp alist)
                                (<= n (len alist)))
                    :measure (nfix n)))
    (if (zp n)
        acc
      (first-n-rev-alist-keys
       (1- (lnfix n)) (cdr alist)
       (cons (caar alist) acc))))

  (local (in-theory (enable first-n-rev-alist-keys
                            set-difference$)))
  (local (include-book "centaur/misc/lists" :dir :system))
  (local (in-theory (disable acl2::take-redefinition)))

  (defthm first-n-rev-def
    (implies (and (alistp alist)
                  (<= (nfix n) (len alist)))
             (equal (first-n-rev-alist-keys n alist acc)
                    (revappend (take n (alist-keys alist)) acc)))
    :hints(("Goal" :in-theory (enable alist-keys))))

  (local (defthm take-of-append-len-of-first
           (implies (and (equal n (len a))
                         (true-listp a))
                    (equal (take n (append a b))
                           a))
           :hints(("Goal" :in-theory (e/d (alist-keys))))))


  (defthm first-n-rev-is-hons-sd1
    (b* (((mv varmap &)
          (make-varmap vars1 regp1 nil aignet1))
         ((mv varmap &) (add-to-varmap vars2 regp2 varmap aignet2))
         (nins (- (len varmap) (len vars1))))
      (implies (no-duplicatesp vars2)
               (equal (first-n-rev-alist-keys nins varmap nil)
                      (set-difference$ vars2 vars1))))
    :hints(("Goal" :in-theory (disable append acl2::rev))))

  (in-theory (disable first-n-rev-def))

  (defthm true-listp-first-n-rev-alist-key
    (equal (true-listp (first-n-rev-alist-keys n alist acc))
           (true-listp acc))))



(defsection aig-fsm-prepare-aignet/varmap
  (local (in-theory (enable length)))

  (define aig-fsm-prepare-aignet/varmap (reg-alist out-list max-nodes aignet)
    (declare (xargs :stobjs aignet
                    :guard (posp max-nodes)
                    :guard-debug t))
    :returns (mv varmap input-vars reg-vars new-aignet)
    (b* ((reg-aigs (alist-vals reg-alist))
         (all-vars (acl2::aig-vars-unordered-list
                    (cons reg-aigs out-list)))
         (reg-vars (alist-keys reg-alist))
         (nregs    (len reg-vars))
         (- (cw "regs: ~x0~%" nregs))
         (nouts (len out-list))
         (nins (nfix (- (len all-vars) nregs)))
         (max-nodes (mbe :logic (if (posp max-nodes)
                                    max-nodes
                                  1000)
                         :exec max-nodes))
         (aignet (aignet-init nouts nregs nins max-nodes aignet))
; (reg-lits (lits-of-type 0 nregs (reg-type)))
; (varmap    (make-fast-alist (pairlis$ reg-vars reg-lits)))
         ((mv varmap aignet) (make-varmap reg-vars t nil aignet))
; (input-vars (acl2::hons-sd1 all-vars varmap))
; (nins     (length input-vars))
; (- (cw "ins: ~x0~%" nins))
; (inp-lits (lits-of-type 0 nins (input-type)))
; (varmap    (acl2::make-fal (pairlis$ input-vars inp-lits) varmap))
         ((mv varmap aignet)   (add-to-varmap all-vars nil varmap aignet))
         (nins     (- (length varmap) nregs))
         (input-vars (first-n-rev-alist-keys nins varmap nil))
         (- (cw "ins: ~x0~%" nins)))
      (mv varmap input-vars reg-vars aignet))
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

    (defthm aignet-nodes-ok-of-aig-fsm-prepare-aignet/varmap
      (aignet-nodes-ok (mv-nth 3 (aig-fsm-prepare-aignet/varmap
                                  reg-alist out-list max-nodes aignet))))

    (std::defret num-outs-of-aig-fsm-prepare-aignet/varmap
      (equal (stype-count :po new-aignet) 0))

    (defthm len-first-n-rev-alist-keys
      (equal (len (first-n-rev-alist-keys n x acc))
             (+ (nfix n) (len acc)))
      :hints(("Goal" :in-theory (enable first-n-rev-alist-keys))))

    (std::defret num-ins-of-aig-fsm-prepare-aignet/varmap
      (equal (stype-count :pi new-aignet)
             (len input-vars)))))


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





(defsection good-varmap-p-of-aig-fsm-prepare-aignet/varmap
  (local (in-theory (enable good-varmap-p)))
  (local (include-book "arithmetic/top-with-meta" :dir :system))


  (defthm non-bool-atom-listp-of-accumulate-aig-vars
    (equal (non-bool-atom-listp
            (mv-nth 1 (acl2::accumulate-aig-vars x nodetable acc)))
           (non-bool-atom-listp acc)))

  (defthm non-bool-atom-listp-of-aig-vars-unordered
    (non-bool-atom-listp (acl2::aig-vars-unordered x))
    :hints(("Goal" :in-theory (enable acl2::aig-vars-unordered))))


  (defthm non-bool-atom-listp-of-set-difference
    (implies (non-bool-atom-listp x)
             (non-bool-atom-listp (set-difference$ x y)))
    :hints(("Goal" :in-theory (enable set-difference$))))

  ;; (defthm good-varmap-p-of-make-varmap
  ;;   (implies (and (non-bool-atom-listp vars)
  ;;                 (<= (+ (nfix start) (len vars))
  ;;                     (nfix (nth *num-regs* aignet))))
  ;;            (equal (good-varmap-p (make-varmap start vars (reg-type) acc) aignet)
  ;;                   (good-varmap-p acc aignet)))
  ;;   :hints(("Goal" :in-theory (enable make-varmap
  ;;                                     aignet-id-in-bounds
  ;;                                     id-in-bounds)
  ;;           :induct (make-varmap start vars (reg-type) acc))))


  ;; (defthm good-varmap-p-of-add-to-varmap
  ;;   (implies (and (non-bool-atom-listp vars)
  ;;                 (no-duplicatesp vars)
  ;;                 (<= (+ (nfix start) (len (set-difference$ vars (alist-keys acc))))
  ;;                     (nfix (nth *num-inputs* aignet))))
  ;;            (equal (good-varmap-p (add-to-varmap start vars (input-type) acc) aignet)
  ;;                   (good-varmap-p acc aignet)))
  ;;   :hints(("Goal" :in-theory (enable add-to-varmap
  ;;                                     set-difference$
  ;;                                     aignet-id-in-bounds
  ;;                                     id-in-bounds)
  ;;           :induct (add-to-varmap start vars (input-type) acc))))


  ;; (defthm good-varmap-p-of-make-fal
  ;;   (implies (and (good-varmap-p a aignet)
  ;;                 (good-varmap-p b aignet))
  ;;            (good-varmap-p (acl2::make-fal a b) aignet)))

  ;; (defthm good-varmap-p-of-increase
  ;;   (implies (and (good-varmap-p varmap aignet)
  ;;                 (<= (nfix (nth *num-inputs* aignet))
  ;;                     (nfix (nth *num-inputs* aignet2)))
  ;;                 (<= (nfix (nth *num-regs* aignet))
  ;;                     (nfix (nth *num-regs* aignet2))))
  ;;            (good-varmap-p varmap aignet2))
  ;;   :hints(("Goal" :in-theory (enable good-varmap-p
  ;;                                     aignet-id-in-bounds
  ;;                                     id-in-bounds))))

  ;; (local (defun tmpind (n invars)
  ;;          (if (atom invars)
  ;;              n
  ;;            (tmpind (+ 1 (nfix n)) (cdr invars)))))

  ;; (local (defthmd good-varmap-p-of-pairlis-inputs1
  ;;          (implies (and (non-bool-atom-listp invars)
  ;;                        (<= (+ (nfix n) (len invars))
  ;;                            (nfix (nth *num-inputs* aignet))))
  ;;                   (good-varmap-p (pairlis$ invars
  ;;                                            (lits-of-type n (+ (nfix n) (len invars)) (input-type)))
  ;;                                  aignet))
  ;;          :hints (("goal" :induct (tmpind n invars)
  ;;                   :in-theory (enable pairlis$ id-in-bounds aignet-id-in-bounds)
  ;;                   :expand ((:free (max type) (lits-of-type n max type)))))))

  ;; (defthm good-varmap-p-of-pairlis-inputs
  ;;   (implies (and (non-bool-atom-listp invars)
  ;;                 (<= (len invars) (nfix (nth *num-inputs* aignet))))
  ;;            (good-varmap-p
  ;;             (pairlis$ invars (lits-of-type 0 (len invars) (input-type)))
  ;;             aignet))
  ;;   :hints (("goal" :use ((:instance good-varmap-p-of-pairlis-inputs1
  ;;                          (n 0))))))

  ;; (local (defthmd good-varmap-p-of-pairlis-regs1
  ;;          (implies (and (non-bool-atom-listp invars)
  ;;                        (<= (+ (nfix n) (len invars))
  ;;                            (nfix (nth *num-regs* aignet))))
  ;;                   (good-varmap-p (pairlis$ invars
  ;;                                            (lits-of-type n (+ (nfix n) (len invars)) (reg-type)))
  ;;                                  aignet))
  ;;          :hints (("goal" :induct (tmpind n invars)
  ;;                   :in-theory (enable pairlis$ id-in-bounds aignet-id-in-bounds)
  ;;                   :expand ((:free (max type) (lits-of-type n max type)))))))

  ;; (defthm good-varmap-p-of-pairlis-regs
  ;;   (implies (and (non-bool-atom-listp invars)
  ;;                 (<= (len invars) (nfix (nth *num-regs* aignet))))
  ;;            (good-varmap-p
  ;;             (pairlis$ invars (lits-of-type 0 (len invars) (reg-type)))
  ;;             aignet))
  ;;   :hints (("goal" :use ((:instance good-varmap-p-of-pairlis-regs1
  ;;                          (n 0))))))

  (local (in-theory (disable aignet-init)))

  (defthm good-varmap-p-of-aig-fsm-prepare-aignet/varmap
    (implies (non-bool-atom-listp (alist-keys reg-alist))
             (b* (((mv varmap & & aignet)
                   (aig-fsm-prepare-aignet/varmap
                    reg-alist out-lits max-gates aignet)))
               (good-varmap-p varmap aignet)))
    :hints(("Goal" :in-theory (e/d* (aig-fsm-prepare-aignet/varmap)
                                    (aig-vars aignet-init))))))



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

  (define aig-fsm-set-nxsts (reg-alist reg-lits varmap aignet)
    (declare (xargs :stobjs aignet
                    :guard (and (lit-listp reg-lits)
                                (aignet-lit-listp reg-lits aignet)
                                (equal (len reg-lits) (len (alist-keys
                                                            reg-alist)))
                                (good-varmap-p varmap aignet)
                                (bound-to-regs-in-varmap
                                 (alist-keys reg-alist) varmap aignet))
                    :guard-hints (("goal" :expand ((aignet-lit-listp reg-lits
                                                                     aignet)
                                                   (lit-listp reg-lits)
                                                   (alist-keys reg-alist))))))
    :returns (mv new-varmap new-aignet)
    (b* (((when (atom reg-alist)) (mv varmap aignet))
         ((when (atom (car reg-alist)))
          (aig-fsm-set-nxsts (cdr reg-alist) reg-lits varmap aignet))
         ((when (or (consp (caar reg-alist))
                    (booleanp (caar reg-alist))))
          (aig-fsm-set-nxsts (cdr reg-alist) (cdr reg-lits) varmap aignet))
         (regname (caar reg-alist))
         (fanin (car reg-lits))
         (rolook (hons-get regname varmap))
         ((mv ro-lit varmap aignet)
          (if rolook
              (mv (cdr rolook) varmap aignet)
            (b* ((ro-lit (mk-lit (num-nodes aignet) 0))
                 (aignet (aignet-add-reg aignet))
                 (varmap (hons-acons regname ro-lit varmap)))
              (mv ro-lit varmap aignet))))
         (ro-id (lit-id ro-lit))
         (regp (int= 1 (io-id->regp ro-id aignet)))
         (- (and (not regp) (cw "~x0 mapping not a register output~%"
                                regname)))
         (ro-unconnected (and regp (int= ro-id
                                         (regnum->id (io-id->ionum ro-id aignet) aignet))))
         (aignet (if ro-unconnected
                     (aignet-set-nxst fanin ro-id aignet)
                   (prog2$ (cw "Failed to add register input for ~x0~%" regname)
                           aignet))))
      (aig-fsm-set-nxsts (cdr reg-alist) (cdr reg-lits) varmap aignet))
    ///

    (def-aignet-preservation-thms aig-fsm-set-nxsts)


    (defthm good-varmap-p-of-aig-fsm-set-nxsts
      (implies (and (aignet-lit-listp reg-lits aignet)
                    (equal (len reg-lits) (len (alist-keys reg-alist)))
                    (good-varmap-p varmap aignet)
                    (bound-to-regs-in-varmap (alist-keys reg-alist) varmap aignet))
               (mv-let (varmap aignet)
                 (aig-fsm-set-nxsts reg-alist reg-lits varmap aignet)
                 (good-varmap-p varmap aignet)))
      :hints(("Goal" :in-theory (enable aig-fsm-set-nxsts good-varmap-p)
              :induct (aig-fsm-set-nxsts reg-alist reg-lits varmap aignet))))

    (std::defret num-outs-of-aig-fsm-set-nxsts
      (equal (stype-count :po new-aignet)
             (stype-count :po aignet)))

    (std::defret num-ins-of-aig-fsm-set-nxsts
      (equal (stype-count :pi new-aignet)
             (stype-count :pi aignet))))


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

    (std::defret num-ins-of-aig-fsm-add-outs
      (equal (stype-count :pi new-aignet)
             (stype-count :pi aignet))
      :hints (("goal" :induct t :do-not-induct t))))


  (defthm add-to-varmap-preserves-lookup
    (implies (hons-assoc-equal x varmap)
             (let ((varmap1 (mv-nth 0 (add-to-varmap vars f varmap aignet))))
               (equal (cdr (hons-assoc-equal x varmap1))
                      (cdr (hons-assoc-equal x varmap)))))
    :hints(("Goal" :in-theory (enable add-to-varmap))))

  ;; (defthm aignet-add-in-preserves-bound-to-regs
  ;;   (implies (and (bound-to-regs-in-varmap names varmap aignet)
  ;;                 (good-varmap-p varmap aignet))
  ;;            (bound-to-regs-in-varmap names varmap (mv-nth 1 (aignet-add-in aignet)))))

  (defthm bound-to-regs-in-varmap-preserved-by-varmap-add-other
    (implies (and (bound-to-regs-in-varmap vars1 acc aignet)
                  (not (hons-assoc-equal v acc)))
             (bound-to-regs-in-varmap
              vars1
              (cons (cons v lit) acc)
              aignet)))

  (defthm add-to-varmap-preserves-bound-to-regs
    (implies (and (bound-to-regs-in-varmap names varmap aignet)
                  (good-varmap-p varmap aignet)
                  (non-bool-atom-listp vars))
             (mv-let (varmap aignet)
               (add-to-varmap vars f varmap aignet)
               (bound-to-regs-in-varmap names varmap aignet)))
    :hints(("Goal" :in-theory (enable add-to-varmap good-varmap-p))))

  (defthm bound-to-regs-in-varmap-of-prepare-aignet/varmap
    (implies (non-bool-atom-listp (alist-keys reg-alist))
             (bound-to-regs-in-varmap
              (alist-keys reg-alist)
              (mv-nth 0 (aig-fsm-prepare-aignet/varmap reg-alist out-list max-nodes aignet))
              (mv-nth 3 (aig-fsm-prepare-aignet/varmap reg-alist out-list max-nodes aignet))))
    :hints(("Goal" :in-theory (enable aig-fsm-prepare-aignet/varmap)
            :do-not-induct t)))

  (defthm bound-to-regs-in-varmap-of-aiglist-to-aignet
    (implies (and (bound-to-regs-in-varmap names varmap aignet)
                  (good-varmap-p varmap aignet))
             (bound-to-regs-in-varmap
              names varmap
              (mv-nth 3 (aiglist-to-aignet aigs xmemo varmap gatesimp strash aignet)))))

  (defthm non-bool-atom-listp-keys-of-hons-shrink-alist
    (implies (and (non-bool-atom-listp (alist-keys acc))
                  (non-bool-atom-listp (alist-keys a)))
             (non-bool-atom-listp
              (alist-keys (hons-shrink-alist a acc)))))

  (define aig-fsm-to-aignet (reg-alist out-list max-nodes gatesimp aignet)
    (declare (xargs :stobjs aignet
                    :guard (and (posp max-nodes)
                                (natp gatesimp)
                                (non-bool-atom-listp (alist-keys reg-alist)))
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
         (reg-alist (fast-alist-free (hons-shrink-alist reg-alist nil)))
         (reg-aigs (alist-vals reg-alist))
         ((mv varmap invars regvars aignet)
          (aig-fsm-prepare-aignet/varmap reg-alist out-list max-nodes aignet))
         (strash    (if (gatesimp-hashp gatesimp)
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
         ((mv varmap aignet) (aig-fsm-set-nxsts reg-alist reg-lits varmap aignet))
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

    (defthm aignet-nodes-ok-of-aig-fsm-to-aignet
      (implies (non-bool-atom-listp (alist-keys regs))
               (aignet-nodes-ok
                (mv-nth 0 (aig-fsm-to-aignet regs outs max-gates gatesimp
                                             aignet)))))

    (defthm true-listp-aig-fsm-to-aignet-invars
      (true-listp (mv-nth 2 (aig-fsm-to-aignet regs outs max-gates gatesimp aignet)))
      :rule-classes (:Rewrite :type-prescription))

    (defthm true-listp-aig-fsm-to-aignet-regvars
      (true-listp (mv-nth 3 (aig-fsm-to-aignet regs outs max-gates gatesimp aignet)))
      :rule-classes (:Rewrite :type-prescription))

    ;; (local (include-book "arithmetic/top-with-meta" :dir :system))


    ;; This correctness condition isn't quite right for aignet, at least the way
    ;; we've set it up here.  Basically, if there are duplicated keys in the reg
    ;; alist, we don't add as many regins as there are keys.  We do take the
    ;; non-shadowed ones in the alist.

    ;; (defthm aig-fsm-to-aignet-correct
    ;;   (b* (((mv aignet varmap)
    ;;         (aig-fsm-to-aignet reg-alist out-list max-gates gatesimp aignet))
    ;;        (env (aignet-eval-to-env in-vals reg-vals (reverse-varmap varmap))))
    ;;     (implies (non-bool-atom-listp (alist-keys reg-alist))
    ;;              (and (equal (lit-eval-list (outs aignet) in-vals reg-vals aignet)
    ;;                          (acl2::aig-eval-list out-list env))
    ;;                   (equal (lit-eval-list (regs aignet) in-vals reg-vals aignet)
    ;;                          (acl2::aig-eval-list (alist-vals reg-alist) env)))))
    ;; :hints(("Goal" :in-theory (e/d* ((:ruleset aignet-frame-thms)
    ;;                                  num-regs-of-aig-fsm-prepare-aignet/varmap
    ;;                                  num-outs-of-aig-fsm-prepare-aignet/varmap
    ;;                                  outs-of-aig-fsm-prepare-aignet/varmap
    ;;                                  regs-of-aig-fsm-prepare-aignet/varmap
    ;;                                  outs-aux-meaning
    ;;                                  regs-aux-meaning)
    ;;                                 (aiglist-to-aignet
    ;;                                  lit-eval-list
    ;;                                  acl2::aig-eval-list
    ;;                                  aignet-eval-to-env
    ;;                                  reverse-varmap
    ;;                                  aig-vars
    ;;                                  lits-of-type
    ;;                                  acl2::hons-sd1
    ;;                                  len
    ;;                                  pairlis$
    ;;                                  hons-assoc-equal
    ;;                                  acl2::make-fal
    ;;                                  outs-aux regs-aux
    ;;                                  set-outs-aux
    ;;                                  set-regs-aux
    ;;                                  set-regs-logic
    ;;                                  set-outs-logic
    ;;                                  update-lit-list
    ;;                                  set::double-containment
    ;;                                  resize-list))
    ;;         :do-not-induct t)))

    (defthm good-varmap-p-of-aig-fsm-to-aignet
      (implies (non-bool-atom-listp (alist-keys regs))
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
             (len invars)))))
