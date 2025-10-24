; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "FGL")

(include-book "bvar-db-bfrlist")
(include-book "pathcond")
(include-book "contexts")


;; (defines fgl-object-boundedp
;;   (define fgl-object-boundedp (x &optional ((bfrstate bfrstate-p) 'bfrstate))
;;     :measure (fgl-object-count x)
;;     :verify-guards nil
;;     (mbe :logic (and (fgl-object-p x)
;;                      (fgl-object-case x
;;                        :g-concrete t
;;                        :g-boolean (bfr-p x.bool)
;;                        :g-integer (bfr-listp x.bits)
;;                        :g-ite (and (fgl-object-boundedp x.test)
;;                                    (fgl-object-boundedp x.then)
;;                                    (fgl-object-boundedp x.else))
;;                        :g-apply (fgl-objectlist-boundedp x.args)
;;                        :g-var t
;;                        :g-cons (and (fgl-object-boundedp x.car)
;;                                     (fgl-object-boundedp x.cdr))
;;                        :g-map (fgl-object-alist-boundedp x.alist)))
;;          :exec (and (fgl-object-p x)
;;                     (fgl-object-boundedp-aux x))))
;;   (define fgl-objectlist-boundedp (x
;;                                &optional ((bfrstate bfrstate-p) 'bfrstate))
;;     :measure (fgl-objectlist-count x)
;;     (mbe :logic (and (fgl-objectlist-p x)
;;                      (if (atom x)
;;                          t
;;                        (and (fgl-object-boundedp (car x))
;;                             (fgl-objectlist-boundedp (cdr x)))))
;;          :exec (and (fgl-objectlist-p x)
;;                     (fgl-objectlist-boundedp-aux x))))
;;   (define fgl-object-alist-boundedp (x
;;                                &optional ((bfrstate bfrstate-p) 'bfrstate))
;;     :measure (fgl-object-alist-count x)
;;     (mbe :logic (and (fgl-object-alist-p x)
;;                      (if (atom x)
;;                          t
;;                        (and (fgl-object-boundedp (cdar x))
;;                             (fgl-object-alist-boundedp (cdr x)))))
;;          :exec (and (fgl-object-alist-p x)
;;                     (fgl-object-alist-boundedp-aux x))))
;;   ///
;;   (local
;;    (defthm-fgl-object-boundedp-flag
;;      (defthm fgl-object-boundedp-aux-elim
;;        (implies (fgl-object-p x)
;;                 (equal (fgl-object-boundedp-aux x)
;;                        (fgl-object-boundedp x)))
;;        :hints ('(:expand ((fgl-object-boundedp-aux x)
;;                           (fgl-object-boundedp x))))
;;        :flag fgl-object-boundedp)
;;      (defthm fgl-objectlist-boundedp-aux-elim
;;        (implies (fgl-objectlist-p x)
;;                 (equal (fgl-objectlist-boundedp-aux x)
;;                        (fgl-objectlist-boundedp x)))
;;        :hints ('(:expand ((fgl-objectlist-boundedp-aux x)
;;                           (fgl-objectlist-boundedp-aux nil)
;;                           (fgl-objectlist-boundedp x)
;;                           (fgl-objectlist-boundedp nil))))
;;        :flag fgl-objectlist-boundedp)
     
;;      (defthm fgl-object-alist-boundedp-aux-elim
;;        (implies (fgl-object-alist-p x)
;;                 (equal (fgl-object-alist-boundedp-aux x)
;;                        (fgl-object-alist-boundedp x)))
;;        :hints ('(:expand ((fgl-object-alist-boundedp-aux x)
;;                           (fgl-object-alist-boundedp-aux nil)
;;                           (fgl-object-alist-boundedp x)
;;                           (fgl-object-alist-boundedp nil))))
;;        :flag fgl-object-alist-boundedp)))
  
;;   (verify-guards fgl-object-boundedp-fn)

;;   (defthm fgl-object-p-when-fgl-object-boundedp
;;     (implies (fgl-object-boundedp x)
;;              (fgl-object-p x))
;;     :rule-classes (:rewrite :forward-chaining))

;;   (defthm fgl-objectlist-p-when-fgl-objectlist-boundedp
;;     (implies (fgl-objectlist-boundedp x)
;;              (fgl-objectlist-p x))
;;     :rule-classes (:rewrite :forward-chaining))

;;   (defthm fgl-object-boundedp-when-g-boolean
;;     (implies (and (fgl-object-case x :g-boolean)
;;                   (fgl-object-boundedp x))
;;              (bfr-p (g-boolean->bool x)))
;;     :hints (("goal" :expand ((fgl-object-boundedp x)))))

;;   (defthm fgl-object-boundedp-when-g-integer
;;     (implies (and (fgl-object-case x :g-integer)
;;                   (fgl-object-boundedp x))
;;              (bfr-listp (g-integer->bits x)))
;;     :hints (("goal" :expand ((fgl-object-boundedp x)))))

;;   (defthm fgl-object-boundedp-when-g-ite
;;     (implies (and (fgl-object-case x :g-ite)
;;                   (fgl-object-boundedp x))
;;              (and (fgl-object-boundedp (g-ite->test x))
;;                   (fgl-object-boundedp (g-ite->then x))
;;                   (fgl-object-boundedp (g-ite->else x))))
;;     :hints (("goal" :expand ((fgl-object-boundedp x)))))

;;   (defthm fgl-object-boundedp-when-g-apply
;;     (implies (and (fgl-object-case x :g-apply)
;;                   (fgl-object-boundedp x))
;;              (fgl-objectlist-boundedp (g-apply->args x)))
;;     :hints (("goal" :expand ((fgl-object-boundedp x)))))

;;   (defthm fgl-object-boundedp-when-g-cons
;;     (implies (and (fgl-object-case x :g-cons)
;;                   (fgl-object-boundedp x))
;;              (and (fgl-object-boundedp (g-cons->car x))
;;                   (fgl-object-boundedp (g-cons->cdr x))))
;;     :hints (("goal" :expand ((fgl-object-boundedp x)))))

;;   (defthm fgl-object-boundedp-when-g-map
;;     (implies (and (fgl-object-case x :g-map)
;;                   (fgl-object-boundedp x))
;;              (fgl-object-alist-boundedp (g-map->alist x)))
;;     :hints (("goal" :expand ((fgl-object-boundedp x)))))

;;   (defthm fgl-objectlist-boundedp-implies-car/cdr
;;     (implies (fgl-objectlist-boundedp x)
;;              (and (fgl-object-boundedp (car x))
;;                   (fgl-objectlist-boundedp (cdr x))))
;;     :hints (("goal" :expand ((fgl-objectlist-boundedp x)
;;                              (fgl-object-boundedp nil)
;;                              (fgl-objectlist-boundedp nil)))))

;;   (defthm fgl-object-alist-boundedp-implies-cdar/cdr
;;     (implies (fgl-object-alist-boundedp x)
;;              (and (fgl-object-boundedp (cdar x))
;;                   (fgl-object-alist-boundedp (cdr x))))
;;     :hints (("goal" :expand ((fgl-object-alist-boundedp x)
;;                              (fgl-object-boundedp nil)
;;                              (fgl-object-alist-boundedp nil)))))

;;   (defthm fgl-objectlist-boundedp-of-cons
;;     (implies (and (fgl-object-boundedp x)
;;                   (fgl-objectlist-boundedp y))
;;              (fgl-objectlist-boundedp (cons x y)))
;;     :hints (("goal" :expand ((fgl-objectlist-boundedp (cons x y))))))

;;   (defthm fgl-objectlist-boundedp-of-nil
;;     (fgl-objectlist-boundedp nil)
;;     :hints (("goal" :expand ((fgl-objectlist-boundedp nil)))))

;;   (defthm fgl-object-boundedp-of-g-concrete
;;     (fgl-object-boundedp (g-concrete val))
;;     :hints (("goal" :expand ((fgl-object-boundedp (g-concrete val))))))

;;   (defthm fgl-object-boundedp-of-g-boolean
;;     (implies (bfr-p bool)
;;              (fgl-object-boundedp (g-boolean bool)))
;;     :hints (("goal" :expand ((fgl-object-boundedp (g-boolean bool))))))

;;   (defthm fgl-object-boundedp-of-g-integer
;;     (implies (bfr-listp bits)
;;              (fgl-object-boundedp (g-integer bits)))
;;     :hints (("goal" :expand ((fgl-object-boundedp (g-integer bits))))))

;;   (defthm fgl-object-boundedp-of-g-ite
;;     (implies (and (fgl-object-boundedp test)
;;                   (fgl-object-boundedp then)
;;                   (fgl-object-boundedp else))
;;              (fgl-object-boundedp (g-ite test then else)))
;;     :hints (("goal" :expand ((fgl-object-boundedp (g-ite test then else))))))

;;   (defthm fgl-object-boundedp-of-g-apply
;;     (implies (and (fgl-objectlist-boundedp args))
;;              (fgl-object-boundedp (g-apply fn args)))
;;     :hints (("goal" :expand ((fgl-object-boundedp (g-apply fn args))))))

;;   (defthm fgl-object-boundedp-of-g-var
;;     (fgl-object-boundedp (g-var name))
;;     :hints (("goal" :expand ((fgl-object-boundedp (g-var name))))))

;;   (defthm fgl-object-boundedp-of-g-cons
;;     (implies (and (fgl-object-boundedp car)
;;                   (fgl-object-boundedp cdr))
;;              (fgl-object-boundedp (g-cons car cdr)))
;;     :hints (("goal" :expand ((fgl-object-boundedp (g-cons car cdr))))))

;;   (defthm fgl-object-boundedp-of-g-map
;;     (implies (fgl-object-alist-boundedp alist)
;;              (fgl-object-boundedp (g-map tag alist)))
;;     :hints (("goal" :expand ((fgl-object-boundedp (g-map tag alist))
;;                              (fgl-object-alist-boundedp alist)
;;                              (fgl-object-alist-boundedp (fgl-object-alist-fix alist))))))

;;   (fty::deffixequiv-mutual fgl-object-boundedp
;;     :hints ((acl2::use-termhint
;;              `(:expand ((fgl-object-boundedp-aux ,(acl2::hq x) ,(acl2::hq bfrstate))
;;                         (fgl-object-boundedp-aux ,(acl2::hq (fgl-object-fix x)) ,(acl2::hq bfrstate))
;;                         (fgl-object-boundedp-aux ,(acl2::hq x) ,(acl2::hq (bfrstate-fix bfrstate)))
;;                         (fgl-objectlist-boundedp-aux ,(acl2::hq x) ,(acl2::hq bfrstate))
;;                         (fgl-objectlist-boundedp-aux ,(acl2::hq (fgl-objectlist-fix x)) ,(acl2::hq bfrstate))
;;                         (fgl-objectlist-boundedp-aux ,(acl2::hq x) ,(acl2::hq (bfrstate-fix bfrstate))))))))

;;   (defthm-fgl-object-boundedp-flag
;;     (defthm fgl-object-boundedp-when-bfrstate>=
;;       (implies (and (bfrstate>= new old)
;;                     (fgl-object-boundedp x old))
;;                (fgl-object-boundedp x new))
;;       :hints ('(:expand ((:free (bfrstate) (fgl-object-boundedp x)))))
;;       :flag fgl-object-boundedp)
;;     (defthm fgl-objectlist-boundedp-when-bfrstate>=
;;       (implies (and (bfrstate>= new old)
;;                     (fgl-objectlist-boundedp x old))
;;                (fgl-objectlist-boundedp x new))
;;       :hints ('(:expand ((:free (bfrstate) (fgl-objectlist-boundedp x)))))
;;       :flag fgl-objectlist-boundedp)
;;     (defthm fgl-object-alist-boundedp-when-bfrstate>=
;;       (implies (and (bfrstate>= new old)
;;                     (fgl-object-alist-boundedp x old))
;;                (fgl-object-alist-boundedp x new))
;;       :hints ('(:expand ((:free (bfrstate) (fgl-object-alist-boundedp x)))))
;;       :flag fgl-object-alist-boundedp)
;;     :hints (("goal" :induct (fgl-object-boundedp-flag flag x old)))))


#!aignet
(define id-max-pi-dep ((id natp) (aignet))
  :measure (nfix id)
  :guard (id-existsp id aignet)
  :returns (pi-bound natp :rule-classes :type-prescription)
  (b* (((unless (mbt (id-existsp id aignet)))
        0)
       (type (id->type id aignet))
       (regp (id->regp id aignet)))
    (aignet-case
      type regp
      :gate (max (id-max-pi-dep (lit->var (gate-id->fanin0 id aignet)) aignet)
                 (id-max-pi-dep (lit->var (gate-id->fanin1 id aignet)) aignet))
      ;; :co (id-max-pi-dep (lit->var (co-id->fanin id aignet)) aignet)
      :pi (+ 1 (ci-id->ionum id aignet))
      :reg 0
      :const 0))
  ///
  (local (defthm nth-of-take
           (implies (< (nfix n) (nfix m))
                    (equal (nth n (take m x))
                           (nth n x)))
           :hints(("Goal" :in-theory (enable nth take)))))
  
  (local (defthm bits-equiv-of-take-implies-nth
           (implies (and (bits-equiv (take n x) (take n y))
                         (< (nfix i) (nfix n)))
                    (equal (equal (bfix (nth i x)) (bfix (nth i y)))
                           t))
           :hints (("goal" :use ((:instance nth-of-take (m n) (n i) (x x))
                                 (:instance nth-of-take (m n) (n i) (x y)))
                    :in-theory (disable nth-of-take)))))
  
  (defthm id-max-pi-dep-implies-eval-with-low-bits-equiv
    (implies (and (<= (id-max-pi-dep id aignet) (nfix n))
                  (bits-equiv (take n invals1)
                              (take n invals2)))
             (equal (id-eval id invals1 regvals aignet)
                    (id-eval id invals2 regvals aignet)))
    :hints (("goal" :induct (id-max-pi-dep id aignet)
             :expand ((id-max-pi-dep id aignet)
                      (:free (invals) (id-eval id invals regvals aignet))
                      (:free (lit invals) (lit-eval lit invals regvals aignet))
                      (:free (lit invals) (lit-eval lit invals regvals aignet))
                      (:free (lit1 lit2 invals) (eval-and-of-lits lit1 lit2 invals regvals aignet))
                      (:free (lit1 lit2 invals) (eval-xor-of-lits lit1 lit2 invals regvals aignet)))))
    :rule-classes nil))

#!aignet
(define aignet-record-pi-deps-aux ((i natp) (aignet) (u32arr))
  :returns (new-u32arr)
  :guard (and (<= i (num-fanins aignet))
              (<= (num-fanins aignet) (u32-length u32arr)))
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  :measure (nfix (- (num-fanins aignet) (nfix i)))
  (b* (((when (mbe :logic (zp (- (num-fanins aignet) (nfix i)))
                   :exec (eql i (num-fanins aignet))))
        u32arr)
       (slot0 (id->slot i 0 aignet))
       (type (snode->type slot0))
       (u32arr
        (aignet-case
          type
          :gate (b* ((max0 (get-u32 (lit->var (snode->fanin slot0)) u32arr))
                     (slot1 (id->slot i 1 aignet))
                     (max1 (get-u32 (lit->var (snode->fanin slot1)) u32arr)))
                  (set-u32 i (max max0 max1) u32arr))
          :in (b* ((slot1 (id->slot i 1 aignet))
                   (regp (snode->regp slot1))
                   ((when (eql regp 1))
                    (set-u32 i 0 u32arr)))
                (set-u32 i (+ 1 (snode->ionum slot1)) u32arr))
          :const (set-u32 i 0 u32arr))))
    (aignet-record-pi-deps-aux (1+ (lnfix i)) aignet u32arr))
  ///
  (local
   (defun-sk aignet-record-pi-deps-aux-invar (i aignet u32arr)
     (forall k
             (implies (< (nfix k) (nfix i))
                      (equal (nth k u32arr)
                             (id-max-pi-dep k aignet))))
     :rewrite :direct))

  (local (in-theory (disable aignet-record-pi-deps-aux-invar)))
  
  (defthm aignet-record-pi-deps-aux-preserves-lower
    (implies (< (nfix k) (nfix i))
             (equal (nth k (aignet-record-pi-deps-aux i aignet u32arr))
                    (nth k u32arr))))

  (local (in-theory (disable nth update-nth
                             (:d aignet-record-pi-deps-aux))))
  
  (local
   (defthm aignet-record-pi-deps-aux-preserves-invar
     (implies (aignet-record-pi-deps-aux-invar i aignet u32arr)
              (aignet-record-pi-deps-aux-invar (num-fanins aignet) aignet
                                               (aignet-record-pi-deps-aux
                                                i aignet u32arr)))
     :hints (("goal" :induct (aignet-record-pi-deps-aux
                              i aignet u32arr)
              :expand ((aignet-record-pi-deps-aux i aignet u32arr)))
             (and stable-under-simplificationp
                  (let* ((lit (assoc 'aignet-record-pi-deps-aux-invar clause))
                         (witness `(aignet-record-pi-deps-aux-invar-witness . ,(cdr lit))))
                    `(:computed-hint-replacement
                      ('(:expand ((id-max-pi-dep i aignet)
                                  (id-max-pi-dep ,witness aignet))
                         :use ((:instance aignet-record-pi-deps-aux-invar-necc
                                (k ,witness)))
                         :in-theory (e/d (aignet-idp)
                                         (aignet-record-pi-deps-aux-invar-necc))
                         :cases ((< (nfix ,witness) (+ 1 (nfix i)))
                                 (< (nfix ,witness) (nfix i)))))
                      :expand (,lit)))))))


  (defthm aignet-record-pi-deps-aux-correct
    (implies (< (nfix k) (num-fanins aignet))
             (equal (nth k (aignet-record-pi-deps-aux 0 aignet u32arr))
                    (id-max-pi-dep k aignet)))
    :hints(("Goal" :use ((:instance aignet-record-pi-deps-aux-preserves-invar
                          (i 0)))
            :expand ((aignet-record-pi-deps-aux-invar 0 aignet u32arr))
            :in-theory (disable aignet-record-pi-deps-aux-preserves-invar))))

  (defret len-of-<fn>
    (implies (<= (num-fanins aignet) (len u32arr))
             (equal (len new-u32arr)
                    (len u32arr)))
    :hints (("goal" :induct <call>
             :expand (<call>)))))

#!aignet
(define aignet-record-pi-deps (aignet u32arr)
  :returns (new-u32arr)
  :guard-hints (("goal" :do-not-induct t))
  :prepwork ((local (include-book "std/lists/resize-list" :dir :system)))
  (b* ((u32arr (mbe :logic (non-exec (create-u32arr))
                    :exec (resize-u32 0 u32arr)))
       (u32arr (resize-u32 (num-fanins aignet) u32arr)))
    (aignet-record-pi-deps-aux 0 aignet u32arr))
  ///
  (defthm aignet-record-pi-deps-correct
    (implies (< (nfix k) (num-fanins aignet))
             (equal (nth k (aignet-record-pi-deps aignet u32arr))
                    (id-max-pi-dep k aignet))))

  (defthm aignet-record-pi-deps-normalize-u32arr
    (implies (syntaxp (not (equal u32arr ''nil)))
             (equal (aignet-record-pi-deps aignet u32arr)
                    (aignet-record-pi-deps aignet nil))))

  (defret len-of-<fn>
    (equal (len new-u32arr)
           (num-fanins aignet))))


(define bfr-var-bounds-ok (x 
                           &optional
                           ((bound natp) 'bound)
                           (u32arr 'u32arr))
  :guard (bfr-p x (bfrstate (bfrmode :aignet) (max 0 (1- (u32-length u32arr)))))
  :guard-hints (("goal" :in-theory (enable bfr-p)))
  :returns (ok)
  (or (booleanp x)
      (let ((id (aignet::lit->var x)))
        (and (< id (u32-length u32arr))
             (<= (get-u32 id u32arr) (lnfix bound)))))
  ///

  (local (defthm nth-of-take
           (equal (nth n (take m x))
                  (if (< (nfix n) (nfix m))
                      (nth n x)
                    nil))
           :hints(("Goal" :in-theory (enable nth take)))))
  
  (local (defthm bits-equiv-of-invals
           (implies (<= (nfix bound) (nfix var))
                    (acl2::bits-equiv (take bound (alist-to-bitarr pis (cons (cons var t) rest) nil))
                                      (take bound (alist-to-bitarr pis rest nil))))
           :hints(("Goal" :in-theory (enable acl2::bits-equiv)))))
  
  (defret <fn>-implies-bfr-boundedp
    :pre-bind ((u32arr (aignet::aignet-record-pi-deps (logicman->aignet logicman) nil)))
    (implies (and (bfr-mode-is :aignet (bfrstate->mode (logicman->bfrstate)))
                  ok)
             (bfr-boundedp x bound logicman))
    :hints (("goal" :expand ((bfr-boundedp x bound logicman)
                             (:free (invals) (aignet::lit-eval x invals nil (logicman->aignet logicman))))
             :in-theory (enable bfr-eval bfr-set-var
                                bfr->aignet-lit
                                bfr-fix
                                aignet-lit->bfr
                                aignet::aignet-lit-fix
                                aignet::aignet-idp
                                aignet::aignet-id-fix)
             :use ((:instance aignet::id-max-pi-dep-implies-eval-with-low-bits-equiv
                    (aignet (logicman->aignet logicman))
                    (id (aignet::lit->var x))
                    (regvals nil)
                    (invals1 (ALIST-TO-BITARR
                              (AIGNET::STYPE-COUNT :PI (LOGICMAN->AIGNET LOGICMAN))
                              (CONS (CONS (MV-NTH 0
                                                  (BFR-BOUNDEDP-WITNESS X BOUND LOGICMAN))
                                          T)
                                    (MV-NTH 1
                                            (BFR-BOUNDEDP-WITNESS X BOUND LOGICMAN)))
                              NIL))
                    (n bound)
                    (invals2 (ALIST-TO-BITARR (AIGNET::STYPE-COUNT :PI (LOGICMAN->AIGNET LOGICMAN))
                                              (MV-NTH 1
                                                      (BFR-BOUNDEDP-WITNESS X BOUND LOGICMAN))
                                              NIL)))))))

  (fty::deffixequiv bfr-var-bounds-ok))

(define bfrlist-var-bounds-ok (x 
                               &optional
                               ((bound natp) 'bound)
                               (u32arr 'u32arr))
  :guard (bfr-listp x (bfrstate (bfrmode :aignet) (max 0 (1- (u32-length u32arr)))))
  :returns (ok)
  (if (atom x)
      t
    (and (bfr-var-bounds-ok (car x))
         (bfrlist-var-bounds-ok (cdr x))))
  ///
  (defret <fn>-implies-bfr-boundedp
    :pre-bind ((u32arr (aignet::aignet-record-pi-deps (logicman->aignet logicman) nil)))
    (implies (and (bfr-mode-is :aignet (bfrstate->mode (logicman->bfrstate)))
                  ok)
             (bfrlist-boundedp x bound logicman))
    :hints(("Goal" :in-theory (enable bfrlist-boundedp))))

  (fty::deffixequiv bfrlist-var-bounds-ok))

    
             
             
                  
             


(defines fgl-object-var-bounds-ok
  (define fgl-object-var-bounds-ok ((x fgl-object-p)
                                    &optional
                                    ((bound natp) 'bound)
                                    (u32arr 'u32arr))
    :guard (fgl-object-bfrs-ok x (bfrstate (bfrmode :aignet) (max 0 (1- (u32-length u32arr)))))
    :guard-hints (("Goal" :expand ((fgl-object-bfrlist x)
                                   (fgl-objectlist-bfrlist x)
                                   (fgl-object-alist-bfrlist x))))
    :measure (acl2::two-nats-measure (fgl-object-count x) 0)
    :returns (ok)
    (fgl-object-case x
      :g-concrete t
      :g-boolean (bfr-var-bounds-ok x.bool)
      :g-integer (bfrlist-var-bounds-ok x.bits)
      :g-ite (and (fgl-object-var-bounds-ok x.test)
                  (fgl-object-var-bounds-ok x.then)
                  (fgl-object-var-bounds-ok x.else))
      :g-apply (fgl-objectlist-var-bounds-ok x.args)
      :g-var t
      :g-cons (and (fgl-object-var-bounds-ok x.car)
                   (fgl-object-var-bounds-ok x.cdr))
      :g-map (fgl-object-alist-var-bounds-ok x.alist)))
  (define fgl-objectlist-var-bounds-ok ((x fgl-objectlist-p)
                                        &optional
                                        ((bound natp) 'bound)
                                        (u32arr 'u32arr))
    :guard (fgl-objectlist-bfrs-ok x (bfrstate (bfrmode :aignet) (max 0 (1- (u32-length u32arr)))))
    :measure (acl2::two-nats-measure (fgl-objectlist-count x) 0)
    :returns (ok)
    (if (atom x)
        t
      (and (fgl-object-var-bounds-ok (car x))
           (fgl-objectlist-var-bounds-ok (cdr x)))))

  (define fgl-object-alist-var-bounds-ok ((x fgl-object-alist-p)
                                          &optional
                                          ((bound natp) 'bound)
                                          (u32arr 'u32arr))
    :guard (fgl-object-alist-bfrs-ok x (bfrstate (bfrmode :aignet) (max 0 (1- (u32-length u32arr)))))
    :measure (acl2::two-nats-measure (fgl-object-alist-count x) (len x))
    :returns (ok)
    (if (atom x)
        t
      (if (mbt (consp (car x)))
          (and (fgl-object-var-bounds-ok (cdar x))
               (fgl-object-alist-var-bounds-ok (cdr x)))
        (fgl-object-alist-var-bounds-ok (cdr x)))))
  ///
  (local (in-theory (disable (:d fgl-object-var-bounds-ok)
                             (:d fgl-objectlist-var-bounds-ok)
                             (:d fgl-object-alist-var-bounds-ok))))

  (fty::deffixequiv-mutual fgl-object-var-bounds-ok
    :hints (("goal" :expand ((fgl-object-alist-fix x)))
            (acl2::use-termhint
             `(:expand ((:free (bound) (fgl-object-var-bounds-ok ,(acl2::hq x)))
                        (:free (bound) (fgl-object-var-bounds-ok ,(acl2::hq (fgl-object-fix x))))
                        (:free (bound) (fgl-object-var-bounds-ok ,(acl2::hq x)))
                        (:free (bound) (fgl-objectlist-var-bounds-ok ,(acl2::hq x)))
                        (:free (bound) (fgl-objectlist-var-bounds-ok ,(acl2::hq (fgl-objectlist-fix x))))
                        (:free (bound) (fgl-objectlist-var-bounds-ok ,(acl2::hq x)))
                        (:free (bound) (fgl-object-alist-var-bounds-ok ,(acl2::hq x)))
                        (:free (bound) (fgl-object-alist-var-bounds-ok ,(acl2::hq (fgl-object-alist-fix x))))
                        (:free (bound) (fgl-object-alist-var-bounds-ok ,(acl2::hq x))))))))


  (defret-mutual <fn>-implies-bfrlist-boundedp
    (defret <fn>-implies-bfrlist-boundedp
      :pre-bind ((u32arr (aignet::aignet-record-pi-deps (logicman->aignet logicman) nil)))
      (implies (and (bfr-mode-is :aignet (bfrstate->mode (logicman->bfrstate)))
                    ok)
               (bfrlist-boundedp (fgl-object-bfrlist x) bound logicman))
      :hints ('(:expand ((:free (u32arr) <call>)
                         (fgl-object-bfrlist x))
                :do-not-induct t))
      :fn fgl-object-var-bounds-ok)
    (defret <fn>-implies-bfrlist-boundedp
      :pre-bind ((u32arr (aignet::aignet-record-pi-deps (logicman->aignet logicman) nil)))
      (implies (and (bfr-mode-is :aignet (bfrstate->mode (logicman->bfrstate)))
                    ok)
               (bfrlist-boundedp (fgl-objectlist-bfrlist x) bound logicman))
      :hints ('(:expand ((:free (u32arr) <call>)
                         (fgl-objectlist-bfrlist x))
                :do-not-induct t))
      :fn fgl-objectlist-var-bounds-ok)
    (defret <fn>-implies-bfrlist-boundedp
      :pre-bind ((u32arr (aignet::aignet-record-pi-deps (logicman->aignet logicman) nil)))
      (implies (and (bfr-mode-is :aignet (bfrstate->mode (logicman->bfrstate)))
                    ok)
               (bfrlist-boundedp (fgl-object-alist-bfrlist x) bound logicman))
      :hints ('(:expand ((:free (u32arr) <call>)
                         (fgl-object-alist-bfrlist x))
                :do-not-induct t))
      :fn fgl-object-alist-var-bounds-ok)
    :hints (("Goal"
             :INDUCT (FGL-OBJECT-VAR-BOUNDS-OK-FLAG FLAG X BOUND
                                                    (aignet::aignet-record-pi-deps (logicman->aignet logicman) nil))))))

  
(define bvar-db-var-bounds-ok ((var natp)
                               bvar-db
                               &optional
                               (u32arr 'u32arr))
  :guard (and (<= (base-bvar bvar-db) var)
              (<= var (next-bvar bvar-db))
              (bvar-db-bfrs-ok bvar-db (bfrstate (bfrmode :aignet) (max 0 (1- (u32-length u32arr))))))
  :measure (nfix (- (next-bvar bvar-db) (nfix var)))
  :returns (ok)
  (if (mbe :logic (zp (- (next-bvar bvar-db) (nfix var)))
           :exec (eql var (next-bvar bvar-db)))
      t
    (and (fgl-object-var-bounds-ok (get-bvar->term var bvar-db) (lnfix var))
         (bvar-db-var-bounds-ok (1+ (lnfix var)) bvar-db)))
  ///
  (defret <fn>-implies-bfrlist-boundedp
    :pre-bind ((u32arr (aignet::aignet-record-pi-deps (logicman->aignet logicman) nil)))
    (implies (and (bfr-mode-is :aignet (bfrstate->mode (logicman->bfrstate)))
                  ok
                  (<= (base-bvar bvar-db) (nfix var))
                  (<= (nfix var) (nfix k))
                  (< (nfix k) (next-bvar bvar-db)))
             (bfrlist-boundedp (fgl-object-bfrlist (get-bvar->term$c k bvar-db)) k logicman))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))))

  
  

(defsection bvar-db-boundedp
  (defun-sk bvar-db-boundedp (bvar-db logicman)
    (forall var
            (implies (and (natp var)
                          (<= (base-bvar$c bvar-db) var)
                          (< var (next-bvar$c bvar-db)))
                     (bfrlist-boundedp (fgl-object-bfrlist (get-bvar->term$c var bvar-db))
                                       var logicman)))
    :rewrite :direct)

  (defthm bvar-db-boundedp-of-empty
    (bvar-db-boundedp (init-bvar-db$c base bvar-db) logicman))

  (in-theory (disable bvar-db-boundedp
                      bvar-db-boundedp-necc))

  (defthm bvar-db-boundedp-of-add
    (implies (and (equal (next-bvar$c bvar-db) (bfr-nvars logicman))
                  (bvar-db-boundedp bvar-db logicman))
             (bvar-db-boundedp (add-term-bvar$c x bvar-db) logicman))
    :hints (("goal" :expand ((bvar-db-boundedp (add-term-bvar$c x bvar-db) logicman))
             :use ((:instance bvar-db-boundedp-necc
                    (var (bvar-db-boundedp-witness (add-term-bvar$c x bvar-db) logicman)))))))

  (defthm bvar-db-boundedp-of-update-term-equivs
    (implies (bvar-db-boundedp bvar-db logicman)
             (bvar-db-boundedp (update-term-equivs$c equivs bvar-db) logicman))
    :hints (("goal" :expand ((bvar-db-boundedp (update-term-equivs$c equivs bvar-db) logicman))
             :use ((:instance bvar-db-boundedp-necc
                    (var (bvar-db-boundedp-witness (update-term-equivs$c equivs bvar-db) logicman)))))))

  (defthm bvar-db-boundedp-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (bvar-db-boundedp bvar-db old)
                  (lbfr-listp (bvar-db-bfrlist bvar-db) old))
             (bvar-db-boundedp bvar-db new))
    :hints (("goal" :expand ((bvar-db-boundedp bvar-db new))
             :use ((:instance bvar-db-boundedp-necc
                    (var (bvar-db-boundedp-witness bvar-db new))
                    (logicman old)))))))


(define bvar-db-boundedp-exec (bvar-db logicman)
  :guard (bvar-db-bfrs-ok bvar-db (logicman->bfrstate))
  :guard-hints (("goal" :in-theory (enable logicman->bfrstate))
                (and stable-under-simplificationp
                     '(:in-theory (enable bvar-db-boundedp))))
  :enabled t
  (mbe :logic (non-exec (ec-call (bvar-db-boundedp bvar-db logicman)))
       :exec (or (bfr-mode-case (lbfr-mode)
                   :aignet
                   (with-local-stobj u32arr
                     (mv-let (u32arr ok)
                       (stobj-let ((aignet (logicman->aignet logicman)))
                                  (u32arr)
                                  (aignet::aignet-record-pi-deps aignet u32arr)
                                  (let ((ok (bvar-db-var-bounds-ok (base-bvar bvar-db) bvar-db)))
                                    (mv u32arr ok)))
                       ok))
                   :aig nil :bdd nil)
                 (non-exec (ec-call (bvar-db-boundedp bvar-db logicman))))))




;; (local (include-book "std/lists/take" :dir :system))
;; (local (in-theory (disable acl2::take-redefinition acl2::take-of-1)))

;; (local (defthm take-of-symbol-list
;;          (implies (symbol-listp x)
;;                   (symbol-listp (take n x)))
;;          :hints(("Goal" :in-theory (enable acl2::take-redefinition)))))

;; (define context-p (x)
;;   (or (pseudo-fnsym-p x)
;;       (and (pseudo-lambda-p x)
;;            (eql (len (acl2::pseudo-lambda->formals x)) 1)))
;;   ///
;;   (define context-fix ((x context-p))
;;     :Returns (new-x context-p)
;;     (mbe :logic (if (pseudo-fnsym-p x)
;;                     x
;;                   (b* (((pseudo-lambda x) (pseudo-lambda-fix x)))
;;                     (pseudo-lambda (take 1 x.formals) x.body)))
;;          :exec x)
;;     ///
;;     (defthm context-fix-when-context-p
;;       (implies (context-p x)
;;                (equal (context-fix x) x)))

;;     (fty::deffixtype context :pred context-p :fix context-fix :equiv context-equiv
;;       :define t)))


(define check-equiv-replacement ((x fgl-object-p)
                                 (equiv-term fgl-object-p)
                                 (contexts equiv-contextsp)
                                 state)
  :returns (mv ok
               (equiv fgl-object-p)
               negp
               iff-equiv-p)
  (declare (ignorable state))
  ;; BOZO fix these to work with context fixing terms, refinements, negated equivs, etc
  (b* (((when (hons-equal (fgl-object-fix x)
                          (fgl-object-fix equiv-term)))
        (mv t nil t (member-eq 'iff (equiv-contexts-fix contexts))))
       ((unless (fgl-object-case equiv-term :g-apply))
        (mv nil nil nil nil))
       (equiv (g-apply->fn equiv-term))
       ((unless (or (eq equiv 'equal)
                    (member-eq equiv (equiv-contexts-fix contexts))))
        (mv nil nil nil nil))
       (args (g-apply->args equiv-term))
       ((unless (equal (len args) 2))
        (mv nil nil nil nil))
       ((when (hons-equal (car args) (fgl-object-fix x)))
        (mv t (cadr args) nil nil))
       ((when (hons-equal (cadr args) (fgl-object-fix x)))
        (mv t (car args) nil nil)))
    (mv nil nil nil nil))
  ///
  (defret fgl-object-bfrlist-of-<fn>
    (implies (not (member v (fgl-object-bfrlist equiv-term)))
             (not (member v (fgl-object-bfrlist equiv))))))



(define try-equivalences ((x fgl-object-p)
                          (bvars nat-listp)
                          (contexts equiv-contextsp)
                          pathcond
                          bvar-db
                          logicman
                          state)
  :guard (and (bvar-list-okp bvars bvar-db)
              (equal (next-bvar bvar-db) (bfr-nvars)))
  :returns (mv ok
               (new-x fgl-object-p)
               (new-pathcond (equal new-pathcond (pathcond-fix pathcond))))
  :guard-hints ((and stable-under-simplificationp
                     '(:expand ((bvar-list-okp$c bvars bvar-db))
                       :in-theory (enable bfr-varname-p))))
  (b* ((pathcond (pathcond-fix pathcond))
       ((when (atom bvars)) (mv nil nil pathcond))
       (bvar (lnfix (car bvars)))
       (bfr-var (bfr-var bvar logicman))
       (equiv-term (get-bvar->term bvar bvar-db))
       ((mv check-ok repl negp iff-equiv-p)
        (check-equiv-replacement x equiv-term contexts state))
       ((unless check-ok)
        (try-equivalences x (cdr bvars) contexts pathcond bvar-db logicman state))
       ((mv ans pathcond) (logicman-pathcond-implies bfr-var pathcond logicman))
       ((when (if negp (eql ans 0) (eql ans 1)))
        (mv t repl pathcond))
       ((when (and iff-equiv-p ans))
        (mv t (eql ans 1) pathcond)))
      (try-equivalences x (cdr bvars) contexts pathcond bvar-db logicman state))
  ///
  (local (defthm fgl-object-bfrlist-of-boolean
           (implies (booleanp x)
                    (equal (fgl-object-bfrlist x) nil))
           :hints(("Goal" :in-theory (enable booleanp)))))
  (defret fgl-object-bfrlist-of-<fn>
    (implies (and (not (member v (bvar-db-bfrlist bvar-db)))
                  (bvar-list-okp$c bvars bvar-db))
             (not (member v (fgl-object-bfrlist new-x))))
    :hints(("Goal" :in-theory (enable bvar-list-okp$c)))))


(define try-equivalences-loop ((x fgl-object-p)
                               (contexts equiv-contextsp)
                               (clk natp)
                               pathcond
                               bvar-db
                               logicman
                               state)
  :guard (equal (next-bvar bvar-db) (bfr-nvars))
  :measure (nfix clk)
  :returns (mv error
               (replacement fgl-object-p)
               (new-pathcond (equal new-pathcond (pathcond-fix pathcond))))
  (b* ((pathcond (pathcond-fix pathcond))
       ((when (zp clk)) (mv "try-equivalences ran out of clock -- equiv loop?"
                            (fgl-object-fix x)
                            pathcond))
       (equivs (get-term->equivs x bvar-db))
       ((mv ok repl pathcond)
        (try-equivalences x equivs contexts pathcond bvar-db logicman state))
       ((when ok)
        (try-equivalences-loop repl contexts (1- clk) pathcond bvar-db logicman state)))
    (mv nil (fgl-object-fix x) pathcond))
  ///
  (defret fgl-object-bfrlist-of-<fn>
    (implies (and (not (member v (bvar-db-bfrlist bvar-db)))
                  (not (member v (fgl-object-bfrlist x))))
             (not (member v (fgl-object-bfrlist replacement))))))


(define maybe-add-equiv-term ((test-obj fgl-object-p)
                              (bvar natp)
                              bvar-db
                              state)
  :guard (and (<= (base-bvar bvar-db) bvar)
              (< bvar (next-bvar bvar-db)))
  :returns (new-bvar-db)
  ;; We (maybe) add an association between some term and the generated Boolean
  ;; variable, saying that if the Boolean variable is assumed true or false,
  ;; that may imply some value of the test-obj.

  ;; In some cases we associate test-obj itself to bvar.  In this case the
  ;; association means if bvar is NIL, then normalize test-obj is NIL.
  ;; Otherwise test-obj is (equal x y) and we associate either x or y to bvar;
  ;; in this case, if bvar is true, normalize (respectively) x to y or y to x.
  (declare (ignorable state))
  (fgl-object-case test-obj
    :g-var (add-term-equiv test-obj bvar bvar-db)
    :g-apply (b* ((fn test-obj.fn)
                  (args test-obj.args)

                  ((unless (and (eq fn 'equal)
                                (equal (len args) 2)))
                   (add-term-equiv test-obj bvar bvar-db))
                  ((list a b) args)
                  ;; The rest is just a heuristic determination of which should rewrite to
                  ;; the other. Note: in many cases we don't rewrite either way!

                  ;; Heuristic 1: when a variable is equated with anything else, normalize var -> other.
                  ;; (Note this could loop, up to the user to prevent this)
                  (a-varp (fgl-object-case a :g-var))
                  (b-varp (fgl-object-case b :g-var))
                  ((when a-varp)
                   (if b-varp
                       (add-term-equiv test-obj bvar bvar-db)
                     (add-term-equiv a bvar bvar-db)))
                  ((when b-varp)
                   (add-term-equiv b bvar bvar-db))

                  ;; Heuristic 2: when one object has no free variables,
                  ;;              normalize other -> good obj.
                  (a-goodp (fgl-object-variable-free-p a))
                  ((when a-goodp)
                   (add-term-equiv b bvar bvar-db))
                  (b-goodp (fgl-object-variable-free-p b))
                  ((when b-goodp)
                   (add-term-equiv a bvar bvar-db)))

               ;; Neither heuristic applied -- don't normalize either way.
               (add-term-equiv test-obj bvar bvar-db))

    :otherwise (add-term-equiv test-obj bvar bvar-db))
  ///
  

  (defthm bvar-db-bfrlist-of-maybe-add-equiv-term
    (equal (bvar-db-bfrlist (maybe-add-equiv-term obj bvar bvar-db state))
           (bvar-db-bfrlist bvar-db))
    :hints(("Goal" :in-theory (enable maybe-add-equiv-term
                                      bvar-db-bfrlist
                                      add-term-equiv))))

  (defthm bvar-db-boundedp-of-maybe-add-equiv-term
    (implies (bvar-db-boundedp bvar-db logicman)
             (bvar-db-boundedp (maybe-add-equiv-term obj bvar bvar-db state) logicman))
    :hints (("goal" :expand ((bvar-db-boundedp (maybe-add-equiv-term obj bvar bvar-db state) logicman))
             :use ((:instance bvar-db-boundedp-necc
                    (var (bvar-db-boundedp-witness
                          (maybe-add-equiv-term obj bvar bvar-db state) logicman))))
             :in-theory (enable add-term-equiv))))

  (defthm next-bvar$c-of-maybe-add-equiv-term
    (equal (next-bvar$c (maybe-add-equiv-term x bvar bvar-db state))
           (next-bvar$c bvar-db))
    :hints(("Goal" :in-theory (enable maybe-add-equiv-term))))

  (defthm base-bvar$c-of-maybe-add-equiv-term
    (equal (base-bvar$c (maybe-add-equiv-term x bvar bvar-db state))
           (base-bvar$c bvar-db))
    :hints(("Goal" :in-theory (enable maybe-add-equiv-term))))

  (defthm get-bvar->term$c-of-maybe-add-equiv-term
    (equal (get-bvar->term$c n (maybe-add-equiv-term x bvar bvar-db state))
           (get-bvar->term$c n bvar-db)))

  (defthm get-term->bvar$c-of-maybe-add-equiv-term
    (equal (get-term->bvar$c obj (maybe-add-equiv-term x bvar bvar-db state))
           (get-term->bvar$c obj bvar-db))))



