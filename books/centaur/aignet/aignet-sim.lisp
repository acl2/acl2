; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "AIGNET")

(include-book "aignet-from-aig")
(include-book "centaur/vl/util/cwtime" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable nth update-nth
                           sets::double-containment)))

(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(include-book "ihs/logops-definitions" :dir :system)
(local (defthm nfix-equal-posp
         (implies (and (syntaxp (quotep x))
                       (posp x))
                  (equal (equal (nfix n) x)
                         (equal n x)))
         :hints(("Goal" :in-theory (enable nfix)))))

(local (defthm equal-1-when-bitp
         (implies (not (equal x 0))
                  (equal (equal x 1) (acl2::bitp x)))))





(defsection aig-fast-biteval-seq

  (local (in-theory (disable acl2::nth-with-large-index)))

  (local (defthm lookup-when-good-varmap-p-natp
           (implies (and (good-varmap-p varmap aignet)
                         (hons-assoc-equal var varmap))
                    (and (integerp (cdr (hons-assoc-equal var varmap)))
                         (<= 0 (cdr (hons-assoc-equal var varmap)))))
           :hints(("Goal" :in-theory (enable hons-assoc-equal
                                             good-varmap-p)))))

  (defun aig-fast-biteval-set-ins (inalist varmap aignet-vals aignet)
    (declare (xargs :stobjs (aignet-vals aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (good-varmap-p varmap aignet)
                                (bitarr-sizedp aignet-vals aignet))
                    :guard-debug t))
    (b* (((when (atom inalist)) aignet-vals)
         ((when (atom (car inalist)))
          (aig-fast-biteval-set-ins (cdr inalist) varmap aignet-vals aignet))
         (varmap-look (hons-get (caar inalist) varmap))
         ((when (not varmap-look))
          ;; an unused variable -- no big deal
          (aig-fast-biteval-set-ins (cdr inalist) varmap aignet-vals aignet))
         (lit (cdr varmap-look))
         (id (lit-id lit))
         ((unless (and (int= (id->type id aignet) (in-type))
                       (int= (io-id->regp id aignet) 0)
                       (int= (lit-neg (cdr varmap-look)) 0)))
          (cw "Bad variable: not mapped to a nonnegated PI node: ~x0~%" (caar inalist))
          (aig-fast-biteval-set-ins (cdr inalist) varmap aignet-vals aignet))
         (aignet-vals (set-id->bit id (if (cdar inalist) 1 0) aignet-vals)))
      (aig-fast-biteval-set-ins (cdr inalist) varmap aignet-vals aignet)))

  (defthm aignet-eval-well-sizedp-after-aig-fast-biteval-set-ins
    (implies (bitarr-sizedp aignet-vals aignet)
             (memo-tablep (aig-fast-biteval-set-ins
                           inalist varmap aignet-vals aignet)
                          aignet))
    :hints (("goal" :induct (aig-fast-biteval-set-ins
                             inalist varmap aignet-vals aignet))))

  (defun aig-fast-biteval-set-regs (initvals varmap aignet-vals aignet)
    (declare (xargs :stobjs (aignet-vals aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (good-varmap-p varmap aignet)
                                (bitarr-sizedp aignet-vals aignet))))
    (b* (((when (atom initvals)) aignet-vals)
         ((when (atom (car initvals)))
          (aig-fast-biteval-set-regs (cdr initvals) varmap aignet-vals aignet))
         (varmap-look (hons-get (caar initvals) varmap))
         ((when (not varmap-look))
          ;; an unused variable -- no big deal
          (aig-fast-biteval-set-regs (cdr initvals) varmap aignet-vals aignet))
         (lit (cdr varmap-look))
         (id (lit-id lit))
         ((unless (and (int= (id->type id aignet) (in-type))
                       (int= (io-id->regp id aignet) 1)
                       (int= (lit-neg (cdr varmap-look)) 0)))
          (cw "Bad variable: not mapped to a nonnegated reg node: ~x0~%" (caar initvals))
          (aig-fast-biteval-set-regs (cdr initvals) varmap aignet-vals aignet))
         (ri (regnum->id (io-id->ionum id aignet) aignet))
         (aignet-vals (set-id->bit ri (if (cdar initvals) 1 0)
                                aignet-vals)))
      (aig-fast-biteval-set-regs (cdr initvals) varmap aignet-vals aignet)))

  (defthm aignet-eval-well-sizedp-after-aig-fast-biteval-set-regs
    (implies (bitarr-sizedp aignet-vals aignet)
             (memo-tablep (aig-fast-biteval-set-regs
                           initvals varmap aignet-vals aignet)
                          aignet))
    :hints (("goal" :induct (aig-fast-biteval-set-regs
                             initvals varmap aignet-vals aignet))))


  (defun aignet-eval-get-outs (n aignet-vals aignet)
    (declare (xargs :stobjs (aignet aignet-vals)
                    :guard (and (aignet-well-formedp aignet)
                                (natp n)
                                (<= n (num-outs aignet))
                                (bitarr-sizedp aignet-vals aignet))
                    :measure (nfix (- (nfix (num-outs aignet)) (nfix n)))
                    :hints(("Goal" :in-theory (enable nfix)))))
    (b* (((when (mbe :logic (zp (- (nfix (num-outs aignet)) (nfix n)))
                     :exec (int= n (num-outs aignet))))
          nil))
      (cons (int= 1 (get-id->bit (outnum->id n aignet) aignet-vals))
            (aignet-eval-get-outs (1+ (lnfix n)) aignet-vals aignet))))

  (defun aignet-eval-get-state (n aignet-vals aignet)
    (declare (xargs :stobjs (aignet aignet-vals)
                    :guard (and (aignet-well-formedp aignet)
                                (natp n)
                                (<= n (num-regs aignet))
                                (bitarr-sizedp aignet-vals aignet))
                    :measure (nfix (- (nfix (num-regs aignet)) (nfix n)))
                    :hints(("Goal" :in-theory (enable nfix)))))
    (b* (((when (mbe :logic (zp (- (nfix (num-regs aignet)) (nfix n)))
                     :exec (int= n (num-regs aignet))))
          nil)
         (ri (regnum->id n aignet)))
      (cons (int= 1 (get-id->bit ri aignet-vals))
            (aignet-eval-get-state (1+ (lnfix n)) aignet-vals aignet))))

  (defun aig-fast-biteval-step (inalist varmap aignet-vals aignet)
    (declare (xargs :stobjs (aignet-vals aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (good-varmap-p varmap aignet)
                                (bitarr-sizedp aignet-vals aignet))
                    :guard-debug t))
    (b* ((aignet-vals (aig-fast-biteval-set-ins inalist varmap aignet-vals aignet)))
      (aignet-eval-frame1 aignet-vals aignet)))

  (defthm aignet-eval-well-sizedp-after-aig-fast-biteval-step
    (implies (bitarr-sizedp aignet-vals aignet)
             (memo-tablep (aig-fast-biteval-step
                           inalist varmap aignet-vals aignet)
                          aignet))
    :hints(("Goal" :in-theory (disable aignet-vals-update-ri->ros aignet-eval))))

  (local (in-theory (disable aig-fast-biteval-step)))

  (defun aigneteval-print-state (n aignet-vals aignet)
    (declare (xargs :stobjs (aignet-vals aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (natp n)
                                (<= n (num-regs aignet))
                                (bitarr-sizedp aignet-vals aignet))
                    :measure (nfix (- (nfix (num-regs aignet)) (nfix n)))))
    (if (mbe :logic (zp (- (nfix (num-regs aignet)) (nfix n)))
             :exec (= (num-regs aignet) n))
        (cw "~%")
      (prog2$ (cw "~x0" (get-id->bit (regnum->id n aignet) aignet-vals))
              (aigneteval-print-state (1+ (lnfix n)) aignet-vals aignet))))


  (defun aig-fast-biteval-run (input-seq varmap aignet-vals aignet)
    (Declare (xargs :stobjs (aignet-vals aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (good-varmap-p varmap aignet)
                                (bitarr-sizedp aignet-vals aignet))))
    (b* (((when (Atom input-seq)) aignet-vals)
         (aignet-vals
          (aig-fast-biteval-step (car input-seq) varmap aignet-vals aignet)))
      ;;(cw "State: ")
      ;;(aigneteval-print-state 0 aignet-vals aignet)
      (aig-fast-biteval-run (cdr input-seq) varmap aignet-vals aignet)))

  (defthm aignet-eval-well-sizedp-after-aig-fast-biteval-run
    (implies (bitarr-sizedp aignet-vals aignet)
             (memo-tablep (aig-fast-biteval-run
                           inalists varmap aignet-vals aignet)
                          aignet)))

  (local (in-theory (disable aig-fsm-to-aignet)))

  (defun aig-fast-biteval-seq-body (updates outs init-st input-seq aignet aignet-vals)
    (declare (xargs :stobjs (aignet aignet-vals)
                    :guard (non-bool-atom-listp (alist-keys updates))
                    :guard-debug t
                    :guard-hints
                    ('(:do-not-induct t
                       :use ((:instance
                              aignet-well-formedp-of-aig-fsm-to-aignet
                              (regs updates)
                              (max-gates (+ 1 (* 10 (+ (len updates) (len outs)))))
                              (gatesimp 8)))
                       :in-theory (disable aignet-well-formedp-of-aig-fsm-to-aignet)))))
    (b* (((mv aignet varmap & &)
          (cwtime
           (aig-fsm-to-aignet
            updates outs
            (+ 1 (* 10 (+ (len updates) (len outs))))
            8 aignet)))
         ((with-fast varmap))
         (aignet-vals (resize-bits (num-nodes aignet) aignet-vals))
         (aignet-vals
          (cwtime (aig-fast-biteval-set-regs init-st varmap aignet-vals aignet)))
         ;;(- (cw "Initially:~%state: ")
         ;;   (aigneteval-print-state 0 aignet-vals aignet))
         (aignet-vals
          (cwtime (aig-fast-biteval-run input-seq varmap aignet-vals aignet)))
         (res (cwtime
               (aignet-eval-get-outs 0 aignet-vals aignet)
               :name aignet-eval-get-outs)))
      (mv res aignet aignet-vals)))

  (defund aig-fast-biteval-seq (updates outs init-st input-seq)
    (declare (xargs :guard (non-bool-atom-listp
                            (alist-keys updates))))
    (b* (((local-stobjs aignet aignet-vals)
          (mv res aignet aignet-vals)))
      (aig-fast-biteval-seq-body
       updates outs init-st input-seq aignet aignet-vals)))

  (local (in-theory (enable aig-fast-biteval-seq)))

  (defthm true-listp-of-aig-fast-biteval-seq
    (true-listp (aig-fast-biteval-seq updates outs init-st input-seq)))


  (defun aig-fast-biteval-run-outs (input-seq varmap aignet-vals aignet)
    (Declare (xargs :stobjs (aignet-vals aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (good-varmap-p varmap aignet)
                                (bitarr-sizedp aignet-vals aignet))))
    (b* (((when (Atom input-seq)) (mv nil aignet-vals))
         (aignet-vals
          (aig-fast-biteval-step (car input-seq) varmap aignet-vals aignet))
         (out-eval (aignet-eval-get-outs 0 aignet-vals aignet))
         ;;(cw "State: ")
         ;;(aigneteval-print-state 0 aignet-vals aignet)
         ((mv rest aignet-vals)
          (aig-fast-biteval-run-outs (cdr input-seq) varmap aignet-vals aignet)))
      (mv (cons out-eval rest) aignet-vals)))

  (defthm aignet-eval-well-sizedp-after-aig-fast-biteval-run-outs
    (implies (bitarr-sizedp aignet-vals aignet)
             (memo-tablep (mv-nth 1 (aig-fast-biteval-run-outs
                                     input-seq varmap aignet-vals
                                     aignet))
                          aignet)))


  (defun aig-fast-biteval-seq-outs/state-body (updates outs init-st input-seq aignet aignet-vals)
    (declare (xargs :stobjs (aignet aignet-vals)
                    :guard (non-bool-atom-listp (alist-keys updates))
                    :guard-debug t
                    :guard-hints
                    ('(:do-not-induct t
                       :use ((:instance
                              aignet-well-formedp-of-aig-fsm-to-aignet
                              (regs updates)
                              (max-gates (+ 1 (* 10 (+ (len updates) (len outs)))))
                              (gatesimp 8)))
                       :in-theory (disable aignet-well-formedp-of-aig-fsm-to-aignet)))))
    (b* (((mv aignet varmap & regvars)
          (cwtime
           (aig-fsm-to-aignet
            updates outs
            (+ 1 (* 10 (+ (len updates) (len outs))))
            8 aignet)))
         ((with-fast varmap))
         (aignet-vals (resize-bits (num-nodes aignet) aignet-vals))
         (aignet-vals
          (cwtime (aig-fast-biteval-set-regs init-st varmap aignet-vals aignet)))
         ;;(- (cw "Initially:~%state: ")
         ;;   (aigneteval-print-state 0 aignet-vals aignet))
         ((mv outs aignet-vals)
          (cwtime (aig-fast-biteval-run-outs input-seq varmap aignet-vals aignet)))
         (st (aignet-eval-get-state 0 aignet-vals aignet))
         (st-alist (pairlis$ regvars st)))
      (mv outs st-alist aignet aignet-vals)))

  (defund aig-fast-biteval-seq-outs/state (updates outs init-st input-seq)
    (declare (xargs :guard (non-bool-atom-listp
                            (alist-keys updates))))
    (b* (((local-stobjs aignet aignet-vals)
          (mv res st aignet aignet-vals)))
      (cw "~x0 frames~%" (len input-seq))
      (aig-fast-biteval-seq-outs/state-body
       updates outs init-st input-seq aignet aignet-vals))))
