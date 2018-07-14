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
(include-book "from-hons-aig")
(include-book "eval")
(include-book "centaur/vl/util/cwtime" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))
(local (in-theory (disable nth update-nth
                           acl2::nth-with-large-index
                           set::double-containment)))

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



(local (defthm lookup-when-good-varmap-p-natp
         (implies (and (good-varmap-p varmap aignet)
                       (hons-assoc-equal var varmap))
                  (and (integerp (cdr (hons-assoc-equal var varmap)))
                       (<= 0 (cdr (hons-assoc-equal var varmap)))))
         :hints(("Goal" :in-theory (enable hons-assoc-equal
                                           good-varmap-p)))))

(define aig-fast-biteval-set-ins (inalist varmap vals aignet)
  :guard (and (good-varmap-p varmap aignet)
              (<= (num-nodes aignet) (bits-length vals)))
  (b* (((when (atom inalist)) vals)
       ((when (atom (car inalist)))
        (aig-fast-biteval-set-ins (cdr inalist) varmap vals aignet))
       (varmap-look (hons-get (caar inalist) varmap))
       ((when (not varmap-look))
        ;; an unused variable -- no big deal
        (aig-fast-biteval-set-ins (cdr inalist) varmap vals aignet))
       (lit (cdr varmap-look))
       (id (lit-id lit))
       ((unless (and (int= (id->type id aignet) (in-type))
                     (int= (id->regp id aignet) 0)
                     (int= (lit-neg (cdr varmap-look)) 0)))
        (cw "Bad variable: not mapped to a nonnegated PI node: ~x0~%" (caar inalist))
        (aig-fast-biteval-set-ins (cdr inalist) varmap vals aignet))
       (vals (set-bit id (if (cdar inalist) 1 0) vals)))
    (aig-fast-biteval-set-ins (cdr inalist) varmap vals aignet))
  ///
  (defthm aig-fast-biteval-set-ins-length-of-vals
    (<= (len vals)
        (len (aig-fast-biteval-set-ins inalist varmap vals aignet)))
    :rule-classes :linear))

(define aig-fast-biteval-set-regs (initvals varmap vals aignet)
  :guard (and (good-varmap-p varmap aignet)
              (<= (num-nodes aignet) (bits-length vals)))
  (b* (((when (atom initvals)) vals)
       ((when (atom (car initvals)))
        (aig-fast-biteval-set-regs (cdr initvals) varmap vals aignet))
       (varmap-look (hons-get (caar initvals) varmap))
       ((when (not varmap-look))
        ;; an unused variable -- no big deal
        (aig-fast-biteval-set-regs (cdr initvals) varmap vals aignet))
       (lit (cdr varmap-look))
       (id (lit-id lit))
       ((unless (and (int= (id->type id aignet) (in-type))
                     (int= (id->regp id aignet) 1)
                     (int= (lit-neg (cdr varmap-look)) 0)))
        (cw "Bad variable: not mapped to a nonnegated reg node: ~x0~%" (caar initvals))
        (aig-fast-biteval-set-regs (cdr initvals) varmap vals aignet))
       (nxst (reg-id->nxst id aignet))
       (vals (set-bit nxst (if (cdar initvals) 1 0)
                      vals)))
    (aig-fast-biteval-set-regs (cdr initvals) varmap vals aignet))
  ///
  (defthm aig-fast-biteval-set-regs-length-of-vals
    (<= (len vals)
        (len (aig-fast-biteval-set-regs inalist varmap vals aignet)))
    :rule-classes :linear))


(define aignet-eval-get-outs ((n :type (integer 0 *))
                              vals aignet)
  :guard (and (<= n (num-outs aignet))
              (<= (num-nodes aignet) (bits-length vals)))
  :measure (nfix (- (nfix (num-outs aignet)) (nfix n)))
  :returns (outs (equal (len outs)
                        (nfix (- (num-outs aignet) (nfix n)))))
  (b* (((when (mbe :logic (zp (- (nfix (num-outs aignet)) (nfix n)))
                   :exec (int= n (num-outs aignet))))
        nil))
    (cons (int= 1 (get-bit (outnum->id n aignet) vals))
          (aignet-eval-get-outs (1+ (lnfix n)) vals aignet))))

(define aignet-eval-get-state ((n :type (integer 0 *))
                               vals aignet)
  :guard (and (<= n (num-regs aignet))
              (<= (num-nodes aignet) (bits-length vals)))
  :measure (nfix (- (nfix (num-regs aignet)) (nfix n)))
  (b* (((when (mbe :logic (zp (- (nfix (num-regs aignet)) (nfix n)))
                   :exec (int= n (num-regs aignet))))
        nil)
       (reg (regnum->id n aignet))
       (nxst (reg-id->nxst reg aignet))
       (target (if (int= nxst 0) reg nxst)))
    (cons (int= 1 (get-bit target vals))
          (aignet-eval-get-state (1+ (lnfix n)) vals aignet))))

(define aig-fast-biteval-step (inalist varmap vals aignet)
  :guard (and (good-varmap-p varmap aignet)
              (<= (num-nodes aignet) (bits-length vals)))
  (b* ((vals (aig-fast-biteval-set-ins inalist varmap vals aignet)))
    (aignet-eval-frame vals aignet))
  ///
  (defthm aig-fast-biteval-step-length-of-vals
    (<= (len vals)
        (len (aig-fast-biteval-step inalist varmap vals aignet)))
    :rule-classes :linear))

(define aignet-eval-print-state ((n natp) vals aignet)
  :guard (and (<= n (num-regs aignet))
              (<= (num-nodes aignet) (bits-length vals)))
  :measure (nfix (- (nfix (num-regs aignet)) (nfix n)))
  (if (mbe :logic (zp (- (nfix (num-regs aignet)) (nfix n)))
           :exec (= (num-regs aignet) n))
      (cw "~%")
    (prog2$ (cw "~x0" (get-bit (regnum->id n aignet) vals))
            (aignet-eval-print-state (1+ (lnfix n)) vals aignet))))


(define aig-fast-biteval-run (input-seq varmap vals aignet)
  :guard (and (good-varmap-p varmap aignet)
              (<= (num-nodes aignet) (bits-length vals)))
  (b* (((when (Atom input-seq)) vals)
       (vals
        (aig-fast-biteval-step (car input-seq) varmap vals aignet)))
    ;;(cw "State: ")
    ;;(aignet-eval-print-state 0 vals aignet)
    (aig-fast-biteval-run (cdr input-seq) varmap vals aignet))
  ///
  (defthm aig-fast-biteval-run-length-of-vals
    (<= (len vals)
        (len (aig-fast-biteval-run input-seq varmap vals aignet)))
    :rule-classes :linear))

(define aig-fast-biteval-seq-body (updates outs init-st input-seq aignet vals)
  :guard (acl2::aig-var-listp (alist-keys updates))
  (b* (((mv aignet varmap & &)
        (cwtime
         (aig-fsm-to-aignet
          updates outs
          (+ 1 (* 10 (+ (len updates) (len outs))))
          8 aignet)))
       ((with-fast varmap))
       (vals (resize-bits (num-nodes aignet) vals))
       (vals
        (cwtime (aig-fast-biteval-set-regs init-st varmap vals aignet)))
       ;;(- (cw "Initially:~%state: ")
       ;;   (aignet-eval-print-state 0 vals aignet))
       (vals
        (cwtime (aig-fast-biteval-run input-seq varmap vals aignet)))
       (res (cwtime
             (aignet-eval-get-outs 0 vals aignet)
             :name aignet-eval-get-outs)))
    (mv res aignet vals)))

(define aig-fast-biteval-seq (updates outs init-st input-seq)
  :guard (acl2::aig-var-listp (alist-keys updates))
  (b* (((local-stobjs aignet vals)
        (mv res aignet vals)))
    (aig-fast-biteval-seq-body
     updates outs init-st input-seq aignet vals))
  ///
  (defthm true-listp-of-aig-fast-biteval-seq
    (true-listp (aig-fast-biteval-seq updates outs init-st input-seq))
    :hints (("goal" :in-theory (enable aig-fast-biteval-seq-body)))))


(define aig-fast-biteval-run-outs (input-seq varmap vals aignet)
  :guard (and (good-varmap-p varmap aignet)
              (<= (num-nodes aignet) (bits-length vals)))
  (b* (((when (Atom input-seq)) (mv nil vals))
       (vals
        (aig-fast-biteval-step (car input-seq) varmap vals aignet))
       (out-eval (aignet-eval-get-outs 0 vals aignet))
       ;;(cw "State: ")
       ;;(aignet-eval-print-state 0 vals aignet)
       ((mv rest vals)
        (aig-fast-biteval-run-outs (cdr input-seq) varmap vals aignet)))
    (mv (cons out-eval rest) vals))
  ///
  (defthm aig-fast-biteval-run-outs-length-of-vals
    (<= (len vals)
        (len (mv-nth 1 (aig-fast-biteval-run-outs input-seq varmap vals aignet))))
    :rule-classes :linear))


(define aig-fast-biteval-seq-outs/state-body (updates outs init-st input-seq aignet vals)
  :guard (acl2::aig-var-listp (alist-keys updates))
  (b* (((mv aignet varmap & regvars)
        (cwtime
         (aig-fsm-to-aignet
          updates outs
          (+ 1 (* 10 (+ (len updates) (len outs))))
          8 aignet)))
       ((with-fast varmap))
       (vals (resize-bits (num-nodes aignet) vals))
       (vals
        (cwtime (aig-fast-biteval-set-regs init-st varmap vals aignet)))
       ;;(- (cw "Initially:~%state: ")
       ;;   (aignet-eval-print-state 0 vals aignet))
       ((mv outs vals)
        (cwtime (aig-fast-biteval-run-outs input-seq varmap vals aignet)))
       (st (aignet-eval-get-state 0 vals aignet))
       (st-alist (pairlis$ regvars st)))
    (mv outs st-alist aignet vals)))

(define aig-fast-biteval-seq-outs/state (updates outs init-st input-seq)
  :guard (acl2::aig-var-listp (alist-keys updates))
  (b* (((local-stobjs aignet vals)
        (mv res st aignet vals)))
    (cw "~x0 frames~%" (len input-seq))
    (aig-fast-biteval-seq-outs/state-body
     updates outs init-st input-seq aignet vals)))
