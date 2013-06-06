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

(in-package "AIGNET$C")

(local (include-book "aignet-exec-thms"))

(set-enforce-redundancy t)
; (include-book "centaur/aignet/idp" :dir :system)
(include-book "litp")
(include-book "snodes")
(include-book "cutil/define" :dir :system)
(defmacro const-type () 0)
(defmacro gate-type () 1)
(defmacro in-type () 2)
(defmacro out-type () 3)

(defstobj aignet

  (num-ins     :type (integer 0 *) :initially 0)
  (num-outs    :type (integer 0 *) :initially 0)
  (num-regs    :type (integer 0 *) :initially 0)
  (num-gates   :type (integer 0 *) :initially 0)
  (num-nxsts  :type (integer 0 *) :initially 0)
  ;; num-nodes = the sum of the above + 1 (const)
  (num-nodes    :type (integer 0 *) :initially 1)

; For space efficiency we tell the Lisp to use unsigned-byte 32's here, which
; in CCL at least will result in a very compact representation of these arrays.
; We might change this in the future if we ever need more space.  We try not to
; let this affect our logical story to the degree possible.
;
; The sizes of these arrays could also complicate our logical story, but we try
; to avoid thinking about their sizes at all.  Instead, we normally think of
; these as having unbounded length.  In the implementation we generally expect
; that:
;
;    num-nodes <= |gates|
;    num-outs    <= |outs|
;    num-regs    <= |regs|
;
; But if these don't hold we'll generally just cause an error, and logically we
; just act like the arrays are unbounded.

  (nodes       :type (array (unsigned-byte 32) (2))
               :initially 0
               :resizable t)
  (ins        :type (array (unsigned-byte 32) (0))
              :initially 0
              :resizable t)
  (outs       :type (array (unsigned-byte 32) (0))
              :initially 0
              :resizable t)
  (regs       :type (array (unsigned-byte 32) (0))
              :initially 0
              :resizable t)

  :inline t
  ;; BOZO do we want to add some notion of the initial state of the
  ;; registers, or the current state, or anything like that?  And if
  ;; so, what do we want to allow it to be?  Or can we deal with that
  ;; separately on a per-algorithm basis?
  )


(defund aignet-sizes-ok (aignet)
  (declare (xargs :stobjs aignet))
  (and (natp (num-ins aignet))
       (natp (num-regs aignet))
       (natp (num-outs aignet))
       (natp (num-gates aignet))
       (natp (num-nxsts aignet))
       (natp (num-nodes aignet))
       (<= (lnfix (num-ins aignet))
           (ins-length aignet))
       (<= (lnfix (num-outs aignet))
           (outs-length aignet))
       (<= (lnfix (num-regs aignet))
           (regs-length aignet))
       (<= (* 2 (lnfix (num-nodes aignet)))
           (nodes-length aignet))))

(defsection executable-node-accessors

  ;; Executable accessors.  These come in various levels of granularity for
  ;; convenience.

  ;; get one of the two slots of an node by ID
  (definline id->slot (id slot aignet)
    (declare (type (integer 0 *) id)
             (type bit slot)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (< id (num-nodes aignet)))))
    (lnfix (nodesi (+ (acl2::lbfix slot) (* 2 (lnfix id))) aignet)))

  (definlined set-snode->regid (regin slot0)
    (declare (type (integer 0 *) slot0)
             (type (integer 0 *) regin))
    (logior (ash (lnfix regin) 2)
            (logand 3 (lnfix slot0))))

  ;; get a particular field by ID
  (definline id->type (id aignet)
    (declare (type (integer 0 *) id)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (< id (num-nodes aignet)))))
    (snode->type (id->slot id 0 aignet)))

  (definline id->phase (id aignet)
    (declare (type (integer 0 *) id)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (< id (num-nodes aignet)))))
    (snode->phase (id->slot id 1 aignet)))

  (definline id->regp (id aignet)
    (declare (type (integer 0 *) id)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (< id (num-nodes aignet)))))
    (snode->regp (id->slot id 1 aignet)))

  (definline id->ionum (id aignet)
    (declare (type (integer 0 *) id)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (< id (num-nodes aignet)))))
    (snode->ionum (id->slot id 1 aignet)))

  (definline id->fanin0 (id aignet)
    (declare (type (integer 0 *) id)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (< id (num-nodes aignet)))))
    (snode->fanin (id->slot id 0 aignet)))

  (definline id->fanin1 (id aignet)
    (declare (type (integer 0 *) id)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (< id (num-nodes aignet)))))
    (snode->fanin (id->slot id 1 aignet)))

  (definline reg-id->nxst (id aignet)
    (declare (type (integer 0 *) id)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (< id (num-nodes aignet)))))
    (snode->regid (id->slot id 0 aignet)))

  (definline nxst-id->reg (id aignet)
    (declare (type (integer 0 *) id)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (< id (num-nodes aignet)))))
    (snode->regid (id->slot id 1 aignet)))

  (definline update-node-slot (id slot val aignet)
    (declare (type (integer 0 *) id)
             (type (integer 0 *) val)
             (type bit slot)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (< id (num-nodes aignet)))))
    (mbe :logic (update-nodesi (+ (bfix slot) (* 2 (lnfix id)))
                              (nfix val) aignet)
         :exec (if (< val (expt 2 32))
                   (update-nodesi (+ slot (* 2 (lnfix id))) val aignet)
                 (ec-call (update-nodesi (+ slot (* 2 (lnfix id))) val
                                         aignet))))))




(defsection maybe-grow-arrays
  ;; Reallocate the array if there isn't room to add an node.
  (definlined maybe-grow-nodes (aignet)
    (declare (xargs :stobjs aignet))
    (let ((target (+ 2 (* 2 (lnfix (num-nodes aignet))))))
      (if (< (nodes-length aignet) target)
          (resize-nodes (max 16 (* 2 target)) aignet)
        aignet)))

  (definlined maybe-grow-ins (aignet)
    (declare (xargs :stobjs aignet))
    (let ((target (+ 1 (lnfix (num-ins aignet)))))
      (if (< (ins-length aignet) target)
          (resize-ins (max 16 (* 2 target)) aignet)
        aignet)))

  (definlined maybe-grow-regs (aignet)
    (declare (xargs :stobjs aignet))
    (let ((target (+ 1 (lnfix (num-regs aignet)))))
      (if (< (regs-length aignet) target)
          (resize-regs (max 16 (* 2 target)) aignet)
        aignet)))

  (definlined maybe-grow-outs (aignet)
    (declare (xargs :stobjs aignet))
    (let ((target (+ 1 (lnfix (num-outs aignet)))))
      (if (< (outs-length aignet) target)
          (resize-outs (max 16 (* 2 target)) aignet)
        aignet))))

;; (define regs-in-bounds ((n natp) aignet)
;;   :guard (and (aignet-sizes-ok aignet)
;;               (<= n (num-regs aignet)))
;;   (if (zp n)
;;       t
;;     (and (< (id-val (regsi (1- n) aignet)) (lnfix (num-nodes aignet)))
;;          (regs-in-bounds (1- n) aignet))))

;; (define aignet-regs-in-bounds (aignet)
;;   :guard (aignet-sizes-ok aignet)
;;   (regs-in-bounds (num-regs aignet) aignet))

(defsection io-accessors/updaters
  (definline set-innum->id (n id aignet)
    (declare (type (integer 0 *) n)
             (type (integer 0 *) id)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (< n (num-ins aignet)))))
    (mbe :logic (non-exec
                 (update-nth *insi*
                             (update-nth n id (nth *insi* aignet))
                             aignet))
         :exec (if (< id (expt 2 32))
                   (update-insi n id aignet)
                 (ec-call (update-insi n id aignet)))))

  
  (definline innum->id (n aignet)
    (declare (type (integer 0 *) n)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (< n (num-ins aignet)))))
    (lnfix (insi n aignet)))

  (definline set-regnum->id (n id aignet)
    (declare (type (integer 0 *) n)
             (type (integer 0 *) id)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (< n (num-regs aignet)))))
    (mbe :logic (non-exec
                 (update-nth *regsi*
                             (update-nth n id (nth *regsi* aignet))
                             aignet))
         :exec (if (< id (expt 2 32))
                   (update-regsi n id aignet)
                 (ec-call (update-regsi n id aignet)))))


  (definline set-outnum->id (n id aignet)
    (declare (type (integer 0 *) n)
             (type (integer 0 *) id)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (< n (num-outs aignet)))))
    (mbe :logic (non-exec
                 (update-nth *outsi*
                             (update-nth n id (nth *outsi* aignet))
                             aignet))
         :exec (if (< id (expt 2 32))
                   (update-outsi n id aignet)
                 (ec-call (update-outsi n id aignet)))))

  (definline outnum->id (n aignet)
    (declare (type (integer 0 *) n)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (< n (num-outs aignet)))))
    (lnfix (outsi n aignet)))


  ;; (definline regnum->ri (n aignet)
  ;;   (declare (type (integer 0 *) n)
  ;;            (xargs :stobjs aignet
  ;;                   :guard (and (aignet-sizes-ok aignet)
  ;;                               (aignet-regs-in-bounds aignet)
  ;;                               (< n (num-regs aignet)))))
  ;;   (b* ((id (lnfix (regsi n aignet))))
  ;;     (if (int= (id->type id aignet) (in-type))
  ;;         (reg-id->nxst id aignet)
  ;;       id)))

  (definline regnum->id (n aignet)
    (declare (type (integer 0 *) n)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                ;; (aignet-regs-in-bounds aignet)
                                (< n (num-regs aignet)))))
    (lnfix (regsi n aignet))))

(definline lit->phase (lit aignet)
  (declare (type (integer 0 *) lit)
           (xargs :stobjs aignet
                  :guard (and (aignet-sizes-ok aignet)
                              (litp lit)
                              (< (lit-id lit)
                                 (num-nodes aignet)))))
  (b-xor (id->phase (lit-id lit) aignet)
         (lit-neg lit)))


(define fanin-litp ((lit litp) aignet)
  :inline t
  :guard (aignet-sizes-ok aignet)
  :enabled t
  (declare (type (integer 0 *) lit))
  (let ((id (lit-id lit)))
    (and (< id (lnfix (num-nodes aignet)))
         (not (int= (id->type id aignet) (out-type))))))


(defsection add-nodes


    (define add-node (aignet)
      :inline t
      (declare (xargs :stobjs aignet
                      :guard (aignet-sizes-ok aignet)))
      (b* ((aignet (maybe-grow-nodes aignet))
           (nodes  (lnfix (num-nodes aignet))))
        (update-num-nodes (+ 1 nodes) aignet)))

    (define add-in (aignet)
      :inline t
      (declare (xargs :stobjs aignet
                      :guard (aignet-sizes-ok aignet)))
      (b* ((aignet (maybe-grow-ins aignet))
           (ins  (lnfix (num-ins aignet))))
        (update-num-ins (+ 1 ins) aignet)))

    (define add-out (aignet)
      :inline t
      (declare (xargs :stobjs aignet
                      :guard (aignet-sizes-ok aignet)))
      (b* ((aignet (maybe-grow-outs aignet))
           (outs  (lnfix (num-outs aignet))))
        (update-num-outs (+ 1 outs) aignet)))

    (define add-reg (aignet)
      :inline t
      (declare (xargs :stobjs aignet
                      :guard (aignet-sizes-ok aignet)))
      (b* ((aignet (maybe-grow-regs aignet))
           (regs  (lnfix (num-regs aignet))))
        (update-num-regs (+ 1 regs) aignet)))

  (defund aignet-add-in (aignet)
    (declare (xargs :stobjs aignet
                    :guard (aignet-sizes-ok aignet)))
    (b* ((pi-num (lnfix (num-ins aignet)))
         (nodes  (lnfix (num-nodes aignet)))
         (aignet (add-node aignet))
         (aignet (add-in aignet))
         (aignet (set-innum->id pi-num nodes aignet))
         ((mv slot0 slot1)
          (mk-snode (in-type) 0 0 0 pi-num))
         (aignet (update-node-slot nodes 0 slot0 aignet))
         (aignet (update-node-slot nodes 1 slot1 aignet)))
      aignet))

  (defund aignet-add-reg (aignet)
    (declare (xargs :stobjs aignet
                    :guard (aignet-sizes-ok aignet)))
    (b* ((ro-num (num-regs aignet))
         (nodes  (num-nodes aignet))
         (aignet (add-reg aignet))
         (aignet (add-node aignet))
         (aignet (set-regnum->id ro-num nodes aignet))
         ((mv slot0 slot1)
          (mk-snode (in-type) 1 0 0 ro-num))
         (aignet (update-node-slot nodes 0 slot0 aignet))
         (aignet (update-node-slot nodes 1 slot1 aignet)))
      aignet))

  (defund aignet-add-gate (f0 f1 aignet)
    (declare (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (litp f0) (litp f1)
                                (< (lit-id f0)
                                   (num-nodes aignet))
                                (not (int= (id->type (lit-id f0) aignet)
                                           (out-type)))
                                (< (lit-id f1)
                                   (num-nodes aignet))
                                (not (int= (id->type (lit-id f1) aignet)
                                           (out-type))))
                    :guard-hints (("goal" :in-theory (e/d (add-node)
                                                          (len-update-nth-linear))))))
    (b* ((nodes  (num-nodes aignet))
         (aignet (add-node aignet))
         (aignet (update-num-gates (+ 1 (lnfix (num-gates aignet))) aignet))
         (phase (b-and (lit->phase f0 aignet)
                       (lit->phase f1 aignet)))
         ((mv slot0 slot1)
          (mk-snode (gate-type) 0 phase (lit-val f0) (lit-val f1)))
         (aignet (update-node-slot nodes 0 slot0 aignet))
         (aignet (update-node-slot nodes 1 slot1 aignet)))
      aignet))

  (defund aignet-add-out (f aignet)
    (declare (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (litp f)
                                (< (lit-id f)
                                   (num-nodes aignet))
                                (not (int= (id->type (lit-id f) aignet)
                                           (out-type))))
                    :guard-hints (("goal" :in-theory (enable add-node
                                                             add-out)))))
    (b* ((nodes  (num-nodes aignet))
         (po-num (num-outs aignet))
         (aignet (add-node aignet))
         (aignet (add-out aignet))
         (phase  (lit->phase f aignet))
         (aignet (set-outnum->id po-num nodes aignet))
         ((mv slot0 slot1)
          (mk-snode (out-type) 0 phase (lit-val f) po-num))
         (aignet (update-node-slot nodes 0 slot0 aignet))
         (aignet (update-node-slot nodes 1 slot1 aignet)))
      aignet))

  (defund aignet-set-nxst (f regid aignet)
    (declare (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (litp f)
                                (< (lit-id f)
                                   (num-nodes aignet))
                                (not (int= (id->type (lit-id f) aignet)
                                           (out-type)))
                                (natp regid)
                                (< regid (num-nodes aignet))
                                (int= (id->type regid aignet)
                                      (in-type))
                                (int= (id->regp regid aignet) 1))
                    :guard-hints ((and stable-under-simplificationp
                                       '(:use aignet-sizes-ok
                                         :in-theory (disable aignet-sizes-ok))))))
    (b* ((nodes  (num-nodes aignet))
         (aignet (add-node aignet))
         (aignet (update-num-nxsts (+ 1 (lnfix (num-nxsts aignet))) aignet))
         (slot0 (id->slot regid 0 aignet))
         (new-slot0 (set-snode->regid nodes slot0))
         (aignet (update-node-slot regid 0 new-slot0 aignet))
         (phase  (lit->phase f aignet))
         ((mv slot0 slot1)
          (mk-snode (out-type) 1 phase (lit-val f) (lnfix regid)))
         (aignet (update-node-slot nodes 0 slot0 aignet))
         (aignet (update-node-slot nodes 1 slot1 aignet)))
      aignet)))



(defsection aignet-init
  ;; Clears the aignet without resizing, unless the node array is size 0.
  (defun aignet-clear (aignet)
    (declare (xargs :stobjs aignet
                    :guard-debug t))
    (b* ((aignet (update-num-ins 0 aignet))
         (aignet (update-num-regs 0 aignet))
         (aignet (update-num-gates 0 aignet))
         (aignet (update-num-nxsts 0 aignet))
         (aignet (update-num-outs 0 aignet))
         (aignet (update-num-nodes 1 aignet))
         (aignet (if (< 1 (nodes-length aignet))
                  aignet
                ;; arbitrary
                (resize-nodes 10 aignet)))
         ;; set up the constant node
         (aignet (update-nodesi 0 0 aignet))
         (aignet (update-nodesi 1 0 aignet)))
      aignet))


  (defun aignet-init (max-outs max-regs max-ins max-nodes aignet)
    (declare (type (integer 0 *) max-outs max-regs max-ins)
             (type (integer 1 *) max-nodes)
             (xargs :stobjs aignet))
    (b* ((max-nodes (mbe :logic (if (< 0 (nfix max-nodes))
                                   max-nodes
                                 1)
                        :exec max-nodes))
         (aignet (resize-nodes (* 2 max-nodes) aignet))
         (aignet (resize-ins (lnfix max-ins) aignet))
         (aignet (resize-outs (lnfix max-outs) aignet))
         (aignet (resize-regs (lnfix max-regs) aignet)))
      (aignet-clear aignet))))


(definline id-existsp (id aignet)
  (declare (xargs :stobjs aignet
                  :guard (natp id)))
  (< (lnfix id) (lnfix (num-nodes aignet))))
