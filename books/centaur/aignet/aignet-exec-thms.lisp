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

(in-package "AIGNET$C")
;; (include-book "centaur/aignet/idp" :dir :system)
(include-book "litp")
(include-book "snodes")
(include-book "std/util/defmvtypes" :dir :system)
(include-book "tools/defmacfun" :dir :system)
(include-book "arithmetic/nat-listp" :dir :system)
(include-book "std/basic/arith-equivs" :dir :system)
(include-book "tools/stobj-frame" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))
(local (in-theory (disable nth update-nth
                           acl2::nfix-when-not-natp
                           resize-list
                           acl2::resize-list-when-empty
                           acl2::make-list-ac-redef
                           ;set::double-containment
                           ;set::sets-are-true-lists
                           make-list-ac)))

(local (in-theory (disable true-listp-update-nth
                           acl2::nth-with-large-index
                           unsigned-byte-p)))

(defmacro const-type () 0)
(defmacro gate-type () 1)
(defmacro in-type () 2)
(defmacro out-type () 3)


(defsection aignet

  (defstobj aignet

    (num-ins     :type (unsigned-byte 29) :initially 0)
    (num-outs    :type (unsigned-byte 29) :initially 0)
    (num-regs    :type (unsigned-byte 29) :initially 0)
    (num-nxsts   :type (unsigned-byte 29) :initially 0)
    ;; num-nodes = the sum of the above + 1 (const)
    (num-nodes   :type (unsigned-byte 29) :initially 1)
    (max-fanin   :type (unsigned-byte 29) :initially 0)

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

  ;; (defun id32-listp (x)
  ;;   (declare (xargs :guard t))
  ;;   (if (atom x)
  ;;       (equal x nil)
  ;;     (and (unsigned-byte-p 32 (car x))
  ;;          (idp (car x))
  ;;          (id32-listp (cdr x)))))

  (defun 32bit-listp (x)
    (declare (xargs :guard t))
    (if (atom x)
        (equal x nil)
      (and (unsigned-byte-p 32 (car x))
           (32bit-listp (cdr x)))))


  (defthm 32bit-listp-of-update-nth
    (implies (and (< (nfix n) (len x))
                  (32bit-listp x)
                  (unsigned-byte-p 32 v))
             (32bit-listp (update-nth n v x)))
    :hints(("Goal" :in-theory (enable update-nth))))

  (defthmd nth-in-32bit-listp
    (implies (and (32bit-listp gates)
                  (< (nfix idx) (len gates)))
             (and (integerp (nth idx gates))
                  (<= 0 (nth idx gates))
                  (natp (nth idx gates))
                  (unsigned-byte-p 32 (nth idx gates))))
    :hints(("Goal" :in-theory (enable nth))))

  (defthm nodesp-is-32bit-listp
    (equal (nodesp x)
           (32bit-listp x)))

  (defthm insp-is-32bit-listp
    (equal (insp x)
           (32bit-listp x)))

  (defthm outsp-is-32bit-listp
    (equal (outsp x)
           (32bit-listp x)))

  (defthm regsp-is-32bit-listp
    (equal (regsp x)
           (32bit-listp x))))

(def-ruleset! aignet-frame-thms nil)

(defmacro def-aignet-frame (fn &key hints)
  `(encapsulate nil
    (local (in-theory (enable* aignet-frame-thms)))
    (acl2::def-stobj-frame ,fn aignet :ruleset aignet-frame-thms
                           ,@(and hints `(:hints ,hints)))))



(defsection aignet-sizes-ok
  (defund aignet-sizes-ok (aignet)
    (declare (xargs :stobjs aignet))
    (and (natp (num-ins aignet))
         (natp (num-regs aignet))
         (natp (num-outs aignet))
         (natp (num-nxsts aignet))
         (posp (num-nodes aignet))
         (natp (max-fanin aignet))
         (< (lnfix (num-ins aignet)) (lnfix (num-nodes aignet)))
         (< (lnfix (num-regs aignet)) (lnfix (num-nodes aignet)))
         (< (lnfix (num-outs aignet)) (lnfix (num-nodes aignet)))
         (< (lnfix (num-nxsts aignet)) (lnfix (num-nodes aignet)))
         (<= (lnfix (num-ins aignet))
             (ins-length aignet))
         (<= (lnfix (num-outs aignet))
             (outs-length aignet))
         (<= (lnfix (num-regs aignet))
             (regs-length aignet))
         (<= (* 2 (lnfix (num-nodes aignet)))
             (nodes-length aignet))
         (unsigned-byte-p 30 (nodes-length aignet))
         (unsigned-byte-p 29 (ins-length aignet))
         (unsigned-byte-p 29 (regs-length aignet))
         (unsigned-byte-p 29 (outs-length aignet))))

  (def-aignet-frame aignet-sizes-ok)

  (local (in-theory (enable aignet-sizes-ok)))

  (defthm aignet-sizes-ok-ins
    (implies (aignet-sizes-ok aignet)
             (<= (nth *num-ins* aignet)
                 (len (nth *insi* aignet))))
    :rule-classes (:rewrite :linear))

  (defthm aignet-sizes-ok-outs
    (implies (aignet-sizes-ok aignet)
             (<= (nth *num-outs* aignet)
                 (len (nth *outsi* aignet))))
    :rule-classes (:rewrite :linear))

  (defthm aignet-sizes-ok-regs
    (implies (aignet-sizes-ok aignet)
             (<= (nth *num-regs* aignet)
                 (len (nth *regsi* aignet))))
    :rule-classes (:rewrite :linear))

  (defthm aignet-sizes-ok-nodes
    (implies (aignet-sizes-ok aignet)
             (<= (* 2 (nth *num-nodes* aignet))
                 (len (nth *nodesi* aignet))))
    :rule-classes (:rewrite :linear))

  ;; (defthm aignet-sizes-ok-max-fanin
  ;;   (implies (aignet-sizes-ok aignet)
  ;;            (< (nth *max-fanin* aignet)
  ;;               (nth *num-nodes* aignet)))
  ;;   :rule-classes (:rewrite :linear))

  (defthm aignet-sizes-ok-posp-num-nodes
    (implies (aignet-sizes-ok aignet)
             (posp (nth *num-nodes* aignet)))
    :rule-classes :type-prescription)

  (defthm aignet-sizes-ok-natp-num-ins
    (implies (aignet-sizes-ok aignet)
             (natp (nth *num-ins* aignet)))
    :rule-classes :type-prescription)

  (defthm aignet-sizes-ok-natp-num-outs
    (implies (aignet-sizes-ok aignet)
             (natp (nth *num-outs* aignet)))
    :rule-classes :type-prescription)

  (defthm aignet-sizes-ok-natp-num-regs
    (implies (aignet-sizes-ok aignet)
             (natp (nth *num-regs* aignet)))
    :rule-classes :type-prescription)

  (defthm aignet-sizes-ok-natp-num-nxsts
    (implies (aignet-sizes-ok aignet)
             (natp (nth *num-nxsts* aignet)))
    :rule-classes :type-prescription)

  (defthm aignet-sizes-ok-natp-num-outs
    (implies (aignet-sizes-ok aignet)
             (natp (nth *num-outs* aignet)))
    :rule-classes :type-prescription)

  (defthm aignet-sizes-ok-natp-max-fanin
    (implies (aignet-sizes-ok aignet)
             (natp (nth *max-fanin* aignet)))
    :rule-classes :type-prescription)

  ;; (defthm aignet-sizes-ok-of-add-in
  ;;   (implies (and (aignet-sizes-ok aignet)
  ;;                 (< (num-ins aignet)
  ;;                    (ins-length aignet))
  ;;                 (equal ins (nth *num-ins* aignet)))
  ;;            (aignet-sizes-ok
  ;;             (update-nth *num-ins*
  ;;                         (+ 1 ins)
  ;;                         aignet))))

  ;; (defthm aignet-sizes-ok-of-add-node
  ;;   (implies (and (aignet-sizes-ok aignet)
  ;;                 (<= (+ 2 (* 2 (nfix (nth *num-nodes* aignet))))
  ;;                     (len (nth *nodesi* aignet)))
  ;;                 (equal nodes (nfix (nth *num-nodes* aignet))))
  ;;            (aignet-sizes-ok
  ;;             (update-nth *num-nodes*
  ;;                         (+ 1 nodes)
  ;;                         aignet))))

  ;; (defthm aignet-sizes-ok-of-add-out
  ;;   (implies (and (aignet-sizes-ok aignet)
  ;;                 (< (num-outs aignet)
  ;;                    (outs-length aignet))
  ;;                 (equal outs (nth *num-outs* Aignet)))
  ;;            (aignet-sizes-ok
  ;;             (update-nth *num-outs*
  ;;                         (+ 1 outs)
  ;;                         aignet))))

  ;; (defthm aignet-sizes-ok-of-add-reg
  ;;   (implies (and (aignet-sizes-ok aignet)
  ;;                 (< (num-regs aignet)
  ;;                    (regs-length aignet))
  ;;                 (equal regs (nth *num-regs* Aignet)))
  ;;            (aignet-sizes-ok
  ;;             (update-nth *num-regs*
  ;;                         (+ 1 regs)
  ;;                         aignet))))

  (defthm aignet-sizes-ok-of-update-arr
    (implies (and (aignet-sizes-ok aignet)
                  (member field (list *outsi*
                                      *insi*
                                      *regsi*))
                  (>= (len fval) (len (nth field aignet)))
                  (< (len fval) (expt 2 29))
                  (< (nfix n) (1- (expt 2 29))))
             (aignet-sizes-ok
              (update-nth field (update-nth n v fval)
                          aignet)))
    :hints(("Goal" :in-theory (enable unsigned-byte-p)
            :do-not-induct t)))

  (defthm aignet-sizes-ok-of-update-nodes
    (implies (and (aignet-sizes-ok aignet)
                  (>= (len fval) (len (nth *nodesi* aignet)))
                  (< (len fval) (expt 2 30))
                  (< (nfix n) (1- (expt 2 30))))
             (aignet-sizes-ok
              (update-nth *nodesi* (update-nth n v fval)
                          aignet)))
    :hints(("Goal" :in-theory (enable unsigned-byte-p))))


  (defthm aignet-sizes-ok-implies-array-length-limit
    (implies (aignet-sizes-ok aignet)
             (and (unsigned-byte-p 30 (len (nth *nodesi* aignet)))
                  (unsigned-byte-p 29 (len (nth *insi* aignet)))
                  (unsigned-byte-p 29 (len (nth *regsi* aignet)))
                  (unsigned-byte-p 29 (len (nth *outsi* aignet))))))

  (defthm aignet-sizes-ok-implies-num-type-bounds
    (implies (aignet-sizes-ok aignet)
             (and (< (nth *num-outs* aignet) (nth *num-nodes* aignet))
                  (< (nth *num-ins* aignet) (nth *num-nodes* aignet))
                  (< (nth *num-regs* aignet) (nth *num-nodes* aignet))
                  (< (nth *num-nxsts* aignet) (nth *num-nodes* aignet))))))

(defsection aignet-lookup-types
  (local (in-theory (enable aignetp aignet-sizes-ok)))
  (defthm lookup-in-aignet-nodes-slot0
    (implies (and (aignetp aignet)
                  (aignet-sizes-ok aignet)
                  (natp n)
                  (< n (nth *num-nodes* aignet)))
             (and (integerp (nth (* 2 n) (nth *nodesi* aignet)))
                  (natp (nth (* 2 n) (nth *nodesi* aignet)))
                  (<= 0 (nth (* 2 n) (nth *nodesi* aignet)))))
    :hints(("Goal" :in-theory (enable nth-in-32bit-listp)))
    :rule-classes (:rewrite :type-prescription))

  (defthm lookup-in-aignet-nodes-slot
    (implies (and (bitp bit)
                  (aignetp aignet)
                  (aignet-sizes-ok aignet)
                  (natp n)
                  (< n (nth *num-nodes* aignet)))
             (and (integerp (nth (+ bit (* 2 n)) (nth *nodesi* aignet)))
                  (natp (nth (+ bit (* 2 n)) (nth *nodesi* aignet)))
                  (<= 0 (nth (+ bit (* 2 n)) (nth *nodesi* aignet)))))
    :hints(("Goal" :in-theory (enable nth-in-32bit-listp)))
    :rule-classes (:rewrite :type-prescription))

  (defthm lookup-in-aignet-ins
    (implies (and (aignetp aignet)
                  (aignet-sizes-ok aignet)
                  (natp n)
                  (< n (nth *num-ins* aignet)))
             (and (integerp (nth n (nth *insi* aignet)))
                  (<= 0 (nth n (nth *insi* aignet)))
                  (unsigned-byte-p 32 (nth n (nth *insi* aignet)))))
    :hints(("Goal" :in-theory (e/d (nth-in-32bit-listp)
                                   (unsigned-byte-p))))
    :rule-classes (:rewrite :type-prescription))

  (defthm lookup-in-aignet-outs
    (implies (and (aignetp aignet)
                  (aignet-sizes-ok aignet)
                  (natp n)
                  (< n (nth *num-outs* aignet)))
             (and (integerp (nth n (nth *outsi* aignet)))
                  (<= 0 (nth n (nth *outsi* aignet)))
                  (unsigned-byte-p 32 (nth n (nth *outsi* aignet)))))
    :hints(("Goal" :in-theory (e/d (nth-in-32bit-listp)
                                   (unsigned-byte-p))))
    :rule-classes (:rewrite :type-prescription))

  (defthm lookup-in-aignet-regs
    (implies (and (aignetp aignet)
                  (aignet-sizes-ok aignet)
                  (natp n)
                  (< n (nth *num-regs* aignet)))
             (and (integerp (nth n (nth *regsi* aignet)))
                  (<= 0 (nth n (nth *regsi* aignet)))
                  (unsigned-byte-p 32 (nth n (nth *regsi* aignet)))))
    :hints(("Goal" :in-theory (e/d (nth-in-32bit-listp)
                                   (unsigned-byte-p))))
    :rule-classes (:rewrite :type-prescription)))

(defsection aignetp-implies
  (defthm aignetp-implies-num-ins
    (implies (aignetp aignet)
             (and (natp (nth *num-ins* aignet))
                  (unsigned-byte-p 29 (nth *num-ins* aignet))))
    :rule-classes (:rewrite (:type-prescription :typed-term (nth *num-ins* aignet))))

  (defthm aignetp-implies-num-outs
    (implies (aignetp aignet)
             (and (natp (nth *num-outs* aignet))
                  (unsigned-byte-p 29 (nth *num-outs* aignet))))
    :rule-classes (:rewrite (:type-prescription :typed-term (nth *num-outs* aignet))))

  (defthm aignetp-implies-num-regs
    (implies (aignetp aignet)
             (and (natp (nth *num-regs* aignet))
                  (unsigned-byte-p 29 (nth *num-regs* aignet))))
    :rule-classes (:rewrite (:type-prescription :typed-term (nth *num-regs* aignet))))

  (defthm aignetp-implies-num-nxsts
    (implies (aignetp aignet)
             (and (natp (nth *num-nxsts* aignet))
                  (unsigned-byte-p 29 (nth *num-nxsts* aignet))))
    :rule-classes (:rewrite (:type-prescription :typed-term (nth *num-nxsts* aignet))))

  (defthm aignetp-implies-num-nodes
    (implies (aignetp aignet)
             (and (natp (nth *num-nodes* aignet))
                  (unsigned-byte-p 29 (nth *num-nodes* aignet))))
    :rule-classes (:rewrite (:type-prescription :typed-term (nth *num-nodes* aignet))))

  (defthm aignetp-implies-max-fanin
    (implies (aignetp aignet)
             (and (natp (nth *max-fanin* aignet))
                  (unsigned-byte-p 29 (nth *max-fanin* aignet))))
    :rule-classes (:rewrite (:type-prescription :typed-term (nth *max-fanin* aignet))))

  (defthm aignetp-implies-num-nodes-limit
    (implies (aignetp aignet)
             (< (nth *num-nodes* aignet) (expt 2 29)))
    :hints(("Goal" :in-theory (enable unsigned-byte-p)))
    :rule-classes :linear))


(in-theory (disable aignetp
                    aignet-sizes-ok))

(local (defthm unsigned-byte-p-of-bit
         (implies (and (bitp x)
                       (posp n))
                  (unsigned-byte-p n x))
         :hints(("Goal" :in-theory (enable unsigned-byte-p bfix)))
         :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))))
                 
(local (defthm unsigned-byte-p-greater-when-32
         (implies (and (syntaxp (quotep n))
                       (natp n)
                       (<= 32 n)
                       (unsigned-byte-p 32 x))
                  (unsigned-byte-p n x))))


(local (defthm unsigned-byte-29-when-less-than-num-nodes
         (implies (and (syntaxp (quotep n))
                       (natp n)
                       (<= 29 n)
                       (< id (nth *num-nodes* aignet))
                       (aignetp aignet)
                       (natp id))
                  (unsigned-byte-p n id))
         :hints(("Goal" :in-theory (enable unsigned-byte-p expt)))))

(local (defthm unsigned-byte-p-of-2x
         (implies (unsigned-byte-p (1- n) x)
                  (unsigned-byte-p n (* 2 x)))
         :hints(("Goal" :in-theory (enable unsigned-byte-p expt)))))

(local (defthm unsigned-byte-p-of-2x+1
         (implies (and (unsigned-byte-p (1- n) x)
                       (bitp bit))
                  (unsigned-byte-p n (+ bit (* 2 x))))
         :hints(("Goal" :in-theory (enable unsigned-byte-p expt)))))

(defsection executable-node-accessors

  ;; Executable accessors.  These come in various levels of granularity for
  ;; convenience.

  ;; get one of the two slots of an node by ID
  (define id->slot ((id natp :type (unsigned-byte 29))
                    (slot bitp :type bit)
                    aignet)
    :guard (and (< id (num-nodes aignet))
                (aignet-sizes-ok aignet))
    :split-types t
    :inline t
    :guard-hints (("goal" :in-theory (enable bitops::ash-is-expt-*-x)))
    (mbe :logic (b* ((id (lnfix id))
                     (slot (acl2::lbfix slot)))
                  (lnfix (nodesi (+ slot (* 2 id)) aignet)))
         :exec (nodesi (the (unsigned-byte 32)
                            (+ (the bit slot)
                               (the (unsigned-byte 32)
                                    (ash (the (unsigned-byte 31) id) 1))))
                       aignet)))

  (local (in-theory (enable id->slot)))

  (def-aignet-frame id->slot)

  (defcong nat-equiv equal (id->slot id slot aignet) 1)
  (defcong bit-equiv equal (id->slot id slot aignet) 2)

  (defthm u32-of-id->slot
    (implies (and (aignetp aignet)
                  (aignet-sizes-ok aignet)
                  (< (nfix id) (num-nodes aignet)))
             (unsigned-byte-p 32 (id->slot id slot aignet)))
    :hints(("Goal" :in-theory (enable aignetp aignet-sizes-ok
                                      nth-in-32bit-listp))))

  (define id->slot0 ((id natp :type (unsigned-byte 29))
                     aignet)
    :inline t
    :enabled t
    :split-types t
    :guard (and (aignet-sizes-ok aignet)
                (< id (num-nodes aignet)))
    :guard-hints (("goal" :in-theory (enable bitops::ash-is-expt-*-x
                                             unsigned-byte-p)))
    (mbe :logic (id->slot id 0 aignet)
         :exec (nodesi (the (unsigned-byte 32)
                            (the (unsigned-byte 32)
                                 (ash (the (unsigned-byte 31) id) 1)))
                       aignet)))

  (define id->slot1 ((id natp :type (unsigned-byte 29))
                     aignet)
    :inline t
    :enabled t
    :split-types t
    :guard (and (aignet-sizes-ok aignet)
                (< id (num-nodes aignet)))
    :guard-hints (("goal" :in-theory (enable bitops::ash-is-expt-*-x
                                             unsigned-byte-p)))
    (mbe :logic (id->slot id 1 aignet)
         :exec (nodesi (the (unsigned-byte 32)
                            (+ 1
                               (the (unsigned-byte 32)
                                    (ash (the (unsigned-byte 31) id) 1))))
                       aignet)))

  (defmacro id->slot$ (id slot aignet)
    (cond ((equal slot 0)
           `(id->slot0 ,id ,aignet))
          ((equal slot 1)
           `(id->slot1 ,id ,aignet))
          (t `(id->slot ,id ,slot ,aignet))))

  (local (in-theory (disable id->slot)))

  (define set-snode->regid ((regin :type (unsigned-byte 30))
                            (slot0 :type (unsigned-byte 32)))
    :inline t
    (mbe :logic (logior (ash (nfix regin) 2)
                        (logand 3 (nfix slot0)))
         :exec (the (unsigned-byte 32)
                    (logior (the (unsigned-byte 32)
                                 (ash (the (unsigned-byte 30) regin) 2))
                            (the (unsigned-byte 2)
                                 (logand 3 (the (unsigned-byte 32) slot0))))))
    ///

    (defthm set-snode->regid-of-mk-snode
      (and (equal (set-snode->regid
                   n (mv-nth 0 (mk-snode type regp phase fanin0 fanin1)))
                  (mv-nth 0 (mk-snode type regp phase n fanin1)))
           (equal (set-snode->regid
                   n (mv-nth 1 (mk-snode type regp phase fanin0 fanin1)))
                  (mv-nth 1 (mk-snode type regp phase fanin0 n))))
      :hints(("Goal" :in-theory (enable mk-snode set-snode->regid))))

    (defthm snode->regid-of-set-snode->regid
      (equal (snode->regid (set-snode->regid regin slot0))
             (nfix regin))
      :hints(("Goal" :in-theory (enable snode->regid
                                        set-snode->regid))))

    (defthm snode->type-of-set-snode->regid
      (equal (snode->type (set-snode->regid regin slot0))
             (snode->type slot0))
      :hints(("Goal" :in-theory (enable snode->type
                                        set-snode->regid))))

    (defthm snode->phase-of-set-snode->regid
      (equal (snode->phase (set-snode->regid regin slot0))
             (snode->phase slot0))
      :hints(("Goal" :in-theory (enable snode->phase
                                        set-snode->regid))))

    (defcong nat-equiv equal (set-snode->regid regin slot0) 2
      :hints(("Goal" :in-theory (enable set-snode->regid)))))

  ;; get a particular field by ID
  (define id->type ((id natp :type (unsigned-byte 29))
                    aignet)
    :inline t
    :enabled t
    :split-types t
    :guard (and (aignet-sizes-ok aignet)
                (< id (num-nodes aignet)))
    :guard-hints (("goal" :in-theory (enable snode->type)))
    (mbe :logic (snode->type (id->slot id 0 aignet))
         :exec (logand 3 (the (unsigned-byte 32) (id->slot$ id 0 aignet)))))

  (define id->phase ((id natp :type (unsigned-byte 29))
                     aignet)
    :inline t
    :enabled t
    :split-types t
    :guard (and (aignet-sizes-ok aignet)
                (< id (num-nodes aignet)))
    :guard-hints (("goal" :in-theory (enable snode->phase)))
    (mbe :logic (snode->phase (id->slot id 1 aignet))
         :exec (logand 1 (the (unsigned-byte 32)
                              (ash (the (unsigned-byte 32) (id->slot$ id 1 aignet)) -1)))))

  (define id->regp ((id natp :type (unsigned-byte 29))
                    aignet)
    :inline t
    :enabled t
    :split-types t
    :guard (and (aignet-sizes-ok aignet)
                (< id (num-nodes aignet)))
    :guard-hints (("goal" :in-theory (enable snode->regp)))
    (mbe :logic (snode->regp (id->slot id 1 aignet))
         :exec (logand 1 (the (unsigned-byte 32) (id->slot$ id 1 aignet)))))

  (define id->ionum ((id natp :type (unsigned-byte 29))
                     aignet)
    :inline t
    :enabled t
    :split-types t
    :guard (and (aignet-sizes-ok aignet)
                (< id (num-nodes aignet)))
    :guard-hints (("goal" :in-theory (enable snode->ionum)))
    (mbe :logic (snode->ionum (id->slot id 1 aignet))
         :exec (ash (the (unsigned-byte 32) (id->slot$ id 1 aignet)) -2)))

  (define id->fanin0 ((id natp :type (unsigned-byte 29))
                      aignet)
    :inline t
    :enabled t
    :split-types t
    :guard (and (aignet-sizes-ok aignet)
                (< id (num-nodes aignet)))
    :guard-hints (("goal" :in-theory (enable snode->fanin)))
    (mbe :logic (snode->fanin (id->slot id 0 aignet))
         :exec (ash (the (unsigned-byte 32) (id->slot$ id 0 aignet)) -2)))

  (define id->fanin1 ((id natp :type (unsigned-byte 29))
                      aignet)
    :inline t
    :enabled t
    :split-types t
    :guard (and (aignet-sizes-ok aignet)
                (< id (num-nodes aignet)))
    :guard-hints(("Goal" :in-theory (enable snode->fanin)))
    (mbe :logic (snode->fanin (id->slot id 1 aignet))
         :exec (ash (the (unsigned-byte 32) (id->slot$ id 1 aignet)) -2)))

  (define reg-id->nxst ((id natp :type (unsigned-byte 29))
                        aignet)
    :inline t
    :enabled t
    :split-types t
    :guard (and (aignet-sizes-ok aignet)
                (< id (num-nodes aignet)))
    :guard-hints (("goal" :in-theory (enable snode->regid)))
    (mbe :logic (snode->regid (id->slot id 0 aignet))
         :exec (ash (the (unsigned-byte 32) (id->slot$ id 0 aignet)) -2)))

  (define nxst-id->reg ((id natp :type (unsigned-byte 29))
                        aignet)
    :inline t
    :enabled t
    :split-types t
    :guard (and (aignet-sizes-ok aignet)
                (< id (num-nodes aignet)))
    :guard-hints (("goal" :in-theory (enable snode->regid)))
    (mbe :logic (snode->regid (id->slot id 1 aignet))
         :exec (ash (the (unsigned-byte 32) (id->slot$ id 1 aignet)) -2)))

  (define update-node-slot ((id natp :type (unsigned-byte 29))
                            (slot bitp :type bit)
                            (val (unsigned-byte-p 32 val) :type (unsigned-byte 32))
                            aignet)
    :inline t
    :split-types t
    :guard (and (aignet-sizes-ok aignet)
                (< id (num-nodes aignet)))
    :guard-hints (("goal" :in-theory (enable bitops::ash-is-expt-*-x)))
    (mbe :logic (update-nodesi (+ (bfix slot) (* 2 (lnfix id)))
                               (nfix val) aignet)
         :exec (b* ((idx (the (unsigned-byte 32)
                              (+ (the bit slot)
                                 (the (unsigned-byte 32)
                                      (ash (the (unsigned-byte 31) (lnfix id)) 1))))))
                 (update-nodesi idx val aignet)))
    ///

    (define update-node-slot0 ((id natp :type (unsigned-byte 29))
                               (val (unsigned-byte-p 32 val) :type (unsigned-byte 32))
                               aignet)
      :inline t
      :split-types t
      :enabled t
      :guard (and (aignet-sizes-ok aignet)
                  (< id (num-nodes aignet)))
      :guard-hints (("goal" :in-theory (enable update-node-slot
                                               bitops::ash-is-expt-*-x)))
      (mbe :logic (update-node-slot id 0 val aignet)
           :exec (b* ((idx (the (unsigned-byte 32)
                                (ash (the (unsigned-byte 31) (lnfix id)) 1))))
                   (update-nodesi idx val aignet))))

    (define update-node-slot1 ((id natp :type (unsigned-byte 29))
                               (val (unsigned-byte-p 32 val) :type (unsigned-byte 32))
                               aignet)
      :inline t
      :split-types t
      :enabled t
      :guard (and (aignet-sizes-ok aignet)
                  (< id (num-nodes aignet)))
      :guard-hints (("goal" :in-theory (enable update-node-slot
                                               bitops::ash-is-expt-*-x)))
      (mbe :logic (update-node-slot id 1 val aignet)
           :exec (b* ((idx (the (unsigned-byte 32)
                                (+ 1
                                   (the (unsigned-byte 32)
                                        (ash (the (unsigned-byte 31) (lnfix id)) 1))))))
                   (update-nodesi idx val aignet))))

    (defmacro update-node-slot$ (id slot val aignet)
      (cond ((equal slot 0)
             `(update-node-slot0 ,id ,val ,aignet))
            ((equal slot 1)
             `(update-node-slot1 ,id ,val ,aignet))
            (t `(update-node-slot ,id ,slot ,val ,aignet))))



    (local (in-theory (enable update-node-slot)))

    (def-aignet-frame update-node-slot)

    (local (defthm even-is-not-odd
             (implies (and (integerp a) (integerp b))
                      (not (equal (+ 1 (* 2 a)) (* 2 b))))
             :hints (("goal" :use ((:theorem
                                    (implies
                                     (and (integerp a)
                                          (integerp b))
                                     (not (equal (acl2::logcar (+ 1 (* 2 a)))
                                                 (acl2::logcar (* 2 b)))))))))))

    (defthm id->slot-of-update-node-slot
      (equal (id->slot id1 slot1 (update-node-slot id2 slot2 val2 aignet))
             (if (and (equal (nfix id1) (nfix id2))
                      (equal (bfix slot1) (bfix slot2)))
                 (nfix val2)
               (id->slot id1 slot1 aignet)))
      :hints(("Goal" :in-theory (enable bfix id->slot))))

    (defthm len-of-update-node-slot
      (<= (len (nth *nodesi* aignet))
          (len (nth *nodesi* (update-node-slot id slot val aignet))))
      :rule-classes :linear)

    (defcong nat-equiv equal (update-node-slot id slot val aignet) 1)
    (defcong bit-equiv equal (update-node-slot id slot val aignet) 2)
    (defcong nat-equiv equal (update-node-slot id slot val aignet) 3)))




(defsection maybe-grow-arrays
  (local (in-theory (enable acl2::nth-of-resize-list-split
                            ;; acl2::nth-with-large-index
                            )))
  (local (in-theory (enable aignetp)))
  (local (in-theory (disable aignetp-implies-num-nodes
                             len)))

  (local (defthm unsigned-byte-p-when-less
           (implies (and (syntaxp (quotep n))
                         (natp n)
                         (natp x)
                         (< x (expt 2 n)))
                    (unsigned-byte-p n x))
           :hints(("Goal" :in-theory (enable unsigned-byte-p)))))

  ;; Reallocate the array if there isn't room to add an node.
  (define maybe-grow-nodes (aignet)
    :guard (and (< (num-nodes aignet) #x1fffffff)
                (aignet-sizes-ok aignet))
    :inline t
    :guard-hints (("goal" :do-not-induct t
                   :in-theory (enable bitops::ash-is-expt-*-x)))
    ;; Plus 2 to ensure there's room to add a node.
    (mbe :logic (let ((target (+ 2 (* 2 (lnfix (num-nodes aignet))))))
                  (if (< (nodes-length aignet) target)
                      (if (< (nodes-length aignet) #x3fffffff)
                          (resize-nodes (min #x3fffffff
                                             (max 16 (* 2 target)))
                                        aignet)
                        aignet)
                    aignet))
         :exec (b* ((target (the (unsigned-byte 30)
                                 (+ 2
                                    (the (unsigned-byte 30)
                                         (ash (the (unsigned-byte 29)
                                                   (num-nodes aignet))
                                              1)))))
                    ((unless (< (the (unsigned-byte 30) (nodes-length aignet))
                                (the (unsigned-byte 30) target)))
                     aignet)
                    (new-size (the (unsigned-byte 30)
                                   (min #x3fffffff
                                        (the (unsigned-byte 31)
                                             (max 16
                                                  (the (unsigned-byte 31)
                                                       (ash (the (unsigned-byte 30) target) 1))))))))
                 (resize-nodes (the (unsigned-byte 30) new-size) aignet)))
    ///

    (local (in-theory (enable maybe-grow-nodes)))

    (def-aignet-frame maybe-grow-nodes)

    (defthm nth-of-maybe-grow-nodes
      (nat-equiv (nth id (nth *nodesi* (maybe-grow-nodes aignet)))
                 (nth id (nth *nodesi* aignet)))
      :hints(("Goal" :in-theory (enable acl2::nth-with-large-index))))

    (defthm id->slot-of-maybe-grow-nodes
      (equal (id->slot id slot (maybe-grow-nodes aignet))
             (id->slot id slot aignet))
      :hints(("Goal" :in-theory (e/d (id->slot)
                                     (maybe-grow-nodes)))))


    (defthm len-nodes-of-maybe-grow-nodes
      (implies (< (nfix (num-nodes aignet)) #x1fffffff)
               (<= (+ 2 (* 2 (nfix (nth *num-nodes* aignet))))
                   (len (nth *nodesi* (maybe-grow-nodes aignet)))))
      :rule-classes ((:rewrite)
                     (:linear :trigger-terms
                      ((len (nth *nodesi* (maybe-grow-nodes aignet)))))))

    (defthm aignet-sizes-ok-of-maybe-grow-nodes
      (implies (aignet-sizes-ok aignet)
               (aignet-sizes-ok (maybe-grow-nodes aignet)))
      :hints((and stable-under-simplificationp
                  `(:expand (,(car (last clause)))))))

    (defthm len-of-maybe-grow-nodes
      (<= (len aignet) (len (maybe-grow-nodes aignet)))
      :rule-classes :linear)

    (defthm len-of-maybe-grow-nodes-increased
      (<= (len (nth n aignet))
          (len (nth n (maybe-grow-nodes aignet))))
      :rule-classes ((:linear :trigger-terms
                      ((len (nth n (maybe-grow-nodes aignet)))))))

    (defthm 32bit-listp-of-resize-list
      (implies (and (32bit-listp x)
                    (unsigned-byte-p 32 d))
               (32bit-listp (resize-list x n d)))
      :hints(("Goal" :in-theory (enable resize-list
                                        32bit-listp))))

    (defthm aignetp-of-maybe-grow-nodes
      (implies (aignetp aignet)
               (aignetp (maybe-grow-nodes aignet)))))

  (define maybe-grow-ins (aignet)
    :guard (and (< (num-ins aignet) #x1ffffffe)
                (aignet-sizes-ok aignet))
    :inline t
    :guard-hints (("goal" :do-not-induct t
                   :in-theory (enable bitops::ash-is-expt-*-x)))
    :prepwork ((local (defthm aignet-sizes-ok-implies-num-ins-less
                        (implies (aignet-sizes-ok aignet)
                                 (< (nth *num-ins* aignet) (nth *num-nodes* aignet)))
                        :rule-classes :linear)))
    (mbe :logic (let ((target (+ 1 (nfix (num-ins aignet)))))
                  (if (< (ins-length aignet) target)
                      (if (< (ins-length aignet) #x1fffffff)
                          (resize-ins (min #x1fffffff
                                           (max 16 (* 2 target)))
                                      aignet)
                        aignet)
                    aignet))
         :exec (b* ((target (the (unsigned-byte 29)
                                 (+ 1
                                    (the (unsigned-byte 29) (num-ins aignet)))))
                    ((unless (< (the (unsigned-byte 29) (ins-length aignet))
                                (the (unsigned-byte 29) target)))
                     aignet)
                    (new-size (the (unsigned-byte 29)
                                   (min #x1fffffff
                                        (the (unsigned-byte 30)
                                             (max 16
                                                  (the (unsigned-byte 30)
                                                       (ash (the (unsigned-byte 29) target) 1))))))))
                 (resize-ins (the (unsigned-byte 30) new-size) aignet)))
    ///
    (def-aignet-frame maybe-grow-ins)

    (defthm nth-in-of-maybe-grow-ins
      (nat-equiv (nth n (nth *insi* (maybe-grow-ins aignet)))
                 (nth n (nth *insi* aignet)))
      :hints(("Goal" :in-theory (enable acl2::nth-with-large-index))))

    (defthm id->slot-of-maybe-grow-ins
      (equal (id->slot id slot (maybe-grow-ins aignet))
             (id->slot id slot aignet))
      :hints(("Goal" :in-theory (enable* aignet-frame-thms))))

    (defthm len-ins-of-maybe-grow-ins
      (implies (and (aignet-sizes-ok aignet)
                    (< (nfix (num-nodes aignet)) #x1fffffff))
               (<= (+ 1 (nfix (nth *num-ins* aignet)))
                   (len (nth *insi* (maybe-grow-ins aignet)))))
      :rule-classes ((:linear :trigger-terms
                      ((len (nth *insi* (maybe-grow-ins aignet)))))))

    (defthm len-of-maybe-grow-ins-increased
      (<= (len (nth n aignet))
          (len (nth n (maybe-grow-ins aignet))))
      :rule-classes ((:linear :trigger-terms
                      ((len (nth n (maybe-grow-ins aignet)))))))

    (defthm aignet-sizes-ok-of-maybe-grow-ins
      (implies (aignet-sizes-ok aignet)
               (aignet-sizes-ok (maybe-grow-ins aignet)))
      :hints((and stable-under-simplificationp
                  `(:expand (,(car (last clause)))))))

    (defthm len-of-maybe-grow-ins
      (<= (len aignet) (len (maybe-grow-ins aignet)))
      :rule-classes :linear)

    (defthm 32bit-listp-of-resize-list
      (implies (and (32bit-listp x)
                    (unsigned-byte-p 32 d))
               (32bit-listp (resize-list x n d)))
      :hints(("Goal" :in-theory (enable resize-list
                                        32bit-listp))))

    (defthm aignetp-of-maybe-grow-ins
      (implies (aignetp aignet)
               (aignetp (maybe-grow-ins aignet)))))

  (define maybe-grow-regs (aignet)
    :guard (and (< (num-regs aignet) #x1ffffffe)
                (aignet-sizes-ok aignet))
    :inline t
    :guard-hints (("goal" :do-not-induct t
                   :in-theory (enable bitops::ash-is-expt-*-x)))
    :prepwork ((local (defthm aignet-sizes-ok-implies-num-regs-less
                        (implies (aignet-sizes-ok aignet)
                                 (< (nth *num-regs* aignet) (nth *num-nodes* aignet)))
                        :rule-classes :linear)))
    (mbe :logic (let ((target (+ 1 (nfix (num-regs aignet)))))
                  (if (< (regs-length aignet) target)
                      (if (< (regs-length aignet) #x1fffffff)
                          (resize-regs (min #x1fffffff
                                           (max 16 (* 2 target)))
                                      aignet)
                        aignet)
                    aignet))
         :exec (b* ((target (the (unsigned-byte 29)
                                 (+ 1
                                    (the (unsigned-byte 29) (num-regs aignet)))))
                    ((unless (< (the (unsigned-byte 29) (regs-length aignet))
                                (the (unsigned-byte 29) target)))
                     aignet)
                    (new-size (the (unsigned-byte 29)
                                   (min #x1fffffff
                                        (the (unsigned-byte 30)
                                             (max 16
                                                  (the (unsigned-byte 30)
                                                       (ash (the (unsigned-byte 29) target) 1))))))))
                 (resize-regs (the (unsigned-byte 30) new-size) aignet)))
    ///
    (def-aignet-frame maybe-grow-regs)

    (defthm nth-in-of-maybe-grow-regs
      (nat-equiv (nth n (nth *regsi* (maybe-grow-regs aignet)))
                 (nth n (nth *regsi* aignet)))
      :hints(("Goal" :in-theory (enable acl2::nth-with-large-index))))

    (defthm id->slot-of-maybe-grow-regs
      (equal (id->slot id slot (maybe-grow-regs aignet))
             (id->slot id slot aignet))
      :hints(("Goal" :in-theory (enable* aignet-frame-thms))))

    (defthm len-regs-of-maybe-grow-regs
      (implies (and (aignet-sizes-ok aignet)
                    (< (nfix (num-nodes aignet)) #x1fffffff))
               (<= (+ 1 (nfix (nth *num-regs* aignet)))
                   (len (nth *regsi* (maybe-grow-regs aignet)))))
      :rule-classes ((:linear :trigger-terms
                      ((len (nth *regsi* (maybe-grow-regs aignet)))))))

    (defthm len-of-maybe-grow-regs-increased
      (<= (len (nth n aignet))
          (len (nth n (maybe-grow-regs aignet))))
      :rule-classes ((:linear :trigger-terms
                      ((len (nth n (maybe-grow-regs aignet)))))))

    (defthm aignet-sizes-ok-of-maybe-grow-regs
      (implies (aignet-sizes-ok aignet)
               (aignet-sizes-ok (maybe-grow-regs aignet)))
      :hints((and stable-under-simplificationp
                  `(:expand (,(car (last clause)))))))

    (defthm len-of-maybe-grow-regs
      (<= (len aignet) (len (maybe-grow-regs aignet)))
      :rule-classes :linear)

    (defthm 32bit-listp-of-resize-list
      (implies (and (32bit-listp x)
                    (unsigned-byte-p 32 d))
               (32bit-listp (resize-list x n d)))
      :hints(("Goal" :in-theory (enable resize-list
                                        32bit-listp))))

    (defthm aignetp-of-maybe-grow-regs
      (implies (aignetp aignet)
               (aignetp (maybe-grow-regs aignet)))))

  (define maybe-grow-outs (aignet)
    :guard (and (< (num-outs aignet) #x1ffffffe)
                (aignet-sizes-ok aignet))
    :inline t
    :guard-hints (("goal" :do-not-induct t
                   :in-theory (enable bitops::ash-is-expt-*-x)))
    :prepwork ((local (defthm aignet-sizes-ok-implies-num-outs-less
                        (implies (aignet-sizes-ok aignet)
                                 (< (nth *num-outs* aignet) (nth *num-nodes* aignet)))
                        :rule-classes :linear)))
    (mbe :logic (let ((target (+ 1 (nfix (num-outs aignet)))))
                  (if (< (outs-length aignet) target)
                      (if (< (outs-length aignet) #x1fffffff)
                          (resize-outs (min #x1fffffff
                                           (max 16 (* 2 target)))
                                      aignet)
                        aignet)
                    aignet))
         :exec (b* ((target (the (unsigned-byte 29)
                                 (+ 1
                                    (the (unsigned-byte 29) (num-outs aignet)))))
                    ((unless (< (the (unsigned-byte 29) (outs-length aignet))
                                (the (unsigned-byte 29) target)))
                     aignet)
                    (new-size (the (unsigned-byte 29)
                                   (min #x1fffffff
                                        (the (unsigned-byte 30)
                                             (max 16
                                                  (the (unsigned-byte 30)
                                                       (ash (the (unsigned-byte 29) target) 1))))))))
                 (resize-outs (the (unsigned-byte 30) new-size) aignet)))
    ///
    (def-aignet-frame maybe-grow-outs)

    (defthm nth-in-of-maybe-grow-outs
      (nat-equiv (nth n (nth *outsi* (maybe-grow-outs aignet)))
                 (nth n (nth *outsi* aignet)))
      :hints(("Goal" :in-theory (enable acl2::nth-with-large-index))))

    (defthm id->slot-of-maybe-grow-outs
      (equal (id->slot id slot (maybe-grow-outs aignet))
             (id->slot id slot aignet))
      :hints(("Goal" :in-theory (enable* aignet-frame-thms))))

    (defthm len-outs-of-maybe-grow-outs
      (implies (and (aignet-sizes-ok aignet)
                    (< (nfix (num-nodes aignet)) #x1fffffff))
               (<= (+ 1 (nfix (nth *num-outs* aignet)))
                   (len (nth *outsi* (maybe-grow-outs aignet)))))
      :rule-classes ((:linear :trigger-terms
                      ((len (nth *outsi* (maybe-grow-outs aignet)))))))

    (defthm len-of-maybe-grow-outs-increased
      (<= (len (nth n aignet))
          (len (nth n (maybe-grow-outs aignet))))
      :rule-classes ((:linear :trigger-terms
                      ((len (nth n (maybe-grow-outs aignet)))))))

    (defthm aignet-sizes-ok-of-maybe-grow-outs
      (implies (aignet-sizes-ok aignet)
               (aignet-sizes-ok (maybe-grow-outs aignet)))
      :hints((and stable-under-simplificationp
                  `(:expand (,(car (last clause)))))))

    (defthm len-of-maybe-grow-outs
      (<= (len aignet) (len (maybe-grow-outs aignet)))
      :rule-classes :linear)

    (defthm 32bit-listp-of-resize-list
      (implies (and (32bit-listp x)
                    (unsigned-byte-p 32 d))
               (32bit-listp (resize-list x n d)))
      :hints(("Goal" :in-theory (enable resize-list
                                        32bit-listp))))

    (defthm aignetp-of-maybe-grow-outs
      (implies (aignetp aignet)
               (aignetp (maybe-grow-outs aignet))))))

;; (define regs-in-bounds ((n natp) aignet)
;;   :guard (and (aignet-sizes-ok aignet)
;;               (<= n (num-regs aignet)))
;;   (if (zp n)
;;       t
;;     (and (< (id-val (regsi (1- n) aignet)) (lnfix (num-nodes aignet)))
;;          (regs-in-bounds (1- n) aignet)))
;;   ///
;;   (defthm regs-in-bounds-implies
;;     (implies (and (regs-in-bounds n aignet)
;;                   (< (nfix m) (nfix n)))
;;              (< (id-val (nth m (nth *regsi* aignet)))
;;                 (nfix (num-nodes aignet))))
;;     :rule-classes ((:linear :trigger-terms
;;                     ((id-val (nth m (nth *regsi* aignet)))))))
;;   (def-aignet-frame regs-in-bounds))

;; (define aignet-regs-in-bounds (aignet)
;;   :guard (aignet-sizes-ok aignet)
;;   (regs-in-bounds (num-regs aignet) aignet)
;;   ///
;;   (def-aignet-frame aignet-regs-in-bounds)
;;   (defthm aignet-regs-in-bounds-implies
;;     (implies (and (aignet-regs-in-bounds aignet)
;;                   (< (nfix m) (nfix (num-regs aignet))))
;;              (< (id-val (nth m (nth *regsi* aignet)))
;;                 (nfix (num-nodes aignet))))
;;     :rule-classes ((:linear :trigger-terms
;;                     ((id-val (nth m (nth *regsi* aignet))))))))

(defsection io-accessors/updaters

  (defthm unsigned-byte-when-less-than-num-ins
    (implies (and (< n (nth *num-ins* aignet))
                  (aignet-sizes-ok aignet)
                  (natp n))
             (unsigned-byte-p 29 n))
    :hints(("Goal" :in-theory (enable aignet-sizes-ok unsigned-byte-p))))

  (define set-innum->id ((n natp :type (unsigned-byte 29))
                         (id natp :type (unsigned-byte 29))
                         aignet)
    :guard (and (aignet-sizes-ok aignet)
                (< n (num-ins aignet))
                (< id (num-nodes aignet)))
    :inline t
    :enabled t
    :split-types t
    (mbe :logic (non-exec
                 (update-nth *insi*
                             (update-nth n id (nth *insi* aignet))
                             aignet))
         :exec (update-insi n id aignet)))

  (define innum->id ((n natp :type (unsigned-byte 29))
                     aignet)
    :inline t
    :split-types t
    :enabled t
    :guard (and (aignet-sizes-ok aignet)
                (< n (num-ins aignet)))
    (lnfix (insi n aignet)))

  (defthm unsigned-byte-when-less-than-num-regs
    (implies (and (< n (nth *num-regs* aignet))
                  (aignet-sizes-ok aignet)
                  (natp n))
             (unsigned-byte-p 29 n))
    :hints(("Goal" :in-theory (enable aignet-sizes-ok unsigned-byte-p))))

  (define set-regnum->id ((n natp :type (unsigned-byte 29))
                         (id natp :type (unsigned-byte 29))
                         aignet)
    :guard (and (aignet-sizes-ok aignet)
                (< n (num-regs aignet))
                (< id (num-nodes aignet)))
    :inline t
    :enabled t
    :split-types t
    (mbe :logic (non-exec
                 (update-nth *regsi*
                             (update-nth n id (nth *regsi* aignet))
                             aignet))
         :exec (update-regsi n id aignet)))

  (define regnum->id ((n natp :type (unsigned-byte 29))
                     aignet)
    :inline t
    :split-types t
    :enabled t
    :guard (and (aignet-sizes-ok aignet)
                (< n (num-regs aignet)))
    (lnfix (regsi n aignet)))

  (defthm unsigned-byte-when-less-than-num-outs
    (implies (and (< n (nth *num-outs* aignet))
                  (aignet-sizes-ok aignet)
                  (natp n))
             (unsigned-byte-p 29 n))
    :hints(("Goal" :in-theory (enable aignet-sizes-ok unsigned-byte-p))))

  (define set-outnum->id ((n natp :type (unsigned-byte 29))
                         (id natp :type (unsigned-byte 29))
                         aignet)
    :guard (and (aignet-sizes-ok aignet)
                (< n (num-outs aignet))
                (< id (num-nodes aignet)))
    :inline t
    :enabled t
    :split-types t
    (mbe :logic (non-exec
                 (update-nth *outsi*
                             (update-nth n id (nth *outsi* aignet))
                             aignet))
         :exec (update-outsi n id aignet)))

  (define outnum->id ((n natp :type (unsigned-byte 29))
                     aignet)
    :inline t
    :split-types t
    :enabled t
    :guard (and (aignet-sizes-ok aignet)
                (< n (num-outs aignet)))
    (lnfix (outsi n aignet))))

(local (defthm unsigned-byte-30-of-lit
         (implies (and (unsigned-byte-p 29 (lit-id lit))
                       (litp lit)
                       (natp n)
                       (<= 30 n))
                  (unsigned-byte-p n lit))
         :hints(("Goal" :in-theory (enable lit-id)))))
         

(define lit->phase ((lit litp :type (unsigned-byte 30))
                    aignet)
  :split-types t
  :inline t
  :guard (and (aignet-sizes-ok aignet)
              (< (lit-id lit)
                 (num-nodes aignet)))
  (b-xor (id->phase (lit->var^ lit) aignet)
         (lit->neg^ lit)))


(define fanin-litp ((lit litp) aignet)
  :inline t
  :guard (aignet-sizes-ok aignet)
  :enabled t
  (declare (type (integer 0 *) lit))
  (let ((id (lit-id lit)))
    (and (< id (lnfix (num-nodes aignet)))
         (not (int= (id->type id aignet) (out-type))))))


(define count-nodes ((n natp) (type natp) (regp bitp) aignet)
  :guard (and (aignet-sizes-ok aignet)
              (<= n (num-nodes aignet)))
  :measure (nfix (- (nfix (num-nodes aignet)) (nfix n)))
  :returns (count natp :rule-classes :type-prescription)
  (b* (((when (zp (- (nfix (num-nodes aignet)) (nfix n))))
        0)
       (n-type (id->type n aignet))
       (n-regp (id->regp n aignet)))
    (+ (if (and (eql n-type type)
                (eql n-regp regp))
           1
         0)
       (count-nodes (+ 1 (lnfix n)) type regp aignet)))
  ///
  (def-aignet-frame count-nodes)

  (local (in-theory (enable* aignet-frame-thms)))

  (defthm count-nodes-of-incr-num-nodes
    (implies (and (equal nn (nfix (nth *num-nodes* aignet)))
                  (< (nfix n) (nfix (nth *num-nodes* aignet))))
             (equal (count-nodes n type regp
                                 (update-nth *num-nodes*
                                             (+ 1 nn)
                                             aignet))
                    (+ (if (and (equal (id->type (nth *num-nodes* aignet) aignet) type)
                                (equal (id->regp (nth *num-nodes* aignet) aignet) regp))
                           1
                         0)
                       (count-nodes n type regp aignet))))
    :hints (("goal" :induct (count-nodes n type regp aignet)
             :expand ((:free (aignet) (count-nodes n type regp aignet))))))

  (defthm count-nodes-of-update-past
    (implies (<= (num-nodes aignet) (nfix m))
             (equal (count-nodes n type regp (update-node-slot m slot val aignet))
                    (count-nodes n type regp aignet)))
    :hints (("goal" :induct (count-nodes n type regp aignet)
             :expand ((:free (aignet) (count-nodes n type regp aignet))))))

  (defthm count-nodes-of-maybe-grow-ins
    (equal (count-nodes n type regp (maybe-grow-ins aignet))
           (count-nodes n type regp aignet))
    :hints(("Goal" :in-theory (enable maybe-grow-ins))))

  (defthm count-nodes-of-maybe-grow-regs
    (equal (count-nodes n type regp (maybe-grow-regs aignet))
           (count-nodes n type regp aignet))
    :hints(("Goal" :in-theory (enable maybe-grow-regs))))

  (defthm count-nodes-of-maybe-grow-outs
    (equal (count-nodes n type regp (maybe-grow-outs aignet))
           (count-nodes n type regp aignet))
    :hints(("Goal" :in-theory (enable maybe-grow-outs))))

  (defthm count-nodes-of-maybe-grow-nodes
    (equal (count-nodes n type regp (maybe-grow-nodes aignet))
           (count-nodes n type regp aignet)))
  
  (defthm count-nodes-of-update-regid
    (implies (equal (id->slot regid 0 aignet1) (id->slot regid 0 aignet))
             (equal (count-nodes n type regp
                                 (update-node-slot regid 0
                                                   (set-snode->regid nxst
                                                                     (id->slot regid 0 aignet1))
                                                   aignet))
                    (count-nodes n type regp aignet))))

  (defthm count-nodes-of-decr-num-nodes
    (implies (and (equal nn (nfix (nth *num-nodes* aignet)))
                  (< (nfix n) (nfix (nth *num-nodes* aignet))))
             (equal (count-nodes n type regp
                                 (update-nth *num-nodes*
                                             (+ -1 nn)
                                             aignet))
                    (+ (if (and (equal (id->type (+ -1 (nfix (nth *num-nodes* aignet))) aignet) type)
                                (equal (id->regp (+ -1 (nfix (nth *num-nodes* aignet))) aignet) regp))
                           -1
                         0)
                       (count-nodes n type regp aignet))))
    :hints (("goal" :induct (count-nodes n type regp aignet)
             :expand ((:free (aignet) (count-nodes n type regp aignet))))))

  (defthm count-nodes-posp-when-node-exists
    (implies (and (equal (snode->regp (id->slot m 1 aignet)) regp)
                  (equal (snode->type (id->slot m 0 aignet)) type)
                  (<= (nfix n) (nfix m))
                  (< (nfix m) (nfix (num-nodes aignet))))
             (< 0 (count-nodes n type regp aignet)))
    :rule-classes :linear)

  (defthmd regp-when-count-nodes-equal-0
    (implies (and (equal (count-nodes n type regp aignet) 0)
                  (bitp regp)
                  (<= (nfix n) (nfix m))
                  (< (nfix m) (nfix (num-nodes aignet)))
                  (equal (id->type m aignet) type))
             (equal (snode->regp (id->slot m 1 aignet))
                    (b-not regp)))
    :hints(("Goal" :in-theory (enable b-not)))))
                    

(define aignet-counts-accurate (aignet)
  :guard (aignet-sizes-ok aignet)
  (and (eql (nfix (num-ins aignet)) (count-nodes 0 (in-type) 0 aignet))
       (eql (nfix (num-regs aignet)) (count-nodes 0 (in-type) 1 aignet))
       (eql (nfix (num-outs aignet)) (count-nodes 0 (out-type) 0 aignet))
       (eql (nfix (num-nxsts aignet)) (count-nodes 0 (out-type) 1 aignet)))
  ///
    


  ;; (defthm aignet-counts-accurate-rw
  ;;   (implies (aignet-counts-accurate aignet)
  ;;            (and (nat-equiv (nth *num-ins* aignet) (count-nodes 0 (in-type) 0 aignet))
  ;;                 (nat-equiv (nth *num-regs* aignet) (count-nodes 0 (in-type) 1 aignet))
  ;;                 (nat-equiv (nth *num-outs* aignet) (count-nodes 0 (out-type) 0 aignet))
  ;;                 (nat-equiv (nth *num-nxsts* aignet) (count-nodes 0 (out-type) 1 aignet)))))

  ;; (defthm aignet-counts-accurate-rw-natp
  ;;   (implies (aignet-counts-accurate aignet)
  ;;            (and (implies (natp (num-ins aignet))
  ;;                          (equal (nth *num-ins* aignet) (count-nodes 0 (in-type) 0 aignet)))
  ;;                 (implies (natp (num-regs aignet))
  ;;                          (equal (nth *num-regs* aignet) (count-nodes 0 (in-type) 1 aignet)))
  ;;                 (implies (natp (num-outs aignet))
  ;;                          (equal (nth *num-outs* aignet) (count-nodes 0 (out-type) 0 aignet)))
  ;;                 (implies (natp (num-nxsts aignet))
  ;;                          (equal (nth *num-nxsts* aignet) (count-nodes 0 (out-type) 1 aignet))))))

  (defthm aignet-counts-accurate-rw
    (implies (aignet-counts-accurate aignet)
             (and (equal (count-nodes 0 (in-type) 0 aignet) (nfix (nth *num-ins* aignet)))
                  (equal (count-nodes 0 (in-type) 1 aignet) (nfix (nth *num-regs* aignet)))
                  (equal (count-nodes 0 (out-type) 0 aignet) (nfix (nth *num-outs* aignet)))
                  (equal (count-nodes 0 (out-type) 1 aignet) (nfix (nth *num-nxsts* aignet))))))


  (defthm aignet-counts-accurate-of-update-nth
    (implies (and (not (equal (nfix n) *num-nodes*))
                  (not (equal (nfix n) *nodesi*))
                  (not (equal (nfix n) *num-regs*))
                  (not (equal (nfix n) *num-ins*))
                  (not (equal (nfix n) *num-outs*))
                  (not (equal (nfix n) *num-nxsts*))
                  (aignet-counts-accurate aignet))
             (aignet-counts-accurate (update-nth n v aignet)))
    :hints (("goal" :in-theory (enable* aignet-frame-thms)))))

(defsection aignet-nodes-nonconst
  (defun-sk aignet-nodes-nonconst (aignet)
    (forall idx 
            (implies (and (posp idx)
                          (< idx (nfix (num-nodes aignet))))
                     (not (equal (snode->type (id->slot idx 0 aignet))
                                 (const-type)))))
    :rewrite :direct)

  (in-theory (disable aignet-nodes-nonconst))

  (defthm aignet-nodes-nonconst-of-update-nth
    (implies (and (not (equal (nfix n) *num-nodes*))
                  (not (equal (nfix n) *nodesi*))
                  (aignet-nodes-nonconst aignet))
             (aignet-nodes-nonconst (update-nth n v aignet)))
    :hints (("goal" :in-theory (enable* aignet-frame-thms))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm aignet-nodes-nonconst-of-decr-num-nodes
    (implies (and (aignet-nodes-nonconst aignet)
                  (<= (nfix n) (nfix (num-nodes aignet))))
             (aignet-nodes-nonconst (update-nth *num-nodes* n aignet)))
    :hints (("goal" :in-theory (enable* aignet-frame-thms))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause))))))))

;; (defsection aignet-max-fanin-correct
;;   (defun-sk aignet-max-fanin-sufficient (aignet)
;;     (forall idx
;;             (implies (and (< (nfix (max-fanin aignet)) (nfix idx))
;;                           (< (nfix idx) (nfix (num-nodes aignet))))
;;                      (equal (snode->type (id->slot idx 0 aignet))
;;                             (out-type))))
;;     :rewrite :direct)

;;   (in-theory (disable aignet-max-fanin-sufficient))

;;   (define aignet-max-fanin-correct (aignet)
;;     :guard (aignet-sizes-ok aignet)
;;     (and (< (lnfix (max-fanin aignet)) (lnfix (num-nodes aignet)))
;;          (not (equal (id->type (max-fanin aignet) aignet) (out-type)))
;;          (ec-call (aignet-max-fanin-sufficient aignet)))))

(define aignet-find-max-fanin ((n natp) aignet)
    :guard (and (aignet-sizes-ok aignet)
                (< n (num-nodes aignet))
                (equal (id->type 0 aignet) (const-type)))
    :measure (nfix n)
    :returns (max-fanin natp :rule-classes :type-prescription)
    (b* (((unless (and (int= (id->type n aignet) (out-type))
                       (mbt (not (zp n)))))
          (lnfix n)))
      (aignet-find-max-fanin (1- (lnfix n)) aignet))
    ///
    (defcong nat-equiv equal (aignet-find-max-fanin n aignet) 1)

    (std::defret fanin-of-aignet-find-max-fanin
      (implies (equal (id->type 0 aignet) (const-type))
               (not (equal (snode->type (id->slot max-fanin 0 aignet)) (out-type)))))

    (std::defretd out-type-of-greater-than-find-max-fanin
      (implies (and (< max-fanin (nfix m))
                    (<= (nfix m) (nfix n)))
               (equal (snode->type (id->slot m 0 aignet)) (out-type))))

    (std::defret aignet-find-max-fanin-bound
      (<= max-fanin (nfix n))
      :rule-classes (:rewrite :linear))
    (local (in-theory (enable* aignet-frame-thms)))
    (def-aignet-frame aignet-find-max-fanin)

    (defthm aignet-find-max-fanin-of-maybe-grow-outs
      (equal (aignet-find-max-fanin n (maybe-grow-outs aignet))
             (aignet-find-max-fanin n aignet)))

    (defthm aignet-find-max-fanin-of-maybe-grow-nodes
      (equal (aignet-find-max-fanin n (maybe-grow-nodes aignet))
             (aignet-find-max-fanin n aignet)))

    (defthm aignet-find-max-fanin-of-maybe-grow-regs
      (equal (aignet-find-max-fanin n (maybe-grow-regs aignet))
             (aignet-find-max-fanin n aignet)))

    (defthm aignet-find-max-fanin-of-update-greater
      (implies (< (nfix n) (nfix m))
               (equal (aignet-find-max-fanin n (update-node-slot m slot val aignet))
                      (aignet-find-max-fanin n aignet))))
    
    (defthm aignet-find-max-fanin-of-update-regid
      (implies (equal (id->slot regid 0 aignet1) (id->slot regid 0 aignet))
               (equal (aignet-find-max-fanin n
                                             (update-node-slot regid 0
                                                               (set-snode->regid nxst
                                                                                 (id->slot regid 0 aignet1))
                                                               aignet))
                      (aignet-find-max-fanin n aignet)))
      :hints (("goal" :induct (aignet-find-max-fanin n aignet)
               :expand ((:free (Aignet) (aignet-find-max-fanin n aignet))))))

    (defthmd aignet-find-max-fanin-of-lesser-n-when-less
      (implies (and (<= (aignet-find-max-fanin m aignet) (nfix n))
                    (<= (nfix n) (nfix m)))
               (equal (aignet-find-max-fanin m aignet)
                      (aignet-find-max-fanin n aignet)))
      :hints (("goal" :induct (aignet-find-max-fanin m aignet))))

    (defthm unsigned-byte-p-of-aignet-find-max-fanin
      (implies (unsigned-byte-p w n)
               (unsigned-byte-p w (aignet-find-max-fanin n aignet)))
      :hints(("Goal" :in-theory (enable unsigned-byte-p)))))

(defsection add-nodes
  
  (local (in-theory (disable unsigned-byte-30-of-lit
                             aignet-sizes-ok-implies-num-type-bounds)))

  (defthm unsigned-byte-32-of-mk-snode-0
    (implies (unsigned-byte-p 30 fanin0)
             (unsigned-byte-p 32 (mv-nth 0 (mk-snode type regp phase fanin0 fanin1))))
    :hints(("Goal" :in-theory (enable mk-snode))))

  (defthm unsigned-byte-32-of-mk-snode-1
    (implies (unsigned-byte-p 30 fanin1)
             (unsigned-byte-p 32 (mv-nth 1 (mk-snode type regp phase fanin0 fanin1))))
    :hints(("Goal" :in-theory (enable mk-snode))))

  (defthm len-update-node-slot
    (implies (and (equal (nth *num-nodes* aignet)
                         (nth *num-nodes* aignet1))
                  (natp (nth *num-nodes* aignet))
                  ;; (< (nth *num-nodes* aignet1) #x1fffffff)
                  (<= (+ 2 (* 2 (nth *num-nodes* aignet1))) (len (nth *nodesi* aignet))))
             (equal (len (nth *nodesi* (update-node-slot (nth *num-nodes* aignet1)
                                                         bit val aignet)))
                    (len (nth *nodesi* aignet))))
    :hints(("Goal" :in-theory (enable update-node-slot maybe-grow-nodes))))

  (defthm len-update-node-slot-less
    (implies (and (< (nfix id) (nfix (nth *num-nodes* aignet)))
                  ;; (< (nth *num-nodes* aignet1) #x1fffffff)
                  (<= (+ 2 (* 2 (nth *num-nodes* aignet))) (len (nth *nodesi* aignet))))
             (equal (len (nth *nodesi* (update-node-slot id bit val aignet)))
                    (len (nth *nodesi* aignet))))
    :hints(("Goal" :in-theory (enable update-node-slot maybe-grow-nodes))))

  (local (in-theory (enable aignet-sizes-ok)))

  (local (defthm len-update-nth-linear
           (<= (len x) (len (update-nth n v x)))
           :rule-classes
           ((:linear :trigger-terms
             ((len (update-nth n v x))))
            (:rewrite))))

  ;; (local (defthm len-update-nth-compare
  ;;          (implies (< y (len x))
  ;;                   (< y (len (update-nth n v x))))))

  ;; (local (defthm len-grow-ins-compare
  ;;          (implies (< y (len (nth n x)))
  ;;                   (< y (len (nth n (maybe-grow-ins x)))))))

  ;; (defthm len-grow-nodes-compare
  ;;          (implies (< y (len (nth n x)))
  ;;                   (< y (len (nth n (maybe-grow-nodes x))))))

  ;; (defthm len-grow-outs-compare
  ;;          (implies (< y (len (nth n x)))
  ;;                   (< y (len (nth n (maybe-grow-outs x))))))

  ;; (defthm len-grow-regins-compare
  ;;          (implies (< y (len (nth n x)))
  ;;                   (< y (len (nth n (maybe-grow-regins x))))))

  ;; (defthm len-grow-regs-compare
  ;;          (implies (< y (len (nth n x)))
  ;;                   (< y (len (nth n (maybe-grow-regs x))))))

  ;; (local (in-theory (disable acl2::len-update-nth1
  ;;                            len-update-nth)))

  (defsection incr-node-nums
    (local (in-theory (enable aignet-sizes-ok
                              maybe-grow-nodes
                              maybe-grow-ins
                              maybe-grow-regs
                              maybe-grow-outs
                              unsigned-byte-p)))
    (define add-node (aignet)
      :inline t
      :guard (and (aignet-sizes-ok aignet)
                  (< (num-nodes aignet) #x1fffffff))
      (b* ((aignet (maybe-grow-nodes aignet))
           (nodes  (lnfix (num-nodes aignet))))
        (update-num-nodes (the (unsigned-byte 29) (+ 1 (the (unsigned-byte 29) nodes)))
                          aignet))
      ;; ///
      ;; (defthm add-node-preserves-aignet-sizes-ok
      ;;   (implies (aignet-sizes-ok aignet)
      ;;            (aignet-sizes-ok (add-node aignet))))
      )

    (define add-in (aignet)
      :inline t
      :guard (and (aignet-sizes-ok aignet)
                  (< (num-ins aignet) #x1ffffffe))
      (b* ((aignet (maybe-grow-ins aignet))
           (ins  (lnfix (num-ins aignet))))
        (update-num-ins (the (unsigned-byte 29) (+ 1 (the (unsigned-byte 29) ins))) aignet))
      ;; ///
      ;; (defthm add-in-preserves-aignet-sizes-ok
      ;;   (implies (aignet-sizes-ok aignet)
      ;;            (aignet-sizes-ok (add-in aignet))))
      )

    (define add-out (aignet)
      :inline t
      :guard (and (aignet-sizes-ok aignet)
                  (< (num-outs aignet) #x1ffffffe))
      (b* ((aignet (maybe-grow-outs aignet))
           (outs  (lnfix (num-outs aignet))))
        (update-num-outs (the (unsigned-byte 29) (+ 1 (the (unsigned-byte 29) outs))) aignet))
      ;; ///
      ;; (defthm add-out-preserves-aignet-sizes-ok
      ;;   (implies (aignet-sizes-ok aignet)
      ;;            (aignet-sizes-ok (add-out aignet))))
      )

    (define add-reg (aignet)
      :inline t
      :guard (and (aignet-sizes-ok aignet)
                  (< (num-regs aignet) #x1ffffffe))
      (b* ((aignet (maybe-grow-regs aignet))
           (regs  (lnfix (num-regs aignet))))
        (update-num-regs (the (unsigned-byte 29) (+ 1 (the (unsigned-byte 29) regs))) aignet))
      ;; ///
      ;; (defthm add-reg-preserves-aignet-sizes-ok
      ;;   (implies (aignet-sizes-ok aignet)
      ;;            (aignet-sizes-ok (add-reg aignet))))
      ))

  (local (in-theory (enable add-in add-out add-reg add-node)))

  (local (in-theory (enable* aignet-frame-thms)))

  (define aignet-add-in (aignet)
    :guard (and (aignet-sizes-ok aignet)
                (< (num-nodes aignet) #x1fffffff))

    (b* ((?pi-num (lnfix (num-ins aignet)))
         (?nodes  (lnfix (num-nodes aignet)))
         (aignet (add-node aignet))
         (aignet (add-in aignet))
         (aignet (update-max-fanin nodes aignet))
         (aignet (set-innum->id pi-num nodes aignet))
         ((mv slot0 slot1)
          (mk-snode^ (in-type) 0 0 0 pi-num))
         (aignet (update-node-slot$ nodes 0 slot0 aignet))
         (aignet (update-node-slot$ nodes 1 slot1 aignet)))
      aignet)
    ///

    (def-aignet-frame aignet-add-in)
    (local (in-theory (enable* aignet-frame-thms)))
    (defthm aignet-add-in-preserves-sizes-ok
      (implies (and (aignet-sizes-ok aignet)
                    (< (num-nodes aignet) #x1fffffff))
               (aignet-sizes-ok
                (aignet-add-in aignet)))
      :hints(("Goal" :in-theory (enable aignet-sizes-ok))))

    (defthm aignet-add-in-preserves-counts-accurate
      (implies (and (aignet-sizes-ok aignet)
                    (aignet-counts-accurate aignet))
               (aignet-counts-accurate (aignet-add-in aignet)))
      :hints((and stable-under-simplificationp
                  `(:expand ,(car (last clause))))))

    (defthm aignet-add-in-preserves-aignet-nodes-nonconst
      (implies (aignet-nodes-nonconst aignet)
               (aignet-nodes-nonconst (aignet-add-in aignet)))
      :hints((and stable-under-simplificationp
                  (let ((lit (car (last clause))))
                    `(:expand (,lit)
                      :use ((:instance aignet-nodes-nonconst-necc
                             (idx (aignet-nodes-nonconst-witness . ,(cdr lit)))))
                      :in-theory (disable aignet-nodes-nonconst-necc))))))

    ;; (defthm aignet-add-in-preserves-aignet-max-fanin-correct
    ;;   (implies (equal (nth *max-fanin* aignet) (aignet-find-max-fanin (+ -1 (nfix (num-nodes aignet))) aignet))
    ;;            (let ((aignet (aignet-add-in aignet)))
    ;;              (equal (nth *max-fanin* aignet) (aignet-find-max-fanin (+ -1 (nfix (num-nodes aignet))) aignet))))
    ;;   :hints (("goal" :Expand ((:free (aignet1) (aignet-find-max-fanin (nfix (nth *num-nodes* aignet)) aignet1))))))

    (defthm aignet-find-max-fanin-of-aignet-add-in
      (implies (equal (nfix n) (nfix (num-nodes aignet$c)))
               (equal (aignet-find-max-fanin n (aignet-add-in aignet$c))
                      (nfix (num-nodes aignet$c))))
      :hints (("goal" :Expand ((:free (aignet1) (aignet-find-max-fanin n aignet1))))))
    
    ;; (defthm aignet-add-in-preserves-regs-in-bounds
    ;;   (implies (regs-in-bounds n aignet)
    ;;            (regs-in-bounds n
    ;;             (aignet-add-in aignet)))
    ;;   :hints(("Goal" :in-theory (enable regs-in-bounds))))


    (defthm num-ins-of-add-in
      (equal (nth *num-ins* (aignet-add-in aignet))
             (+ 1 (nfix (nth *num-ins* aignet)))))

    (defthm num-nodes-of-add-in
      (equal (nth *num-nodes* (aignet-add-in aignet))
             (+ 1 (nfix (nth *num-nodes* aignet)))))

    (defthm max-fanin-of-add-in
      (equal (nth *max-fanin* (aignet-add-in aignet))
             (nfix (nth *num-nodes* aignet))))

    (defthm new-in-of-add-in
      (implies (nat-equiv n (nth *num-ins* aignet))
               (equal (nth n
                           (nth *insi*
                                (aignet-add-in aignet)))
                      (nfix (num-nodes aignet)))))

    (defthm nth-in-of-add-in
      (implies (< (nfix n) (nfix (nth *num-ins* aignet)))
               (nat-equiv (nth n (nth *insi* (aignet-add-in aignet)))
                          (nth n (nth *insi* aignet)))))

    (defthm nth-node-of-add-in
      (implies (case-split (not (nat-equiv id (num-nodes aignet))))
               (equal (id->slot id slot (aignet-add-in aignet))
                      (id->slot id slot aignet))))

    (defthm new-node-of-add-in
      (implies (and (case-split (nat-equiv id (num-nodes aignet)))
                    (aignet-sizes-ok aignet))
               (b* ((slot0 (id->slot id 0 (aignet-add-in aignet)))
                    (slot1 (id->slot id 1 (aignet-add-in aignet)))
                    ((mv s0 s1) (mk-snode (in-type) 0 0 0 (num-ins aignet))))
                 (and (equal slot0 s0)
                      (equal slot1 s1))))))

  ;; (defthm regnum->id-of-add-in
  ;;   (implies (aignet-regs-in-bounds aignet)
  ;;            (equal (regnum->id n (aignet-add-in aignet))
  ;;                   (regnum->id n aignet)))
  ;;   :hints(("Goal" :in-theory (enable regnum->id))))


  ;; (defthm aignet-add-in-preserves-aignet-regs-in-bounds
  ;;   (implies (aignet-regs-in-bounds aignet)
  ;;            (aignet-regs-in-bounds (aignet-add-in aignet)))
  ;;   :hints(("Goal" :in-theory (e/d* (aignet-regs-in-bounds)
  ;;                                   (aignet-add-in)))))

  (define aignet-add-reg (aignet)
    :guard (and (aignet-sizes-ok aignet)
                (< (num-nodes aignet) #x1fffffff))
    :prepwork ((local (defthm unsigned-byte-30-of-num-nodes
                        (implies (aignetp aignet)
                                 (unsigned-byte-p 30 (nth *num-nodes* aignet)))
                        :hints(("Goal" :in-theory (enable aignetp))))))
    (b* ((ro-num (lnfix (num-regs aignet)))
         (nodes  (lnfix (num-nodes aignet)))
         (aignet (add-node aignet))
         (aignet (add-reg aignet))
         (aignet (update-max-fanin nodes aignet))
         (aignet (set-regnum->id ro-num nodes aignet))
         ((mv slot0 slot1)
          (mk-snode^ (in-type) 1 0 nodes ro-num))
         (aignet (update-node-slot$ nodes 0 slot0 aignet))
         (aignet (update-node-slot$ nodes 1 slot1 aignet)))
      aignet)
    ///
    (def-aignet-frame aignet-add-reg)
    (local (in-theory (enable* aignet-frame-thms)))

    (defthm aignet-add-reg-preserves-sizes-ok
      (implies (and (aignet-sizes-ok aignet)
                    (< (num-nodes aignet) #x1fffffff))
               (aignet-sizes-ok
                (aignet-add-reg aignet)))
      :hints(("Goal" :in-theory (enable aignet-sizes-ok
                                        add-node add-reg))))

    (defthm aignet-add-reg-preserves-counts-accurate
      (implies (and (aignet-sizes-ok aignet)
                    (aignet-counts-accurate aignet))
               (aignet-counts-accurate (aignet-add-reg aignet)))
      :hints((and stable-under-simplificationp
                  `(:expand ,(car (last clause))))))

    (defthm aignet-add-reg-preserves-aignet-nodes-nonconst
      (implies (aignet-nodes-nonconst aignet)
               (aignet-nodes-nonconst (aignet-add-reg aignet)))
      :hints((and stable-under-simplificationp
                  (let ((lit (car (last clause))))
                    `(:expand (,lit)
                      :use ((:instance aignet-nodes-nonconst-necc
                             (idx (aignet-nodes-nonconst-witness . ,(cdr lit)))))
                      :in-theory (disable aignet-nodes-nonconst-necc))))))

    ;; (defthm aignet-add-reg-preserves-aignet-max-fanin-correct
    ;;   (implies (equal (nth *max-fanin* aignet) (aignet-find-max-fanin (+ -1 (nfix (num-nodes aignet))) aignet))
    ;;            (let ((aignet (aignet-add-reg aignet)))
    ;;              (equal (nth *max-fanin* aignet) (aignet-find-max-fanin (+ -1 (nfix (num-nodes aignet))) aignet))))
    ;;   :hints (("goal" :Expand ((:free (aignet1) (aignet-find-max-fanin (nfix (nth *num-nodes* aignet)) aignet1))))))

    (defthm aignet-find-max-fanin-of-aignet-add-reg
      (implies (equal (nfix n) (nfix (num-nodes aignet$c)))
               (equal (aignet-find-max-fanin n (aignet-add-reg aignet$c))
                      (nfix (num-nodes aignet$c))))
      :hints (("goal" :Expand ((:free (aignet1) (aignet-find-max-fanin n aignet1))))))
    
    ;; (defthm aignet-add-reg-preserves-aignet-max-fanin-correct
    ;;   (implies (aignet-max-fanin-correct aignet)
    ;;            (aignet-max-fanin-correct (aignet-add-reg aignet)))
    ;;   :hints(("goal" :in-theory (enable aignet-max-fanin-correct))
    ;;          (and stable-under-simplificationp
    ;;               (let ((lit (car (last clause))))
    ;;                 (and (eq (car lit) 'aignet-max-fanin-sufficient)
    ;;                      `(:expand (,lit)
    ;;                        :use ((:instance aignet-max-fanin-sufficient-necc
    ;;                               (idx (aignet-max-fanin-sufficient-witness . ,(cdr lit)))))
    ;;                        :in-theory (disable aignet-max-fanin-sufficient-necc)))))))

    ;; (defthm aignet-add-reg-preserves-regs-in-bounds
    ;;   (implies (regs-in-bounds n aignet)
    ;;            (regs-in-bounds n
    ;;                            (aignet-add-reg aignet)))
    ;;   :hints(("Goal" :in-theory (enable regs-in-bounds
    ;;                                     add-node
    ;;                                     add-reg)))
    ;;   ;; :hints(("Goal" :in-theory (disable aignet-sizes-ok
    ;;   ;;                                    len-update-nth
    ;;   ;;                                    acl2::len-update-nth1)))
    ;;   )


    (defthm new-reg-of-add-reg
      (implies (nat-equiv n (nth *num-regs* aignet))
               (nat-equiv (nth n
                               (nth *regsi*
                                    (aignet-add-reg aignet)))
                          (num-nodes aignet))))

    (defthm nth-reg-of-add-reg
      (implies (< (nfix n) (nfix (nth *num-regs* aignet)))
               (nat-equiv (nth n (nth *regsi* (aignet-add-reg aignet)))
                          (nth n (nth *regsi* aignet)))))

    (defthm num-regs-of-add-reg
      (equal (nth *num-regs* (aignet-add-reg aignet))
             (+ 1 (nfix (nth *num-regs* aignet))))
      :hints(("Goal" :in-theory (enable add-node add-reg))))

    (defthm max-fanin-of-add-reg
      (equal (nth *max-fanin* (aignet-add-reg aignet))
             (nfix (nth *num-nodes* aignet))))

    (defthm nth-node-of-add-reg
      (implies (case-split (not (nat-equiv id (num-nodes aignet))))
               (equal (id->slot id slot (aignet-add-reg aignet))
                      (id->slot id slot aignet))))

    (defthm new-node-of-add-reg
      (implies (and (case-split (nat-equiv id (num-nodes aignet)))
                    (aignet-sizes-ok aignet))
               (b* ((slot0 (id->slot id 0 (aignet-add-reg aignet)))
                    (slot1 (id->slot id 1 (aignet-add-reg aignet)))
                    ((mv s0 s1) (mk-snode (in-type) 1 0 (num-nodes aignet) (num-regs aignet))))
                 (and (equal slot0 s0)
                      (equal slot1 s1)))))

    (defthm num-nodes-of-add-reg
      (equal (nth *num-nodes* (aignet-add-reg aignet))
             (+ 1 (nfix (nth *num-nodes* aignet))))
      :hints(("Goal" :in-theory (enable add-node add-reg)))))

  ;; (defthm aignet-add-reg-preserves-aignet-regs-in-bound
  ;;   (implies (and (aignet-regs-in-bounds aignet)
  ;;                 (aignet-sizes-ok aignet))
  ;;            (aignet-regs-in-bounds (aignet-add-reg aignet)))
  ;;   :hints(("Goal" :in-theory (e/d (aignet-regs-in-bounds
  ;;                                   regs-in-bounds)
  ;;                                  (aignet-add-reg)))
  ;;          (and stable-under-simplificationp
  ;;               '(:in-theory (enable aignet-add-reg)))))

  (define aignet-add-and ((f0 litp :type (unsigned-byte 30))
                           (f1 litp :type (unsigned-byte 30))
                           aignet)
    :split-types t
    :guard (and (aignet-sizes-ok aignet)
                (< (num-nodes aignet) #x1fffffff)
                (< (lit-id f0)
                   (num-nodes aignet))
                (not (int= (id->type (lit-id f0) aignet)
                           (out-type)))
                (< (lit-id f1)
                   (num-nodes aignet))
                (not (int= (id->type (lit-id f1) aignet)
                           (out-type))))
    :guard-hints (("goal" :in-theory (e/d (add-node
                                           unsigned-byte-30-of-lit)
                                          (len-update-nth-linear))))
    (b* ((nodes  (lnfix (num-nodes aignet)))
         (phase (b-and (lit->phase f0 aignet)
                       (lit->phase f1 aignet)))
         (aignet (add-node aignet))
         (aignet (update-max-fanin nodes aignet))
         ((mv slot0 slot1)
          (mk-snode^ (gate-type) 0 phase (lit-fix f0) (lit-fix f1)))
         (aignet (update-node-slot$ nodes 0 slot0 aignet))
         (aignet (update-node-slot$ nodes 1 slot1 aignet)))
      aignet)
    ///
    (def-aignet-frame aignet-add-and)
    (local (in-theory (enable* aignet-frame-thms)))
    (defthm aignet-add-and-preserves-sizes-ok
      (implies (and (aignet-sizes-ok aignet)
                    (< (num-nodes aignet) #x1fffffff))
               (aignet-sizes-ok
                (aignet-add-and f0 f1 aignet)))
      :hints(("Goal" :in-theory (enable aignet-sizes-ok
                                        add-node))))

    (defthm aignet-add-and-preserves-counts-accurate
      (implies (and (aignet-sizes-ok aignet)
                    (aignet-counts-accurate aignet))
               (aignet-counts-accurate (aignet-add-and f0 f1 aignet)))
      :hints((and stable-under-simplificationp
                  `(:expand ,(car (last clause))))))

    (defthm aignet-add-and-preserves-aignet-nodes-nonconst
      (implies (aignet-nodes-nonconst aignet)
               (aignet-nodes-nonconst (aignet-add-and f0 f1 aignet)))
      :hints((and stable-under-simplificationp
                  (let ((lit (car (last clause))))
                    `(:expand (,lit)
                      :use ((:instance aignet-nodes-nonconst-necc
                             (idx (aignet-nodes-nonconst-witness . ,(cdr lit)))))
                      :in-theory (disable aignet-nodes-nonconst-necc))))))

    ;; (defthm aignet-add-and-preserves-aignet-max-fanin-correct
    ;;   (implies (equal (nth *max-fanin* aignet) (aignet-find-max-fanin (+ -1 (nfix (num-nodes aignet))) aignet))
    ;;            (let ((aignet (aignet-add-and f0 f1 aignet)))
    ;;              (equal (nth *max-fanin* aignet) (aignet-find-max-fanin (+ -1 (nfix (num-nodes aignet))) aignet))))
    ;;   :hints (("goal" :Expand ((:free (aignet1) (aignet-find-max-fanin (nfix (nth *num-nodes* aignet)) aignet1))))))

    (defthm aignet-find-max-fanin-of-aignet-add-and
      (implies (equal (nfix n) (nfix (num-nodes aignet$c)))
               (equal (aignet-find-max-fanin n (aignet-add-and f0 f1 aignet$c))
                      (nfix (num-nodes aignet$c))))
      :hints (("goal" :Expand ((:free (aignet1) (aignet-find-max-fanin n aignet1))))))

    ;; (defthm aignet-add-and-preserves-aignet-max-fanin-correct
    ;;   (implies (aignet-max-fanin-correct aignet)
    ;;            (aignet-max-fanin-correct (aignet-add-and f0 f1 aignet)))
    ;;   :hints(("goal" :in-theory (enable aignet-max-fanin-correct))
    ;;          (and stable-under-simplificationp
    ;;               (let ((lit (car (last clause))))
    ;;                 (and (eq (car lit) 'aignet-max-fanin-sufficient)
    ;;                      `(:expand (,lit)
    ;;                        :use ((:instance aignet-max-fanin-sufficient-necc
    ;;                               (idx (aignet-max-fanin-sufficient-witness . ,(cdr lit)))))
    ;;                        :in-theory (disable aignet-max-fanin-sufficient-necc)))))))
    ;; (defthm aignet-add-and-preserves-regs-in-bounds
    ;;   (implies (regs-in-bounds n aignet)
    ;;            (regs-in-bounds n
    ;;                            (aignet-add-and f0 f1 aignet)))
    ;;   :hints(("Goal" :in-theory (enable regs-in-bounds
    ;;                                     add-node)))
    ;;   ;; :hints(("Goal" :in-theory (disable aignet-sizes-ok
    ;;   ;;                                    len-update-nth
    ;;   ;;                                    acl2::len-update-nth1)))
    ;;   )

    (defthm max-fanin-of-add-and
      (equal (nth *max-fanin* (aignet-add-and f0 f1 aignet))
             (nfix (nth *num-nodes* aignet))))

    (defthm num-nodes-of-add-and
      (equal (nth *num-nodes* (aignet-add-and f0 f1 aignet))
             (+ 1 (nfix (nth *num-nodes* aignet))))
      :hints(("Goal" :in-theory (enable add-node))))


    (defthm nth-node-of-add-and
      (implies (case-split (not (nat-equiv id (num-nodes aignet))))
               (equal (id->slot id slot (aignet-add-and f0 f1 aignet))
                      (id->slot id slot aignet))))

    (defthm new-node-of-add-and
      (implies (and (case-split (nat-equiv id (num-nodes aignet)))
                    (aignet-sizes-ok aignet))
               (b* ((slot0 (id->slot id 0 (aignet-add-and f0 f1 aignet)))
                    (slot1 (id->slot id 1 (aignet-add-and f0 f1 aignet)))
                    ((mv s0 s1) (mk-snode (gate-type) 0
                                          (b-and (lit->phase f0 aignet)
                                                 (lit->phase f1 aignet))
                                          (lit-fix f0)
                                          (lit-fix f1))))
                 (and (equal slot0 s0)
                      (equal slot1 s1))))))


  (define aignet-add-xor ((f0 litp :type (unsigned-byte 30))
                           (f1 litp :type (unsigned-byte 30))
                           aignet)
    :split-types t
    :guard (and (aignet-sizes-ok aignet)
                (< (num-nodes aignet) #x1fffffff)
                (< (lit-id f0)
                   (num-nodes aignet))
                (not (int= (id->type (lit-id f0) aignet)
                           (out-type)))
                (< (lit-id f1)
                   (num-nodes aignet))
                (not (int= (id->type (lit-id f1) aignet)
                           (out-type))))
    :guard-hints (("goal" :in-theory (e/d (add-node
                                           unsigned-byte-30-of-lit)
                                          (len-update-nth-linear))))
    (b* ((nodes  (lnfix (num-nodes aignet)))
         (phase (b-xor (lit->phase f0 aignet)
                       (lit->phase f1 aignet)))
         (aignet (add-node aignet))
         (aignet (update-max-fanin nodes aignet))
         ((mv slot0 slot1)
          (mk-snode^ (gate-type) 1 phase (lit-fix f0) (lit-fix f1)))
         (aignet (update-node-slot$ nodes 0 slot0 aignet))
         (aignet (update-node-slot$ nodes 1 slot1 aignet)))
      aignet)
    ///
    (def-aignet-frame aignet-add-xor)
    (local (in-theory (enable* aignet-frame-thms)))
    (defthm aignet-add-xor-preserves-sizes-ok
      (implies (and (aignet-sizes-ok aignet)
                    (< (num-nodes aignet) #x1fffffff))
               (aignet-sizes-ok
                (aignet-add-xor f0 f1 aignet)))
      :hints(("Goal" :in-theory (enable aignet-sizes-ok
                                        add-node))))

    (defthm aignet-add-xor-preserves-counts-accurate
      (implies (and (aignet-sizes-ok aignet)
                    (aignet-counts-accurate aignet))
               (aignet-counts-accurate (aignet-add-xor f0 f1 aignet)))
      :hints((and stable-under-simplificationp
                  `(:expand ,(car (last clause))))))

    (defthm aignet-add-xor-preserves-aignet-nodes-nonconst
      (implies (aignet-nodes-nonconst aignet)
               (aignet-nodes-nonconst (aignet-add-xor f0 f1 aignet)))
      :hints((and stable-under-simplificationp
                  (let ((lit (car (last clause))))
                    `(:expand (,lit)
                      :use ((:instance aignet-nodes-nonconst-necc
                             (idx (aignet-nodes-nonconst-witness . ,(cdr lit)))))
                      :in-theory (disable aignet-nodes-nonconst-necc))))))

    ;; (defthm aignet-add-xor-preserves-aignet-max-fanin-correct
    ;;   (implies (equal (nth *max-fanin* aignet) (aignet-find-max-fanin (+ -1 (nfix (num-nodes aignet))) aignet))
    ;;            (let ((aignet (aignet-add-xor f0 f1 aignet)))
    ;;              (equal (nth *max-fanin* aignet) (aignet-find-max-fanin (+ -1 (nfix (num-nodes aignet))) aignet))))
    ;;   :hints (("goal" :Expand ((:free (aignet1) (aignet-find-max-fanin (nfix (nth *num-nodes* aignet)) aignet1))))))

    (defthm aignet-find-max-fanin-of-aignet-add-xor
      (implies (equal (nfix n) (nfix (num-nodes aignet$c)))
               (equal (aignet-find-max-fanin n (aignet-add-xor f0 f1 aignet$c))
                      (nfix (num-nodes aignet$c))))
      :hints (("goal" :Expand ((:free (aignet1) (aignet-find-max-fanin n aignet1))))))

    ;; (defthm aignet-add-xor-preserves-aignet-max-fanin-correct
    ;;   (implies (aignet-max-fanin-correct aignet)
    ;;            (aignet-max-fanin-correct (aignet-add-xor f0 f1 aignet)))
    ;;   :hints(("goal" :in-theory (enable aignet-max-fanin-correct))
    ;;          (and stable-under-simplificationp
    ;;               (let ((lit (car (last clause))))
    ;;                 (and (eq (car lit) 'aignet-max-fanin-sufficient)
    ;;                      `(:expand (,lit)
    ;;                        :use ((:instance aignet-max-fanin-sufficient-necc
    ;;                               (idx (aignet-max-fanin-sufficient-witness . ,(cdr lit)))))
    ;;                        :in-theory (disable aignet-max-fanin-sufficient-necc)))))))
    ;; (defthm aignet-add-xor-preserves-regs-in-bounds
    ;;   (implies (regs-in-bounds n aignet)
    ;;            (regs-in-bounds n
    ;;                            (aignet-add-xor f0 f1 aignet)))
    ;;   :hints(("Goal" :in-theory (enable regs-in-bounds
    ;;                                     add-node)))
    ;;   ;; :hints(("Goal" :in-theory (disable aignet-sizes-ok
    ;;   ;;                                    len-update-nth
    ;;   ;;                                    acl2::len-update-nth1)))
    ;;   )

    (defthm max-fanin-of-add-xor
      (equal (nth *max-fanin* (aignet-add-xor f0 f1 aignet))
             (nfix (nth *num-nodes* aignet))))

    (defthm num-nodes-of-add-xor
      (equal (nth *num-nodes* (aignet-add-xor f0 f1 aignet))
             (+ 1 (nfix (nth *num-nodes* aignet))))
      :hints(("Goal" :in-theory (enable add-node))))


    (defthm nth-node-of-add-xor
      (implies (case-split (not (nat-equiv id (num-nodes aignet))))
               (equal (id->slot id slot (aignet-add-xor f0 f1 aignet))
                      (id->slot id slot aignet))))

    (defthm new-node-of-add-xor
      (implies (and (case-split (nat-equiv id (num-nodes aignet)))
                    (aignet-sizes-ok aignet))
               (b* ((slot0 (id->slot id 0 (aignet-add-xor f0 f1 aignet)))
                    (slot1 (id->slot id 1 (aignet-add-xor f0 f1 aignet)))
                    ((mv s0 s1) (mk-snode (gate-type) 1
                                          (b-xor (lit->phase f0 aignet)
                                                 (lit->phase f1 aignet))
                                          (lit-fix f0)
                                          (lit-fix f1))))
                 (and (equal slot0 s0)
                      (equal slot1 s1))))))


  ;; (defthm aignet-add-xor-preserves-aignet-regs-in-bound
  ;;   (implies (aignet-regs-in-bounds aignet)
  ;;            (aignet-regs-in-bounds (aignet-add-xor f0 f1 aignet)))
  ;;   :hints(("Goal" :in-theory (e/d (aignet-regs-in-bounds)
  ;;                                  (aignet-add-xor)))))

  (define aignet-add-out ((f litp :type (unsigned-byte 30))
                          aignet)
    :split-types t
    :guard (and (aignet-sizes-ok aignet)
                (< (num-nodes aignet) #x1fffffff)
                (< (lit-id f)
                   (num-nodes aignet))
                (not (int= (id->type (lit-id f) aignet)
                           (out-type))))
    :guard-hints (("goal" :in-theory (enable add-node add-out
                                             unsigned-byte-30-of-lit)))
    (b* ((nodes  (num-nodes aignet))
         (po-num (num-outs aignet))
         (phase  (lit->phase f aignet))
         (aignet (add-node aignet))
         (aignet (add-out aignet))
         (aignet (set-outnum->id po-num nodes aignet))
         ((mv slot0 slot1)
          (mk-snode^ (out-type) 0 phase (lit-fix f) po-num))
         (aignet (update-node-slot$ nodes 0 slot0 aignet))
         (aignet (update-node-slot$ nodes 1 slot1 aignet)))
      aignet)
    ///

    (def-aignet-frame aignet-add-out)
    (local (in-theory (enable* aignet-frame-thms)))
    (defthm aignet-add-out-preserves-sizes-ok
      (implies (and (aignet-sizes-ok aignet)
                    (< (num-nodes aignet) #x1fffffff))
               (aignet-sizes-ok
                (aignet-add-out f aignet)))
      :hints(("Goal" :in-theory (enable aignet-sizes-ok))))

    (defthm aignet-add-out-preserves-counts-accurate
      (implies (and (aignet-sizes-ok aignet)
                    (aignet-counts-accurate aignet))
               (aignet-counts-accurate (aignet-add-out f aignet)))
      :hints((and stable-under-simplificationp
                  `(:expand ,(car (last clause))))))

    (defthm aignet-add-out-preserves-aignet-nodes-nonconst
      (implies (aignet-nodes-nonconst aignet)
               (aignet-nodes-nonconst (aignet-add-out f aignet)))
      :hints((and stable-under-simplificationp
                  (let ((lit (car (last clause))))
                    `(:expand (,lit)
                      :use ((:instance aignet-nodes-nonconst-necc
                             (idx (aignet-nodes-nonconst-witness . ,(cdr lit)))))
                      :in-theory (disable aignet-nodes-nonconst-necc))))))

    ;; (defthm aignet-add-out-preserves-aignet-max-fanin-correct
    ;;   (implies (and (equal (nth *max-fanin* aignet) (aignet-find-max-fanin (+ -1 (nfix (num-nodes aignet))) aignet))
    ;;                 ;; (natp (num-nodes aignet))
    ;;                 )
    ;;            (let ((aignet (aignet-add-out f aignet)))
    ;;              (equal (nth *max-fanin* aignet) (aignet-find-max-fanin (+ -1 (nfix (num-nodes aignet))) aignet))))
    ;;   :hints (("goal" :Expand ((:free (aignet1) (aignet-find-max-fanin (nfix (nth *num-nodes* aignet)) aignet1)))
    ;;            :in-theory (enable* aignet-frame-thms))))

    (defthm aignet-find-max-fanin-of-aignet-add-out
      (implies (equal (nfix n) (nfix (num-nodes aignet$c)))
               (equal (aignet-find-max-fanin n (aignet-add-out f aignet$c))
                      (aignet-find-max-fanin (+ -1 (nfix (num-nodes aignet$c)))
                                             aignet$c)))
      :hints (("goal" :Expand ((:free (aignet1) (aignet-find-max-fanin n aignet1))))))

    ;; (defthm aignet-add-out-preserves-aignet-max-fanin-correct
    ;;   (implies (and (aignet-max-fanin-correct aignet)
    ;;                 (aignet-sizes-ok aignet))
    ;;            (aignet-max-fanin-correct (aignet-add-out f aignet)))
    ;;   :hints(("goal" :in-theory (enable aignet-max-fanin-correct))
    ;;          (and stable-under-simplificationp
    ;;               (let ((lit (car (last clause))))
    ;;                 (and (eq (car lit) 'aignet-max-fanin-sufficient)
    ;;                      `(:expand (,lit)
    ;;                        :use ((:instance aignet-max-fanin-sufficient-necc
    ;;                               (idx (aignet-max-fanin-sufficient-witness . ,(cdr lit)))))
    ;;                        :in-theory (disable aignet-max-fanin-sufficient-necc)))))))

    ;; (defthm aignet-add-out-preserves-regs-in-bounds
    ;;   (implies (regs-in-bounds n aignet)
    ;;            (regs-in-bounds n
    ;;             (aignet-add-out f aignet)))
    ;;   :hints(("Goal" :in-theory (enable regs-in-bounds)))
    ;;   ;; :hints(("Goal" :in-theory (disable aignet-sizes-ok
    ;;   ;;                                    len-update-nth
    ;;   ;;                                    acl2::len-update-nth1)))
    ;;   )

    (defthm num-outs-of-add-out
      (equal (nth *num-outs* (aignet-add-out f aignet))
             (+ 1 (nfix (nth *num-outs* aignet)))))

    (defthm num-nodes-of-add-out
      (equal (nth *num-nodes* (aignet-add-out f aignet))
             (+ 1 (nfix (nth *num-nodes* aignet))))
      :hints(("Goal" :in-theory (enable add-node add-out))))

    (defthm new-out-of-add-out
      (implies (nat-equiv n (nth *num-outs* aignet))
               (nat-equiv (nth n
                               (nth *outsi*
                                    (aignet-add-out f aignet)))
                          (num-nodes aignet))))

    (defthm nth-out-of-add-out
      (implies (< (nfix n) (nfix (nth *num-outs* aignet)))
               (nat-equiv (nth n (nth *outsi* (aignet-add-out f aignet)))
                          (nth n (nth *outsi* aignet)))))

    (defthm nth-node-of-add-out
      (implies (case-split (not (nat-equiv id (num-nodes aignet))))
               (equal (id->slot id slot (aignet-add-out f aignet))
                      (id->slot id slot aignet))))

    (defthm new-node-of-add-out
      (implies (and (case-split (nat-equiv id (num-nodes aignet)))
                    (aignet-sizes-ok aignet))
               (b* ((slot0 (id->slot id 0 (aignet-add-out f aignet)))
                    (slot1 (id->slot id 1 (aignet-add-out f aignet)))
                    ((mv s0 s1) (mk-snode (out-type) 0
                                          (lit->phase f aignet)
                                          (lit-fix f)
                                          (num-outs aignet))))
                 (and (equal slot0 s0)
                      (equal slot1 s1))))))



  ;; (defthm aignet-add-out-preserves-aignet-regs-in-bound
  ;;   (implies (aignet-regs-in-bounds aignet)
  ;;            (aignet-regs-in-bounds (aignet-add-out f aignet)))
  ;;   :hints(("Goal" :in-theory (e/d (aignet-regs-in-bounds)
  ;;                                  (aignet-add-out)))))

  (defthm unsigned-byte-32-of-set-snode->regid
    (implies (unsigned-byte-p 29 regid)
             (unsigned-byte-p 32 (set-snode->regid regid slot)))
    :hints(("Goal" :in-theory (enable set-snode->regid))))

  (define aignet-set-nxst ((f litp :type (unsigned-byte 30))
                           (regid natp :type (unsigned-byte 29))
                           aignet)
    :split-types t
    :guard (and (aignet-sizes-ok aignet)
                (< (num-nodes aignet) #x1fffffff)
                (< (lit-id f)
                   (num-nodes aignet))
                (not (int= (id->type (lit-id f) aignet)
                           (out-type)))
                (< regid (num-nodes aignet))
                (int= (id->type regid aignet)
                      (in-type))
                (int= (id->regp regid aignet) 1))
    :guard-hints ((and stable-under-simplificationp
                       '(:use aignet-sizes-ok
                         :in-theory (e/d (unsigned-byte-30-of-lit)
                                         (aignet-sizes-ok)))))
    :prepwork ((local (defthm unsigned-byte-30-of-num-nodes
                        (implies (aignetp aignet)
                                 (unsigned-byte-p 30 (nth *num-nodes* aignet)))
                        :hints(("Goal" :in-theory (enable aignetp)))))
               (local (defthm unsigned-byte-p-when-less
                        (implies (and (syntaxp (quotep n))
                                      (natp n)
                                      (natp x)
                                      (< x (expt 2 n)))
                                 (unsigned-byte-p n x))
                        :hints(("Goal" :in-theory (enable unsigned-byte-p)))))
               (local (defthm aignet-sizes-ok-implies-num-nxsts-less
                        (implies (aignet-sizes-ok aignet)
                                 (< (nth *num-nxsts* aignet) (nth *num-nodes* aignet)))
                        :rule-classes :linear)))
    (b* ((nodes  (num-nodes aignet))
         (phase  (lit->phase f aignet))
         (aignet (add-node aignet))
         (aignet (update-num-nxsts (the (unsigned-byte 29)
                                        (+ 1 (the (unsigned-byte 29) (num-nxsts aignet))))
                                   aignet))
         (slot0 (id->slot$ regid 0 aignet))
         (new-slot0 (set-snode->regid nodes slot0))
         (aignet (update-node-slot$ regid 0 new-slot0 aignet))
         ((mv slot0 slot1)
          (mk-snode (out-type) 1 phase (lit-fix f) (lnfix regid)))
         (aignet (update-node-slot$ nodes 0 slot0 aignet))
         (aignet (update-node-slot$ nodes 1 slot1 aignet)))
      aignet)
    ///

    (def-aignet-frame aignet-set-nxst)
  (local (in-theory (enable* aignet-frame-thms)))
  (defthm aignet-set-nxst-preserves-sizes-ok
    (implies (and (aignet-sizes-ok aignet)
                  (< (num-nodes aignet) #x1fffffff)
                  (< (nfix regid) (num-nodes aignet)))
             (aignet-sizes-ok
              (aignet-set-nxst f regid aignet)))
    :hints(("Goal" :in-theory (enable aignet-sizes-ok
                                      add-node
                                      add-reg))))

  (defthm aignet-set-nxst-preserves-counts-accurate
    (implies (and (aignet-sizes-ok aignet)
                  (aignet-counts-accurate aignet))
             (aignet-counts-accurate (aignet-set-nxst f regid aignet)))
      :hints((and stable-under-simplificationp
                  `(:expand ,(car (last clause))))))

  (defthm aignet-set-nxst-preserves-aignet-nodes-nonconst
    (implies (aignet-nodes-nonconst aignet)
             (aignet-nodes-nonconst (aignet-set-nxst f regid aignet)))
    :hints((and stable-under-simplificationp
                (let ((lit (car (last clause))))
                  `(:expand (,lit)
                    :use ((:instance aignet-nodes-nonconst-necc
                           (idx (aignet-nodes-nonconst-witness . ,(cdr lit)))))
                    :in-theory (disable aignet-nodes-nonconst-necc))))))

  ;; (defthm aignet-set-nxst-preserves-aignet-max-fanin-correct
  ;;   (implies (And (equal (nth *max-fanin* aignet) (aignet-find-max-fanin (+ -1 (nfix (num-nodes aignet))) aignet))
  ;;                 ;; (natp (num-nodes aignet))
  ;;                 )
  ;;            (let ((aignet (aignet-set-nxst f regid aignet)))
  ;;              (equal (nth *max-fanin* aignet) (aignet-find-max-fanin (+ -1 (nfix (num-nodes aignet))) aignet))))
  ;;   :hints (("goal" :Expand ((:free (aignet1) (aignet-find-max-fanin (nfix (nth *num-nodes* aignet)) aignet1))))))

  (defthm aignet-find-max-fanin-of-aignet-set-nxst
    (implies (equal (nfix n) (nfix (num-nodes aignet$c)))
             (equal (aignet-find-max-fanin n (aignet-set-nxst f regid aignet$c))
                    (aignet-find-max-fanin (+ -1 (nfix (num-nodes aignet$c)))
                                           aignet$c)))
    :hints (("goal" :Expand ((:free (aignet1) (aignet-find-max-fanin n aignet1))))))

  ;; (defthm aignet-set-nxst-preserves-aignet-max-fanin-correct
  ;;   (implies (and (aignet-max-fanin-correct aignet)
  ;;                 (aignet-sizes-ok aignet))
  ;;            (aignet-max-fanin-correct (aignet-set-nxst f regid aignet)))
  ;;   :hints(("goal" :in-theory (enable aignet-max-fanin-correct))
  ;;          (and stable-under-simplificationp
  ;;               (let ((lit (car (last clause))))
  ;;                 (and (eq (car lit) 'aignet-max-fanin-sufficient)
  ;;                      `(:expand (,lit)
  ;;                        :use ((:instance aignet-max-fanin-sufficient-necc
  ;;                               (idx (aignet-max-fanin-sufficient-witness . ,(cdr lit)))))
  ;;                        :in-theory (disable aignet-max-fanin-sufficient-necc)))))))

  ;; (defthm aignet-set-nxst-preserves-regs-in-bounds
  ;;   (implies (regs-in-bounds n aignet)
  ;;            (regs-in-bounds n
  ;;                            (aignet-set-nxst f regid aignet)))
  ;;   :hints(("Goal" :in-theory (enable regs-in-bounds
  ;;                                     add-node
  ;;                                     add-reg)))
  ;;   ;; :hints(("Goal" :in-theory (disable aignet-sizes-ok
  ;;   ;;                                    len-update-nth
  ;;   ;;                                    acl2::len-update-nth1)))
  ;;   )

  ;; (defthm num-regs-of-set-nxst
  ;;   (implies (aignet-sizes-ok aignet)
  ;;            (equal (nth *num-regs* (aignet-set-nxst f regid aignet))
  ;;                   (if (< (num-nxsts aignet)
  ;;                          (num-regs aignet))
  ;;                       (num-regs aignet)
  ;;                     (+ 1 (num-regs aignet)))))
  ;;   :hints(("Goal" :in-theory (enable add-node add-reg))))

  (defthm num-nxsts-of-set-nxst
    (implies (aignet-sizes-ok aignet)
             (equal (nth *num-nxsts* (aignet-set-nxst f regid aignet))
                    (+ 1 (num-nxsts aignet))))
    :hints(("Goal" :in-theory (enable add-node add-reg))))

  ;; (defthm num-regs-of-set-nxst
  ;;   (implies (aignet-sizes-ok aignet)
  ;;            (equal (nth *num-regs* (aignet-set-nxst f regid aignet))
  ;;                   (if (< (num-nxsts aignet)
  ;;                          (num-regs aignet))
  ;;                       (num-regs aignet)
  ;;                     (+ 1 (num-regs aignet)))))
  ;;   :hints(("Goal" :in-theory (enable add-node add-reg))))

  (defthm num-nodes-of-set-nxst
    (equal (nth *num-nodes* (aignet-set-nxst f regid aignet))
           (+ 1 (nfix (nth *num-nodes* aignet))))
    :hints(("Goal" :in-theory (enable add-node add-reg))))

  ;; (defthm new-reg-of-set-nxst
  ;;   (implies (nat-equiv n (nth *num-nxsts* aignet))
  ;;            (equal (nth n
  ;;                        (nth *regsi*
  ;;                             (aignet-set-nxst f regid aignet)))
  ;;                   (if (< (num-nxsts aignet)
  ;;                          (num-regs aignet))
  ;;                       (nth n (nth *regsi* aignet))
  ;;                     (nfix (num-nodes aignet))))))

  ;; (defthm nth-reg-of-set-nxst
  ;;   (implies (case-split (not (equal (nfix n) (nfix (nth *num-nxsts* aignet)))))
  ;;            (nat-equiv (nth n (nth *regsi* (aignet-set-nxst f regid aignet)))
  ;;                      (nth n (nth *regsi* aignet)))))


  (defthm nth-node-of-set-nxst
    (implies (and (case-split (not (nat-equiv id (num-nodes aignet))))
                  (< (nfix regid) (num-nodes aignet))
                  (int= (id->type regid aignet)
                        (in-type))
                  (int= (id->regp regid aignet) 1))
             (equal (id->slot id slot (aignet-set-nxst f regid aignet))
                    (if (and (nat-equiv id regid)
                             (equal (bfix slot) 0))
                        (set-snode->regid
                         (num-nodes aignet)
                         (id->slot regid 0 aignet))
                      (id->slot id slot aignet)))))

  (defthm new-node-of-set-nxst
    (implies (and (case-split (nat-equiv id (num-nodes aignet)))
                  (aignet-sizes-ok aignet))
             (b* ((slot0 (id->slot id 0 (aignet-set-nxst f regid aignet)))
                  (slot1 (id->slot id 1 (aignet-set-nxst f regid aignet)))
                  ((mv s0 s1) (mk-snode (out-type) 1 (lit->phase f aignet)
                                        (lit-fix f) (lnfix regid))))
               (and (equal slot0 s0)
                    (equal slot1 s1)))))

  ;; (defthm aignet-set-nxst-preserves-aignet-regs-in-bounds
  ;;   (implies (and (aignet-regs-in-bounds aignet)
  ;;                 (aignet-sizes-ok aignet))
  ;;            (aignet-regs-in-bounds (aignet-set-nxst f regid aignet)))
  ;;   :hints(("Goal" :in-theory (e/d (aignet-regs-in-bounds
  ;;                                   regs-in-bounds)
  ;;                                  (aignet-set-nxst
  ;;                                   aignet-set-nxst-preserves-regs-in-bounds))
  ;;           :use ((:instance aignet-set-nxst-preserves-regs-in-bounds
  ;;                  (n (num-regs aignet)))))
  ;;          (and stable-under-simplificationp
  ;;               '(:in-theory (enable aignet-set-nxst
  ;;                                    add-node)))))
  ))



;; We can cheaply roll back the effect of adding a node, unless it's a nextstate, by
;; decrementing the node count and node type count.
(define aignet-gates-onlyp ((n natp) aignet)
  ;; Checks no nextstates in the nodes above n.
  :guard (and (aignet-sizes-ok aignet)
              (<= n (num-nodes aignet)))
  :measure (nfix (- (nfix (num-nodes aignet)) (nfix n)))
  (b* (((when (mbe :logic (zp (- (nfix (num-nodes aignet)) (nfix n)))
                   :exec (eql n (num-nodes aignet))))
        t))
    (and (int= (id->type (lnfix n) aignet) (gate-type))
         (aignet-gates-onlyp (+ 1 (lnfix n)) aignet)))
  ///
  (local (defthm dumb
           (implies (equal (nfix n) (+ -1 m))
                    (equal (+ 1 (nfix n))
                           (fix m)))))

  (defthmd aignet-gates-onlyp-implies-gate
    (implies (and (aignet-gates-onlyp n aignet)
                  (<= (nfix n) (nfix m))
                  (< (nfix m) (nfix (num-nodes aignet))))
             (equal (snode->type (id->slot m 0 aignet)) (gate-type))))

  (local (in-theory (enable* aignet-frame-thms)))

  (defthm aignet-gates-onlyp-of-decrease-num-nodes
    (implies (and (<= (nfix new-num-nodes) (nfix (num-nodes aignet)))
                  (aignet-gates-onlyp n aignet))
             (aignet-gates-onlyp n (update-nth *num-nodes* new-num-nodes aignet))))

  (def-aignet-frame aignet-gates-onlyp))


(define aignet-nongate-witness ((n natp) aignet)
  ;; Checks no nextstates in the nodes above n.
  :guard (and (aignet-sizes-ok aignet)
              (<= n (num-nodes aignet)))
  :measure (nfix (- (nfix (num-nodes aignet)) (nfix n)))
  (b* (((when (mbe :logic (zp (- (nfix (num-nodes aignet)) (nfix n)))
                   :exec (eql n (num-nodes aignet))))
        (lnfix n)))
    (if (int= (id->type n aignet) (gate-type))
        (aignet-nongate-witness (+ 1 (lnfix n)) aignet)
      (lnfix n)))
  ///

  (defthmd not-aignet-gates-onlyp-implies-witness
    (implies (not (aignet-gates-onlyp n aignet))
             (and (let ((m (aignet-nongate-witness n aignet)))
                    (and (<= (nfix n) (nfix m))
                         (< (nfix m) (nfix (num-nodes aignet)))
                         (not (equal (id->type m aignet) (gate-type)))))))
    :hints(("Goal" :in-theory (enable aignet-gates-onlyp)))))
    



(defsection aignet-rollback
  (local (in-theory (enable aignet-sizes-ok
                            aignet-counts-accurate
                            regp-when-count-nodes-equal-0)))

  (local (defthm unsigned-byte-p-when-less-than-num-nodes
           (implies (and (<= n (nth *num-nodes* aignet))
                         (natp n)
                         (aignetp aignet))
                    (unsigned-byte-p 29 n))
           :hints(("Goal" :in-theory (enable aignetp unsigned-byte-p)))))

  ;; (local (defthm nfix-n-minus-1-lte
  ;;          (implies (natp n)
  ;;                   (<= (nfix (+ -1 n)) n))
  ;;          :rule-classes :linear))

  ;; (local (defthm aignet-nodes-nonconst-implies-type
  ;;          (implies (and (aignet-nodes-nonconst aignet)
  ;;                        (posp n)
  ;;                        (< (nfix n) (nfix (num-nodes aignet)))
  ;;                        (not (equal (id->type n aignet) 1)))
  ;;                   (equal (equal (snode->type (id->slot n 0 aignet)) 3)
  ;;                          (not (equal (id->type n aignet) 2))))))
  


  ;; (define aignet-rollback-one (aignet)
  ;;   :guard (and (aignet-sizes-ok aignet)
  ;;               (< 1 (num-nodes aignet))
  ;;               (ec-call (aignet-counts-accurate aignet))
  ;;               (ec-call (aignet-nodes-nonconst aignet))
  ;;               (not (and (equal (id->type (+ -1 (num-nodes aignet)) aignet) (out-type))
  ;;                         (equal (id->regp (+ -1 (num-nodes aignet)) aignet) 1))))
  ;;   :guard-debug t
  ;;   :returns (new-aignet)
  ;;   :prepwork ((local (defthm unsigned-byte-p-when-less
  ;;                       (implies (and (syntaxp (quotep n))
  ;;                                     (natp n)
  ;;                                     (natp x)
  ;;                                     (< x (expt 2 n)))
  ;;                                (unsigned-byte-p n x))
  ;;                       :hints(("Goal" :in-theory (enable unsigned-byte-p))))))
  ;;   (b* ((n (+ -1 (lnfix (num-nodes aignet))))
  ;;        (type (id->type n aignet))
  ;;        ((when (eql type (gate-type)))
  ;;         (update-num-nodes n aignet))
  ;;        ((when (eql type (out-type)))
  ;;         ;; We can't handle nxst nodes without doing something more
  ;;         ;; complicated, so we'll just guard against them in the logic
  ;;         ;; version.
  ;;         (b* ((aignet (update-num-outs (1- (lnfix (num-outs aignet))) aignet)))
  ;;           (update-num-nodes n aignet)))
  ;;        (regp (id->regp n aignet))
  ;;        (aignet (if (int= regp 1)
  ;;                    (update-num-regs (1- (lnfix (num-regs aignet))) aignet)
  ;;                  (update-num-ins (1- (lnfix (num-ins aignet))) aignet))))
  ;;     (update-num-nodes n aignet))
  ;;   ///
  ;;   (std::defret num-nodes-of-aignet-rollback-one
  ;;     (implies (posp (nfix (num-nodes aignet)))
  ;;              (equal (nth *num-nodes* new-aignet)
  ;;                     (+ -1 (nfix (num-nodes aignet))))))
    
  ;;   (local (in-theory (enable* aignet-frame-thms)))
  ;;   (def-aignet-frame aignet-rollback-one)

  ;;   (std::defret aignet-rollback-one-preserves-sizes-ok
  ;;     (implies (and (aignet-sizes-ok aignet)
  ;;                   (< 1 (nfix (num-nodes aignet)))
  ;;                   (not (and (equal (id->type (+ -1 (nfix (num-nodes aignet))) aignet) (out-type))
  ;;                             (equal (id->regp (+ -1 (nfix (num-nodes aignet))) aignet) 1)))
  ;;                   (aignet-nodes-nonconst aignet)
  ;;                   (aignet-counts-accurate aignet))
  ;;              (aignet-sizes-ok new-aignet)))

  ;;   (std::defret aignet-rollback-one-preserves-counts-accurate
  ;;     (implies (and (< 1 (nfix (num-nodes aignet)))
  ;;                   (not (and (equal (id->type (+ -1 (nfix (num-nodes aignet))) aignet) (out-type))
  ;;                             (equal (id->regp (+ -1 (nfix (num-nodes aignet))) aignet) 1)))
  ;;                   (aignet-nodes-nonconst aignet)
  ;;                   (aignet-counts-accurate aignet))
  ;;              (aignet-counts-accurate new-aignet)))

  ;;   ;; (local (defthm equal-of-update-nths

  ;;   (local (defthm update-nth-of-equal-nth
  ;;            (implies (and (equal (nth n y) (nth n x))
  ;;                          (< (nfix n) (len x)))
  ;;                     (equal (update-nth n (nth n y) x)
  ;;                            x))))

  ;;   (std::defret count-nodes-of-aignet-rollback-one
  ;;     (implies (and (< 1 (nfix (num-nodes aignet)))
  ;;                   (not (and (equal (id->type (+ -1 (nfix (num-nodes aignet))) aignet) (out-type))
  ;;                             (equal (id->regp (+ -1 (nfix (num-nodes aignet))) aignet) 1)))
  ;;                   (aignet-nodes-nonconst aignet)
  ;;                   (aignet-counts-accurate aignet)
  ;;                   (< (nfix m) (nfix (num-nodes aignet))))
  ;;              (equal (count-nodes m type regp new-aignet)
  ;;                     (- (count-nodes m type regp aignet)
  ;;                        (count-nodes (+ -1 (nfix (num-nodes aignet))) type regp aignet))))
  ;;     :hints (("goal" :expand ((count-nodes (+ -1 (nth *num-nodes* aignet)) type regp aignet)
  ;;                              (count-nodes (nth *num-nodes* aignet) type regp aignet)))))

  ;;   ;; (std::defret aignet-rollback-one-semantics
  ;;   ;;   (implies (and (aignetp aignet)
  ;;   ;;                 (< 1 (nfix (num-nodes aignet)))
  ;;   ;;                 (aignet-nodes-nonconst aignet)
  ;;   ;;                 (not (and (equal (id->type (+ -1 (nfix (num-nodes aignet))) aignet) (out-type))
  ;;   ;;                           (equal (id->regp (+ -1 (nfix (num-nodes aignet))) aignet) 1))))
  ;;   ;;            (equal new-aignet
  ;;   ;;                   (b* ((n (+ -1 (nfix (nth *num-nodes* aignet))))
  ;;   ;;                        (aignet0 aignet)
  ;;   ;;                        (aignet (update-nth *num-nodes* n aignet))
  ;;   ;;                        (aignet (update-nth *num-ins*
  ;;   ;;                                            (- (nfix (nth *num-ins* aignet0))
  ;;   ;;                                               (count-nodes n (in-type) 0 aignet0))
  ;;   ;;                                            aignet))
  ;;   ;;                        (aignet (update-nth *num-outs*
  ;;   ;;                                            (- (nfix (nth *num-outs* aignet0))
  ;;   ;;                                               (count-nodes n (out-type) 0 aignet0))
  ;;   ;;                                            aignet))
  ;;   ;;                        (aignet (update-nth *num-regs*
  ;;   ;;                                            (- (nfix (nth *num-regs* aignet0))
  ;;   ;;                                               (count-nodes n (in-type) 1 aignet0))
  ;;   ;;                                            aignet)))
  ;;   ;;                     aignet)))
  ;;   ;;   :hints (("goal" :in-theory (enable aignetp)
  ;;   ;;            :expand ((:free (type regp)
  ;;   ;;                      (count-nodes (+ -1 (nth *num-nodes* aignet)) type regp aignet))
  ;;   ;;                     (:free (type regp)
  ;;   ;;                      (count-nodes (nth *num-nodes* aignet) type regp aignet))))))

  ;;   (local (defthm nfix-decr-nfix
  ;;            (<= (nfix (+ -1 (nfix x))) (nfix x))
  ;;            :hints(("Goal" :in-theory (enable nfix)))))

  ;;   (std::defret aignet-rollback-one-preserves-gates-onlyp
  ;;     (implies (aignet-gates-onlyp n aignet)
  ;;              (aignet-gates-onlyp n new-aignet)))

  ;;   (std::defret aignet-rollback-one-preserves-nonconst
  ;;     (implies (aignet-nodes-nonconst aignet)
  ;;              (aignet-nodes-nonconst new-aignet))
  ;;     :hints ((and stable-under-simplificationp
  ;;                  `(:expand (,(car (last clause)))))))

  ;;   (std::defret id->slot-of-aignet-rollback-one
  ;;     (equal (id->slot n slot new-aignet)
  ;;            (id->slot n slot aignet)))

  ;;   (std::defret aignet-rollback-one-preserves-find-max-fanin
  ;;     (implies (and (< (+ 1 (nfix n)) (nfix (num-nodes aignet))))
  ;;              (equal (aignet-find-max-fanin n new-aignet)
  ;;                     (aignet-find-max-fanin n aignet)))))
  
  ;; (local (in-theory (disable aignet-sizes-ok
  ;;                            aignet-counts-accurate)))

  ;; (define aignet-rollback-aux ((n natp) aignet)
  ;;   :guard (and (aignet-sizes-ok aignet)
  ;;               (< (nfix n) (num-nodes aignet))
  ;;               (aignet-counts-accurate aignet)
  ;;               (ec-call (aignet-nodes-nonconst aignet))
  ;;               (aignet-gates-onlyp n aignet))
  ;;   :measure (nfix (- (nfix (num-nodes aignet)) (+ 1 (nfix n))))
  ;;   :guard-hints (("goal" :cases ((EQUAL (SNODE->TYPE (ID->SLOT (+ -1 (NTH *NUM-NODES* AIGNET))
  ;;                                                               0 AIGNET))
  ;;                                        (out-type)))))
  ;;   :prepwork ((local (in-theory (enable aignet-gates-onlyp-implies-not-nextst))))
  ;;   :returns (new-aignet)
  ;;   (b* (((when (mbe :logic (zp (- (nfix (num-nodes aignet)) (+ 1 (nfix n))))
  ;;                    :exec (int= (num-nodes aignet) (+ 1 n))))
  ;;         aignet)
  ;;        (aignet (aignet-rollback-one aignet)))
  ;;     (aignet-rollback-aux n aignet))
  ;;   ///
  ;;   (std::defret aignet-sizes-ok-of-aignet-rollback-aux
  ;;     (implies (and (aignet-sizes-ok aignet)
  ;;                   (aignet-gates-onlyp n aignet)
  ;;                   (aignet-nodes-nonconst aignet)
  ;;                   (aignet-counts-accurate aignet))
  ;;              (aignet-sizes-ok new-aignet)))

  ;;   (std::defret aignet-nodes-nonconst-of-aignet-rollback-aux
  ;;     (implies (aignet-nodes-nonconst aignet)
  ;;              (aignet-nodes-nonconst new-aignet)))

  ;;   (std::defret aignet-counts-accurate-of-aignet-rollback-aux
  ;;     (implies (and (aignet-gates-onlyp n aignet)
  ;;                   (aignet-nodes-nonconst aignet)
  ;;                   (aignet-counts-accurate aignet))
  ;;              (aignet-counts-accurate new-aignet)))

  ;;   (std::defret num-nodes-of-aignet-rollback-aux
  ;;     (implies (< (nfix n) (nfix (num-nodes aignet)))
  ;;              (equal (nth *num-nodes* new-aignet)
  ;;                     (+ 1 (nfix n)))))

  ;;   (std::defret id->slot-of-aignet-rollback-aux
  ;;     (equal (id->slot m slot new-aignet)
  ;;            (id->slot m slot aignet)))

  ;;   (std::defret aignet-rollback-aux-preserves-find-max-fanin
  ;;     (implies (and (<= (nfix m) (nfix n)))
  ;;              (equal (aignet-find-max-fanin m new-aignet)
  ;;                     (aignet-find-max-fanin m aignet))))

  ;;   (std::defret count-nodes-of-aignet-rollback-aux
  ;;     (implies (and (aignet-gates-onlyp n aignet)
  ;;                   (aignet-nodes-nonconst aignet)
  ;;                   (aignet-counts-accurate aignet)
  ;;                   (<= (nfix m) (nfix n)))
  ;;              (equal (count-nodes m type regp new-aignet)
  ;;                     (- (count-nodes m type regp aignet)
  ;;                        (count-nodes (+ 1 (nfix n)) type regp aignet))))
  ;;     :hints (("goal" :induct <call>)
  ;;             (and stable-under-simplificationp
  ;;                  '(:expand ((count-nodes (+ 1 n) type regp aignet)
  ;;                             (count-nodes (+ 1 (nfix n)) type regp aignet)
  ;;                             ;; (count-nodes (nth *num-nodes* aignet) type regp aignet)
  ;;                             )))))

  ;;   (local (in-theory (enable* aignet-frame-thms)))
  ;;   (def-aignet-frame aignet-rollback-aux))

  (local (defthm count-nodes-when-gates-onlyp
           (implies (and (not (equal type (gate-type)))
                         (aignet-gates-onlyp n aignet))
                    (equal (count-nodes n type regp aignet) 0))
           :hints(("Goal" :in-theory (enable count-nodes aignet-gates-onlyp)))))

  (local (defthm count-nodes-when-gates-onlyp-less
           (implies (and (not (equal type (gate-type)))
                         (aignet-gates-onlyp m aignet)
                         (<= (nfix m) (nfix n)))
                    (equal (count-nodes n type regp aignet) 0))
           :hints(("Goal" :in-theory (enable aignet-gates-onlyp)))))

  (local (defthm count-nodes-bound-when-gates-onlyp
           (implies (and (not (equal type (gate-type)))
                         (aignet-gates-onlyp n aignet)
                         (<= (nfix m) (nfix n)))
                    (<= (count-nodes m type regp aignet) (- (nfix n) (nfix m))))
           :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding
                                              (:i count-nodes))
                   :induct (count-nodes m type regp aignet))
                  (and stable-under-simplificationp
                       '(:expand ((count-nodes m type regp aignet)))))
           :rule-classes :linear))

  (local (defthm count-const-nodes-when-aignet-nodes-nonconst
           (implies (and (aignet-nodes-nonconst aignet)
                         (posp n))
                    (equal (count-nodes n 0 regp aignet) 0))
           :hints(("Goal" :in-theory (enable count-nodes)))))

  (local (defthmd aignet-gates-onlyp-implies-n-positive
           (implies (and (aignet-gates-onlyp n aignet)
                         (posp (nth *num-nodes* aignet))
                         (equal (snode->type (id->slot 0 0 aignet)) 0))
                    (posp n))
           :hints (("Goal" :expand ((aignet-gates-onlyp n aignet))))
           :rule-classes :forward-chaining))

  (local (defthm count-nodes-0-bound-when-gates-onlyp
           (implies (and (not (equal type (gate-type)))
                         (not (equal type (const-type)))
                         (aignet-nodes-nonconst aignet)
                         (aignet-gates-onlyp n aignet)
                         (posp (nth *num-nodes* aignet))
                         (equal (id->type 0 aignet) (const-type)))
                    (< (count-nodes 0 type regp aignet) (nfix n)))
           :hints (("goal" :expand ((count-nodes 0 type regp aignet))
                    :in-theory (enable aignet-gates-onlyp-implies-n-positive)))
           :rule-classes :linear))

  (define aignet-rollback ((n posp) aignet)
    :guard (and (aignet-sizes-ok aignet)
                (<= n (num-nodes aignet))
                (aignet-counts-accurate aignet)
                (ec-call (aignet-nodes-nonconst aignet))
                (aignet-gates-onlyp n aignet)
                (equal (id->type 0 aignet) (const-type)))
    :prepwork ((local (in-theory (enable* aignet-frame-thms))))
    :returns (new-aignet)
    (b* ((aignet (update-num-nodes n aignet)))
      (update-max-fanin
       (aignet-find-max-fanin (1- (acl2::lposfix n)) aignet)
       aignet))
    ///
    
    (local (defthm aignet-sizes-ok-of-update-max-fanin
             (implies (and (aignet-sizes-ok aignet)
                           (natp max-fanin))
                      (aignet-sizes-ok (update-nth *max-fanin* max-fanin aignet)))
             :hints(("Goal" :in-theory (enable aignet-sizes-ok)))))

    (std::defret aignet-sizes-ok-of-aignet-rollback
      (implies (and (aignet-sizes-ok aignet)
                    (posp n)
                    (<= n (nfix (num-nodes aignet)))
                    (aignet-gates-onlyp n aignet)
                    (aignet-nodes-nonconst aignet)
                    (aignet-counts-accurate aignet)
                    (equal (snode->type (id->slot 0 0 aignet)) (const-type)))
               (aignet-sizes-ok new-aignet)))

    (std::defret aignet-nodes-nonconst-of-aignet-rollback
      (implies (and (aignet-nodes-nonconst aignet)
                    (<= (nfix n) (nfix (num-nodes aignet))))
               (aignet-nodes-nonconst new-aignet))
      :hints(("Goal" :in-theory (enable* aignet-frame-thms))))

    (local (include-book "clause-processors/use-by-hint" :dir :system))

    (local (defthm count-nodes-of-update-num-nodes-when-nonconst
             (implies (and (aignet-gates-onlyp n aignet)
                           (not (equal type (gate-type)))
                           (<= (nfix m) (nfix n))
                           (<= (nfix n) (nfix (num-nodes aignet))))
                      (equal (count-nodes m type regp (update-nth *num-nodes* n aignet))
                             (count-nodes m type regp aignet)))
             :hints(("Goal" :in-theory (enable* (:i count-nodes)
                                                acl2::arith-equiv-forwarding
                                                aignet-gates-onlyp)
                     :induct (count-nodes m type regp aignet)
                     :expand ((:free (aignet)
                               (count-nodes m type regp aignet)))))))
                          
    (std::defret aignet-counts-accurate-of-aignet-rollback
      (implies (and (aignet-gates-onlyp n aignet)
                    (<= (nfix n) (nfix (num-nodes aignet)))
                    (aignet-nodes-nonconst aignet)
                    (aignet-counts-accurate aignet))
               (aignet-counts-accurate new-aignet)))

    (std::defret num-nodes-of-aignet-rollback
      (implies (<= (acl2::pos-fix n) (nfix (num-nodes aignet)))
               (equal (nth *num-nodes* new-aignet)
                      n)))

    (local
     (defthm out-type-of-greater-than-find-max-fanin-special
       (implies (and (bind-free '((n . (nfix n))) (n))
                     (< (aignet-find-max-fanin n aignet)
                        (nfix m))
                     (<= (nfix m) (nfix n)))
                (equal (snode->type (id->slot m 0 aignet)) (out-type)))
       :hints (("goal" :use out-type-of-greater-than-find-max-fanin))))

    (std::defret max-fanin-correct-of-aignet-rollback
      (implies (and (nat-equiv (nth *max-fanin* aignet)
                               (aignet-find-max-fanin (+ -1 (nfix (num-nodes aignet))) aignet))
                    (equal (id->type 0 aignet) 0)
                    (<= (nfix n) (nfix (num-nodes aignet))))
               (nat-equiv (nth *max-fanin* new-aignet)
                          (aignet-find-max-fanin (+ -1 (acl2::pos-fix n)) new-aignet)))
      :hints(("Goal" :in-theory (enable* ;; aignet-max-fanin-correct
                                         out-type-of-greater-than-find-max-fanin
                                         aignet-frame-thms))
             (and stable-under-simplificationp
                  '(:use ((:instance aignet-find-max-fanin-of-lesser-n-when-less
                           (m (+ -1 (num-nodes aignet)))
                           (n (nfix n)))))))

             ;; (and stable-under-simplificationp
             ;;      (let ((lit (car (last clause))))
             ;;        (and (eq (car lit) 'aignet-max-fanin-sufficient)
             ;;             `(:expand (,lit)))))
             )



    ;; (std::defretd count-nodes-of-aignet-rollback
    ;;   (implies (and (aignet-gates-onlyp n aignet)
    ;;                 (aignet-nodes-nonconst aignet)
    ;;                 (aignet-counts-accurate aignet)
    ;;                 (<= (nfix m) (nfix n)))
    ;;            (equal (count-nodes m type regp new-aignet)
    ;;                   (- (count-nodes m type regp aignet)
    ;;                      (count-nodes (+ 1 (nfix n)) type regp aignet)))))

    ;; (std::defret num-regs-of-aignet-rollback
    ;;   (implies (and (aignet-gates-onlyp n aignet)
    ;;                 (aignet-nodes-nonconst aignet)
    ;;                 (aignet-counts-accurate aignet))
    ;;            (nat-equiv (nth *num-regs* new-aignet)
    ;;                       (- (nfix (nth *num-regs* aignet))
    ;;                          (count-nodes (+ 1 (nfix n)) (in-type) 1 aignet))))
    ;;   :hints(("Goal" :in-theory (e/d (aignet-counts-accurate
    ;;                                   count-nodes-of-aignet-rollback)
    ;;                                  (aignet-rollback
    ;;                                   aignet-counts-accurate-of-aignet-rollback))
    ;;           :use aignet-counts-accurate-of-aignet-rollback)))

    ;; (std::defret num-ins-of-aignet-rollback
    ;;   (implies (and (aignet-gates-onlyp n aignet)
    ;;                 (aignet-nodes-nonconst aignet)
    ;;                 (aignet-counts-accurate aignet))
    ;;            (nat-equiv (nth *num-ins* new-aignet)
    ;;                       (- (nfix (nth *num-ins* aignet))
    ;;                          (count-nodes (+ 1 (nfix n)) (in-type) 0 aignet))))
    ;;   :hints(("Goal" :in-theory (e/d (aignet-counts-accurate
    ;;                                   count-nodes-of-aignet-rollback)
    ;;                                  (aignet-rollback
    ;;                                   aignet-counts-accurate-of-aignet-rollback))
    ;;           :use aignet-counts-accurate-of-aignet-rollback)))

    ;; (std::defret num-outs-of-aignet-rollback
    ;;   (implies (and (aignet-gates-onlyp n aignet)
    ;;                 (aignet-nodes-nonconst aignet)
    ;;                 (aignet-counts-accurate aignet))
    ;;            (nat-equiv (nth *num-outs* new-aignet)
    ;;                       (- (nfix (nth *num-outs* aignet))
    ;;                          (count-nodes (+ 1 (nfix n)) (out-type) 0 aignet))))
    ;;   :hints(("Goal" :in-theory (e/d (aignet-counts-accurate
    ;;                                   count-nodes-of-aignet-rollback)
    ;;                                  (aignet-rollback
    ;;                                   aignet-counts-accurate-of-aignet-rollback))
    ;;           :use aignet-counts-accurate-of-aignet-rollback)))

    ;; (local (defthm count-nodes-when-aignet-gates-onlyp
    ;;          (implies (and (aignet-gates-onlyp n aignet)
    ;;                        (< (nfix n) (nfix m)))
    ;;                   (equal (count-nodes m (out-type) 1 aignet) 0))
    ;;          :hints(("Goal" :in-theory (enable count-nodes
    ;;                                            aignet-gates-onlyp-implies-not-nextst)))))

    ;; (std::defret num-nxsts-of-aignet-rollback
    ;;   (implies (and (aignet-gates-onlyp n aignet)
    ;;                 (aignet-nodes-nonconst aignet)
    ;;                 (aignet-counts-accurate aignet))
    ;;            (nat-equiv (nth *num-nxsts* new-aignet)
    ;;                       (nth *num-nxsts* aignet)))
    ;;   :hints(("Goal" :in-theory (e/d (aignet-counts-accurate
    ;;                                   count-nodes-of-aignet-rollback)
    ;;                                  (aignet-rollback
    ;;                                   aignet-counts-accurate-of-aignet-rollback))
    ;;           :use aignet-counts-accurate-of-aignet-rollback)))

    (def-aignet-frame aignet-rollback)
    
    
    (std::defret id->slot-of-aignet-rollback-below
      (implies (<= (nfix m) (nfix n))
               (equal (id->slot m slot new-aignet)
                      (id->slot m slot aignet))))

    (std::defret find-max-fanin-of-aignet-rollback
      (implies (<= (nfix m) (nfix n))
               (equal (aignet-find-max-fanin m new-aignet)
                      (aignet-find-max-fanin m aignet)))
      :hints(("Goal" :in-theory (e/d (aignet-find-max-fanin)
                                     (aignet-rollback)))))))
    
    

(defsection aignet-init
  (local (defthm consp-of-resize-list
           (equal (Consp (resize-list lst n default))
                  (posp n))
           :hints(("Goal" :in-theory (enable resize-list)))))
  ;; Clears the aignet without resizing, unless the node array is size 0.
  (defun aignet-clear (aignet)
    (declare (xargs :stobjs aignet
                    :guard-debug t))
    (b* ((aignet (update-num-ins 0 aignet))
         (aignet (update-num-regs 0 aignet))
         (aignet (update-max-fanin 0 aignet))
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


  (define aignet-init ((max-outs :type (unsigned-byte 29))
                       (max-regs :type (unsigned-byte 29))
                       (max-ins :type (unsigned-byte 29))
                       (max-nodes posp :type (unsigned-byte 29))
                       aignet)
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
