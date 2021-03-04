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
(include-book "semantics")
(include-book "lit-lists")
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/take" :dir :system))

;; (local (include-book "data-structures/list-defthms" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))
(local (in-theory (disable nth update-nth
                           acl2::nfix-when-not-natp
                           resize-list
                           ;; acl2::resize-list-when-empty
                           acl2::resize-list-when-atom
                           ;; acl2::make-list-ac-redef
                           make-list-ac)))

(local (in-theory (disable true-listp-update-nth
                           ;; acl2::nth-with-large-index
                           )))

(local (std::add-default-post-define-hook :fix))

(defsection aignet-eval
 :parents (aignet)
  :short "Evaluating AIGNET networks"
  :autodoc nil
  :long "
<p>The (combinational) semantics of an AIGNET network is given by the function</p>
@({(lit-eval lit invals regvals aignet).})
<p>Invals and regvals are bit arrays containing a value for each (respectively)
primary input and register node in the network.  But because this function is a
simple recursive specification for the semantics of a node and not written for
performance, it is likely to perform badly (worst-case exponential time in the
size of the network).</p>

<p>To actually execute evaluations of nodes, instead do the following:</p>

@({
 (b* ((vals ;; Resize vals to have one bit for each aignet node.
       (resize-bits (num-fanins aignet) vals))
      (vals ;; Copy primary input values from invals into vals.
       (aignet-invals->vals invals vals aignet))
      (vals ;; Copy register values from regvals into vals.
       (aignet-regvals->vals regvals vals aignet))
      (vals ;; Record the evaluations of all other nodes in vals.
       (aignet-eval vals aignet))
      (lit-value1 ;; Look up the value of a particular literal of interest.
       (aignet-eval-lit lit1 vals))
      (lit-value2 ;; Look up another literal.
       (aignet-eval-lit lit2 vals)))
  ...)
 })

<p>(Note: invals and regvals have a different layout than vals; they include
only one entry per (respectively) primary input or register instead of one
entry per node, so they are indexed by I/O number whereas vals is indexed by
node ID.)</p>

<p>The following theorem shows the correspondence between a literal looked up
in @('vals') after running aignet-eval and the @('lit-eval') of that
literal:</p>
 @(thm aignet-eval-lit-of-aignet-eval)

<p>These theorems resolve the copying between invals/regvals and @('vals'):</p>
 @(thm aignet-vals->invals-of-aignet-invals->vals)
 @(thm aignet-vals->invals-of-aignet-regvals->vals)
 @(thm aignet-vals->regvals-of-aignet-regvals->vals)
 @(thm aignet-vals->regvals-of-aignet-invals->vals)

<p>For higher-level functions for simulation, see the book \"aig-sim.lisp\".</p>
"
  (local (in-theory (disable acl2::bfix-when-not-1
                             acl2::nfix-when-not-natp)))


  ;; (local (in-theory (disable acl2::nth-with-large-index)))

  (definline aignet-eval-lit (lit vals)
    (declare (type (integer 0 *) lit)
             (xargs :stobjs vals
                    :guard (and (litp lit)
                                (< (lit-id lit) (bits-length vals)))))
    (b-xor (lit-neg lit)
           (get-bit (lit-id lit) vals)))

  ;; (local (in-theory (enable nth-in-aignet-valsp-bound
  ;;                           nth-in-aignet-valsp-type)))

  (local (in-theory (disable bitops::logxor-equal-0)))

  (local (in-theory (enable aignet-idp)))

  (defiteration
    aignet-eval (vals aignet)
    (declare (xargs :stobjs (vals aignet)
                    :guard (<= (num-fanins aignet) (bits-length vals))))
    (b* ((n (lnfix n))
         (nid n)
         (slot0 (id->slot nid 0 aignet))
         (type (snode->type slot0)))
      (aignet-case
       type
       :gate  (b* ((f0 (snode->fanin slot0))
                   (slot1 (id->slot nid 1 aignet))
                   (f1 (snode->fanin slot1))
                   (xor (snode->regp slot1))
                   (v0 (aignet-eval-lit f0 vals))
                   (v1 (aignet-eval-lit f1 vals))
                   (val (if (eql xor 1)
                            (b-xor v0 v1)
                          (b-and v0 v1))))
                (set-bit nid val vals))
       :const (set-bit nid 0 vals)
       :in    vals))
    :index n
    :returns vals
    :last (num-fanins aignet)
    :package aignet::foo)

  (in-theory (disable aignet-eval))
  (local (in-theory (enable aignet-eval)))

  (local (defthm bit-listp-of-update-nth
           (implies (and (bit-listp x)
                         (< (nfix n) (len x))
                         (bitp val))
                    (bit-listp (update-nth n val x)))
           :hints(("Goal" :in-theory (enable update-nth)))))

  (defthm aignet-eval-iter-preserves-size
    (implies (and (<= (num-fanins aignet) (len vals))
                  (<= (nfix n) (num-fanins aignet)))
             (equal (len (aignet-eval-iter n vals aignet))
                    (len vals)))
    :hints ((acl2::just-induct-and-expand
             (aignet-eval-iter n vals aignet))))

  (defthm aignet-eval-preserves-size
    (implies (<= (num-fanins aignet) (len vals))
             (equal (len (aignet-eval vals aignet))
                    (len vals)))
    :hints(("Goal" :in-theory (enable aignet-eval))))

  (defthm aignet-eval-iter-preserves-bit-listp
    (implies (and (bit-listp vals)
                  (<= (nfix n) (num-fanins aignet))
                  (<= (num-fanins aignet) (len vals)))
             (bit-listp (aignet-eval-iter n vals aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet-eval-iter n vals aignet))))

  (defthm aignet-eval-preserves-bit-listp
    (implies (and (bit-listp vals)
                  (<= (num-fanins aignet) (len vals)))
             (bit-listp (aignet-eval vals aignet)))
    :hints(("Goal" :in-theory (enable aignet-eval))))

  (defthm aignet-vals-well-sizedp-after-aignet-eval-iter
    (<= (len vals)
        (len (aignet-eval-iter n vals aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet-eval-iter n vals aignet)))
    :rule-classes :linear)

  (defthm aignet-vals-well-sizedp-after-aignet-eval
    (<= (len vals)
        (len (aignet-eval vals aignet)))
    :rule-classes :linear)

  (fty::deffixequiv aignet-eval-iter :args ((aignet aignet)))
  (fty::deffixequiv acl2::aignet-eval$inline :args ((aignet aignet)))

  (defiteration aignet-vals->invals (invals vals aignet)
    (declare (xargs :stobjs (vals aignet invals)
                    :guard (and (<= (num-fanins aignet) (bits-length vals))
                                (<= (num-ins aignet) (bits-length invals)))))
    (b* ((id (innum->id n aignet))
         (val (get-bit id vals)))
      (set-bit n val invals))
    :returns invals
    :index n
    :last (num-ins aignet))

  (in-theory (disable aignet-vals->invals))
  (local (in-theory (enable aignet-vals->invals)))


  (defthm nth-of-aignet-vals->invals-iter
    (implies (<= (nfix m) (num-ins aignet))
             (bit-equiv
              (nth n (aignet-vals->invals-iter m in-vals vals aignet))
              (if (< (nfix n) (nfix m))
                  (nth (innum->id n aignet)
                       vals)
                (nth n in-vals))))
    :hints ((acl2::just-induct-and-expand (aignet-vals->invals-iter m in-vals
                                                                    vals
                                                                    aignet))))

  (defthm nth-of-aignet-vals->invals
    (bit-equiv
     (nth n (aignet-vals->invals in-vals vals aignet))
     (if (< (nfix n) (num-ins aignet))
         (nth (innum->id n aignet)
              vals)
       (nth n in-vals))))

  (fty::deffixequiv aignet-vals->invals-iter :args ((aignet aignet)))
  (fty::deffixequiv aignet-vals->invals$inline :args ((aignet aignet)))

  (defthm len-of-aignet-vals->invals-iter
    (implies (and (<= (num-ins aignet) (len invals))
                  (<= (nfix n) (num-ins aignet)))
             (equal (len (aignet-vals->invals-iter n invals vals aignet))
                    (len invals)))
    :hints(("Goal" :in-theory (enable aignet-vals->invals-iter))))

  (defthm len-of-aignet-vals->invals
    (implies (<= (num-ins aignet) (len invals))
             (equal (len (aignet-vals->invals invals vals aignet))
                    (len invals)))
    :hints(("Goal" :in-theory (enable aignet-vals->invals))))

  (defiteration aignet-invals->vals (invals vals aignet)
    (declare (xargs :stobjs (vals aignet invals)
                    :guard (and (<= (num-fanins aignet) (bits-length vals))
                                (<= (num-ins aignet) (bits-length invals)))))
    (b* ((id (innum->id n aignet))
         (val (get-bit n invals)))
      (set-bit id val vals))
    :returns vals
    :index n
    :last (num-ins aignet))

  (in-theory (disable aignet-invals->vals))
  (local (in-theory (enable aignet-invals->vals)))

  (defthm aignet-invals->vals-iter-preserves-size
    (implies (and (<= (num-fanins aignet) (len vals)))
             (equal (len (aignet-invals->vals-iter n invals vals aignet))
                    (len vals)))
    :hints ((acl2::just-induct-and-expand
             (aignet-invals->vals-iter n invals vals aignet))))

  (defthm aignet-invals->vals-preserves-size
    (implies (<= (num-fanins aignet) (len vals))
             (equal (len (aignet-invals->vals invals vals aignet))
                    (len vals)))
    :hints(("Goal" :in-theory (enable aignet-invals->vals))))

  (defthm aignet-invals->vals-iter-preserves-bit-listp
    (implies (and (bit-listp vals)
                  (<= (num-fanins aignet) (len vals)))
             (bit-listp (aignet-invals->vals-iter n invals vals aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet-invals->vals-iter n invals vals aignet))))

  (defthm aignet-invals->vals-preserves-bit-listp
    (implies (and (bit-listp vals)
                  (<= (num-fanins aignet) (len vals)))
             (bit-listp (aignet-invals->vals invals vals aignet)))
    :hints(("Goal" :in-theory (enable aignet-invals->vals))))


  (defthm nth-of-aignet-invals->vals-iter
    (implies (<= (nfix m) (num-ins aignet))
             (bit-equiv
              (nth n (aignet-invals->vals-iter m invals vals aignet))
              (if (and (< (nfix n) (num-fanins aignet))
                       (equal (id->type n aignet) (in-type))
                       (equal (id->regp n aignet) 0)
                       (< (ci-id->ionum n aignet) (nfix m)))
                  (nth (ci-id->ionum n aignet) invals)
                (nth n vals))))
    :hints((acl2::just-induct-and-expand
            (aignet-invals->vals-iter m invals vals aignet))
           (and stable-under-simplificationp
                '(:in-theory (enable lookup-stype-in-bounds)))))

  (defthm nth-of-aignet-invals->vals
    (bit-equiv
     (nth n (aignet-invals->vals invals vals aignet))
     (if (and (< (nfix n) (num-fanins aignet))
              (equal (id->type n aignet) (in-type))
              (equal (id->regp n aignet) 0)
              (< (ci-id->ionum n aignet) (num-ins aignet)))
         (nth (ci-id->ionum n aignet) invals)
       (nth n vals))))

  (defthm memo-tablep-of-aignet-invals->vals-iter
    (implies (< (fanin-count aignet) (len vals))
             (<
              (fanin-count aignet)
              (len (aignet-invals->vals-iter m invals vals aignet))))
    :hints((acl2::just-induct-and-expand
            (aignet-invals->vals-iter m invals vals aignet)))
    :rule-classes :linear)

  (defthm memo-tablep-of-aignet-invals->vals
    (implies (< (fanin-count aignet) (len vals))
             (<
              (fanin-count aignet)
              (len (aignet-invals->vals invals vals aignet))))
    :rule-classes :linear)

  (fty::deffixequiv aignet-invals->vals-iter :args ((aignet aignet)))
  (fty::deffixequiv aignet-invals->vals$inline :args ((aignet aignet)))

  (defthm aignet-invals->vals-iter-of-take
    (implies (and (<= (stype-count :pi aignet) (nfix k))
                  (<= (nfix n) (stype-count :pi aignet)))
             (equal (aignet-invals->vals-iter n (take k invals) vals aignet)
                    (aignet-invals->vals-iter n invals vals aignet)))
    :hints(("Goal" :in-theory (enable aignet-invals->vals-iter))))

  (defthm aignet-invals->vals-of-take
    (implies (<= (stype-count :pi aignet) (nfix k))
             (equal (aignet-invals->vals (take k invals) vals aignet)
                    (aignet-invals->vals invals vals aignet)))
    :hints(("Goal" :in-theory (enable aignet-invals->vals))))

  (defiteration aignet-vals->regvals (regvals vals aignet)
    (declare (xargs :stobjs (vals aignet regvals)
                    :guard (and (<= (num-fanins aignet) (bits-length vals))
                                (<= (num-regs aignet) (bits-length regvals)))))
    (b* ((id (regnum->id n aignet))
         (val (get-bit id vals)))
      (set-bit n val regvals))
    :returns regvals
    :index n
    :last (num-regs aignet))

  (in-theory (disable aignet-vals->regvals))
  (local (in-theory (enable aignet-vals->regvals)))


  (defthm nth-of-aignet-vals->regvals-iter
    (implies (<= (nfix m) (num-regs aignet))
             (bit-equiv
              (nth n (aignet-vals->regvals-iter m reg-vals vals aignet))
              (if (< (nfix n) (nfix m))
                  (nth (regnum->id n aignet)
                       vals)
                (nth n reg-vals))))
    :hints ((acl2::just-induct-and-expand (aignet-vals->regvals-iter m reg-vals
                                                                     vals
                                                                     aignet))))

  (defthm nth-of-aignet-vals->regvals
    (bit-equiv
     (nth n (aignet-vals->regvals reg-vals vals aignet))
     (if (< (nfix n) (num-regs aignet))
         (nth (regnum->id n aignet)
              vals)
       (nth n reg-vals))))

  (fty::deffixequiv aignet-vals->regvals-iter :args ((aignet aignet)))
  (fty::deffixequiv aignet-vals->regvals$inline :args ((aignet aignet)))

  (defthm len-of-aignet-vals->regvals-iter
    (implies (and (<= (num-regs aignet) (len regvals))
                  (<= (nfix n) (num-regs aignet)))
             (equal (len (aignet-vals->regvals-iter n regvals vals aignet))
                    (len regvals)))
    :hints(("Goal" :in-theory (enable aignet-vals->regvals-iter))))

  (defthm len-of-aignet-vals->regvals
    (implies (<= (num-regs aignet) (len regvals))
             (equal (len (aignet-vals->regvals regvals vals aignet))
                    (len regvals)))
    :hints(("Goal" :in-theory (enable aignet-vals->regvals))))


  (defiteration aignet-regvals->vals (regvals vals aignet)
    (declare (xargs :stobjs (vals aignet regvals)
                    :guard (and (<= (num-fanins aignet) (bits-length vals))
                                (<= (num-regs aignet) (bits-length regvals)))))
    (b* ((id (regnum->id n aignet))
         (val (get-bit n regvals)))
      (set-bit id val vals))
    :returns vals
    :index n
    :last (num-regs aignet))

  (in-theory (disable aignet-regvals->vals))
  (local (in-theory (enable aignet-regvals->vals)))


  (defthm aignet-regvals->vals-iter-preserves-size
    (implies (and (<= (num-fanins aignet) (len vals)))
             (equal (len (aignet-regvals->vals-iter n regvals vals aignet))
                    (len vals)))
    :hints ((acl2::just-induct-and-expand
             (aignet-regvals->vals-iter n regvals vals aignet))))

  (defthm aignet-regvals->vals-preserves-size
    (implies (<= (num-fanins aignet) (len vals))
             (equal (len (aignet-regvals->vals regvals vals aignet))
                    (len vals)))
    :hints(("Goal" :in-theory (enable aignet-regvals->vals))))

  (defthm aignet-regvals->vals-iter-size-nondecr
    (>= (len (aignet-regvals->vals-iter n regvals vals aignet))
        (len vals))
    :hints ((acl2::just-induct-and-expand
             (aignet-regvals->vals-iter n regvals vals aignet)))
    :rule-classes :linear)

  (defthm aignet-regvals->vals-size-nondecr
    (>= (len (aignet-regvals->vals regvals vals aignet))
        (len vals))
    :hints(("Goal" :in-theory (enable aignet-regvals->vals)))
    :rule-classes :linear)


  (defthm aignet-regvals->vals-iter-preserves-bit-listp
    (implies (and (bit-listp vals)
                  (<= (num-fanins aignet) (len vals)))
             (bit-listp (aignet-regvals->vals-iter n regvals vals aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet-regvals->vals-iter n regvals vals aignet))))

  (defthm aignet-regvals->vals-preserves-bit-listp
    (implies (and (bit-listp vals)
                  (<= (num-fanins aignet) (len vals)))
             (bit-listp (aignet-regvals->vals regvals vals aignet)))
    :hints(("Goal" :in-theory (enable aignet-regvals->vals))))


  (defthm nth-of-aignet-regvals->vals-iter
    (implies (<= (nfix m) (num-regs aignet))
             (bit-equiv
              (nth n (aignet-regvals->vals-iter m regvals vals aignet))
              (if (and (< (nfix n) (num-fanins aignet))
                       (equal (id->type n aignet) (in-type))
                       (equal (id->regp n aignet) 1)
                       (< (ci-id->ionum n aignet) (nfix m)))
                  (nth (ci-id->ionum n aignet) regvals)
                (nth n vals))))
    :hints((acl2::just-induct-and-expand
            (aignet-regvals->vals-iter m regvals vals aignet))
           (and stable-under-simplificationp
                '(:in-theory (enable lookup-stype-in-bounds)))))

  (defthm nth-of-aignet-regvals->vals
    (bit-equiv
     (nth n (aignet-regvals->vals regvals vals aignet))
     (if (and (< (nfix n) (num-fanins aignet))
              (equal (id->type n aignet) (in-type))
              (equal (id->regp n aignet) 1)
              (< (ci-id->ionum n aignet) (num-regs aignet)))
         (nth (ci-id->ionum n aignet) regvals)
       (nth n vals))))

  (defthm memo-tablep-of-aignet-regvals->vals-iter
    (implies (< (fanin-count aignet) (len vals))
             (<
              (fanin-count aignet)
              (len (aignet-regvals->vals-iter m regvals vals aignet))))
    :hints((acl2::just-induct-and-expand
            (aignet-regvals->vals-iter m regvals vals aignet)))
    :rule-classes :linear)

  (defthm memo-tablep-of-aignet-regvals->vals
    (implies (< (fanin-count aignet) (len vals))
             (<
              (fanin-count aignet)
              (len (aignet-regvals->vals regvals vals aignet))))
    :rule-classes :linear)

  (defcong bits-equiv equal (aignet-invals->vals-iter n invals vals aignet) 2
    :hints(("Goal" :in-theory (enable aignet-invals->vals-iter))))

  (defcong bits-equiv equal (aignet-invals->vals invals vals aignet) 1
    :hints(("Goal" :in-theory (enable aignet-invals->vals))))

  (defcong bits-equiv equal (aignet-regvals->vals-iter n regvals vals aignet) 2
    :hints(("Goal" :in-theory (enable aignet-regvals->vals-iter))))

  (defcong bits-equiv equal (aignet-regvals->vals regvals vals aignet) 1
    :hints(("Goal" :in-theory (enable aignet-regvals->vals))))



  (defthm aignet-regvals->vals-iter-of-take
    (implies (and (<= (stype-count :reg aignet) (nfix k))
                  (<= (nfix n) (stype-count :reg aignet)))
             (equal (aignet-regvals->vals-iter n (take k regvals) vals aignet)
                    (aignet-regvals->vals-iter n regvals vals aignet)))
    :hints(("Goal" :in-theory (enable aignet-regvals->vals-iter))))

  (defthm aignet-regvals->vals-of-take
    (implies (<= (stype-count :reg aignet) (nfix k))
             (equal (aignet-regvals->vals (take k regvals) vals aignet)
                    (aignet-regvals->vals regvals vals aignet)))
    :hints(("Goal" :in-theory (enable aignet-regvals->vals))))

  (defcong bits-equiv equal
    (aignet-vals->invals-iter n invals vals aignet) 3
    :hints(("Goal" :in-theory (enable aignet-vals->invals-iter))))
  (defcong bits-equiv equal (aignet-vals->invals invals vals aignet) 2)

  (defcong bits-equiv equal
    (aignet-vals->regvals-iter n regvals vals aignet) 3
    :hints(("Goal" :in-theory (enable aignet-vals->regvals-iter))))
  (defcong bits-equiv equal (aignet-vals->regvals regvals vals aignet) 2)

  (fty::deffixequiv aignet-regvals->vals-iter :args ((aignet aignet)))
  (fty::deffixequiv aignet-regvals->vals$inline :args ((aignet aignet)))


  (defthm id-eval-of-in/regvals-of-aignet-vals-of-in/regvals-iters
    (let* ((vals (aignet-invals->vals-iter
                         (stype-count (pi-stype) aignet)
                         invals vals aignet))
           (vals (aignet-regvals->vals-iter
                         (stype-count (reg-stype) aignet)
                         regvals vals aignet))
           (invals (aignet-vals->invals-iter
                    (stype-count (pi-stype) aignet)
                    invals vals aignet))
           (regvals (aignet-vals->regvals-iter
                     (stype-count (reg-stype) aignet)
                     regvals vals aignet)))
      (bit-equiv (id-eval id invals regvals aignet)
                 (id-eval id invals regvals aignet)))
    :hints (("Goal" :induct
             (id-eval-ind id aignet))
            '(:in-theory (e/d* (lit-eval
                                eval-and-of-lits)
                               (id-eval))
              :do-not-induct t
              :expand
              ((:free (regvals invals)
                (id-eval 0 invals regvals aignet))
               (:free (regvals invals)
                (id-eval id invals regvals aignet))))))

  (defthm id-eval-of-in/regvals-of-aignet-vals-of-in/regvals
    (let* ((vals (aignet-invals->vals
                         invals vals aignet))
           (vals (aignet-regvals->vals
                         regvals vals aignet))
           (invals (aignet-vals->invals
                    invals vals aignet))
           (regvals (aignet-vals->regvals
                     regvals vals aignet)))
      (bit-equiv (id-eval id invals regvals aignet)
                 (id-eval id invals regvals aignet))))

  (defthm aignet-eval-iter-preserves-ci-val
    (implies (equal (id->type id aignet) (in-type))
             (equal (nth id (aignet-eval-iter n vals
                                                           aignet))
                    (nth id vals)))
    :hints ((acl2::just-induct-and-expand
             (aignet-eval-iter n vals aignet))))

  (defthm aignet-eval-preserves-ci-val
    (implies (equal (id->type id aignet) (in-type))
             (equal (nth id (aignet-eval vals aignet))
                    (nth id vals)))
    :hints ((acl2::just-induct-and-expand
             (aignet-eval-iter n vals aignet))))

  (defthm aignet-eval-iter-preserves-in-vals
    (implies (<= (nfix n) (num-ins aignet))
             (equal (aignet-vals->invals-iter n in-vals
                                              (aignet-eval-iter m vals aignet)
                                              aignet)
                    (aignet-vals->invals-iter n in-vals vals aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet-vals->invals-iter n in-vals vals aignet)
             :expand-others
             ((:free (vals)
               (aignet-vals->invals-iter n in-vals vals aignet))))))

  (defthm aignet-eval-preserves-in-vals
    (equal (aignet-vals->invals in-vals
                                (aignet-eval vals aignet)
                                aignet)
           (aignet-vals->invals in-vals vals aignet)))

  (defthm aignet-eval-iter-preserves-reg-vals
    (implies (<= (nfix n) (num-regs aignet))
             (equal (aignet-vals->regvals-iter n reg-vals
                                               (aignet-eval-iter m vals aignet)
                                               aignet)
                    (aignet-vals->regvals-iter n reg-vals vals aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet-vals->regvals-iter n reg-vals vals aignet)
             :expand-others
             ((:free (vals)
               (aignet-vals->regvals-iter n reg-vals vals aignet))))))

  (defthm aignet-eval-preserves-reg-vals
    (equal (aignet-vals->regvals reg-vals
                                 (aignet-eval vals aignet)
                                 aignet)
           (aignet-vals->regvals reg-vals vals aignet)))


  (local (defthm bfix-when-equal-b-and
           (implies (equal x (b-and a b))
                    (equal (bfix x) x))))

  (defthmd nth-in-aignet-eval-iter-preserved
    (implies (and (< (nfix m) (nfix n))
                  (equal nm (1+ (nfix m)))
                  (syntaxp (not (equal n nm))))
             (equal (nth m (aignet-eval-iter n vals
                                                          aignet))
                    (nth m (aignet-eval-iter nm vals
                                                          aignet))))
    :hints ((acl2::just-induct-and-expand (aignet-eval-iter n vals aignet))
            '(:in-theory (disable b-xor b-and
                                  aignet-eval-lit
                                  (:definition aignet-eval-iter)))
            (and stable-under-simplificationp
                 '(:expand ((aignet-eval-iter n vals
                                              aignet)
                            (aignet-eval-iter (+ 1 (nfix m)) vals
                                              aignet))))))


  (defthm aignet-eval-iter-nth-previous
    (implies (<= (nfix n) (nfix m))
             (equal (nth m (aignet-eval-iter n vals aignet))
                    (nth m vals)))
    :hints ((acl2::just-induct-and-expand
             (aignet-eval-iter n vals aignet))
            '(:in-theory (disable nth-in-aignet-eval-iter-preserved
                                  aignet-eval-iter))))

  (defthm aignet-eval-nth-previous
    (implies (<= (nfix (num-fanins aignet)) (nfix m))
             (equal (nth m (aignet-eval vals aignet))
                    (nth m vals))))

  (defthm aignet-eval-records-id-evals-lemma
    (implies (and (bind-free '((invals . 'nil) (regvals . 'nil))
                             (invals regvals))
                  (< (nfix id) (nfix n))
                  (<= (nfix n) (nfix (num-fanins aignet))))
             (bit-equiv (nth id (aignet-eval-iter n vals aignet))
                        (id-eval id
                                 (aignet-vals->invals invals vals aignet)
                                 (aignet-vals->regvals regvals vals aignet)
                                 aignet)))
    :hints ((acl2::just-induct-and-expand
             (id-eval-ind id aignet)
             :expand-others
             ((id-eval id (aignet-vals->invals invals vals aignet)
                       (aignet-vals->regvals regvals vals aignet)
                       aignet)))
            '(:in-theory (enable* lit-eval eval-and-of-lits eval-xor-of-lits
                                  nth-in-aignet-eval-iter-preserved
                                  aignet-idp)
              :expand ((aignet-eval-iter
                        (+ 1 (nfix id)) vals aignet))))
    :rule-classes nil)

  (defthm aignet-eval-iter-records-id-evals
    (implies (and (bind-free '((invals . 'nil) (regvals . 'nil))
                             (invals regvals))
                  (< (nfix id) (nfix n))
                  (<= (nfix n) (num-fanins aignet)))
             (bit-equiv (nth id (aignet-eval-iter n vals aignet))
                        (id-eval id
                                 (aignet-vals->invals invals vals aignet)
                                 (aignet-vals->regvals regvals vals aignet)
                                 aignet)))
    :hints (("goal" :use ((:instance aignet-eval-records-id-evals-lemma
                           (id id))))))


  (defthm id-eval-of-aignet-vals->invals-normalize
    (implies (and (syntaxp (not (equal invals ''nil)))
                  (aignet-idp id aignet))
             (equal (id-eval id (aignet-vals->invals
                                 invals vals aignet)
                             regvals aignet)
                    (id-eval id (aignet-vals->invals
                                 nil vals aignet)
                             regvals aignet)))
    :hints (("goal" :induct (id-eval-ind id aignet)
             :in-theory (enable lit-eval eval-and-of-lits eval-xor-of-lits)
             :expand ((:free (invals regvals)
                       (id-eval id invals regvals aignet))))))

  (defthm id-eval-of-aignet-vals->regvals-normalize
    (implies (and (syntaxp (not (equal regvals ''nil)))
                  (aignet-idp id aignet))
             (equal (id-eval id invals
                             (aignet-vals->regvals
                              regvals vals aignet)
                             aignet)
                    (id-eval id
                             invals
                             (aignet-vals->regvals
                              nil vals aignet)
                             aignet)))
    :hints (("goal" :induct (id-eval-ind id aignet)
             :in-theory (enable lit-eval eval-and-of-lits eval-xor-of-lits)
             :expand ((:free (invals regvals)
                       (id-eval id invals regvals aignet))))))


  (defthm aignet-eval-records-id-evals
    (implies (and (bind-free '((invals . 'nil) (regvals . 'nil))
                             (invals regvals))
                  (aignet-idp id aignet))
             (bit-equiv (nth id (aignet-eval vals aignet))
                        (id-eval id
                                 (aignet-vals->invals invals vals aignet)
                                 (aignet-vals->regvals regvals vals aignet)
                                 aignet)))
    :hints(("Goal" :in-theory (e/d (aignet-idp)
                                   (aignet-vals->invals
                                    aignet-vals->regvals)))))

  (defthm aignet-eval-lit-of-aignet-eval
    (implies (aignet-idp (lit-id lit) aignet)
             (equal (aignet-eval-lit lit (aignet-eval vals aignet))
                    (lit-eval lit
                              (aignet-vals->invals nil vals aignet)
                              (aignet-vals->regvals nil vals aignet)
                              aignet)))
    :hints(("Goal" :in-theory (e/d (lit-eval aignet-idp)))))

  ;; (defthm aignet-eval-iter-of-update-greater
  ;;   (implies (<= (nfix n) (nfix m))
  ;;            (equal (aignet-eval-iter
  ;;                    n (update-nth m val vals)
  ;;                    aignet)
  ;;                   (let ((vals (aignet-eval-iter
  ;;                                       n vals aignet)))
  ;;                     (update-nth m val vals))))
  ;;   :hints ((acl2::just-induct-and-expand
  ;;            (aignet-eval-iter n vals aignet)
  ;;            :expand-others
  ;;            ((:free (vals)
  ;;              (aignet-eval-iter n vals aignet))))
  ;;           '(:in-theory (e/d (co-orderedp gate-orderedp)
  ;;                             (nth-in-aignet-eval-iter-preserved
  ;;                              aignet-eval-iter))))))


  (defthm id-eval-of-aignet-vals->invals-of-extension
    (implies (and (syntaxp (not (equal new orig)))
                  (aignet-extension-p new orig))
             (equal (id-eval id
                             (aignet-vals->invals
                              invals vals new)
                             regvals
                             orig)
                    (id-eval id
                             (aignet-vals->invals
                              invals vals orig)
                             regvals
                             orig)))
    :hints (("goal" :induct (id-eval-ind id orig)
             :in-theory (enable lit-eval eval-and-of-lits eval-xor-of-lits)
             :expand ((:free (invals regvals)
                       (id-eval id invals regvals orig))))))

  (defthm id-eval-of-aignet-vals->regvals-of-extension
    (implies (and (syntaxp (not (equal new orig)))
                  (aignet-extension-p new orig))
             (equal (id-eval id
                             invals
                             (aignet-vals->regvals
                              regvals vals new)
                             orig)
                    (id-eval id
                             invals
                             (aignet-vals->regvals
                              regvals vals orig)
                             orig)))
    :hints (("goal" :induct (id-eval-ind id orig)
             :in-theory (enable lit-eval eval-and-of-lits eval-xor-of-lits)
             :expand ((:free (invals regvals)
                       (id-eval id invals regvals orig))))))

  ;; (local (in-theory (disable acl2::take)))

  (defun set-prefix (n first second)
    (declare (xargs :guard (and (true-listp first)
                                (true-listp second)
                                (natp n))))
    (if (zp n)
        second
      (cons (car first)
            (set-prefix (1- n) (cdr first) (cdr second)))))

  (defun nth-set-prefix-ind (m n first second)
    (if (or (zp m) (zp n))
        second
      (cons (car first)
            (nth-set-prefix-ind (1- m) (1- n) (cdr first) (cdr second)))))

  (defthm nth-of-set-prefix
    (equal (nth m (set-prefix n first second))
           (if (< (nfix m) (nfix n))
               (nth m first)
             (nth m second)))
    :hints(("Goal"
            :induct (nth-set-prefix-ind m n first second)
            :expand ((set-prefix n first second))
            :in-theory (enable nth))))

  (local (in-theory (disable set-prefix)))

  (defthm aignet-vals->invals-of-aignet-invals->vals
    (bits-equiv (aignet-vals->invals
                 invals1
                 (aignet-invals->vals
                  invals vals aignet)
                 aignet)
                (set-prefix (num-ins aignet) invals invals1))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm aignet-vals->invals-of-aignet-regvals->vals
    (bits-equiv (aignet-vals->invals
                 invals1
                 (aignet-regvals->vals
                  regvals vals aignet)
                 aignet)
                (aignet-vals->invals invals1 vals aignet))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm aignet-vals->regvals-of-aignet-regvals->vals
    (bits-equiv (aignet-vals->regvals
                 regvals1
                 (aignet-regvals->vals
                  regvals vals aignet)
                 aignet)
                (set-prefix (num-regs aignet) regvals regvals1))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm aignet-vals->regvals-of-aignet-invals->vals
    (bits-equiv (aignet-vals->regvals
                 regvals1
                 (aignet-invals->vals
                  invals vals aignet)
                 aignet)
                (aignet-vals->regvals regvals1 vals aignet))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm id-eval-of-set-prefix-invals
    (equal (id-eval id (set-prefix (stype-count (pi-stype) aignet) invals other)
                    regvals aignet)
           (id-eval id invals regvals aignet))
    :hints(("Goal" :induct (id-eval-ind id aignet)
            :in-theory (enable id-eval lit-eval eval-and-of-lits eval-xor-of-lits))))

  (defthm id-eval-of-set-prefix-regvals
    (equal (id-eval id invals
                    (set-prefix (stype-count (reg-stype) aignet) regvals other)
                    aignet)
           (id-eval id invals regvals aignet))
    :hints(("Goal" :induct (id-eval-ind id aignet)
            :in-theory (enable id-eval lit-eval eval-and-of-lits eval-xor-of-lits))))

  (defthm lit-eval-of-set-prefix-regvals
    (equal (lit-eval lit invals
                     (set-prefix (stype-count (reg-stype) aignet) regvals other)
                     aignet)
           (lit-eval lit invals regvals aignet))
    :hints(("Goal" :expand ((:free (invals regvals)
                             (lit-eval lit invals regvals aignet))))))

  (defthm lit-eval-of-set-prefix-invals
    (equal (lit-eval lit (set-prefix (stype-count (pi-stype) aignet) invals other)
                     regvals aignet)
           (lit-eval lit invals regvals aignet))
    :hints(("Goal" :expand ((:free (invals regvals)
                             (lit-eval lit invals regvals aignet))))))

  (local (defthm true-listp-of-aignet-eval-iter
           (implies (true-listp vals)
                    (true-listp (aignet-eval-iter n vals aignet)))
           :hints(("Goal" :in-theory (e/d (aignet-eval-iter)
                                          (aignet-eval-lit))))))

  (defthm true-listp-of-aignet-eval
    (implies (true-listp vals)
             (true-listp (aignet-eval vals aignet)))))


(define aignet-record-vals ((vals)
                            (invals)
                            (regvals)
                            (aignet))
  :guard (and (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  :returns (new-vals)
  (b* ((vals (mbe :logic (non-exec (bit-list-fix vals)) :exec vals))
       (vals (resize-bits (num-fanins aignet) vals))
       (vals (aignet-invals->vals invals vals aignet))
       (vals (aignet-regvals->vals regvals vals aignet)))
    (aignet-eval vals aignet))
  ///
  (defret len-of-aignet-record-vals
    (equal (len new-vals) (num-fanins aignet)))

  (local (defthm true-listp-when-bit-listp-rw
           (implies (bit-listp x) (true-listp x))))

  (local (defthm bit-listp-of-resize-list
           (implies (and (bitp default)
                         (bit-listp lst))
                    (bit-listp (acl2::resize-list lst n default)))
           :hints(("Goal" :in-theory (enable acl2::resize-list)))))

  (local (defthm bitp-nth-of-bit-list
           (implies (and (bit-listp lst)
                         (< (nfix n) (len lst)))
                    (bitp (nth n lst)))
           :hints(("Goal" :in-theory (enable nth)))))

  (local (in-theory (enable aignet-idp)))

  (local (defthm aignet-eval-records-id-evals-bit-list
           (implies (and (bind-free '((invals . 'nil) (regvals . 'nil))
                                    (invals regvals))
                         (bit-listp vals)
                         (<= (num-fanins aignet) (len vals))
                         (aignet-idp id aignet))
                    (equal (nth id (aignet-eval vals aignet))
                           (id-eval id
                                    (aignet-vals->invals invals vals aignet)
                                    (aignet-vals->regvals regvals vals aignet)
                                    aignet)))
           :hints(("Goal" :use ((:instance aignet-eval-records-id-evals))
                   :in-theory (disable aignet-eval-records-id-evals)))))

  (defthm aignet-record-vals-normalize-input
    (implies (syntaxp (not (equal vals ''nil)))
             (equal (aignet-record-vals vals invals regvals aignet)
                    (aignet-record-vals nil invals regvals aignet)))
    :hints ((acl2::equal-by-nths-hint)))

  (defret nth-of-aignet-record-vals
    (implies (< (nfix n) (num-fanins aignet))
             (equal (nth n new-vals)
                    (id-eval n invals regvals aignet))))

  (defret true-listp-of-<fn>
    (true-listp new-vals)
    :rule-classes :type-prescription)

  (defret len-of-<fn>
    (equal (len new-vals)
           (num-fanins aignet)))

  (defthmd aignet-eval-in-terms-of-aignet-record-vals
    (bits-equiv (aignet-eval vals aignet)
                (append (aignet-record-vals nil
                                            (aignet-vals->invals nil vals aignet)
                                            (aignet-vals->regvals nil vals aignet)
                                            aignet)
                        (nthcdr (num-fanins aignet) vals)))
    :hints(("Goal" :in-theory (e/d (bits-equiv) (nthcdr)))))


  (defthm aignet-vals->invals-of-aignet-record-vals
    (bits-equiv (aignet-vals->invals nil (aignet-record-vals vals invals regvals aignet) aignet)
                (take (num-ins aignet) invals))
    :hints(("Goal" :in-theory (enable bits-equiv))))

  (defthm aignet-vals->regvals-of-aignet-record-vals
    (bits-equiv (aignet-vals->regvals nil (aignet-record-vals vals invals regvals aignet) aignet)
                (take (num-regs aignet) regvals))
    :hints(("Goal" :in-theory (enable bits-equiv))))

  (defcong bits-equiv equal (aignet-record-vals vals invals regvals aignet) 2)
  (defcong bits-equiv equal (aignet-record-vals vals invals regvals aignet) 3)

  (defthm aignet-record-vals-of-take-invals
    (implies (<= (stype-count :pi aignet) (nfix k))
             (equal (aignet-record-vals vals (take k invals) regvals aignet)
                    (aignet-record-vals vals invals regvals aignet))))

  (defthm aignet-record-vals-of-take-regvals
    (implies (<= (stype-count :reg aignet) (nfix k))
             (equal (aignet-record-vals vals invals (take k regvals) aignet)
                    (aignet-record-vals vals invals regvals aignet)))))


(local (defthm bit-list-fix-of-true-list-fix
         (Equal (bit-list-fix (true-list-fix x))
                (bit-list-fix x))
         :hints(("Goal" :in-theory (enable bit-list-fix)))))

(define aignet-val-okp ((n natp) vals aignet)
  :guard (and (<= (num-fanins aignet) (bits-length vals))
              (id-existsp n aignet))
  :guard-hints(("Goal" :in-theory (enable aignet-idp)))
  (b* ((slot0 (id->slot n 0 aignet))
       (type (snode->type slot0)))
    (aignet-case
      type
      :gate (b* ((f0 (snode->fanin slot0))
                 (slot1 (id->slot n 1 aignet))
                 (f1 (snode->fanin slot1))
                 (xor (snode->regp slot1))
                 (v0 (aignet-eval-lit f0 vals))
                 (v1 (aignet-eval-lit f1 vals))
                 (val (if (eql xor 1)
                          (b-xor v0 v1)
                        (b-and v0 v1))))
              (eql (get-bit n vals) val))
      :const (eql (get-bit n vals) 0)
      :in t))
  ///

  (local (defthm bit-list-fix-equal-cons
           (equal (equal (cons x y) (bit-list-fix z))
                  (and (consp z)
                       (equal x (bfix (car z)))
                       (equal y (bit-list-fix (cdr z)))))
           :hints(("Goal" :in-theory (enable bit-list-fix)))))

  (local (in-theory (disable take)))

  (local (defthm nth-when-take-bit-list-equiv
           (implies (and (equal (bit-list-fix (take n x))
                                (bit-list-fix (take n y)))
                         (< (nfix k) (nfix n))
                         (equal ans (nth k y))
                         (syntaxp (not (equal ans `(nth ,k ,x)))))
                    (bit-equiv (nth k x) ans))
           :hints (("goal" :use ((:instance nth-of-bit-list-fix
                                  (n k) (x (take n x)))
                                 (:instance nth-of-bit-list-fix
                                  (n k) (x (take n y))))
                    :in-theory (disable nth-of-bit-list-fix)))))

  (local (in-theory (disable acl2::nth-when-zp
                             acl2::nth-when-too-large-cheap
                             lookup-id-in-bounds-when-positive
                             lookup-id-out-of-bounds)))

  (defthm aignet-val-okp-correct
    (b* ((invals (aignet-vals->invals nil vals aignet))
         (regvals (aignet-vals->regvals nil vals aignet))
         (vals-spec (aignet-record-vals nil invals regvals aignet)))
      (implies (and (equal (bit-list-fix (take n vals-spec))
                           (bit-list-fix (take n vals)))
                    (< (nfix n) (num-fanins aignet)))
               (iff (aignet-val-okp n vals aignet)
                    (bit-equiv (nth n vals-spec)
                               (nth n vals)))))
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (invals regvals) (id-eval n invals regvals aignet)))
                   :in-theory (enable eval-and-of-lits
                                      eval-xor-of-lits
                                      lit-eval))))))

(define aignet-vals-p-aux ((n natp) vals aignet)
  :guard (and (<= (num-fanins aignet) (bits-length vals))
              (<= n (num-fanins aignet)))
  :guard-hints(("Goal" :in-theory (enable aignet-idp)))
  :measure (nfix (- (num-fanins aignet) (nfix n)))
  (b* (((when (mbe :logic (zp (- (num-fanins aignet) (nfix n)))
                   :exec (eql (num-fanins aignet) n)))
        t))
    (and (aignet-val-okp n vals aignet)
         (aignet-vals-p-aux (1+ (lnfix n)) vals aignet)))
  ///
  (local (defthm bit-list-fix-equal-cons
           (equal (equal (cons x y) (bit-list-fix z))
                  (and (consp z)
                       (equal x (bfix (car z)))
                       (equal y (bit-list-fix (cdr z)))))
           :hints(("Goal" :in-theory (enable bit-list-fix)))))

  (local (in-theory (enable aignet-idp)))
  (local (in-theory (disable take)))

  (local (defthm nth-without-early-out
           (equal (nth n x)
                  (if (zp n)
                      (car x)
                    (nth (1- n) (cdr x))))
           :hints(("Goal" :in-theory (enable nth)))
           :rule-classes :definition))

  (local (defthmd take-of-n-plus-1-redef
           (implies (natp n)
                    (equal (take (+ 1 n) x)
                           (append (take n x)
                                   (list (nth n x)))))
           :hints(("Goal" :in-theory (e/d (take)
                                          (nth))))))

  (local (defthm take-of-n-plus-1-special
           (equal (take (+ 1 (nfix n)) x)
                  (append (take n x)
                          (list (nth n x))))
           :hints(("Goal" :in-theory (enable take-of-n-plus-1-redef)))))


  (local (defthm nth-when-take-bit-list-equiv
           (implies (and (< (nfix k) (nfix n))
                         (equal (bit-list-fix (take n x))
                                (bit-list-fix y))
                         (equal ans (nth k y))
                         (syntaxp (not (equal ans `(nth ,k ,x)))))
                    (bit-equiv (nth k x) ans))
           :hints (("goal" :use ((:instance nth-of-bit-list-fix
                                  (n k) (x (take n x)))
                                 (:instance nth-of-bit-list-fix
                                  (n k) (x y)))
                    :in-theory (disable nth-of-bit-list-fix)))))

  (local (in-theory (disable nth-when-take-bit-list-equiv)))

  (local (defthm nth-when-take-bit-list-equiv-special
           (let ((n (+ 1 (fanin-count aignet))))
             (implies (and (equal (bit-list-fix (take n x))
                                  (bit-list-fix y))
                           (< (nfix k) (nfix n))
                           (equal ans (nth k y))
                           (syntaxp (not (equal ans `(nth ,k ,x)))))
                      (bit-equiv (nth k x) ans)))
           :hints (("Goal" :use ((:instance nth-when-take-bit-list-equiv
                                  (n (+ 1 (fanin-count aignet)))))))))

  (local (defthm nthcdr-append-of-len
           (equal (nthcdr (len x) (append x y))
                  y)))

  (local (defthm nthcdr-of-append-same-length
           (implies (equal (len x) (nfix n))
                    (equal (nthcdr n (append x y))
                           y))))


  (local (defthm my-nth-of-append
           (equal (nth n (append x y))
                  (if (< (nfix n) (len x))
                      (nth n x)
                    (nth (- (nfix n) (len x)) y)))))

  (local (defthm take-of-bit-list-fix
           (implies (<= (nfix n) (len x))
                    (equal (take n (bit-list-fix x))
                           (bit-list-fix (take n x))))
           :hints(("Goal" :in-theory (enable take bit-list-fix)))))

  (local (defthmd take-when-take-of-greater
           (implies (and (equal (bit-list-fix (take n x)) (bit-list-fix (take n y)))
                         (<= (nfix m) (nfix n))
                         ;; dumb hyp to stop loop below
                         (equal (nfix m) (len y)))
                    (bit-list-equiv (take m x)
                                    (take m y)))
           :hints (("goal" :use ((:instance take-of-bit-list-fix
                                  (n m) (x (take n x)))
                                 (:instance take-of-bit-list-fix
                                  (n m) (x (take n y))))
                    :in-theory (disable take-of-bit-list-fix)))))

  (local (in-theory (disable acl2::zp-when-integerp
                             nth-without-early-out
                             acl2::nth-of-append
                             bit-list-fix-when-bit-listp)))
  ;; (local (in-theory (disable acl2::nfix-when-natp)))

  (defthm aignet-vals-p-aux-correct
    (b* ((invals (aignet-vals->invals nil vals aignet))
         (regvals (aignet-vals->regvals nil vals aignet))
         (vals-spec (aignet-record-vals nil invals regvals aignet)))
      (implies (equal (bit-list-fix (take n vals-spec))
                      (bit-list-fix (take n vals)))
               (iff (aignet-vals-p-aux n vals aignet)
                    (equal (bit-list-fix (take (num-fanins aignet) vals-spec))
                           (bit-list-fix (take (num-fanins aignet) vals))))))
    :hints (("goal" :induct (aignet-vals-p-aux n vals aignet)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable take-when-take-of-greater))))))


(defrefinement bit-list-equiv bits-equiv
  :hints(("Goal" :in-theory (e/d (bits-equiv) (nth-of-bit-list-fix))
          :use ((:instance nth-of-bit-list-fix
                 (n (acl2::bits-equiv-witness x y)))
                (:instance nth-of-bit-list-fix
                 (n (acl2::bits-equiv-witness x y))
                 (x y))))))

(local (defthmd equal-of-len
         (implies (syntaxp (quotep n))
                  (equal (equal (len x) n)
                         (cond ((equal n 0) (atom x))
                               ((zp n) nil)
                               ((consp x) (equal (len (cdr x)) (1- n)))
                               (t nil))))))

(local (defun bit-list-equiv-when-bits-equiv-of-true-lists-ind (x y)
         (if (atom x)
             y
           (bit-list-equiv-when-bits-equiv-of-true-lists-ind (cdr x) (cdr y)))))

(local (defthm bit-list-equiv-when-bits-equiv-of-true-lists
         (implies (and (bits-equiv x y)
                       (true-listp x)
                       (true-listp y)
                       (equal (len x) (len y)))
                  (equal (equal (bit-list-fix x) (bit-list-fix y)) t))
         :hints (("goal" :induct (bit-list-equiv-when-bits-equiv-of-true-lists-ind x y)
                  :in-theory (enable (:i acl2::fast-list-equiv)
                                     equal-of-len)
                  :expand ((bit-list-fix x)
                           (bit-list-fix y))))))




(define aignet-vals-p (vals aignet)
  :guard-hints (("goal" :in-theory (disable take)
                 :cases ((aignet-vals-p-aux 0 vals aignet))
                 :do-not-induct t))
  (and (<= (num-fanins aignet) (bits-length vals))
       (mbe :logic (non-exec (bits-equiv (aignet-record-vals nil
                                                             (aignet-vals->invals nil vals aignet)
                                                             (aignet-vals->regvals nil vals aignet)
                                                             aignet)
                                         (take (num-fanins aignet) vals)))
            :exec (aignet-vals-p-aux 0 vals aignet)))
  ///
  (local (defthmd nth-take-when-bits-equiv
           (implies (and (bits-equiv (take m x) y)
                         (< (nfix n) (nfix m)))
                    (bit-equiv (nth n x) (nth n y)))
           :hints (("goal" :use ((:instance acl2::nth-of-take
                                  (i n) (n m) (l x)))
                    :in-theory (disable acl2::nth-of-take)
                    :do-not-induct t))))

  (defthmd nth-when-aignet-vals-p
    (implies (and (aignet-vals-p vals aignet)
                  (aignet-idp n aignet))
             (bit-equiv (nth n vals)
                        (id-eval n
                                 (aignet-vals->invals nil vals aignet)
                                 (aignet-vals->regvals nil vals aignet)
                                 aignet)))
    :hints(("Goal" :in-theory (e/d (aignet-idp) (take))
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:in-theory (e/d (nth-take-when-bits-equiv)
                                  (take acl2::nth-of-take))))))

  (local (defcong bits-equiv bits-equiv (take n x) 2
           :hints ((and stable-under-simplificationp
                        `(:expand (,(car (last clause))))))))

  (defthm aignet-vals-p-of-aignet-eval
    (implies (<= (num-fanins aignet) (len vals))
             (aignet-vals-p (aignet-eval vals aignet) aignet))
    :hints(("Goal" :in-theory (e/d (aignet-eval-in-terms-of-aignet-record-vals)
                                   (take)))))

  (defthm aignet-vals-p-of-aignet-record-vals
    (aignet-vals-p (aignet-record-vals vals invals regvals aignet) aignet)))



(defsection copy-bitarr
  (defiteration copy-bitarr-aux (bitarr vals)
    ;; copy from bitarr to vals
    (declare (xargs :stobjs (bitarr vals)
                    :guard (<= (bits-length bitarr) (bits-length vals))))
    (b* ((val (get-bit n bitarr)))
      (set-bit n val vals))
    :index n
    :returns vals
    :last (bits-length bitarr)
    :package aignet::foo)

  (local (defthm copy-bitarr-aux-iter-preserves-len
           (implies (and (<= (len bitarr) (len vals))
                         (<= (nfix n) (len bitarR)))
                    (equal (len (copy-bitarr-aux-iter n bitarr vals))
                           (len vals)))
           :hints (("goal" :induct (copy-bitarr-aux-iter n bitarr vals)
                    :expand ((copy-bitarr-aux-iter n bitarr vals))))))

  (local (defthm copy-bitarr-aux-preserves-len
           (implies (<= (len bitarr) (len vals))
                    (equal (len (copy-bitarr-aux bitarr vals))
                           (len vals)))))

  (local (defthm nth-of-copy-bitarr-aux-iter
           (equal (nth m (copy-bitarr-aux-iter n bitarr vals))
                  (if (< (nfix m) (nfix n))
                      (bfix (nth m bitarr))
                    (nth m vals)))
           :hints (("goal" :induct (copy-bitarr-aux-iter n bitarr vals)
                    :expand ((copy-bitarr-aux-iter n bitarr vals))))))

  (local (defthm nth-of-copy-bitarr-aux
           (equal (nth m (copy-bitarr-aux bitarr vals))
                  (if (< (nfix m) (len bitarr))
                      (bfix (nth m bitarr))
                    (nth m vals)))))

  (local (defthm true-listp-of-copy-bitarr-aux-iter
           (implies (true-listp vals)
                    (true-listp (copy-bitarr-aux-iter n bitarr vals)))
           :hints (("goal" :induct (copy-bitarr-aux-iter n bitarr vals)
                    :expand ((copy-bitarr-aux-iter n bitarr vals))))))

  (local (defthm true-listp-of-copy-bitarr-aux
           (implies (true-listp vals)
                    (true-listp (copy-bitarr-aux bitarr vals)))))

  (in-theory (disable copy-bitarr-aux))

  (define copy-bitarr (bitarr vals)
    (b* ((vals (resize-bits (bits-length bitarr) vals)))
      (copy-bitarr-aux bitarr vals))
    ///
    (defthm copy-bitarr-equals
      (equal (copy-bitarr bitarr vals)
             (bit-list-fix bitarr))
      :hints (("goal" :do-not-induct t)
              (acl2::equal-by-nths-hint)))))



(defsection aignet-sim-frames



  (local (defthm bit-listp-of-update-nth
           (implies (and (bit-listp x)
                         (< (nfix n) (len x))
                         (bitp val))
                    (bit-listp (update-nth n val x)))
           :hints(("Goal" :in-theory (enable update-nth)))))

  (defiteration aignet-frame->vals (k frames vals aignet)
    (declare (xargs :stobjs (vals aignet frames)
                    :guard (and (natp k)
                                (<= (num-fanins aignet) (bits-length vals))
                                (<= (num-ins aignet) (frames-ncols frames))
                                (< k (frames-nrows frames)))))
    (b* ((id (innum->id n aignet))
         (val (frames-get2 k n frames)))
      (set-bit id val vals))
    :returns vals
    :index n
    :last (num-ins aignet))

  (in-theory (disable aignet-frame->vals))
  (local (in-theory (enable aignet-frame->vals)))

  (defthm aignet-frame->vals-iter-preserves-size
    (implies (and (<= (num-fanins aignet) (len vals)))
             (equal (len (aignet-frame->vals-iter n k frames vals aignet))
                    (len vals)))
    :hints ((acl2::just-induct-and-expand
             (aignet-frame->vals-iter n k frames vals aignet))))

  (defthm aignet-frame->vals-preserves-size
    (implies (<= (num-fanins aignet) (len vals))
             (equal (len (aignet-frame->vals k frames vals aignet))
                    (len vals)))
    :hints(("Goal" :in-theory (enable aignet-frame->vals))))

  (defthm aignet-frame->vals-iter-preserves-bit-listp
    (implies (and (bit-listp vals)
                  (<= (num-fanins aignet) (len vals)))
             (bit-listp (aignet-frame->vals-iter n k frames vals aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet-frame->vals-iter n k frames vals aignet))))

  (defthm aignet-frame->vals-preserves-bit-listp
    (implies (and (bit-listp vals)
                  (<= (num-fanins aignet) (len vals)))
             (bit-listp (aignet-frame->vals k frames vals aignet)))
    :hints(("Goal" :in-theory (enable aignet-frame->vals))))


  (fty::deffixequiv aignet-frame->vals-iter :args ((aignet aignet)))
  (fty::deffixequiv aignet-frame->vals$inline :args ((aignet aignet)))

  (defthm nth-of-aignet-frame->vals-iter
    (implies (<= (nfix m) (num-ins aignet))
             (bit-equiv
              (nth n (aignet-frame->vals-iter m k frames vals aignet))
              (if (and (< (nfix n) (num-fanins aignet))
                       (equal (id->type n aignet) (in-type))
                       (equal (id->regp n aignet) 0)
                       (< (ci-id->ionum n aignet) (nfix m)))
                  (nth (ci-id->ionum n aignet)
                       (nth k (stobjs::2darr->rows frames)))
                (nth n vals))))
    :hints((acl2::just-induct-and-expand
            (aignet-frame->vals-iter m k frames vals aignet))
           (and stable-under-simplificationp
                '(:in-theory (enable lookup-stype-in-bounds)))))

  (defthm nth-of-aignet-frame->vals
    (bit-equiv
     (nth n (aignet-frame->vals k frames vals aignet))
     (if (and (< (nfix n) (num-fanins aignet))
              (equal (id->type n aignet) (in-type))
              (equal (id->regp n aignet) 0)
              (< (ci-id->ionum n aignet) (num-ins aignet)))
         (nth (ci-id->ionum n aignet)
              (nth k (stobjs::2darr->rows frames)))
       (nth n vals))))

  (defthm memo-tablep-of-aignet-frame->vals-iter
    (implies (< (fanin-count aignet) (len vals))
             (<
              (fanin-count aignet)
              (len (aignet-frame->vals-iter m k frames vals aignet))))
    :hints((acl2::just-induct-and-expand
            (aignet-frame->vals-iter m k frames vals aignet)))
    :rule-classes :linear)

  (defthm memo-tablep-of-aignet-frame->vals
    (implies (< (fanin-count aignet) (len vals))
             (<
              (fanin-count aignet)
              (len (aignet-frame->vals k frames vals aignet))))
    :rule-classes :linear)


  (define aignet-sim-frame ((k natp)
                            vals
                            frames
                            regvals
                            aignet)
    :guard (and (<= (num-fanins aignet) (bits-length vals))
                (<= (num-ins aignet) (frames-ncols frames))
                (< k (frames-nrows frames))
                (<= (num-regs aignet) (bits-length regvals)))
    (b* ((vals (aignet-frame->vals (lnfix k) frames vals aignet))
         (vals (aignet-regvals->vals regvals vals aignet)))
      (aignet-eval vals aignet))
    ///
    (defthm aignet-sim-frame-preserves-size
      (implies (<= (num-fanins aignet) (len vals))
               (equal (len (aignet-sim-frame k vals frames regvals aignet))
                      (len vals)))))


  (defiteration aignet-vals->nxstvals (regvals vals aignet)
    (declare (xargs :stobjs (vals aignet regvals)
                    :guard (and (<= (num-fanins aignet) (bits-length vals))
                                (<= (num-regs aignet) (bits-length regvals)))))
    (b* ((nextst-lit (regnum->nxst n aignet))
         (val (b-xor (get-bit (lit->var nextst-lit) vals) (lit->neg nextst-lit))))
      (set-bit n val regvals))
    :returns regvals
    :index n
    :last (num-regs aignet))


  (defthm aignet-vals->nxstvals-iter-preserves-size
    (implies (and (<= (num-regs aignet) (len regvals))
                  (<= (nfix n) (num-regs aignet)))
             (equal (len (aignet-vals->nxstvals-iter n regvals vals aignet))
                    (len regvals)))
    :hints (("goal" :induct (aignet-vals->nxstvals-iter n regvals vals aignet)
             :expand ((aignet-vals->nxstvals-iter n regvals vals aignet)))))

  (defthm aignet-vals->nxstvals-preserves-size
    (implies (<= (num-regs aignet) (len regvals))
             (equal (len (aignet-vals->nxstvals regvals vals aignet))
                    (len regvals))))

  (in-theory (disable aignet-vals->nxstvals))
  (local (in-theory (enable aignet-vals->nxstvals)))


  (defthm nth-of-aignet-vals->nxstvals-iter
    (implies (<= (nfix m) (num-regs aignet))
             (bit-equiv
              (nth n (aignet-vals->nxstvals-iter m reg-vals vals aignet))
              (if (< (nfix n) (nfix m))
                  (b* ((nxst (regnum->nxst n aignet)))
                    (b-xor (nth (lit->var nxst)
                                vals)
                           (lit->neg nxst)))
                (nth n reg-vals))))
    :hints ((acl2::just-induct-and-expand (aignet-vals->nxstvals-iter m reg-vals
                                                                     vals
                                                                     aignet))))

  (defthm nth-of-aignet-vals->nxstvals
    (bit-equiv
     (nth n (aignet-vals->nxstvals reg-vals vals aignet))
     (if (< (nfix n) (num-regs aignet))
         (b* ((nxst (regnum->nxst n aignet)))
           (b-xor (nth (lit->var nxst)
                       vals)
                  (lit->neg nxst)))
       (nth n reg-vals))))


  (fty::deffixequiv aignet-vals->nxstvals-iter :args ((aignet aignet)))
  (fty::deffixequiv aignet-vals->nxstvals$inline :args ((aignet aignet)))


  (define aignet-sim-frames-rec ((k natp) vals frames regvals aignet)
    :guard (and (<= (num-fanins aignet) (bits-length vals))
                (<= (num-ins aignet) (frames-ncols frames))
                (<= k (frames-nrows frames))
                (<= (num-regs aignet) (bits-length regvals)))
    :measure (nfix (- (frames-nrows frames) (nfix k)))
    (b* (((when (mbe :logic (zp (- (frames-nrows frames) (nfix k)))
                     :exec (eql (frames-nrows frames) k)))
          (mv regvals vals))
         (vals (aignet-sim-frame k vals frames regvals aignet))
         (regvals (aignet-vals->nxstvals regvals vals aignet)))
      (aignet-sim-frames-rec (1+ (lnfix k)) vals frames regvals aignet))
    ///
    (defthm len-preserved-of-aignet-sim-frames-rec
      (implies (<= (num-fanins aignet) (len vals))
               (equal (len (mv-nth 1 (aignet-sim-frames-rec k vals frames regvals aignet)))
                      (len vals)))))

  (define aignet-sim-frames (vals frames initsts aignet)
    :guard (and (<= (num-regs aignet) (bits-length initsts))
                (<= (num-ins aignet) (frames-ncols frames)))
    :returns (new-vals)
    (b* (((acl2::local-stobjs regvals)
          (mv regvals vals))
         (vals (resize-bits (num-fanins aignet) vals))
         (regvals (copy-bitarr initsts regvals)))
      (aignet-sim-frames-rec 0 vals frames regvals aignet))
    ///
    (defthm len-of-aignet-sim-frames
      (equal (len (aignet-sim-frames vals frames initsts aignet))
             (num-fanins aignet)))))
