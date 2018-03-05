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
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
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
       (resize-bits (num-nodes aignet) vals))
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

<p>The difference between @('aignet-eval') and @('aignet-eval-frame') is that
aignet-eval-frame is designed to be used as part of a sequential simulation.
Therefore, it looks up input nodes in a separate structure
<tt>frames</tt> which gives a value for each input at each frame.  It
assigns values to register output nodes by checking the value stored for its
corresponding register input in the <tt>aignet-vals</tt> structure.  For both
of these node types, @('aignet-eval') assumes that they are already set to the
desired values, and skips them.  The final result is equivalent to the result
of @('aignet-vals') after first copying the RI values to the corresponding ROs
and the inputs from the appropriate frame.</p>

<p>For higher-level functions for simulation, see the book \"aig-sim.lisp\".</p>
"
  (local (in-theory (disable acl2::bfix-when-not-1
                             acl2::nfix-when-not-natp)))


  (defstobj-clone vals bitarr :strsubst (("BIT" . "AIGNET-VAL")))

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
                    :guard (<= (num-nodes aignet) (bits-length vals))))
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
       :out   (b* ((f0 (snode->fanin slot0))
                   (val (aignet-eval-lit f0 vals)))
                (set-bit nid val vals))
       :const (set-bit nid 0 vals)
       :in    vals))
    :index n
    :returns vals
    :last (num-nodes aignet)
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
    (implies (and (<= (num-nodes aignet) (len vals))
                  (<= (nfix n) (num-nodes aignet)))
             (equal (len (aignet-eval-iter n vals aignet))
                    (len vals)))
    :hints ((acl2::just-induct-and-expand
             (aignet-eval-iter n vals aignet))))

  (defthm aignet-eval-preserves-size
    (implies (<= (num-nodes aignet) (len vals))
             (equal (len (aignet-eval vals aignet))
                    (len vals)))
    :hints(("Goal" :in-theory (enable aignet-eval))))

  (defthm aignet-eval-iter-preserves-bit-listp
    (implies (and (bit-listp vals)
                  (<= (nfix n) (num-nodes aignet))
                  (<= (num-nodes aignet) (len vals)))
             (bit-listp (aignet-eval-iter n vals aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet-eval-iter n vals aignet))))

  (defthm aignet-eval-preserves-bit-listp
    (implies (and (bit-listp vals)
                  (<= (num-nodes aignet) (len vals)))
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
                    :guard (and (< (max-fanin aignet) (bits-length vals))
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

  (defiteration aignet-invals->vals (invals vals aignet)
    (declare (xargs :stobjs (vals aignet invals)
                    :guard (and (< (max-fanin aignet) (bits-length vals))
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
    (implies (and (<= (num-nodes aignet) (len vals)))
             (equal (len (aignet-invals->vals-iter n invals vals aignet))
                    (len vals)))
    :hints ((acl2::just-induct-and-expand
             (aignet-invals->vals-iter n invals vals aignet))))

  (defthm aignet-invals->vals-preserves-size
    (implies (<= (num-nodes aignet) (len vals))
             (equal (len (aignet-invals->vals invals vals aignet))
                    (len vals)))
    :hints(("Goal" :in-theory (enable aignet-invals->vals))))

  (defthm aignet-invals->vals-iter-preserves-bit-listp
    (implies (and (bit-listp vals)
                  (<= (num-nodes aignet) (len vals)))
             (bit-listp (aignet-invals->vals-iter n invals vals aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet-invals->vals-iter n invals vals aignet))))

  (defthm aignet-invals->vals-preserves-bit-listp
    (implies (and (bit-listp vals)
                  (<= (num-nodes aignet) (len vals)))
             (bit-listp (aignet-invals->vals invals vals aignet)))
    :hints(("Goal" :in-theory (enable aignet-invals->vals))))


  (defthm nth-of-aignet-invals->vals-iter
    (implies (<= (nfix m) (num-ins aignet))
             (bit-equiv
              (nth n (aignet-invals->vals-iter m invals vals aignet))
              (if (and (< (nfix n) (num-nodes aignet))
                       (equal (id->type n aignet) (in-type))
                       (equal (id->regp n aignet) 0)
                       (< (io-id->ionum n aignet) (nfix m)))
                  (nth (io-id->ionum n aignet) invals)
                (nth n vals))))
    :hints((acl2::just-induct-and-expand
            (aignet-invals->vals-iter m invals vals aignet))
           (and stable-under-simplificationp
                '(:in-theory (enable lookup-stype-in-bounds)))))

  (defthm nth-of-aignet-invals->vals
    (bit-equiv
     (nth n (aignet-invals->vals invals vals aignet))
     (if (and (< (nfix n) (num-nodes aignet))
              (equal (id->type n aignet) (in-type))
              (equal (id->regp n aignet) 0)
              (< (io-id->ionum n aignet) (num-ins aignet)))
         (nth (io-id->ionum n aignet) invals)
       (nth n vals))))

  (defthm memo-tablep-of-aignet-invals->vals-iter
    (implies (< (node-count aignet) (len vals))
             (<
              (node-count aignet)
              (len (aignet-invals->vals-iter m invals vals aignet))))
    :hints((acl2::just-induct-and-expand
            (aignet-invals->vals-iter m invals vals aignet)))
    :rule-classes :linear)

  (defthm memo-tablep-of-aignet-invals->vals
    (implies (< (node-count aignet) (len vals))
             (<
              (node-count aignet)
              (len (aignet-invals->vals invals vals aignet))))
    :rule-classes :linear)
  
  (fty::deffixequiv aignet-invals->vals-iter :args ((aignet aignet)))
  (fty::deffixequiv aignet-invals->vals$inline :args ((aignet aignet)))

  (defiteration aignet-vals->regvals (regvals vals aignet)
    (declare (xargs :stobjs (vals aignet regvals)
                    :guard (and (< (max-fanin aignet) (bits-length vals))
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

  (defiteration aignet-regvals->vals (regvals vals aignet)
    (declare (xargs :stobjs (vals aignet regvals)
                    :guard (and (< (max-fanin aignet) (bits-length vals))
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
    (implies (and (<= (num-nodes aignet) (len vals)))
             (equal (len (aignet-regvals->vals-iter n regvals vals aignet))
                    (len vals)))
    :hints ((acl2::just-induct-and-expand
             (aignet-regvals->vals-iter n regvals vals aignet))))

  (defthm aignet-regvals->vals-preserves-size
    (implies (<= (num-nodes aignet) (len vals))
             (equal (len (aignet-regvals->vals regvals vals aignet))
                    (len vals)))
    :hints(("Goal" :in-theory (enable aignet-regvals->vals))))


  (defthm aignet-regvals->vals-iter-preserves-bit-listp
    (implies (and (bit-listp vals)
                  (<= (num-nodes aignet) (len vals)))
             (bit-listp (aignet-regvals->vals-iter n regvals vals aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet-regvals->vals-iter n regvals vals aignet))))

  (defthm aignet-regvals->vals-preserves-bit-listp
    (implies (and (bit-listp vals)
                  (<= (num-nodes aignet) (len vals)))
             (bit-listp (aignet-regvals->vals regvals vals aignet)))
    :hints(("Goal" :in-theory (enable aignet-regvals->vals))))


  (defthm nth-of-aignet-regvals->vals-iter
    (implies (<= (nfix m) (num-regs aignet))
             (bit-equiv
              (nth n (aignet-regvals->vals-iter m regvals vals aignet))
              (if (and (< (nfix n) (num-nodes aignet))
                       (equal (id->type n aignet) (in-type))
                       (equal (id->regp n aignet) 1)
                       (< (io-id->ionum n aignet) (nfix m)))
                  (nth (io-id->ionum n aignet) regvals)
                (nth n vals))))
    :hints((acl2::just-induct-and-expand
            (aignet-regvals->vals-iter m regvals vals aignet))
           (and stable-under-simplificationp
                '(:in-theory (enable lookup-stype-in-bounds)))))

  (defthm nth-of-aignet-regvals->vals
    (bit-equiv
     (nth n (aignet-regvals->vals regvals vals aignet))
     (if (and (< (nfix n) (num-nodes aignet))
              (equal (id->type n aignet) (in-type))
              (equal (id->regp n aignet) 1)
              (< (io-id->ionum n aignet) (num-regs aignet)))
         (nth (io-id->ionum n aignet) regvals)
       (nth n vals))))

  (defthm memo-tablep-of-aignet-regvals->vals-iter
    (implies (< (node-count aignet) (len vals))
             (<
              (node-count aignet)
              (len (aignet-regvals->vals-iter m regvals vals aignet))))
    :hints((acl2::just-induct-and-expand
            (aignet-regvals->vals-iter m regvals vals aignet)))
    :rule-classes :linear)

  (defthm memo-tablep-of-aignet-regvals->vals
    (implies (< (node-count aignet) (len vals))
             (<
              (node-count aignet)
              (len (aignet-regvals->vals regvals vals aignet))))
    :rule-classes :linear)

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
    (implies (<= (nfix (num-nodes aignet)) (nfix m))
             (equal (nth m (aignet-eval vals aignet))
                    (nth m vals))))

  (defthm aignet-eval-records-id-evals-lemma
    (implies (and (bind-free '((invals . 'nil) (regvals . 'nil))
                             (invals regvals))
                  (< (nfix id) (nfix n))
                  (<= (nfix n) (nfix (num-nodes aignet))))
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
                                 aignet-idp aignet-litp)
              :expand ((aignet-eval-iter
                        (+ 1 (nfix id)) vals aignet))))
    :rule-classes nil)

  (defthm aignet-eval-iter-records-id-evals
    (implies (and (bind-free '((invals . 'nil) (regvals . 'nil))
                             (invals regvals))
                  (< (nfix id) (nfix n))
                  (<= (nfix n) (num-nodes aignet)))
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
    :hints(("Goal" :in-theory (e/d (lit-eval aignet-litp aignet-idp)))))

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

  ;; (local (in-theory (disable acl2::take-redefinition)))

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
                             (lit-eval lit invals regvals aignet)))))))


(define aignet-record-vals ((vals)
                            (invals)
                            (regvals)
                            (aignet))
  :guard (and (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  :returns (new-vals)
  (b* ((vals (mbe :logic (non-exec (bit-list-fix vals)) :exec vals))
       (vals (resize-bits (num-nodes aignet) vals))
       (vals (aignet-invals->vals invals vals aignet))
       (vals (aignet-regvals->vals regvals vals aignet)))
    (aignet-eval vals aignet))
  ///
  (defret len-of-aignet-record-vals
    (equal (len new-vals) (num-nodes aignet)))

  (local (include-book "std/lists/nth" :dir :system))

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
                         (<= (num-nodes aignet) (len vals))
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
    (implies (< (nfix n) (num-nodes aignet))
             (equal (nth n new-vals)
                    (id-eval n invals regvals aignet)))))
  


(defsection aignet-eval-frame


  ;; Similar to aignet-eval, but takes register values from their nextstates.
  (defiteration
    aignet-eval-frame (vals aignet)
    (declare (xargs :stobjs (vals aignet)
                    :guard (<= (num-nodes aignet) (bits-length vals))
                    :guard-hints ('(:in-theory (enable aignet-idp)))))
    (b* ((n (lnfix n))
         (nid n)
         (slot0 (id->slot nid 0 aignet))
         (slot1 (id->slot nid 1 aignet))
         (type (snode->type slot0))
         (regp (snode->regp slot1)))
      (aignet-case
       type regp
       :gate  (b* ((f0 (snode->fanin slot0))
                   (f1 (snode->fanin slot1))
                   (xor (snode->regp slot1))
                   (v0 (aignet-eval-lit f0 vals))
                   (v1 (aignet-eval-lit f1 vals))
                   (val (if (eql xor 1)
                            (b-xor v0 v1)
                          (b-and v0 v1))))
                (set-bit nid val vals))
       :co    (b* ((f0 (snode->fanin slot0))
                   (val (aignet-eval-lit f0 vals)))
                (set-bit nid val vals))
       :const (set-bit nid 0 vals)
       :pi    vals
       :reg   (b* ((nxst (reg-id->nxst nid aignet))
                   (val (get-bit nxst vals)))
                (set-bit nid val vals))))
    :index n
    :returns vals
    :last (num-nodes aignet)
    :package aignet::foo)

  (in-theory (disable aignet-eval-frame))
  (local (in-theory (enable aignet-eval-frame)))

  (defthm aignet-eval-frame-iter-vals-length-preserved
    (<= (len vals)
        (len (aignet-eval-frame-iter n vals aignet)))
    :hints((acl2::just-induct-and-expand
            (aignet-eval-frame-iter n vals aignet)))
    :rule-classes :linear)

  (defthm aignet-eval-frame-vals-length-preserved
    (<= (len vals)
        (len (aignet-eval-frame vals aignet)))
    :rule-classes :linear)

  (fty::deffixequiv aignet-eval-frame-iter :args ((aignet aignet)))
  (fty::deffixequiv acl2::aignet-eval-frame$inline :args ((aignet aignet))))

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

  (local (include-book "std/lists/nth" :dir :system))

  (local (defthm nth-of-bit-list-fix
           (implies (< (nfix n) (len lst))
                    (equal (nth n (bit-list-fix lst))
                           (bfix (nth n lst))))
           :hints(("Goal" :in-theory (enable nth bit-list-fix)))))

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
                                (< (max-fanin aignet) (bits-length vals))
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
    (implies (and (<= (num-nodes aignet) (len vals)))
             (equal (len (aignet-frame->vals-iter n k frames vals aignet))
                    (len vals)))
    :hints ((acl2::just-induct-and-expand
             (aignet-frame->vals-iter n k frames vals aignet))))

  (defthm aignet-frame->vals-preserves-size
    (implies (<= (num-nodes aignet) (len vals))
             (equal (len (aignet-frame->vals k frames vals aignet))
                    (len vals)))
    :hints(("Goal" :in-theory (enable aignet-frame->vals))))

  (defthm aignet-frame->vals-iter-preserves-bit-listp
    (implies (and (bit-listp vals)
                  (<= (num-nodes aignet) (len vals)))
             (bit-listp (aignet-frame->vals-iter n k frames vals aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet-frame->vals-iter n k frames vals aignet))))

  (defthm aignet-frame->vals-preserves-bit-listp
    (implies (and (bit-listp vals)
                  (<= (num-nodes aignet) (len vals)))
             (bit-listp (aignet-frame->vals k frames vals aignet)))
    :hints(("Goal" :in-theory (enable aignet-frame->vals))))


  (fty::deffixequiv aignet-frame->vals-iter :args ((aignet aignet)))
  (fty::deffixequiv aignet-frame->vals$inline :args ((aignet aignet)))

  (defthm nth-of-aignet-frame->vals-iter
    (implies (<= (nfix m) (num-ins aignet))
             (bit-equiv
              (nth n (aignet-frame->vals-iter m k frames vals aignet))
              (if (and (< (nfix n) (num-nodes aignet))
                       (equal (id->type n aignet) (in-type))
                       (equal (id->regp n aignet) 0)
                       (< (io-id->ionum n aignet) (nfix m)))
                  (nth (io-id->ionum n aignet)
                       (nth k (stobjs::2darr->rows frames)))
                (nth n vals))))
    :hints((acl2::just-induct-and-expand
            (aignet-frame->vals-iter m k frames vals aignet))
           (and stable-under-simplificationp
                '(:in-theory (enable lookup-stype-in-bounds)))))

  (defthm nth-of-aignet-frame->vals
    (bit-equiv
     (nth n (aignet-frame->vals k frames vals aignet))
     (if (and (< (nfix n) (num-nodes aignet))
              (equal (id->type n aignet) (in-type))
              (equal (id->regp n aignet) 0)
              (< (io-id->ionum n aignet) (num-ins aignet)))
         (nth (io-id->ionum n aignet)
              (nth k (stobjs::2darr->rows frames)))
       (nth n vals))))

  (defthm memo-tablep-of-aignet-frame->vals-iter
    (implies (< (node-count aignet) (len vals))
             (<
              (node-count aignet)
              (len (aignet-frame->vals-iter m k frames vals aignet))))
    :hints((acl2::just-induct-and-expand
            (aignet-frame->vals-iter m k frames vals aignet)))
    :rule-classes :linear)

  (defthm memo-tablep-of-aignet-frame->vals
    (implies (< (node-count aignet) (len vals))
             (<
              (node-count aignet)
              (len (aignet-frame->vals k frames vals aignet))))
    :rule-classes :linear)


  (define aignet-sim-frame ((k natp)
                            vals
                            frames
                            regvals
                            aignet)
    :guard (and (<= (num-nodes aignet) (bits-length vals))
                (<= (num-ins aignet) (frames-ncols frames))
                (< k (frames-nrows frames))
                (<= (num-regs aignet) (bits-length regvals)))
    (b* ((vals (aignet-frame->vals (lnfix k) frames vals aignet))
         (vals (aignet-regvals->vals regvals vals aignet)))
      (aignet-eval vals aignet))
    ///
    (defthm aignet-sim-frame-preserves-size
      (implies (<= (num-nodes aignet) (len vals))
               (equal (len (aignet-sim-frame k vals frames regvals aignet))
                      (len vals)))))


  (defiteration aignet-vals->nxstvals (regvals vals aignet)
    (declare (xargs :stobjs (vals aignet regvals)
                    :guard (and (<= (num-nodes aignet) (bits-length vals))
                                (<= (num-regs aignet) (bits-length regvals)))))
    (b* ((reg-id (regnum->id n aignet))
         (nextst-id (reg-id->nxst reg-id aignet))
         (val (get-bit nextst-id vals)))
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
                  (nth (reg-id->nxst (regnum->id n aignet) aignet)
                       vals)
                (nth n reg-vals))))
    :hints ((acl2::just-induct-and-expand (aignet-vals->nxstvals-iter m reg-vals
                                                                     vals
                                                                     aignet))))

  (defthm nth-of-aignet-vals->nxstvals
    (bit-equiv
     (nth n (aignet-vals->nxstvals reg-vals vals aignet))
     (if (< (nfix n) (num-regs aignet))
         (nth (reg-id->nxst (regnum->id n aignet) aignet)
              vals)
       (nth n reg-vals))))


  (fty::deffixequiv aignet-vals->nxstvals-iter :args ((aignet aignet)))
  (fty::deffixequiv aignet-vals->nxstvals$inline :args ((aignet aignet)))


  (define aignet-sim-frames-rec ((k natp) vals frames regvals aignet)
    :guard (and (<= (num-nodes aignet) (bits-length vals))
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
      (implies (<= (num-nodes aignet) (len vals))
               (equal (len (mv-nth 1 (aignet-sim-frames-rec k vals frames regvals aignet)))
                      (len vals)))))

  (define aignet-sim-frames (vals frames initsts aignet)
    :guard (and (<= (num-regs aignet) (bits-length initsts))
                (<= (num-ins aignet) (frames-ncols frames)))
    :returns (new-vals)
    (b* (((acl2::local-stobjs regvals)
          (mv regvals vals))
         (vals (resize-bits (num-nodes aignet) vals))
         (regvals (copy-bitarr initsts regvals)))
      (aignet-sim-frames-rec 0 vals frames regvals aignet))
    ///
    (defthm len-of-aignet-sim-frames
      (equal (len (aignet-sim-frames vals frames initsts aignet))
             (num-nodes aignet)))))
         


