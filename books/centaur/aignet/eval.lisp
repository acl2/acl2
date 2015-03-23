
(in-package "AIGNET")

(include-book "semantics")

(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))
(local (in-theory (disable set::double-containment)))
(local (in-theory (disable nth update-nth
                           acl2::nfix-when-not-natp
                           resize-list
                           acl2::resize-list-when-empty
                           acl2::make-list-ac-redef
                           set::double-containment
                           set::sets-are-true-lists
                           make-list-ac)))

(local (in-theory (disable true-listp-update-nth
                           acl2::nth-with-large-index)))



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

<p>See @(see aignet-seq-eval) for discussion of sequential evaluation.</p>


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

  (local (in-theory (disable acl2::nth-with-large-index)))

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
                   (f1 (gate-id->fanin1 nid aignet))
                   (v0 (aignet-eval-lit f0 vals))
                   (v1 (aignet-eval-lit f1 vals))
                   (val (b-and v0 v1)))
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


  (defiteration aignet-vals->invals (aignet-invals vals aignet)
    (declare (xargs :stobjs (vals aignet aignet-invals)
                    :guard (and (<= (num-nodes aignet) (bits-length vals))
                                (<= (num-ins aignet) (bits-length aignet-invals)))))
    (b* ((id (innum->id n aignet))
         (val (get-bit id vals)))
      (set-bit n val aignet-invals))
    :returns aignet-invals
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

  (defiteration aignet-invals->vals (aignet-invals vals aignet)
    (declare (xargs :stobjs (vals aignet aignet-invals)
                    :guard (and (<= (num-nodes aignet) (bits-length vals))
                                (<= (num-ins aignet) (bits-length aignet-invals)))))
    (b* ((id (innum->id n aignet))
         (val (get-bit n aignet-invals)))
      (set-bit id val vals))
    :returns vals
    :index n
    :last (num-ins aignet))

  (in-theory (disable aignet-invals->vals))
  (local (in-theory (enable aignet-invals->vals)))


  (defthm nth-of-aignet-invals->vals-iter
    (implies (<= (nfix m) (num-ins aignet))
             (bit-equiv
              (nth n (aignet-invals->vals-iter m aignet-invals vals aignet))
              (if (and (< (nfix n) (num-nodes aignet))
                       (equal (id->type n aignet) (in-type))
                       (equal (io-id->regp n aignet) 0)
                       (< (io-id->ionum n aignet) (nfix m)))
                  (nth (io-id->ionum n aignet) aignet-invals)
                (nth n vals))))
    :hints((acl2::just-induct-and-expand
            (aignet-invals->vals-iter m aignet-invals vals aignet))
           (and stable-under-simplificationp
                '(:in-theory (enable lookup-stype-in-bounds)))))

  (defthm nth-of-aignet-invals->vals
    (bit-equiv
     (nth n (aignet-invals->vals aignet-invals vals aignet))
     (if (and (< (nfix n) (num-nodes aignet))
              (equal (id->type n aignet) (in-type))
              (equal (io-id->regp n aignet) 0)
              (< (io-id->ionum n aignet) (num-ins aignet)))
         (nth (io-id->ionum n aignet) aignet-invals)
       (nth n vals))))
  
  (defthm memo-tablep-of-aignet-invals->vals-iter
    (implies (< (node-count aignet) (len vals))
             (<
              (node-count aignet)
              (len (aignet-invals->vals-iter m aignet-invals vals aignet))))
    :hints((acl2::just-induct-and-expand
            (aignet-invals->vals-iter m aignet-invals vals aignet)))
    :rule-classes :linear)

  (defthm memo-tablep-of-aignet-invals->vals
    (implies (< (node-count aignet) (len vals))
             (<
              (node-count aignet)
              (len (aignet-invals->vals aignet-invals vals aignet))))
    :rule-classes :linear)


  (defiteration aignet-vals->regvals (aignet-regvals vals aignet)
    (declare (xargs :stobjs (vals aignet aignet-regvals)
                    :guard (and (<= (num-nodes aignet) (bits-length vals))
                                (<= (num-regs aignet) (bits-length aignet-regvals)))))
    (b* ((id (regnum->id n aignet))
         (val (get-bit id vals)))
      (set-bit n val aignet-regvals))
    :returns aignet-regvals
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

  (defiteration aignet-regvals->vals (aignet-regvals vals aignet)
    (declare (xargs :stobjs (vals aignet aignet-regvals)
                    :guard (and (<= (num-nodes aignet) (bits-length vals))
                                (<= (num-regs aignet) (bits-length aignet-regvals)))))
    (b* ((id (regnum->id n aignet))
         (val (get-bit n aignet-regvals)))
      (set-bit id val vals))
    :returns vals
    :index n
    :last (num-regs aignet))

  (in-theory (disable aignet-regvals->vals))
  (local (in-theory (enable aignet-regvals->vals)))


  (defthm nth-of-aignet-regvals->vals-iter
    (implies (<= (nfix m) (num-regs aignet))
             (bit-equiv
              (nth n (aignet-regvals->vals-iter m aignet-regvals vals aignet))
              (if (and (< (nfix n) (num-nodes aignet))
                       (equal (id->type n aignet) (in-type))
                       (equal (io-id->regp n aignet) 1)
                       (< (io-id->ionum n aignet) (nfix m)))
                  (nth (io-id->ionum n aignet) aignet-regvals)
                (nth n vals))))
    :hints((acl2::just-induct-and-expand
            (aignet-regvals->vals-iter m aignet-regvals vals aignet))
           (and stable-under-simplificationp
                '(:in-theory (enable lookup-stype-in-bounds)))))

  (defthm nth-of-aignet-regvals->vals
    (bit-equiv
     (nth n (aignet-regvals->vals aignet-regvals vals aignet))
     (if (and (< (nfix n) (num-nodes aignet))
              (equal (id->type n aignet) (in-type))
              (equal (io-id->regp n aignet) 1)
              (< (io-id->ionum n aignet) (num-regs aignet)))
         (nth (io-id->ionum n aignet) aignet-regvals)
       (nth n vals))))

  (defthm memo-tablep-of-aignet-regvals->vals-iter
    (implies (< (node-count aignet) (len vals))
             (<
              (node-count aignet)
              (len (aignet-regvals->vals-iter m aignet-regvals vals aignet))))
    :hints((acl2::just-induct-and-expand
            (aignet-regvals->vals-iter m aignet-regvals vals aignet)))
    :rule-classes :linear)

  (defthm memo-tablep-of-aignet-regvals->vals
    (implies (< (node-count aignet) (len vals))
             (<
              (node-count aignet)
              (len (aignet-regvals->vals aignet-regvals vals aignet))))
    :rule-classes :linear)

  (defcong bits-equiv equal
    (aignet-vals->invals-iter n invals vals aignet) 3
    :hints(("Goal" :in-theory (enable aignet-vals->invals-iter))))
  (defcong bits-equiv equal (aignet-vals->invals invals vals aignet) 2)

  (defcong bits-equiv equal
    (aignet-vals->regvals-iter n regvals vals aignet) 3
    :hints(("Goal" :in-theory (enable aignet-vals->regvals-iter))))
  (defcong bits-equiv equal (aignet-vals->regvals regvals vals aignet) 2)


  

  (defthm id-eval-of-in/regvals-of-aignet-vals-of-in/regvals-iters
    (let* ((vals (aignet-invals->vals-iter
                         (stype-count (pi-stype) aignet)
                         aignet-invals vals aignet))
           (vals (aignet-regvals->vals-iter
                         (stype-count (reg-stype) aignet)
                         aignet-regvals vals aignet))
           (invals (aignet-vals->invals-iter
                    (stype-count (pi-stype) aignet)
                    invals vals aignet))
           (regvals (aignet-vals->regvals-iter
                     (stype-count (reg-stype) aignet)
                     regvals vals aignet)))
      (bit-equiv (id-eval id invals regvals aignet)
                 (id-eval id aignet-invals aignet-regvals aignet)))
    :hints (("Goal" :induct
             (id-eval-ind id aignet))
            '(:in-theory (e/d* (lit-eval
                                eval-and-of-lits)
                               (id-eval))
              :do-not-induct t
              :expand
              ((:free (aignet-regvals aignet-invals)
                (id-eval 0 aignet-invals aignet-regvals aignet))
               (:free (aignet-regvals aignet-invals)
                (id-eval id aignet-invals aignet-regvals aignet))))))

  (defthm id-eval-of-in/regvals-of-aignet-vals-of-in/regvals
    (let* ((vals (aignet-invals->vals
                         aignet-invals vals aignet))
           (vals (aignet-regvals->vals
                         aignet-regvals vals aignet))
           (invals (aignet-vals->invals
                    invals vals aignet))
           (regvals (aignet-vals->regvals
                     regvals vals aignet)))
      (bit-equiv (id-eval id invals regvals aignet)
                 (id-eval id aignet-invals aignet-regvals aignet))))

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
            '(:in-theory (enable* lit-eval eval-and-of-lits
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
             :in-theory (enable lit-eval eval-and-of-lits)
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
             :in-theory (enable lit-eval eval-and-of-lits)
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
                              aignet-invals vals new)
                             regvals
                             orig)
                    (id-eval id
                             (aignet-vals->invals
                              aignet-invals vals orig)
                             regvals
                             orig)))
    :hints (("goal" :induct (id-eval-ind id orig)
             :in-theory (enable lit-eval eval-and-of-lits)
             :expand ((:free (invals regvals)
                       (id-eval id invals regvals orig))))))

  (defthm id-eval-of-aignet-vals->regvals-of-extension
    (implies (and (syntaxp (not (equal new orig)))
                  (aignet-extension-p new orig))
             (equal (id-eval id
                             invals
                             (aignet-vals->regvals
                              aignet-regvals vals new)
                             orig)
                    (id-eval id
                             invals
                             (aignet-vals->regvals
                              aignet-regvals vals orig)
                             orig)))
    :hints (("goal" :induct (id-eval-ind id orig)
             :in-theory (enable lit-eval eval-and-of-lits)
             :expand ((:free (invals regvals)
                       (id-eval id invals regvals orig))))))

  (local (in-theory (disable acl2::take-redefinition)))
  
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
                  aignet-invals vals aignet)
                 aignet)
                (set-prefix (num-ins aignet) aignet-invals invals1))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm aignet-vals->invals-of-aignet-regvals->vals
    (bits-equiv (aignet-vals->invals
                 invals1
                 (aignet-regvals->vals
                  aignet-regvals vals aignet)
                 aignet)
                (aignet-vals->invals invals1 vals aignet))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm aignet-vals->regvals-of-aignet-regvals->vals
    (bits-equiv (aignet-vals->regvals
                 regvals1
                 (aignet-regvals->vals
                  aignet-regvals vals aignet)
                 aignet)
                (set-prefix (num-regs aignet) aignet-regvals regvals1))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm aignet-vals->regvals-of-aignet-invals->vals
    (bits-equiv (aignet-vals->regvals
                 regvals1
                 (aignet-invals->vals
                  aignet-invals vals aignet)
                 aignet)
                (aignet-vals->regvals regvals1 vals aignet))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm id-eval-of-set-prefix-invals
    (equal (id-eval id (set-prefix (stype-count (pi-stype) aignet) invals other)
                    regvals aignet)
           (id-eval id invals regvals aignet))
    :hints(("Goal" :induct (id-eval-ind id aignet)
            :in-theory (enable id-eval lit-eval eval-and-of-lits))))

  (defthm id-eval-of-set-prefix-regvals
    (equal (id-eval id invals
                    (set-prefix (stype-count (reg-stype) aignet) regvals other)
                    aignet)
           (id-eval id invals regvals aignet))
    :hints(("Goal" :induct (id-eval-ind id aignet)
            :in-theory (enable id-eval lit-eval eval-and-of-lits))))

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
         (type (snode->type slot0)))
      (aignet-seq-case
       type
       (io-id->regp nid aignet)
       :gate  (b* ((f0 (snode->fanin slot0))
                   (f1 (gate-id->fanin1 nid aignet))
                   (v0 (aignet-eval-lit f0 vals))
                   (v1 (aignet-eval-lit f1 vals))
                   (val (b-and v0 v1)))
                (set-bit nid val vals))
       :co    (b* ((f0 (snode->fanin slot0))
                   (val (aignet-eval-lit f0 vals)))
                (set-bit nid val vals))
       :const (set-bit nid 0 vals)
       :pi    vals
       :reg   (b* ((nxst (reg-id->nxst nid aignet))
                   ((when (int= nxst 0))
                    vals)
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
    :rule-classes :linear))
