;; svcnf.lisp
;;
;; Book defining some of the core algorithmic functions used in translating
;; definitions to aignet, doing forward lifted aignet evaluation steps, and
;; translation of aignet circuits (defined by outputs) into cnf.

(in-package "EXSIM")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; BOZOs
;; 1. ???
;;
;; TODOs
;; 1. ??? 
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "std/io/read-file-lines-no-newlines" :dir :system)
(include-book "std/strings/strtok" :dir :system)
(include-book "centaur/satlink/top" :dir :system)
(include-book "centaur/aignet/top" :dir :system)
(include-book "centaur/aignet/transforms" :dir :system)
(include-book "aignet-ipasir-off")
(include-book "centaur/sv/svex/top" :dir :system)
(include-book "support")
(include-book "nxtypes")
(include-book "extypes")
(include-book "exbase")

(defmacro num-nodes (a) `(aignet::num-fanins ,a))

(defsection sv-to-aignet-and-aignet-to-cnf-support
  :parents (exsim)
  :short "Support functions for SV to AIGNET and maintaining AIGNET/CNF connection"
  :autodoc nil
  :long "
<p> This book defines three primary functions supporting the exsim structures 
and main loop. The following functions are the main exports of the book: </p>

<h3> Building an aignet and variable mapping from SVEX-based next-tbl: </h3>

<p> The function @({ (mod-tbl->aignet mod-tbl) }) with implicit binding of
aignet and state returns @({ (mv aig-ndx-tbl aignet state) }) where the aignet
is updated with a network corresponding to the variables and next-state
expressions in the provided next-tbl and the returned aig-ndx-tbl provides a
mapping for the variables in the next-tbl to AIG indexes. The aignet that is
produced will have the same number of inputs and outputs and every variable
will be defined as the same index range in the input and output arrays in the
aignet. </p>

<h3> Lifted forward evaluation to propogate constants through AIGNET: </h3>

<p> The function @({ (forward-reduce in-vals out-vals) }) with implicit binding
of aignet performs a lifted evaluation of a single step of the output or
next-state function defined by the aignet using the partial binding of the
inputs defined by in-vals. The out-vals will be extended with any new output
bindings that have become either constant 1 or 0 in the evaluation. </p>

<h3> Computing aignet from SVEX-based next-tbl: </h3>

<p> The function @({ (backward-expand outs in-vals base) }) with implicit
binding of aignet and ipasir will first perform a copy/reduce of the aignet
network driving the list of outputs in outs with inputs bound by the partial
input evaluation in-vals. The function then either computes the CNF for
resulting network and returns it or adds the clauses to the incremental ipasir
object. In addition to the CNF and ipasir, the function returns a mapping for
the literals in the generated CNF which map to AIG variables on the input and
output side </p>
")

(defmacro btm-lit    ()  2)
(defmacro btm-litp   (x) `(eql ,x (btm-lit)))
(defmacro btm-or-bit (x) `(<= ,x 2))
;; NOTE -- important to start sat literals at 2!:
;; 0,1 is used for true/false, 2/3 is used for btm/top
;; (although I don't use top at the moment..
(defmacro init-sat-base () 2)

(defmacro acons! (&rest x) `(acl2::acons! ,@x))

;;
;; 1. supporting initialization:
;;    (init-aignet exs$)
;;    -- calls mod-tbl->aignet to initialize aignet, refcounts, and aig-var-map
;;    -- allocates other objects/stobjs (xvals array for eval)
;;
;; 2. supporting step-free:
;;    (eval-lift-aignet exs$)
;;     -- calls aignet-eval-lift using the lvals and stores values in lvals
;;    (fill-lvals vars clk exs$)
;;    (pull-lvals vars clk exs$)
;;    -- these functions setup the lvals stobj for eval and then pull the
;;       values that come out (along with checking if anything "changed").
;;
;; 3. supporting step-fail
;;

(define get-base-size ((var sv::svar-p) (tbl aig-var-tbl-p))
  :returns (mv (base natp) (size natp))
  (b* ((look (hons-get var tbl))
       ((when (not look))
        (prog2$ (raise "Could not find var:~x0~%" var) (mv 0 0)))
       ((aig-var-elem el) (cdr look)))
    (mv el.base el.size)))

(define a4vec->aiglist* (up lo (siz natp))
  :returns (rslt true-listp)
  (cond ((zp siz) ())
        ((or (atom lo) (atom up))
         ;; NOTE -- we would like to throw an exception if the up and lo
         ;;         do not match expected size, but sometimes, as an optimization
         ;;         apparently, the generation of the a4vec from svex can lead to
         ;;         this.. It is acceptable (since we are anding upper and lower bits)
         ;;         to just return nil here.. (we are only supporting 2-valued
         ;;         at the moment).
         ;; (raise "a4vec insufficient in length!"))
         (cons nil 
               (a4vec->aiglist* up lo (1- siz))))
        (t
         (cons (aig-and (car up) (car lo))
               (a4vec->aiglist* (cdr up) (cdr lo) (1- siz))))))

;(define a4vec->aiglist* (up lo)
;  :returns (rslt true-listp)
;  (cond ((and (consp lo) (consp up))
;         (cons (aig-and (car up) (car lo))
;               (a4vec->aiglist* (cdr up) (cdr lo))))
;        ((and (atom lo) (atom up)) ())
;        (t
;         (raise "a4vec was expected to have matching upper and lower lengths:~x0~%"
;                (list (consp lo) (consp up))))))

(define a4vec->aiglist ((a4v sv::a4vec-p) (siz natp))
  :returns (rslt true-listp)
  (b* ((up (sv::a4vec->upper a4v))
       (lo (sv::a4vec->lower a4v)))
    (a4vec->aiglist* up lo siz)))

(define a4vecs->aiglists ((a4vs sv::a4veclist-p)
                          (tbl aig-var-tbl-p))
  :returns (rslt true-listp)
  (cond ((and (endp a4vs) (endp tbl)) ())
        ((or (endp a4vs) (endp tbl))
         (raise "illegal inconsistent input lengths!"))
        (t
         (b* (((aig-var-elem el) (cdar tbl)))
           (append (a4vec->aiglist (first a4vs) el.size)
                   (a4vecs->aiglists (rest a4vs) (rest tbl)))))))
          
(define create-a4vec-size-base ((size natp) (index natp) (base natp))
  :returns (rslt true-listp)
  (if (zp size) ()
    (cons (+ base index)
          (create-a4vec-size-base (1- size) (1+ index) base))))

(define make-a4env-svex ((tbl aig-var-tbl-p)
                         &key ((rslt sv::svex-a4vec-env-p) ':make-a4env-svex))
  :returns (rslt sv::svex-a4vec-env-p :hyp :guard)
  (if (atom tbl) rslt
    (make-a4env-svex (rest tbl)
                     :rslt
                     (b* ((var (caar tbl))
                          ((aig-var-elem el) (cdar tbl))
                          (vec (create-a4vec-size-base el.size 0 el.base)))
                       (hons-acons var (sv::a4vec vec vec) rslt)))))

(define make-in-vars-map (aig-vars
                          &key ((ndx natp) '0) (rslt ':make-in-vars-map))
  (if (atom aig-vars) rslt
    (make-in-vars-map (rest aig-vars) :ndx (1+ ndx)
                      :rslt (hons-acons (first aig-vars) ndx rslt))))

(define get-sat-lits ((aignet-lits lit-listp) sat-lits)
  :returns (rslt lit-listp :hyp :guard)
  (if (atom aignet-lits) ()
    (b* ((lit (first aignet-lits))
         (id  (lit-id lit))
         (neg (lit-neg lit)))
      (cons (nfix (logxor neg (aignet-id->sat-lit id sat-lits)))
            (get-sat-lits (rest aignet-lits) sat-lits)))))

(define bnfix (x (n natp)) (if (and (natp x) (< x n)) x 0))

(defconst *undef-in-var-lit* (mk-lit 0 1))

;; BOZO -- I am not sure any of the following compute-*-map functions are used anywhere any more and should be removed!

(define make-input-lits ((size natp) (ndx natp) in-v-map aignet)
  :guard (> (num-ins aignet) 0)
  :guard-hints (("Goal" :in-theory (enable bnfix)))
  :returns (rslt lit-listp :hyp :guard)
  (if (zp size) ()
    (cons (b* ((look (hons-get ndx in-v-map)))
            (if look
                (mk-lit (innum->id (bnfix (cdr look) (num-ins aignet))
                                   aignet)
                        0)
              *undef-in-var-lit*))
          (make-input-lits (1- size) (1+ ndx) in-v-map aignet))))

(define make-output-lits ((size natp) (ndx natp) aignet)
  :guard (> (num-outs aignet) 0)
  :guard-hints (("Goal" :in-theory (enable bnfix)))
  :returns (rslt lit-listp :hyp :guard)
  (if (zp size) ()
    ;; BOZO -- (mk-lit?)
    (cons (outnum->fanin (bnfix ndx (num-outs aignet))
                         aignet)
          (make-output-lits (1- size) (1+ ndx) aignet))))

(define compute-in-map ((tbl aig-var-tbl-p) in-v-map
                        &key
                        (aignet 'aignet) ((rslt lits-alist-p) 'nil))
  :guard (> (num-ins aignet) 0)
  :returns (rslt lits-alist-p)
  (if (atom tbl) (lits-alist-fix rslt)
    (b* ((var (caar tbl))
         ((aig-var-elem el) (cdar tbl)))
      (compute-in-map (rest tbl) in-v-map
                      :rslt
                      (hons-acons var 
                                  (make-input-lits el.size el.base in-v-map aignet)
                                  rslt)))))

(defthm natp-junk1
  (implies (and (natp x) (natp y))
           (natp (+ x y)))
  :hints (("Goal" :in-theory (enable natp))))

(define compute-out-map ((vars sv::svarlist-p) (tbl aig-var-tbl-p)
                         &key
                         ((ndx natp) '0) (aignet 'aignet) ((rslt lits-alist-p) 'nil))
  :guard (> (num-outs aignet) 0)
  :returns (rslt lits-alist-p)
  (if (atom vars) (lits-alist-fix rslt)
    (b* ((var (first vars))
         ((mv - size) (get-base-size var tbl)))
      (compute-out-map (rest vars) tbl :ndx (+ ndx size)
                       :rslt
                       (hons-acons var
                                   (make-output-lits size ndx aignet)
                                   rslt)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; New approach based on aignet's processing in the main exloop..
;; so, we need to translate the generated mod-tbl into an aignet..
;; and then process that..
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; some simple properties of rev$!

(defthm rev!-aig-var-listp
  (implies (and (acl2::aig-var-listp x) (acl2::aig-var-listp y))
           (acl2::aig-var-listp (acl2::rev$! x y)))
  :hints (("Goal" :in-theory (enable acl2::rev$! acl2::aig-var-listp))))

(defthm rev!-svex-list
  (implies (and (sv::svexlist-p x) (sv::svexlist-p y))
           (sv::svexlist-p (acl2::rev$! x y)))
  :hints (("Goal" :in-theory (enable acl2::rev$!))))

(defthm rev!-ndx-list
  (implies (and (ndx-list-p x) (ndx-list-p y))
           (ndx-list-p (acl2::rev$! x y)))
  :hints (("Goal" :in-theory (enable acl2::rev$!))))

(defthm rev!-aig-var-tbl
  (implies (and (aig-var-tbl-p x) (aig-var-tbl-p y))
           (aig-var-tbl-p (acl2::rev$! x y)))
  :hints (("Goal" :in-theory (enable acl2::rev$!))))

(defthm rev!-ndx->var-map
  (implies (and (ndx->var-map-p x) (ndx->var-map-p y))
           (ndx->var-map-p (acl2::rev$! x y)))
  :hints (("Goal" :in-theory (enable acl2::rev$!))))

(defthm rev!-var->ndx-map
  (implies (and (var->ndx-map-p x) (var->ndx-map-p y))
           (var->ndx-map-p (acl2::rev$! x y)))
  :hints (("Goal" :in-theory (enable acl2::rev$!))))

;;;;

(defthm aig-var-tbl-fast-alist-fork
  (implies (and (aig-var-tbl-p x) (aig-var-tbl-p y))
           (aig-var-tbl-p (fast-alist-fork x y))))

(defthm aig-var-tbl-last
  (implies (aig-var-tbl-p x)
           (aig-var-tbl-p (last x))))

(define mod-tbl->svex-list ((nxts exs-mod-tbl-p)
                            &key ((rslt sv::svexlist-p) 'nil))
  :returns (rslt sv::svexlist-p)
  (if (atom nxts) (sv::svexlist-fix (acl2::rev! rslt))
    (b* ((var (caar nxts))
         ((exs-mod-el el) (cdar nxts)))
      (mod-tbl->svex-list (rest nxts)
                          :rslt (cons (if (eq el.port :input)
                                          (sv::svex-var var)
                                        el.next)
                                      rslt)))))

(define mod-tbl->aig-var-tbl ((nxts exs-mod-tbl-p) 
                              &key ((base natp) '1) ((rslt aig-var-tbl-p) 'nil))
  :returns (rslt aig-var-tbl-p)
  (if (atom nxts)
      (aig-var-tbl-fix (fast-alist-clean (make-fast-alist rslt)))
    (b* ((var (caar nxts))
         ((exs-mod-el el) (cdar nxts)))
      (mod-tbl->aig-var-tbl (rest nxts)
                            :base (+ base el.size)
                            :rslt (acons! var 
                                          (make-aig-var-elem 
                                           :base base :size el.size)
                                          rslt)))))

(define elem->aig-vars ((size natp) (base natp) (rslt acl2::aig-var-listp))
  :returns (rslt acl2::aig-var-listp :hyp :guard)
  (if (zp size) rslt (elem->aig-vars (1- size) (1+ base) (cons base rslt))))

(define non-bool-atom-list-fix ((x acl2::aig-var-listp))
  :returns (rslt acl2::aig-var-listp)
  (mbe :logic (if (acl2::aig-var-listp x) x ())
       :exec x))

(define tbl->aig-vars ((tbl aig-var-tbl-p) &key ((rslt acl2::aig-var-listp) 'nil))
  :returns (rslt acl2::aig-var-listp)
  (if (atom tbl) (non-bool-atom-list-fix (acl2::rev! rslt))
    (tbl->aig-vars (rest tbl) :rslt (b* (((aig-var-elem el) (cdar tbl)))
                                      (elem->aig-vars el.size el.base rslt)))))

;; (define aignet-add-outs ((lits lit-listp) aignet)
;;   :guard (aignet-lit-listp lits aignet)
;;   (if (endp lits) aignet
;;     (b* ((aignet (aignet-add-out (first lits) aignet)))
;;       (aignet-add-outs (rest lits) aignet))))

(define my-rewrite-config ()
  '(:REWRITE-CONFIG (AIGNET::CUTS4-CONFIG . 10)
                    (AIGNET::CUT-TRIES-LIMIT . 5)
                    (AIGNET::ZERO-COST-REPLACE)
                    (AIGNET::EVALUATION-METHOD . :NOBUILD)
                    (AIGNET::GATESIMP . 41)))

(define my-balance-config ()
  `(:BALANCE-CONFIG (AIGNET::SEARCH-HIGHER-LEVELS . t)
                    (AIGNET::SEARCH-SECOND-LIT . t)
                    (AIGNET::SEARCH-LIMIT . 1000)
                    (AIGNET::SUPERGATE-LIMIT . 1000)
                    (AIGNET::VERBOSITY-LEVEL . 0) ;; we change this one..
                    (AIGNET::GATESIMP . 41)))

(define mk-ndxs ((ndx natp) (size natp) &key ((rslt ndx-list-p) 'nil))
  :returns (rslt ndx-list-p)
  (if (zp size) (ndx-list-fix (acl2::rev! rslt))
    (mk-ndxs (1+ ndx) (1- size) :rslt (cons ndx rslt))))

(define aig-var-tbl->var-ndx-map ((tbl aig-var-tbl-p)
                                  &key
                                  ((ndx natp) '0)
                                  ((rslt var->ndx-map-p) 'nil))
  :returns (rslt var->ndx-map-p)
  (if (endp tbl)
      (var->ndx-map-fix (make-fast-alist rslt))
    (b* (((aig-var-elem el) (cdar tbl)))
      (aig-var-tbl->var-ndx-map (rest tbl)
                                :ndx (+ ndx el.size)
                                :rslt (acons! (caar tbl)
                                                    (mk-ndxs ndx el.size)
                                                    rslt)))))

(define add-ndx-vars ((ndxs ndx-list-p)
                      (var sv::svar-p)
                      (rslt ndx->var-map-p)
                      &key ((offset natp) '0))
  :returns (rslt ndx->var-map-p)
  (if (endp ndxs) (ndx->var-map-fix rslt)
    (add-ndx-vars (rest ndxs) var
                  (acons! (first ndxs)
                                (make-ndx->var-elem :var var
                                                    :off offset)
                                rslt)
                  :offset (1+ offset))))

(define aig-var-tbl->ndx-var-map ((map var->ndx-map-p)
                                  &key ((rslt ndx->var-map-p) 'nil))
  :returns (rslt ndx->var-map-p)
  (if (endp map)
      (ndx->var-map-fix (make-fast-alist rslt))
    (aig-var-tbl->ndx-var-map (rest map)
                              :rslt (add-ndx-vars (cdar map)
                                                  (caar map)
                                                  rslt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mod-tbl->aignet ((mod-tbl exs-mod-tbl-p)
                         &key
                         ;;
                         ;; NOTE -- in our default comb-transforms, we do NOT do the following:
                         ;;
                         ;;   1) observability-fix  -- this is intended to reduce the AIG nodes
                         ;;      under the assumption that only certain conditions reach the outputs
                         ;;      this could be useful, but in practice is also expensive and does not
                         ;;      buy as much for us in this context where we have lots of outputs and
                         ;;      a decent amount of visibility in theory.. there are combinational
                         ;;      subterms that could still be reduced.. but the cost at getting at
                         ;;      them vs. the benefits has not shown to be sufficient in tests we have
                         ;;      done so far.
                         ;;
                         ;;   2) abc-comb-simplify -- at the moment, we don't want to assume that the user
                         ;;      has ABC installed, and ABC is a bit bigger of a "trust tag" than the
                         ;;      the already existing trust-tags on which we rely. Further, it's not
                         ;;      clear if there is any significant further reduction offered by ABC comb.
                         ;;      simplify over the exisiting rewriting and fraiging transformations.
                         ;;
                         ((comb-transforms comb-transformlist-p)
                          '(list (my-balance-config)
                                 (my-rewrite-config)
                                 (aignet::make-fraig-config)))
                         ((gatesimp gatesimp-p) 
                          '(default-gatesimp))
                         (aignet 'aignet)
                         (state 'state))
  :returns (mv (vmap var->ndx-map-p) (nmap ndx->var-map-p) aignet state)
  (b* (((local-stobjs strash) (mv vmap nmap aignet state strash))
       (exprs    (mod-tbl->svex-list mod-tbl))
       (tbl      (mod-tbl->aig-var-tbl mod-tbl))
       (a4env    (cwtime (make-a4env-svex tbl) :mintime 0))
       (masks    (cwtime (sv::svexlist-mask-alist exprs) :mintime 0))
       (a4vecs   (cwtime (sv::svexlist->a4vec-top exprs a4env masks) :mintime 0))
       (-        (fast-alist-free a4env))
       (aiglist  (cwtime (a4vecs->aiglists a4vecs tbl) :mintime 0))
       (aig-vars (tbl->aig-vars tbl))
       (varmap   (consecutive-vars-to-varmap 1 aig-vars nil))
       (strash   (strashtab-init 100 nil nil strash))
       (aignet   (aignet-clear aignet))
       (aignet   (aignet-add-ins (len aig-vars) aignet))
       ((mv out-lits strash aignet)
        (cwtime (aiglist-to-aignet-top aiglist varmap gatesimp strash aignet) :mintime 0))
       (aignet   (aignet-add-outs out-lits aignet))
       (-        (fast-alist-free varmap))
       ((mv aignet state)
        (cwtime (apply-comb-transforms! aignet comb-transforms state) :mintime 0))
       (vmap     (aig-var-tbl->var-ndx-map tbl))
       (nmap     (aig-var-tbl->ndx-var-map vmap))
       (-        (fast-alist-free tbl)))
    (mv vmap nmap aignet state strash)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definline aignet-eval-lift-lit (lit lvals)
  (declare (type (integer 0 *) lit)
           (xargs :stobjs lvals
                  :guard (and (litp lit)
                              (< (lit-id lit) (lits-length lvals)))))
  (b* ((val (get-lit (lit-id lit) lvals)))
    (if (>= val (btm-lit)) (btm-lit) (b-xor (lit-neg lit) val))))

(defiteration aignet-eval-lift (lvals aignet)
  (declare (xargs :stobjs (lvals aignet)
                  :guard (<= (num-nodes aignet) (lits-length lvals))
                  :guard-hints (("Goal" :in-theory (enable aignet-idp)))))
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
                 (v0 (aignet-eval-lift-lit f0 lvals))
                 (v1 (aignet-eval-lift-lit f1 lvals))
                 (val (cond ((eql xor 1)
                             (if (or (btm-litp v0) (btm-litp v1))
                                 (btm-lit)
                               (b-xor v0 v1)))
                            ((btm-litp v0)
                             (if (eql v1 0) 0 (btm-lit)))
                            ((btm-litp v1)
                             (if (eql v0 0) 0 (btm-lit)))
                            (t (b-and v0 v1)))))
              (set-lit nid val lvals))
     :out   (b* ((f0 (snode->fanin slot0))
                 (val (aignet-eval-lift-lit f0 lvals)))
              (set-lit nid val lvals))
     :const (set-lit nid 0 lvals)
     :in    lvals))
  :index n
  :returns lvals
  :last (num-nodes aignet)
  :package exsim::foo)

;(define ndx->out-id ((ndx ndx-p) aignet)
;  :inline t
;  :guard (< ndx (num-outs aignet))
;  :returns (id (< id (num-nodes aignet))
;               :rule-classes :linear)
;  (outnum->id ndx aignet))

(define ndx->in-id ((ndx ndx-p) aignet)
  :inline t
  :guard (< ndx (num-ins aignet))
  :returns (id (< id (num-nodes aignet))
               :rule-classes :linear)
  (innum->id ndx aignet))

(defthm bitp-implies-litp
  (implies (bitp x) (litp x))
  :hints (("Goal" :in-theory (enable bitp litp))))

(define install-in-vals (in-lvals
                         (in-add ndx-map-p) ;; fast-alist
                         &key
                         ((ndx natp) '0)
                         (lvals 'lvals)
                         (aignet 'aignet))
  :guard (and (<= (num-nodes aignet) (lits-length lvals))
              (<= ndx (num-ins aignet))
              (<= (num-ins aignet) (lits-length in-lvals)))
  :measure (nfix (- (num-ins aignet) ndx))
  (if (mbe :logic (zp (- (num-ins aignet) ndx))
           :exec  (eql ndx (num-ins aignet)))
      lvals
    (b* ((look (hons-get ndx in-add))
         (val (if look (cdr look) (get-lit ndx in-lvals)))
         (id (ndx->in-id ndx aignet))
         (lvals (set-lit id val lvals)))
      (install-in-vals in-lvals in-add :ndx (1+ ndx)))))

(define install-in-chgs ((in-chgs ndx-map-p) ;; alist
                         &key
                         (lvals 'lvals)
                         (aignet 'aignet))
  :guard (<= (num-nodes aignet) (lits-length lvals))
  (if (endp in-chgs) lvals
    (b* ((ndx (caar in-chgs))
         (val (cdar in-chgs))
         ((when (not (< ndx (num-ins aignet))))
          (prog2$ (raise "internal error: illegal ndx encountered:~x0~%" ndx)
                  lvals))
         (id (ndx->in-id ndx aignet))
         (lvals (set-lit id val lvals)))
      (install-in-chgs (rest in-chgs)))))

(define extract-out-vals (out-lvals
                          (out-add ndx-map-p) ;; fast-alist
                          &key
                          ((rslt ndx-map-p) 'nil)
                          ((ndx natp) '0)
                          (lvals 'lvals)
                          (aignet 'aignet))
  :guard (and (<= (num-nodes aignet) (lits-length lvals))
              (<= ndx (num-outs aignet))
              (<= (num-outs aignet) (lits-length out-lvals)))
  :measure (nfix (- (num-outs aignet) ndx))
  :returns (rslt ndx-map-p)
  (if (mbe :logic (zp (- (num-outs aignet) ndx))
           :exec  (eql ndx (num-outs aignet)))
      (ndx-map-fix rslt)
    (b* (;;(id   (ndx->out-id ndx aignet))
         ;;(val  (get-lit id lvals))
         (lit  (outnum->fanin ndx aignet))
         (val  (aignet-eval-lift-lit lit lvals))
         (look (hons-get ndx out-add))
         (curr (if look (cdr look) (get-lit ndx out-lvals)))
         ((when (if (bitp curr) (eql curr val) (not (bitp val))))
          (extract-out-vals out-lvals out-add :ndx (1+ ndx) :rslt rslt)))
      (extract-out-vals out-lvals out-add :ndx (1+ ndx)
                        :rslt (acons! ndx val rslt)))))

(defthm aignet-evals-lift-len-vals
  (implies (and (<= (num-nodes aignet) (lits-length lvals))
                (<= n (num-nodes aignet)))
           (equal (len (aignet-eval-lift-iter n lvals aignet))
                  (len lvals)))
  :hints (("Goal" :in-theory (enable aignet-eval-lift-iter))))

(defthm install-in-vals-len-vals
  (implies (<= (num-nodes aignet) (lits-length lvals))
           (equal (len (install-in-vals in-lvals in-add :ndx ndx))
                  (len lvals)))
  :hints (("Goal" :in-theory (enable install-in-vals))))

(defthm install-in-chgs-len-vals
  (implies (<= (num-nodes aignet) (lits-length lvals))
           (equal (len (install-in-chgs in-chgs))
                  (len lvals)))
  :hints (("Goal" :in-theory (enable install-in-chgs))))

(define lvals->ndx-map* (lvals (ndx natp)
                         &key
                         ((rslt ndx-map-p) 'nil))
  :guard (<= ndx (lits-length lvals))
  :returns (rslt ndx-map-p)
  (if (zp ndx) (ndx-map-fix rslt)
    (b* ((ndx (1- ndx))
         (val (get-lit ndx lvals))
         (rslt (if (btm-litp val) rslt (acons! ndx val rslt))))
      (lvals->ndx-map* lvals ndx :rslt rslt))))

(defmacro lvals->ndx-map (lv)
  `(lvals->ndx-map* ,lv (lits-length ,lv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define forward-reduce (in-lvals
                        out-lvals
                        (in-add ndx-map-p)
                        (out-add ndx-map-p)
                        (in-chgs ndx-map-p)
                        &key (aignet 'aignet))
  :returns (rslt ndx-map-p)
  (b* (((local-stobjs lvals) (mv new-vals lvals))
       ;; (- (cw "in-lvals->map:~x0~%" (lvals->ndx-map in-lvals)))
       ;; (- (cw "out-lvals->map:~x0~%" (lvals->ndx-map out-lvals)))
       ((when (or (> (num-outs aignet) (lits-length out-lvals))
                  (> (num-ins aignet)  (lits-length in-lvals))))
        (mv (raise "internal error: poor bounds for lvals arrays!") lvals))
       (lvals (resize-lits (num-nodes aignet) lvals))
       (lvals (install-in-vals in-lvals in-add))
       (lvals (install-in-chgs in-chgs))
       (lvals (aignet-eval-lift lvals aignet))
       (rslt  (extract-out-vals out-lvals out-add)))
    (mv rslt lvals)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define compute-refcounts (aignet aignet-refcounts)
  (b* ((aignet-refcounts (resize-u32 (num-nodes aignet) aignet-refcounts)))
    (cwtime (aignet-count-refs aignet-refcounts aignet) :mintime 0)))

(define out-ndx-list-p (x aignet)
  (or (atom x)
      (and (natp (car x))
           (< (car x) (num-outs aignet))
           (out-ndx-list-p (cdr x) aignet))))

(define aignet-copy-dfs-ndxs ((outs ndx-list-p) aignet mark lvals strash aignet2
                              &key ((gatesimp gatesimp-p) '(default-gatesimp)))
  :guard (and (out-ndx-list-p outs aignet)
              (<= (num-nodes aignet) (bits-length mark))
              (<= (num-nodes aignet) (lits-length lvals))
              (aignet-copies-in-bounds lvals aignet2))
  :guard-hints (("Goal" :in-theory (enable out-ndx-list-p)))
  (if (endp outs) (mv aignet2 mark lvals strash)
    (b* (((mv mark lvals strash aignet2)
          (aignet-copy-dfs-rec ;; (outnum->id (first outs) aignet)
                               (lit->var (outnum->fanin (first outs) aignet))
                               aignet mark lvals strash gatesimp aignet2)))
      (aignet-copy-dfs-ndxs (rest outs) aignet mark lvals strash aignet2))))

(define aignet-copy-out-ndxs ((outs ndx-list-p) aignet lvals aignet2)
  :guard (and (out-ndx-list-p outs aignet)
              (<= (num-nodes aignet) (lits-length lvals))
              (aignet-copies-in-bounds lvals aignet2))
  :guard-hints (("Goal" :in-theory (enable out-ndx-list-p)))
  (if (endp outs) aignet2
    (b* ((out-ndx (first outs))
;;         (lit (get-lit (outnum->id out-ndx aignet) lvals))
         (out-lit (outnum->fanin out-ndx aignet))
         (new-lit (get-lit (lit->var out-lit) lvals))
         (lit (mk-lit (lit->var new-lit) 
                      (logxor (lit->neg out-lit) (lit->neg new-lit))))
         (aignet2 (aignet-add-out lit aignet2)))
      (aignet-copy-out-ndxs (rest outs) aignet lvals aignet2))))

(define include-in-vals (in-lvals
                         &key
                         ((ndx natp) '0)
                         (lvals 'lvals)
                         (aignet 'aignet))
  :guard (and (<= (num-nodes aignet) (lits-length lvals))
              (<= (num-ins aignet) (lits-length in-lvals))
              (<= ndx (num-ins aignet)))
  :measure (nfix (- (num-ins aignet) ndx))
  (if (mbe :logic (zp (- (num-ins aignet) ndx))
           :exec  (eql ndx (num-ins aignet)))
      lvals
    (b* ((val (get-lit ndx in-lvals))
         ((when (not (bitp val)))
          (include-in-vals in-lvals :ndx (1+ ndx)))
         (id (ndx->in-id ndx aignet))
         (lvals (set-lit id val lvals)))
      (include-in-vals in-lvals :ndx (1+ ndx)))))


(define aignet-idsp (lst anet)
  :guard (and (nat-listp lst) (node-listp anet))
  (or (atom lst)
      (and (aignet-idp (first lst) anet)
           (aignet-idsp (rest lst) anet))))

(defthm bitp-implies-aignet-litp
  (implies (bitp x) (aignet-idp (lit->var x) aignet))
  :hints (("Goal" :in-theory (enable bitp aignet-idp))))

(defthm aignet-copies-in-bounds-include-in-vals
  (implies (and (equal (num-ins aignet) (num-ins aignet2))
                (aignet-copies-in-bounds lvals aignet2))
           (aignet-copies-in-bounds (include-in-vals in-lvals :ndx ndx) aignet2))
  :hints (("Goal" :in-theory (enable ndx-map-p include-in-vals aignet-copies-in-bounds))))

(defthm aignet-copy-dfs-setup-num-ins
  (equal (num-ins (mv-nth 2 (aignet-copy-dfs-setup aignet mark lvals aignet2)))
         (num-ins aignet))
  :hints (("Goal" :in-theory (enable aignet-copy-dfs-setup num-ins))))

(defthm aignet-copies-in-bounds-aignet-copy-dfs-ndxs
  (implies (aignet-copies-in-bounds lvals aignet2)
           (aignet-copies-in-bounds
            (mv-nth 2 (aignet-copy-dfs-ndxs outs aignet mark lvals strash
                                            aignet2 :gatesimp gatesimp))
            (mv-nth 0 (aignet-copy-dfs-ndxs outs aignet mark lvals strash
                                            aignet2 :gatesimp gatesimp))))
  :hints (("Goal" :in-theory (enable aignet-copy-dfs-ndxs))))

(defthm len-include-in-vals-redx
  (implies (<= (num-nodes aignet) (len lvals))
           (equal (len (include-in-vals in-lvals :ndx ndx)) (len lvals)))
  :hints (("Goal" :in-theory (enable include-in-vals)
           :induct (include-in-vals in-lvals :ndx ndx))))

(defthm len-lvals-aignet-copy-dfs-ndxs-redx
  (implies (<= (num-nodes aignet) (len lvals))
           (equal (len (mv-nth 2 (aignet-copy-dfs-ndxs outs aignet mark lvals strash
                                                       aignet2 :gatesimp gatesimp)))
                  (len lvals)))
  :hints (("Goal" :in-theory (enable aignet-copy-dfs-ndxs))))

;;;;;

(define aignet-out-ndxs-copy-dfs ((outs ndx-list-p) in-lvals aignet aignet2)
  :guard (out-ndx-list-p outs aignet)
  (b* (((local-stobjs mark lvals strash)
        (mv aignet2 mark lvals strash))
       ((when (not (<= (num-ins aignet) (lits-length in-lvals))))
        (prog2$ (raise "internal error: insufficient space in in-lvals")
                (mv aignet2 mark lvals strash)))
       ((mv mark lvals aignet2)
        (aignet-copy-dfs-setup aignet mark lvals aignet2))
       (lvals (include-in-vals in-lvals))
       (strash (strashtab-init 1000 nil nil strash))
       ((mv aignet2 mark lvals strash)
        (aignet-copy-dfs-ndxs outs aignet mark lvals strash aignet2))
       (aignet2 (aignet-copy-out-ndxs outs aignet lvals aignet2)))
    (mv aignet2 mark lvals strash)))

;;;;;

(define offset-lit ((lit litp) (base natp))
  :returns (rslt litp)
  (mk-lit (+ (lit-id lit) base) (lit-neg lit)))

(define offset-clause ((cls lit-listp) (base natp)
                       &key ((rslt lit-listp) 'nil))
  :returns (rslt lit-listp)
  (if (endp cls) (lit-list-fix rslt)
    (offset-clause (rest cls) base
                   :rslt (cons (offset-lit (first cls) base) rslt))))

(define offset-clauses ((cnf lit-list-listp) (base natp)
                        &key ((rslt lit-list-listp) 'nil))
  :returns (rslt lit-list-listp)
  (if (endp cnf) (lit-list-list-fix rslt)
    (offset-clauses (rest cnf) base
                    :rslt (cons (offset-clause (first cnf) base) rslt))))

(define aignet-out-lits (aignet &key ((ndx natp) '0) ((rslt lit-listp) 'nil))
  :guard (<= ndx (num-outs aignet))
  :returns (rslt lit-listp)
  :measure (nfix (- (num-outs aignet) ndx))
  (if (mbe :logic (zp (- (num-outs aignet) ndx))
           :exec  (eql ndx (num-outs aignet)))
      (lit-list-fix rslt)
    (aignet-out-lits aignet :ndx (1+ ndx)
                     ;; :rslt (cons (co-id->fanin (outnum->id ndx aignet) aignet) rslt))))
                     :rslt (cons (outnum->fanin ndx aignet) rslt))))

(define aignet-outs->ipasir-cnf (aignet use-ipasir (base natp) sat-lits ipasir)
  :guard (and (or (not use-ipasir) (solver-rdy ipasir))
              (sat-lits-wfp sat-lits aignet))
  :guard-hints (("Goal" :in-theory (enable solver-rdy)))
  :returns (mv (cnf lit-list-listp)
               (ipasir solver-rdy 
                       :hyp (solver-rdy ipasir)
                       :hints (("Goal" :in-theory (enable solver-rdy))))
               sat-lits)
  (b* (((local-stobjs aignet-refcounts)
        (mv cnf ipasir sat-lits aignet-refcounts))
       (aignet-refcounts (compute-refcounts aignet aignet-refcounts))
       (out-lits (aignet-out-lits aignet))
       ((when (not (and (< (lits-max-id-val out-lits)
                           (u32-length aignet-refcounts))
                        (aignet-lit-listp out-lits aignet))))
        ;; BOZO -- need to remove this once I prove this cannot happen..
        (mv (raise "Illegal internal condition encountered.. sad :( ~x0~%"
                   (list out-lits (u32-length aignet-refcounts)))
            ipasir sat-lits aignet-refcounts))
       ((mv cnf ipasir sat-lits)
        (if use-ipasir
            (b* (((mv sat-lits ipasir)
                  (aignet::aignet-lit-list->ipasir+off out-lits base t aignet-refcounts
                                                       sat-lits aignet ipasir)))
              (mv () ipasir sat-lits))
          ;(b* (((mv sat-lits cnf)
          ;        (aignet-lit-list->cnf out-lits t aignet-refcounts
           ;                             sat-lits aignet ()))
          ;       (ipasir (ipasir-cancel-new-clause ipasir))
          ;       (ipasir (ipasir-input ipasir))
          ;       (cnf (offset-clauses cnf base))
           ;      (ipasir (ipasir-add-clauses ipasir cnf)))
           ;   (mv () ipasir sat-lits)) 
          (b* (((mv sat-lits cnf)
                (aignet-lit-list->cnf out-lits t aignet-refcounts
                                      sat-lits aignet ())))
            (mv (offset-clauses cnf base) ipasir sat-lits)))))
    (mv cnf ipasir sat-lits aignet-refcounts)))

(define aignet-get-sat-lit ((lit litp) (base natp) sat-lits)
  :returns (rlst litp)
  (b* ((id (lit-id lit)) (neg (lit-neg lit)))
    (if (aignet-id-has-sat-var id sat-lits)
        (lnfix (logxor neg (+ (aignet-id->sat-lit id sat-lits)
                              (satlink::make-lit base 0))))
      0)))

(define aignet-sat-in-map ((base natp) sat-lits aignet
                           &key
                           ((ndx natp) '0) ((rslt ndx-map-p) 'nil))
  :measure (nfix (- (num-ins aignet) ndx))
  :guard (<= ndx (num-ins aignet))
  :returns (rslt ndx-map-p)
  (cond ((mbe :logic (zp (- (num-ins aignet) ndx))
              :exec  (eql ndx (num-ins aignet)))
         (ndx-map-fix rslt))
        (t (b* ((a-lit (mk-lit (innum->id ndx aignet) 0))
                (s-lit (aignet-get-sat-lit a-lit base sat-lits)))
             (aignet-sat-in-map base sat-lits aignet
                                :ndx (1+ ndx)
                                :rslt (if (eql s-lit 0) rslt
                                        (acons! ndx s-lit rslt)))))))

(define aignet-sat-out-map ((outs ndx-list-p) (base natp) sat-lits aignet
                            &key
                            ((ndx natp) '0) ((rslt ndx-map-p) 'nil))
  :measure (nfix (- (num-outs aignet) ndx))
  :guard (<= ndx (num-outs aignet))
  :returns (rslt ndx-map-p)
  (cond ((endp outs) (ndx-map-fix rslt))
        ((mbe :logic (zp (- (num-outs aignet) ndx))
              :exec  (eql ndx (num-outs aignet)))
         (raise "aignet should have number of outputs matching ndx-list!"))
        (t (b* ((out   (first outs))
               ;; (a-lit (co-id->fanin (outnum->id ndx aignet) aignet))
                (a-lit (outnum->fanin ndx aignet))
                (s-lit (aignet-get-sat-lit a-lit base sat-lits))
                ((when (eql s-lit 0))
                 (raise "should not have 0 lit for an output!")))
             (aignet-sat-out-map (rest outs) base sat-lits aignet
                                 :ndx (1+ ndx)
                                 :rslt (acons! out s-lit rslt))))))

;; BOZO -- eventually, would like to move "base" into sat-lits computation,
;; and remove this parameter and adjustments from it (it would come from
;; aignet-id->sat-lit directly.
(define aignet-sat-lits->var-maps ((outs ndx-list-p) (base natp) sat-lits aignet)
  :returns (mv (next-base natp)
               (in-lmap  ndx-map-p)
               (out-lmap ndx-map-p))
  ;; BOZO -- don't need 1+ here. sat-next-var$ should be sufficient, but I am
  ;; leaving some gaps.. for some reason which I don't remember..
  (b* ((next-base (lnfix (+ (1+ (sat-next-var$ sat-lits)) base)))
       (in-lmap   (aignet-sat-in-map base sat-lits aignet))
       (out-lmap  (aignet-sat-out-map outs base sat-lits aignet)))
    (mv next-base in-lmap out-lmap)))

;;;;;;;;;
;; now we build AIGs to use as extracted mappings for GL proofs primarily..
;;;;;;;;;

(def-1d-arr aigarr :slotname aig :default-val nil)

(defiteration aignet->aig-loop (aigarr aignet)
  (declare (xargs :stobjs (aigarr aignet)
                  :guard (<= (num-nodes aignet) (aigs-length aigarr))
                  :guard-hints (("Goal" :in-theory (enable aignet-idp)))))
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
                 (v0 (get-aig (lit-id f0) aigarr))
                 (v0 (if (eql (lit-neg f0) 1) (aig-not v0) v0))
                 (v1 (get-aig (lit-id f1) aigarr))
                 (v1 (if (eql (lit-neg f1) 1) (aig-not v1) v1))
                 (aig (cond ((eql xor 1) (aig-xor v0 v1))
                            (t           (aig-and v0 v1)))))
              (set-aig nid aig aigarr))
     :out   (b* ((f0 (snode->fanin slot0))
                 (v0 (get-aig (lit-id f0) aigarr))
                 (v0 (if (eql (lit-neg f0) 1) (aig-not v0) v0)))
              (set-aig nid v0 aigarr))
     :const (set-aig nid nil aigarr)
     :in    aigarr)) ;; already set this up..
  :index n
  :returns aigarr
  :last (num-nodes aignet)
  :package exsim::foo)

(define install-in-aigs ((aig-base natp) in-lvals (in-aigs ndx->aig-p)
                         &key ((ndx natp) '0) ((rslt ndx->aig-p) 'nil)
                         (aigarr 'aigarr) (aignet 'aignet))
  :guard (and (<= (num-nodes aignet) (aigs-length aigarr))
              (<= (num-ins aignet) (lits-length in-lvals))
              (<= ndx (num-ins aignet)))
  :measure (nfix (- (num-ins aignet) ndx))
  :returns (mv (in-aigs ndx->aig-p) (next-base natp) aigarr)
  (if (mbe :logic (zp (- (num-ins aignet) ndx))
           :exec (eql ndx (num-ins aignet)))
      (mv (ndx->aig-fix rslt) (lnfix aig-base) aigarr)
    (b* ((val (get-lit ndx in-lvals))
         (look (hons-get ndx in-aigs))
         (id (ndx->in-id ndx aignet))
         (in-aig (cond ((eql val 0) nil)
                       ((eql val 1) t)
                       (look (cdr look))
                       (t aig-base)))
         (new (not (or (bitp val) look)))
         (aigarr (set-aig id in-aig aigarr))
         (rslt (if look rslt (acons! ndx in-aig rslt)))
         (next-base (if new (1+ aig-base) aig-base)))
      (install-in-aigs next-base in-lvals in-aigs :ndx (1+ ndx) :rslt rslt))))

(define extract-out-aigs ((outs ndx-list-p)
                          &key
                          ((ndx natp) '0) ((rslt ndx->aig-p) 'nil)
                          (aigarr 'aigarr) (aignet 'aignet))
  :guard (and (<= (num-nodes aignet) (aigs-length aigarr))
              (<= ndx (num-outs aignet)))
  :measure (nfix (- (num-outs aignet) ndx))
  :returns (rslt ndx->aig-p)
  (cond ((mbe :logic (zp (- (num-outs aignet) ndx))
              :exec (eql ndx (num-outs aignet)))
         (if (endp outs)
             (ndx->aig-fix rslt)
           (raise "internal error: outs too long")))
        ((endp outs)
         (raise "internal error: not enough outs"))
        (t
         (b* (;; (id (ndx->out-id ndx aignet))
              (lit (outnum->fanin ndx aignet))
              (aig (get-aig (lit->var lit) aigarr))
              (aig (if (eql (lit-neg lit) 1) (aig-not aig) aig))
              (rslt (acons! (first outs) aig rslt)))
           (extract-out-aigs (rest outs) :ndx (1+ ndx) :rslt rslt)))))

(defthm aignet->aig-loop-lift-len
  (implies (and (<= (num-nodes aignet) (aigs-length aigarr))
                (<= n (num-nodes aignet)))
           (equal (len (aignet->aig-loop-iter n aigarr aignet))
                  (len aigarr)))
  :hints (("Goal" :in-theory (enable aignet->aig-loop-iter))))

(defthm install-in-aigs-len-aigarr
  (implies (<= (num-nodes aignet) (aigs-length aigarr))
           (equal (len (mv-nth 2 (install-in-aigs aig-base in-lvals in-aigs :ndx ndx :rslt rslt)))
                  (len aigarr)))
  :hints (("Goal" :in-theory (enable install-in-aigs))))

(define aignet-outs->aig-list ((aig-base natp) (outs ndx-list-p)
                               (curr-in-aigs ndx->aig-p) in-lvals aignet)
  :returns (mv (in-aigs ndx->aig-p)
               (out-aigs ndx->aig-p)
               (next-base natp))
  (b* (((local-stobjs aigarr)
        (mv in-aigs out-aigs next-base aigarr))
       ((when (not (<= (num-ins aignet) (lits-length in-lvals))))
        (mv (raise "illegal internal condition") () 0 aigarr))
       (aigarr (resize-aigs (num-nodes aignet) aigarr))
       ((mv in-aigs next-base aigarr)
        (install-in-aigs aig-base in-lvals curr-in-aigs))
       (aigarr (aignet->aig-loop aigarr aignet))
       (out-aigs (extract-out-aigs outs)))
    (mv in-aigs out-aigs next-base aigarr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define backward-expand ((outs ndx-list-p) in-lvals
                         (curr-in-aigs ndx->aig-p)
                         &key
                         ((base natp) '0) ((aig-base natp) '0)
                         (use-ipasir 'nil) (compute-aigs 'nil) 
                         (aignet 'aignet) (ipasir 'ipasir))
  :guard (or (not use-ipasir) (solver-rdy ipasir))
  :returns (mv (cnf        lit-list-listp)
               (in-lmap    ndx-map-p)
               (out-lmap   ndx-map-p)
               (in-aigs    ndx->aig-p)
               (out-aigs   ndx->aig-p)
               (next-base  natp)
               (next-aig-b natp)
               (ipasir     solver-rdy :hyp (solver-rdy ipasir)))
  (b* (((local-stobjs sat-lits aignet2)
        (mv cnf in-lmap out-lmap in-aigs out-aigs
            next-base next-aig-base ipasir sat-lits aignet2))
       ;; 0. Check a few properties on the inputs.. these should likely be
       ;;    moved into the guard, but I don't think it could ever arise and
       ;;    offers no real to check them here -- and would add more to the
       ;;    invariants required in the exloop/exsim definitions.
       ((when (not (out-ndx-list-p outs aignet)))
        (mv (raise "out ndxs supplied are out-of-bounds:~x0~%" outs) 
            () () () () 0 0 ipasir sat-lits aignet2))
       ;; 1.  Preallocate-empty the sat-lits stobj..
       (sat-lits 
        (sat-lits-empty (num-nodes aignet) sat-lits))
       ;; 2. Copy over the simplified cones for the outputs using values in lvals
       (aignet2
        (aignet-out-ndxs-copy-dfs outs in-lvals aignet aignet2))
       ;; 3. Optionally create AIG maps for logic in aignet
       ((mv in-aigs out-aigs next-aig-base)
        (if compute-aigs
            (aignet-outs->aig-list (lnfix aig-base) outs 
                                   curr-in-aigs in-lvals aignet2)
          (mv nil nil (lnfix aig-base))))
       ;; 4. Create cnf clauses for the simplified cones
       ((mv cnf ipasir sat-lits)
        (aignet-outs->ipasir-cnf aignet2 use-ipasir base sat-lits ipasir))
       ;; 5. Compute next-base, in-map, out-map which includes updates
       ((mv next-base in-lmap out-lmap)
        (aignet-sat-lits->var-maps outs base sat-lits aignet2)))
    (mv cnf in-lmap out-lmap in-aigs out-aigs next-base next-aig-base
        ipasir sat-lits aignet2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; these are wrappers at the exs$ stobj level for the main support routines in svcnf.lisp..

(define exs-mk-var->port ((mod-tbl exs-mod-tbl-p)
                          &key ((rslt var->port-map-p) 'nil))
  :returns (rslt var->port-map-p)
  (if (endp mod-tbl) (var->port-map-fix (make-fast-alist rslt))
    (exs-mk-var->port (rest mod-tbl)
                      :rslt
                      (acons! (caar mod-tbl)
                              (exs-mod-el->port (cdar mod-tbl))
                              rslt))))

(define merge-ndx-aigs ((new ndx->aig-p) (curr ndx->aig-p))
  :returns (rslt ndx->aig-p)
  (if (endp new) (ndx->aig-fix curr)
    (merge-ndx-aigs (rest new)
                    (if (hons-get (caar new) curr)
                        (raise "internal error: should not rebind in aigs!")
                      (hons-acons (caar new) (cdar new) curr)))))

(defthm ndx->aig-fast-alist-fork
  (implies (and (ndx->aig-p x) (ndx->aig-p y))
           (ndx->aig-p (fast-alist-fork x y))))

(defthm ndx->aig-last
  (implies (ndx->aig-p x) (ndx->aig-p (last x))))

(defthm cyc->ndx->aig-fast-alist-fork
  (implies (and (cyc->ndx->aig-p x) (cyc->ndx->aig-p y))
           (cyc->ndx->aig-p (fast-alist-fork x y))))

(defthm cyc->ndx->aig-last
  (implies (cyc->ndx->aig-p x) (cyc->ndx->aig-p (last x))))

(in-theory (enable exs-solver-rdy exs-solver-undf)) ;; temporarily enable these..

(define exs-mod-tbl->aignet ((mod-tbl exs-mod-tbl-p "design tbl which is compiled into aignet in exs$")
                             &key (exs$ 'exs$) (state 'state))
  :returns (mv (new-exs$ exs-solver-undf :hyp (exs-solver-undf exs$)) state)
  (b* ((comb-transforms (if (sim-params->enable-fraig (exs$-sim-params exs$))
                            (list (my-balance-config)
                                  (my-rewrite-config)
                                  (aignet::make-fraig-config))
                          (list (my-balance-config)
                                (my-rewrite-config)))))
    (stobj-let ((aignet (exs$-aignet exs$)))
               (vmap nmap aignet state) 
               (mod-tbl->aignet mod-tbl
                                :comb-transforms comb-transforms)
               (b* ((exs$ (update-exs$-var->ndx vmap exs$))
                    (exs$ (update-exs$-ndx->var nmap exs$))
                    (exs$ (update-exs$-var->port (exs-mk-var->port mod-tbl) exs$)))
                 (mv exs$ state)))))

(define exs-forward-reduce ((cyc natp "defines frame [cyc-1:cyc] for [in:out]")
                            &key
                            ((chgs ndx-ctbl-p) 'nil)   ;; fast-alist of alists
                            ((add-on ndx-ctbl-p) 'nil) ;; fast-alist of fast-alists
                            (exs$ 'exs$))
  :returns (new-outs ndx-map-p "mapping of out ndxs to lits which changed in 0/1/2")
  (b* (((when (not (and (> cyc 0) (< cyc (exs$-cnl-map-length exs$)))))
        (raise "internal error: bad cyc index:~x0~%" cyc))
       (pre (1- cyc))
       (in-chgs (cdr (hons-get pre chgs)))
       (in-add  (cdr (hons-get pre add-on)))
       (out-add (cdr (hons-get cyc add-on))))
    (stobj-let ((aignet    (exs$-aignet exs$))
                (in-lvals  (exs$-cnl-mapi pre exs$))
                (out-lvals (exs$-cnl-mapi cyc exs$)))
               (new-outs) 
               (forward-reduce in-lvals out-lvals in-add out-add in-chgs)
               new-outs)))

(define exs-backward-expand ((out-ndxs ndx-list-p "output indexes for which to generate cnf")
                             (cyc natp "defines frame [cyc-1:cyc] for [in:out]")
                             &key (exs$ 'exs$))
  :guard (exs-solver-rdy exs$)
  :returns (mv (in-map ndx-map-p "mapping of input indexes to sat lits") 
               (out-map ndx-map-p "mapping of output indexes to sat lits") 
               (new-exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$)))
  (b* ((use-ipasir         (not (exs$-use-satlink exs$)))
       (compute-aigs       (exs$-compute-aigs exs$))
       (curr-next-base     (exs$-next-base exs$))
       (curr-next-aig-base (exs$-next-aig-base exs$))
       (curr-out-aig-ctbl  (exs$-out-aig-ctbl exs$))
       (curr-in-aig-ctbl   (exs$-in-aig-ctbl exs$))
       (curr-in-aigs       (and compute-aigs
                                (cdr (hons-get cyc curr-in-aig-ctbl))))
       (curr-out-aigs      (and compute-aigs
                                (cdr (hons-get cyc curr-out-aig-ctbl))))
       ((when (not (and (> cyc 0) (< cyc (exs$-cnl-map-length exs$)))))
        (mv (raise "internal error: bad cyc index:~x0~%" cyc) () exs$))
       (pre (1- cyc)))
    (stobj-let ((ipasir (exs$-solver exs$)) 
                (aignet (exs$-aignet exs$))
                (in-lvals (exs$-cnl-mapi pre exs$)))
               (cnf in-map out-map in-aigs out-aigs next-base next-aig-base ipasir)
               (backward-expand out-ndxs in-lvals curr-in-aigs
                                :base curr-next-base
                                :aig-base curr-next-aig-base
                                :use-ipasir use-ipasir
                                :compute-aigs compute-aigs
                                :aignet aignet
                                :ipasir ipasir)
               (b* ((exs$ (update-exs$-next-base next-base exs$))
                    (exs$ (update-exs$-next-aig-base next-aig-base exs$))
                    (exs$ (if (not compute-aigs) exs$
                            (b* ((new-out-aigs (fast-alist-clean
                                                (merge-ndx-aigs out-aigs
                                                                curr-out-aigs)))
                                 (new-in-aigs  (fast-alist-clean
                                                (merge-ndx-aigs in-aigs
                                                                curr-in-aigs)))
                                 (new-out-ctbl (fast-alist-clean
                                                (hons-acons cyc new-out-aigs
                                                            curr-out-aig-ctbl)))
                                 (new-in-ctbl  (fast-alist-clean
                                                (hons-acons cyc new-in-aigs
                                                            curr-in-aig-ctbl)))
                                 (exs$ (update-exs$-out-aig-ctbl new-out-ctbl exs$))
                                 (exs$ (update-exs$-in-aig-ctbl new-in-ctbl exs$)))
                              exs$)))
                    (exs$ (update-exs$-curr-cnf (revapp! cnf (exs$-curr-cnf exs$)) exs$)))
                 (mv in-map out-map exs$)))))

(in-theory (disable exs-solver-rdy exs-solver-undf)) ;; now we disable these..



