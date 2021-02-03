; Copyright (C) 2020, Rob Sumners
; Written by Rob Sumners
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "GL")

(include-book "gl-misc-utils")
(include-book "centaur/ipasir/ipasir-tools" :dir :system)
(include-book "centaur/aignet/aig-cnf" :dir :system)
(include-book "centaur/ipasir/ipasir-backend" :dir :system)

#|

This book defines the following GL-based utility (using incremental SAT via IPASIR):

(compute-finite-values ...)

Takes a concl and g-bindings (shape specs) similar to def-gl-thm but in
addition for a specified variable in the g-bindings (i.e. one of the free
variables), compute-finite-values will produce a finite number of solutions for
the specified free variable upto some specified limit or potentially a complete
set. We use existing GL->AIG->CNF conversion to get a CNF and variable
correlation through sat-lits and this is then loaded into IPASIR incremental
SAT state and then iterated on with incremental SAT to find the different
possible values.

|#


(fty::defprod gfs-config
  (do-not-expand-free-bvars
   gatesimp
   transform-config
   glcp-config))

(fty::defalist lit-tbl
  :key-type natp
  :val-type satlink::litp
  :true-listp t)

(fty::defalist fin-bind
  :key-type natp
  :val-type booleanp
  :true-listp t)

(fty::deflist fin-binds
  :elt-type fin-bind-p
  :true-listp t)

(fty::define gatesimp-fix (x)
  :returns (rslt aignet::gatesimp-p)
  (if (aignet::gatesimp-p x) x (aignet::default-gatesimp)))
    
(fty::define default-gfs-config ()
  :returns (rslt gfs-config-p)
  (make-gfs-config :gatesimp (aignet::default-gatesimp)
                   :transform-config nil
                   :glcp-config nil))

#!AIGNET
(acl2::defiteration gl::cnf->aignet-load-litarr (litarr sat-lits aignet)
  (declare (xargs :stobjs (litarr sat-lits aignet)
                  :guard (and (aignet::sat-lits-wfp sat-lits aignet)
                              (<= (aignet::num-ins aignet) 
                                  (aignet::lits-length litarr)))))
  (b* ((id (innum->id gl::n aignet))
       ((unless (aignet-id-has-sat-var id sat-lits)) litarr)
       (lit (aignet-id->sat-lit id sat-lits)))
    (set-lit gl::n lit litarr))
  :returns litarr
  :iter-guard (<= gl::n (num-ins aignet))
  :last (num-ins aignet))

#!AIGNET
(define gl::litarr-to-list ((i natp) litarr)
  :guard (<= i (aignet::lits-length litarr))
  :measure (nfix (- (lits-length litarr) (nfix i)))
  (b* (((when (mbe :logic (zp (- (lits-length litarr) (nfix i)))
                   :exec (eql (lits-length litarr) i)))
        nil))
    (cons (get-lit i litarr)
          (gl::litarr-to-list (1+ (lnfix i)) litarr))))

#!AIGNET
(define gl::compute-lit-tbl (vars sat-lits aignet)
  :guard (and (sat-lits-wfp sat-lits aignet)
              (<= (len vars) (num-ins aignet))
              (true-listp vars))
  :returns (rslt gl::lit-tbl-p)
  (b* (((acl2::local-stobjs litarr) (mv lit-tbl litarr))
       (litarr  (resize-lits (num-ins aignet) litarr))
       (litarr  (gl::cnf->aignet-load-litarr litarr sat-lits aignet))
       (lit-tbl (make-fast-alist (pairlis$ vars (gl::litarr-to-list 0 litarr))))
       ((unless (gl::lit-tbl-p lit-tbl))
        (mv (raise "internal error: lit-tbl should be a lit-tbl!") litarr)))
    (mv lit-tbl litarr)))

#!AIGNET
(define gl::term->ipasir ((x      pseudo-termp)
                          (g-b    gl::shape-spec-bindingsp)
                          (config gl::gfs-config-p)
                          &key
                          (ipasir 'ipasir)
                          (state  'state))
  :guard (and (not (eq (ipasir::ipasir-get-status ipasir) :undef))
              (ipasir::ipasir-empty-new-clause ipasir))
  :returns (mv (lit-tbl gl::lit-tbl-p)
               (ipasir (and (equal (ipasir::ipasir$a->status ipasir) :input)
                            (not (ipasir::ipasir$a->new-clause ipasir)))
                       :hyp (and (not (equal (ipasir::ipasir$a->status ipasir) :undef))
                                 (not (ipasir::ipasir$a->new-clause ipasir))))
               state)
  (b* (((acl2::local-stobjs sat-lits aignet)
        (mv lit-tbl sat-lits aignet ipasir state))
       ((mv aig state)
        (gl::gl-term->aig x g-b :config (gl::gfs-config->glcp-config config)))
       ((mv cnf - vars sat-lits aignet)
        (aig->cnf aig sat-lits aignet
                  :transform-config (gl::gfs-config->transform-config config)
                  :gatesimp         (gl::gatesimp-fix (gl::gfs-config->gatesimp config))))
       ;; (- (cw "clauses:~x0~%" cnf))
       (ipasir  (ipasir-add-clauses ipasir cnf))
       ((when (not (true-listp vars)))
        (mv (raise "internal error: expected true-list!") 
            sat-lits aignet ipasir state))
       (lit-tbl (gl::compute-lit-tbl vars sat-lits aignet)))
    (mv lit-tbl sat-lits aignet ipasir state)))

(define read-ipasir-bind ((lit-tbl lit-tbl-p) 
                          &key 
                          ((rslt fin-bind-p) 'nil) 
                          (ipasir::ipasir 'ipasir::ipasir))
  :guard (eq (ipasir::ipasir-get-status ipasir::ipasir) :sat)
  :returns (rslt fin-bind-p)
  (if (endp lit-tbl) (fin-bind-fix (make-fast-alist rslt))
    (b* ((val (ipasir::ipasir-val ipasir::ipasir (cdar lit-tbl))))
      (read-ipasir-bind (rest lit-tbl)
                        :rslt (cons (cons (caar lit-tbl) (eql val 1)) rslt)))))

(define make-bind-clause ((bind fin-bind-p) (lit-tbl lit-tbl-p)
                          &key ((rslt aignet::lit-listp) 'nil))
  :returns (rslt aignet::lit-listp)
  (if (endp bind) (aignet::lit-list-fix rslt)
    (b* ((look (hons-get (caar bind) lit-tbl))
         ((when (not look))
          (make-bind-clause (rest bind) lit-tbl :rslt rslt))
         (val (cdar bind))
         (lit (cdr look))
         (lit (if val (aignet::lit-negate lit) lit)))
      (make-bind-clause (rest bind) lit-tbl :rslt (cons lit rslt)))))

(define prune-fin-bind ((bvars nat-listp) (f-bind fin-bind-p)
                        &key ((rslt fin-bind-p) 'nil))
  :returns (rslt fin-bind-p)
  (if (endp bvars) (fin-bind-fix rslt)
    (prune-fin-bind (rest bvars) f-bind
                    :rslt (cons (cons (first bvars) 
                                      (cdr (hons-get (first bvars) f-bind)))
                                rslt))))

(define compute-fin-binds ((num natp) (tgt-bvars nat-listp) (lit-tbl lit-tbl-p)
                           &key 
                           ((rslt fin-binds-p) 'nil) 
                           (ipasir::ipasir 'ipasir::ipasir))
  :guard (and (not (eq (ipasir::ipasir-get-status ipasir::ipasir) :undef))
              (ipasir::ipasir-empty-new-clause ipasir::ipasir))
  :returns (mv total 
               (rslt fin-binds-p)
               (ipasir::ipasir 
                (and (not (equal (ipasir::ipasir$a->status ipasir::ipasir) :undef))
                     (not (ipasir::ipasir$a->new-clause ipasir::ipasir)))
                :hyp (and (not (equal (ipasir::ipasir$a->status ipasir::ipasir) :undef))
                          (not (ipasir::ipasir$a->new-clause ipasir::ipasir)))))
  :verify-guards nil
  (if (zp num) (mv nil (fin-binds-fix rslt) ipasir::ipasir)
    (b* (((mv status ipasir::ipasir) 
          (ipasir::ipasir-solve ipasir::ipasir)))
      (cond ((eq status :failed)
             ;; BOZO (Rob) -- not sure what to do here.. gonna allow result to go back
             ;; output a note.. but that is not exactly what I want to do..
             (prog2$ (cw "NOTE during gl-fin-set computation: returning early due to incremental SAT failure!") 
                     (mv nil (fin-binds-fix rslt) ipasir::ipasir)))
            ((eq status :unsat)
             (mv t (fin-binds-fix rslt) ipasir::ipasir))
            (t (b* ((bind     (read-ipasir-bind lit-tbl))
                    (tgt-bind (prune-fin-bind tgt-bvars bind))
                    (bind-cls (make-bind-clause tgt-bind lit-tbl))
                    (ipasir::ipasir   
                     (ipasir::ipasir-add-clauses ipasir::ipasir (list bind-cls))))
                 (compute-fin-binds (1- num) tgt-bvars lit-tbl :rslt (cons bind rslt))))))))

(verify-guards compute-fin-binds-fn)

(define eval-numlist-f-b ((vars nat-listp) (f-b fin-bind-p))
  :returns (rslt integerp)
  (if (endp vars) 0
    (b* ((v (first vars))
         (rst (rest vars))
         (val (cdr (hons-get v f-b))))
      (if (endp rst)
          (if val -1 0)
        (logior (if val 1 0)
                (ash (eval-numlist-f-b rst f-b) 1))))))                          

(defines eval-shape-f-bind
  :short "evaluate a shape specifier relative to an f-binding mapping aig-vars to bools"
  :returns-hints (("Goal" :in-theory (enable shape-specp)))
  
  (define eval-shape-f-bind ((x shape-specp) (f-b fin-bind-p))
    (if (atom x) x
      (gl::pattern-match x
         ((gl::g-number nspec) (eval-numlist-f-b (car nspec) f-b))
         ((gl::g-integer bits) (eval-numlist-f-b bits f-b))
         ((gl::g-boolean n)    (cdr (hons-get n f-b)))
         ((gl::g-var &)        nil) ;; default to nil for g-vars!
         ((gl::g-ite test then else)
          (if (eval-shape-f-bind test f-b)
              (eval-shape-f-bind then f-b)
            (eval-shape-f-bind else f-b)))
         ((gl::g-concrete obj) obj) 
         ((gl::g-call fn args &)
          (b* ((args (eval-shape-f-bind-list args f-b))
               ((mv ok rslt) (gl::eval-g-base-apply fn args))
               ((unless ok)  
                (acl2::raise "evaluation of call in shape under f-bind failed:~x0" fn)))
            rslt))
         (& (cons (eval-shape-f-bind (car x) f-b)
                  (eval-shape-f-bind (cdr x) f-b))))))
 
    (define eval-shape-f-bind-list ((x gl::shape-spec-listp) (f-b fin-bind-p))
      (if (atom x) nil
        (cons (eval-shape-f-bind (first x) f-b)
              (eval-shape-f-bind-list (rest x) f-b)))))

(define alist-fix (x)
  :inline t
  :enabled t
  :guard (alistp x)
  (mbe :logic (if (alistp x) x nil)
       :exec x))

(define trans-fin-bind ((g-b shape-spec-bindingsp) 
                        (f-b fin-bind-p)
                        &key ((rslt alistp) 'nil))
  :returns (rslt alistp)
  (if (atom g-b) (alist-fix rslt)
    (trans-fin-bind (rest g-b) f-b
                    :rslt (cons (cons (caar g-b)
                                      (eval-shape-f-bind (cadar g-b) f-b))
                                rslt))))

(define create-g-fset ((g-bind alistp) target)
  (b* ((look (assoc-equal target g-bind)))
    (cons (if look (cdr look)
            (acl2::raise "did not find target var in resulting g-bind:~x0" target))
          ;; BOZO -- could remove the target entry here, but no real reason to..
          g-bind)))

(define trans-fin-binds ((fin-binds fin-binds-p)
                         (g-b shape-spec-bindingsp)
                         target
                         &key (rslt 'nil))
  (if (endp fin-binds) rslt
    (b* ((g-bind (trans-fin-bind g-b (first fin-binds)))
         (- (fast-alist-free (first fin-binds))) ;; don't need this anymore..
         (g-fset (create-g-fset g-bind target)))
      (trans-fin-binds (rest fin-binds) g-b target :rslt (cons g-fset rslt)))))

(define comp-free-bvars ((tgt-bvars nat-listp)
                         (lit-tbl lit-tbl-p)
                         &key ((rslt nat-listp) 'nil))
  :returns (rslt nat-listp)
  (if (endp tgt-bvars)
      (mbe :logic (if (nat-listp rslt) rslt nil) :exec rslt)
    (comp-free-bvars (rest tgt-bvars) lit-tbl
                     :rslt (if (hons-get (first tgt-bvars) lit-tbl) rslt
                             (cons (first tgt-bvars) rslt)))))
   
(define free-fast-alists (x)
  (if (atom x) x
    (b* ((- (fast-alist-free (first x))))
      (free-fast-alists (rest x)))))

(define add-exp-fin-bind ((free-bvars nat-listp)
                          (fin-bind fin-bind-p)
                          (rslt fin-binds-p))
  :verify-guards nil
  :returns (rslt fin-binds-p)
  (if (endp free-bvars)
      (cons (make-fast-alist (fin-bind-fix fin-bind))
            (fin-binds-fix rslt))
    (b* ((bvar (first free-bvars))
         (rst  (rest  free-bvars)))
      (add-exp-fin-bind rst (cons (cons bvar t) fin-bind)
                        (add-exp-fin-bind rst (cons (cons bvar nil) fin-bind)
                                          rslt)))))

(verify-guards add-exp-fin-bind)

(define expand-fin-binds ((fin-binds fin-binds-p)
                          (free-bvars nat-listp)
                          &key ((rslt fin-binds-p) 'nil))
  :returns (rslt fin-binds-p)
  (if (endp fin-binds) (fin-binds-fix rslt)
    (expand-fin-binds (rest fin-binds) free-bvars
                      :rslt (add-exp-fin-bind free-bvars (first fin-binds) rslt)))) 

(define compute-finite-set ((x     pseudo-termp) 
                            (g-b   shape-spec-bindingsp)
                            target       ;; variable in g-b targeted for finite enumeration
                            (num   natp) ;; minimum number of values to find before exiting
                            &key
                            ((config gfs-config-p) '(default-gfs-config))
                            (state                 'state))
  :guard (assoc-equal target g-b)
  :guard-hints (("Goal" :in-theory (enable shape-spec-bindingsp)))
  (ipasir::with-local-ipasir
    (mv-let (is-total rslt ipasir::ipasir state)
        (b* (((mv lit-tbl ipasir::ipasir state) 
                                     (term->ipasir x g-b config))
             (tgt-shape              (cadr (assoc-equal target g-b)))
             (tgt-bvars              (gl::shape-spec-indices tgt-shape))
             (free-bvars             (comp-free-bvars   tgt-bvars lit-tbl))
             ((mv is-total fin-binds ipasir::ipasir) 
                                     (compute-fin-binds num tgt-bvars lit-tbl))
             (fin-binds              (if (or (atom free-bvars)
                                             (gfs-config->do-not-expand-free-bvars config))
                                         fin-binds
                                       (b* ((- (free-fast-alists fin-binds)))
                                         (expand-fin-binds fin-binds free-bvars))))
             (rslt                   (trans-fin-binds   fin-binds g-b target))
             (-                      (fast-alist-free   lit-tbl))
             (-                      (fast-alist-free   fin-binds)))
          (mv is-total rslt ipasir::ipasir state))
      (mv is-total rslt state))))

;; (defmacro def-gl-fin-set (name &rest 
;; (defmacro def-gl-fin-set )

;; we also define a useful alternate composition which computes the set
;; of possible values that a given term may evaluate to..

(define compute-finite-values ((x     pseudo-termp) 
                               (h     pseudo-termp)
                               (g-b   shape-spec-bindingsp)
                               (num   natp) ;; minimum number of values to find before exiting
                               &key
                               ((top-var variablep)   '(quote top))
                               ((config gfs-config-p) '(default-gfs-config))
                               (state                 'state))
  :guard (not (assoc-equal top-var g-b))
  :guard-hints (("Goal" :in-theory (enable shape-spec-bindingsp)))
  (b* (((mv shape state) (compute-gl-term-shape x g-b))
       (new-g-b          (cons (list top-var shape) g-b))
       (new-x            `(if ,h (equal ,top-var ,x) (quote nil))))
    (compute-finite-set new-x new-g-b top-var num :config config)))

;;;;;;;;;;;;;;;;

(define see-fs ((x      pseudo-termp) 
                (g-b    shape-spec-bindingsp)
                target        ;; variable in g-b targeted for finite enumeration
                (num    natp) ;; minimum number of values to find before exiting
                &key
                (state  'state))
  :guard (assoc-equal target g-b)
  :guard-hints (("Goal" :in-theory (enable shape-spec-bindingsp)))
  (b* (((mv is-total rslt state) 
        (compute-finite-set x g-b target num)))
    (mv (list is-total rslt) state)))

(define see-vals ((x      pseudo-termp) 
                  (g-b    shape-spec-bindingsp)
                  (num    natp) ;; minimum number of values to find before exiting
                  &key
                  ((top-var variablep)   '(quote top))
                  (state  'state))
  :guard (not (assoc-equal top-var g-b))
  :guard-hints (("Goal" :in-theory (enable shape-spec-bindingsp)))
  (b* (((mv is-total rslt state) 
        (compute-finite-values x ''t g-b num :top-var top-var)))
    (mv (list is-total rslt) state)))

