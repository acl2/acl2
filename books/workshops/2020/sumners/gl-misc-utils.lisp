; Copyright (C) 2020, Rob Sumners
; Written by Rob Sumners
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "GL")

(include-book "gl-misc-types")
(include-book "centaur/gl/gl" :dir :system)

#|

This book defines the following GL-based utility:

(compute-gl-term-shape ...)

Given a term and g-bindings, perform a symbolic simulation using the current 
built-in (well, it would be nice to use apply$ here but no stobj support) GL 
term interpreter to compute the shape with corresponding BFR (should only use
this in AIG-based modes like satlink). We then traverse the computed structure
and replace the BFR/AIGs with fresh variables (offset from a given starting
variable index). This is useful in combination with def-gl-fin-set to easily
generate the finite set of solutions to a given function without having to 
know beforehand the "shape" of the function. Many other uses as well..

|#


(define len! (x &key ((r natp) '0))
  :returns (rslt natp)
  (if (atom x) (lnfix r) (len! (rest x) :r (1+ r))))


(defsection shape-obj->bvar-vbind
  ;;
  ;; NOTE -- the following is a special variable binding, where the last
  ;;         cdr is expected to be T (at least, not nil).. and nil is used
  ;;         as a bottom value which denotes "no binding exists"
  ;; NOTE -- we include this type here instead of a types book because it
  ;;         should be in GL package and it is integral to the immediate
  ;;         definitions below
  ;;
  (fty::defalist bv-bind
                 :key-type natp
                 :val-type booleanp)
  
  (define look-bvar-bind ((bv natp) (vbind bv-bind-p))
    (if (atom vbind) nil
      (b* ((fst (car vbind)))
        (if (eql bv (car fst)) fst
          (look-bvar-bind bv (rest vbind)))))
    ///
    (defthm look-bvar-bind-retn
      (implies (and (bv-bind-p vb)
                    (look-bvar-bind bv vb))
               (and (consp (look-bvar-bind bv vb))
                    (natp (car (look-bvar-bind bv vb)))
                    (booleanp (cdr (look-bvar-bind bv vb)))))
      :hints (("Goal" :in-theory (enable bv-bind-p)))))

  (define add-bvar-vbind ((bv natp) (val booleanp) (vbind bv-bind-p))
    :returns (rslt bv-bind-p)
    (b* ((look (look-bvar-bind bv vbind)))
      (if look (and (eq val (cdr look)) (bv-bind-fix vbind))
        (cons (cons (lnfix bv) (bool-fix val)) (bv-bind-fix vbind)))))

  (define match-obj-vbind (x y bool-ctx (vbind bv-bind-p))
    :returns (rslt bv-bind-p)
    (and (if bool-ctx (iff x y) (equal x y)) (bv-bind-fix vbind)))

  (define match-int-vlst-vbind ((vlst nat-listp) (num integerp) (vbind bv-bind-p))
    :returns (rslt bv-bind-p)
    (and vbind 
         (not (endp vlst))
         (b* ((r-vl  (rest vlst))
              (f-vl  (first vlst)))
           (if (atom r-vl)
               (cond ((eql num 0)
                      (add-bvar-vbind f-vl nil vbind))
                     ((eql num -1)
                      (add-bvar-vbind f-vl nil vbind))
                     (t ;; integer was too big for variables
                      nil))
             (b* ((f-num (logand num 1))
                  (r-num (ash num -1)))
               (match-int-vlst-vbind r-vl r-num
                                     (add-bvar-vbind f-vl (eql f-num 1) 
                                                     vbind)))))))

  (define int-obj->var-bind ((vlst nat-listp) obj bool-ctx (vbind bv-bind-p))
    :returns (rslt bv-bind-p)
    (if bool-ctx ;; then we are matching an integer to boolean truth
        (match-obj-vbind t obj t vbind)
      (and (integerp obj)
           (match-int-vlst-vbind vlst obj vbind))))

  (define bool-obj->var-bind ((var natp) obj bool-ctx (vbind bv-bind-p))
    :returns (rslt bv-bind-p)
    (and (or bool-ctx (booleanp obj))
         (b* ((val (if bool-ctx (bool-fix obj) obj)))
           (add-bvar-vbind var val vbind))))

  (define shape-obj->bvar-vbind* ((shp shape-specp) obj bool-ctx (vbind bv-bind-p))
    :returns (rslt bv-bind-p)
    :verify-guards nil
    (cond
     ((not vbind) nil)
     ((atom shp)  (match-obj-vbind shp obj bool-ctx vbind))
     (t
      (pattern-match shp
        ((g-integer bits) (int-obj->var-bind bits obj bool-ctx vbind))
        ((g-number num)   (int-obj->var-bind (car num) obj bool-ctx vbind))
        ((g-boolean n)    (bool-obj->var-bind n obj bool-ctx vbind))
        ((g-ite tst then else)
         (b* ((t-bind (shape-obj->bvar-vbind* then obj bool-ctx
                        (shape-obj->bvar-vbind* tst t t vbind))))
           (or t-bind  ;; BOZO -- should I bias to then? or random? seems that
                       ;;         for most shapes, then short circuits faster.
               (shape-obj->bvar-vbind* else obj bool-ctx
                 (shape-obj->bvar-vbind* tst nil t vbind)))))
        ((g-concrete y)   (match-obj-vbind y obj bool-ctx vbind))
        ;; NOTE -- g-var's are untyped (i.e. not boolean) variables and we are only
        ;;         allowed in this function to match an object using boolean variable
        ;;         bindings.. so, we cannot match through binding a g-var:
        ;; BOZO -- similar to g-var case, we simply don't handle arbitrary function 
        ;;         calls. Note that if specific functions (say record access and update) 
        ;;         were needed and we could push the binding down then we could look
        ;;         to support both g-call and g-var to get to those cases.. would be
        ;;         a good idea in some cases and we could use the invert function
        ;;         provided in the g-call to assist, but not supported at the moment.
        ((g-var v)        nil)
        ((g-call & & &)   nil)
        ;; otherwise.. matching a cons..
        (& (if bool-ctx
               (match-obj-vbind t obj t vbind)
             (and (consp obj)
                  (shape-obj->bvar-vbind* (cdr shp) (cdr obj) nil
                    (shape-obj->bvar-vbind* (car shp) (car obj) nil vbind)))))))))
  
  (verify-guards shape-obj->bvar-vbind*)

  (define shape-obj->bvar-vbind ((shp shape-specp) obj)
    :short "given a shape specifier and some object, return a binding to 
            the (boolean) variables in spec such that the spec. matches obj.
            returns nil if no such binding can be found."
    :returns (rslt bv-bind-p)
    (shape-obj->bvar-vbind* shp obj nil t))
)

(defsection gobj-to-shape-spec

  (define mk-numlist ((n natp) (ndx natp) &key ((r nat-listp) 'nil))
    :returns (rslt nat-listp)
    (if (zp n) (mbe :logic (and (nat-listp r) r) :exec r)
      (mk-numlist (1- n) (1+ ndx) :r (cons ndx r))))
  
  (defthm shape-specp-cons
    (implies (and (shape-specp x) (shape-specp y))
             (shape-specp (cons x y)))
    :hints (("Goal" :in-theory (enable shape-specp)
             :expand (shape-specp (cons x y)))))
  
  (define gobj-to-shape-spec-loop (x (ndx natp) lst?)
    :returns (mv (rslt (if lst? (shape-spec-listp rslt) (shape-specp rslt))
                       :hints (("Goal" :in-theory (enable shape-specp))))
                 (n natp))
    :verify-guards nil
    (cond
     ((and lst? (consp x))
      (b* (((mv fst ndx)
            (gobj-to-shape-spec-loop (first x) ndx nil))
           ((mv rst ndx)
            (gobj-to-shape-spec-loop (rest x) ndx t)))
        (mv (cons fst rst) ndx)))
     (lst? (mv () (lnfix ndx)))
     ((atom x)
      (if (shape-specp x)
          (mv x (lnfix ndx))
        (mv (acl2::raise "ill-formed symbolic object encountered:~x0" x) (lnfix ndx))))
     (t
      (pattern-match x
        ((g-number nspec)
         (if (atom nspec)
             (mv (acl2::raise "ill-formed symbolic object encountered:~x0" x) (lnfix ndx))
           (b* ((n (len! (car nspec))))
             (mv (g-integer (mk-numlist n ndx)) (lnfix (+ ndx n))))))
        ((g-integer bits)
         (b* ((n (len! bits)))
           (mv (g-integer (mk-numlist n ndx)) (lnfix (+ ndx n)))))
        ((g-boolean &)
         (mv (g-boolean (lnfix ndx)) (lnfix (1+ ndx))))
        ((g-var var)
         (if (variablep var)
             (mv x (lnfix ndx))
           (mv (acl2::raise "ill-formed symbolic object encountered:~x0" x) (lnfix ndx))))
        ((g-ite test then else)
         (b* (((mv test ndx)
               (gobj-to-shape-spec-loop test ndx nil))
              ((mv then ndx)
               (gobj-to-shape-spec-loop then ndx nil))
              ((mv else ndx)
               (gobj-to-shape-spec-loop else ndx nil)))
           (mv (g-ite test then else) ndx)))
        ((g-concrete &) (mv x (lnfix ndx)))
        ((g-apply fn args)
         (if (not (and (symbolp fn) (not (eq fn 'quote))))
             (mv (acl2::raise "ill-formed symbolic object encountered:~x0" x) (lnfix ndx))
           (b* (((mv args ndx)
                 (gobj-to-shape-spec-loop args ndx t)))
             ;; BOZO -- need to include a mapping of functions and shapes to inverses.. but
             ;; don't have that yet.. may cause us to fail some coverage tests if we don't fix
             ;; this afterwards.
             (mv (g-call fn args nil) ndx))))
        ((g-call & & &)
         ;; NOTE -- we should not see G-CALL's in symbolic objects, so fail:
         (mv (acl2::raise "ill-formed symbolic object encountered:~x0" x) (lnfix ndx)))
        (&
         (b* (((mv scar ndx)
               (gobj-to-shape-spec-loop (car x) ndx nil))
              ((mv scdr ndx)
               (gobj-to-shape-spec-loop (cdr x) ndx nil)))
           (mv (cons scar scdr) ndx)))))))

  (verify-guards gobj-to-shape-spec-loop)

  (define gobj-to-shape-spec (x &key ((ndx natp) '2))
    :short "map a symbolic gl object to a corresponding shape spec"
    :returns (rslt shape-specp
                   :hints (("Goal"
                            :in-theory (disable RETURN-TYPE-OF-GOBJ-TO-SHAPE-SPEC-LOOP.RSLT)
                            :use ((:instance RETURN-TYPE-OF-GOBJ-TO-SHAPE-SPEC-LOOP.RSLT
                                             (lst? nil))))))
    (b* (((mv rslt -) (gobj-to-shape-spec-loop x ndx nil)))
      rslt))
)

(defsection offset-ndxs-shape-spec
  
  (define offset-numlist ((x nat-listp) (off natp))
    :returns (rslt nat-listp)
    (if (endp x) () (cons (lnfix (+ (first x) off))
                          (offset-numlist (rest x) off))))
  
  (defines offset-ndxs-shape-spec
    :short "a simple function which offsets all of the var. ndxs in a given shape by a given offset"
    :returns-hints (("Goal" :in-theory (enable shape-specp)))
  
    (define offset-ndxs-shape-spec ((x shape-specp) (off natp))
      :returns (rslt shape-specp :hyp :guard)
      (if (atom x) x
        (pattern-match x
         ((g-number nspec)
          (g-integer (offset-numlist (car nspec) off)))
         ((g-integer bits) (g-integer (offset-numlist bits off)))
         ((g-boolean n) (g-boolean (lnfix (+ n off))))
         ((g-var &) x)
         ((g-ite test then else)
          (g-ite (offset-ndxs-shape-spec test off)
                 (offset-ndxs-shape-spec then off)
                 (offset-ndxs-shape-spec else off)))
         ((g-concrete &) x)
         ((g-call fn args inv)
          (g-call fn (offset-ndxs-shape-spec-list args off) inv))
         (& (cons (offset-ndxs-shape-spec (car x) off)
                  (offset-ndxs-shape-spec (cdr x) off))))))
 
    (define offset-ndxs-shape-spec-list ((x shape-spec-listp) (off natp))
      :returns (rslt shape-spec-listp :hyp :guard)
      (if (atom x) nil
        (cons (offset-ndxs-shape-spec (first x) off)
              (offset-ndxs-shape-spec-list (rest x) off)))))

)


(defsection compute-gl-term-shape

  (define gl-interp-loop-setup ((g-b shape-spec-bindingsp)
                                config next-bvar
                                pathcond bvar-db state)
    :short "this function computes an alist and config and sets up pathcond and bvar-db for GL interpreter calls"
    :guard-hints (("Goal" :in-theory (e/d (get-global) (glcp-config-p))))
    :returns (mv alist
                 (config (and (glcp-config-p config)
                              (acl2::interp-defs-alistp (glcp-config->overrides config))))
                 pathcond bvar-db state)
    (b* (((unless (bfr-mode)) ;; we do not want to do this in BDD-mode:
          (mv (acl2::raise "do not want to call this function in BDD mode!")
              (make-glcp-config) pathcond bvar-db state))
         ((mv erp overrides state)
          (preferred-defs-to-overrides
           (table-alist 'preferred-defs (w state)) state))
         ((when erp)
          (mv (acl2::raise "error encountered while getting preferred defs:~x0" erp)
              (make-glcp-config) pathcond bvar-db state))
         (tmp-bvar (if (natp next-bvar) next-bvar 2))
         (bvar-db  (init-bvar-db tmp-bvar bvar-db))
         (pathcond (bfr-hyp-init pathcond))
         (alist    (shape-specs-to-interp-al g-b))
         (config   (or config (make-glcp-config :overrides overrides)))
         ((when (not (glcp-config-p config)))
          (mv (acl2::raise "ill-formed glcp config object encountered:~x0" config)
              (make-glcp-config) pathcond bvar-db state))
         ((when (not (acl2::interp-defs-alistp (glcp-config->overrides config))))
          (mv (acl2::raise "glcp-config overrides returned ill-formed:~x0" (glcp-config->overrides config))
              (make-glcp-config) pathcond bvar-db state)))
      (mv alist config pathcond bvar-db state)))
  
  ;; our main function.. we introduce this with a make-event so that we can
  ;; get the latest and greatest gl clause-processor interp-term function from
  ;; the world..
  
  (make-event
   (b* ((interp-term-fn
         (cdr (assoc 'interp-term
                     (table-alist 'latest-greatest-gl-clause-proc
                                  (w state)))))
        ((unless interp-term-fn)
         (prog2$ (er hard? 'compute-gl-term-shape
                     "Could not find interp-term function.. possible that GL is not loaded?.. shouldn't happen")
                 `(value t))))
     `(define compute-gl-term-shape ((x   pseudo-termp)
                                     (g-b shape-spec-bindingsp)
                                     &key
                                     (config    'nil)
                                     (next-bvar 'nil)
                                     (state     'state))
        :short "takes a term and shape-spec binding to variables and returns a shape-spec 
                correlated to symbolic evaluation of the term"
        :guard-hints (("Goal" :in-theory (e/d (get-global) (glcp-config-p))))
        :returns (mv (rslt shape-specp) state)
        (b* (((acl2::local-stobjs pathcond interp-st bvar-db)
              (mv shp pathcond interp-st bvar-db state))
             ((mv alist config pathcond bvar-db state)
              (gl-interp-loop-setup g-b config next-bvar pathcond bvar-db state))
             (clk (glcp-config->concl-clk config))
             (contexts nil)
             ((mv xobj erp pathcond interp-st bvar-db state)
              (,interp-term-fn x alist contexts pathcond clk
                               config interp-st bvar-db state))
             ((when erp)
              (mv (acl2::raise "error encountered during glcp interpretation:~x0" erp)
                  pathcond interp-st bvar-db state))
             (next-bvar (if (natp next-bvar) next-bvar
                          (shape-spec-max-bvar-list (shape-spec-bindings->sspecs g-b))))
             (shp (gobj-to-shape-spec xobj :ndx next-bvar)))
          (mv shp pathcond interp-st bvar-db state)))))

)
  
#|

(setup-sat)

(compute-gl-term-shape '(cons (binary-+ x y) (cons (< y x) (cons (if (< x y) ':foo ':bar) 'nil)))
                       `((x ,(g-integer (list 1 2 6))) (y ,(g-integer (list 3 4 5)))))

should return:

(((:G-INTEGER 10 9 8 7)
  (:G-BOOLEAN . 11)
  (:G-ITE ((:G-BOOLEAN . 12) . :BAR)
          . :FOO))
 <state>)

|#

(defsection gl-term->aig

  ;; BOZO -- I would love to convert the following to work on "hypo" and "concl" like
  ;;         def-gl-thm processes it and the best approximation would be to implement
  ;;         something similar to interp-term-under-hyp (but with guards verified)
  ;;         but I need to understand how the parameterized bvar-db stuff works because
  ;;         I don't want to lose contact with the AIG vars.. so doing the easier thing
  ;;         for now..
  
  (make-event
   (b* ((interp-test-fn
         (cdr (assoc 'interp-test
                     (table-alist 'latest-greatest-gl-clause-proc
                                  (w state)))))
        ((unless interp-test-fn)
         (prog2$ (er hard? 'gl-term->aig
                     "Could not find interp-test function.. possible that GL is not loaded?.. shouldn't happen")
                 `(value t))))
     `(define gl-term->aig ((x         pseudo-termp)
                            (g-b       shape-spec-bindingsp)
                            &key
                            (config    'nil)
                            (next-bvar 'nil)
                            (state     'state))
        :short "takes a term x and a shape binding g-b, and uses GL interpretation 
                (under boolean context) to produce an AIG"
        :guard-hints (("Goal" :in-theory (e/d (get-global) (glcp-config-p))))
        (b* (((acl2::local-stobjs pathcond interp-st bvar-db)
              (mv bfr pathcond interp-st bvar-db state))
             ((mv alist config pathcond bvar-db state)
              (gl-interp-loop-setup g-b config next-bvar pathcond bvar-db state))
             (clk (glcp-config->concl-clk config))
             ((mv bfr erp pathcond interp-st bvar-db state)
              (,interp-test-fn x alist pathcond clk
                               config interp-st bvar-db state))
             ((when erp)
              (mv (acl2::raise "error encountered during glcp interpretation:~x0" erp)
                  pathcond interp-st bvar-db state)))
          (mv bfr pathcond interp-st bvar-db state)))))

  ;; a few stupid functions for testing purposes..
  
  (define aig->trm (x)
    (cond ((atom x) x)
          ((eq (cdr x) nil) (list 'not (aig->trm (car x))))
          (t (list 'and (aig->trm (car x)) (aig->trm (cdr x))))))
  
  (define g->a ((x   pseudo-termp)
                (g-b shape-spec-bindingsp)
                &key 
                (state 'state))
    (b* (((mv bfr state) (gl-term->aig x g-b)))
      (mv (aig->trm bfr) state)))

)
  
#|

(setup-sat)

(g->a '(equal x y) `((x ,(g-integer (list 3 4 5))) (y ,(g-integer (list 6 7 8)))))

(g->a '(< x y) `((x ,(g-integer (list 3 4 5))) (y ,(g-integer (list 6 7 8)))))

(g->a '(if (integerp x) (if (< y '0) 't 'nil) 'nil) `((x ,(g-integer (list 3 4 5))) (y ,(g-integer (list 6 7 8)))))

|#
