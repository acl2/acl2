; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "../mlib/expr-tools")
(include-book "../mlib/stmt-tools")
(include-book "../mlib/modnamespace")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc resolve-indexing
  :parents (transforms)
  :short "Resolve @(':vl-index') operators into @(':vl-bitselect') and
@(':vl-array-index') operators."

  :long "<p>When our @(see parser) encounters a subexpression like @('foo[i]'),
it does not know whether @('foo') is an ordinary vector like @('wire [3:0]
foo'), an array like @('reg [63:0] foo [128:0];'), or something more
complicated like a reference into an array of instances or similar.  To account
for this, the parser just produces @(':vl-index') operators whenever it sees a
selection like @('foo[i]').</p>

<p>In this transform, we convert these unresolved index operators into proper
@(':vl-bitselect') or @(':vl-array-index') operations when we can tell that
they are pointing at an ordinary wire or an array, respectively.  This
transform should typically be run very early in the transformation sequence, as
later transforms often expect to find proper @(':vl-bitselect') operators.</p>

<p>Note that this transform may not convert all occurrences of @(':vl-index')
operators.  For instance, we don't (currently) try to follow hierarchical
identifiers.  We might eventually want to make this transform smarter, to be
able to handle more cases.</p>")

(local (xdoc::set-default-parents resolve-indexing))

(define vl-vardecl-bitselect-p ((x vl-vardecl-p))
  :short "Recognize variables @('foo') where @('foo[i]') is definitely a
          bit-select, i.e., not some kind of array index or similar."
  :long "<p>BOZO this is pretty weak right now.  Eventually we'll want to
         extend it to things like packed structures, etc.</p>"
  (b* (((vl-vardecl x) x)
       ((when (consp x.dims))
        ;; Has array dimensions, doesn't seem like a bit-select.
        nil)
       ((unless (eq (vl-datatype-kind x.vartype) :vl-coretype))
        ;; Struct or enum or user defined type of some kind.  Don't try to
        ;; handle it yet.  BOZO eventually handle this sort of thing
        nil)
       ((vl-coretype x.vartype) x.vartype))
    (or
     ;; Vector integer types.  These may have an associated packed dimension list
     ;; directly within the type, e.g., we might have `reg foo` or `reg [3:0] foo;`
     (and (member x.vartype.name '(:vl-reg :vl-logic :vl-bit))
          (or (atom x.vartype.dims)        ;; Selecting from reg foo; -- weird but we'll call it good
              (atom (cdr x.vartype.dims))  ;; Selecting from reg [3:0] foo; -- fine
              ;; Otherwise something like reg [3:0][4:0] foo -- doesn't seem like a bitselect
              ))
     ;; Atomic integer types.  It seems okay to bit-select from these.  They
     ;; should never have associated dimensions.
     (and (member x.vartype.name '(:vl-byte :vl-shortint :vl-int :vl-longint :vl-integer))
          ;; dims should never happen here
          (or (atom x.vartype.dims)
              (raise "integer atom type with dimensions? ~x0." x)))
     ;; Anything else is just too hard and we're not going to think about it.
     ;; This includes, e.g.,: real, string, chandle, void, event
     )))

(define vl-vardecllist-filter-arrays
  :short "Filter variable declarations into those for which @('foo[i]') is a
          bit-select versus an array-index."
  ((x          vl-vardecllist-p "Decls we're filtering.")
   (bitselects vl-vardecllist-p "Accumulator for variables whose selects are bit-selects.")
   (arrays     vl-vardecllist-p "Accumulator for variables whose selects are array indexing operations.")
   (others     vl-vardecllist-p "Accumulator for more complicated things."))
  :verbosep t
  :returns
  (mv (bitselects vl-vardecllist-p)
      (arrays     vl-vardecllist-p)
      (others     vl-vardecllist-p))
  (b* (((when (atom x))
        (mv (vl-vardecllist-fix bitselects)
            (vl-vardecllist-fix arrays)
            (vl-vardecllist-fix others)))
       (x1 (vl-vardecl-fix (car x)))
       ((vl-vardecl x1) x1)
       ((when (consp x1.dims))
        ;; I think this might be right.  It has array dimensions, so no matter
        ;; what kind of base type it is, it seems reasonable to call an index
        ;; into it an array index.
        (vl-vardecllist-filter-arrays (cdr x) bitselects (cons x1 arrays) others))
       ((when (vl-vardecl-bitselect-p x1))
        (vl-vardecllist-filter-arrays (cdr x) (cons x1 bitselects) arrays others)))
    ;; Otherwise, too hard, not sure what this is yet.
    (vl-vardecllist-filter-arrays (cdr x) bitselects arrays (cons x1 others))))

(define vl-netdecllist-filter-arrays
  :short "Filter register declarations into arrays and non-arrays."
  ((x          vl-netdecllist-p "Decls we're filtering.")
   (arrays     vl-netdecllist-p "Accumulator for the arrays.")
   (non-arrays vl-netdecllist-p "Accumulator for the non-arrays."))
  :returns
  (mv (arrays vl-netdecllist-p)
      (non-arrays vl-netdecllist-p))
  (b* (((when (atom x))
        (mv (vl-netdecllist-fix arrays)
            (vl-netdecllist-fix non-arrays)))
       (x1 (vl-netdecl-fix (car x)))
       ((when (consp (vl-netdecl->arrdims x1)))
        (vl-netdecllist-filter-arrays (cdr x) (cons x1 arrays) non-arrays)))
    (vl-netdecllist-filter-arrays (cdr x) arrays (cons x1 non-arrays))))

;; BOZO maybe we can also have arrays of variables, events, etc.?

(defines vl-expr-resolve-indexing-aux
  :short "Core routine for introducing @(':vl-array-index') and
@(':vl-bitselect') operators throughout a @(see vl-expr-p)."

  (define vl-expr-resolve-indexing-aux
    ((x        vl-expr-p)
     (arrfal   "Fast alist binding names of arrays to anything.")
     (wirefal  "Fast alist binding names of wires (non-arrays) to anything.")
     (warnings vl-warninglist-p
               "We don't currently add any warnings, but we put this warnings
                accumulator in, in case we ever want to."))
    :returns
    (mv (new-warnings vl-warninglist-p)
        (changedp     booleanp :rule-classes :type-prescription
                      "Optimization, don't re-cons index-free expresions.")
        (new-x        vl-expr-p))
    :verify-guards nil
    :measure (vl-expr-count x)
    :flag :expr
    (b* ((x (vl-expr-fix x))
         ((when (vl-fast-atom-p x))
          (mv (ok) nil x))
         (op   (vl-nonatom->op x))
         (args (vl-nonatom->args x))
         ((mv warnings args-changedp args)
          (vl-exprlist-resolve-indexing-aux args arrfal wirefal warnings))

         (name (and (eq op :vl-index)
                    (vl-idexpr-p (first args))
                    (vl-idexpr->name (first args))))

         ((unless name)
          ;; BOZO maybe some kind of hierarchical identifier or similar?  We
          ;; could do something smarter here to try to track it down and figure
          ;; it out.  Or, maybe we should leave those things as
          ;; unresolved-indexes.
          (mv (ok)
              args-changedp
              (if (not args-changedp)
                  x
                (change-vl-nonatom x :args args))))

         ((when (hons-get name wirefal))
          (mv (ok) t (change-vl-nonatom x :op :vl-bitselect)))
         ((when (hons-get name arrfal))
          (mv (ok) t (change-vl-nonatom x :op :vl-array-index))))

      ;; Otherwise: we somehow don't know whether this name is an array or a
      ;; non-array.  It might be, for instance, that this is a "real" variable
      ;; or similar, which we aren't supporting.  We're just going to leave any
      ;; indexing into such variables as unresolved.
      (mv (ok)
          args-changedp
          (if (not args-changedp)
              x
            (change-vl-nonatom x :args args)))))

  (define vl-exprlist-resolve-indexing-aux
    ((x        vl-exprlist-p)
     (arrfal   "Fast alist binding names of arrays to anything.")
     (wirefal  "Fast alist binding names of wires (non-arrays) to anything.")
     (warnings vl-warninglist-p))
    :returns
    (mv (new-warnings vl-warninglist-p)
        (changedp     booleanp :rule-classes :type-prescription)
        (new-x        (and (vl-exprlist-p new-x)
                           (equal (len new-x) (len x)))))
    :verify-guards nil
    :measure (vl-exprlist-count x)
    :flag :list
    (b* (((when (atom x))
          (mv (ok) nil nil))
         ((mv warnings car-changedp car-prime)
          (vl-expr-resolve-indexing-aux (car x) arrfal wirefal warnings))
         ((mv warnings cdr-changedp cdr-prime)
          (vl-exprlist-resolve-indexing-aux (cdr x) arrfal wirefal warnings))
         (changedp (or car-changedp cdr-changedp))
         (new-x    (cons car-prime cdr-prime)))
      (mv warnings changedp new-x)))
  ///
  (defthm-vl-expr-resolve-indexing-aux-flag
    (defthm true-listp-of-vl-exprlist-resolve-indexing-aux
      (b* (((mv ?warnings ?changedp new-x)
            (vl-exprlist-resolve-indexing-aux x arrfal wirefal warnings)))
        (true-listp new-x))
      :rule-classes :type-prescription
      :flag :list)
    :skip-others t)

  (local (defthm-vl-expr-resolve-indexing-aux-flag
           ;; BOZO wtf, why do I need this?
           (defthm l0
             (b* (((mv ?warnings ?changedp new-x)
                   (vl-exprlist-resolve-indexing-aux x arrfal wirefal warnings)))
               (iff new-x (consp x)))
             :flag :list)
           :skip-others t))

  (verify-guards vl-expr-resolve-indexing-aux))

(defmacro def-vl-resolve-indexing (name &key body)
  (b* ((mksym-package-symbol (pkg-witness "VL"))
       (fn   (mksym name '-resolve-indexing))
       (type (mksym name '-p))
       (fix  (mksym name '-fix)))
    `(define ,fn
       :short ,(cat "Resolve @(':vl-index') operators throughout a @(see " (symbol-name type) ").")
       ((x        ,type)
        (arrfal   "Fast alist binding array names to whatever.")
        (wirefal  "Fast alist binding wire names to whatever.")
        (warnings vl-warninglist-p))
       :returns
       (mv (warnings vl-warninglist-p)
           (new-x    ,type))
       (b* ((x        (,fix x))
            (warnings (vl-warninglist-fix warnings)))
         ,body))))

(defmacro def-vl-resolve-indexing-list (name &key element)
  (b* ((mksym-package-symbol (pkg-witness "VL"))
       (fn      (mksym name '-resolve-indexing))
       (elem-fn (mksym element '-resolve-indexing))
       (type    (mksym name '-p))
       ;(fix     (mksym name '-fix))
       )
    `(define ,fn
       :short ,(cat "Resolve @(':vl-index') operators throughout a @(see " (symbol-name type) ").")
       ((x        ,type)
        (arrfal   "Fast alist binding array names to whatever.")
        (wirefal  "Fast alist binding wire names to whatever.")
        (warnings vl-warninglist-p))
       :returns
       (mv (warnings vl-warninglist-p)
           (new-x    ,type))
       (b* (((when (atom x))
             (mv (ok) nil))
            ((mv warnings car-prime) (,elem-fn (car x) arrfal wirefal warnings))
            ((mv warnings cdr-prime) (,fn (cdr x) arrfal wirefal warnings)))
         (mv warnings (cons car-prime cdr-prime)))
       ///
       (defthm ,(mksym 'true-listp-of- fn)
         (true-listp (mv-nth 1 (,fn x arrfal wirefal warnings)))
         :rule-classes :type-prescription)

       (defthm ,(mksym 'len-of- fn)
         (equal (len (mv-nth 1 (,fn x arrfal wirefal warnings)))
                (len x))))))

(def-vl-resolve-indexing vl-expr
  ;; Simple wrapper that just bundles up the changedp optimization.
  :body
  (b* (((mv warnings ?changedp new-x)
        (vl-expr-resolve-indexing-aux x arrfal wirefal warnings)))
    (mv warnings new-x)))

;; Simple wrapper that just bundles up the changedp optimization.
(def-vl-resolve-indexing-list vl-exprlist :element vl-expr)

(def-vl-resolve-indexing vl-maybe-expr
  :body
  (if (not x)
      (mv warnings nil)
    (vl-expr-resolve-indexing x arrfal wirefal warnings)))

(def-vl-resolve-indexing vl-assign
  :body
  (b* (((vl-assign x) x)
       ((mv warnings lvalue-prime)
        (vl-expr-resolve-indexing x.lvalue arrfal wirefal warnings))
       ((mv warnings expr-prime)
        (vl-expr-resolve-indexing x.expr arrfal wirefal warnings)))
    (mv warnings
        (change-vl-assign x
                          :lvalue lvalue-prime
                          :expr expr-prime))))

(def-vl-resolve-indexing-list vl-assignlist :element vl-assign)

(def-vl-resolve-indexing vl-plainarg
  :body (b* (((vl-plainarg x) x)
             ((unless x.expr)
              (mv warnings x))
             ((mv warnings expr-prime)
              (vl-expr-resolve-indexing x.expr arrfal wirefal warnings)))
            (mv warnings (change-vl-plainarg x :expr expr-prime))))

(def-vl-resolve-indexing-list vl-plainarglist :element vl-plainarg)

(def-vl-resolve-indexing vl-namedarg
  :body (b* (((vl-namedarg x) x)
             ((unless x.expr)
              (mv warnings x))
             ((mv warnings expr-prime)
              (vl-expr-resolve-indexing x.expr arrfal wirefal warnings)))
            (mv warnings (change-vl-namedarg x :expr expr-prime))))

(def-vl-resolve-indexing-list vl-namedarglist :element vl-namedarg)

(def-vl-resolve-indexing vl-arguments
  :body
  (vl-arguments-case x
    :named (b* (((mv warnings args-prime)
                 (vl-namedarglist-resolve-indexing x.args arrfal wirefal warnings)))
             (mv warnings (change-vl-arguments-named x :args args-prime)))
    :plain (b* (((mv warnings args-prime)
                 (vl-plainarglist-resolve-indexing x.args arrfal wirefal warnings)))
             (mv warnings (change-vl-arguments-plain x :args args-prime)))))

(def-vl-resolve-indexing vl-modinst
  :body (b* (((vl-modinst x) x)
             ((mv warnings args-prime)
              (vl-arguments-resolve-indexing x.portargs arrfal wirefal warnings)))
            (mv warnings (change-vl-modinst x :portargs args-prime))))

(def-vl-resolve-indexing-list vl-modinstlist :element vl-modinst)

(def-vl-resolve-indexing vl-gateinst
  :body (b* (((vl-gateinst x) x)
             ((mv warnings args-prime)
              (vl-plainarglist-resolve-indexing x.args arrfal wirefal warnings)))
            (mv warnings (change-vl-gateinst x :args args-prime))))

(def-vl-resolve-indexing-list vl-gateinstlist :element vl-gateinst)

(def-vl-resolve-indexing vl-delaycontrol
  :body (b* (((vl-delaycontrol x) x)
             ((mv warnings value-prime)
              (vl-expr-resolve-indexing x.value arrfal wirefal warnings)))
            (mv warnings (change-vl-delaycontrol x :value value-prime))))

(def-vl-resolve-indexing vl-evatom
  :body (b* (((vl-evatom x) x)
             ((mv warnings expr-prime)
              (vl-expr-resolve-indexing x.expr arrfal wirefal warnings)))
            (mv warnings (change-vl-evatom x :expr expr-prime))))

(def-vl-resolve-indexing-list vl-evatomlist :element vl-evatom)

(def-vl-resolve-indexing vl-eventcontrol
  :body (b* (((vl-eventcontrol x) x)
             ((mv warnings atoms-prime)
              (vl-evatomlist-resolve-indexing x.atoms arrfal wirefal warnings)))
            (mv warnings (change-vl-eventcontrol x :atoms atoms-prime))))

(def-vl-resolve-indexing vl-repeateventcontrol
  :body (b* (((vl-repeateventcontrol x) x)
             ((mv warnings expr-prime)
              (vl-expr-resolve-indexing x.expr arrfal wirefal warnings))
             ((mv warnings ctrl-prime)
              (vl-eventcontrol-resolve-indexing x.ctrl arrfal wirefal warnings))
             (x-prime (change-vl-repeateventcontrol x
                                                    :expr expr-prime
                                                    :ctrl ctrl-prime)))
            (mv warnings x-prime)))

(def-vl-resolve-indexing vl-delayoreventcontrol
  :body (case (tag x)
          (:vl-delaycontrol
           (vl-delaycontrol-resolve-indexing x arrfal wirefal warnings))
          (:vl-eventcontrol
           (vl-eventcontrol-resolve-indexing x arrfal wirefal warnings))
          (otherwise
           (vl-repeateventcontrol-resolve-indexing x arrfal wirefal warnings))))

(def-vl-resolve-indexing vl-maybe-delayoreventcontrol
  :body (if x
            (vl-delayoreventcontrol-resolve-indexing x arrfal wirefal warnings)
          (mv warnings nil)))

(defthm vl-maybe-delayoreventcontrol-resolve-indexing-under-iff
  (implies (force (vl-maybe-delayoreventcontrol-p x))
           (iff (mv-nth 1 (vl-maybe-delayoreventcontrol-resolve-indexing x arrfal wirefal warnings))
                x))
  :hints(("Goal"
          :in-theory (e/d (vl-maybe-delayoreventcontrol-resolve-indexing
                           vl-maybe-delayoreventcontrol-p)
                          (vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-resolve-indexing.new-x))
          :use ((:instance
                 vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-resolve-indexing.new-x)))))

(defines vl-stmt-resolve-indexing

  (define vl-stmt-resolve-indexing
    ((x        vl-stmt-p)
     (arrfal   "Fast alist binding names of arrays to anything.")
     (wirefal  "Fast alist binding names of wires (non-arrays) to anything.")
     (warnings vl-warninglist-p))
    :returns
    (mv (new-warnings vl-warninglist-p)
        (new-x        vl-stmt-p))
    :verify-guards nil
    :measure (vl-stmt-count x)
    :flag :stmt
    (b* ((x (vl-stmt-fix x))
         ((when (vl-atomicstmt-p x))
          (case (vl-stmt-kind x)
            (:vl-nullstmt
             (mv (ok) x))
            (:vl-assignstmt
             (b* (((vl-assignstmt x) x)
                  ((mv warnings lvalue-prime) (vl-expr-resolve-indexing x.lvalue arrfal wirefal warnings))
                  ((mv warnings expr-prime)   (vl-expr-resolve-indexing x.expr arrfal wirefal warnings))
                  ((mv warnings ctrl-prime)   (vl-maybe-delayoreventcontrol-resolve-indexing x.ctrl arrfal wirefal warnings))
                  (x-prime                    (change-vl-assignstmt x
                                                                    :lvalue lvalue-prime
                                                                    :expr expr-prime
                                                                    :ctrl ctrl-prime)))
               (mv (ok) x-prime)))
            (:vl-deassignstmt
             (b* (((vl-deassignstmt x) x)
                  ((mv warnings lvalue-prime) (vl-expr-resolve-indexing x.lvalue arrfal wirefal warnings))
                  (x-prime                    (change-vl-deassignstmt x :lvalue lvalue-prime)))
               (mv warnings x-prime)))
            (:vl-enablestmt
             (b* (((vl-enablestmt x) x)
                  ((mv warnings id-prime)   (vl-expr-resolve-indexing x.id arrfal wirefal warnings))
                  ((mv warnings args-prime) (vl-exprlist-resolve-indexing x.args arrfal wirefal warnings))
                  (x-prime                  (change-vl-enablestmt x
                                                                  :id id-prime
                                                                  :args args-prime)))
               (mv warnings x-prime)))
            (:vl-disablestmt
             (b* (((vl-disablestmt x) x)
                  ((mv warnings id-prime) (vl-expr-resolve-indexing x.id arrfal wirefal warnings))
                  (x-prime                (change-vl-disablestmt x :id id-prime)))
               (mv warnings x-prime)))
            (:vl-eventtriggerstmt
             (b* (((vl-eventtriggerstmt x) x)
                  ((mv warnings id-prime) (vl-expr-resolve-indexing x.id arrfal wirefal warnings))
                  (x-prime                (change-vl-eventtriggerstmt x :id id-prime)))
               (mv warnings x-prime)))
            (otherwise (mv (impossible) x))))
         ((mv warnings exprs-prime)
          (vl-exprlist-resolve-indexing (vl-compoundstmt->exprs x) arrfal wirefal warnings))
         ((mv warnings stmts-prime)
          (vl-stmtlist-resolve-indexing (vl-compoundstmt->stmts x) arrfal wirefal warnings))
         ((mv warnings ctrl-prime)
          (vl-maybe-delayoreventcontrol-resolve-indexing (vl-compoundstmt->ctrl x) arrfal wirefal warnings))
         (x-prime
          (change-vl-compoundstmt x
                                  :exprs exprs-prime
                                  :stmts stmts-prime
                                  :ctrl ctrl-prime)))
      (mv (ok) x-prime)))

  (define vl-stmtlist-resolve-indexing
    ((x        vl-stmtlist-p)
     (arrfal   "Fast alist binding names of arrays to anything.")
     (wirefal  "Fast alist binding names of wires (non-arrays) to anything.")
     (warnings vl-warninglist-p))
    :returns
    (mv (new-warnings vl-warninglist-p)
        (new-x        (and (vl-stmtlist-p new-x)
                           (equal (len new-x) (len x)))))
    :measure (vl-stmtlist-count x)
    :flag :list
    (b* (((when (atom x))
          (mv (ok) nil))
         ((mv warnings car-prime)
          (vl-stmt-resolve-indexing (car x) arrfal wirefal warnings))
         ((mv warnings cdr-prime)
          (vl-stmtlist-resolve-indexing (cdr x) arrfal wirefal warnings)))
      (mv warnings (cons car-prime cdr-prime))))
  ///
  (verify-guards vl-stmt-resolve-indexing)
  (deffixequiv-mutual vl-stmt-resolve-indexing))

(def-vl-resolve-indexing vl-always
  :body (b* (((vl-always x) x)
             ((mv warnings stmt-prime)
              (vl-stmt-resolve-indexing x.stmt arrfal wirefal warnings))
             (x-prime
              (change-vl-always x :stmt stmt-prime)))
            (mv warnings x-prime)))

(def-vl-resolve-indexing-list vl-alwayslist :element vl-always)

(def-vl-resolve-indexing vl-initial
  :body (b* (((vl-initial x) x)
             ((mv warnings stmt-prime)
              (vl-stmt-resolve-indexing x.stmt arrfal wirefal warnings))
             (x-prime
              (change-vl-initial x :stmt stmt-prime)))
            (mv warnings x-prime)))

(def-vl-resolve-indexing-list vl-initiallist :element vl-initial)

(def-vl-resolve-indexing vl-port
  :body (b* (((vl-port x) x)
             ((unless x.expr)
              (mv warnings x))
             ((mv warnings expr-prime)
              (vl-expr-resolve-indexing x.expr arrfal wirefal warnings))
             (x-prime
              (change-vl-port x :expr expr-prime)))
          (mv warnings x-prime)))

(def-vl-resolve-indexing-list vl-portlist :element vl-port)


(def-vl-resolve-indexing vl-fundecl
  :body
  (b* (((vl-fundecl x) x)

       ;; This is tricky because the function can have its own declarations.
       ((mv vardecls paramdecls)
        (vl-filter-blockitems x.decls))

       ;; Remove any locally declared names from the global arrfal/wirefal
       ;; we've been given.  In practice, shadowed-names should be short
       ;; because most functions are pretty simple and don't have more than a
       ;; few variables.  So, I'm not worried about just using
       ;; set-difference-equal calls, here.
       (shadowed-names
        (mergesort (append (vl-vardecllist->names vardecls)
                           (vl-paramdecllist->names paramdecls))))
       (visible-global-arrnames
        (set-difference-equal (alist-keys arrfal) shadowed-names))
       (visible-global-wirenames
        (set-difference-equal (alist-keys wirefal) shadowed-names))

       ;; It would probably be safe to turn indexing operations that are
       ;; selecting from most parameters and variables into bitselects.
       ((mv var-bitselects var-arrays ?var-others)
        (vl-vardecllist-filter-arrays vardecls nil nil nil))

       ;; The function's inputs are also okay to turn into bit selects, because
       ;; they can't be arrays.
       (innames         (vl-taskportlist->names x.inputs))

       (local-arrnames  (append-without-guard (vl-vardecllist->names var-arrays)
                                              visible-global-arrnames))
       (local-wirenames (append-without-guard (vl-vardecllist->names var-bitselects)
                                              innames
                                              visible-global-wirenames))
       (local-arrfal    (make-lookup-alist local-arrnames))
       (local-wirefal   (make-lookup-alist local-wirenames))
       ((mv warnings new-body)
        (vl-stmt-resolve-indexing x.body local-arrfal local-wirefal warnings))
       (- (fast-alist-free local-arrfal))
       (- (fast-alist-free local-wirefal))
       (new-x (change-vl-fundecl x :body new-body)))
    (mv warnings new-x)))

(def-vl-resolve-indexing-list vl-fundecllist :element vl-fundecl)

(define vl-module-resolve-indexing ((x vl-module-p))
  :returns (new-x vl-module-p)
  (b* ((x (vl-module-fix x))
       ((vl-module x) x)
       ((when (vl-module->hands-offp x))
        x)

       ((mv var-bitselects var-arrays ?var-others)
        (vl-vardecllist-filter-arrays x.vardecls nil nil nil))
       ((mv net-arrays net-wires)
        (vl-netdecllist-filter-arrays x.netdecls nil nil))

       (arr-names (append (vl-vardecllist->names var-arrays)
                          (vl-netdecllist->names net-arrays)))
       (wire-names (append (vl-vardecllist->names var-bitselects)
                           (vl-netdecllist->names net-wires)))

       (arrfal  (make-lookup-alist arr-names))
       (wirefal (make-lookup-alist wire-names))

       (warnings x.warnings)
       ((mv warnings ports)     (vl-portlist-resolve-indexing     x.ports arrfal wirefal warnings))
       ((mv warnings assigns)   (vl-assignlist-resolve-indexing   x.assigns arrfal wirefal warnings))
       ((mv warnings modinsts)  (vl-modinstlist-resolve-indexing  x.modinsts arrfal wirefal warnings))
       ((mv warnings gateinsts) (vl-gateinstlist-resolve-indexing x.gateinsts arrfal wirefal warnings))
       ((mv warnings alwayses)  (vl-alwayslist-resolve-indexing   x.alwayses arrfal wirefal warnings))
       ((mv warnings initials)  (vl-initiallist-resolve-indexing  x.initials arrfal wirefal warnings))
       ((mv warnings fundecls)  (vl-fundecllist-resolve-indexing  x.fundecls arrfal wirefal warnings))

       (- (fast-alist-free arrfal))
       (- (fast-alist-free wirefal))
       (new-x (change-vl-module x
                                :ports ports
                                :assigns assigns
                                :modinsts modinsts
                                :gateinsts gateinsts
                                :alwayses alwayses
                                :initials initials
                                :fundecls fundecls
                                :warnings warnings)))
    new-x))

(defprojection vl-modulelist-resolve-indexing ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-resolve-indexing x))

(define vl-design-resolve-indexing ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x)
       (new-mods (vl-modulelist-resolve-indexing x.mods)))
    (change-vl-design x :mods new-mods)))

