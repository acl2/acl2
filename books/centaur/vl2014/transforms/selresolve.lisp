; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL2014")
(include-book "../mlib/consteval")
(include-book "../mlib/stmt-tools")
(include-book "../mlib/blocks")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc selresolve
  :parents (transforms)
  :short "Simplification of select expressions, e.g., @('mywire[3-1]')."

  :long "<p>It is sometimes useful to statically evaluate indexes into wires
and registers, particularly to deal with the results of @(see
unparameterization).  For instance,</p>

@({
    wire a_msb = abus[width-1];
})

<p>May have been converted into something like:</p>

@({
    wire a_msb = abus[6-1];
})

<p>And in this case it is much nicer to statically resolve this and know that
we are talking about bit @('5') rather than to treat it as a dynamic bit
select.  It is also here that we deal with resolving multiplicities on
replication (multiple concatenation) operations.</p>

<p>See also the @(see rangeresolve) transform.</p>")

(local (xdoc::set-default-parents selresolve))

(define vl-op-selresolve
  :short "Non-recursively resolve indices on a single select, or the
multiplicity of a single multiconcat."

  ((op       "some operator being applied to @('args')" vl-op-p)
   (args     vl-exprlist-p)
   (ss       vl-scopestack-p)
   (warnings vl-warninglist-p)
   (context  "like @('op(args)'), for better warnings" vl-expr-p))
  :guard (or (not (vl-op-arity op))
             (equal (len args) (vl-op-arity op)))
  :returns (mv (warnings vl-warninglist-p)
               (new-args vl-exprlist-p))

  :long "<p>This is the core function for simplifying indices.  If @('op') is a
bit-select, part-select, or multiple concatenation, we try to evaluate
expressions within it, e.g., replacing @('6-1') with @('5'), which may have
arisen during the course of unparameterization.</p>"

  (b* ((op      (vl-op-fix op))
       (context (vl-expr-fix context))
       (args    (vl-exprlist-fix args)))
    (case op
      ((:vl-select-colon :vl-partselect-colon)
       (b* ((from   (vl-expr-fix (first args)))
            (index1 (vl-expr-fix (second args)))
            (index2 (vl-expr-fix (third args)))
            ((mv ok1 index1) (vl-consteval index1 ss))
            ((mv ok2 index2) (vl-consteval index2 ss))
            ((unless (and ok1 ok2))
             (mv (warn :type :vl-bad-expression
                       ;; BOZO need some context
                       :msg "Unable to safely resolve indices on part-select ~a0."
                       :args (list context))
                 args))
            ;; See also vl-rangeresolve.  We could create a part-select that
            ;; just uses the reduced index1 and index2 expressions.  But nobody
            ;; wants to look at things like foo[4'd3 : 4'd0].  So, instead of
            ;; keeping the size information, use vl-make-index, which can
            ;; usually build special indexes that the pretty-printer knows not
            ;; to put sizes on.
            (msb (vl-make-index (vl-resolved->val index1)))
            (lsb (vl-make-index (vl-resolved->val index2))))
         (mv (ok) (list from msb lsb))))

      ((:vl-select-pluscolon :vl-partselect-pluscolon
        :vl-select-minuscolon :vl-partselect-minuscolon)
       (b* ((from   (vl-expr-fix (first args)))
            (index1 (vl-expr-fix (second args)))
            (index2 (vl-expr-fix (third args)))
            ((mv ok1 index1) (vl-consteval index1 ss))
            ((mv ok2 index2) (vl-consteval index2 ss))
            ((unless ok2)
             (mv (warn :type :vl-bad-select
                       ;; BOZO need some context
                       :msg "Unable to safely resolve width on part-select ~a0."
                       :args (list context))
                 args))
            ;; See also vl-rangeresolve.  We could create a part-select that
            ;; just uses the reduced index1 and index2 expressions.  But nobody
            ;; wants to look at things like foo[4'd3 : 4'd0].  So, instead of
            ;; keeping the size information, use vl-make-index, which can
            ;; usually build special indexes that the pretty-printer knows not
            ;; to put sizes on.
            (new-idx1 (if ok1 (vl-make-index (vl-resolved->val index1)) index1))
            (new-idx2 (vl-make-index (vl-resolved->val index2))))
         (mv (ok) (list from new-idx1 new-idx2))))

      ((:vl-bitselect :vl-index)
       (b* ((from  (vl-expr-fix (first args)))
            (index (vl-expr-fix (second args)))
            ((mv ok index) (vl-consteval index ss))
            ((unless ok)
             (mv (warn :type :vl-dynamic-bsel
                       ;; BOZO need some context
                       :msg "Unable to safely resolve index on bit-select ~a0, ~
                             so a dynamic bit-select will have to be used ~
                             instead."
                       :args (list context))
                 args))
            ;; As in the partselect case.
            (atom (vl-make-index (vl-resolved->val index))))
         (mv (ok) (list from atom))))

      (:vl-multiconcat
       (b* ((mult        (vl-expr-fix (first args)))
            (kitty       (vl-expr-fix (second args)))
            ((mv ok val) (vl-consteval mult ss))
            ((unless ok)
             (mv (warn :type :vl-bad-expression
                       ;; BOZO need some context
                       :msg "Unable to safely resolve multiplicity on ~
                             multiconcat ~a0."
                       :args (list context))
                 args))
            ((when (>= (vl-resolved->val val) (expt 2 20)))
             ;; BOZO would be better to make this limit configurable.
             (mv (fatal :type :vl-replication-too-big
                        :msg "~a0: replicating expression with multiplicity ~
                              ~x1. That's crazy.   Causing a fatal warning to ~
                              try to prevent future transforms on this ~
                              module.  {~a2{~a3}}"
                        :args (list context (vl-resolved->val val)
                                    mult kitty))
                 args))
            ;; As in the partselect case.
            (atom (vl-make-index (vl-resolved->val val))))
         (mv (ok) (list atom kitty))))

      (otherwise
       (mv (ok) args))))
  ///
  (defthm len-of-vl-op-selresolve
    (implies (or (not (vl-op-arity op))
                 (equal (len args) (vl-op-arity op)))
             (b* (((mv ?warnings new-args) (vl-op-selresolve op args ss warnings context)))
               (equal (len new-args)
                      (len args))))))

(defines vl-expr-selresolve
  :short "Recursively simplify indices on selects and multiplicities on
multiconcats throughout an expression."

  (define vl-expr-selresolve
    ((x        vl-expr-p)
     (ss       vl-scopestack-p)
     (warnings vl-warninglist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    vl-expr-p))
    :verify-guards nil
    :measure (vl-expr-count x)
    (b* ((x (vl-expr-fix x))
         ((when (vl-fast-atom-p x))
          (mv (ok) x))
         (op                 (vl-nonatom->op x))
         ((mv warnings args) (vl-exprlist-selresolve (vl-nonatom->args x) ss warnings))
         ((mv warnings args) (vl-op-selresolve op args ss warnings x)))
      (mv warnings (change-vl-nonatom x :args args))))

  (define vl-exprlist-selresolve
    ((x        vl-exprlist-p)
     (ss       vl-scopestack-p)
     (warnings vl-warninglist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    (and (vl-exprlist-p new-x)
                                (equal (len new-x) (len x)))))
    :measure (vl-exprlist-count x)
    (b* (((when (atom x))
          (mv (ok) nil))
         ((mv warnings car-prime) (vl-expr-selresolve (car x) ss warnings))
         ((mv warnings cdr-prime) (vl-exprlist-selresolve (cdr x) ss warnings)))
      (mv warnings (cons car-prime cdr-prime))))
  ///
  (verify-guards vl-expr-selresolve)
  (deffixequiv-mutual vl-expr-selresolve))

(defmacro def-vl-selresolve (name &key body)
  (b* ((mksym-package-symbol (pkg-witness "VL2014"))
       (fn   (mksym name '-selresolve))
       (type (mksym name '-p))
       (fix  (mksym name '-fix)))
    `(define ,fn ((x ,type)
                  (ss vl-scopestack-p)
                  (warnings vl-warninglist-p))
       :returns (mv (warnings vl-warninglist-p)
                    (new-x    ,type))
       (declare (ignorable ss))
       (b* ((x        (,fix x))
            (warnings (vl-warninglist-fix warnings)))
         ,body))))

(defmacro def-vl-selresolve-list (name &key element)
  (b* ((mksym-package-symbol (pkg-witness "VL2014"))
       (fn      (mksym name '-selresolve))
       (type    (mksym name '-p))
       (elem-fn (mksym element '-selresolve)))
    `(define ,fn ((x ,type)
                  (ss vl-scopestack-p)
                  (warnings vl-warninglist-p))
       :returns (mv (warnings vl-warninglist-p)
                    (new-x    ,type))
       (b* (((when (atom x))
             (mv (ok) nil))
            ((mv warnings car-prime) (,elem-fn (car x) ss warnings))
            ((mv warnings cdr-prime) (,fn (cdr x) ss warnings)))
         (mv warnings (cons car-prime cdr-prime)))
       ///
       (defmvtypes ,fn (nil true-listp)))))

(def-vl-selresolve vl-maybe-expr
  :body (if (not x)
            (mv (ok) nil)
          (vl-expr-selresolve x ss warnings)))

(def-vl-selresolve vl-port
  :body (b* ((x (vl-port-fix x))
             ((when (eq (tag x) :vl-interfaceport))
              (mv warnings x))
             ((vl-regularport x) x)
             ((mv warnings expr) (vl-maybe-expr-selresolve x.expr ss warnings)))
          (mv warnings (change-vl-regularport x :expr expr))))

(def-vl-selresolve-list vl-portlist :element vl-port)

(def-vl-selresolve vl-assign
  :body (b* (((vl-assign x) x)
             ((mv warnings lvalue) (vl-expr-selresolve x.lvalue ss warnings))
             ((mv warnings expr)   (vl-expr-selresolve x.expr ss warnings)))
            (mv warnings (change-vl-assign x
                                           :lvalue lvalue
                                           :expr expr))))

(def-vl-selresolve-list vl-assignlist :element vl-assign)

(def-vl-selresolve vl-plainarg
  :body (b* (((vl-plainarg x) x)
             ((mv warnings expr) (vl-maybe-expr-selresolve x.expr ss warnings)))
          (mv warnings (change-vl-plainarg x :expr expr))))

(def-vl-selresolve-list vl-plainarglist :element vl-plainarg)

(def-vl-selresolve vl-namedarg
  :body (b* (((vl-namedarg x) x)
             ((mv warnings expr) (vl-maybe-expr-selresolve x.expr ss warnings)))
          (mv warnings (change-vl-namedarg x :expr expr))))

(def-vl-selresolve-list vl-namedarglist :element vl-namedarg)

(def-vl-selresolve vl-arguments
  :body (vl-arguments-case x
          :vl-arguments-named
          (b* (((mv warnings args) (vl-namedarglist-selresolve x.args ss warnings)))
            (mv warnings (change-vl-arguments-named x :args args)))
          :vl-arguments-plain
          (b* (((mv warnings args) (vl-plainarglist-selresolve x.args ss warnings)))
            (mv warnings (change-vl-arguments-plain x :args args)))))








(def-vl-selresolve vl-paramvalue
  :body (b* ((x (vl-paramvalue-fix x)))
          (vl-paramvalue-case x
            :expr (vl-expr-selresolve x ss warnings)
            :datatype
            ;; BOZO should probably go into the datatype and resolve selects there, too.
            (mv warnings x))))

(def-vl-selresolve-list vl-paramvaluelist :element vl-paramvalue)

(def-vl-selresolve vl-maybe-paramvalue
  :body (if x
            (vl-paramvalue-selresolve x ss warnings)
          (mv warnings nil)))

(def-vl-selresolve vl-namedparamvalue
  :body (b* (((vl-namedparamvalue x) x)
             ((mv warnings value) (vl-maybe-paramvalue-selresolve x.value ss warnings)))
          (mv warnings (change-vl-namedparamvalue x :value value))))

(def-vl-selresolve-list vl-namedparamvaluelist :element vl-namedparamvalue)

(def-vl-selresolve vl-paramargs
  :body (vl-paramargs-case x
          :vl-paramargs-named
          (b* (((mv warnings args) (vl-namedparamvaluelist-selresolve x.args ss warnings)))
            (mv warnings (change-vl-paramargs-named x :args args)))
          :vl-paramargs-plain
          (b* (((mv warnings args) (vl-paramvaluelist-selresolve x.args ss warnings)))
            (mv warnings (change-vl-paramargs-plain x :args args)))))

(def-vl-selresolve vl-modinst
  :body (b* (((vl-modinst x) x)
             ((mv warnings paramargs) (vl-paramargs-selresolve x.paramargs ss warnings))
             ((mv warnings portargs)  (vl-arguments-selresolve x.portargs ss warnings)))
          (mv warnings (change-vl-modinst x
                                          :paramargs paramargs
                                          :portargs  portargs))))

(def-vl-selresolve-list vl-modinstlist :element vl-modinst)

(def-vl-selresolve vl-gateinst
  :body (b* (((vl-gateinst x) x)
             ((mv warnings args) (vl-plainarglist-selresolve x.args ss warnings)))
          (mv warnings (change-vl-gateinst x :args args))))

(def-vl-selresolve-list vl-gateinstlist :element vl-gateinst)

(def-vl-selresolve vl-delaycontrol
  :body (b* (((vl-delaycontrol x) x)
             ((mv warnings value) (vl-expr-selresolve x.value ss warnings)))
          (mv warnings (change-vl-delaycontrol x :value value))))

(def-vl-selresolve vl-evatom
  :body (b* (((vl-evatom x) x)
             ((mv warnings expr-prime) (vl-expr-selresolve x.expr ss warnings)))
          (mv warnings (change-vl-evatom x :expr expr-prime))))

(def-vl-selresolve-list vl-evatomlist :element vl-evatom)

(def-vl-selresolve vl-eventcontrol
  :body (b* (((vl-eventcontrol x) x)
             ((mv warnings atoms) (vl-evatomlist-selresolve x.atoms ss warnings)))
          (mv warnings (change-vl-eventcontrol x :atoms atoms))))

(def-vl-selresolve vl-repeateventcontrol
  :body (b* (((vl-repeateventcontrol x) x)
             ((mv warnings expr) (vl-expr-selresolve x.expr ss warnings))
             ((mv warnings ctrl) (vl-eventcontrol-selresolve x.ctrl ss warnings)))
          (mv warnings (change-vl-repeateventcontrol x
                                                     :expr expr
                                                     :ctrl ctrl))))

(def-vl-selresolve vl-delayoreventcontrol
  :body (case (tag x)
          (:vl-delaycontrol (vl-delaycontrol-selresolve x ss warnings))
          (:vl-eventcontrol (vl-eventcontrol-selresolve x ss warnings))
          (otherwise        (vl-repeateventcontrol-selresolve x ss warnings))))

(def-vl-selresolve vl-maybe-delayoreventcontrol
  :body (if x
            (vl-delayoreventcontrol-selresolve x ss warnings)
          (mv (ok) nil)))

(defthm vl-maybe-delayoreventcontrol-selresolve-under-iff
  (b* (((mv ?warnings new-x)
        (vl-maybe-delayoreventcontrol-selresolve x ss warnings)))
    (iff new-x x))
  :hints(("Goal"
          :in-theory (e/d (vl-maybe-delayoreventcontrol-selresolve
                           vl-maybe-delayoreventcontrol-p)
                          (vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-selresolve.new-x))
          :use ((:instance vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-selresolve.new-x)))))

(defines vl-stmt-selresolve

  (define vl-stmt-selresolve
    ((x        vl-stmt-p)
     (ss       vl-scopestack-p)
     (warnings vl-warninglist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    vl-stmt-p))
    :verify-guards nil
    :measure (vl-stmt-count x)
    (b* ((x (vl-stmt-fix x))
         ((when (vl-atomicstmt-p x))
          (case (vl-stmt-kind x)
            (:vl-nullstmt
             (mv (ok) x))
            (:vl-assignstmt
             (b* (((vl-assignstmt x) x)
                  ((mv warnings lvalue) (vl-expr-selresolve x.lvalue ss warnings))
                  ((mv warnings expr)   (vl-expr-selresolve x.expr ss warnings))
                  ((mv warnings ctrl)   (vl-maybe-delayoreventcontrol-selresolve x.ctrl ss warnings)))
               (mv warnings (change-vl-assignstmt x
                                                  :lvalue lvalue
                                                  :expr   expr
                                                  :ctrl   ctrl))))
            (:vl-deassignstmt
             (b* (((vl-deassignstmt x) x)
                  ((mv warnings lvalue) (vl-expr-selresolve x.lvalue ss warnings)))
               (mv warnings (change-vl-deassignstmt x :lvalue lvalue))))
            (:vl-enablestmt
             (b* (((vl-enablestmt x) x)
                  ((mv warnings id)   (vl-expr-selresolve x.id ss warnings))
                  ((mv warnings args) (vl-exprlist-selresolve x.args ss warnings)))
               (mv warnings (change-vl-enablestmt x
                                                  :id   id
                                                  :args args))))
            (:vl-disablestmt
             (b* (((vl-disablestmt x) x)
                  ((mv warnings id) (vl-expr-selresolve x.id ss warnings)))
               (mv warnings (change-vl-disablestmt x :id id))))
            (:vl-returnstmt
             (b* (((vl-returnstmt x) x)
                  ((mv warnings val)
                   (if x.val
                       (vl-expr-selresolve x.val ss warnings)
                     (mv warnings x.val))))
               (mv (ok) (change-vl-returnstmt x :val val))))
            (:vl-eventtriggerstmt
             (b* (((vl-eventtriggerstmt x) x)
                  ((mv warnings id) (vl-expr-selresolve x.id ss warnings)))
               (mv warnings (change-vl-eventtriggerstmt x :id id))))
            (otherwise
             (mv (impossible) x))))
         ((mv warnings exprs) (vl-exprlist-selresolve (vl-compoundstmt->exprs x) ss warnings))
         ((mv warnings stmts) (vl-stmtlist-selresolve (vl-compoundstmt->stmts x) ss warnings))
         ((mv warnings ctrl)  (vl-maybe-delayoreventcontrol-selresolve (vl-compoundstmt->ctrl x) ss warnings)))
      (mv warnings (change-vl-compoundstmt x
                                           :exprs exprs
                                           :stmts stmts
                                           :ctrl ctrl))))

  (define vl-stmtlist-selresolve
    ((x        vl-stmtlist-p)
     (ss       vl-scopestack-p)
     (warnings vl-warninglist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    (and (vl-stmtlist-p new-x)
                                (equal (len new-x) (len x)))))
    :measure (vl-stmtlist-count x)
    (b* (((when (atom x))
          (mv (ok) nil))
         ((mv warnings car-prime) (vl-stmt-selresolve (car x) ss warnings))
         ((mv warnings cdr-prime) (vl-stmtlist-selresolve (cdr x) ss warnings)))
      (mv warnings (cons car-prime cdr-prime))))
  ///
  (verify-guards vl-stmt-selresolve)
  (deffixequiv-mutual vl-stmt-selresolve))

(def-vl-selresolve vl-always
  :body (b* (((vl-always x) x)
             ((mv warnings stmt) (vl-stmt-selresolve x.stmt ss warnings)))
          (mv warnings (change-vl-always x :stmt stmt))))

(def-vl-selresolve-list vl-alwayslist :element vl-always)

(def-vl-selresolve vl-initial
  :body (b* (((vl-initial x) x)
             ((mv warnings stmt) (vl-stmt-selresolve x.stmt ss warnings)))
          (mv warnings (change-vl-initial x :stmt stmt))))

(def-vl-selresolve-list vl-initiallist :element vl-initial)

(def-vl-selresolve vl-fundecl
  :body (b* (((vl-fundecl x) x)
             ((mv warnings body) (vl-stmt-selresolve x.body ss warnings)))
          (mv warnings (change-vl-fundecl x :body body))))

(def-vl-selresolve-list vl-fundecllist :element vl-fundecl)

(def-genblob-transform vl-genblob-selresolve ((ss vl-scopestack-p)
                                                (warnings vl-warninglist-p))
  :returns ((warnings vl-warninglist-p))
  ;; :verify-guards nil
  (b* (((vl-genblob x) x)
       (ss (vl-scopestack-push (vl-genblob-fix x) ss))
       ((mv warnings assigns)   (vl-assignlist-selresolve   x.assigns ss   warnings))
       ((mv warnings modinsts)  (vl-modinstlist-selresolve  x.modinsts ss  warnings))
       ((mv warnings gateinsts) (vl-gateinstlist-selresolve x.gateinsts ss warnings))
       ((mv warnings alwayses)  (vl-alwayslist-selresolve   x.alwayses ss  warnings))
       ((mv warnings initials)  (vl-initiallist-selresolve  x.initials ss  warnings))
       ((mv warnings fundecls)  (vl-fundecllist-selresolve  x.fundecls ss  warnings))

       ((mv warnings generates)  (vl-generates-selresolve  x.generates ss  warnings))
       ((mv warnings ports)      (vl-portlist-selresolve     x.ports ss     warnings)))

    (mv warnings
        (change-vl-genblob
         x
         :ports     ports
         :assigns   assigns
         :modinsts  modinsts
         :gateinsts gateinsts
         :alwayses  alwayses
         :initials  initials
         :fundecls  fundecls
         :generates generates)))
  :apply-to-generates vl-generates-selresolve)



(define vl-module-selresolve ((x vl-module-p) (ss vl-scopestack-p))
  :returns (new-x vl-module-p)
  (b* (((vl-module x))
       (genblob (vl-module->genblob x))
       ((mv warnings new-genblob) (vl-genblob-selresolve genblob ss x.warnings))
       (x-warn (change-vl-module x :warnings warnings)))
    (vl-genblob->module new-genblob x-warn)))

(defprojection vl-modulelist-selresolve ((x vl-modulelist-p) (ss vl-scopestack-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-selresolve x ss))

(define vl-design-selresolve ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x)
       (ss (vl-scopestack-init x))
       (new-mods (vl-modulelist-selresolve x.mods ss)))
    (vl-scopestacks-free)
    (change-vl-design x :mods new-mods)))



