; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "VL")
(include-book "../mlib/expr-tools")
(include-book "../mlib/stmt-tools")
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
      (:vl-partselect-colon
       (b* ((from   (vl-expr-fix (first args)))
            (index1 (vl-expr-fix (second args)))
            (index2 (vl-expr-fix (third args)))
            (val1   (vl-constexpr-reduce index1))
            (val2   (vl-constexpr-reduce index2))
            ((unless (and val1 val2))
             (mv (warn :type :vl-bad-expression
                       ;; BOZO need some context
                       :msg "Unable to safely resolve indices on part-select ~a0."
                       :args (list context))
                 args))
            (msb (hons-copy (make-vl-atom
                             :guts (make-vl-constint :origwidth 32
                                                     :origtype :vl-signed
                                                     :value val1
                                                     :wasunsized t))))
            (lsb (hons-copy (make-vl-atom
                             :guts (make-vl-constint :origwidth 32
                                                     :origtype :vl-signed
                                                     :value val2
                                                     :wasunsized t)))))
         (mv (ok) (list from msb lsb))))

      (:vl-bitselect
       (b* ((from  (vl-expr-fix (first args)))
            (index (vl-expr-fix (second args)))
            (val   (vl-constexpr-reduce index))
            ((unless val)
             (mv (warn :type :vl-dynamic-bsel
                       ;; BOZO need some context
                       :msg "Unable to safely resolve index on bit-select ~a0, ~
                             so a dynamic bit-select will have to be used ~
                             instead."
                       :args (list context))
                 args))
            (atom (hons-copy (make-vl-atom
                              :guts (make-vl-constint :origwidth 32
                                                      :origtype :vl-signed
                                                      :value val
                                                      :wasunsized t)))))
         (mv (ok) (list from atom))))

      (:vl-multiconcat
       (b* ((mult   (vl-expr-fix (first args)))
            (kitty  (vl-expr-fix (second args)))
            (val    (vl-constexpr-reduce mult))
            ((unless val)
             (mv (warn :type :vl-bad-expression
                       ;; BOZO need some context
                       :msg "Unable to safely resolve multiplicity on ~
                             multiconcat ~a0."
                       :args (list context))
                 args))
            (atom (hons-copy (make-vl-atom
                              :guts (make-vl-constint :origwidth 32
                                                      :origtype :vl-signed
                                                      :value val
                                                      :wasunsized t)))))
         (mv (ok) (list atom kitty))))

      (otherwise
       (mv (ok) args))))
  ///
  (defthm len-of-vl-op-selresolve
    (implies (or (not (vl-op-arity op))
                 (equal (len args) (vl-op-arity op)))
             (b* (((mv ?warnings new-args) (vl-op-selresolve op args warnings context)))
               (equal (len new-args)
                      (len args))))))

(defines vl-expr-selresolve
  :short "Recursively simplify indices on selects and multiplicities on
multiconcats throughout an expression."

  (define vl-expr-selresolve
    ((x        vl-expr-p)
     (warnings vl-warninglist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    vl-expr-p))
    :verify-guards nil
    :measure (vl-expr-count x)
    (b* ((x (vl-expr-fix x))
         ((when (vl-fast-atom-p x))
          (mv (ok) x))
         (op                 (vl-nonatom->op x))
         ((mv warnings args) (vl-exprlist-selresolve (vl-nonatom->args x) warnings))
         ((mv warnings args) (vl-op-selresolve op args warnings x)))
      (mv warnings (change-vl-nonatom x :args args))))

  (define vl-exprlist-selresolve
    ((x        vl-exprlist-p)
     (warnings vl-warninglist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    (and (vl-exprlist-p new-x)
                                (equal (len new-x) (len x)))))
    :measure (vl-exprlist-count x)
    (b* (((when (atom x))
          (mv (ok) nil))
         ((mv warnings car-prime) (vl-expr-selresolve (car x) warnings))
         ((mv warnings cdr-prime) (vl-exprlist-selresolve (cdr x) warnings)))
      (mv warnings (cons car-prime cdr-prime))))
  ///
  (verify-guards vl-expr-selresolve)
  (deffixequiv-mutual vl-expr-selresolve))

(defmacro def-vl-selresolve (name &key body)
  (b* ((mksym-package-symbol (pkg-witness "VL"))
       (fn   (mksym name '-selresolve))
       (type (mksym name '-p))
       (fix  (mksym name '-fix)))
    `(define ,fn ((x ,type)
                    (warnings vl-warninglist-p))
       :returns (mv (warnings vl-warninglist-p)
                    (new-x    ,type))
       (b* ((x        (,fix x))
            (warnings (vl-warninglist-fix warnings)))
         ,body))))

(defmacro def-vl-selresolve-list (name &key element)
  (b* ((mksym-package-symbol (pkg-witness "VL"))
       (fn      (mksym name '-selresolve))
       (type    (mksym name '-p))
       (elem-fn (mksym element '-selresolve)))
    `(define ,fn ((x ,type)
                    (warnings vl-warninglist-p))
       :returns (mv (warnings vl-warninglist-p)
                    (new-x    ,type))
       (b* (((when (atom x))
             (mv (ok) nil))
            ((mv warnings car-prime) (,elem-fn (car x) warnings))
            ((mv warnings cdr-prime) (,fn (cdr x) warnings)))
         (mv warnings (cons car-prime cdr-prime)))
       ///
       (defmvtypes ,fn (nil true-listp)))))

(def-vl-selresolve vl-maybe-expr
  :body (if (not x)
            (mv (ok) nil)
          (vl-expr-selresolve x warnings)))

(def-vl-selresolve vl-port
  :body (b* (((vl-port x) x)
             ((mv warnings expr) (vl-maybe-expr-selresolve x.expr warnings)))
          (mv warnings (change-vl-port x :expr expr))))

(def-vl-selresolve-list vl-portlist :element vl-port)

(def-vl-selresolve vl-assign
  :body (b* (((vl-assign x) x)
             ((mv warnings lvalue) (vl-expr-selresolve x.lvalue warnings))
             ((mv warnings expr)   (vl-expr-selresolve x.expr warnings)))
            (mv warnings (change-vl-assign x
                                           :lvalue lvalue
                                           :expr expr))))

(def-vl-selresolve-list vl-assignlist :element vl-assign)

(def-vl-selresolve vl-plainarg
  :body (b* (((vl-plainarg x) x)
             ((mv warnings expr) (vl-maybe-expr-selresolve x.expr warnings)))
          (mv warnings (change-vl-plainarg x :expr expr))))

(def-vl-selresolve-list vl-plainarglist :element vl-plainarg)

(def-vl-selresolve vl-namedarg
  :body (b* (((vl-namedarg x) x)
             ((mv warnings expr) (vl-maybe-expr-selresolve x.expr warnings)))
          (mv warnings (change-vl-namedarg x :expr expr))))

(def-vl-selresolve-list vl-namedarglist :element vl-namedarg)

(def-vl-selresolve vl-arguments
  :body (vl-arguments-case x
          :named (b* (((mv warnings args) (vl-namedarglist-selresolve x.args warnings)))
                   (mv warnings (change-vl-arguments-named x :args args)))
          :plain (b* (((mv warnings args) (vl-plainarglist-selresolve x.args warnings)))
                   (mv warnings (change-vl-arguments-plain x :args args)))))

(def-vl-selresolve vl-modinst
  :body (b* (((vl-modinst x) x)
             ((mv warnings paramargs) (vl-arguments-selresolve x.paramargs warnings))
             ((mv warnings portargs)  (vl-arguments-selresolve x.portargs warnings)))
          (mv warnings (change-vl-modinst x
                                          :paramargs paramargs
                                          :portargs  portargs))))

(def-vl-selresolve-list vl-modinstlist :element vl-modinst)

(def-vl-selresolve vl-gateinst
  :body (b* (((vl-gateinst x) x)
             ((mv warnings args) (vl-plainarglist-selresolve x.args warnings)))
          (mv warnings (change-vl-gateinst x :args args))))

(def-vl-selresolve-list vl-gateinstlist :element vl-gateinst)

(def-vl-selresolve vl-delaycontrol
  :body (b* (((vl-delaycontrol x) x)
             ((mv warnings value) (vl-expr-selresolve x.value warnings)))
          (mv warnings (change-vl-delaycontrol x :value value))))

(def-vl-selresolve vl-evatom
  :body (b* (((vl-evatom x) x)
             ((mv warnings expr-prime) (vl-expr-selresolve x.expr warnings)))
          (mv warnings (change-vl-evatom x :expr expr-prime))))

(def-vl-selresolve-list vl-evatomlist :element vl-evatom)

(def-vl-selresolve vl-eventcontrol
  :body (b* (((vl-eventcontrol x) x)
             ((mv warnings atoms) (vl-evatomlist-selresolve x.atoms warnings)))
          (mv warnings (change-vl-eventcontrol x :atoms atoms))))

(def-vl-selresolve vl-repeateventcontrol
  :body (b* (((vl-repeateventcontrol x) x)
             ((mv warnings expr) (vl-expr-selresolve x.expr warnings))
             ((mv warnings ctrl) (vl-eventcontrol-selresolve x.ctrl warnings)))
          (mv warnings (change-vl-repeateventcontrol x
                                                     :expr expr
                                                     :ctrl ctrl))))

(def-vl-selresolve vl-delayoreventcontrol
  :body (case (tag x)
          (:vl-delaycontrol (vl-delaycontrol-selresolve x warnings))
          (:vl-eventcontrol (vl-eventcontrol-selresolve x warnings))
          (otherwise        (vl-repeateventcontrol-selresolve x warnings))))

(def-vl-selresolve vl-maybe-delayoreventcontrol
  :body (if x
            (vl-delayoreventcontrol-selresolve x warnings)
          (mv (ok) nil)))

(defthm vl-maybe-delayoreventcontrol-selresolve-under-iff
  (b* (((mv ?warnings new-x)
        (vl-maybe-delayoreventcontrol-selresolve x warnings)))
    (iff new-x x))
  :hints(("Goal"
          :in-theory (e/d (vl-maybe-delayoreventcontrol-selresolve
                           vl-maybe-delayoreventcontrol-p)
                          (vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-selresolve.new-x))
          :use ((:instance vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-selresolve.new-x)))))

(defines vl-stmt-selresolve

  (define vl-stmt-selresolve
    ((x        vl-stmt-p)
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
                  ((mv warnings lvalue) (vl-expr-selresolve x.lvalue warnings))
                  ((mv warnings expr)   (vl-expr-selresolve x.expr warnings))
                  ((mv warnings ctrl)   (vl-maybe-delayoreventcontrol-selresolve x.ctrl warnings)))
               (mv warnings (change-vl-assignstmt x
                                                  :lvalue lvalue
                                                  :expr   expr
                                                  :ctrl   ctrl))))
            (:vl-deassignstmt
             (b* (((vl-deassignstmt x) x)
                  ((mv warnings lvalue) (vl-expr-selresolve x.lvalue warnings)))
               (mv warnings (change-vl-deassignstmt x :lvalue lvalue))))
            (:vl-enablestmt
             (b* (((vl-enablestmt x) x)
                  ((mv warnings id)   (vl-expr-selresolve x.id warnings))
                  ((mv warnings args) (vl-exprlist-selresolve x.args warnings)))
               (mv warnings (change-vl-enablestmt x
                                                  :id   id
                                                  :args args))))
            (:vl-disablestmt
             (b* (((vl-disablestmt x) x)
                  ((mv warnings id) (vl-expr-selresolve x.id warnings)))
               (mv warnings (change-vl-disablestmt x :id id))))
            (:vl-eventtriggerstmt
             (b* (((vl-eventtriggerstmt x) x)
                  ((mv warnings id) (vl-expr-selresolve x.id warnings)))
               (mv warnings (change-vl-eventtriggerstmt x :id id))))
            (otherwise
             (mv (impossible) x))))
         ((mv warnings exprs) (vl-exprlist-selresolve (vl-compoundstmt->exprs x) warnings))
         ((mv warnings stmts) (vl-stmtlist-selresolve (vl-compoundstmt->stmts x) warnings))
         ((mv warnings ctrl)  (vl-maybe-delayoreventcontrol-selresolve (vl-compoundstmt->ctrl x) warnings)))
      (mv warnings (change-vl-compoundstmt x
                                           :exprs exprs
                                           :stmts stmts
                                           :ctrl ctrl))))

  (define vl-stmtlist-selresolve
    ((x        vl-stmtlist-p)
     (warnings vl-warninglist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    (and (vl-stmtlist-p new-x)
                                (equal (len new-x) (len x)))))
    :measure (vl-stmtlist-count x)
    (b* (((when (atom x))
          (mv (ok) nil))
         ((mv warnings car-prime) (vl-stmt-selresolve (car x) warnings))
         ((mv warnings cdr-prime) (vl-stmtlist-selresolve (cdr x) warnings)))
      (mv warnings (cons car-prime cdr-prime))))
  ///
  (verify-guards vl-stmt-selresolve)
  (deffixequiv-mutual vl-stmt-selresolve))

(def-vl-selresolve vl-always
  :body (b* (((vl-always x) x)
             ((mv warnings stmt) (vl-stmt-selresolve x.stmt warnings)))
          (mv warnings (change-vl-always x :stmt stmt))))

(def-vl-selresolve-list vl-alwayslist :element vl-always)

(def-vl-selresolve vl-initial
  :body (b* (((vl-initial x) x)
             ((mv warnings stmt) (vl-stmt-selresolve x.stmt warnings)))
          (mv warnings (change-vl-initial x :stmt stmt))))

(def-vl-selresolve-list vl-initiallist :element vl-initial)

(def-vl-selresolve vl-fundecl
  :body (b* (((vl-fundecl x) x)
             ((mv warnings body) (vl-stmt-selresolve x.body warnings)))
          (mv warnings (change-vl-fundecl x :body body))))

(def-vl-selresolve-list vl-fundecllist :element vl-fundecl)

(define vl-module-selresolve ((x vl-module-p))
  :returns (new-x vl-module-p)
  (b* (((vl-module x) x)
       ((when (vl-module->hands-offp x))
        (vl-module-fix x))
       (warnings                x.warnings)
       ((mv warnings ports)     (vl-portlist-selresolve     x.ports     warnings))
       ((mv warnings assigns)   (vl-assignlist-selresolve   x.assigns   warnings))
       ((mv warnings modinsts)  (vl-modinstlist-selresolve  x.modinsts  warnings))
       ((mv warnings gateinsts) (vl-gateinstlist-selresolve x.gateinsts warnings))
       ((mv warnings alwayses)  (vl-alwayslist-selresolve   x.alwayses  warnings))
       ((mv warnings initials)  (vl-initiallist-selresolve  x.initials  warnings))
       ((mv warnings fundecls)  (vl-fundecllist-selresolve  x.fundecls  warnings)))
      (change-vl-module x
                        :ports     ports
                        :warnings  warnings
                        :assigns   assigns
                        :modinsts  modinsts
                        :gateinsts gateinsts
                        :alwayses  alwayses
                        :initials  initials
                        :fundecls  fundecls)))

(defprojection vl-modulelist-selresolve ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-selresolve x))

(define vl-design-selresolve ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x)
       (new-mods (vl-modulelist-selresolve x.mods)))
    (change-vl-design x :mods new-mods)))
