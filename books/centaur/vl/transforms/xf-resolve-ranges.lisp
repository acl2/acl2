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
(include-book "../mlib/range-tools")
(include-book "../mlib/stmt-tools")
(local (include-book "../util/arithmetic"))

(defxdoc rangeresolve
  :parents (transforms)
  :short "Simplification of ranges, e.g., @('reg [6-1:0]')"

  :long "<p>We sometimes need to statically evaluate expressions until a
constant is reached, particularly to deal with the results of @(see
unparameterization).  For instance, </p>

@({
   reg [width-1:0] r ;
})

<p>May have been converted into something like:</p>

@({
    reg [6-1:0] r ;
})

<p>And so in order to determine what the size of @('r') is, we need to evaluate
these expressions.  This leads us to a precarious place, because normally in
order to evaluate a Verilog expression, we need to have computed its size and
the sizes of all its subexpressions.  And so, we want to restrict ourselves to
a subset of the Verilog expressions which we can confidently resolve to a
constant without having their widths available.</p>

<p>In short, we carve out a very small set of Verilog expressions which includes
only:</p>

<ul>
 <li>Plain decimal integers (which are both unsized and signed)</li>
 <li>Addition, subtraction, and multiplication</li>
</ul>

<p>In practice, at Centaur we don't even need this much -- subtraction would do
just fine.  But it was so easy to add the others that I went ahead and did it
anyway, on the off chance that some day we will want @('2 * width') or @('width
+ 1') or something along those lines.</p>

<p>These constant expressions occur in net and register declarations, and also
may occur in expressions such as bit-selects, part-selects, and multiple
concatenations.</p>")

(local (xdoc::set-default-parents rangeresolve))

(define vl-rangeexpr-reduce
  :short "An evaluator for a small set of \"constant expressions\" in Verilog."
  ((x vl-expr-p))
  :returns (value? "An unsigned 31-bit integer (i.e., a positive signed 32-bit
                    integer) on success, or @('nil') on failure."
                   maybe-natp :rule-classes :type-prescription)

  :long "<p>This is a very careful, limited evaluator.  It checks, after every
computation, that the result is in [0, 2^31).  This is the minimum size of
\"integer\" for Verilog implementations, which is the size that plain decimal
integer literals are supposed to have.  If we ever leave that range, we just
fail to evaluate the expression.</p>

<p>Note that in general it is <b>not safe</b> to call this function on
arbitrary Verilog expressions to do constant folding because the size of the
left-hand side can influence the widths at which the interior computations are
to be done.  However, it is safe to use this inside of range expressions,
because there is no left-hand side to provide us a context.</p>

<p>BOZO is it really unsafe?  At worst the left-hand side is bigger than 31
bits, and we end up with a larger context, right?  But can that actually hurt
us in some way, if the result of every operation stays in bounds?  I don't
think it can.</p>"

  (cond ((mbe :logic (not (consp x))
              :exec nil)
         ;; Stupid termination hack.
         nil)

        ((vl-fast-atom-p x)
         ;; The following is quite restrictive.  We only permit integer
         ;; literals which were have the :wasunsized attribute set and are
         ;; signed.  Such literals would arise in Verilog by being written as
         ;; plain decimal integers like 5, or as unbased, signed integers in
         ;; other bases such as 'shFFF and so on.
         ;;
         ;; The reason I am doing this is becuase these numbers are
         ;; "predictable" in that they are to be interpreted as n-bit
         ;; constants, where n is at least 32 bits, and I do not want any
         ;; confusion about which width we are operating in.
         ;;
         ;; If you want to extend this, you need to be very careful to
         ;; understand how the signedness rules and width rules are going to
         ;; apply.  In particular, the calculations below in the non-atom case
         ;; are currently relying upon the fact that everything is in the
         ;; signed, 32-bit world.
         (let ((guts (vl-atom->guts x)))
           (and (vl-fast-constint-p guts)
                (eq (vl-constint->origtype guts) :vl-signed)
                (eql (vl-constint->origwidth guts) 32)
                (vl-constint->wasunsized guts)
                (< (vl-constint->value guts) (expt 2 31))
                ;; This lnfix is a stupid hack that gives us an unconditional
                ;; type prescription rule.  We "know" that the value is an
                ;; natural nubmer as long as x is indeed an expression.
                (lnfix (vl-constint->value guts)))))

        (t
         ;; Be very careful if you decide to try to extend this to support
         ;; other operations!  In particular, you should understand the
         ;; signedness rules and how operations like comparisons will take you
         ;; out of the world of signed arithmetic.
         (case (vl-nonatom->op x)
           (:vl-unary-plus
            (vl-rangeexpr-reduce (first (vl-nonatom->args x))))
           (:vl-binary-plus
            (b* ((arg1 (vl-rangeexpr-reduce (first (vl-nonatom->args x))))
                 (arg2 (vl-rangeexpr-reduce (second (vl-nonatom->args x)))))
              (and arg1
                   arg2
                   (< (+ arg1 arg2) (expt 2 31))
                   (+ arg1 arg2))))
           (:vl-binary-minus
            (b* ((arg1 (vl-rangeexpr-reduce (first (vl-nonatom->args x))))
                 (arg2 (vl-rangeexpr-reduce (second (vl-nonatom->args x)))))
              (and arg1
                   arg2
                   (<= 0 (- arg1 arg2))
                   (- arg1 arg2))))
           (:vl-binary-times
            (b* ((arg1 (vl-rangeexpr-reduce (first (vl-nonatom->args x))))
                 (arg2 (vl-rangeexpr-reduce (second (vl-nonatom->args x)))))
              (and arg1
                   arg2
                   (< (* arg1 arg2) (expt 2 31))
                   (* arg1 arg2))))
           (:vl-binary-shl
            (b* ((arg1 (vl-rangeexpr-reduce (first (vl-nonatom->args x))))
                 (arg2 (vl-rangeexpr-reduce (second (vl-nonatom->args x)))))
              (and arg1
                   arg2
                   (< (ash arg1 arg2) (expt 2 31))
                   (ash arg1 arg2))))
           (t
            ;; Some unsupported operation -- fail.
            nil))))
  :prepwork ((local (in-theory (enable maybe-natp))))
  ///
  (defthm upper-bound-of-vl-rangeexpr-reduce
    (implies (force (vl-expr-p x))
             (< (vl-rangeexpr-reduce x)
                (expt 2 31)))
    :rule-classes :linear))

(defmacro def-vl-rangeresolve (name &key type body guard-hints)
  `(define ,name ((x ,type)
                  (warnings vl-warninglist-p))
     :returns (mv (warnings vl-warninglist-p :hyp :fguard)
                  (new-x ,type :hyp :fguard))
     ,@(and guard-hints
            `(:guard-hints ,guard-hints))
     ,body))

(defmacro def-vl-rangeresolve-list (name &key type element)
  `(define ,name ((x ,type)
                  (warnings vl-warninglist-p))
     :returns (mv (warnings vl-warninglist-p :hyp :fguard)
                  (new-x ,type :hyp :fguard))
     (b* (((when (atom x))
           (mv warnings nil))
          ((mv warnings car-prime) (,element (car x) warnings))
          ((mv warnings cdr-prime) (,name (cdr x) warnings)))
       (mv warnings (cons car-prime cdr-prime)))
     ///
     (defmvtypes ,name (nil true-listp))))

(def-vl-rangeresolve vl-rangeresolve
  :type vl-range-p
  :body (b* (((vl-range x) x)
             (msb-val (vl-rangeexpr-reduce x.msb))
             (lsb-val (vl-rangeexpr-reduce x.lsb)))
          (if (and msb-val lsb-val)
              ;; Ordinary case, build a new range.  We could probably use
              ;; vl-make-index here instead of constructing these manually, but
              ;; it produces sized results and maybe it's slightly better not
              ;; to size these yet.  Hrmn.  It probably doesn't matter.
              ;; Whatever.
              (mv warnings
                  (make-honsed-vl-range
                   :msb (make-honsed-vl-atom
                         :guts (make-honsed-vl-constint :origwidth 32
                                                        :origtype :vl-signed
                                                        :value msb-val
                                                        :wasunsized t))
                   :lsb (make-honsed-vl-atom
                         :guts (make-honsed-vl-constint :origwidth 32
                                                        :origtype :vl-signed
                                                        :value lsb-val
                                                        :wasunsized t))))

            ;; Failure, just return the unreduced range.
            (mv (warn :type :vl-bad-range
                      ;; BOZO need some context
                      :msg "Unable to safely resolve range ~a0."
                      :args (list x))
                x))))

(def-vl-rangeresolve vl-maybe-rangeresolve
  :type vl-maybe-range-p
  :body (if (not x)
            (mv warnings nil)
          ;; Historic note.  We used to eliminate [0:0] ranges, turning
          ;; them them into NIL.  We no longer do this because Verilog-XL
          ;; and NCVerilog are not okay with indexing into a scalar wire.
          ;; That is, if you declare
          ;;   wire [0:0] foo;
          ;;   wire bar;
          ;; Then these tools are happy with things like foo[0], but not
          ;; with bar[0].  On the down-side, Verilog-XL doesn't like to
          ;; have a wire like foo hooked up to a gate.
          (vl-rangeresolve x warnings)))

(def-vl-rangeresolve-list vl-rangelist-rangeresolve
  :type vl-rangelist-p
  :element vl-rangeresolve)

(def-vl-rangeresolve vl-portdecl-rangeresolve
  :type vl-portdecl-p
  :body (b* (((vl-portdecl x) x)
             ((mv warnings range) (vl-maybe-rangeresolve x.range warnings)))
            (mv warnings (change-vl-portdecl x :range range))))

(def-vl-rangeresolve-list vl-portdecllist-rangeresolve
  :type vl-portdecllist-p
  :element vl-portdecl-rangeresolve)

(def-vl-rangeresolve vl-netdecl-rangeresolve
  :type vl-netdecl-p
  :body (b* (((vl-netdecl x) x)
             ((mv warnings range)   (vl-maybe-rangeresolve x.range warnings))
             ((mv warnings arrdims) (vl-rangelist-rangeresolve x.arrdims warnings)))
          (mv warnings (change-vl-netdecl x
                                          :range   range
                                          :arrdims arrdims))))

(def-vl-rangeresolve-list vl-netdecllist-rangeresolve
  :type vl-netdecllist-p
  :element vl-netdecl-rangeresolve)

(def-vl-rangeresolve vl-regdecl-rangeresolve
  :type vl-regdecl-p
  :body (b* (((vl-regdecl x) x)
             ((mv warnings range)   (vl-maybe-rangeresolve x.range warnings))
             ((mv warnings arrdims) (vl-rangelist-rangeresolve x.arrdims warnings)))
          (mv warnings (change-vl-regdecl x
                                          :range   range
                                          :arrdims arrdims))))

(def-vl-rangeresolve-list vl-regdecllist-rangeresolve
  :type vl-regdecllist-p
  :element vl-regdecl-rangeresolve)

(def-vl-rangeresolve vl-vardecl-rangeresolve
  :type vl-vardecl-p
  :body (b* (((vl-vardecl x) x)
             ((mv warnings arrdims) (vl-rangelist-rangeresolve x.arrdims warnings)))
          (mv warnings (change-vl-vardecl x :arrdims arrdims))))

(def-vl-rangeresolve-list vl-vardecllist-rangeresolve
  :type vl-vardecllist-p
  :element vl-vardecl-rangeresolve)

(def-vl-rangeresolve vl-modinst-rangeresolve
  :type vl-modinst-p
  :body (b* (((vl-modinst x) x)
             ((mv warnings range) (vl-maybe-rangeresolve x.range warnings)))
          (mv warnings (change-vl-modinst x :range range))))

(def-vl-rangeresolve-list vl-modinstlist-rangeresolve
  :type vl-modinstlist-p
  :element vl-modinst-rangeresolve)

(def-vl-rangeresolve vl-gateinst-rangeresolve
  :type vl-gateinst-p
  :body (b* (((vl-gateinst x) x)
             ((mv warnings range) (vl-maybe-rangeresolve x.range warnings)))
          (mv warnings (change-vl-gateinst x :range range))))

(def-vl-rangeresolve-list vl-gateinstlist-rangeresolve
  :type vl-gateinstlist-p
  :element vl-gateinst-rangeresolve)

(def-vl-rangeresolve vl-paramdecl-rangeresolve
  :type vl-paramdecl-p
  :body (b* (((vl-paramdecl x) x)
             ((mv warnings range) (vl-maybe-rangeresolve x.range warnings)))
          (mv warnings (change-vl-paramdecl x :range range))))

(def-vl-rangeresolve-list vl-paramdecllist-rangeresolve
  :type vl-paramdecllist-p
  :element vl-paramdecl-rangeresolve)

(def-vl-rangeresolve vl-eventdecl-rangeresolve
  :type vl-eventdecl-p
  :body (b* (((vl-eventdecl x) x)
             ((mv warnings arrdims) (vl-rangelist-rangeresolve x.arrdims warnings)))
          (mv warnings (change-vl-eventdecl x :arrdims arrdims))))

(def-vl-rangeresolve-list vl-eventdecllist-rangeresolve
  :type vl-eventdecllist-p
  :element vl-eventdecl-rangeresolve)

(def-vl-rangeresolve vl-taskport-rangeresolve
  :type vl-taskport-p
  :body
  (b* (((vl-taskport x) x)
       ((mv warnings range) (vl-maybe-rangeresolve x.range warnings)))
    (mv warnings (change-vl-taskport x :range range))))

(def-vl-rangeresolve-list vl-taskportlist-rangeresolve
  :type vl-taskportlist-p
  :element vl-taskport-rangeresolve)

(def-vl-rangeresolve vl-blockitem-rangeresolve
  :type vl-blockitem-p
  :body (case (tag x)
          (:vl-regdecl   (vl-regdecl-rangeresolve   x warnings))
          (:vl-vardecl   (vl-vardecl-rangeresolve   x warnings))
          (:vl-eventdecl (vl-eventdecl-rangeresolve x warnings))
          (:vl-paramdecl (vl-paramdecl-rangeresolve x warnings))
          (otherwise (mv nil warnings))))

(def-vl-rangeresolve-list vl-blockitemlist-rangeresolve
  :type vl-blockitemlist-p
  :element vl-blockitem-rangeresolve)

(def-vl-rangeresolve vl-fundecl-rangeresolve
  :type vl-fundecl-p
  :body
  (b* (((vl-fundecl x) x)
       ((mv warnings rrange) (vl-maybe-rangeresolve x.rrange warnings))
       ((mv warnings decls)  (vl-blockitemlist-rangeresolve x.decls warnings))
       ((mv warnings inputs) (vl-taskportlist-rangeresolve x.inputs warnings)))
    (mv warnings
        (change-vl-fundecl x
                           :rrange rrange
                           :decls  decls
                           :inputs inputs))))

(def-vl-rangeresolve-list vl-fundecllist-rangeresolve
  :type vl-fundecllist-p
  :element vl-fundecl-rangeresolve)

(define vl-module-rangeresolve ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard)
  (b* (((vl-module x) x)
       ((when (vl-module->hands-offp x))
        x)
       (warnings                 x.warnings)
       ((mv warnings portdecls)  (vl-portdecllist-rangeresolve  x.portdecls  warnings))
       ((mv warnings netdecls)   (vl-netdecllist-rangeresolve   x.netdecls   warnings))
       ((mv warnings vardecls)   (vl-vardecllist-rangeresolve   x.vardecls   warnings))
       ((mv warnings regdecls)   (vl-regdecllist-rangeresolve   x.regdecls   warnings))
       ((mv warnings eventdecls) (vl-eventdecllist-rangeresolve x.eventdecls warnings))
       ((mv warnings modinsts)   (vl-modinstlist-rangeresolve   x.modinsts   warnings))
       ((mv warnings gateinsts)  (vl-gateinstlist-rangeresolve  x.gateinsts  warnings))
       ((mv warnings fundecls)   (vl-fundecllist-rangeresolve   x.fundecls   warnings))
       ;; BOZO may eventually want to resolve ranges in block items within statements.
       )
      (change-vl-module x
                        :warnings   warnings
                        :portdecls  portdecls
                        :netdecls   netdecls
                        :vardecls   vardecls
                        :regdecls   regdecls
                        :eventdecls eventdecls
                        :modinsts   modinsts
                        :gateinsts  gateinsts
                        :fundecls   fundecls)))

(defprojection vl-modulelist-rangeresolve (x)
  (vl-module-rangeresolve x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p)

(define vl-design-rangeresolve ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x)
       (new-mods (vl-modulelist-rangeresolve x.mods)))
    (change-vl-design x :mods new-mods)))




(define vl-op-selresolve
  ((op       "some operator being applied to @('args')" vl-op-p)
   (args     (and (vl-exprlist-p args)
                  (or (not (vl-op-arity op))
                      (equal (len args) (vl-op-arity op)))))
   (warnings vl-warninglist-p)
   (context  "like @('op(args)'), for better warnings" vl-expr-p))
  :returns
  (mv (warnings vl-warninglist-p)
      (new-args :hyp :fguard
                (and (vl-exprlist-p new-args)
                     (equal (len new-args) (len args)))))
  :short "Non-recursively resolve indices on a single select or the
multiplicity of a single multiconcat."

  :long "<p>This is the core function for simplifying indices.  If @('op') is a
bit-select, part-select, or multiple concatenation, we try to evaluate
expressions within it, e.g., replacing @('6-1') with @('5'), which may have
arisen during the course of unparameterization.</p>"

  (case op
    (:vl-partselect-colon
     (b* ((from   (first args))
          (index1 (second args))
          (index2 (third args))
          (val1   (vl-rangeexpr-reduce index1))
          (val2   (vl-rangeexpr-reduce index2))
          ((unless (and val1 val2))
           (mv (warn :type :vl-bad-expression
                     ;; BOZO need some context
                     :msg "Unable to safely resolve indices on part-select ~a0."
                     :args (list context))
               args))
          (msb (make-honsed-vl-atom
                :guts (make-honsed-vl-constint :origwidth 32
                                               :origtype :vl-signed
                                               :value val1
                                               :wasunsized t)))
          (lsb  (make-honsed-vl-atom
                 :guts (make-honsed-vl-constint :origwidth 32
                                                :origtype :vl-signed
                                                :value val2
                                                :wasunsized t))))
       (mv (ok) (list from msb lsb))))

    (:vl-bitselect
     (b* ((from  (first args))
          (index (second args))
          (val   (vl-rangeexpr-reduce index))
          ((unless val)
           (mv (warn :type :vl-dynamic-bsel
                     ;; BOZO need some context
                     :msg "Unable to safely resolve index on bit-select ~a0, ~
                           so a dynamic bit-select will have to be used ~
                           instead."
                     :args (list context))
               args))
          (atom (make-honsed-vl-atom
                 :guts (make-honsed-vl-constint :origwidth 32
                                                :origtype :vl-signed
                                                :value val
                                                :wasunsized t))))
       (mv (ok) (list from atom))))

    (:vl-multiconcat
     (b* ((mult   (first args))
          (kitty  (second args))
          (val    (vl-rangeexpr-reduce mult))
          ((unless val)
           (mv (warn :type :vl-bad-expression
                     ;; BOZO need some context
                     :msg "Unable to safely resolve multiplicity on ~
                           multiconcat ~a0."
                     :args (list context))
               args))
          (atom (make-honsed-vl-atom
                 :guts (make-honsed-vl-constint :origwidth 32
                                                :origtype :vl-signed
                                                :value val
                                                :wasunsized t))))
       (mv (ok) (list atom kitty))))

    (otherwise
     (mv (ok) args)))

  :guard-hints (("Goal" :in-theory (enable vl-op-p vl-op-arity))))


(defines vl-expr-selresolve
  :short "Recursively simplify indices on selects and multiplicities on
multiconcats throughout an expression."

  (define vl-expr-selresolve
    ((x        vl-expr-p)
     (warnings vl-warninglist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    vl-expr-p :hyp (force (vl-expr-p x))))
    :verify-guards nil
    :measure (two-nats-measure (acl2-count x) 1)
    (b* (((when (vl-fast-atom-p x))
          (mv (ok) x))
         (op                 (vl-nonatom->op x))
         ((mv warnings args) (vl-exprlist-selresolve (vl-nonatom->args x) warnings))
         ((mv warnings args) (vl-op-selresolve op args warnings x)))
      (mv warnings (change-vl-nonatom x :args args))))

  (define vl-exprlist-selresolve
    ((x        vl-exprlist-p)
     (warnings vl-warninglist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    (and (implies (force (vl-exprlist-p x))
                                         (vl-exprlist-p new-x))
                                (equal (len new-x) (len x)))))
    :measure (two-nats-measure (acl2-count x) 0)
    (b* (((when (atom x))
          (mv (ok) nil))
         ((mv warnings car-prime) (vl-expr-selresolve (car x) warnings))
         ((mv warnings cdr-prime) (vl-exprlist-selresolve (cdr x) warnings)))
      (mv warnings (cons car-prime cdr-prime))))
  ///
  (verify-guards vl-expr-selresolve))

(defmacro def-vl-selresolve (name &key type body)
  `(define ,name ((x ,type)
                  (warnings vl-warninglist-p))
     :returns (mv (warnings vl-warninglist-p)
                  (new-x    ,type :hyp (force (,type x))))
     ,body))

(defmacro def-vl-selresolve-list (name &key type element)
  `(define ,name ((x ,type)
                  (warnings vl-warninglist-p))
     :returns (mv (warnings vl-warninglist-p)
                  (new-x    ,type :hyp (force (,type x))))
     (b* (((when (atom x))
           (mv (ok) nil))
          ((mv warnings car-prime) (,element (car x) warnings))
          ((mv warnings cdr-prime) (,name (cdr x) warnings)))
       (mv warnings (cons car-prime cdr-prime)))
     ///
     (defmvtypes ,name (nil true-listp))))

(def-vl-selresolve vl-maybe-expr-selresolve
  :type vl-maybe-expr-p
  :body (if (not x)
            (mv (ok) nil)
          (vl-expr-selresolve x warnings)))

(def-vl-selresolve vl-port-selresolve
  :type vl-port-p
  :body (b* (((vl-port x) x)
             ((mv warnings expr) (vl-maybe-expr-selresolve x.expr warnings)))
          (mv warnings (change-vl-port x :expr expr))))

(def-vl-selresolve-list vl-portlist-selresolve
  :type vl-portlist-p
  :element vl-port-selresolve)

(def-vl-selresolve vl-assign-selresolve
  :type vl-assign-p
  :body (b* (((vl-assign x) x)
             ((mv warnings lvalue) (vl-expr-selresolve x.lvalue warnings))
             ((mv warnings expr)   (vl-expr-selresolve x.expr warnings)))
            (mv warnings (change-vl-assign x
                                           :lvalue lvalue
                                           :expr expr))))

(def-vl-selresolve-list vl-assignlist-selresolve
  :type vl-assignlist-p
  :element vl-assign-selresolve)

(def-vl-selresolve vl-plainarg-selresolve
  :type vl-plainarg-p
  :body (b* (((vl-plainarg x) x)
             ((mv warnings expr) (vl-maybe-expr-selresolve x.expr warnings)))
          (mv warnings (change-vl-plainarg x :expr expr))))

(def-vl-selresolve-list vl-plainarglist-selresolve
  :type vl-plainarglist-p
  :element vl-plainarg-selresolve)

(def-vl-selresolve vl-namedarg-selresolve
  :type vl-namedarg-p
  :body (b* (((vl-namedarg x) x)
             ((mv warnings expr) (vl-maybe-expr-selresolve x.expr warnings)))
          (mv warnings (change-vl-namedarg x :expr expr))))

(def-vl-selresolve-list vl-namedarglist-selresolve
  :type vl-namedarglist-p
  :element vl-namedarg-selresolve)

(def-vl-selresolve vl-arguments-selresolve
  :type vl-arguments-p
  :body (b* (((vl-arguments x) x)
             ((mv warnings args) (if x.namedp
                                     (vl-namedarglist-selresolve x.args warnings)
                                   (vl-plainarglist-selresolve x.args warnings))))
            (mv warnings (vl-arguments x.namedp args))))

(def-vl-selresolve vl-modinst-selresolve
  :type vl-modinst-p
  :body (b* (((vl-modinst x) x)
             ((mv warnings paramargs) (vl-arguments-selresolve x.paramargs warnings))
             ((mv warnings portargs)  (vl-arguments-selresolve x.portargs warnings)))
          (mv warnings (change-vl-modinst x
                                          :paramargs paramargs
                                          :portargs  portargs))))

(def-vl-selresolve-list vl-modinstlist-selresolve
  :type vl-modinstlist-p
  :element vl-modinst-selresolve)

(def-vl-selresolve vl-gateinst-selresolve
  :type vl-gateinst-p
  :body (b* (((vl-gateinst x) x)
             ((mv warnings args) (vl-plainarglist-selresolve x.args warnings)))
          (mv warnings (change-vl-gateinst x :args args))))

(def-vl-selresolve-list vl-gateinstlist-selresolve
  :type vl-gateinstlist-p
  :element vl-gateinst-selresolve)

(def-vl-selresolve vl-delaycontrol-selresolve
  :type vl-delaycontrol-p
  :body (b* (((vl-delaycontrol x) x)
             ((mv warnings value) (vl-expr-selresolve x.value warnings)))
          (mv warnings (change-vl-delaycontrol x :value value))))

(def-vl-selresolve vl-evatom-selresolve
  :type vl-evatom-p
  :body (b* (((vl-evatom x) x)
             ((mv warnings expr-prime) (vl-expr-selresolve x.expr warnings)))
          (mv warnings (change-vl-evatom x :expr expr-prime))))

(def-vl-selresolve-list vl-evatomlist-selresolve
  :type vl-evatomlist-p
  :element vl-evatom-selresolve)

(def-vl-selresolve vl-eventcontrol-selresolve
  :type vl-eventcontrol-p
  :body (b* (((vl-eventcontrol x) x)
             ((mv warnings atoms) (vl-evatomlist-selresolve x.atoms warnings)))
          (mv warnings (change-vl-eventcontrol x :atoms atoms))))

(def-vl-selresolve vl-repeateventcontrol-selresolve
  :type vl-repeateventcontrol-p
  :body (b* (((vl-repeateventcontrol x) x)
             ((mv warnings expr) (vl-expr-selresolve x.expr warnings))
             ((mv warnings ctrl) (vl-eventcontrol-selresolve x.ctrl warnings)))
          (mv warnings (change-vl-repeateventcontrol x
                                                     :expr expr
                                                     :ctrl ctrl))))

(encapsulate
 ()
 (local (in-theory (disable vl-delayoreventcontrol-p-when-vl-maybe-delayoreventcontrol-p)))
 (def-vl-selresolve vl-delayoreventcontrol-selresolve
   :type vl-delayoreventcontrol-p
   :body (case (tag x)
           (:vl-delaycontrol        (vl-delaycontrol-selresolve x warnings))
           (:vl-eventcontrol        (vl-eventcontrol-selresolve x warnings))
           (:vl-repeat-eventcontrol (vl-repeateventcontrol-selresolve x warnings))
           (otherwise
            (mv (impossible) x)))))

(def-vl-selresolve vl-maybe-delayoreventcontrol-selresolve
  :type vl-maybe-delayoreventcontrol-p
  :body (if x
            (vl-delayoreventcontrol-selresolve x warnings)
          (mv (ok) nil)))

(defthm vl-maybe-delayoreventcontrol-selresolve-under-iff
  (implies (and (force (vl-maybe-delayoreventcontrol-p x))
                (force (vl-warninglist-p warnings)))
           (b* (((mv ?warnings new-x)
                 (vl-maybe-delayoreventcontrol-selresolve x warnings)))
             (iff new-x x)))
  :hints(("Goal"
          :in-theory (e/d (vl-maybe-delayoreventcontrol-selresolve
                           vl-maybe-delayoreventcontrol-p)
                          (return-type-of-vl-delayoreventcontrol-selresolve.new-x))
          :use ((:instance return-type-of-vl-delayoreventcontrol-selresolve.new-x)))))

(def-vl-selresolve vl-assignstmt-selresolve
  :type vl-assignstmt-p
  :body (b* (((vl-assignstmt x) x)
             ((mv warnings lvalue) (vl-expr-selresolve x.lvalue warnings))
             ((mv warnings expr) (vl-expr-selresolve x.expr warnings))
             ((mv warnings ctrl) (vl-maybe-delayoreventcontrol-selresolve x.ctrl warnings)))
          (mv warnings (change-vl-assignstmt x
                                             :lvalue lvalue
                                             :expr   expr
                                             :ctrl   ctrl))))

(def-vl-selresolve vl-deassignstmt-selresolve
  :type vl-deassignstmt-p
  :body (b* (((vl-deassignstmt x) x)
             ((mv warnings lvalue) (vl-expr-selresolve x.lvalue warnings)))
          (mv warnings (change-vl-deassignstmt x :lvalue lvalue))))

(def-vl-selresolve vl-enablestmt-selresolve
  :type vl-enablestmt-p
  :body (b* (((vl-enablestmt x) x)
             ((mv warnings id)   (vl-expr-selresolve x.id warnings))
             ((mv warnings args) (vl-exprlist-selresolve x.args warnings)))
            (mv warnings (change-vl-enablestmt x
                                               :id   id
                                               :args args))))

(def-vl-selresolve vl-disablestmt-selresolve
  :type vl-disablestmt-p
  :body (b* (((vl-disablestmt x) x)
             ((mv warnings id) (vl-expr-selresolve x.id warnings)))
          (mv warnings (change-vl-disablestmt x :id id))))


(def-vl-selresolve vl-eventtriggerstmt-selresolve
  :type vl-eventtriggerstmt-p
  :body (b* (((vl-eventtriggerstmt x) x)
             ((mv warnings id) (vl-expr-selresolve x.id warnings)))
            (mv warnings (change-vl-eventtriggerstmt x :id id))))

(def-vl-selresolve vl-atomicstmt-selresolve
  :type vl-atomicstmt-p
  :body (case (tag x)
          (:vl-nullstmt         (mv (ok) x))
          (:vl-assignstmt       (vl-assignstmt-selresolve x warnings))
          (:vl-deassignstmt     (vl-deassignstmt-selresolve x warnings))
          (:vl-enablestmt       (vl-enablestmt-selresolve x warnings))
          (:vl-disablestmt      (vl-disablestmt-selresolve x warnings))
          (:vl-eventtriggerstmt (vl-eventtriggerstmt-selresolve x warnings))
          (otherwise
           (mv (impossible) x))))


(defines vl-stmt-selresolve

  (define vl-stmt-selresolve
    ((x        vl-stmt-p)
     (warnings vl-warninglist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    vl-stmt-p :hyp (force (vl-stmt-p x))))
    :verify-guards nil
    :measure (two-nats-measure (acl2-count x) 1)
    (b* (((when (vl-fast-atomicstmt-p x))
          (vl-atomicstmt-selresolve x warnings))
         ((vl-compoundstmt x) x)
         ((mv warnings exprs) (vl-exprlist-selresolve x.exprs warnings))
         ((mv warnings stmts) (vl-stmtlist-selresolve x.stmts warnings))
         ((mv warnings ctrl)  (vl-maybe-delayoreventcontrol-selresolve x.ctrl warnings)))
      (mv warnings (change-vl-compoundstmt x
                                           :exprs exprs
                                           :stmts stmts
                                           :ctrl ctrl))))

  (define vl-stmtlist-selresolve
    ((x        vl-stmtlist-p)
     (warnings vl-warninglist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    (and (implies (force (vl-stmtlist-p x))
                                         (vl-stmtlist-p new-x))
                                (equal (len new-x) (len x)))))
    :measure (two-nats-measure (acl2-count x) 0)
    (b* (((when (atom x))
          (mv (ok) nil))
         ((mv warnings car-prime) (vl-stmt-selresolve (car x) warnings))
         ((mv warnings cdr-prime) (vl-stmtlist-selresolve (cdr x) warnings)))
      (mv warnings (cons car-prime cdr-prime))))
  ///
  (verify-guards vl-stmt-selresolve))

(def-vl-selresolve vl-always-selresolve
  :type vl-always-p
  :body (b* (((vl-always x) x)
             ((mv warnings stmt) (vl-stmt-selresolve x.stmt warnings)))
            (mv warnings (change-vl-always x :stmt stmt))))

(def-vl-selresolve-list vl-alwayslist-selresolve
  :type vl-alwayslist-p
  :element vl-always-selresolve)

(def-vl-selresolve vl-initial-selresolve
  :type vl-initial-p
  :body (b* (((vl-initial x) x)
             ((mv warnings stmt) (vl-stmt-selresolve x.stmt warnings)))
          (mv warnings (change-vl-initial x :stmt stmt))))

(def-vl-selresolve-list vl-initiallist-selresolve
  :type vl-initiallist-p
  :element vl-initial-selresolve)

(def-vl-selresolve vl-fundecl-selresolve
  :type vl-fundecl-p
  :body (b* (((vl-fundecl x) x)
             ((mv warnings body) (vl-stmt-selresolve x.body warnings)))
          (mv warnings (change-vl-fundecl x :body body))))

(def-vl-selresolve-list vl-fundecllist-selresolve
  :type vl-fundecllist-p
  :element vl-fundecl-selresolve)

(define vl-module-selresolve ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard)
  (b* (((vl-module x) x)
       ((when (vl-module->hands-offp x))
        x)
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

(defprojection vl-modulelist-selresolve (x)
  (vl-module-selresolve x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p)

(define vl-design-selresolve ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x)
       (new-mods (vl-modulelist-selresolve x.mods)))
    (change-vl-design x :mods new-mods)))
