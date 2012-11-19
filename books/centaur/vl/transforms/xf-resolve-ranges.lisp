; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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


(defxdoc vl-rangeexpr-reduce
  :parents (rangeresolve)
  :short "An evaluator for a small set of \"constant expressions\" in Verilog."
  :long "<p>We now introduce an evaluator for this subset of Verilog expressions.</p>

<p>Our evaluator is very careful and checks, after every computation, that the
 result is still within the 32-bit signed integer range.  (This is the minimum
 size of \"integer\" for Verilog implementations, which is the size that plain
 decimal integer literals are supposed to have.)  If we ever leave that range,
 we just fail to evaluate the expression.</p>

<p>Note that in general it is <b>not safe</b> to call this function on arbitrary
 Verilog expressions to do constant folding because the size of the left-hand
 side can influence the widths at which the interior computations are to be
 done.  However, it is safe to use this inside of range expressions, because
 there is no left-hand side to provide us a context.</p>

<p>We return a signed, 32-bit integer on success, or @('nil') on failure.</p>")


(defund vl-rangeexpr-reduce (x)
  (declare (xargs :guard (vl-expr-p x)))

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
           (and (eq (tag guts) :vl-constint)
                (eq (vl-constint->origtype guts) :vl-signed)
                (equal (vl-constint->origwidth guts) 32)
                (vl-constint->wasunsized guts)
                (< (vl-constint->value guts) (expt 2 31))
                ;; This lnfix is a stupid hack that gives us an unconditional
                ;; type prescription rule.  We "know" that the value is an
                ;; natural nubmer as long as x is indeed an expression.
                (lnfix (vl-constint->value guts)))))

        (t
         ;; The only operations we permit here are plus, minus, times, and left
         ;; shift.
         ;; What's more, we also require that the result of every computation
         ;; during the range resolution is within the signed, 32-bit range.
         ;;
         ;; Be very careful if you decide to try to extend this to support
         ;; other operations!  In particular, you should understand the
         ;; signedness rules and how operations like comparisons will take you
         ;; out of the world of signed arithmetic.
         (case (vl-nonatom->op x)
           (:vl-unary-plus
            (vl-rangeexpr-reduce (first (vl-nonatom->args x))))
;           (:vl-unary-minus
;            (let ((arg (vl-rangeexpr-reduce (first (vl-nonatom->args x))))
;                  (ret (- arg)))
;              (and arg
;                   (<= 0 ret)
;                   (<= ret (expt 2 31))
;                   ret)))
           (:vl-binary-plus
            (let ((arg1 (vl-rangeexpr-reduce (first (vl-nonatom->args x))))
                  (arg2 (vl-rangeexpr-reduce (second (vl-nonatom->args x)))))
              (and arg1
                   arg2
                   (< (+ arg1 arg2) (expt 2 31))
                   (+ arg1 arg2))))
           (:vl-binary-minus
            (let ((arg1 (vl-rangeexpr-reduce (first (vl-nonatom->args x))))
                  (arg2 (vl-rangeexpr-reduce (second (vl-nonatom->args x)))))
              (and arg1
                   arg2
                   (<= 0 (- arg1 arg2))
                   (- arg1 arg2))))
           (:vl-binary-times
            (let ((arg1 (vl-rangeexpr-reduce (first (vl-nonatom->args x))))
                  (arg2 (vl-rangeexpr-reduce (second (vl-nonatom->args x)))))
              (and arg1
                   arg2
                   (< (* arg1 arg2) (expt 2 31))
                   (* arg1 arg2))))
           (:vl-binary-shl
            (let ((arg1 (vl-rangeexpr-reduce (first (vl-nonatom->args x))))
                  (arg2 (vl-rangeexpr-reduce (second (vl-nonatom->args x)))))
              (and arg1
                   arg2
                   (<= 0 (ash arg1 arg2))
                   (< (ash arg1 arg2) (expt 2 31))
                   (ash arg1 arg2))))
           (t
            ;; Some unsupported operation -- fail.
            nil)))))

(defthm type-of-vl-rangeexpr-reduce
  (vl-maybe-natp (vl-rangeexpr-reduce x))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-rangeexpr-reduce))))

(defthm upper-bound-of-vl-rangeexpr-reduce
  (implies (and (vl-rangeexpr-reduce x)
                (force (vl-expr-p x)))
           (< (vl-rangeexpr-reduce x)
              (expt 2 31)))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable vl-rangeexpr-reduce))))





(defmacro def-vl-rangeresolve (name &key type body guard-hints)
  (let* ((name-s     (symbol-name name))
         (type-s     (symbol-name type))
         (thm-warn-s (cat "VL-WARNINGLIST-P-" name-s))
         (thm-type-s (cat type-s "-OF-" name-s))
         (thm-warn   (intern-in-package-of-symbol thm-warn-s name))
         (thm-type   (intern-in-package-of-symbol thm-type-s name)))
    `(defsection ,name

       (defund ,name (x warnings)
         "Returns (MV WARNINGS-PRIME X-PRIME)"
         (declare (xargs :guard (and (,type x)
                                     (vl-warninglist-p warnings))
                         ,@(and guard-hints
                                `(:guard-hints ,guard-hints))))
         ,body)

       (local (in-theory (enable ,name)))

       (defthm ,thm-warn
         (implies (force (vl-warninglist-p warnings))
                  (vl-warninglist-p (mv-nth 0 (,name x warnings)))))

       (defthm ,thm-type
         (implies (force (,type x))
                  (,type (mv-nth 1 (,name x warnings))))))))

(defmacro def-vl-rangeresolve-list (name &key type element)
  (let* ((name-s     (symbol-name name))
         (type-s     (symbol-name type))
         (thm-warn-s (cat "VL-WARNINGLIST-P-" name-s))
         (thm-type-s (cat type-s "-OF-" name-s))
         (thm-true-s (cat "TRUE-LISTP-OF-" name-s))
         (thm-warn   (intern-in-package-of-symbol thm-warn-s name))
         (thm-type   (intern-in-package-of-symbol thm-type-s name))
         (thm-true   (intern-in-package-of-symbol thm-true-s name)))
    `(defsection ,name

       (defund ,name (x warnings)
         "Returns (MV WARNINGS-PRIME X-PRIME)"
         (declare (xargs :guard (and (,type x)
                                     (vl-warninglist-p warnings))))
         (if (atom x)
             (mv warnings nil)
           (b* (((mv warnings car-prime) (,element (car x) warnings))
                ((mv warnings cdr-prime) (,name (cdr x) warnings)))
               (mv warnings (cons car-prime cdr-prime)))))

       (local (in-theory (enable ,name)))

       (defthm ,thm-warn
         (implies (vl-warninglist-p warnings)
                  (vl-warninglist-p (mv-nth 0 (,name x warnings)))))

       (defthm ,thm-type
         (implies (force (,type x))
                  (,type (mv-nth 1 (,name x warnings)))))

       (defthm ,thm-true
         (true-listp (mv-nth 1 (,name x warnings)))
         :rule-classes :type-prescription))))


(def-vl-rangeresolve vl-rangeresolve
  :type vl-range-p
  :body (let ((msb-val (vl-rangeexpr-reduce (vl-range->msb x)))
              (lsb-val (vl-rangeexpr-reduce (vl-range->lsb x))))
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
            (mv (cons (make-vl-warning
                       :type :vl-bad-range
                       ;; BOZO need some context
                       :msg "Unable to safely resolve range ~a0."
                       :args (list x)
                       :fn 'vl-rangeresolve)
                      warnings)
                x))))

(def-vl-rangeresolve vl-maybe-rangeresolve
  :type vl-maybe-range-p
  :body (if (not x)
            (mv warnings nil)
          (mv-let (warnings range)
                  (vl-rangeresolve x warnings)
                  ;; Historic note:  We used to eliminate [0:0] ranges as
                  ;; follows.  But we no longer do, because Verilog-XL and
                  ;; NCVerilog both seem ok with them, and not ok with indexing
                  ;; into a scalar wire.
                  ;; (if (and (vl-range-resolved-p range)
                  ;;          (= (vl-resolved->val (vl-range->left range)) 0)
                  ;;          (= (vl-resolved->val (vl-range->right range)) 0))
                  ;;     ;; Special case: range reduced to [0:0]; get rid of it!
                  ;;     ;; This helps avoid [0:0] wire declarations that Cadence
                  ;;     ;; doesn't like (at least, it doesn't like hooking them
                  ;;     ;; up to gates)
                  ;;     (mv warnings nil)
                  ;;   (mv warnings range))
                  (mv warnings range))))

(def-vl-rangeresolve-list vl-rangelist-rangeresolve
  :type vl-rangelist-p
  :element vl-rangeresolve)



(def-vl-rangeresolve vl-portdecl-rangeresolve
  :type vl-portdecl-p
  :body (b* (((mv warnings range-prime)
              (vl-maybe-rangeresolve (vl-portdecl->range x) warnings)))
            (mv warnings (change-vl-portdecl x :range range-prime))))

(def-vl-rangeresolve-list vl-portdecllist-rangeresolve
  :type vl-portdecllist-p
  :element vl-portdecl-rangeresolve)



(def-vl-rangeresolve vl-netdecl-rangeresolve
  :type vl-netdecl-p
  :body (b* (((mv warnings range-prime)
              (vl-maybe-rangeresolve (vl-netdecl->range x) warnings))
             ((mv warnings arrdims-prime)
              (vl-rangelist-rangeresolve (vl-netdecl->arrdims x) warnings)))
            (mv warnings (change-vl-netdecl x
                                            :range range-prime
                                            :arrdims arrdims-prime))))

(def-vl-rangeresolve-list vl-netdecllist-rangeresolve
  :type vl-netdecllist-p
  :element vl-netdecl-rangeresolve)


(def-vl-rangeresolve vl-regdecl-rangeresolve
  :type vl-regdecl-p
  :body (b* (((mv warnings range-prime)
              (vl-maybe-rangeresolve (vl-regdecl->range x) warnings))
             ((mv warnings arrdims-prime)
              (vl-rangelist-rangeresolve (vl-regdecl->arrdims x) warnings)))
            (mv warnings (change-vl-regdecl x
                                            :range range-prime
                                            :arrdims arrdims-prime))))

(def-vl-rangeresolve-list vl-regdecllist-rangeresolve
  :type vl-regdecllist-p
  :element vl-regdecl-rangeresolve)


(def-vl-rangeresolve vl-vardecl-rangeresolve
  :type vl-vardecl-p
  :body (b* (((mv warnings arrdims-prime)
              (vl-rangelist-rangeresolve (vl-vardecl->arrdims x) warnings)))
            (mv warnings (change-vl-vardecl x
                                            :arrdims arrdims-prime))))

(def-vl-rangeresolve-list vl-vardecllist-rangeresolve
  :type vl-vardecllist-p
  :element vl-vardecl-rangeresolve)


(def-vl-rangeresolve vl-modinst-rangeresolve
  :type vl-modinst-p
  :body (b* (((mv warnings range-prime)
              (vl-maybe-rangeresolve (vl-modinst->range x) warnings)))
            (mv warnings (change-vl-modinst x :range range-prime))))

(def-vl-rangeresolve-list vl-modinstlist-rangeresolve
  :type vl-modinstlist-p
  :element vl-modinst-rangeresolve)


(def-vl-rangeresolve vl-gateinst-rangeresolve
  :type vl-gateinst-p
  :body (b* (((mv warnings range-prime)
              (vl-maybe-rangeresolve (vl-gateinst->range x) warnings)))
            (mv warnings (change-vl-gateinst x :range range-prime))))

(def-vl-rangeresolve-list vl-gateinstlist-rangeresolve
  :type vl-gateinstlist-p
  :element vl-gateinst-rangeresolve)


(def-vl-rangeresolve vl-paramdecl-rangeresolve
  :type vl-paramdecl-p
  :body (b* (((mv warnings range-prime)
              (vl-maybe-rangeresolve (vl-paramdecl->range x) warnings)))
            (mv warnings (change-vl-paramdecl x :range range-prime))))

(def-vl-rangeresolve-list vl-paramdecllist-rangeresolve
  :type vl-paramdecllist-p
  :element vl-paramdecl-rangeresolve)


(def-vl-rangeresolve vl-eventdecl-rangeresolve
  :type vl-eventdecl-p
  :body (b* (((mv warnings arrdims-prime)
              (vl-rangelist-rangeresolve (vl-eventdecl->arrdims x) warnings)))
            (mv warnings (change-vl-eventdecl x :arrdims arrdims-prime))))

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
          (:vl-regdecl (vl-regdecl-rangeresolve x warnings))
          (:vl-vardecl (vl-vardecl-rangeresolve x warnings))
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
       ((mv warnings decls) (vl-blockitemlist-rangeresolve x.decls warnings))
       ((mv warnings inputs) (vl-taskportlist-rangeresolve x.inputs warnings)))
    (mv warnings
        (change-vl-fundecl x
                           :rrange rrange
                           :decls decls
                           :inputs inputs))))

(def-vl-rangeresolve-list vl-fundecllist-rangeresolve
  :type vl-fundecllist-p
  :element vl-fundecl-rangeresolve)



(defund vl-module-rangeresolve (x)
  (declare (xargs :guard (vl-module-p x)))
  (b* (((when (vl-module->hands-offp x))
        x)
       (warnings                 (vl-module->warnings x))
       ((mv warnings portdecls)  (vl-portdecllist-rangeresolve (vl-module->portdecls x) warnings))
       ((mv warnings netdecls)   (vl-netdecllist-rangeresolve (vl-module->netdecls x) warnings))
       ((mv warnings vardecls)   (vl-vardecllist-rangeresolve (vl-module->vardecls x) warnings))
       ((mv warnings regdecls)   (vl-regdecllist-rangeresolve (vl-module->regdecls x) warnings))
       ((mv warnings eventdecls) (vl-eventdecllist-rangeresolve (vl-module->eventdecls x) warnings))
       ((mv warnings modinsts)   (vl-modinstlist-rangeresolve (vl-module->modinsts x) warnings))
       ((mv warnings gateinsts)  (vl-gateinstlist-rangeresolve (vl-module->gateinsts x) warnings))
       ((mv warnings fundecls)   (vl-fundecllist-rangeresolve (vl-module->fundecls x) warnings))
       ;; BOZO may eventually want to resolve ranges in block items within statements.
       )
      (change-vl-module x
                        :warnings warnings
                        :portdecls portdecls
                        :netdecls netdecls
                        :vardecls vardecls
                        :regdecls regdecls
                        :eventdecls eventdecls
                        :modinsts modinsts
                        :gateinsts gateinsts
                        :fundecls fundecls)))

(defthm vl-module-p-of-vl-module-rangeresolve
  (implies (force (vl-module-p x))
           (vl-module-p (vl-module-rangeresolve x)))
  :hints(("Goal" :in-theory (enable vl-module-rangeresolve))))

(defthm vl-module->name-of-vl-module-rangeresolve
  (equal (vl-module->name (vl-module-rangeresolve x))
         (vl-module->name x))
  :hints(("Goal" :in-theory (enable vl-module-rangeresolve))))


(defprojection vl-modulelist-rangeresolve (x)
  (vl-module-rangeresolve x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p)

(defthm vl-modulelist->names-of-vl-modulelist-rangeresolve
  (equal (vl-modulelist->names (vl-modulelist-rangeresolve x))
         (vl-modulelist->names x))
  :hints(("Goal" :induct (len x))))




(defsection vl-op-selresolve
  :parents (rangeresolve)
  :short "Main function for simplifying selects"
  :long "<p><b>Signature:</b> @(call vl-op-selresolve) returns @('(mv
warnings-prime args-prime)')</p>

<p>@('op') is some operator being applied to @('args').  @('warnings') is an
accumulator for warnings, which we may extend, and @('context') is irrelevant
and is only used to generate more useful warnings.</p>

<p>If @('op') is a bit-select, part-select, or multiple concatenation, we try
to evaluate expressions within it, e.g., replacing @('6-1') with @('5'), which
may have arisen during the course of unparameterization.</p>"

  (defund vl-op-selresolve (op args warnings context)
    "Returns (MV WARNINGS-PRIME ARGS-PRIME)"
    (declare (xargs :guard (and (vl-op-p op)
                                (vl-exprlist-p args)
                                (or (not (vl-op-arity op))
                                    (equal (len args) (vl-op-arity op)))
                                (vl-warninglist-p warnings)
                                (vl-expr-p context))
                    :guard-hints (("Goal" :in-theory (enable vl-op-p vl-op-arity)))))
    (case op
      (:vl-partselect-colon
       (b* ((from   (first args))
            (index1 (second args))
            (index2 (third args))
            (val1   (vl-rangeexpr-reduce index1))
            (val2   (vl-rangeexpr-reduce index2))
            ((unless (and val1 val2))
             (mv (cons (make-vl-warning
                        :type :vl-bad-expression
                        ;; BOZO need some context
                        :msg "Unable to safely resolve indices on part-select ~a0."
                        :args (list context)
                        :fn 'vl-op-selresolve)
                       warnings)
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
         (mv warnings (list from msb lsb))))

      (:vl-bitselect
       (b* ((from  (first args))
            (index (second args))
            (val   (vl-rangeexpr-reduce index))
            ((unless val)
             (mv (cons (make-vl-warning
                        :type :vl-dynamic-bsel
                        ;; BOZO need some context
                        :msg "Unable to safely resolve index on bit-select ~
                              ~a0, so a dynamic bit-select will have to be ~
                              used instead."
                        :args (list context)
                        :fn 'vl-op-selresolve)
                       warnings)
                 args))
            (atom (make-honsed-vl-atom 
                   :guts (make-honsed-vl-constint :origwidth 32
                                                  :origtype :vl-signed
                                                  :value val
                                                  :wasunsized t))))
         (mv warnings (list from atom))))

      (:vl-multiconcat
       (b* ((mult   (first args))
            (kitty  (second args))
            (val    (vl-rangeexpr-reduce mult))
            ((unless val)
             (mv (cons (make-vl-warning
                        :type :vl-bad-expression
                        ;; BOZO need some context
                        :msg "Unable to safely resolve multiplicity on multiconcat ~a0."
                        :args (list context)
                        :fn 'vl-op-selresolve)
                       warnings)
                 args))
            (atom (make-honsed-vl-atom
                   :guts (make-honsed-vl-constint :origwidth 32
                                                  :origtype :vl-signed
                                                  :value val
                                                  :wasunsized t))))
         (mv warnings (list atom kitty))))

      (otherwise
       (mv warnings args))))

  (local (in-theory (enable vl-op-selresolve)))

  (defthm vl-warninglist-p-of-vl-op-selresolve
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-op-selresolve op args warnings context)))))

  (defthm vl-exprlist-p-of-vl-op-selresolve
    (implies (and (force (vl-op-p op))
                  (force (vl-exprlist-p args))
                  (force (or (not (vl-op-arity op))
                             (equal (len args) (vl-op-arity op)))))
             (vl-exprlist-p (mv-nth 1 (vl-op-selresolve op args warnings context)))))

  (defthm len-of-vl-op-selresolve
    (implies (and (force (vl-op-p op))
                  (force (vl-exprlist-p args))
                  (force (or (not (vl-op-arity op))
                             (equal (len args) (vl-op-arity op)))))
             (equal (len (mv-nth 1 (vl-op-selresolve op args warnings context)))
                    (len args)))))


(defsection vl-expr-selresolve

  (mutual-recursion
   (defund vl-expr-selresolve (x warnings)
     "Returns (MV WARNINGS-PRIME X-PRIME)"
     (declare (xargs :guard (and (vl-expr-p x)
                                 (vl-warninglist-p warnings))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (if (vl-fast-atom-p x)
         (mv warnings x)
       (b* ((op                 (vl-nonatom->op x))
            ((mv warnings args) (vl-exprlist-selresolve (vl-nonatom->args x) warnings))
            ((mv warnings args) (vl-op-selresolve op args warnings x)))
           (mv warnings
               (change-vl-nonatom x :args args)))))

   (defund vl-exprlist-selresolve (x warnings)
     "Returns (MV WARNINGS-PRIME X-PRIME)"
     (declare (xargs :guard (and (vl-exprlist-p x)
                                 (vl-warninglist-p warnings))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         (mv warnings nil)
       (b* (((mv warnings car-prime) (vl-expr-selresolve (car x) warnings))
            ((mv warnings cdr-prime) (vl-exprlist-selresolve (cdr x) warnings)))
           (mv warnings (cons car-prime cdr-prime))))))

  (defthm vl-exprlist-selresolve-when-not-consp
    (implies (not (consp x))
             (equal (vl-exprlist-selresolve x warnings)
                    (mv warnings nil)))
    :hints(("Goal" :in-theory (enable vl-exprlist-selresolve))))

  (defthm vl-exprlist-selresolve-of-cons
    (equal (vl-exprlist-selresolve (cons a x) warnings)
           (b* (((mv warnings car-prime) (vl-expr-selresolve a warnings))
                ((mv warnings cdr-prime) (vl-exprlist-selresolve x warnings)))
               (mv warnings (cons car-prime cdr-prime))))
    :hints(("Goal" :in-theory (enable vl-exprlist-selresolve))))

  (local (defun my-induction (x warnings)
           (if (atom x)
               (mv warnings nil)
             (b* (((mv warnings car-prime) (vl-expr-selresolve (car x) warnings))
                  ((mv warnings cdr-prime) (my-induction (cdr x) warnings)))
                 (mv warnings (cons car-prime cdr-prime))))))

  (defthm len-of-vl-exprlist-selresolve
    (equal (len (mv-nth 1 (vl-exprlist-selresolve x warnings)))
           (len x))
    :hints(("Goal" :induct (my-induction x warnings))))

  (flag::make-flag vl-flag-expr-selresolve
                   vl-expr-selresolve
                   :flag-mapping ((vl-expr-selresolve . expr)
                                  (vl-exprlist-selresolve . list)))

  (defthm-vl-flag-expr-selresolve lemma
    (expr (implies (force (vl-expr-p x))
                   (vl-expr-p (mv-nth 1 (vl-expr-selresolve x warnings))))
          :name vl-expr-p-of-vl-expr-selresolve)
    (list (implies (force (vl-exprlist-p x))
                   (vl-exprlist-p (mv-nth 1 (vl-exprlist-selresolve x warnings))))
          :name vl-exprlist-p-of-vl-exprlist-selresolve)
    :hints(("Goal"
            :induct (vl-flag-expr-selresolve flag x warnings)
            :expand ((vl-expr-selresolve x warnings)
                     (vl-exprlist-selresolve x warnings)))))

  (defthm-vl-flag-expr-selresolve lemma
    (expr (implies (force (vl-warninglist-p warnings))
                   (vl-warninglist-p (mv-nth 0 (vl-expr-selresolve x warnings))))
          :name vl-warninglist-p-of-vl-expr-selresolve)
    (list (implies (force (vl-warninglist-p warnings))
                   (vl-warninglist-p (mv-nth 0 (vl-exprlist-selresolve x warnings))))
          :name vl-warninglist-p-of-vl-exprlist-selresolve)
    :hints(("Goal"
            :induct (vl-flag-expr-selresolve flag x warnings)
            :expand ((vl-expr-selresolve x warnings)
                     (vl-exprlist-selresolve x warnings)))))

  (verify-guards vl-expr-selresolve))


(defmacro def-vl-selresolve (name &key type body)
  (let* ((name-s     (symbol-name name))
         (type-s     (symbol-name type))
         (thm-warn-s (cat "VL-WARNINGLIST-P-" name-s))
         (thm-type-s (cat type-s "-OF-" name-s))
         (thm-warn   (intern-in-package-of-symbol thm-warn-s name))
         (thm-type   (intern-in-package-of-symbol thm-type-s name)))
    `(defsection ,name

       (defund ,name (x warnings)
         (declare (xargs :guard (and (,type x)
                                     (vl-warninglist-p warnings))))
         ,body)

       (local (in-theory (enable ,name)))

      (defthm ,thm-warn
        (implies (force (vl-warninglist-p warnings))
                 (vl-warninglist-p (mv-nth 0 (,name x warnings)))))

      (defthm ,thm-type
        (implies (force (,type x))
                 (,type (mv-nth 1 (,name x warnings))))))))

(defmacro def-vl-selresolve-list (name &key type element)
  (let* ((name-s     (symbol-name name))
         (type-s     (symbol-name type))
         (thm-warn-s (cat "VL-WARNINGLIST-P-" name-s))
         (thm-type-s (cat type-s "-OF-" name-s))
         (thm-true-s (cat "TRUE-LISTP-OF-" name-s))
         (thm-warn   (intern-in-package-of-symbol thm-warn-s name))
         (thm-type   (intern-in-package-of-symbol thm-type-s name))
         (thm-true   (intern-in-package-of-symbol thm-true-s name)))
    `(defsection ,name

      (defund ,name (x warnings)
        (declare (xargs :guard (and (,type x)
                                    (vl-warninglist-p warnings))))
        (if (atom x)
            (mv warnings nil)
          (b* (((mv warnings car-prime) (,element (car x) warnings))
               ((mv warnings cdr-prime) (,name (cdr x) warnings)))
              (mv warnings (cons car-prime cdr-prime)))))

      (local (in-theory (enable ,name)))

      (defthm ,thm-warn
        (implies (force (vl-warninglist-p warnings))
                 (vl-warninglist-p (mv-nth 0 (,name x warnings)))))

      (defthm ,thm-type
        (implies (force (,type x))
                 (,type (mv-nth 1 (,name x warnings)))))

      (defthm ,thm-true
        (true-listp (mv-nth 1 (,name x warnings)))
        :rule-classes :type-prescription))))


(def-vl-selresolve vl-port-selresolve
  :type vl-port-p
  :body (b* ((expr (vl-port->expr x))
             ((when (not expr))
              (mv warnings x))
             ((mv warnings expr-prime)
              (vl-expr-selresolve expr warnings)))
          (mv warnings
              (change-vl-port x :expr expr-prime))))

(def-vl-selresolve-list vl-portlist-selresolve
  :type vl-portlist-p
  :element vl-port-selresolve)



(def-vl-selresolve vl-assign-selresolve
  :type vl-assign-p
  :body (b* (((mv warnings lvalue-prime)
              (vl-expr-selresolve (vl-assign->lvalue x) warnings))
             ((mv warnings expr-prime)
              (vl-expr-selresolve (vl-assign->expr x) warnings)))
            (mv warnings (change-vl-assign x
                                           :lvalue lvalue-prime
                                           :expr expr-prime))))

(def-vl-selresolve-list vl-assignlist-selresolve
  :type vl-assignlist-p
  :element vl-assign-selresolve)

(def-vl-selresolve vl-plainarg-selresolve
  :type vl-plainarg-p
  :body (b* ((expr (vl-plainarg->expr x))
             ((when (not expr))
              (mv warnings x))
             ((mv warnings expr-prime)
              (vl-expr-selresolve expr warnings)))
            (mv warnings
                (change-vl-plainarg x :expr expr-prime))))

(def-vl-selresolve-list vl-plainarglist-selresolve
  :type vl-plainarglist-p
  :element vl-plainarg-selresolve)

(def-vl-selresolve vl-namedarg-selresolve
  :type vl-namedarg-p
  :body (b* ((expr (vl-namedarg->expr x))
             ((when (not expr))
              (mv warnings x))
             ((mv warnings expr-prime)
              (vl-expr-selresolve expr warnings)))
            (mv warnings
                (change-vl-namedarg x :expr expr-prime))))

(def-vl-selresolve-list vl-namedarglist-selresolve
  :type vl-namedarglist-p
  :element vl-namedarg-selresolve)

(def-vl-selresolve vl-arguments-selresolve
  :type vl-arguments-p
  :body (b* ((namedp (vl-arguments->namedp x))
             (args   (vl-arguments->args x))
             ((mv warnings args-prime)
              (if namedp
                  (vl-namedarglist-selresolve args warnings)
                (vl-plainarglist-selresolve args warnings))))
            (mv warnings (vl-arguments namedp args-prime))))

(def-vl-selresolve vl-modinst-selresolve
  :type vl-modinst-p
  :body (b* (((mv warnings paramargs-prime)
              (vl-arguments-selresolve (vl-modinst->paramargs x) warnings))
             ((mv warnings portargs-prime)
              (vl-arguments-selresolve (vl-modinst->portargs x) warnings)))
            (mv warnings
                (change-vl-modinst x
                                   :paramargs paramargs-prime
                                   :portargs portargs-prime))))

(def-vl-selresolve-list vl-modinstlist-selresolve
  :type vl-modinstlist-p
  :element vl-modinst-selresolve)


(def-vl-selresolve vl-gateinst-selresolve
  :type vl-gateinst-p
  :body (b* (((mv warnings args-prime)
              (vl-plainarglist-selresolve (vl-gateinst->args x) warnings)))
            (mv warnings (change-vl-gateinst x :args args-prime))))

(def-vl-selresolve-list vl-gateinstlist-selresolve
  :type vl-gateinstlist-p
  :element vl-gateinst-selresolve)



(def-vl-selresolve vl-delaycontrol-selresolve
  :type vl-delaycontrol-p
  :body (b* (((mv warnings value-prime)
              (vl-expr-selresolve (vl-delaycontrol->value x) warnings))
             (x-prime
              (change-vl-delaycontrol x :value value-prime)))
            (mv warnings x-prime)))

(def-vl-selresolve vl-evatom-selresolve
  :type vl-evatom-p
  :body (b* (((mv warnings expr-prime)
              (vl-expr-selresolve (vl-evatom->expr x) warnings))
             (x-prime
              (change-vl-evatom x :expr expr-prime)))
            (mv warnings x-prime)))

(def-vl-selresolve-list vl-evatomlist-selresolve
  :type vl-evatomlist-p
  :element vl-evatom-selresolve)

(def-vl-selresolve vl-eventcontrol-selresolve
  :type vl-eventcontrol-p
  :body (b* (((mv warnings atoms-prime)
              (vl-evatomlist-selresolve (vl-eventcontrol->atoms x) warnings))
             (x-prime
              (change-vl-eventcontrol x :atoms atoms-prime)))
            (mv warnings x-prime)))

(def-vl-selresolve vl-repeateventcontrol-selresolve
  :type vl-repeateventcontrol-p
  :body (b* (((mv warnings expr-prime)
              (vl-expr-selresolve (vl-repeateventcontrol->expr x) warnings))
             ((mv warnings ctrl-prime)
              (vl-eventcontrol-selresolve (vl-repeateventcontrol->ctrl x) warnings))
             (x-prime
              (change-vl-repeateventcontrol x
                                            :expr expr-prime
                                            :ctrl ctrl-prime)))
            (mv warnings x-prime)))

(encapsulate
 ()
 (local (in-theory (disable vl-delayoreventcontrol-p-when-vl-maybe-delayoreventcontrol-p)))
 (def-vl-selresolve vl-delayoreventcontrol-selresolve
   :type vl-delayoreventcontrol-p
   :body (case (tag x)
           (:vl-delaycontrol (vl-delaycontrol-selresolve x warnings))
           (:vl-eventcontrol (vl-eventcontrol-selresolve x warnings))
           (:vl-repeat-eventcontrol (vl-repeateventcontrol-selresolve x warnings))
           (otherwise
            (mv (er hard 'vl-delayoreventcontrol-p
                    "Impossible case.  This is not really an error.  We are just ~
                     using the guard mechanism to prove that all cases have been ~
                     covered.")
                x)))))

(def-vl-selresolve vl-maybe-delayoreventcontrol-selresolve
  :type vl-maybe-delayoreventcontrol-p
  :body (if x
            (vl-delayoreventcontrol-selresolve x warnings)
          (mv warnings nil)))

(defthm vl-maybe-delayoreventcontrol-selresolve-under-iff
  (implies (force (vl-maybe-delayoreventcontrol-p x))
           (iff (mv-nth 1 (vl-maybe-delayoreventcontrol-selresolve x warnings))
                x))
  :hints(("Goal"
          :in-theory (e/d (vl-maybe-delayoreventcontrol-selresolve
                           vl-maybe-delayoreventcontrol-p)
                          (vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-selresolve))
          :use ((:instance vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-selresolve)))))



(def-vl-selresolve vl-assignstmt-selresolve
  :type vl-assignstmt-p
  :body (b* (((mv warnings lvalue-prime)
              (vl-expr-selresolve (vl-assignstmt->lvalue x) warnings))
             ((mv warnings expr-prime)
              (vl-expr-selresolve (vl-assignstmt->expr x) warnings))
             ((mv warnings ctrl-prime)
              (vl-maybe-delayoreventcontrol-selresolve (vl-assignstmt->ctrl x) warnings)))
            (mv warnings (change-vl-assignstmt x
                                               :lvalue lvalue-prime
                                               :expr expr-prime
                                               :ctrl ctrl-prime))))

(def-vl-selresolve vl-deassignstmt-selresolve
  :type vl-deassignstmt-p
  :body (b* (((mv warnings lvalue-prime)
              (vl-expr-selresolve (vl-deassignstmt->lvalue x) warnings)))
            (mv warnings (change-vl-deassignstmt x :lvalue lvalue-prime))))

(def-vl-selresolve vl-enablestmt-selresolve
  :type vl-enablestmt-p
  :body (b* (((mv warnings id-prime)
              (vl-expr-selresolve (vl-enablestmt->id x) warnings))
             ((mv warnings args-prime)
              (vl-exprlist-selresolve (vl-enablestmt->args x) warnings)))
            (mv warnings (change-vl-enablestmt x
                                               :id id-prime
                                               :args args-prime))))

(def-vl-selresolve vl-disablestmt-selresolve
  :type vl-disablestmt-p
  :body (b* (((mv warnings id-prime)
              (vl-expr-selresolve (vl-disablestmt->id x) warnings)))
            (mv warnings (change-vl-disablestmt x :id id-prime))))

(def-vl-selresolve vl-eventtriggerstmt-selresolve
  :type vl-eventtriggerstmt-p
  :body (b* (((mv warnings id-prime)
              (vl-expr-selresolve (vl-eventtriggerstmt->id x) warnings)))
            (mv warnings (change-vl-eventtriggerstmt x :id id-prime))))

(def-vl-selresolve vl-atomicstmt-selresolve
  :type vl-atomicstmt-p
  :body (case (tag x)
          (:vl-nullstmt         (mv warnings x))
          (:vl-assignstmt       (vl-assignstmt-selresolve x warnings))
          (:vl-deassignstmt     (vl-deassignstmt-selresolve x warnings))
          (:vl-enablestmt       (vl-enablestmt-selresolve x warnings))
          (:vl-disablestmt      (vl-disablestmt-selresolve x warnings))
          (:vl-eventtriggerstmt (vl-eventtriggerstmt-selresolve x warnings))
          (otherwise
           (mv (er hard 'vl-atomicstmt-selresolve
                   "Impossible case.   This is not really an error.  We are just ~
                    using the guard mechanism to prove that all cases have been ~
                    covered.")
               x))))


(defsection vl-stmt-selresolve

  (mutual-recursion

   (defund vl-stmt-selresolve (x warnings)
     (declare (xargs :guard (and (vl-stmt-p x)
                                 (vl-warninglist-p warnings))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (if (vl-fast-atomicstmt-p x)
         (vl-atomicstmt-selresolve x warnings)
       (b* (((mv warnings exprs-prime)
             (vl-exprlist-selresolve (vl-compoundstmt->exprs x) warnings))
            ((mv warnings stmts-prime)
             (vl-stmtlist-selresolve (vl-compoundstmt->stmts x) warnings))
            ((mv warnings ctrl-prime)
             (vl-maybe-delayoreventcontrol-selresolve (vl-compoundstmt->ctrl x) warnings))
            (x-prime
             (change-vl-compoundstmt x
                                     :exprs exprs-prime
                                     :stmts stmts-prime
                                     :ctrl ctrl-prime)))
         (mv warnings x-prime))))

   (defund vl-stmtlist-selresolve (x warnings)
     (declare (xargs :guard (and (vl-stmtlist-p x)
                                 (vl-warninglist-p warnings))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         (mv warnings nil)
       (b* (((mv warnings car-prime) (vl-stmt-selresolve (car x) warnings))
            ((mv warnings cdr-prime) (vl-stmtlist-selresolve (cdr x) warnings)))
         (mv warnings (cons car-prime cdr-prime))))))

  (FLAG::make-flag vl-flag-stmt-selresolve
                   vl-stmt-selresolve
                   :flag-mapping ((vl-stmt-selresolve . stmt)
                                  (vl-stmtlist-selresolve . list)))

  (defthm-vl-flag-stmt-selresolve lemma
    (stmt (implies (force (vl-warninglist-p warnings))
                   (vl-warninglist-p (mv-nth 0 (vl-stmt-selresolve x warnings))))
          :name vl-warninglist-p-of-vl-stmt-selresolve)
    (list (implies (force (vl-warninglist-p warnings))
                   (vl-warninglist-p (mv-nth 0 (vl-stmtlist-selresolve x warnings))))
          :name vl-warninglist-p-of-vl-stmtlist-selresolve)
    :hints(("Goal"
            :induct (vl-flag-stmt-selresolve flag x warnings)
            :expand ((vl-stmt-selresolve x warnings)
                     (vl-stmtlist-selresolve x warnings)))))

  (defthm vl-stmtlist-selresolve-when-not-consp
    (implies (not (consp x))
             (equal (vl-stmtlist-selresolve x warnings)
                    (mv warnings nil)))
    :hints(("Goal" :in-theory (enable vl-stmtlist-selresolve))))

  (defthm vl-stmtlist-selresolve-of-cons
    (equal (vl-stmtlist-selresolve (cons a x) warnings)
           (b* (((mv warnings car-prime) (vl-stmt-selresolve a warnings))
                ((mv warnings cdr-prime) (vl-stmtlist-selresolve x warnings)))
             (mv warnings (cons car-prime cdr-prime))))
    :hints(("Goal" :in-theory (enable vl-stmtlist-selresolve))))

  (local (defun my-induction (x warnings)
           (if (atom x)
               (mv warnings x)
             (b* (((mv warnings car-prime) (vl-stmt-selresolve (car x) warnings))
                  ((mv warnings cdr-prime) (my-induction (cdr x) warnings)))
               (mv warnings (cons car-prime cdr-prime))))))

  (defthm len-of-vl-stmtlist-selresolve
    (equal (len (mv-nth 1 (vl-stmtlist-selresolve x warnings)))
           (len x))
    :hints(("Goal" :induct (my-induction x warnings))))

  (defthm-vl-flag-stmt-selresolve lemma
    (stmt (implies (force (vl-stmt-p x))
                   (vl-stmt-p (mv-nth 1 (vl-stmt-selresolve x warnings))))
          :name vl-stmt-p-of-vl-stmt-selresolve)
    (list (implies (force (vl-stmtlist-p x))
                   (vl-stmtlist-p (mv-nth 1 (vl-stmtlist-selresolve x warnings))))
          :name vl-stmtlist-p-of-vl-stmtlist-selresolve)
    :hints(("Goal"
            :induct (vl-flag-stmt-selresolve flag x warnings)
            :expand ((vl-stmt-selresolve x warnings)
                     (vl-stmtlist-selresolve x warnings)))))

  (verify-guards vl-stmt-selresolve))

(def-vl-selresolve vl-always-selresolve
  :type vl-always-p
  :body (b* (((mv warnings stmt-prime)
              (vl-stmt-selresolve (vl-always->stmt x) warnings)))
            (mv warnings (change-vl-always x :stmt stmt-prime))))

(def-vl-selresolve-list vl-alwayslist-selresolve
  :type vl-alwayslist-p
  :element vl-always-selresolve)


(def-vl-selresolve vl-initial-selresolve
  :type vl-initial-p
  :body (b* (((mv warnings stmt-prime)
              (vl-stmt-selresolve (vl-initial->stmt x) warnings)))
            (mv warnings (change-vl-initial x :stmt stmt-prime))))

(def-vl-selresolve-list vl-initiallist-selresolve
  :type vl-initiallist-p
  :element vl-initial-selresolve)

(def-vl-selresolve vl-fundecl-selresolve
  :type vl-fundecl-p
  :body
  (b* (((vl-fundecl x) x)
       ((mv warnings body) (vl-stmt-selresolve x.body warnings)))
    (mv warnings
        (change-vl-fundecl x :body body))))

(def-vl-selresolve-list vl-fundecllist-selresolve
  :type vl-fundecllist-p
  :element vl-fundecl-selresolve)


(defsection vl-module-selresolve

  (defund vl-module-selresolve (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* (((when (vl-module->hands-offp x))
          x)
         ((vl-module x) x)
         (warnings                x.warnings)
         ((mv warnings ports)     (vl-portlist-selresolve x.ports warnings))
         ((mv warnings assigns)   (vl-assignlist-selresolve x.assigns warnings))
         ((mv warnings modinsts)  (vl-modinstlist-selresolve x.modinsts warnings))
         ((mv warnings gateinsts) (vl-gateinstlist-selresolve x.gateinsts warnings))
         ((mv warnings alwayses)  (vl-alwayslist-selresolve x.alwayses warnings))
         ((mv warnings initials)  (vl-initiallist-selresolve x.initials warnings))
         ((mv warnings fundecls)  (vl-fundecllist-selresolve x.fundecls warnings)))
      (change-vl-module x
                        :ports ports
                        :warnings warnings
                        :assigns assigns
                        :modinsts modinsts
                        :gateinsts gateinsts
                        :alwayses alwayses
                        :initials initials
                        :fundecls fundecls)))

  (local (in-theory (enable vl-module-selresolve)))

  (defthm vl-module-p-of-vl-module-selresolve
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-selresolve x))))

  (defthm vl-module->name-of-vl-module-selresolve
    (equal (vl-module->name (vl-module-selresolve x))
           (vl-module->name x))))


(defsection vl-modulelist-selresolve

  (defprojection vl-modulelist-selresolve (x)
    (vl-module-selresolve x)
    :guard (vl-modulelist-p x)
    :result-type vl-modulelist-p)

  (local (in-theory (enable vl-modulelist-selresolve)))

  (defthm vl-modulelist->names-of-vl-modulelist-selresolve
    (equal (vl-modulelist->names (vl-modulelist-selresolve x))
           (vl-modulelist->names x))))
