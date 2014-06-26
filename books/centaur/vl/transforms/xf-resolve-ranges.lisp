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
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

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

(defmacro def-vl-rangeresolve (name &key fn body)
  (b* ((mksym-package-symbol (pkg-witness "VL"))
       (fn   (or fn (mksym name '-rangeresolve)))
       (type (mksym name '-p))
       (fix  (mksym name '-fix)))
    `(define ,fn ((x ,type)
                    (warnings vl-warninglist-p))
       :returns (mv (warnings vl-warninglist-p)
                    (new-x ,type))
       (b* ((x        (,fix x))
            (warnings (vl-warninglist-fix warnings)))
         ,body))))

(defmacro def-vl-rangeresolve-list (name &key element element-fn)
  (b* ((mksym-package-symbol (pkg-witness "VL"))
       (fn      (mksym name '-rangeresolve))
       (type    (mksym name '-p))
       (elem-fn (or element-fn (mksym element '-rangeresolve))))
    `(define ,fn ((x ,type)
                  (warnings vl-warninglist-p))
       :returns (mv (warnings vl-warninglist-p)
                    (new-x ,type))
       (b* (((when (atom x))
             (mv (ok) nil))
            ((mv warnings car-prime) (,elem-fn (car x) warnings))
            ((mv warnings cdr-prime) (,fn (cdr x) warnings)))
         (mv warnings (cons car-prime cdr-prime)))
       ///
       (defmvtypes ,fn (nil true-listp)))))

(def-vl-rangeresolve vl-range
  :fn vl-rangeresolve
  :body
  (b* (((vl-range x) x)
       (msb-val (vl-constexpr-reduce x.msb))
       (lsb-val (vl-constexpr-reduce x.lsb)))
    (if (and msb-val lsb-val)
        ;; Ordinary case, build a new range.  We could probably use
        ;; vl-make-index here instead of constructing these manually, but
        ;; it produces sized results and maybe it's slightly better not
        ;; to size these yet.  Hrmn.  It probably doesn't matter.
        ;; Whatever.
        (mv (ok)
            (hons-copy (make-vl-range
                        :msb (make-vl-atom
                              :guts (make-vl-constint :origwidth 32
                                                      :origtype :vl-signed
                                                      :value msb-val
                                                      :wasunsized t))
                        :lsb (make-vl-atom
                              :guts (make-vl-constint :origwidth 32
                                                      :origtype :vl-signed
                                                      :value lsb-val
                                                      :wasunsized t)))))
      ;; Failure, just return the unreduced range.
      (mv (warn :type :vl-bad-range
                ;; BOZO need some context
                :msg "Unable to safely resolve range ~a0."
                :args (list x))
          x))))

(def-vl-rangeresolve vl-maybe-range
  :fn vl-maybe-rangeresolve
  :body
  (if (not x)
      (mv (ok) nil)
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

(def-vl-rangeresolve-list vl-rangelist
  :element vl-range
  :element-fn vl-rangeresolve)

(def-vl-rangeresolve vl-packeddimension
  :body (if (eq x :vl-unsized-dimension)
            (mv (ok) x)
          (vl-rangeresolve x warnings)))

(def-vl-rangeresolve-list vl-packeddimensionlist
  :element vl-packeddimension)

(def-vl-rangeresolve vl-maybe-packeddimension
  :body (if (not x)
            (mv (ok) nil)
          (vl-packeddimension-rangeresolve x warnings)))

(def-vl-rangeresolve vl-enumbasetype
  :body (b* (((vl-enumbasetype x) x)
             ((mv warnings dim) (vl-maybe-packeddimension-rangeresolve x.dim warnings)))
          (mv warnings (change-vl-enumbasetype x :dim dim))))

(def-vl-rangeresolve vl-enumitem
  :body (b* (((vl-enumitem x) x)
             ((mv warnings range) (vl-maybe-rangeresolve x.range warnings)))
          (mv warnings (change-vl-enumitem x :range range))))

(def-vl-rangeresolve-list vl-enumitemlist
  :element vl-enumitem)

(defines vl-datatype-rangeresolve
  :verify-guards nil

  (define vl-datatype-rangeresolve ((x        vl-datatype-p)
                                    (warnings vl-warninglist-p))
    :measure (vl-datatype-count x)
    :returns (mv (warnings vl-warninglist-p)
                 (new-x vl-datatype-p))
    (vl-datatype-case x
      (:vl-coretype
       (b* (((mv warnings dims) (vl-packeddimensionlist-rangeresolve x.dims warnings)))
         (mv warnings (change-vl-coretype x :dims dims))))
      (:vl-struct
       (b* (((mv warnings dims)    (vl-packeddimensionlist-rangeresolve x.dims warnings))
            ((mv warnings members) (vl-structmemberlist-rangeresolve x.members warnings)))
         (mv warnings (change-vl-struct x
                                        :dims dims
                                        :members members))))
      (:vl-union
       (b* (((mv warnings dims)    (vl-packeddimensionlist-rangeresolve x.dims warnings))
            ((mv warnings members) (vl-structmemberlist-rangeresolve x.members warnings)))
         (mv warnings (change-vl-union x
                                        :dims dims
                                        :members members))))
      (:vl-enum
       (b* (((mv warnings basetype) (vl-enumbasetype-rangeresolve x.basetype warnings))
            ((mv warnings items)    (vl-enumitemlist-rangeresolve x.items warnings))
            ((mv warnings dims)     (vl-packeddimensionlist-rangeresolve x.dims warnings)))
         (mv warnings (change-vl-enum x
                                      :basetype basetype
                                      :items    items
                                      :dims     dims))))
      (:vl-usertype
       (b* (((mv warnings dims) (vl-packeddimensionlist-rangeresolve x.dims warnings)))
         (mv warnings (change-vl-usertype x
                                          :dims dims))))))

  (define vl-structmemberlist-rangeresolve ((x vl-structmemberlist-p)
                                            (warnings vl-warninglist-p))
    :measure (vl-structmemberlist-count x)
    :returns (mv (warnings vl-warninglist-p)
                 (new-x vl-structmemberlist-p))
    (b* (((when (atom x))
          (mv (ok) nil))
         ((mv warnings x1) (vl-structmember-rangeresolve (car x) warnings))
         ((mv warnings x2) (vl-structmemberlist-rangeresolve (cdr x) warnings)))
      (mv warnings (cons x1 x2))))

  (define vl-structmember-rangeresolve ((x vl-structmember-p)
                                        (warnings vl-warninglist-p))
    :measure (vl-structmember-count x)
    :returns (mv (warnings vl-warninglist-p)
                 (new-x vl-structmember-p))
    (b* (((vl-structmember x) x)
         ((mv warnings type) (vl-datatype-rangeresolve x.type warnings))
         ((mv warnings dims) (vl-packeddimensionlist-rangeresolve x.dims warnings)))
      (mv warnings (change-vl-structmember x
                                           :type type
                                           :dims dims))))
  ///
  (verify-guards vl-datatype-rangeresolve)
  (deffixequiv-mutual vl-datatype-rangeresolve))

(def-vl-rangeresolve vl-portdecl
  :body (b* (((vl-portdecl x) x)
             ((mv warnings range) (vl-maybe-rangeresolve x.range warnings)))
            (mv warnings (change-vl-portdecl x :range range))))

(def-vl-rangeresolve-list vl-portdecllist :element vl-portdecl)

(def-vl-rangeresolve vl-netdecl
  :body (b* (((vl-netdecl x) x)
             ((mv warnings range)   (vl-maybe-rangeresolve x.range warnings))
             ((mv warnings arrdims) (vl-rangelist-rangeresolve x.arrdims warnings)))
          (mv warnings (change-vl-netdecl x
                                          :range   range
                                          :arrdims arrdims))))

(def-vl-rangeresolve-list vl-netdecllist :element vl-netdecl)

(def-vl-rangeresolve vl-vardecl
  :body (b* (((vl-vardecl x) x)
             ((mv warnings vartype) (vl-datatype-rangeresolve x.vartype warnings))
             ((mv warnings dims)    (vl-packeddimensionlist-rangeresolve x.dims warnings)))
          (mv warnings (change-vl-vardecl x
                                          :vartype vartype
                                          :dims dims))))

(def-vl-rangeresolve-list vl-vardecllist :element vl-vardecl)

(def-vl-rangeresolve vl-modinst
  :body (b* (((vl-modinst x) x)
             ((mv warnings range) (vl-maybe-rangeresolve x.range warnings)))
          (mv warnings (change-vl-modinst x :range range))))

(def-vl-rangeresolve-list vl-modinstlist :element vl-modinst)

(def-vl-rangeresolve vl-gateinst
  :body (b* (((vl-gateinst x) x)
             ((mv warnings range) (vl-maybe-rangeresolve x.range warnings)))
          (mv warnings (change-vl-gateinst x :range range))))

(def-vl-rangeresolve-list vl-gateinstlist :element vl-gateinst)

(def-vl-rangeresolve vl-paramdecl
  :body (b* (((vl-paramdecl x) x)
             ((mv warnings range) (vl-maybe-rangeresolve x.range warnings)))
          (mv warnings (change-vl-paramdecl x :range range))))

(def-vl-rangeresolve-list vl-paramdecllist :element vl-paramdecl)

(def-vl-rangeresolve vl-eventdecl
  :body (b* (((vl-eventdecl x) x)
             ((mv warnings arrdims) (vl-rangelist-rangeresolve x.arrdims warnings)))
          (mv warnings (change-vl-eventdecl x :arrdims arrdims))))

(def-vl-rangeresolve-list vl-eventdecllist :element vl-eventdecl)

(def-vl-rangeresolve vl-taskport
  :body (b* (((vl-taskport x) x)
             ((mv warnings range) (vl-maybe-rangeresolve x.range warnings)))
          (mv warnings (change-vl-taskport x :range range))))

(def-vl-rangeresolve-list vl-taskportlist :element vl-taskport)

(def-vl-rangeresolve vl-blockitem
  :body (case (tag x)
          (:vl-vardecl   (vl-vardecl-rangeresolve   x warnings))
          (:vl-eventdecl (vl-eventdecl-rangeresolve x warnings))
          (otherwise     (vl-paramdecl-rangeresolve x warnings))))

(def-vl-rangeresolve-list vl-blockitemlist :element vl-blockitem)

(def-vl-rangeresolve vl-fundecl
  :body (b* (((vl-fundecl x) x)
             ((mv warnings rrange) (vl-maybe-rangeresolve x.rrange warnings))
             ((mv warnings decls)  (vl-blockitemlist-rangeresolve x.decls warnings))
             ((mv warnings inputs) (vl-taskportlist-rangeresolve x.inputs warnings)))
          (mv warnings (change-vl-fundecl x
                                          :rrange rrange
                                          :decls  decls
                                          :inputs inputs))))

(def-vl-rangeresolve-list vl-fundecllist :element vl-fundecl)

(define vl-module-rangeresolve ((x vl-module-p))
  :returns (new-x vl-module-p)
  (b* (((vl-module x) x)
       ((when (vl-module->hands-offp x))
        (vl-module-fix x))
       (warnings                 x.warnings)
       ((mv warnings portdecls)  (vl-portdecllist-rangeresolve  x.portdecls  warnings))
       ((mv warnings netdecls)   (vl-netdecllist-rangeresolve   x.netdecls   warnings))
       ((mv warnings vardecls)   (vl-vardecllist-rangeresolve   x.vardecls   warnings))
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
                        :eventdecls eventdecls
                        :modinsts   modinsts
                        :gateinsts  gateinsts
                        :fundecls   fundecls)))

(defprojection vl-modulelist-rangeresolve ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-rangeresolve x))

(define vl-design-rangeresolve ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x)
       (new-mods (vl-modulelist-rangeresolve x.mods)))
    (change-vl-design x :mods new-mods)))

