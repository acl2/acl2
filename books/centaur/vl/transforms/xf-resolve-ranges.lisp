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
(include-book "../mlib/consteval")
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
these expressions.</p>")

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
       ((mv msb-ok msb) (vl-consteval x.msb))
       ((mv lsb-ok lsb) (vl-consteval x.lsb))
       ((unless (and msb-ok lsb-ok))
        ;; Failure, just return the unreduced range.
        (mv (warn :type :vl-bad-range
                  ;; BOZO need some context
                  :msg "Unable to safely resolve range ~a0."
                  :args (list x))
            x))
       ;; We could create a new range that just had the reduced MSB and LSB
       ;; here.  However, we don't really care at all about the width/type
       ;; of the resulting expressions.  That is, nobody wants to see:
       ;;
       ;;    wire [4'd3 : 4'd0] foo;
       ;;
       ;; So since the widths/types don't matter, we'll just use VL-MAKE-INDEX
       ;; to recreate the indices; it does something clever for 32-bit integers
       ;; to make them look like they're unsized.
       (msb (vl-make-index (vl-resolved->val msb)))
       (lsb (vl-make-index (vl-resolved->val lsb))))
    (mv (ok) (hons-copy (make-vl-range :msb msb :lsb lsb)))))

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
      (:vl-nettype
       (b* (((mv warnings range) (vl-maybe-rangeresolve x.range warnings)))
         (mv warnings (change-vl-nettype x :range range))))
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

(def-vl-rangeresolve vl-maybe-datatype
  :body (if (not x)
            (mv (ok) nil)
          (vl-datatype-rangeresolve x warnings)))

(def-vl-rangeresolve vl-portdecl
  :body (b* (((vl-portdecl x) x)
             ((mv warnings type) (vl-datatype-rangeresolve x.type warnings)))
            (mv warnings (change-vl-portdecl x :type type))))

(def-vl-rangeresolve-list vl-portdecllist :element vl-portdecl)

(def-vl-rangeresolve vl-vardecl
  :body (b* (((vl-vardecl x) x)
             ((mv warnings type) (vl-datatype-rangeresolve x.type warnings))
             ((mv warnings dims) (vl-packeddimensionlist-rangeresolve x.dims warnings)))
          (mv warnings (change-vl-vardecl x
                                          :type type
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

(def-vl-rangeresolve vl-paramtype
  :body
  (vl-paramtype-case x
    (:vl-implicitvalueparam
     (b* (((mv warnings range-prime)   (vl-maybe-rangeresolve x.range warnings))
          (x-prime                     (change-vl-implicitvalueparam x :range range-prime)))
       (mv warnings x-prime)))
    (:vl-explicitvalueparam
     (b* (((mv warnings type-prime)    (vl-datatype-rangeresolve x.type warnings))
          (x-prime                     (change-vl-explicitvalueparam x :type type-prime)))
       (mv warnings x-prime)))
    (:vl-typeparam
     (b* (((mv warnings default-prime) (vl-maybe-datatype-rangeresolve x.default warnings))
          (x-prime                     (change-vl-typeparam x :default default-prime)))
       (mv warnings x-prime)))))

(def-vl-rangeresolve vl-paramdecl
  :body (b* (((vl-paramdecl x) x)
             ((mv warnings type) (vl-paramtype-rangeresolve x.type warnings)))
          (mv warnings (change-vl-paramdecl x :type type))))

(def-vl-rangeresolve-list vl-paramdecllist :element vl-paramdecl)

(def-vl-rangeresolve vl-taskport
  :body (b* (((vl-taskport x) x)
             ((mv warnings range) (vl-maybe-rangeresolve x.range warnings)))
          (mv warnings (change-vl-taskport x :range range))))

(def-vl-rangeresolve-list vl-taskportlist :element vl-taskport)

(def-vl-rangeresolve vl-blockitem
  :body (case (tag x)
          (:vl-vardecl   (vl-vardecl-rangeresolve   x warnings))
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
       ((mv warnings vardecls)   (vl-vardecllist-rangeresolve   x.vardecls   warnings))
       ((mv warnings modinsts)   (vl-modinstlist-rangeresolve   x.modinsts   warnings))
       ((mv warnings gateinsts)  (vl-gateinstlist-rangeresolve  x.gateinsts  warnings))
       ((mv warnings fundecls)   (vl-fundecllist-rangeresolve   x.fundecls   warnings))
       ;; BOZO may eventually want to resolve ranges in block items within statements.
       )
      (change-vl-module x
                        :warnings   warnings
                        :portdecls  portdecls
                        :vardecls   vardecls
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

