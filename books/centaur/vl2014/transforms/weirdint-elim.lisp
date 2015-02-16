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
(include-book "../primitives")
(include-book "../mlib/modgen")
(include-book "../mlib/namefactory")
(include-book "../mlib/allexprs")
(include-book "../mlib/stmt-tools")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))
(local (std::add-default-post-define-hook :fix))

(defxdoc weirdint-elim
  :parents (transforms)
  :short "Replace integer literals with X and Z values with concatenations of
generated wires."

  :long "<p>In this transformation, we replace any @(see vl-weirdint-p) atoms
with concatenations of the special wires @('vl-x-value') and
@('vl-z-value') (for X and Z bits), and one-bit constants @('1'b0') and
@('1'b1') (for 1 and 0 bits).  If necessary, we then add instances of the
primitive @(see *vl-1-bit-x*) and @(see *vl-1-bit-z*) modules to drive the X
and Z wires.</p>

<p>The net effect is that after this transformation, no modules besides
@('VL_1_BIT_X') and @('VL_1_BIT_Z') will contain any weird literals.  This
transformation is convenient for our conversion to E, where X and Z are not
valid literals.</p>

<h3>Order Considerations</h3>

<p>This must be done after occform, or it will interfere with the creation
of Z muxes.</p>")

(local (xdoc::set-default-parents weirdint-elim))

(defval *vl-x-wire-expr*
  (vl-idexpr "vl-x-wire" 1 :vl-unsigned))

(defval *vl-z-wire-expr*
  (vl-idexpr "vl-z-wire" 1 :vl-unsigned))


; We assume all sizing has already been done, so we need to produce full size
; and signedness information on all numbers we introduce.

(define vl-weirdint-bits-to-exprs
  :short "Translate MSB-first bits from a weirdint into expressions, which
will become the arguments to a concatenation."
  ((bits vl-bitlist-p))
  :returns (exprs vl-exprlist-p
                  "Any 0 bits become 1'b0, 1 bits become 1'b1, Z bits
                   become vl-z-wire, and X bits become vl-x-wire.")
  (if (atom bits)
      nil
    (cons (case (vl-bit-fix (car bits))
            (:vl-0val |*sized-1'b0*|)
            (:vl-1val |*sized-1'b1*|)
            (:vl-xval *vl-x-wire-expr*)
            (:vl-zval *vl-z-wire-expr*))
          (vl-weirdint-bits-to-exprs (cdr bits)))))

(define vl-weirdint-to-concat
  ((x        vl-weirdint-p)
   (warnings vl-warninglist-p))
   :returns (mv (warnings vl-warninglist-p)
                (concat vl-expr-p))
   (b* ((x (vl-weirdint-fix x))
        ((vl-weirdint x) x)
        ((when (eq x.origtype :vl-signed))
         (mv (fatal :type :vl-unsupported
                    :msg "Don't want to think about signed weirdints, but found ~a0."
                    :args (list x))
             ;; Build an equivalent expr to use as the default value
             (make-vl-atom :guts x
                           :finalwidth x.origwidth
                           :finaltype :vl-signed))))
     (mv (ok)
         (make-vl-nonatom :op :vl-concat
                          :args (vl-weirdint-bits-to-exprs x.bits)
                          :finalwidth x.origwidth
                          :finaltype :vl-unsigned))))

(defines vl-expr-weirdint-elim

  (define vl-expr-weirdint-elim ((x        vl-expr-p)
                                 (warnings vl-warninglist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (changedp booleanp :rule-classes :type-prescription)
                 (new-x vl-expr-p))
    :verify-guards nil
    :measure (vl-expr-count x)
    :flag :expr
    (b* ((x (vl-expr-fix x))
         ((when (vl-fast-atom-p x))
          (b* (((unless (vl-fast-weirdint-p (vl-atom->guts x)))
                ;; Nothing needs to be changed.
                (mv (ok) nil x))

               (guts (vl-atom->guts x))
               ((unless (and (posp (vl-expr->finalwidth x))
                             (eql (vl-expr->finalwidth x)
                                  (vl-weirdint->origwidth guts))))
                ;; Probably unnecessary extra sanity check.
                (mv (fatal :type :vl-programming-error
                           :msg "Bad widths on weirdint: ~x0."
                           :args (list x))
                    nil x))
               ((mv warnings concat)
                (vl-weirdint-to-concat guts warnings)))
             (mv warnings t concat)))

         ((mv warnings changedp args-prime)
          (vl-exprlist-weirdint-elim (vl-nonatom->args x) warnings))

         (x-prime (if changedp
                      (change-vl-nonatom x :args args-prime)
                    x)))
      (mv warnings changedp x-prime)))

  (define vl-exprlist-weirdint-elim ((x        vl-exprlist-p)
                                     (warnings vl-warninglist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (changedp booleanp :rule-classes :type-prescription)
                 (new-x (and (vl-exprlist-p new-x)
                             (equal (len new-x) (len x)))))
    :measure (vl-exprlist-count x)
    :flag :list
    (b* (((when (atom x))
          (mv (ok) nil nil))
         ((mv warnings car-changedp car-prime)
          (vl-expr-weirdint-elim (car x) warnings))
         ((mv warnings cdr-changedp cdr-prime)
          (vl-exprlist-weirdint-elim (cdr x) warnings))
         (changedp (or car-changedp cdr-changedp))
         (x-prime  (if changedp
                       (cons car-prime cdr-prime)
                     (vl-exprlist-fix x))))
      (mv warnings changedp x-prime)))
  ///
  (verify-guards vl-expr-weirdint-elim)
  (deffixequiv-mutual vl-expr-weirdint-elim))

(defmacro def-vl-weirdint-elim (name &key body)
  (b* ((mksym-package-symbol (pkg-witness "VL2014"))
       (fn   (mksym name '-weirdint-elim))
       (type (mksym name '-p))
       (fix  (mksym name '-fix)))
  `(define ,fn ((x ,type)
                  (warnings vl-warninglist-p))
     :returns (mv (warnings vl-warninglist-p)
                  (changedp booleanp :rule-classes :type-prescription)
                  (x-prime ,type))
     (b* ((x (,fix x)))
       ,body))))


(defmacro def-vl-weirdint-elim-list (name &key element)
  (b* ((mksym-package-symbol (pkg-witness "VL2014"))
       (fn      (mksym name '-weirdint-elim))
       (elem-fn (mksym element '-weirdint-elim))
       (type    (mksym name '-p))
       (fix     (mksym name '-fix)))
    `(define ,fn ((x ,type)
                    (warnings vl-warninglist-p))
       :returns (mv (warnings vl-warninglist-p)
                    (changedp booleanp :rule-classes :type-prescription)
                    (new-x ,type))
       (b* (((when (atom x))
             (mv (ok) nil nil))
            ((mv warnings car-changedp car-prime) (,elem-fn (car x) warnings))
            ((mv warnings cdr-changedp cdr-prime) (,fn (cdr x) warnings))
            (changedp (or car-changedp cdr-changedp))
            (x-prime  (if changedp
                          (cons car-prime cdr-prime)
                        (,fix x))))
         (mv warnings changedp x-prime)))))

(def-vl-weirdint-elim vl-maybe-expr
  :body (if (not x)
            (mv (ok) nil nil)
          (vl-expr-weirdint-elim x warnings)))

(def-vl-weirdint-elim vl-assign
  :body
  (b* (((vl-assign x) x)
       ((mv warnings lvalue-changedp lvalue) (vl-expr-weirdint-elim x.lvalue warnings))
       ((mv warnings expr-changedp expr)     (vl-expr-weirdint-elim x.expr warnings))
       (changedp (or lvalue-changedp expr-changedp))
       (x-prime  (if changedp
                     (change-vl-assign x
                                       :lvalue lvalue
                                       :expr expr)
                   x)))
    (mv warnings changedp x-prime)))

(def-vl-weirdint-elim-list vl-assignlist :element vl-assign)

(def-vl-weirdint-elim vl-plainarg
  :body
  (b* (((vl-plainarg x) x)
       ((unless x.expr)
        (mv (ok) nil x))
       ((mv warnings expr-changedp expr-prime) (vl-expr-weirdint-elim x.expr warnings))
       (changedp expr-changedp)
       (x-prime  (if changedp
                     (change-vl-plainarg x :expr expr-prime)
                   x)))
    (mv warnings changedp x-prime)))

(def-vl-weirdint-elim-list vl-plainarglist :element vl-plainarg)

(def-vl-weirdint-elim vl-namedarg
  :body
  (b* (((vl-namedarg x) x)
       ((unless x.expr)
        (mv (ok) nil x))
       ((mv warnings expr-changedp expr-prime) (vl-expr-weirdint-elim x.expr warnings))
       (changedp expr-changedp)
       (x-prime  (if changedp
                     (change-vl-namedarg x :expr expr-prime)
                   x)))
    (mv warnings changedp x-prime)))

(def-vl-weirdint-elim-list vl-namedarglist :element vl-namedarg)

(def-vl-weirdint-elim vl-arguments
  :body
  (vl-arguments-case x
    :vl-arguments-named
    (b* (((mv warnings changedp args-prime)
          (vl-namedarglist-weirdint-elim x.args warnings))
         (x-prime (if changedp
                      (change-vl-arguments-named x :args args-prime)
                    x)))
      (mv warnings changedp x-prime))
    :vl-arguments-plain
    (b* (((mv warnings changedp args-prime)
          (vl-plainarglist-weirdint-elim x.args warnings))
         (x-prime (if changedp
                      (change-vl-arguments-plain x :args args-prime)
                    x)))
      (mv warnings changedp x-prime))))

(def-vl-weirdint-elim vl-modinst
  :body (b* (((mv warnings args-changedp args-prime)
              (vl-arguments-weirdint-elim (vl-modinst->portargs x) warnings))
             (changedp args-changedp)
             (x-prime  (if changedp
                           (change-vl-modinst x :portargs args-prime)
                         x)))
          (mv warnings changedp x-prime)))

(def-vl-weirdint-elim-list vl-modinstlist :element vl-modinst)

(def-vl-weirdint-elim vl-gateinst
  :body (b* (((mv warnings args-changedp args-prime)
              (vl-plainarglist-weirdint-elim (vl-gateinst->args x) warnings))
             (changedp args-changedp)
             (x-prime  (if changedp
                           (change-vl-gateinst x :args args-prime)
                         x)))
          (mv warnings changedp x-prime)))

(def-vl-weirdint-elim-list vl-gateinstlist :element vl-gateinst)

(def-vl-weirdint-elim vl-delaycontrol
  :body (b* (((mv warnings val-changedp value-prime)
              (vl-expr-weirdint-elim (vl-delaycontrol->value x) warnings))
             (changedp val-changedp)
             (x-prime  (if changedp
                           (change-vl-delaycontrol x :value value-prime)
                         x)))
          (mv warnings changedp x-prime)))

(def-vl-weirdint-elim vl-evatom
  :body (b* (((mv warnings expr-changedp expr-prime)
              (vl-expr-weirdint-elim (vl-evatom->expr x) warnings))
             (changedp expr-changedp)
             (x-prime  (if changedp
                           (change-vl-evatom x :expr expr-prime)
                         x)))
          (mv warnings changedp x-prime)))

(def-vl-weirdint-elim-list vl-evatomlist :element vl-evatom)

(def-vl-weirdint-elim vl-eventcontrol
  :body (b* (((mv warnings atoms-changedp atoms-prime)
              (vl-evatomlist-weirdint-elim (vl-eventcontrol->atoms x) warnings))
             (changedp atoms-changedp)
             (x-prime  (if changedp
                           (change-vl-eventcontrol x :atoms atoms-prime)
                         x)))
          (mv warnings changedp x-prime)))

(def-vl-weirdint-elim vl-repeateventcontrol
  :body (b* (((mv warnings expr-changedp expr-prime)
              (vl-expr-weirdint-elim (vl-repeateventcontrol->expr x) warnings))
             ((mv warnings ctrl-changedp ctrl-prime)
              (vl-eventcontrol-weirdint-elim (vl-repeateventcontrol->ctrl x) warnings))
             (changedp (or expr-changedp ctrl-changedp))
             (x-prime (if changedp
                          (change-vl-repeateventcontrol x
                                                        :expr expr-prime
                                                        :ctrl ctrl-prime)
                        x)))
          (mv warnings changedp x-prime)))

(def-vl-weirdint-elim vl-delayoreventcontrol
  :body (case (tag x)
          (:vl-delaycontrol (vl-delaycontrol-weirdint-elim x warnings))
          (:vl-eventcontrol (vl-eventcontrol-weirdint-elim x warnings))
          (otherwise        (vl-repeateventcontrol-weirdint-elim x warnings))))

(def-vl-weirdint-elim vl-maybe-delayoreventcontrol
  :body (if x
            (vl-delayoreventcontrol-weirdint-elim x warnings)
          (mv (ok) nil nil)))

(defthm vl-maybe-delayoreventcontrol-weirdint-elim-under-iff
  (implies (force (vl-maybe-delayoreventcontrol-p x))
           (iff (mv-nth 2 (vl-maybe-delayoreventcontrol-weirdint-elim x warnings))
                x))
  :hints(("Goal"
          :in-theory (e/d (vl-maybe-delayoreventcontrol-weirdint-elim
                           vl-maybe-delayoreventcontrol-p)
                          (vl-delayoreventcontrol-p-OF-VL-DELAYOREVENTCONTROL-WEIRDINT-ELIM.X-PRIME))
          :use ((:instance vl-delayoreventcontrol-p-OF-VL-DELAYOREVENTCONTROL-WEIRDINT-ELIM.X-PRIME)))))



(defines vl-stmt-weirdint-elim

  (define vl-stmt-weirdint-elim
    ((x        vl-stmt-p)
     (warnings vl-warninglist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (changedp booleanp :rule-classes :type-prescription)
                 (new-x    vl-stmt-p))
    :verify-guards nil
    :measure (vl-stmt-count x)
    :flag :stmt
    (b* ((x (vl-stmt-fix x))
         ((when (vl-atomicstmt-p x))
          (case (vl-stmt-kind x)
            (:vl-nullstmt
             (mv (ok) nil x))
            (:vl-assignstmt
             (b* (((mv warnings lvalue-changedp lvalue-prime)
                   (vl-expr-weirdint-elim (vl-assignstmt->lvalue x) warnings))
                  ((mv warnings expr-changedp expr-prime)
                   (vl-expr-weirdint-elim (vl-assignstmt->expr x) warnings))
                  ((mv warnings ctrl-changedp ctrl-prime)
                   (vl-maybe-delayoreventcontrol-weirdint-elim (vl-assignstmt->ctrl x) warnings))
                  (changedp (or lvalue-changedp expr-changedp ctrl-changedp))
                  (x-prime (if changedp
                               (change-vl-assignstmt x
                                                     :lvalue lvalue-prime
                                                     :expr expr-prime
                                                     :ctrl ctrl-prime)
                             x)))
               (mv (ok) changedp x-prime)))
            (:vl-deassignstmt
             (b* (((mv warnings lvalue-changedp lvalue-prime)
                   (vl-expr-weirdint-elim (vl-deassignstmt->lvalue x) warnings))
                  (changedp lvalue-changedp)
                  (x-prime (if changedp
                               (change-vl-deassignstmt x :lvalue lvalue-prime)
                             x)))
               (mv (ok) changedp x-prime)))
            (:vl-enablestmt
             (b* (((mv warnings id-changedp id-prime)
                   (vl-expr-weirdint-elim (vl-enablestmt->id x) warnings))
                  ((mv warnings args-changedp args-prime)
                   (vl-exprlist-weirdint-elim (vl-enablestmt->args x) warnings))
                  (changedp (or id-changedp args-changedp))
                  (x-prime (if changedp
                               (change-vl-enablestmt x
                                                     :id id-prime
                                                     :args args-prime)
                             x)))
               (mv (ok) changedp x-prime)))
            (:vl-disablestmt
             (b* (((mv warnings id-changedp id-prime)
                   (vl-expr-weirdint-elim (vl-disablestmt->id x) warnings))
                  (changedp id-changedp)
                  (x-prime (if changedp
                               (change-vl-disablestmt x :id id-prime)
                             x)))
               (mv (ok) changedp x-prime)))
            (:vl-returnstmt
             (b* (((vl-returnstmt x) x)
                  ((mv warnings val-changedp val)
                   (if x.val
                       (vl-expr-weirdint-elim x.val warnings)
                     (mv warnings nil x.val))))
               (mv (ok) val-changedp (change-vl-returnstmt x :val val))))
            (:vl-eventtriggerstmt
             (b* (((mv warnings id-changedp id-prime)
                   (vl-expr-weirdint-elim (vl-eventtriggerstmt->id x) warnings))
                  (changedp id-changedp)
                  (x-prime (if changedp
                               (change-vl-eventtriggerstmt x :id id-prime)
                             x)))
               (mv (ok) changedp x-prime)))
            (otherwise
             (mv (impossible) nil x))))
         ;; Compound statements
         ((mv warnings expr-changedp exprs-prime)
          (vl-exprlist-weirdint-elim (vl-compoundstmt->exprs x) warnings))
         ((mv warnings stmts-changedp stmts-prime)
          (vl-stmtlist-weirdint-elim (vl-compoundstmt->stmts x) warnings))
         ((mv warnings ctrl-changedp ctrl-prime)
          (vl-maybe-delayoreventcontrol-weirdint-elim (vl-compoundstmt->ctrl x) warnings))
         (changedp (or expr-changedp stmts-changedp ctrl-changedp))
         (x-prime  (if changedp
                       (change-vl-compoundstmt x
                                               :exprs exprs-prime
                                               :stmts stmts-prime
                                               :ctrl ctrl-prime)
                     x)))
      (mv warnings changedp x-prime)))

   (define vl-stmtlist-weirdint-elim ((x        vl-stmtlist-p)
                                      (warnings vl-warninglist-p))
     :returns (mv (warnings vl-warninglist-p)
                  (changedp booleanp :rule-classes :type-prescription)
                  (new-x    (and (vl-stmtlist-p new-x)
                                 (equal (len new-x) (len x)))))
     :measure (vl-stmtlist-count x)
     :flag :list
     (b* (((when (atom x))
           (mv (ok) nil nil))
          ((mv warnings car-changedp car-prime)
           (vl-stmt-weirdint-elim (car x) warnings))
          ((mv warnings cdr-changedp cdr-prime)
           (vl-stmtlist-weirdint-elim (cdr x) warnings))
          (changedp (or car-changedp cdr-changedp))
          (x-prime  (if changedp
                        (cons car-prime cdr-prime)
                      (vl-stmtlist-fix x))))
       (mv warnings changedp x-prime)))

   ///
   (verify-guards vl-stmt-weirdint-elim)
   (deffixequiv-mutual vl-stmt-weirdint-elim))

(def-vl-weirdint-elim vl-always
  :body (b* (((mv warnings stmt-changedp stmt-prime)
              (vl-stmt-weirdint-elim (vl-always->stmt x) warnings))
             (changedp stmt-changedp)
             (x-prime (if changedp
                          (change-vl-always x :stmt stmt-prime)
                        x)))
            (mv warnings changedp x-prime)))

(def-vl-weirdint-elim-list vl-alwayslist :element vl-always)

(def-vl-weirdint-elim vl-initial
  :body (b* (((mv warnings stmt-changedp stmt-prime)
              (vl-stmt-weirdint-elim (vl-initial->stmt x) warnings))
             (changedp stmt-changedp)
             (x-prime (if changedp
                          (change-vl-initial x :stmt stmt-prime)
                        x)))
            (mv warnings changedp x-prime)))

(def-vl-weirdint-elim-list vl-initiallist :element vl-initial)



; All the groundwork is done.  We just need to be able to rewrite the X's and
; Z's throughout the module now.  This is mainly straightforward, but we have a
; couple of extra considerations:
;
;   1. If we actually made any changes, we may need to also introduce instances
;      of VL_1_BIT_X and/or VL_1_BIT_Z to drive vl-x-wire and/or
;      vl-z-wire.
;
;   2. If we made any changes, we need to be sure that we aren't introducing
;      any name conflicts as we add vl-x-wire and vl-z-wire.
;

(define vl-module-add-x/z-wire
  :short "Extend mod with a wire declaration for vl-x-wire or vl-z-wire, and a
          module instance that drives it."
  ((nf    vl-namefactory-p)
   (mod   vl-module-p)
   (which (or (eq which :x) (eq which :z))))
  :returns
  (mv (nf      vl-namefactory-p)
      (new-mod vl-module-p))

  (b* ((vardecls   (vl-module->vardecls mod))
       (modinsts   (vl-module->modinsts mod))

       (wirename (if (eq which :x)
                     "vl-x-wire"
                   "vl-z-wire"))

       ((mv instname nf)
        (vl-namefactory-plain-name (if (eq which :x)
                                       "vl_make_x_wire"
                                     "vl_make_z_wire")
                                   nf))

       (target-mod (if (eq which :x)
                       *vl-1-bit-x*
                     *vl-1-bit-z*))

       (new-vardecl (make-vl-vardecl :name wirename
                                     :type *vl-plain-old-wire-type*
                                     :nettype :vl-wire
                                     :loc *vl-fakeloc*))

       (new-expr    (if (eq which :x)
                        *vl-x-wire-expr*
                      *vl-z-wire-expr*))

       (new-modinst (make-vl-modinst
                     :modname (vl-module->name target-mod)
                     :instname instname
                     :paramargs (make-vl-paramargs-plain :args nil)
                     :portargs (make-vl-arguments-plain
                                :args (list (make-vl-plainarg :expr new-expr
                                                              :dir :vl-output
                                                              :portname "out")))
                     :loc *vl-fakeloc*))

       (mod-prime (change-vl-module mod
                                    :vardecls (cons new-vardecl vardecls)
                                    :modinsts (cons new-modinst modinsts))))

    (mv nf mod-prime)))

(define vl-module-weirdint-elim ((x vl-module-p))
  :returns (mv (new-x vl-module-p)
               (addmods vl-modulelist-p))

  (b* ((x (vl-module-fix x))
       ((when (vl-module->hands-offp x))
        (mv x nil))
       ((vl-module x) x)
       (warnings x.warnings)

       ((mv warnings assigns-changedp assigns)
        (vl-assignlist-weirdint-elim x.assigns warnings))
       ((mv warnings modinsts-changedp modinsts)
        (vl-modinstlist-weirdint-elim x.modinsts warnings))
       ((mv warnings gateinsts-changedp gateinsts)
        (vl-gateinstlist-weirdint-elim x.gateinsts warnings))
       ((mv warnings alwayses-changedp alwayses)
        (vl-alwayslist-weirdint-elim x.alwayses warnings))
       ((mv warnings initials-changedp initials)
        (vl-initiallist-weirdint-elim x.initials warnings))

       (changedp (or assigns-changedp modinsts-changedp gateinsts-changedp
                     alwayses-changedp initials-changedp))
       ((unless changedp)
        (mv (change-vl-module x :warnings warnings) nil))

; If we get to here, then the module has some changes.  We need to figure out
; which modules we need to add, and add the appropriate instances.  To begin
; with, we'll make sure that vl-x-wire and vl-z-wire are free for use.

       (orig-names (vl-exprlist-names (vl-module-allexprs x)))
       ((when (or (member-equal "vl-x-wire" orig-names)
                  (member-equal "vl-z-wire" orig-names)))
        (let ((warnings
               (fatal :type :vl-bad-names
                      :msg "~m0 already has a wire named \"vl-x-wire\" or \"vl-z-wire\"."
                      :args (list (vl-module->name x)))))
          (mv (change-vl-module x :warnings warnings) nil)))

; Okay, we can use vl-x-wire and vl-z-wire.  Lets see which ones we need.

       (temp-module (change-vl-module x
                                      :assigns assigns
                                      :modinsts modinsts
                                      :gateinsts gateinsts
                                      :alwayses alwayses
                                      :initials initials
                                      :warnings warnings))

       (new-names   (vl-exprlist-names (vl-module-allexprs temp-module)))
       (need-x-wire (member-equal "vl-x-wire" new-names))
       (need-z-wire (member-equal "vl-z-wire" new-names))
       ((unless (or need-x-wire need-z-wire))
        (let ((warnings
               (fatal :type :vl-weirdint-not-weird
                      :msg "Expected to at least need X or Z after eliminating weird ints.")))
          (mv (change-vl-module x :warnings warnings) nil)))

       (addmods nil)
       (addmods (if need-x-wire (cons *vl-1-bit-x* addmods) addmods))
       (addmods (if need-z-wire (cons *vl-1-bit-z* addmods) addmods))

       (nf          (vl-starting-namefactory temp-module))
       ((mv nf temp-module)
        (if need-x-wire
            (vl-module-add-x/z-wire nf temp-module :x)
          (mv nf temp-module)))

       ((mv nf temp-module)
        (if need-z-wire
            (vl-module-add-x/z-wire nf temp-module :z)
          (mv nf temp-module)))
       (- (vl-free-namefactory nf))
       )

    (mv temp-module addmods))
  ///
  (defmvtypes vl-module-weirdint-elim (nil true-listp)))

(define vl-modulelist-weirdint-elim-aux ((x vl-modulelist-p))
  :returns (mv (new-x vl-modulelist-p)
               (addmods vl-modulelist-p))
  (b* (((when (atom x))
        (mv nil nil))
       ((mv car-prime new1) (vl-module-weirdint-elim (car x)))
       ((mv cdr-prime new2) (vl-modulelist-weirdint-elim-aux (cdr x)))
       (x-prime             (cons car-prime cdr-prime))
       (new                 (append new1 new2)))
    (mv x-prime new)))

(define vl-modulelist-weirdint-elim ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (b* (((mv x-prime new-mods) (vl-modulelist-weirdint-elim-aux x))
       (new-mods              (mergesort new-mods))
       (full-mods             (mergesort (append new-mods x-prime)))
       ((unless (uniquep (vl-modulelist->names full-mods)))
        (raise "Name collision!")))
    full-mods))

(define vl-design-weirdint-elim
  :short "Top-level @(see weirdint-elim) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-weirdint-elim x.mods))))



