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
(include-book "occform/util")
(include-book "../mlib/allexprs")
(include-book "../mlib/stmt-tools")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))

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
  :returns (exprs vl-exprlist-p :hyp :fguard
                  "Any 0 bits become 1'b0, 1 bits become 1'b1, Z bits
                   become vl-z-wire, and X bits become vl-x-wire.")
  (if (atom bits)
      nil
    (cons (case (car bits)
            (:vl-0val |*sized-1'b0*|)
            (:vl-1val |*sized-1'b1*|)
            (:vl-xval *vl-x-wire-expr*)
            (:vl-zval *vl-z-wire-expr*))
          (vl-weirdint-bits-to-exprs (cdr bits)))))

(define vl-weirdint-to-concat
  ((x        vl-weirdint-p)
   (warnings vl-warninglist-p))
   :returns (mv (warnings vl-warninglist-p)
                (concat vl-expr-p :hyp (force (vl-weirdint-p x))))
   (b* ((width (vl-weirdint->origwidth x))
        (type  (vl-weirdint->origtype x))
        (bits  (vl-weirdint->bits x))
        ((when (eq type :vl-signed))
         (mv (fatal :type :vl-unsupported
                    :msg "Don't want to think about signed weirdints, but found ~a0."
                    :args (list x))
             ;; Build an equivalent expr to use as the default value
             (make-vl-atom :guts x :finalwidth width :finaltype :vl-signed))))
     (mv (ok)
         (make-vl-nonatom :op :vl-concat
                          :args (vl-weirdint-bits-to-exprs bits)
                          :finalwidth width
                          :finaltype :vl-unsigned))))

(defines vl-expr-weirdint-elim

  (define vl-expr-weirdint-elim ((x        vl-expr-p)
                                 (warnings vl-warninglist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (changedp booleanp :rule-classes :type-prescription)
                 (new-x vl-expr-p :hyp (force (vl-expr-p x))))
    :verify-guards nil
    :measure (two-nats-measure (acl2-count x) 1)
    :flag :expr
    (b* (((when (vl-fast-atom-p x))
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
                             (equal (len new-x) (len x)))
                        :hyp (force (vl-exprlist-p x))))
    :measure (two-nats-measure (acl2-count x) 0)
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
                     x)))
      (mv warnings changedp x-prime)))
  ///
  (verify-guards vl-expr-weirdint-elim))

(defmacro def-vl-weirdint-elim (name &key type body)
  `(define ,name ((x ,type)
                  (warnings vl-warninglist-p))
     :returns (mv (warnings vl-warninglist-p)
                  (changedp booleanp :rule-classes :type-prescription)
                  (x-prime ,type :hyp (force (,type x))))
      ,body))

(defmacro def-vl-weirdint-elim-list (name &key type element)
  `(define ,name ((x ,type)
                  (warnings vl-warninglist-p))
     :returns (mv (warnings vl-warninglist-p)
                  (changedp booleanp :rule-classes :type-prescription)
                  (new-x ,type :hyp (,type x)))
     (b* (((when (atom x))
           (mv (ok) nil nil))
          ((mv warnings car-changedp car-prime) (,element (car x) warnings))
          ((mv warnings cdr-changedp cdr-prime) (,name (cdr x) warnings))
          (changedp (or car-changedp cdr-changedp))
          (x-prime  (if changedp (cons car-prime cdr-prime) x)))
       (mv warnings changedp x-prime))))

(def-vl-weirdint-elim vl-maybe-expr-weirdint-elim
  :type vl-maybe-expr-p
  :body (if (not x)
            (mv (ok) nil nil)
          (vl-expr-weirdint-elim x warnings)))

(def-vl-weirdint-elim vl-assign-weirdint-elim
  :type vl-assign-p
  :body (b* (((mv warnings lvalue-changedp lvalue-prime)
              (vl-expr-weirdint-elim (vl-assign->lvalue x) warnings))
             ((mv warnings expr-changedp expr-prime)
              (vl-expr-weirdint-elim (vl-assign->expr x) warnings))
             (changedp (or lvalue-changedp expr-changedp))
             (x-prime  (if changedp
                           (change-vl-assign x
                                             :lvalue lvalue-prime
                                             :expr expr-prime)
                         x)))
          (mv warnings changedp x-prime)))

(def-vl-weirdint-elim-list vl-assignlist-weirdint-elim
  :type vl-assignlist-p
  :element vl-assign-weirdint-elim)

(def-vl-weirdint-elim vl-plainarg-weirdint-elim
  :type vl-plainarg-p
  :body (b* ((expr (vl-plainarg->expr x))
             ((unless expr)
              (mv (ok) nil x))
             ((mv warnings expr-changedp expr-prime)
              (vl-expr-weirdint-elim expr warnings))
             (changedp expr-changedp)
             (x-prime  (if changedp
                           (change-vl-plainarg x :expr expr-prime)
                         x)))
          (mv warnings changedp x-prime)))

(def-vl-weirdint-elim-list vl-plainarglist-weirdint-elim
  :type vl-plainarglist-p
  :element vl-plainarg-weirdint-elim)

(def-vl-weirdint-elim vl-namedarg-weirdint-elim
  :type vl-namedarg-p
  :body (b* ((expr (vl-namedarg->expr x))
             ((unless expr)
              (mv (ok) nil x))
             ((mv warnings expr-changedp expr-prime)
              (vl-expr-weirdint-elim expr warnings))
             (changedp expr-changedp)
             (x-prime  (if changedp
                           (change-vl-namedarg x :expr expr-prime)
                         x)))
          (mv warnings changedp x-prime)))

(def-vl-weirdint-elim-list vl-namedarglist-weirdint-elim
  :type vl-namedarglist-p
  :element vl-namedarg-weirdint-elim)

(def-vl-weirdint-elim vl-arguments-weirdint-elim
  :type vl-arguments-p
  :body (b* ((namedp (vl-arguments->namedp x))
             (args   (vl-arguments->args x))
             ((mv warnings args-changedp args-prime)
              (if (vl-arguments->namedp x)
                  (vl-namedarglist-weirdint-elim args warnings)
                (vl-plainarglist-weirdint-elim args warnings)))
             (changedp args-changedp)
             (x-prime  (if changedp
                           (vl-arguments namedp args-prime)
                         x)))
          (mv warnings changedp x-prime)))

(def-vl-weirdint-elim vl-modinst-weirdint-elim
  :type vl-modinst-p
  :body (b* (((mv warnings args-changedp args-prime)
              (vl-arguments-weirdint-elim (vl-modinst->portargs x) warnings))
             (changedp args-changedp)
             (x-prime  (if changedp
                           (change-vl-modinst x :portargs args-prime)
                         x)))
          (mv warnings changedp x-prime)))

(def-vl-weirdint-elim-list vl-modinstlist-weirdint-elim
  :type vl-modinstlist-p
  :element vl-modinst-weirdint-elim)

(def-vl-weirdint-elim vl-gateinst-weirdint-elim
  :type vl-gateinst-p
  :body (b* (((mv warnings args-changedp args-prime)
              (vl-plainarglist-weirdint-elim (vl-gateinst->args x) warnings))
             (changedp args-changedp)
             (x-prime  (if changedp
                           (change-vl-gateinst x :args args-prime)
                         x)))
          (mv warnings changedp x-prime)))

(def-vl-weirdint-elim-list vl-gateinstlist-weirdint-elim
  :type vl-gateinstlist-p
  :element vl-gateinst-weirdint-elim)

(def-vl-weirdint-elim vl-delaycontrol-weirdint-elim
  :type vl-delaycontrol-p
  :body (b* (((mv warnings val-changedp value-prime)
              (vl-expr-weirdint-elim (vl-delaycontrol->value x) warnings))
             (changedp val-changedp)
             (x-prime  (if changedp
                           (change-vl-delaycontrol x :value value-prime)
                         x)))
          (mv warnings changedp x-prime)))

(def-vl-weirdint-elim vl-evatom-weirdint-elim
  :type vl-evatom-p
  :body (b* (((mv warnings expr-changedp expr-prime)
              (vl-expr-weirdint-elim (vl-evatom->expr x) warnings))
             (changedp expr-changedp)
             (x-prime  (if changedp
                           (change-vl-evatom x :expr expr-prime)
                         x)))
          (mv warnings changedp x-prime)))

(def-vl-weirdint-elim-list vl-evatomlist-weirdint-elim
  :type vl-evatomlist-p
  :element vl-evatom-weirdint-elim)

(def-vl-weirdint-elim vl-eventcontrol-weirdint-elim
  :type vl-eventcontrol-p
  :body (b* (((mv warnings atoms-changedp atoms-prime)
              (vl-evatomlist-weirdint-elim (vl-eventcontrol->atoms x) warnings))
             (changedp atoms-changedp)
             (x-prime  (if changedp
                           (change-vl-eventcontrol x :atoms atoms-prime)
                         x)))
          (mv warnings changedp x-prime)))

(def-vl-weirdint-elim vl-repeateventcontrol-weirdint-elim
  :type vl-repeateventcontrol-p
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

(encapsulate
 ()
 (local (in-theory (disable vl-delayoreventcontrol-p-when-vl-maybe-delayoreventcontrol-p)))
 (def-vl-weirdint-elim vl-delayoreventcontrol-weirdint-elim
   :type vl-delayoreventcontrol-p
   :body (case (tag x)
           (:vl-delaycontrol (vl-delaycontrol-weirdint-elim x warnings))
           (:vl-eventcontrol (vl-eventcontrol-weirdint-elim x warnings))
           (:vl-repeat-eventcontrol (vl-repeateventcontrol-weirdint-elim x warnings))
           (otherwise
            (mv (impossible) nil x)))))

(def-vl-weirdint-elim vl-maybe-delayoreventcontrol-weirdint-elim
  :type vl-maybe-delayoreventcontrol-p
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
                          (RETURN-TYPE-OF-VL-DELAYOREVENTCONTROL-WEIRDINT-ELIM.X-PRIME                           ))
          :use ((:instance RETURN-TYPE-OF-VL-DELAYOREVENTCONTROL-WEIRDINT-ELIM.X-PRIME                           )))))


(def-vl-weirdint-elim vl-nullstmt-weirdint-elim
  :type vl-nullstmt-p
  :body (mv (ok) nil x))

(def-vl-weirdint-elim vl-assignstmt-weirdint-elim
  :type vl-assignstmt-p
  :body (b* (((mv warnings lvalue-changedp lvalue-prime)
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
          (mv warnings changedp x-prime)))

(def-vl-weirdint-elim vl-deassignstmt-weirdint-elim
  :type vl-deassignstmt-p
  :body (b* (((mv warnings lvalue-changedp lvalue-prime)
              (vl-expr-weirdint-elim (vl-deassignstmt->lvalue x) warnings))
             (changedp lvalue-changedp)
             (x-prime (if changedp
                          (change-vl-deassignstmt x :lvalue lvalue-prime)
                        x)))
          (mv warnings changedp x-prime)))

(def-vl-weirdint-elim vl-enablestmt-weirdint-elim
  :type vl-enablestmt-p
  :body (b* (((mv warnings id-changedp id-prime)
              (vl-expr-weirdint-elim (vl-enablestmt->id x) warnings))
             ((mv warnings args-changedp args-prime)
              (vl-exprlist-weirdint-elim (vl-enablestmt->args x) warnings))
             (changedp (or id-changedp args-changedp))
             (x-prime (if changedp
                          (change-vl-enablestmt x
                                                :id id-prime
                                                :args args-prime)
                        x)))
          (mv warnings changedp x-prime)))

(def-vl-weirdint-elim vl-disablestmt-weirdint-elim
  :type vl-disablestmt-p
  :body (b* (((mv warnings id-changedp id-prime)
              (vl-expr-weirdint-elim (vl-disablestmt->id x) warnings))
             (changedp id-changedp)
             (x-prime (if changedp
                          (change-vl-disablestmt x :id id-prime)
                        x)))
          (mv warnings changedp x-prime)))

(def-vl-weirdint-elim vl-eventtriggerstmt-weirdint-elim
  :type vl-eventtriggerstmt-p
  :body (b* (((mv warnings id-changedp id-prime)
              (vl-expr-weirdint-elim (vl-eventtriggerstmt->id x) warnings))
             (changedp id-changedp)
             (x-prime (if changedp
                          (change-vl-eventtriggerstmt x :id id-prime)
                        x)))
          (mv warnings changedp x-prime)))

(def-vl-weirdint-elim vl-atomicstmt-weirdint-elim
  :type vl-atomicstmt-p
  :body (case (tag x)
          (:vl-nullstmt         (vl-nullstmt-weirdint-elim x warnings))
          (:vl-assignstmt       (vl-assignstmt-weirdint-elim x warnings))
          (:vl-deassignstmt     (vl-deassignstmt-weirdint-elim x warnings))
          (:vl-enablestmt       (vl-enablestmt-weirdint-elim x warnings))
          (:vl-disablestmt      (vl-disablestmt-weirdint-elim x warnings))
          (:vl-eventtriggerstmt (vl-eventtriggerstmt-weirdint-elim x warnings))
          (otherwise
           (mv (impossible) nil x))))

(defines vl-stmt-weirdint-elim

  (define vl-stmt-weirdint-elim
    ((x        vl-stmt-p)
     (warnings vl-warninglist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (changedp booleanp :rule-classes :type-prescription)
                 (new-x    vl-stmt-p :hyp (force (vl-stmt-p x))))
    :verify-guards nil
    :measure (two-nats-measure (acl2-count x) 1)
    :flag :stmt
    (b* (((when (vl-fast-atomicstmt-p x))
          (vl-atomicstmt-weirdint-elim x warnings))
         ((mv warnings expr-changedp exprs-prime)
          (vl-exprlist-weirdint-elim (vl-compoundstmt->exprs x) warnings))
         ((mv warnings stmts-changedp stmts-prime)
          (vl-stmtlist-weirdint-elim (vl-compoundstmt->stmts x) warnings))
         ((mv warnings ctrl-changedp ctrl-prime)
          (vl-maybe-delayoreventcontrol-weirdint-elim (vl-compoundstmt->ctrl x)
                                                      warnings))
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
                                 (equal (len new-x) (len x)))
                            :hyp (force (vl-stmtlist-p x))))
     :measure (two-nats-measure (acl2-count x) 0)
     :flag :list
     (b* (((when (atom x))
           (mv (ok) nil nil))
          ((mv warnings car-changedp car-prime)
           (vl-stmt-weirdint-elim (car x) warnings))
          ((mv warnings cdr-changedp cdr-prime)
           (vl-stmtlist-weirdint-elim (cdr x) warnings))
          (changedp (or car-changedp cdr-changedp))
          (x-prime  (if changedp (cons car-prime cdr-prime) x)))
       (mv warnings changedp x-prime)))

   ///
   (verify-guards vl-stmt-weirdint-elim))

(def-vl-weirdint-elim vl-always-weirdint-elim
  :type vl-always-p
  :body (b* (((mv warnings stmt-changedp stmt-prime)
              (vl-stmt-weirdint-elim (vl-always->stmt x) warnings))
             (changedp stmt-changedp)
             (x-prime (if changedp
                          (change-vl-always x :stmt stmt-prime)
                        x)))
            (mv warnings changedp x-prime)))

(def-vl-weirdint-elim-list vl-alwayslist-weirdint-elim
  :type vl-alwayslist-p
  :element vl-always-weirdint-elim)

(def-vl-weirdint-elim vl-initial-weirdint-elim
  :type vl-initial-p
  :body (b* (((mv warnings stmt-changedp stmt-prime)
              (vl-stmt-weirdint-elim (vl-initial->stmt x) warnings))
             (changedp stmt-changedp)
             (x-prime (if changedp
                          (change-vl-initial x :stmt stmt-prime)
                        x)))
            (mv warnings changedp x-prime)))

(def-vl-weirdint-elim-list vl-initiallist-weirdint-elim
  :type vl-initiallist-p
  :element vl-initial-weirdint-elim)



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
  (mv (nf      vl-namefactory-p :hyp (force (vl-namefactory-p nf)))
      (new-mod vl-module-p :hyp (and (force (vl-namefactory-p nf))
                                     (force (vl-module-p mod)))))
  (b* ((netdecls   (vl-module->netdecls mod))
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

       (new-netdecl (make-vl-netdecl :name wirename
                                     :type :vl-wire
                                     :loc *vl-fakeloc*))

       (new-expr    (if (eq which :x)
                        *vl-x-wire-expr*
                      *vl-z-wire-expr*))

       (new-modinst (make-vl-modinst
                     :modname (vl-module->name target-mod)
                     :instname instname
                     :paramargs (vl-arguments nil nil)
                     :portargs (vl-arguments nil
                                             (list (make-vl-plainarg :expr new-expr
                                                                     :dir :vl-output
                                                                     :portname "out")))
                     :loc *vl-fakeloc*))

       (mod-prime (change-vl-module mod
                                    :netdecls (cons new-netdecl netdecls)
                                    :modinsts (cons new-modinst modinsts))))

    (mv nf mod-prime)))

(define vl-module-weirdint-elim ((x vl-module-p))
  :returns (mv (new-x vl-module-p :hyp :fguard)
               (addmods vl-modulelist-p))

  (b* (((when (vl-module->hands-offp x))
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
        (let ((wrn (make-vl-warning
                    :type :vl-bad-names
                    :msg "~m0 already has a wire named \"vl-x-wire\" or \"vl-z-wire\"."
                    :fatalp t
                    :args (list (vl-module->name x))
                    :fn __function__)))
          (mv (change-vl-module x :warnings (cons wrn warnings)) nil)))

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
        (let ((wrn (make-vl-warning
                    :type :vl-weirdint-not-weird
                    :msg "Expected to at least need X or Z after eliminating weird ints."
                    :fatalp t
                    :fn 'vl-module-weirdint-elim)))
          (mv (change-vl-module x :warnings (cons wrn warnings)) nil)))

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
  :returns (mv (new-x vl-modulelist-p :hyp :fguard)
               (addmods vl-modulelist-p :hyp :fguard))
  (b* (((when (atom x))
        (mv nil nil))
       ((mv car-prime new1) (vl-module-weirdint-elim (car x)))
       ((mv cdr-prime new2) (vl-modulelist-weirdint-elim-aux (cdr x)))
       (x-prime             (cons car-prime cdr-prime))
       (new                 (append new1 new2)))
    (mv x-prime new)))

(define vl-modulelist-weirdint-elim ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p :hyp :fguard)
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
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-weirdint-elim x.mods))))



