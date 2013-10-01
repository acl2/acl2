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

(defconst *vl-x-wire-expr*
  (vl-idexpr "vl-x-wire" 1 :vl-unsigned))

(defconst *vl-z-wire-expr*
  (vl-idexpr "vl-z-wire" 1 :vl-unsigned))


; We assume all sizing has already been done, so we need to produce full size
; and signedness information on all numbers we introduce.

(defsection vl-weirdint-bits-to-exprs

; BITS are the MSB-first list of bits from a weirdint.  We want to create a
; list of expressions which will become the arguments to a concatenation, which
; represent the bit values.  Any 0 bits become 1'b0, 1 bits become 1'b1, Z bits
; become vl-z-wire, and X bits become vl-x-wire.

  (defund vl-weirdint-bits-to-exprs (bits)
    (declare (xargs :guard (vl-bitlist-p bits)))
    (if (atom bits)
        nil
      (cons (case (car bits)
              (:vl-0val |*sized-1'b0*|)
              (:vl-1val |*sized-1'b1*|)
              (:vl-xval *vl-x-wire-expr*)
              (:vl-zval *vl-z-wire-expr*))
            (vl-weirdint-bits-to-exprs (cdr bits)))))

  (local (in-theory (enable vl-weirdint-bits-to-exprs)))

  (defthm vl-exprlist-p-of-vl-weirdint-bits-to-exprs
    (implies (force (vl-bitlist-p bits))
             (vl-exprlist-p (vl-weirdint-bits-to-exprs bits)))
    :hints(("Goal" :in-theory (enable vl-bit-p)))))



(defsection vl-weirdint-to-concat

  (defund vl-weirdint-to-concat (x warnings)
    "Returns (MV WARNINGS' CONCAT)"
    (declare (xargs :guard (and (vl-weirdint-p x)
                                (vl-warninglist-p warnings))))
    (b* ((width (vl-weirdint->origwidth x))
         (type  (vl-weirdint->origtype x))
         (bits  (vl-weirdint->bits x))

         ((when (eq type :vl-signed))
          (b* ((w (make-vl-warning :type :vl-unsupported
                                   :msg "Don't want to think about signed weirdints, but found ~a0."
                                   :args (list x)
                                   :fatalp t
                                   :fn 'vl-weirdint-to-concat))
               ;; Build an equivalent expr to use as the default value
               (expr (make-vl-atom :guts x :finalwidth width :finaltype :vl-signed)))
            (mv (cons w warnings) expr)))

         (expr (make-vl-nonatom :op :vl-concat
                                :args (vl-weirdint-bits-to-exprs bits)
                                :finalwidth width
                                :finaltype :vl-unsigned)))
      (mv warnings expr)))

  (local (in-theory (enable vl-weirdint-to-concat)))

  (defthm vl-warninglist-p-of-vl-weirdint-to-concat
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-weirdint-to-concat x warnings)))))

  (defthm vl-expr-p-of-vl-weirdint-to-concat
    (implies (force (vl-weirdint-p x))
             (vl-expr-p (mv-nth 1 (vl-weirdint-to-concat x warnings))))))



(defsection vl-expr-weirdint-elim

  (mutual-recursion

   (defund vl-expr-weirdint-elim (x warnings)
     "Returns (MV WARNINGS CHANGEDP X-PRIME)"
     (declare (xargs :guard (and (vl-expr-p x)
                                 (vl-warninglist-p warnings))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (b* (((when (vl-fast-atom-p x))
           (b* (((unless (vl-fast-weirdint-p (vl-atom->guts x)))
                 ;; Nothing needs to be changed.
                 (mv warnings nil x))

                (guts (vl-atom->guts x))

                ((unless (and (posp (vl-expr->finalwidth x))
                              (= (vl-expr->finalwidth x) (vl-weirdint->origwidth guts))))
                 ;; Probably unnecessary extra sanity check.
                 (b* ((w (make-vl-warning :type :vl-programming-error
                                          :msg "Bad widths on weirdint: ~x0."
                                          :args (list x)
                                          :fatalp t
                                          :fn 'vl-expr-weirdint-elim)))
                   (mv (cons w warnings) nil x)))

                ((mv warnings concat) (vl-weirdint-to-concat guts warnings)))
             (mv warnings t concat)))

          ((mv warnings changedp args-prime)
           (vl-exprlist-weirdint-elim (vl-nonatom->args x) warnings))

          (x-prime (if changedp
                       (change-vl-nonatom x :args args-prime)
                     x)))

       (mv warnings changedp x-prime)))

   (defund vl-exprlist-weirdint-elim (x warnings)
     "Returns (MV WARNINGS CHANGEDP X-PRIME)"
     (declare (xargs :guard (and (vl-exprlist-p x)
                                 (vl-warninglist-p warnings))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         (mv warnings nil nil)
       (b* (((mv warnings car-changedp car-prime) (vl-expr-weirdint-elim (car x) warnings))
            ((mv warnings cdr-changedp cdr-prime) (vl-exprlist-weirdint-elim (cdr x) warnings))
            (changedp (or car-changedp cdr-changedp))
            (x-prime  (if changedp
                          (cons car-prime cdr-prime)
                        x)))
           (mv warnings changedp x-prime)))))

  (defthm vl-exprlist-weirdint-elim-when-not-consp
    (implies (not (consp x))
             (equal (vl-exprlist-weirdint-elim x warnings)
                    (mv warnings nil nil)))
    :hints(("Goal" :in-theory (enable vl-exprlist-weirdint-elim))))

  (defthm vl-exprlist-weirdint-elim-when-of-cons
    (equal (vl-exprlist-weirdint-elim (cons a x) warnings)
           (b* (((mv warnings car-changedp car-prime) (vl-expr-weirdint-elim a warnings))
                ((mv warnings cdr-changedp cdr-prime) (vl-exprlist-weirdint-elim x warnings))
                (changedp (or car-changedp cdr-changedp))
                (x-prime  (if changedp (cons car-prime cdr-prime) (cons a x))))
               (mv warnings changedp x-prime)))
    :hints(("Goal" :in-theory (enable vl-exprlist-weirdint-elim))))

  (local (defun my-induction (x warnings)
           (if (atom x)
               (mv warnings nil)
             (b* (((mv warnings & &) (vl-expr-weirdint-elim (car x) warnings)))
                 (my-induction (cdr x) warnings)))))

  (defthm len-of-vl-exprlist-weirdint-elim
    (equal (len (mv-nth 2 (vl-exprlist-weirdint-elim x warnings)))
           (len x))
    :hints(("Goal" :induct (my-induction x warnings))))

  (defthm true-listp-of-vl-exprlist-weirdint-elim
    (implies (true-listp x)
             (true-listp (mv-nth 2 (vl-exprlist-weirdint-elim x warnings))))
    :rule-classes :type-prescription
    :hints(("Goal" :induct (my-induction x warnings))))

  (flag::make-flag vl-flag-expr-weirdint-elim
                   vl-expr-weirdint-elim
                   :flag-mapping ((vl-expr-weirdint-elim . expr)
                                  (vl-exprlist-weirdint-elim . list)))

  (defthm-vl-flag-expr-weirdint-elim lemma
    (expr (implies (force (vl-warninglist-p warnings))
                   (vl-warninglist-p (mv-nth 0 (vl-expr-weirdint-elim x warnings))))
          :name vl-warninglist-p-of-vl-expr-weirdint-elim)
    (list (implies (force (vl-warninglist-p warnings))
                   (vl-warninglist-p (mv-nth 0 (vl-exprlist-weirdint-elim x warnings))))
          :name vl-warninglist-p-of-vl-exprlist-weirdint-elim)
    :hints(("Goal"
            :induct (vl-flag-expr-weirdint-elim flag x warnings)
            :expand ((vl-expr-weirdint-elim x warnings)))))

  (defthm-vl-flag-expr-weirdint-elim lemma
    (expr (implies (force (vl-expr-p x))
                   (vl-expr-p (mv-nth 2 (vl-expr-weirdint-elim x warnings))))
          :name vl-expr-p-of-vl-expr-weirdint-elim)
    (list (implies (force (vl-exprlist-p x))
                   (vl-exprlist-p (mv-nth 2 (vl-exprlist-weirdint-elim x warnings))))
          :name vl-exprlist-p-of-vl-exprlist-weirdint-elim)
    :hints(("Goal"
            :induct (vl-flag-expr-weirdint-elim flag x warnings)
            :expand ((vl-expr-weirdint-elim x warnings)))))

  (verify-guards vl-expr-weirdint-elim))





(defmacro def-vl-weirdint-elim (name &key type body)
  (let* ((name-s     (symbol-name name))
         (type-s     (symbol-name type))
         (thm-warn-s (cat "VL-WARNINGLIST-P-" name-s))
         (thm-type-s (cat type-s "-OF-" name-s))
         (thm-warn   (intern-in-package-of-symbol thm-warn-s name))
         (thm-type   (intern-in-package-of-symbol thm-type-s name)))

  `(encapsulate
    ()
    (defund ,name (x warnings)
      "Returns (MV WARNINGS CHANGEDP X-PRIME)"
      (declare (xargs :guard (and (,type x)
                                  (vl-warninglist-p warnings))))
      ,body)

    (local (in-theory (enable ,name)))

    (defthm ,thm-warn
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p (mv-nth 0 (,name x warnings)))))

    (defthm ,thm-type
      (implies (force (,type x))
               (,type (mv-nth 2 (,name x warnings)))))
    )))


(defmacro def-vl-weirdint-elim-list (name &key type element)
  (let* ((name-s     (symbol-name name))
         (type-s     (symbol-name type))
         (thm-warn-s (cat "VL-WARNINGLIST-P-" name-s))
         (thm-type-s (cat type-s "-OF-" name-s))
         (thm-true-s (cat "TRUE-LISTP-OF-" name-s))
         (thm-warn   (intern-in-package-of-symbol thm-warn-s name))
         (thm-type   (intern-in-package-of-symbol thm-type-s name))
         (thm-true   (intern-in-package-of-symbol thm-true-s name)))

  `(encapsulate
    ()
    (defund ,name (x warnings)
      (declare (xargs :guard (and (,type x)
                                  (vl-warninglist-p warnings))))
      (if (atom x)
          (mv warnings nil nil)
        (b* (((mv warnings car-changedp car-prime) (,element (car x) warnings))
             ((mv warnings cdr-changedp cdr-prime) (,name (cdr x) warnings))
             (changedp (or car-changedp cdr-changedp))
             (x-prime  (if changedp (cons car-prime cdr-prime) x)))
            (mv warnings changedp x-prime))))

    (local (in-theory (enable ,name)))

    (defthm ,thm-warn
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p (mv-nth 0 (,name x warnings)))))

    (defthm ,thm-type
      (implies (force (,type x))
               (,type (mv-nth 2 (,name x warnings)))))

    (defthm ,thm-true
      (implies (true-listp x)
               (true-listp (mv-nth 2 (,name x warnings))))
      :rule-classes :type-prescription)
    )))




(def-vl-weirdint-elim vl-maybe-expr-weirdint-elim
  :type vl-maybe-expr-p
  :body (if (not x)
            (mv warnings nil nil)
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
             ((when (not expr))
              (mv warnings nil x))
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
             ((when (not expr))
              (mv warnings nil x))
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
            (mv (er hard 'vl-delayoreventcontrol-weirdint-elim
                    "Impossible case.  This is not really an error.  We are just ~
                     using the guard mechanism to prove that all cases have been ~
                     covered.")
                nil
                x)))))

(def-vl-weirdint-elim vl-maybe-delayoreventcontrol-weirdint-elim
  :type vl-maybe-delayoreventcontrol-p
  :body (if x
            (vl-delayoreventcontrol-weirdint-elim x warnings)
          (mv warnings nil nil)))

(defthm vl-maybe-delayoreventcontrol-weirdint-elim-under-iff
  (implies (force (vl-maybe-delayoreventcontrol-p x))
           (iff (mv-nth 2 (vl-maybe-delayoreventcontrol-weirdint-elim x warnings))
                x))
  :hints(("Goal"
          :in-theory (e/d (vl-maybe-delayoreventcontrol-weirdint-elim
                           vl-maybe-delayoreventcontrol-p)
                          (vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-weirdint-elim))
          :use ((:instance vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-weirdint-elim)))))



(def-vl-weirdint-elim vl-nullstmt-weirdint-elim
  :type vl-nullstmt-p
  :body (mv warnings nil x))

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
           (mv (er hard 'vl-atomicstmt-weirdint-elim
                   "Impossible case.   This is not really an error.  We are just ~
                    using the guard mechanism to prove that all cases have been ~
                    covered.")
               nil
               x))))

(defsection vl-stmt-weirdint-elim

  (mutual-recursion

   (defund vl-stmt-weirdint-elim (x warnings)
     (declare (xargs :guard (and (vl-stmt-p x)
                                 (vl-warninglist-p warnings))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (if (vl-fast-atomicstmt-p x)
         (vl-atomicstmt-weirdint-elim x warnings)
       (b* (((mv warnings expr-changedp exprs-prime)
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
           (mv warnings changedp x-prime))))

   (defund vl-stmtlist-weirdint-elim (x warnings)
     (declare (xargs :guard (and (vl-stmtlist-p x)
                                 (vl-warninglist-p warnings))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         (mv warnings nil nil)
       (b* (((mv warnings car-changedp car-prime) (vl-stmt-weirdint-elim (car x) warnings))
            ((mv warnings cdr-changedp cdr-prime) (vl-stmtlist-weirdint-elim (cdr x) warnings))
            (changedp (or car-changedp cdr-changedp))
            (x-prime  (if changedp (cons car-prime cdr-prime) x)))
           (mv warnings changedp x-prime)))))

  (FLAG::make-flag vl-flag-stmt-weirdint-elim
                   vl-stmt-weirdint-elim
                   :flag-mapping ((vl-stmt-weirdint-elim . stmt)
                                  (vl-stmtlist-weirdint-elim . list)))

  (defthm-vl-flag-stmt-weirdint-elim lemma
    (stmt (implies (force (vl-warninglist-p warnings))
                   (vl-warninglist-p (mv-nth 0 (vl-stmt-weirdint-elim x warnings))))
          :name vl-warninglist-p-of-vl-stmt-weirdint-elim-1)
    (list (implies (force (vl-warninglist-p warnings))
                   (vl-warninglist-p (mv-nth 0 (vl-stmtlist-weirdint-elim x warnings))))
          :name vl-warninglist-p-of-vl-stmtlist-weirdint-elim-1)
    :hints(("Goal"
            :induct (vl-flag-stmt-weirdint-elim flag x warnings)
            :expand ((vl-stmt-weirdint-elim x warnings)
                     (vl-stmtlist-weirdint-elim x warnings)))))

  (defthm vl-stmtlist-weirdint-elim-when-not-consp
    (implies (not (consp x))
             (equal (vl-stmtlist-weirdint-elim x warnings)
                    (mv warnings nil nil)))
    :hints(("Goal" :in-theory (enable vl-stmtlist-weirdint-elim))))

  (defthm vl-stmtlist-weirdint-elim-of-cons
    (equal (vl-stmtlist-weirdint-elim (cons a x) warnings)
           (b* (((mv warnings car-changedp car-prime) (vl-stmt-weirdint-elim a warnings))
                ((mv warnings cdr-changedp cdr-prime) (vl-stmtlist-weirdint-elim x warnings))
                (changedp (or car-changedp cdr-changedp))
                (x-prime  (if changedp (cons car-prime cdr-prime) (cons a x))))
               (mv warnings changedp x-prime)))
    :hints(("Goal" :in-theory (enable vl-stmtlist-weirdint-elim))))

  (local (defun my-induction (x warnings)
           (if (atom x)
               (mv warnings x)
             (b* (((mv warnings & &) (vl-stmt-weirdint-elim (car x) warnings)))
                 (my-induction (cdr x) warnings)))))

  (defthm len-of-vl-stmtlist-weirdint-elim
    (equal (len (mv-nth 2 (vl-stmtlist-weirdint-elim x warnings)))
           (len x))
    :hints(("Goal" :induct (my-induction x warnings))))

  (defthm-vl-flag-stmt-weirdint-elim lemma
    (stmt (implies (force (vl-stmt-p x))
                   (vl-stmt-p (mv-nth 2 (vl-stmt-weirdint-elim x warnings))))
          :name vl-stmt-p-of-vl-stmt-weirdint-elim-2)
    (list (implies (force (vl-stmtlist-p x))
                   (vl-stmtlist-p (mv-nth 2 (vl-stmtlist-weirdint-elim x warnings))))
          :name vl-stmtlist-p-of-vl-stmtlist-weirdint-elim-2)
    :hints(("Goal"
            :induct (vl-flag-stmt-weirdint-elim flag x warnings)
            :expand ((vl-stmt-weirdint-elim x warnings)
                     (vl-stmtlist-weirdint-elim x warnings)))))

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

(defsection vl-module-add-x/z-wire

; We extend mod with a wire declaration for vl-x-wire or vl-z-wire, and a
; module instance that drives it.

  (defund vl-module-add-x/z-wire (nf mod which)
    "Returns (MV NF' MOD')"
    (declare (xargs :guard (and (vl-namefactory-p nf)
                                (vl-module-p mod)
                                (or (eq which :x)
                                    (eq which :z)))))
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

  (local (in-theory (enable vl-module-add-x/z-wire)))

  (defthm vl-module-p-of-vl-module-add-x/z-wire
    (implies (and (force (vl-namefactory-p nf))
                  (force (vl-module-p mod)))
             (vl-module-p (mv-nth 1 (vl-module-add-x/z-wire nf mod which)))))

  (defthm vl-module->name-of-vl-module-add-x/z-wire
    (equal (vl-module->name (mv-nth 1 (vl-module-add-x/z-wire nf mod which)))
           (vl-module->name mod)))

  (defthm vl-namefactory-p-of-vl-module-add-x/z-wire
    (implies (force (vl-namefactory-p nf))
             (vl-namefactory-p (mv-nth 0 (vl-module-add-x/z-wire nf mod which))))))




(defsection vl-module-weirdint-elim

  (defund vl-module-weirdint-elim (x)
    "Returns (MV X-PRIME ADD-MODS)"
    (declare (xargs :guard (vl-module-p x)))
    (b* (((when (vl-module->hands-offp x))
          (mv x nil))
         (warnings (vl-module->warnings x))

         ((mv warnings assigns-changedp assigns)
          (vl-assignlist-weirdint-elim (vl-module->assigns x) warnings))
         ((mv warnings modinsts-changedp modinsts)
          (vl-modinstlist-weirdint-elim (vl-module->modinsts x) warnings))
         ((mv warnings gateinsts-changedp gateinsts)
          (vl-gateinstlist-weirdint-elim (vl-module->gateinsts x) warnings))
         ((mv warnings alwayses-changedp alwayses)
          (vl-alwayslist-weirdint-elim (vl-module->alwayses x) warnings))
         ((mv warnings initials-changedp initials)
          (vl-initiallist-weirdint-elim (vl-module->initials x) warnings))

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
                      :fn 'vl-module-weirdint-elim)))
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

        (mv temp-module addmods)))

  (defmvtypes vl-module-weirdint-elim (nil true-listp))

  (local (in-theory (enable vl-module-weirdint-elim)))

  (defthm vl-module-p-of-vl-module-weirdint-elim
    (implies (force (vl-module-p x))
             (vl-module-p (mv-nth 0 (vl-module-weirdint-elim x)))))

  (defthm vl-module->name-of-vl-module-weirdint-elim
    (equal (vl-module->name (mv-nth 0 (vl-module-weirdint-elim x)))
           (vl-module->name x)))

  (defthm vl-modulelist-p-of-vl-module-weirdint-elim
    (vl-modulelist-p (mv-nth 1 (vl-module-weirdint-elim x)))))


(defsection vl-modulelist-weirdint-elim-aux

  (defund vl-modulelist-weirdint-elim-aux (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    "Returns (MV X-PRIME NEW-MODS)"
    (if (atom x)
        (mv nil nil)
      (b* (((mv car-prime new1) (vl-module-weirdint-elim (car x)))
           ((mv cdr-prime new2) (vl-modulelist-weirdint-elim-aux (cdr x)))
           (x-prime             (cons car-prime cdr-prime))
           (new                 (append new1 new2)))
          (mv x-prime new))))

  (local (in-theory (enable vl-modulelist-weirdint-elim-aux)))

  (defthm vl-modulelist-p-of-vl-modulelist-weirdint-elim-0
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (mv-nth 0 (vl-modulelist-weirdint-elim-aux x)))))

  (defthm vl-modulelist-p-of-vl-modulelist-weirdint-elim-1
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (mv-nth 1 (vl-modulelist-weirdint-elim-aux x)))))

  (defthm vl-modulelist->names-of-vl-modulelist-weirdint-elim-0
    (equal (vl-modulelist->names (mv-nth 0 (vl-modulelist-weirdint-elim-aux x)))
           (vl-modulelist->names x))))


(defsection vl-modulelist-weirdint-elim

  (defund vl-modulelist-weirdint-elim (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    (b* (((mv x-prime new-mods) (vl-modulelist-weirdint-elim-aux x))
         (new-mods              (mergesort new-mods))
         (full-mods             (mergesort (append new-mods x-prime)))
         ((unless (uniquep (vl-modulelist->names full-mods)))
          (er hard? 'vl-modulelist-weirdint-elim "Name collision!")))
        full-mods))

  (local (in-theory (enable vl-modulelist-weirdint-elim)))

  (defthm vl-modulelist-p-of-vl-modulelist-weirdint-elim
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-modulelist-weirdint-elim x))))

  (defthm no-duplicatesp-equal-of-vl-modulelist->names-of-vl-modulelist-weirdint-elim
    (no-duplicatesp-equal (vl-modulelist->names (vl-modulelist-weirdint-elim x)))))




