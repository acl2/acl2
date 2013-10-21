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
(include-book "../../mlib/stmt-tools")
(include-book "../../mlib/delta")
(include-book "../../mlib/context")
(include-book "../occform/util")
(local (include-book "../../util/arithmetic"))

(local (defthm stringp-of-car-when-string-listp
         ;; BOZO this might be worth having non-locally in arithmetic
         (implies (string-listp x)
                  (equal (stringp (car x))
                         (consp x)))))

(local (defthm crock
         ;; BOZO this seems quite possibly better than the rules we have in
         ;; parsetree.  Consider redoing the tag-based theorems for atomguts,
         ;; delayoreventcontrol-p, etc., in this style!
         (implies (vl-delayoreventcontrol-p x)
                  (equal (equal (tag x) :vl-eventcontrol)
                         (vl-eventcontrol-p x)))))

(defsection elimnegedge
  :parents (always-top)
  :short "Coerce any @('negedge')-triggered event controls into @('posedge')
triggered equivalents."

  :long "<p>The basic idea here is to rewrite:</p>

@({
 always @(negedge clk)    -->    wire clkb = ~clk;
   ...                           always @(posedge clkb)
                                   ...
})

<p>so that our backend @('always') transforms, e.g., @(see flopcode), just have
to deal with posedge-triggered statements.</p>

<p>Expressions should be sized before running this transform.  If @('clk') is
not a one-bit wire, we do not transform it and instead cause a fatal warning,
since Verilog implementations disagree about what counts as the edge of a wide
wire.</p>")

(define vl-evatom-elimnegedge ((x     vl-evatom-p)
                               (delta vl-delta-p)
                               (elem  vl-modelement-p))
  :returns (mv (new-x vl-evatom-p :hyp :fguard)
               (delta vl-delta-p  :hyp :fguard))
  :parents (elimnegedge)
  :short "Maybe convert @('negedge clk') into @('posedge clkb'), after first
adding a new wire for @('clkb')."
  (b* (((vl-evatom x) x)
       ((unless (eq x.type :vl-negedge))
        (mv x delta))

       (width (vl-expr->finalwidth x.expr))
       (type  (vl-expr->finaltype x.expr))
       ((unless (natp width))
        (mv x (dwarn :type :vl-bad-edge
                     :msg "~a0: expected arguments of negedge to have widths ~
                           computed, but ~a1 has width ~x2."
                     :args (list elem x.expr width)
                     :fatalp t)))
       ((unless (eql width 1))
        (mv x (dwarn :type :vl-wide-edge
                     :msg "~a0: expected arguments to negedge to have width ~
                           1, but ~a1 has width ~x2.  This is very scary!  ~
                           Verilog implementations don't agree on what ~
                           'negedge w' means when w is a wide wire.    For ~
                           instance, Verilog-XL interprets it as 'negedge ~
                           |w', while NCVerilog treats it as 'negedge w[0]'."
                     :args (list elem x.expr width)
                     :fatalp t)))

       ;; If we get this far, we (negedge x.expr) and x.expr is one bit, so go
       ;; ahead and convert it.
       ((vl-delta delta) delta)
       (preferred-name
        ;; Goofy.  Usually we probably just have (negedge clk).  In this case,
        ;; names is '("clk") and (first names) its just "clk", which is good.
        ;; If we have something elaborate like (negedge clk & en), names will
        ;; be '("clk" "en") or similar and we just pick the one arbitrarily.
        ;; Having no names at all would be very weird, but if we hit that we'll
        ;; just default to "vl_negedge".
        (let ((names (vl-expr-names x.expr)))
          (if (atom names)
              "vl_negedge"
            (cat (car names) "_bar"))))

       (loc                    (vl-modelement-loc elem))
       ((mv new-name nf)       (vl-namefactory-plain-name preferred-name delta.nf))
       ((mv new-expr new-decl) (vl-occform-mkwire new-name 1 :loc loc))
       (new-ass                (make-vl-assign
                                :lvalue new-expr
                                :expr (make-vl-nonatom :op :vl-unary-bitnot
                                                       :args (list x.expr)
                                                       :finalwidth 1
                                                       :finaltype type)
                                :loc loc
                                :atts (acons "VL_NEGEDGE" x.expr nil)))
       (delta (change-vl-delta delta
                               :nf       nf
                               :netdecls (cons new-decl delta.netdecls)
                               :assigns  (cons new-ass delta.assigns)))
       (new-x (change-vl-evatom x
                                :type :vl-posedge
                                :expr new-expr)))
    (mv new-x delta)))

(define vl-evatomlist-elimnegedge ((x     vl-evatomlist-p)
                                   (delta vl-delta-p)
                                   (elem  vl-modelement-p))
  :returns (mv (new-x vl-evatomlist-p :hyp :fguard)
               (delta vl-delta-p      :hyp :fguard))
  :parents (elimnegedge)
  (b* (((when (atom x))
        (mv x delta))
       ((mv car delta) (vl-evatom-elimnegedge (car x) delta elem))
       ((mv cdr delta) (vl-evatomlist-elimnegedge (cdr x) delta elem)))
    (mv (cons car cdr) delta)))

(define vl-eventcontrol-elimnegedge ((x     vl-eventcontrol-p)
                                     (delta vl-delta-p)
                                     (elem  vl-modelement-p))
  :returns (mv (new-x vl-eventcontrol-p :hyp :fguard)
               (delta vl-delta-p        :hyp :fguard))
  :parents (elimnegedge)
  (b* (((vl-eventcontrol x) x)
       ((mv atoms delta) (vl-evatomlist-elimnegedge x.atoms delta elem))
       (new-x (change-vl-eventcontrol x :atoms atoms)))
    (mv new-x delta)))

(define vl-delayoreventcontrol-elimnegedge ((x     vl-delayoreventcontrol-p)
                                            (delta vl-delta-p)
                                            (elem  vl-modelement-p))
  :returns (mv (new-x vl-delayoreventcontrol-p :hyp :fguard)
               (delta vl-delta-p               :hyp :fguard))
  :parents (elimnegedge)
  (case (tag x)
    (:vl-eventcontrol (vl-eventcontrol-elimnegedge x delta elem))
    (otherwise (mv x delta))))

(defsection vl-stmt-elimnegedge
  :parents (elimnegedge)

  (mutual-recursion
   (defund vl-stmt-elimnegedge (x delta elem)
     "Returns (mv new-x delta)"
     (declare (xargs :guard (and (vl-stmt-p x)
                                 (vl-delta-p delta)
                                 (vl-modelement-p elem))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (b* (((when (vl-fast-atomicstmt-p x))
           (mv x delta))
          (stmts (vl-compoundstmt->stmts x))
          ((mv stmts delta)
           (vl-stmtlist-elimnegedge stmts delta elem))
          (x (change-vl-compoundstmt x :stmts stmts))
          ((unless (vl-timingstmt-p x))
           (mv x delta))
          ((vl-timingstmt x) x)
          ((mv ctrl delta)
           (vl-delayoreventcontrol-elimnegedge x.ctrl delta elem)))
       (mv (change-vl-timingstmt x :ctrl ctrl) delta)))

   (defund vl-stmtlist-elimnegedge (x delta elem)
     "Returns (mv new-x delta)"
     (declare (xargs :guard (and (vl-stmtlist-p x)
                                 (vl-delta-p delta)
                                 (vl-modelement-p elem))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 0)))
     (b* (((when (atom x))
           (mv nil delta))
          ((mv car delta) (vl-stmt-elimnegedge (car x) delta elem))
          ((mv cdr delta) (vl-stmtlist-elimnegedge (cdr x) delta elem)))
       (mv (cons car cdr) delta))))

  (flag::make-flag vl-flag-stmt-elimnegedge
                   vl-stmt-elimnegedge
                   :flag-mapping ((vl-stmt-elimnegedge . stmt)
                                  (vl-stmtlist-elimnegedge . list)))

  (defthm vl-stmtlist-elimnegedge-when-not-consp
    (implies (not (consp x))
             (equal (vl-stmtlist-elimnegedge x delta elem)
                    (mv nil delta)))
    :hints(("Goal" :in-theory (enable vl-stmtlist-elimnegedge))))

  (defthm vl-stmtlist-elimnegedge-of-cons
    (equal (vl-stmtlist-elimnegedge (cons a x) delta elem)
           (b* (((mv car delta) (vl-stmt-elimnegedge a delta elem))
                ((mv cdr delta) (vl-stmtlist-elimnegedge x delta elem)))
             (mv (cons car cdr) delta)))
    :hints(("Goal" :in-theory (enable vl-stmtlist-elimnegedge))))

  (local (defun my-induction (x delta elem)
           (b* (((when (atom x))
                 (mv nil delta))
                ((mv car delta) (vl-stmt-elimnegedge (car x) delta elem))
                ((mv cdr delta) (my-induction (cdr x) delta elem)))
             (mv (cons car cdr) delta))))

  (defthm len-of-vl-stmtlist-elimnegedge
    (b* (((mv new-x ?delta) (vl-stmtlist-elimnegedge x delta elem)))
      (equal (len new-x)
             (len x)))
    :hints(("Goal" :induct (my-induction x delta elem))))

  (local
   (defthm nasty-nasty

; Uggggh... Can't use vl-compoundstmt-basic-checksp-of-change-vl-compoundstmt
; because (vl-compoundstmt->type x) gets rewritten.  use of compoundstmt->exprs
; is horrible but gives us a binding for x.

     (implies (and (force (vl-compoundstmt-p x))
                   (force (equal :vl-timingstmt           (vl-compoundstmt->type x)))
                   (force (iff (double-rewrite new-name)  (vl-compoundstmt->name x)))
                   (force (iff (double-rewrite new-ctrl)  (vl-compoundstmt->ctrl x)))
                   (force (equal new-sequentialp          (vl-compoundstmt->sequentialp x)))
                   (force (equal new-casetype             (vl-compoundstmt->casetype x)))
                   (force (equal (consp new-decls) (consp (vl-compoundstmt->decls x))))
                   (force (equal (len (double-rewrite new-stmts)) (len (vl-compoundstmt->stmts x))))
                   )
              (vl-compoundstmt-basic-checksp :vl-timingstmt
                                             (vl-compoundstmt->exprs x)
                                             new-stmts new-name new-decls
                                             new-ctrl new-sequentialp new-casetype))
     :hints(("Goal"
             :in-theory (disable vl-compoundstmt-basic-checksp-of-change-vl-compoundstmt)
             :use ((:instance vl-compoundstmt-basic-checksp-of-change-vl-compoundstmt
                              (new-exprs (vl-compoundstmt->exprs x))
                              ))))))

  (defthm-vl-flag-stmt-elimnegedge

    (defthm return-type-of-vl-stmt-elimnegedge
      (implies (and (force (vl-stmt-p x))
                    (force (vl-delta-p delta))
                    (force (vl-modelement-p elem)))
               (b* (((mv new-x delta)
                     (vl-stmt-elimnegedge x delta elem)))
                 (and (vl-stmt-p new-x)
                      (vl-delta-p delta))))
      :flag stmt)

    (defthm return-type-of-vl-stmtlist-elimnegedge
      (implies (and (force (vl-stmtlist-p x))
                    (force (vl-delta-p delta))
                    (force (vl-modelement-p elem)))
               (b* (((mv new-x delta)
                     (vl-stmtlist-elimnegedge x delta elem)))
                 (and (vl-stmtlist-p new-x)
                      (vl-delta-p delta))))
      :flag list)

    :hints(("Goal"
            :expand ((vl-stmt-elimnegedge x delta elem)))))

  (verify-guards vl-stmt-elimnegedge))


(define vl-always-elimnegedge ((x     vl-always-p)
                               (delta vl-delta-p))
  :returns (mv (new-x vl-always-p :hyp :fguard)
               (delta vl-delta-p  :hyp :fguard))
  :parents (elimnegedge)
  (b* (((vl-always x) x)
       ((mv stmt delta) (vl-stmt-elimnegedge x.stmt delta x)))
    (mv (change-vl-always x :stmt stmt) delta)))

(define vl-alwayslist-elimnegedge  ((x     vl-alwayslist-p)
                                    (delta vl-delta-p))
  :returns (mv (new-x vl-alwayslist-p :hyp :fguard)
               (delta vl-delta-p  :hyp :fguard))
  :parents (elimnegedge)
  (b* (((when (atom x))
        (mv x delta))
       ((mv car delta) (vl-always-elimnegedge (car x) delta))
       ((mv cdr delta) (vl-alwayslist-elimnegedge (cdr x) delta)))
    (mv (cons car cdr) delta)))

(define vl-module-elimnegedge ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard)
  :parents (elimnegedge)
  (b* (((vl-module x) x)
       ((when (vl-module->hands-offp x))
        x)
       ((unless x.alwayses)
        ;; Optimization: not going to do anything, don't bother re-consing the
        ;; module.
        x)
       (delta (vl-starting-delta x))
       (delta (change-vl-delta delta
                               :netdecls x.netdecls
                               :assigns x.assigns))
       ((mv alwayses delta) (vl-alwayslist-elimnegedge x.alwayses delta))
       ((vl-delta delta)    (vl-free-delta delta)))
    (change-vl-module x
                      :alwayses alwayses
                      :assigns  delta.assigns
                      :netdecls delta.netdecls
                      :warnings delta.warnings))
  ///
  (defthm vl-module->name-of-vl-module-elimnegedge
    (equal (vl-module->name (vl-module-elimnegedge x))
           (vl-module->name x))))

(defprojection vl-modulelist-elimnegedge (x)
  (vl-module-elimnegedge x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p
  :parents (elimnegedge)
  :rest
  ((defthm vl-modulelist->names-of-vl-modulelist-elimnegedge
     (equal (vl-modulelist->names (vl-modulelist-elimnegedge x))
            (vl-modulelist->names x)))))

