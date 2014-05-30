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
(include-book "../../mlib/context")
(include-book "../../mlib/lvalues")
(include-book "../../mlib/find-item")
(local (include-book "../../util/arithmetic"))
(local (include-book "../../util/osets"))
(local (std::add-default-post-define-hook :fix))

(define vl-always-scary-regs-aux ((x vl-alwayslist-p))
  :returns (names string-listp)
  :parents (vl-always-scary-regs)
  :short "Returns a list where reg names are repeated N times if they are
repeated in N different always blocks."
  (if (atom x)
      nil
    (append
     ;; Mergesort to remove duplicates that occur in this particular always
     ;; block.  That's because it's fine for a reg to be written multiple
     ;; times in the same block (e.g., under different conditions).
     (mergesort (vl-exprlist-names (vl-always-lvalexprs (car x))))
     (vl-always-scary-regs-aux (cdr x)))))

(define vl-always-scary-regs
  :parents (synthalways)
  :short "Determine which lvalues are assigned to in multiple always blocks."
  ((x vl-alwayslist-p))
  :returns (names (and (string-listp names)
                       (setp names)))
  :long "<p>These registers are generally too complicated to do anything
sensible with.</p>"
  (redundant-mergesort
   (duplicated-members (vl-always-scary-regs-aux x))))

(define vl-always-check-reg
  :parents (synthalways)
  :short "See if a register is simple enough to reasonably synthesize into
a flop/latch."
  ((name "name of a supposed register to be checked" stringp)
   (regs "all registers in the module"               vl-regdecllist-p)
   (elem "context for error messages"                vl-modelement-p))
  :returns
  (warning? (equal (vl-warning-p warning?)
                   (if warning? t nil)))
  :long "<p>We just make sure @('name') is defined as a register and that it
isn't an array.</p>"
  (b* ((name (string-fix name))
       (elem (vl-modelement-fix elem))
       (decl (vl-find-regdecl name regs))
       ((unless decl)
        (make-vl-warning
         :type :vl-always-too-hard
         :msg "~a0: statement is too complex to synthesize.  The variable ~
               being targeted, ~w1, is not declared as a register."
         :args (list elem name)
         :fatalp nil
         :fn __function__))

       ((vl-regdecl decl) decl)
       ((when (consp decl.arrdims))
        (make-vl-warning
         :type :vl-always-too-hard
         :msg "~a0: statement is too complex to synthesize.  The register ~
               being targeted, ~w1, is an array, which we do not support."
         :args (list elem name)
         :fatalp nil
         :fn __function__))

       ((unless (vl-maybe-range-resolved-p decl.range))
        (make-vl-warning
         :type :vl-always-too-hard
         :msg "~a0: statement is too complex to synthesize.  The register ~
               being targeted, ~w1, does not have a resolved size: ~x2"
         :args (list elem name decl.range)
         :fatalp nil
         :fn __function__)))
    nil)
  ///
  (defthm reg-exists-unless-vl-always-check-reg
    (implies (and (not (vl-always-check-reg name regs elem))
                  (force (stringp name))
                  (force (vl-regdecllist-p regs)))
             (member-equal name (vl-regdecllist->names regs)))))

(define vl-always-check-regs ((names string-listp)
                              (regs  vl-regdecllist-p)
                              (elem  vl-modelement-p))
  :returns
  (warning? (equal (vl-warning-p warning?) (if warning? t nil)))
  :parents (synthalways)
  (if (atom names)
      nil
    (or (vl-always-check-reg (car names) regs elem)
        (vl-always-check-regs (cdr names) regs elem)))
  ///
  (defthm regs-exists-unless-vl-always-check-regs
    (implies (and (not (vl-always-check-regs names regs elem))
                  (force (vl-regdecllist-p regs))
                  (force (string-listp names)))
             (subsetp-equal names (vl-regdecllist->names regs)))))


(define vl-always-convert-reg ((x vl-regdecl-p))
  :returns (netdecl vl-netdecl-p)
  :parents (synthalways)
  :short "Convert a register into a wire."

  :long "<p>When we replace @('always') blocks with explicit instances, we have
to convert the register declaration into an ordinary net declaration.</p>

<p>We expect that this function should only ever be called on registers that
have passed @(see vl-always-check-reg), so we cause a hard error if the
register has array dimensions.</p>"

  (b* (((vl-regdecl x) x)
       (- (or (not x.arrdims)
              (raise "Expected all regs to convert to be non-arrays."))))
    (make-vl-netdecl :name    x.name
                     :type    :vl-wire
                     :signedp x.signedp
                     :range   x.range
                     :loc     x.loc
                     :atts    (acons (hons-copy "VL_CONVERTED_REG")
                                     nil x.atts))))

(defprojection vl-always-convert-regs ((x vl-regdecllist-p))
  :parents (synthalways)
  :returns (nets vl-netdecllist-p)
  (vl-always-convert-reg x))

(define vl-stmt-guts ((body vl-stmt-p))
  :parents (synthalways)
  :returns (guts vl-stmtlist-p)
  :short "Coerce a statement into a statement list."
  :long "<p>The idea here is to be able to treat things like these:</p>

@({
  always @(posedge clk)   vs.  always @(posedge clk)
    lhs <= rhs;                  begin
                                   lhs <= rhs;
                                 end
})

<p>in a uniform way.  If we see a @('begin ... end') we'll just return the
@('...') part as a statement list.  If we see any other kind of statement,
e.g., an if statement, a single assignment, etc., then we just return it as a
singleton statement list.</p>"

  (if (and (eq (vl-stmt-kind body) :vl-blockstmt)
           (vl-blockstmt->sequentialp body)
           (not (vl-blockstmt->decls body)))
      (vl-blockstmt->stmts body)
    (list (vl-stmt-fix body))))


(local (defthm consp-of-vl-evatom->expr
         (implies (force (vl-evatom-p x))
                  (consp (vl-evatom->expr x)))
         :rule-classes :type-prescription))

(define vl-match-posedge-clk ((x vl-always-p))
  :returns (mv (clk  (equal (vl-expr-p clk) (if clk t nil)))
               (body (equal (vl-stmt-p body) (if clk t nil))))
  :parents (vl-always-p timing-statements)
  :short "Match @('always @(posedge clk) body')."
  (b* ((stmt (vl-always->stmt x))
       ((unless (eq (vl-stmt-kind stmt) :vl-timingstmt))
        (mv nil nil))
       ((vl-timingstmt stmt) stmt)
       ;; Try to match ctrl with (posedge clk)
       ((unless (and (eq (tag stmt.ctrl) :vl-eventcontrol)
                     (not (vl-eventcontrol->starp stmt.ctrl))))
        (mv nil nil))
       (evatoms (vl-eventcontrol->atoms stmt.ctrl))
       ((unless (and (eql (len evatoms) 1)
                     (eq (vl-evatom->type (car evatoms)) :vl-posedge)))
        (mv nil nil))
       (clk (vl-evatom->expr (car evatoms))))
    (mv clk stmt.body)))

(defprojection vl-evatomlist->exprs ((x vl-evatomlist-p))
  ;; BOZO move to parsetree?
  :parents (vl-evatomlist-p)
  :returns (exprs vl-exprlist-p)
  (vl-evatom->expr x))

(define vl-evatomlist-all-have-edges-p ((x vl-evatomlist-p))
  (if (atom x)
      t
    (and (or (eq (vl-evatom->type (car x)) :vl-posedge)
             (eq (vl-evatom->type (car x)) :vl-negedge))
         (vl-evatomlist-all-have-edges-p (cdr x)))))

(define vl-edge-control-p ((x vl-delayoreventcontrol-p))
  :short "Recognize @@(posedge clk1 or negedge clk2 or ...) style event
          controls."
  (b* ((x (vl-delayoreventcontrol-fix x))
       ((unless (eq (tag x) :vl-eventcontrol))
        ;; Maybe a delay control like #5, not an @(...) control.
        nil)
       ((vl-eventcontrol x) x))
    (and (not x.starp)
         (consp x.atoms)
         (vl-evatomlist-all-have-edges-p x.atoms))))

(define vl-match-always-at-some-edges ((x vl-stmt-p))
  :short "Recognize and decompose edge-triggered statements."
  :returns (mv (body? (equal (vl-stmt-p body?)
                             (if body? t nil)))
               (ctrl? (and (equal (vl-eventcontrol-p ctrl?)
                                  (if body? t nil))
                           (equal (vl-edge-control-p ctrl?)
                                  (if body? t nil))))
               (edges (and (vl-evatomlist-p edges)
                           (vl-evatomlist-all-have-edges-p edges)
                           (equal (consp edges) (if body? t nil))
                           (iff edges body?))))
  (b* (((unless (eq (vl-stmt-kind x) :vl-timingstmt))
        (mv nil nil nil))
       ((vl-timingstmt x) x)
       ((unless (vl-edge-control-p x.ctrl))
        (mv nil nil nil)))
    (mv x.body x.ctrl (vl-eventcontrol->atoms x.ctrl)))
  :prepwork ((local (in-theory (e/d (vl-edge-control-p))))))

