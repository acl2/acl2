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

(define vl-always-scary-regs-aux ((x vl-alwayslist-p))
  :returns (names string-listp :hyp :fguard)
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

(define vl-always-scary-regs ((x vl-alwayslist-p))
  :returns (names :hyp :fguard (and (string-listp names)
                                    (setp names)))
  :parents (synthalways)
  :short "Determine which lvalues are assigned to in multiple always blocks."
  :long "<p>These registers are generally too complicated to do anything
sensible with.</p>"
  (redundant-mergesort
   (duplicated-members (vl-always-scary-regs-aux x))))


(define vl-always-check-reg
  ((name "name of a supposed register to be checked" stringp)
   (regs "all registers in the module"               vl-regdecllist-p)
   (elem "context for error messages"                vl-modelement-p))
  :returns
  (warning? (equal (vl-warning-p warning?) (if warning? t nil)))
  :parents (synthalways)
  :short "See if a register is simple enough to reasonably synthesize into
a flop/latch."
  :long "<p>We just make sure @('name') is defined as a register and that it
isn't an array.</p>"
  (b* ((decl (vl-find-regdecl name regs))
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
                  (force (vl-regdecllist-p regs)))
             (subsetp-equal names (vl-regdecllist->names regs)))))


(define vl-always-convert-reg ((x vl-regdecl-p))
  :returns (netdecl vl-netdecl-p :hyp :fguard)
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

(defprojection vl-always-convert-regs (x)
  (vl-always-convert-reg x)
  :guard (vl-regdecllist-p x)
  :result-type vl-netdecllist-p
  :parents (synthalways))


(define vl-stmt-guts ((body vl-stmt-p))
  :returns (guts vl-stmtlist-p :hyp :fguard)
  :parents (synthalways)
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

  (if (and (vl-blockstmt-p body)
           (vl-blockstmt->sequentialp body)
           (not (vl-blockstmt->decls body)))
      (vl-blockstmt->stmts body)
    (list body)))


(local (defthm consp-of-vl-evatom->expr
         (implies (force (vl-evatom-p x))
                  (consp (vl-evatom->expr x)))
         :rule-classes :type-prescription))

(define vl-match-posedge-clk ((x vl-always-p))
  :returns (mv (clk  :hyp :fguard (equal (vl-expr-p clk) (if clk t nil)))
               (body :hyp :fguard (equal (vl-stmt-p body) (if clk t nil))))
  :parents (vl-always-p timing-statements)
  :short "Match @('always @(posedge clk) body')."
  (b* ((stmt (vl-always->stmt x))
       ((unless (vl-timingstmt-p stmt))
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


(defprojection vl-evatomlist->exprs (x)
  ;; BOZO move to parsetree?
  (vl-evatom->expr x)
  :guard (vl-evatomlist-p x)
  :result-type vl-exprlist-p
  :parents (vl-evatomlist-p))
