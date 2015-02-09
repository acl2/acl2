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
(include-book "../../mlib/lvalues")
(include-book "../../mlib/find")
(include-book "../../mlib/filter")
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
  :parents (always-top)
  :short "Determine which lvalues are assigned to in multiple always blocks."
  ((x vl-alwayslist-p))
  :returns (names (and (string-listp names)
                       (setp names)))
  :long "<p>These registers are generally too complicated to do anything
sensible with.</p>"
  (redundant-mergesort
   (duplicated-members (vl-always-scary-regs-aux x))))

(define vl-always-check-reg
  :parents (always-top)
  :short "See if a register is simple enough to reasonably synthesize into
a flop/latch."
  ((name "name of a supposed register to be checked" stringp)
   (vars "all variables in the module"               vl-vardecllist-p)
   (elem "context for error messages"                vl-modelement-p))
  :returns
  (warning? (equal (vl-warning-p warning?)
                   (if warning? t nil)))
  :long "<p>We just make sure @('name') is defined as a register and that it
isn't an array.</p>"
  (b* ((name (string-fix name))
       (elem (vl-modelement-fix elem))
       (decl (vl-find-vardecl name vars))
       ((unless decl)
        (make-vl-warning
         :type :vl-always-too-hard
         :msg "~a0: statement is too complex to synthesize.  The variable ~
               being targeted, ~w1, is not declared as a register."
         :args (list elem name)
         :fatalp nil
         :fn __function__))

       ((unless (vl-simplereg-p decl))
        (make-vl-warning
         :type :vl-always-too-hard
         :msg "~a0: statement is too complex to synthesize.  The variable ~
               being targeted, ~w1, is not a simple enough register."
         :args (list elem name)
         :fatalp nil
         :fn __function__))

       ;; note we used to check and warn about arrays here but that's covered
       ;; by simplereg-p

       (range (vl-simplereg->range decl))
       ((unless (vl-maybe-range-resolved-p range))
        (make-vl-warning
         :type :vl-always-too-hard
         :msg "~a0: statement is too complex to synthesize.  The register ~
               being targeted, ~w1, does not have a resolved size: ~x2"
         :args (list elem name range)
         :fatalp nil
         :fn __function__)))
    nil)
  ///
  (defthm reg-exists-unless-vl-always-check-reg
    (implies (and (not (vl-always-check-reg name regs elem))
                  (force (stringp name))
                  (force (vl-vardecllist-p regs)))
             (member-equal name (vl-vardecllist->names regs)))))

(define vl-always-check-regs ((names string-listp)
                              (vars  vl-vardecllist-p)
                              (elem  vl-modelement-p))
  :returns
  (warning? (equal (vl-warning-p warning?) (if warning? t nil)))
  :parents (always-top)
  (if (atom names)
      nil
    (or (vl-always-check-reg (car names) vars elem)
        (vl-always-check-regs (cdr names) vars elem)))
  ///
  (defthm regs-exists-unless-vl-always-check-regs
    (implies (and (not (vl-always-check-regs names vars elem))
                  (force (vl-vardecllist-p vars))
                  (force (string-listp names)))
             (subsetp-equal names (vl-vardecllist->names vars)))))

(define vl-always-convert-reg ((x vl-vardecl-p))
  :returns (netdecl vl-vardecl-p)
  :parents (always-top)
  :short "Convert a register into a wire."

  :long "<p>When we replace @('always') blocks with explicit instances, we have
to convert the register declaration into an ordinary net declaration.</p>

<p>We expect that this function should only ever be called on registers that
have passed @(see vl-always-check-reg), so we cause a hard error if the
register has array dimensions.</p>"

  (b* (((vl-vardecl x) x)
       ((unless (vl-simplereg-p x))
        (raise "Expected all variables to convert to be simple regs and not arrays.")
        (vl-vardecl-fix x))
       (range  (vl-simplereg->range x))
       (new-type (make-vl-coretype :name :vl-logic
                                   :signedp (vl-simplereg->signedp x)
                                   :pdims   (and range (list range)))))
    (change-vl-vardecl x
                       :type new-type
                       :nettype :vl-wire
                       :atts (acons (hons-copy "VL_CONVERTED_REG") nil x.atts))))

(defprojection vl-always-convert-regs ((x vl-vardecllist-p))
  :parents (always-top)
  :returns (nets vl-vardecllist-p)
  (vl-always-convert-reg x))

(define vl-always-convert-regport ((x vl-portdecl-p))
  :returns (new-x vl-portdecl-p)
  :parents (always-top)
  :short "Convert a @('reg') portdecl into a @('wire') portdecl."
  :long "<p>See @(see vl-always-convert-reg).</p>"
  (b* (((vl-portdecl x) (vl-portdecl-fix x))

       ((unless (and (eq (vl-datatype-kind x.type) :vl-coretype)
                     (member (vl-coretype->name x.type) '(:vl-reg :vl-logic))))
        (raise "Not actually a portdecl reg?  ~x0" x)
        x)

       (dims    (vl-coretype->pdims x.type))
       ((unless (and (atom (vl-coretype->udims x.type))
                     (or (atom dims)
                         (and (atom (cdr dims))
                              (vl-range-p (car dims))))))
        (raise "Multi-dimensional array on portdecl reg? ~x0" x)
        x))
    (change-vl-portdecl x
                        :type (change-vl-coretype x.type :name :vl-logic)
                        :nettype :vl-wire
                        :atts (acons (hons-copy "VL_CONVERTED_REG") nil x.atts))))

(defprojection vl-always-convert-regports ((x vl-portdecllist-p))
  :parents (always-top)
  :returns (nets vl-portdecllist-p)
  (vl-always-convert-regport x))

(define vl-convert-regs
  :parents (always-top)
  ((cvtregs   string-listp)
   (vardecls  vl-vardecllist-p)
   (portdecls vl-portdecllist-p))
  :returns (mv (new-vardecls  vl-vardecllist-p)
               (new-portdecls vl-portdecllist-p))
  (b* ((cvtregs   (string-list-fix cvtregs))
       (vardecls  (vl-vardecllist-fix vardecls))
       (portdecls (vl-portdecllist-fix portdecls))

       ;; Extra sanity check: cvtregs have been identified for conversion.
       ;; They had better all be names we know about.
       (non-regs (difference (mergesort cvtregs)
                             (mergesort (vl-vardecllist->names vardecls))))
       ((when non-regs)
        ;; Should be impossible
        (raise "Trying to convert non-registers: ~x0.~%" non-regs)
        (mv vardecls portdecls))

       ((mv vardecls-to-convert vardecls-to-leave-alone)
        (vl-filter-vardecls cvtregs vardecls))
       ((mv portdecls-to-convert portdecls-to-leave-alone)
        (vl-filter-portdecls cvtregs portdecls))

       (converted-vardecls (vl-always-convert-regs vardecls-to-convert))
       (converted-portdecls (vl-always-convert-regports portdecls-to-convert)))
    (mv (append converted-vardecls vardecls-to-leave-alone)
        (append converted-portdecls portdecls-to-leave-alone))))


(define vl-stmt-guts ((body vl-stmt-p))
  :parents (always-top)
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
           (not (vl-blockstmt->vardecls body))
           (not (vl-blockstmt->paramdecls body)))
      (vl-blockstmt->stmts body)
    (list (vl-stmt-fix body))))


(local (defthm consp-of-vl-evatom->expr
         (implies (force (vl-evatom-p x))
                  (consp (vl-evatom->expr x)))
         :rule-classes :type-prescription))

(define vl-match-posedge-clk ((x vl-always-p))
  :returns (mv (clk  (equal (vl-expr-p clk) (if clk t nil)))
               (body (equal (vl-stmt-p body) (if clk t nil))))
  :parents (vl-always-p vl-timingstmt)
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
  :parents (always-top)
  (b* ((x (vl-delayoreventcontrol-fix x))
       ((unless (eq (tag x) :vl-eventcontrol))
        ;; Maybe a delay control like #5, not an @(...) control.
        nil)
       ((vl-eventcontrol x) x))
    (and (not x.starp)
         (consp x.atoms)
         (vl-evatomlist-all-have-edges-p x.atoms))))

(define vl-match-always-at-some-edges ((x vl-stmt-p))
  :parents (always-top)
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




(define vl-evatom-plain-p ((x vl-evatom-p))
  :returns plainp
  :parents (vl-match-latch-main vl-evatom-p)
  :short "We say a @(see vl-evatom-p) is <i>plain</i> when it has no
@('posedge') or @('negedge'), and the expression is a simple identifier.  For
instance, an event control list like @('@(a or b or c)') contains only plain
evatoms."
  :long "<p>Typically an @('always') block that has this sort of event control
contains either behavioral-style combinational logic or latches, whereas an
event control with something like @('@(posedge clk)') expresses
flip-flops.</p>"
  (b* (((vl-evatom x) x))
    (and (eq x.type :vl-noedge)
         (vl-idexpr-p x.expr)))
  ///
  (defthm vl-evatom->type-when-vl-evatom-plain-p
    (implies (vl-evatom-plain-p x)
             (equal (vl-evatom->type x) :vl-noedge)))

  (defthm vl-idexpr-p-of-vl-evatom->expr-when-vl-evatom-plain-p
    (implies (vl-evatom-plain-p x)
             (vl-idexpr-p (vl-evatom->expr x)))))

(deflist vl-evatomlist-plain-p (x)
  (vl-evatom-plain-p x)
  :guard (vl-evatomlist-p x)
  :elementp-of-nil nil
  :parents (vl-match-latch-main vl-evatomlist-p)
  :rest
  ((defthm vl-idexprlist-p-of-vl-evatomlist->exprs
     (implies (vl-evatomlist-plain-p x)
              (vl-idexprlist-p (vl-evatomlist->exprs x))))))
