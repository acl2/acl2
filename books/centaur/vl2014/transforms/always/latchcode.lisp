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
(include-book "util")
(include-book "make-latch")
(include-book "../../mlib/delta")
(local (include-book "../../util/arithmetic"))
(local (include-book "../../util/osets"))
(local (in-theory (enable tag-reasoning)))

(defxdoc latchcode
  :parents (transforms)
  :short "Simple pattern matching for recognizing latches."

  :long "<p>BOZO eventually we will want to develop something akin to @(see
edgesynth) for dealing with @('always') blocks for latches, but for now our
latch recognition is extremely primitive.</p>")

(local (xdoc::set-default-parents latchcode))

(local (defthm crock
         (implies (vl-assignstmt->ctrl x)
                  (vl-delayoreventcontrol-p (vl-assignstmt->ctrl x)))))

(local (defthm crock2
         (implies (equal (tag (vl-assignstmt->ctrl x)) :vl-delaycontrol)
                  (vl-delaycontrol-p (vl-assignstmt->ctrl x)))))

(define vl-match-latchbody-form1 ((x vl-stmt-p))
  :returns (mv (test :hyp :fguard (equal (vl-expr-p test) (if test t nil)))
               (lhs  :hyp :fguard (and (equal (vl-expr-p lhs) (if test t nil))
                                       (iff lhs test)))
               (rhs  :hyp :fguard (and (equal (vl-expr-p rhs) (if test t nil))
                                       (iff rhs test)))
               (delay "maybe natp"))
  :parents (vl-match-latch-main)
  :short "Match @('lhs = [#delay] test ? rhs : lhs')."
  (b* (((unless (vl-assignstmt-p x))
        (mv nil nil nil nil))
       ((vl-assignstmt x) x)
       ((unless (or (eq x.type :vl-blocking)
                    ;; BOZO try to require blocking only!!!!
                    (eq x.type :vl-nonblocking)))
        (mv nil nil nil nil))
       ((unless (and (not (vl-fast-atom-p x.expr))
                     (eq (vl-nonatom->op x.expr) :vl-qmark)))
        (mv nil nil nil nil))
       ((list test rhs lhs-copy?) (vl-nonatom->args x.expr))
       ((unless (equal x.lvalue lhs-copy?))
        ;; BOZO should probably be checking expr-fixes or similar.
        (mv nil nil nil nil))
       ((unless (or (not x.ctrl)
                    (and (mbe :logic (vl-delaycontrol-p x.ctrl)
                              :exec (eq (tag x.ctrl) :vl-delaycontrol))
                         (vl-simpledelaycontrol-p x.ctrl))))
        (mv nil nil nil nil))
       (ticks (and x.ctrl (vl-simpledelaycontrol->ticks x.ctrl))))
    (mv test x.lvalue rhs ticks))
  ///
  (defthm maybe-natp-of-vl-match-latchbody-form1.ticks
    (maybe-natp (mv-nth 3 (vl-match-latchbody-form1 x)))
    :rule-classes :type-prescription))


(define vl-match-latchbody-form2 ((x vl-stmt-p))
  :returns (mv (test :hyp :fguard (equal (vl-expr-p test) (if test t nil)))
               (lhs  :hyp :fguard (and (equal (vl-expr-p lhs) (if test t nil))
                                       (iff lhs test)))
               (rhs  :hyp :fguard (and (equal (vl-expr-p rhs) (if test t nil))
                                       (iff rhs test)))
               (delay "maybe natp"))
  :parents (vl-match-latch-main)
  :short "Match @('if (test) lhs = [#delay] rhs')."
  (b* (((unless (vl-ifstmt-p x))
        (mv nil nil nil nil))
       ((vl-ifstmt x) x)
       ((unless (and (vl-nullstmt-p x.falsebranch)
                     (vl-assignstmt-p x.truebranch)))
        (mv nil nil nil nil))
       ((vl-assignstmt ass) x.truebranch)
       ((unless (or (eq ass.type :vl-blocking)
                    ;; BOZO try to require blocking only!!!!
                    (eq ass.type :vl-nonblocking)))
        (mv nil nil nil nil))
       ((unless (or (not ass.ctrl)
                    (and (mbe :logic (vl-delaycontrol-p ass.ctrl)
                              :exec (eq (tag ass.ctrl) :vl-delaycontrol))
                         (vl-simpledelaycontrol-p ass.ctrl))))
        (mv nil nil nil nil))
       (ticks (and ass.ctrl
                   (vl-simpledelaycontrol->ticks ass.ctrl))))
    (mv x.condition ass.lvalue ass.expr ticks))
  ///
  (defthm maybe-natp-of-vl-match-latchbody-form2.ticks
    (maybe-natp (mv-nth 3 (vl-match-latchbody-form2 x)))
    :rule-classes :type-prescription))

(define vl-match-latchbody ((x vl-stmt-p))
  :returns (mv (test :hyp :fguard (equal (vl-expr-p test) (if test t nil)))
               (lhs  :hyp :fguard (and (equal (vl-expr-p lhs) (if test t nil))
                                       (iff lhs test)))
               (rhs  :hyp :fguard (and (equal (vl-expr-p rhs) (if test t nil))
                                       (iff rhs test)))
               (delay "maybe natp"))
  :parents (vl-match-latch-main)
  :short "Pattern match simple kinds of latch statements."
  (b* (((mv test lhs rhs delay) (vl-match-latchbody-form1 x))
       ((when test)
        (mv test lhs rhs delay)))
    (vl-match-latchbody-form2 x))
  ///
  (defthm maybe-natp-of-vl-match-latchbody.ticks
    (maybe-natp (mv-nth 3 (vl-match-latchbody x)))
    :rule-classes :type-prescription))

(define vl-match-latch-main ((x vl-always-p))
  :returns (mv (ctrl :hyp :fguard (equal (vl-eventcontrol-p ctrl) (if ctrl t nil)))
               (test :hyp :fguard (and (equal (vl-expr-p test) (if ctrl t nil))
                                       (iff test ctrl)))
               (lhs  :hyp :fguard (and (equal (vl-expr-p lhs) (if ctrl t nil))
                                       (iff lhs ctrl)))
               (rhs  :hyp :fguard (and (equal (vl-expr-p rhs) (if ctrl t nil))
                                       (iff rhs ctrl)))
               (delay "maybe natp"))
  :short "Pattern matcher for @('always') blocks that might be simple latches."
  :long "<p>We match always blocks of two forms.  Note that form1 is generally
preferable to form2 since @('if') statements behave very badly when @('test')
is X or Z.</p>

@({
 // form 1                             // form 2
 always @(x or y or z or ...)          always @(x or y or z or ...)
   lhs = [#delay] test ? rhs : lhs;      if (test) lhs = [#delay] rhs;
})

<p>We do <b>not</b> check many things here: see @(see vl-careful-match-latch)
versus @(see vl-careless-match-latch).  However, we do at least make sure that
the sensitivity list has only <see topic='@(url vl-evatom-plain-p)'>plain</see>
atoms, i.e., @('posedge')/@('negedge') are not allowed.</p>

<p>We previously allowed blocking or non-blocking assignments, but we now
require that blocking assignments. Blocking assignments appear to be the
correct Verilog coding style for @('always') blocks that aren't edge-triggered;
see for instance <a href='http://www.sunburst-design.com/papers/'>Cliff
Cummings</a> articles about coding styles for non-blocking assignments.</p>"

    (b* ((stmt (vl-always->stmt x))
         ((unless (vl-timingstmt-p stmt))
          (mv nil nil nil nil nil))
         ((vl-timingstmt stmt) stmt)
         ((unless (and (mbe :logic (vl-eventcontrol-p stmt.ctrl)
                            :exec (eq (tag stmt.ctrl) :vl-eventcontrol))
                       (or (vl-eventcontrol->starp stmt.ctrl)
                           (vl-evatomlist-plain-p
                            (vl-eventcontrol->atoms stmt.ctrl)))))
          (mv nil nil nil nil nil))
         ((mv condition lhs rhs delay) (vl-match-latchbody stmt.body))
         ((unless condition)
          (mv nil nil nil nil nil)))
      (mv stmt.ctrl condition lhs rhs delay))
    ///
    (defthm plain-evatoms-when-vl-match-latch-main
      (implies (force (vl-always-p x))
               (b* (((mv ctrl ?condition ?lhs ?rhs) (vl-match-latch-main x)))
                 (implies (and ctrl
                               (not (vl-eventcontrol->starp ctrl)))
                          (vl-evatomlist-plain-p (vl-eventcontrol->atoms ctrl))))))

    (defthm maybe-natp-of-vl-match-latch-main.ticks
      (maybe-natp (mv-nth 4 (vl-match-latch-main x)))
      :rule-classes :type-prescription))



(define vl-careful-match-latch ((x        vl-always-p)
                                (warnings vl-warninglist-p))
  :returns (mv (warnings :hyp :fguard vl-warninglist-p)
               (test     :hyp :fguard (equal (vl-expr-p test) (if test t nil)))
               (lhs      :hyp :fguard
                         (and (equal (vl-expr-p lhs)   (if test t nil))
                              (equal (vl-idexpr-p lhs) (if test t nil))
                              (iff lhs test)))
               (rhs      :hyp :fguard
                         (and (equal (vl-expr-p rhs) (if test t nil))
                              (iff rhs test)))
               (delay "maybe natp"))
  :short "Match @('always') statements that are simple latches, with lots of
extra sanity checking."

  (b* (((mv ctrl condition lhs rhs delay) (vl-match-latch-main x))

       ((unless (and ctrl
                     (vl-idexpr-p lhs)))
        (mv warnings nil nil nil nil))

       ((unless (vl-idexpr-p lhs))
        ;; The problem is: how can we reliably convert foo into a net in a case
        ;; such as this:
        ;;   reg [3:0] foo;
        ;;   always @(en or d) foo[0] = en ? d : foo[0]
        (mv (warn :type :vl-latch-fail
                  :msg "~a0: failing to infer a latch because the left-hand ~
                        side, ~a1, isn't a simple identifier."
                  :args (list x lhs))
            nil nil nil nil))

       ((vl-eventcontrol ctrl) ctrl)
       (lhs-name        (vl-idexpr->name lhs))
       (rhs-wires       (vl-expr-names rhs))
       (condition-wires (vl-expr-names condition))

       ((when (member-equal lhs-name rhs-wires))
        (mv (warn :type :vl-latch-fail
                  :msg "~a0: failing to infer a latch because the register ~
                        being assigned to, ~s1, occurs in the rhs expression, ~
                        ~a2.  This suggests there may be a combinational loop ~
                        when the latch is enabled."
                  :args (list x lhs-name rhs))
            nil nil nil nil))

       ((when (member-equal lhs-name condition-wires))
        (mv (warn :type :vl-latch-fail
                  :msg "~a0: failing to infer a latch because the register ~
                        being assigned to, ~s1, occurs in its own enable ~
                        expression, ~a2.  This seems very strange and might ~
                        indicate some kind of weird race."
                  :args (list x lhs-name condition))
            nil nil nil nil))

       ;; Make sure all wires used in the condition and rhs are found in the
       ;; sensitivity list.
       (need-wires (if ctrl.starp
                       nil
                     (append rhs-wires condition-wires)))
       (have-wires (if ctrl.starp
                       nil
                     (vl-idexprlist->names (vl-evatomlist->exprs ctrl.atoms))))

       ((unless (subsetp-equal need-wires have-wires))
        (mv (warn :type :vl-latch-fail
                  :msg "~a0: failing to infer a latch since the sensitivity ~
                        list omits ~&1."
                  :args (list x (set-difference-equal need-wires have-wires)))
            nil nil nil nil))

       (warnings
        (if (subsetp-equal have-wires need-wires)
            warnings
          (warn :type :vl-sensitivity-list
                :msg "~a0: sensitivity list appears to include ~&1 ~
                      unnecessarily, which might slow down simulations."
                :args (list x (set-difference-equal have-wires need-wires))))))

    (mv warnings condition lhs rhs delay))

  ///
  (defthm maybe-natp-of-vl-careful-match-latch.ticks
    (maybe-natp (mv-nth 4 (vl-careful-match-latch x warnings)))
    :rule-classes :type-prescription))


(define vl-careless-match-latch ((x        vl-always-p)
                                 (warnings vl-warninglist-p))
  :returns (mv (warnings :hyp :fguard vl-warninglist-p)
               (test     :hyp :fguard (equal (vl-expr-p test) (if test t nil)))
               (lhs      :hyp :fguard
                         (and (equal (vl-expr-p lhs) (if test t nil))
                              (iff lhs test)))
               (rhs      :hyp :fguard
                         (and (equal (vl-expr-p rhs) (if test t nil))
                              (iff rhs test)))
               (delay "maybe natp"))
  :short "Match @('always') statements that are simple latches, with minimal
sanity checking."

  (b* (((mv ctrl condition lhs rhs delay) (vl-match-latch-main x))

       ((unless ctrl)
        (mv warnings nil nil nil nil))

       ;; We don't check vl-idexpr-p here.  This is scary: we'll probably screw
       ;; things up if there's a write to just part of a register.

       ((vl-eventcontrol ctrl) ctrl)
       (lhs-wires       (mergesort (vl-expr-names lhs)))
       (rhs-wires       (mergesort (vl-expr-names rhs)))
       (condition-wires (mergesort (vl-expr-names condition)))

       (lhs/rhs-overlap (intersect lhs-wires rhs-wires))
       (warnings
        (if lhs/rhs-overlap
            (warn :type :vl-warn-loopy-latch
                  :msg "~a0: some wires on the left-hand side of the latch ~
                        are also mentioned in the rhs, which might mean a ~
                        combinational loop when the latch is enabled. Loopy ~
                        wires: ~&1."
                  :args (list x lhs/rhs-overlap))
          warnings))

       (lhs/condition-overlap (intersect lhs-wires condition-wires))
       (warnings
        (if lhs/condition-overlap
            (warn :type :vl-warn-weird-latch
                  :msg "~a0: some wires on the left-hand side of the latch ~
                        are also mentioned in the enable condition, which is ~
                        strange and might indicate some kind of weird race.  ~
                        Wires: ~&1."
                  :args (list x lhs/condition-overlap))
          warnings))

       ;; Make sure all wires used in the condition and rhs are found in the
       ;; sensitivity list.
       (need-wires (if ctrl.starp
                       nil
                     (append rhs-wires condition-wires)))
       (have-wires (if ctrl.starp
                       nil
                     (vl-idexprlist->names (vl-evatomlist->exprs ctrl.atoms))))

       ((unless (subsetp-equal need-wires have-wires))
        ;; Unlike the other warnings above, which we don't stop for, this one
        ;; will cause us to fail.
        (mv (warn :type :vl-latch-fail
                  :msg "~a0: failing to infer a latch since the sensitivity ~
                        list omits ~&1."
                  :args (list x (set-difference-equal need-wires have-wires)))
            nil nil nil nil))

       (warnings
        (if (subsetp-equal have-wires need-wires)
            warnings
          (warn :type :vl-sensitivity-list
                :msg "~a0: sensitivity list appears to include ~&1 ~
                      unnecessarily, which might slow down simulations."
                :args (list x (set-difference-equal have-wires need-wires))))))

    (mv warnings condition lhs rhs delay))

  ///
  (defthm maybe-natp-of-vl-careless-match-latch.ticks
    (maybe-natp (mv-nth 4 (vl-careless-match-latch x warnings)))
    :rule-classes :type-prescription))

(define vl-latchcode-synth-always
  ((x          "always block to try to synthesize"
               vl-always-p)
   (scary-regs "names of registers that are assigned to by multiple always
                blocks; these are too scary to try to synthesize"
               (and (string-listp scary-regs)
                    (setp scary-regs)))
   (vars       "all the variables for the module"
               vl-vardecllist-p)
   (cvtregs    "accumulator for names of registers to convert into nets"
               string-listp)
   (delta      "delta for the new nets, instances, etc."
               vl-delta-p)
   (careful-p  "should we be careful or not?"
               booleanp)
   vecp)
  :returns (mv (new-x? "nil on success, x unchanged on failure"
                       (equal (vl-always-p new-x?) (if new-x? t nil))
                       :hyp :fguard)
               (cvtregs string-listp :hyp :fguard)
               (delta   vl-delta-p   :hyp :fguard))
  :short "Try to synthesize a single @('always') block into a latch."

  (b* (((vl-always x) x)

       ((unless (or (eq x.type :vl-always)
                    (eq x.type :vl-always-latch)))
        ;; Don't touch always_comb or always_ff blocks.
        (mv x cvtregs delta))

       ((when (eq x.type :vl-always-latch))
        ;; BOZO.  For now we do not try to really support always_latch.  To
        ;; support always_latch we will need to adjust our pattern matching
        ;; stuff because the always_latch drops the timing statement.  That
        ;; is, you write something like:
        ;;
        ;;    always_latch if (clk) q <= d;
        ;;
        ;; instead of:
        ;;
        ;;    always @(clk or d) if (clk) q <= d;
        ;;
        ;; So our pattern-matching stuff isn't right for always_latch yet.
        (mv x cvtregs
            (dwarn :type :vl-latchcode-fail
                   :msg "~a0: always_latch blocks are not yet implemented."
                   :args (list x))))

       (warnings (vl-delta->warnings delta))

       ((mv warnings test lhs rhs delay)
        (if careful-p
            (vl-careful-match-latch x warnings)
          (vl-careless-match-latch x warnings)))
       (delta (change-vl-delta delta :warnings warnings))
       ((unless test) ;; didn't even match a latch
        (mv x cvtregs delta))

       ;; Basic checks of registers not having array dimentions, not being
       ;; assigned in other blocks...

       (lhs-names (mergesort (vl-expr-names lhs)))
       ((unless (consp lhs-names))
        (mv x cvtregs
            (dwarn :type :vl-latchcode-fail
                   :msg "~a0: not synthesize a latch since the lhs doesn't ~
                         even have any names?  lhs: ~a1."
                   :args (list x lhs-names))))
       (warning   (vl-always-check-regs lhs-names vars x))
       ((when warning)
        (mv x cvtregs (vl-warn-delta warning)))
       (lhs-scary (intersect lhs-names scary-regs))
       ((unless (empty lhs-scary))
        (mv x cvtregs
            (dwarn :type :vl-latchcode-fail
                   :msg "~a0: cowardly refusing to synthesize always block ~
                         for ~a1 since other always blocks write to ~a1."
                   :args (list x lhs-scary))))

       ((unless (eql (vl-expr->finalwidth test) 1))
        ;; The VL_N_BIT_LATCH we build would be mis-sized.
        (mv x cvtregs
            (dwarn :type :vl-latchcode-fail
                   :msg "~a0: statement is too complex to synthesize.  The ~
                         enable for this latch is ~a1, which we expected ~
                         to have width 1, but its width is ~a2."
                   :args (list x test (vl-expr->finalwidth test)))))

       ;; The idea now is to replace X with:
       ;;
       ;;    wire [lhswidth-1:0] lhs_next;
       ;;    wire [lhswidth-1:0] lhs_delfree;
       ;;
       ;;    assign lhs_next = rhs;  // handles any truncation
       ;;    VL_[lhswidth]_BIT_LATCH lhs_latch (lhs_delfree, test, lhs_next);
       ;;    assign #delay lhs = lhs_delfree;  // handles any delay
       ;;
       ;; Of course, we need to know the lhs width to do this...
       (width (vl-expr->finalwidth lhs))
       ((unless (posp width))
        (mv x cvtregs
            (dwarn :type :vl-latchcode-fail
                   :msg "~a0: can't synthesize always block becasue the width ~
                         of the lhs, ~a1, hasn't been computed or isn't a ~
                         positive number.  Its width is ~a2."
                   :args (list x lhs width))))

       ((vl-delta delta) delta)

       (lhs-name
        ;; This is a little goofy.  If we're in "careful" mode this will just
        ;; be the name of the sole target register.  If we're in "careless"
        ;; mode, this is just some random name on the left of the register.
        ;; But that's probably good enough, it's just for better name
        ;; generation.
        (car lhs-names))

       ((mv inst-name nf)    (vl-namefactory-plain-name (cat lhs-name "_latch")   delta.nf))

       ((when vecp)
        ;; everything is inside the latch instance, no extra delay outside
        (b* ((addmods (vl-make-n-bit-latch-vec width (or delay 0)))
             (latchmod (car addmods))
             (inst (vl-simple-instantiate latchmod inst-name
                                          (list lhs test rhs)
                                          :loc x.loc))
             (delta (change-vl-delta delta
                                     :nf       nf
                                     :modinsts (cons inst delta.modinsts)
                                     :addmods  (append-without-guard addmods
                                                                     delta.addmods))))
          (mv nil (append lhs-names cvtregs) delta)))

       ((mv next-name nf)    (vl-namefactory-plain-name (cat lhs-name "_next")    nf))
       ((mv delfree-name nf) (vl-namefactory-plain-name (cat lhs-name "_delfree") nf))

       ;; wire [n-1:0] lhs_next;
       ;; wire [n-1:0] lhs_delfree;
       ((mv next-expr    next-decl)    (vl-occform-mkwire next-name    width :loc x.loc))
       ((mv delfree-expr delfree-decl) (vl-occform-mkwire delfree-name width :loc x.loc))
       (delfree-decl
        (change-vl-vardecl delfree-decl
                           :atts (acons "VL_TARGET_REG" lhs (vl-vardecl->atts delfree-decl))))

       ;; assign lhs_next = rhs;
       (next-ass  (make-vl-assign :lvalue next-expr :expr rhs :loc x.loc))

       ;; VL_N_BIT_LATCH lhs_latch (lhs_delfree, test, lhs_next);
       (addmods   (vl-make-n-bit-latch width))
       (inst      (vl-simple-instantiate (car addmods) inst-name
                                         (list delfree-expr test next-expr)
                                         :loc x.loc))

       ;; assign #delay lhs = lhs_delfree;
       (main-ass  (make-vl-assign :lvalue lhs
                                  :expr   delfree-expr
                                  :loc    x.loc
                                  :delay  (and delay
                                               (let ((amt-expr (vl-make-index delay)))
                                                (make-vl-gatedelay :rise amt-expr
                                                                   :fall amt-expr
                                                                   :high amt-expr)))))

       (cvtregs   (append lhs-names cvtregs))
       (delta     (change-vl-delta delta
                                   :nf       nf
                                   :vardecls (list* next-decl delfree-decl delta.vardecls)
                                   :assigns  (list* next-ass  main-ass     delta.assigns)
                                   :modinsts (cons inst delta.modinsts)
                                   :addmods  (append-without-guard addmods
                                                                   delta.addmods))))
    (mv nil cvtregs delta))

  :prepwork ;; stupidity...
  ((local (defthm car-under-iff-when-vl-modulelist-p
            (implies (vl-modulelist-p x)
                     (iff (car x)
                          (consp x)))))
   (local (defthm stringp-of-first-when-string-listp
            (implies (string-listp x)
                     (equal (stringp (car x))
                            (consp x)))))))


(define vl-latchcode-synth-alwayses ((x          vl-alwayslist-p)
                                     (scary-regs (and (string-listp scary-regs)
                                                      (setp scary-regs)))
                                     (vars       vl-vardecllist-p)
                                     (cvtregs    string-listp)
                                     (delta      vl-delta-p)
                                     (careful-p  booleanp)
                                     vecp)
  :returns (mv (new-x   vl-alwayslist-p :hyp :fguard)
               (cvtregs string-listp :hyp :fguard)
               (delta   vl-delta-p   :hyp :fguard))
  (b* (((when (atom x))
        (mv nil cvtregs delta))
       ((mv new-car? cvtregs delta)
        (vl-latchcode-synth-always (car x) scary-regs vars
                                   cvtregs delta careful-p vecp))
       ((mv new-cdr cvtregs delta)
        (vl-latchcode-synth-alwayses (cdr x) scary-regs vars
                                     cvtregs delta careful-p vecp))
       (new-x (if new-car?
                  (cons new-car? new-cdr)
                new-cdr)))
    (mv new-x cvtregs delta)))
