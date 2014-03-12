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
(include-book "flopcode-prog")
(include-book "flopcode-debug")
(include-book "util")
(include-book "make-flop")
(include-book "../../mlib/delta")
(include-book "../../mlib/filter")
(local (include-book "../../util/arithmetic"))
(local (include-book "../../util/osets"))
(local (in-theory (disable all-equalp)))
(local (non-parallel-book))

(define vl-flopcode-fix ((x (and (vl-expr-p x)
                                 (vl-expr-welltyped-p x)
                                 (posp (vl-expr->finalwidth x)))))
  :parents (vl-flopcode-next-expr)
  :short "Coerce a well-typed expression to unsigned."
  (if (eq (vl-expr->finaltype x) :vl-unsigned)
      x
    (make-vl-nonatom :op :vl-concat
                     :args (list x)
                     :finaltype :vl-unsigned
                     :finalwidth (vl-expr->finalwidth x)))
  ///
  (defthm vl-expr-p-of-vl-flopcode-fix
    (implies (force (vl-expr-p x))
             (vl-expr-p (vl-flopcode-fix x))))

  (defthm vl-expr->finaltype-of-vl-flopcode-fix
    (equal (vl-expr->finaltype (vl-flopcode-fix x))
           :vl-unsigned))

  (defthm vl-expr->finalwidth-of-vl-flopcode-fix
    (equal (vl-expr->finalwidth (vl-flopcode-fix x))
           (vl-expr->finalwidth x)))

  (defthm vl-expr-welltyped-p-of-vl-flopcode-fix
    (implies (and (force (vl-expr-welltyped-p x))
                  (force (posp (vl-expr->finalwidth x))))
             (vl-expr-welltyped-p (vl-flopcode-fix x)))
    :hints(("Goal"
            :expand ((:free (atts args finalwidth finaltype)
                            (vl-expr-welltyped-p
                             (vl-nonatom :vl-concat
                                         atts args finalwidth finaltype))))))))


(define vl-flopcode-next-expr
  ((rx     "flopcode program to synthesize <b>in reverse order</b>"
           (and (vl-stmtlist-p rx)
                (vl-flopcodestmtlist-p rx)))
   (target "target register of the program"
           (and (vl-expr-p target)
                (vl-expr-welltyped-p target)
                (posp (vl-expr->finalwidth target))))
   (warnings "warnings accumulator" vl-warninglist-p)
   (elem     "just a context for warnings" vl-modelement-p))
  :guard ;; require that all widths/types are compatible.
  (b* ((lhses (vl-flopcodestmtlist->lhses rx)))
    (all-equalp (vl-expr->finalwidth target)
                (vl-exprlist->finalwidths lhses)))
  :returns
  (mv (next :hyp :fguard
            (and (vl-expr-p next)
                 (equal (vl-expr->finaltype next) :vl-unsigned)
                 (equal (vl-expr->finalwidth next)
                        (vl-expr->finalwidth target))))
      (warnings :hyp :fguard
                vl-warninglist-p))
  :parents (flopcode)
  :short "Main step in flopcode program synthesis."

  :long "<p>As an example, consider dealing with @(see flopcode) program
like:</p>

@({
 a <= x0 | x1;
 if (c1) a <= x1;
 if (c2) a <= x2;
})

<p>Our basic goal here is to transform these statements into a single @('next')
expression for an explicit flop instance, e.g.,</p>

@({
  c2 ? x2 : c1 ? x1 : (x0 | x1)
})

<p>Our main input is @('rx'), the @(see flopcode) program to synthesize in
<b>reverse</b> order.  That is, for this example program, @('rx') would
initially be:</p>

@({
 if (c2) a <= x2;   // reversed program
 if (c1) a <= x1;
 a <= x0;
})

<p>Why do we take the program in reverse order?  In Verilog, non-blocking
assignments happen in program order.  For instance, if @('c2') is true, then
the final value of @('a') should be @('x2').  Put another way: the later
assignments have priority, so when we convert them into a @('?:') expression,
we want to consider the last cases first.</p>

<p>This function never fails.  We only take @(see warnings) because we might
notice odd flopcode programs such as</p>

@({
 a <= b;
 a <= c;
})

<p>Which would be weird since the assignment @('a <= b') gets immediately
overwritten by @('a <= c').</p>"

  (b* (((when (atom rx))
        ;; No more statements, i.e., none of the tests we saw were
        ;; satisfied, so the register keeps its value.
        (mv (vl-flopcode-fix target) warnings))

       (cond1 (vl-flopcodestmt->test (car rx)))
       (rhs1  (vl-flopcodestmt->rhs  (car rx)))

       (warnings
        (if (or cond1 (atom (cdr rx)))
            warnings
          (warn :type :vl-warn-unreachable
                :msg "~a0: earlier assignments to ~a1 are followed by an ~
                      unconditional assignment to ~a1, so the earlier ~
                      assignments do nothing!"
                :args (list elem target (car rx)))))

       ((unless cond1)
        ;; Unconditional write, so we're just going to get the RHS.
        (mv (vl-flopcode-fix rhs1) warnings))

       ;; Otherwise, now we need to make a ?: operator.
       ((mv rest warnings)
        (vl-flopcode-next-expr (cdr rx) target warnings elem))

       ;; Our guard is enough to ensure everything agrees on the width, so we
       ;; don't have to do much of anything for well-formedness here.
       (next (make-vl-nonatom :op :vl-qmark
                              :args (list cond1 (vl-flopcode-fix rhs1) rest)
                              :finalwidth (vl-expr->finalwidth target)
                              :finaltype :vl-unsigned)))
    (mv next warnings))

  ///
  (defthm vl-expr-welltyped-p-of-vl-flopcode-next-expr
    (implies (and (force (vl-stmtlist-p rx))
                  (force (vl-flopcodestmtlist-p rx))
                  (force (vl-expr-p target))
                  (force (vl-expr-welltyped-p target))
                  (force (posp (vl-expr->finalwidth target)))
                  (force (all-equalp (vl-expr->finalwidth target)
                                     (vl-exprlist->finalwidths
                                      (vl-flopcodestmtlist->lhses rx))))
                  (force (vl-expr-welltyped-p target))
                  (force (vl-warninglist-p warnings))
                  (force (vl-modelement-p elem)))
             (b* (((mv next ?warnings)
                   (vl-flopcode-next-expr rx target warnings elem)))
               (vl-expr-welltyped-p next)))
    :hints(("Goal"
            :do-not '(generalize fertilize)
            :expand ((:free (atts args finalwidth finaltype)
                            (vl-expr-welltyped-p
                             (vl-nonatom :vl-qmark atts args finalwidth finaltype))))
            :in-theory (enable vl-expr-welltyped-p)))))


(define vl-flopcode-synth-always
  ((x          "always block to try to synthesize"
               vl-always-p)
   (scary-regs "names of registers that are assigned to by multiple always
                blocks; these are too scary to try to synthesize"
               string-listp)
   (regs       "all the registers for the module"
               vl-regdecllist-p)
   (cvtregs    "accumulator for names of registers to convert into nets"
               string-listp)
   (delta      "delta for the new nets, instances, etc."
               vl-delta-p))
  :returns (mv (new-x? "nil on success, x unchanged on failure"
                       (equal (vl-always-p new-x?) (if new-x? t nil))
                       :hyp :fguard)
               (cvtregs string-listp :hyp :fguard)
               (delta   vl-delta-p   :hyp :fguard))
  :parents (flopcode)
  :short "Try to synthesize a single @('always') block into a flop."

  (b* (((vl-always x) x)
       ((mv clk body) (vl-match-posedge-clk x))

       ((unless clk)
        ;; Doesn't match "always @(posedge clk) body", so our transform does
        ;; not apply.  We don't want to cause any warnings here, it's just
        ;; not a flop-like always block.
        (mv x cvtregs delta))

       ((unless (eql (vl-expr->finalwidth clk) 1))
        ;; Can't do it: the VL_N_BIT_FLOP instance we write would be mis-sized.
        (mv x cvtregs
            (dwarn :type :vl-flopcode-fail
                   :msg "~a0: statement is too complex to synthesize.  Found ~
                         \"always @(posedge ~a1)\" and so we expected ~a1 to ~
                         have width 1, but its width is ~a2."
                   :args (list x clk (vl-expr->finalwidth clk))
                   :fatalp nil)))

       (prog    (vl-stmt-guts body))
       (warning (vl-flopcodeprog-debug prog x))
       ((when warning)
        ;; Not simple enough to deal with, but since it *does* at least sort of
        ;; look like a flop block, explain why we're failing with a warning.
        (mv x cvtregs (vl-warn-delta warning)))

       (target      (vl-flopcodeprog->target prog))
       (target-name (vl-idexpr->name target))

       (warning     (vl-always-check-reg target-name regs x))
       ((when warning)
        ;; Reg not declared or has some kind of problem, so explain why we're
        ;; failing...
        (mv x cvtregs (vl-warn-delta warning)))

       ((when (member-equal target-name scary-regs))
        (mv x cvtregs
            (dwarn :type :vl-flopcode-fail
                   :msg "~a0: cowardly refusing to synthesize always block ~
                         for ~a1 since other always blocks write to ~a1."
                   :args (list x target)
                   :fatalp nil)))

       ;; Everything looks good: statement is simple enough, types/widths
       ;; are good, not a register that is being written to elsewhere.  So,
       ;; let's synthesize it!
       ((vl-delta delta)  delta)
       (width             (vl-expr->finalwidth target))
       (flopmods          (vl-make-n-bit-flop width))
       (flopmod           (car flopmods))

       ((mv inst-name nf)    (vl-namefactory-plain-name (cat target-name "_inst")    delta.nf))
       ((mv next-name nf)    (vl-namefactory-plain-name (cat target-name "_next")    nf))
       ((mv delfree-name nf) (vl-namefactory-plain-name (cat target-name "_delfree") nf))

       ;; wire [n-1:0] foo_next;       // the data input to foo's register
       ;; wire [n-1:0] foo_delfree;    // output of foo's register but without delay
       ((mv next-expr    next-decl)    (vl-occform-mkwire next-name    width :loc x.loc))
       ((mv delfree-expr delfree-decl) (vl-occform-mkwire delfree-name width :loc x.loc))
       (delfree-decl
        (change-vl-netdecl delfree-decl
                           :atts (acons "VL_TARGET_REG" target (vl-netdecl->atts delfree-decl))))

       ;; assign foo_next = [converted next expr for foo]; // any truncation happens here
       ((mv next-rhs warnings) (vl-flopcode-next-expr (rev prog) target delta.warnings x))
       (next-ass               (make-vl-assign :lvalue next-expr :expr next-rhs :loc x.loc))

       ;; VL_N_BIT_FLOP foo_inst (foo_delfree, clk, foo_next); // always delay/trunc-free
       (inst     (vl-simple-instantiate flopmod inst-name
                                        (list delfree-expr clk next-expr)
                                        :loc x.loc))

       ;; assign #delay foo = foo_delfree;
       (delay    (vl-flopcodeprog->delay prog))
       (main-ass (make-vl-assign :lvalue target
                                 :expr   delfree-expr
                                 :loc    x.loc
                                 :delay  (and delay
                                              (let ((amt-expr (vl-make-index delay)))
                                                (make-vl-gatedelay :rise amt-expr
                                                                   :fall amt-expr
                                                                   :high amt-expr)))))

       (cvtregs  (cons target-name cvtregs))
       (delta    (change-vl-delta delta
                                  :nf       nf
                                  :netdecls (list* next-decl delfree-decl delta.netdecls)
                                  :assigns  (list* next-ass main-ass delta.assigns)
                                  :modinsts (cons inst delta.modinsts)
                                  :addmods  (append-without-guard flopmods delta.addmods)
                                  :warnings warnings)))
    (mv nil cvtregs delta))

  :prepwork ((local (in-theory (e/d (vl-flopcodeprog-p
                                     vl-flopcodeprog->target)
                                    (all-equalp))))

             (local (defthm car-under-iff-when-vl-modulelist-p
                      ;; stupidity...
                      (implies (vl-modulelist-p x)
                               (iff (car x)
                                    (consp x))))))

  ///
  (defthm vl-flopcode-synth-always-cvtregs-exist
    (implies (and (subsetp-equal cvtregs (vl-regdecllist->names regs))
                  (force (vl-regdecllist-p regs)))
             (b* (((mv ?new-x cvtregs ?delta)
                   (vl-flopcode-synth-always x scary-regs regs cvtregs delta)))
               (subsetp-equal cvtregs (vl-regdecllist->names regs))))))


(define vl-flopcode-synth-alwayses ((x          vl-alwayslist-p)
                                    (scary-regs string-listp)
                                    (regs       vl-regdecllist-p)
                                    (cvtregs    string-listp)
                                    (delta      vl-delta-p))
  :returns (mv (new-x   vl-alwayslist-p :hyp :fguard)
               (cvtregs string-listp    :hyp :fguard)
               (delta   vl-delta-p      :hyp :fguard))
  :parents (flopcode)
  (b* (((when (atom x))
        (mv nil cvtregs delta))
       ((mv new-car? cvtregs delta)
        (vl-flopcode-synth-always (car x) scary-regs regs cvtregs delta))
       ((mv new-cdr cvtregs delta)
        (vl-flopcode-synth-alwayses (cdr x) scary-regs regs cvtregs delta))
       (new-x (if new-car?
                  (cons new-car? new-cdr)
                new-cdr)))
    (mv new-x cvtregs delta))

  ///
  (defthm vl-flopcode-synth-alwayses-cvtregs-exist
    (implies (and (subsetp-equal cvtregs (vl-regdecllist->names regs))
                  (force (vl-regdecllist-p regs)))
             (b* (((mv ?new-x cvtregs ?delta)
                   (vl-flopcode-synth-alwayses x scary-regs regs cvtregs delta)))
               (subsetp-equal cvtregs (vl-regdecllist->names regs))))))
