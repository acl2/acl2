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
(include-book "flopcode-synth")
(include-book "latchcode")
(local (include-book "../../util/arithmetic"))

(defxdoc synthalways
  :parents (always-top)
  :short "Main transform for synthesizing simple @('always') blocks into flops
and latch module instances."

  :long "<p>This is a sort of back-end transform that does the final conversion
of already-simplified @('always') statements into flops and latches.  This is
quite similar to how the @(see occform) transform converts Verilog expressions
into explicit instances of generated modules, except that here we are
converting @('always') statements into instances of flop/latch modules.</p>

<p>Notes:</p>

<ul>

<li>We support only a very small set of @('always') statements here; see @(see
flopcode) and @(see latchcode).  Typically you will want to run other
statement-simplifying transformations first to get them into this form; see
@(see always-top).</li>

<li>We expect expressions to be sized so that we can tell which sizes of
flop/latch modules to introduce.</li>

<li>We expect modules to be free of @('initial') statements, otherwise we could
produce invalid modules when we convert registers into nets.</li>

<p>This is a best-effort style transform which will leave unsupported
@('always') blocks alone.  We usually follow up with @(see elimalways) to throw
out modules whose @('always') blocks were not supported.</p>

</ul>")

(define vl-module-synthalways
  ((x         vl-module-p)
   (careful-p booleanp "be careful when processing latches?"))
  :returns (mv (new-x   vl-module-p     :hyp :fguard)
               (addmods vl-modulelist-p :hyp :fguard))
  :parents (flopcode)
  :short "Synthesize simple @('always') blocks in a module."

  (b* (((vl-module x) x)

       ((when (vl-module->hands-offp x))
        ;; Don't mess with it.
        (mv x nil))

       ((unless (consp x.alwayses))
        ;; Optimization: nothing to do, so do nothing.
        (mv x nil))

       ((when (consp x.taskdecls))
        ;; BOZO if we want to support modules with tasks, we need to be able to
        ;; figure out whether they write to registers, and make sure they
        ;; aren't writing to the registers we're synthesizing.  For now, just
        ;; don't try to support modules with tasks.
        (b* ((w (make-vl-warning
                 :type :vl-synthalways-fail
                 :msg "Not trying to synthesize always blocks in ~m0 since it ~
                       has tasks."
                 :args (list x.name)
                 :fn __function__)))
            (mv (change-vl-module x :warnings (cons w x.warnings))
                nil)))

       ((when (consp x.initials))
        ;; BOZO it seems hard to support modules with initial statements.
        ;; Imagine something as simple as:
        ;;
        ;;   reg [3:0] q;
        ;;   always @(posedge clk) q <= d;
        ;;   initial q = 0;
        ;;
        ;; Here, after our synthesis we would have something like:
        ;;
        ;;   wire [3:0] q;
        ;;   wire [3:0] q_next = d;
        ;;   VL_4_BIT_FLOP q_reg (q, clk, q_next);
        ;;   initial q = 0;
        ;;
        ;; The initial statement is now wrong, because it's trying to assign a
        ;; value to q, which has become a wire instead of a reg.  So really
        ;; we'd need to change it to something like:
        ;;
        ;;  initial q_reg.q = 0;
        ;;
        ;; but that's not good enough.  The actual reg is distributed among the
        ;; VL_1_BIT_FLOPs inside of q_reg, so we'd really need something like:
        ;;
        ;;  initial { q_reg.bit_3.q, ..., q_reg.bit_0.q } = 0;
        ;;
        ;; This seems ridiculous.  Let's just not deal with initial statements.
        ;; It seems reasonable to expect that they should be removed when we're
        ;; trying to do synthesis.
        (b* ((w (make-vl-warning
                 :type :vl-synthalways-fail
                 :msg "Not trying to synthesize always blocks in ~m0 since it ~
                       has initial statements."
                 :args (list x.name)
                 :fn __function__)))
          (mv (change-vl-module x :warnings (cons w x.warnings))
              nil)))

       (delta      (vl-starting-delta x))
       (delta      (change-vl-delta delta
                                    ;; We'll strictly add netdecls, modinsts,
                                    ;; and assigns, so pre-populate them.
                                    :netdecls x.netdecls
                                    :modinsts x.modinsts
                                    :assigns  x.assigns))
       (scary-regs (vl-always-scary-regs x.alwayses))
       (cvtregs    nil)

       ;; We just separately rewrite the flops and latches.
       ((mv new-alwayses cvtregs delta)
        (vl-flopcode-synth-alwayses x.alwayses scary-regs x.regdecls
                                    cvtregs delta))
       ((mv new-alwayses cvtregs delta)
        (vl-latchcode-synth-alwayses new-alwayses scary-regs x.regdecls
                                     cvtregs delta careful-p))

       ((vl-delta delta) (vl-free-delta delta))

       ((mv regdecls-to-convert new-regdecls)
        ;; We already know all of the cvtregs are among the regdecls and have
        ;; no arrdims.  So, we can just freely convert look them up and convert
        ;; them here.
        (vl-filter-regdecls cvtregs x.regdecls))

       (new-netdecls (append (vl-always-convert-regs regdecls-to-convert)
                             delta.netdecls))

       (new-x (change-vl-module x
                                :netdecls new-netdecls
                                :regdecls new-regdecls
                                :assigns  delta.assigns
                                :modinsts delta.modinsts
                                :alwayses new-alwayses
                                :warnings delta.warnings)))
    (mv new-x delta.addmods))

  ///
  (defthm vl-module->name-of-vl-module-synthalways
    (b* (((mv new-x ?addmods) (vl-module-synthalways x careful-p)))
      (equal (vl-module->name new-x)
             (vl-module->name x)))))


(define vl-modulelist-synthalways-aux ((x vl-modulelist-p)
                                       (careful-p booleanp))
  :returns (mv (new-x vl-modulelist-p   :hyp :fguard)
               (addmods vl-modulelist-p :hyp :fguard))
  :parents (flopcode)
  (b* (((when (atom x))
        (mv nil nil))
       ((mv car addmods1) (vl-module-synthalways (car x) careful-p))
       ((mv cdr addmods2) (vl-modulelist-synthalways-aux (cdr x) careful-p)))
    (mv (cons car cdr)
        (append-without-guard addmods1 addmods2)))

  ///
  (defthm vl-modulelist->names-of-vl-modulelist-synthalways-aux
    (b* (((mv new-x ?addmods) (vl-modulelist-synthalways-aux x careful-p)))
      (equal (vl-modulelist->names new-x)
             (vl-modulelist->names x)))))


(define vl-modulelist-synthalways ((x vl-modulelist-p)
                                   &key
                                   ((careful-p booleanp) 't))
  :returns (new-x :hyp :fguard
                  (and (vl-modulelist-p new-x)
                       (no-duplicatesp-equal (vl-modulelist->names new-x))))
  :parents (flopcode)
  :short "Top-level @(see flopcode) transform."
  (b* (((mv new-x addmods)
        (vl-modulelist-synthalways-aux x careful-p))
       (all-mods  (union (mergesort new-x) (mergesort addmods)))
       (all-names (vl-modulelist->names all-mods))
       ((unless (uniquep all-names))
        (er hard? __function__ "Name collision: ~x0"
            (duplicated-members all-names))))
    all-mods))

