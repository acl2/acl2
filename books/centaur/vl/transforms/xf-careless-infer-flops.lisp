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
(include-book "../primitives")
(include-book "../mlib/stmt-tools")
(include-book "../mlib/lvalues")
(include-book "../mlib/range-tools")
(include-book "../mlib/namefactory")
(include-book "../mlib/filter")
(include-book "occform/gen-util")
(local (include-book "../util/arithmetic"))
(local (in-theory (disable vl-maybe-module-p-when-vl-module-p)))
(include-book "xf-infer-flops")


(defsection vl-careless-match/check-latch
  ;; Only checks the sensitivity list; skips checks about combinational loops,
  ;; LHS being an identifier, etc.
  (defund vl-careless-match/check-latch (x warnings)
    "Returns (mv successp condition-expr lhs-expr rhs-expr)"
    (declare (xargs :guard (and (vl-always-p x)
                                (vl-warninglist-p warnings))))
    
    (b* (((mv successp ctrl condition lhs rhs)
          (vl-pattern-match-latch x))
         ((unless successp)
          (mv warnings nil nil nil nil))

         (starp (vl-eventcontrol->starp ctrl))
         (atoms (vl-eventcontrol->atoms ctrl))

         (rhs-wires (vl-expr-names rhs))
         (condition-wires (vl-expr-names condition))
         (need-wires (if starp
                         nil
                       (append rhs-wires condition-wires)))
         
         (have-wires (if starp
                         nil
                       (vl-idexprlist->names (vl-evatomlist->exprs atoms))))
         
         ((unless (subsetp-equal need-wires have-wires))
          (mv (cons (make-vl-warning
                     :type :vl-latch-fail
                     :msg "~a0: failing to infer a latch because the sensitivity ~
                            list omits ~&1, which would seem to be necessary."
                     :args (list x (set-difference-equal need-wires have-wires)))
                    warnings)
              nil nil nil nil)))
      (mv warnings t condition lhs rhs)))

  (local (in-theory (enable vl-careless-match/check-latch)))

  (defthm vl-warninglist-p-of-vl-careless-match/check-latch
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-careless-match/check-latch x warnings))))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm booleanp-of-vl-careless-match/check-latch
    (booleanp (mv-nth 1 (vl-careless-match/check-latch x warnings)))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm vl-careless-match/check-latch-basics
    (implies (force (vl-always-p x))
             (and
              (equal (vl-expr-p (mv-nth 2 (vl-careless-match/check-latch x warnings)))
                     (if (mv-nth 1 (vl-careless-match/check-latch x warnings)) t nil))
              (equal (vl-expr-p (mv-nth 3 (vl-careless-match/check-latch x warnings)))
                     (if (mv-nth 1 (vl-careless-match/check-latch x warnings)) t nil))
              (equal (vl-expr-p (mv-nth 4 (vl-careless-match/check-latch x warnings)))
                     (if (mv-nth 1 (vl-careless-match/check-latch x warnings)) t
                       nil))))))


(defsection vl-find-regdecl-list
  (defund vl-find-regdecl-list (names regdecls)
    (declare (xargs :guard (and (string-listp names)
                                (vl-regdecllist-p regdecls))))
    (if (atom names)
        nil
      (let ((look (vl-find-regdecl (car names) regdecls)))
        (if look
            (cons look (vl-find-regdecl-list (cdr names) regdecls))
          (vl-find-regdecl-list (cdr names) regdecls)))))

  (defthm vl-regdecllist-p-of-vl-find-regdecl-list
    (implies (vl-regdecllist-p regdecls)
             (vl-regdecllist-p (vl-find-regdecl-list names regdecls)))
    :hints(("Goal" :in-theory (enable vl-find-regdecl-list)))))

       

; Actual inference of flops and latches:

(defsection vl-always-careless-infer-latch/flop
  :parents (flop-inference latch-inference)
  :short "Try to infer a flop or latch from an <tt>always</tt> block."

  :long "<p><b>Signature:</b> @(call vl-always-careless-infer-latch/flop) returns
<tt>(mv successp warnings regs inst addmods decls assigns nf)</tt>.</p>

<h5>Inputs</h5>
<ul>
 <li><tt>x</tt>, an always block we may infer a flop from</li>
 <li><tt>mod</tt>, the module in which <tt>x</tt> resides</li>
 <li><tt>warnings</tt>, a warnings accumulator</li>
 <li><tt>nf</tt>, a @(see vl-namefactory-p) for generating fresh wire names.</li>
</ul>

<p>We may extend <tt>warnings</tt> when <tt>x</tt> looks like it should
be a flop, but it does not appear safe to convert it.</p>

<p><tt>successp</tt> is true only when we wish to convert this always statement
into a flop or latch.  Aside from <tt>successp</tt> and <tt>warnings</tt>, the
other outputs are only useful when <tt>successp</tt> holds.</p>

<h5>Outputs (when successp)</h5>

<ul>

<li><tt>regs</tt> are the @(see vl-regdecl-p)s that need to be converted into
ordinary wires,</li>

<li><tt>inst</tt> is a new instance of a <tt>VL_<i>N</i>_BIT_FLOP</tt> or
<tt>VL_<i>N</i>_BIT_LATCH</tt> that must be added to the module to replace this
always block,</li>

<li><tt>addmods</tt> are any modules that need to be added to the module list
to ensure that we retain @(see completeness) as we introduce
<tt>inst</tt>,</li>

<li><tt>decls</tt> are any new @(see vl-netdecl-p)s that need to be added
to the module,</li>

<li><tt>assigns</tt> are any new @(see vl-assign-p)s that need to be added to
the module.</li>

<li><tt>nf</tt> is the updated name factory.</li>

</ul>"

  (local (defthm stringp-of-car-of-string-listp
           (implies (and (string-listp x)
                         (consp x))
                    (stringp (car x)))))

  (defund vl-always-careless-infer-latch/flop (x mod warnings nf)
    "Returns (mv successp warnings reg inst addmods decls assigns nf)"
    (declare (xargs :guard (and (vl-always-p x)
                                (vl-module-p mod)
                                (vl-warninglist-p warnings)
                                (vl-namefactory-p nf))))

    (b* (((mv warnings successp type clk-expr lhs-expr rhs-expr delay)

          ;; Try to match either a flop or latch.
          (b* (((mv successp clk-expr lhs-expr rhs-expr delay)
                (vl-pattern-match-flop x))
               ((when successp)
                (mv warnings t :flop clk-expr lhs-expr rhs-expr delay))
               ((mv warnings successp clk-expr lhs-expr rhs-expr)
                (vl-careless-match/check-latch x warnings)))
              (mv warnings successp :latch clk-expr lhs-expr rhs-expr
                  ;; BOZO maybe eventually think about delays on latches
                  delay)))

         ((unless successp)
          (mv nil warnings nil nil nil nil nil nf))

         (loc        (vl-always->loc x))
         (type-str   (if (eq type :flop) "flop" "latch"))
         (fail-type  (if (eq type :flop) :vl-flop-fail :vl-latch-fail))

         ;; We only try to infer a flop/latch if there is a register
         ;; declaration which seems to be sensible.  In particular, the regdecl
         ;; must not have any array dimensions, and its range needs to be
         ;; resolved.

         (lhs-names (vl-expr-names lhs-expr))
         ((unless (consp lhs-names))
          (mv nil
              (cons (make-vl-warning
                     :type fail-type
                     :msg "~a0: failing to infer a ~s1 because of the bizarre ~
                           situation that the LHS is ~a2, which has no ~
                           identifiers in it."
                     :args (list x type-str lhs-expr))
                    warnings)
              nil nil nil nil nil nf))
         (regs       (vl-find-regdecl-list lhs-names
                                           (vl-module->regdecls mod)))
         ((unless (equal (len regs) (len lhs-names)))
          (mv nil
              (cons (make-vl-warning
                     :type fail-type
                     :msg "~a0: despite its ~s1-like appearance, we fail to ~
                           infer a ~s1 because ~s2 is not declared to be a reg."
                     :args (list x type-str
                                 (difference
                                  (mergesort lhs-names)
                                  (mergesort (vl-regdecllist->names regs)))))
                    warnings)
              nil nil nil nil nil nf))

         (size (vl-expr->finalwidth lhs-expr))
         ((unless size)
          (mv nil
              (cons (make-vl-warning
                     :type fail-type
                     :msg "~a0: Could not make a ~s1 because ~a2 is not sized."
                     :args (list x type-str lhs-expr))
                    warnings)
              nil nil nil nil nil nf))

         ((when (eql size 0))
          (mv nil
              (cons (make-vl-warning
                     :type fail-type
                     :msg "~a0: Could not make a ~s1 because ~a2 has size 0."
                     :args (list x type-str lhs-expr))
                    warnings)
              nil nil nil nil nil nf))
         ;; At this point, things seem to be working out.  The always statement
         ;; matches the desired pattern, lhs is known to be a register, it's
         ;; not assigned to elsewhere, etc.  We're going to go ahead and infer
         ;; a flop/latch.  The basic idea is to replace the always statement
         ;; with an instance of some VL_N_BIT_FLOP or VL_N_BIT_LATCH.  We can
         ;; determine N by looking at the size of the register.

         (addmods (if (eq type :flop)
                      (vl-make-n-bit-flop size)
                    (vl-make-n-bit-latch size)))
         (modname (vl-module->name (car addmods)))


         ;; Something tricky is that the rhs expression might be wider than
         ;; the lhs expression.  We want to allow it to be truncated.  But we
         ;; haven't yet computed sizes.  So, our idea is to introduce a new,
         ;; temporary wire that has the size of lhs, and assign rhs to it.
         ;; Later, the assign can be truncated like any other assignment.

         ((mv rhs-temp-name nf)
          (vl-namefactory-plain-name (str::cat (car lhs-names)
                                               "_temp_rhs") nf))

         (rhs-temp-expr (make-vl-atom :guts (make-vl-id :name rhs-temp-name)))
         (rhs-temp-decl (make-vl-netdecl :loc loc
                                         :name rhs-temp-name
                                         :type :vl-wire
                                         :range (vl-make-n-bit-range size)))
         (rhs-temp-assign (make-vl-assign :loc loc
                                          :lvalue rhs-temp-expr
                                          :expr rhs-expr))

         ;; HACK for delays on flops.  (Not trying latches yet).
         ;; If there's a delay like always @(posedge clk) q <= #1 d, then we
         ;; want to essentially replace q with a temporary wire and then add
         ;; assign #1 q = tmp;  To make the code easy to write, we just always
         ;; introduce such a temp wire.

         ((mv lhs-temp-name nf)
          (vl-namefactory-plain-name (str::cat (car lhs-names) "_temp_lhs") nf))

         (lhs-temp-expr (make-vl-atom :guts (make-vl-id :name lhs-temp-name)))
         (lhs-temp-decl (make-vl-netdecl :loc loc
                                         :name lhs-temp-name
                                         :type :vl-wire
                                         :range (vl-make-n-bit-range size)))
         (delay (and delay
                     (not (equal delay 0))
                     (make-vl-gatedelay :rise (vl-make-index delay)
                                        :fall (vl-make-index delay)
                                        :high (vl-make-index delay))))

         (lhs-temp-assign (make-vl-assign :loc loc
                                          :lvalue lhs-expr
                                          :expr lhs-temp-expr
                                          :delay delay))

         (q-arg    (make-vl-plainarg :expr lhs-temp-expr :portname "q" :dir :vl-output))
         (clk-arg  (make-vl-plainarg :expr clk-expr :portname "clk" :dir :vl-input))
         (d-arg    (make-vl-plainarg :expr rhs-temp-expr :portname "d" :dir :vl-input))
         (portargs (vl-arguments nil (list q-arg clk-arg d-arg)))

         ((mv inst-name nf)
          (vl-namefactory-plain-name (str::cat (car lhs-names) "_inst") nf))

         (inst    (make-vl-modinst :instname inst-name
                                   :modname modname
                                   :range nil
                                   :paramargs (vl-arguments nil nil)
                                   :portargs portargs
                                   ;; atts?
                                   :loc loc)))

        (mv t warnings regs inst addmods
            (list rhs-temp-decl lhs-temp-decl)
            (list rhs-temp-assign lhs-temp-assign)
            nf)))

  (defmvtypes vl-always-careless-infer-latch/flop
    (booleanp   ; successp
     nil        ; warnings
     nil        ; regs
     nil        ; inst
     true-listp ; addmods
     true-listp ; decls
     true-listp ; assigns
     nil        ; nf
     ))

  (local (in-theory (enable vl-always-careless-infer-latch/flop)))

  (defthm vl-warninglist-p-of-vl-always-careless-infer-latch/flop
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-always-careless-infer-latch/flop x mod warnings nf)))))

  (defthm vl-always-careless-infer-latch/flop-basics
    (implies (and (force (vl-always-p x))
                  (force (vl-module-p mod))
                  (force (vl-namefactory-p nf)))
             (and
              ;; reg
              (equal
               (vl-regdecllist-p (mv-nth 2 (vl-always-careless-infer-latch/flop x mod warnings nf)))
               t)
              ;; inst
              (equal
               (vl-modinst-p (mv-nth 3 (vl-always-careless-infer-latch/flop x mod warnings nf)))
               (if (mv-nth 0 (vl-always-careless-infer-latch/flop x mod warnings nf)) t nil))
              ;; addmods
              (vl-modulelist-p
               (mv-nth 4 (vl-always-careless-infer-latch/flop x mod warnings nf)))
              ;; decls
              (vl-netdecllist-p
               (mv-nth 5 (vl-always-careless-infer-latch/flop x mod warnings nf)))
              ;; assigns
              (vl-assignlist-p
               (mv-nth 6 (vl-always-careless-infer-latch/flop x mod warnings nf)))
              ;; nf
              (vl-namefactory-p
               (mv-nth 7 (vl-always-careless-infer-latch/flop x mod warnings nf)))))))



(defsection vl-alwayslist-careless-infer-latches/flops
  :parents (flop-inference latch-inference)
  :short "Try to infer latches and flops from a list of <tt>always</tt>
blocks."

  :long "<p><b>Signature:</b> @(call vl-alwayslist-careless-infer-latches/flops) returns
<tt>(mv warnings alwayses regs insts addmods decls assigns nf)</tt>.</p>

<p>We are given <tt>x</tt>, the list of always blocks for the module
<tt>mod</tt>, a name index for <tt>mod</tt>, and the warnings accumulator for
<tt>mod</tt>.  We try to infer flops for each <tt>always</tt> in the list, and
return:</p>

<ul>

<li><tt>alwayses</tt>, a new list of alwayses where we remove any always
 statements that have been successfully converted into flops,</li>

<li><tt>regs</tt>, a list of regdecls that need to be converted into wires,</li>

<li><tt>insts</tt>, a list of module instances that need to be added to the
module (e.g., this list will contain the explicit flop instances that represent
the deleted always blocks),</li>

<li><tt>addmods</tt>, a list of modules that need to be added to the module
list (e.g., this list might include <tt>VL_3_BIT_FLOP</tt> if we've instantiated
it.)</li>

<li><tt>decls</tt> are any new @(see vl-netdecl-p)s that need to be added
to the module,</li>

<li><tt>assigns</tt> are any new @(see vl-assign-p)s that need to be added to
the module.</li>

<li><tt>nf</tt> is the updated name factory.</li>

</ul>"

  (defund vl-alwayslist-careless-infer-latches/flops (x mod warnings nf)
    "Returns (mv warnings alwayses regs insts addmods decls assigns nf)"
    (declare (xargs :guard (and (vl-alwayslist-p x)
                                (vl-module-p mod)
                                (vl-warninglist-p warnings)
                                (vl-namefactory-p nf))))
    (b* (((when (atom x))
          (mv warnings nil nil nil nil nil nil nf))
         ((mv successp1 warnings regs1 inst1 addmods1 decls1 assigns1 nf)
          (vl-always-careless-infer-latch/flop (car x) mod warnings nf))
         ((mv warnings alwayses2 regs2 insts2 addmods2 decls2 assigns2 nf)
          (vl-alwayslist-careless-infer-latches/flops (cdr x) mod warnings nf)))
        (if successp1
            (mv warnings
                alwayses2
                (append (list-fix regs1) regs2)
                (cons inst1 insts2)
                (append addmods1 addmods2)
                (append decls1 decls2)
                (append assigns1 assigns2)
                nf)
          (mv warnings
              (cons (car x) alwayses2)
              regs2
              insts2
              addmods2
              decls2
              assigns2
              nf))))

  (defmvtypes vl-alwayslist-careless-infer-latches/flops
    (nil        ; warnings
     true-listp ; alwayses
     true-listp ; regs
     true-listp ; insts
     true-listp ; addmods
     true-listp ; decls
     true-listp ; assigns
     nil        ; nf
     ))

  (local (in-theory (enable vl-alwayslist-careless-infer-latches/flops)))

  (defthm vl-warninglist-p-of-vl-alwayslist-careless-infer-latches/flops
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-alwayslist-careless-infer-latches/flops x mod warnings nf)))))

  (defthm vl-alwayslist-careless-infer-latches/flops-basics
    (implies (and (force (vl-alwayslist-p x))
                  (force (vl-module-p mod))
                  (force (vl-namefactory-p nf)))
             (let ((ret (vl-alwayslist-careless-infer-latches/flops x mod warnings nf)))
               (and (vl-alwayslist-p  (mv-nth 1 ret))
                    (vl-regdecllist-p (mv-nth 2 ret))
                    (vl-modinstlist-p (mv-nth 3 ret))
                    (vl-modulelist-p  (mv-nth 4 ret))
                    (vl-netdecllist-p (mv-nth 5 ret))
                    (vl-assignlist-p  (mv-nth 6 ret))
                    (vl-namefactory-p (mv-nth 7 ret))
                    )))))







(defsection vl-module-careless-infer-latches/flops

  (defund vl-module-careless-infer-latches/flops (x)
    "Returns (MV X-PRIME ADDMODS)"
    (declare (xargs :guard (vl-module-p x)))
    (b* (((when (vl-module->hands-offp x))
          (mv x nil))
         (alwayses (vl-module->alwayses x))

         ((unless alwayses)
          ;; Optimization.  Skip modules that don't have any always statements.
          (mv x nil))

         (warnings (vl-module->warnings x))
         (regdecls (vl-module->regdecls x))
         (netdecls (vl-module->netdecls x))
         (modinsts (vl-module->modinsts x))
         (assigns  (vl-module->assigns x))

         (nf       (vl-starting-namefactory x))

         ((mv warnings alwayses flop-regs flop-insts addmods new-decls new-assigns nf)
          (vl-alwayslist-careless-infer-latches/flops alwayses x warnings nf))

         (-        (vl-free-namefactory nf))
         (flop-regs      (mergesort flop-regs)) ;; remove duplicates
         (flop-reg-names (vl-regdecllist->names flop-regs))
         (regdecls       (vl-delete-regdecls flop-reg-names regdecls))

         (flop-netdecls  (vl-convert-regdecllist-to-netdecllist flop-regs))
         (netdecls       (append new-decls flop-netdecls netdecls))

         (assigns        (append new-assigns assigns))

         ;; BOZO this might not be optimal for sorting.  Is there any simple
         ;; rule about whether the flops should come first or last?
         (modinsts       (append flop-insts modinsts))

         (x-prime (change-vl-module x
                                    :assigns assigns
                                    :alwayses alwayses
                                    :regdecls regdecls
                                    :netdecls netdecls
                                    :modinsts modinsts
                                    :warnings warnings)))
        (mv x-prime addmods)))

  (defmvtypes vl-module-careless-infer-latches/flops (nil true-listp))

  (local (in-theory (enable vl-module-careless-infer-latches/flops)))

  (defthm vl-module-p-of-vl-module-careless-infer-latches/flops
    (implies (force (vl-module-p x))
             (vl-module-p (mv-nth 0 (vl-module-careless-infer-latches/flops x)))))

  (defthm vl-module->name-of-vl-module-careless-infer-latches/flops
    (equal (vl-module->name (mv-nth 0 (vl-module-careless-infer-latches/flops x)))
           (vl-module->name x)))

  (defthm vl-modulelist-p-of-vl-module-careless-infer-latches/flops
    (implies (force (vl-module-p x))
             (vl-modulelist-p (mv-nth 1 (vl-module-careless-infer-latches/flops x))))))




(defsection vl-modulelist-careless-infer-latches/flops-aux

  (defund vl-modulelist-careless-infer-latches/flops-aux (x)
    "Returns (MV X-PRIME ADDMODS)"
    (declare (xargs :guard (vl-modulelist-p x)))
    (if (atom x)
        (mv nil nil)
      (b* (((mv car-prime car-addmods) (vl-module-careless-infer-latches/flops (car x)))
           ((mv cdr-prime cdr-addmods) (vl-modulelist-careless-infer-latches/flops-aux (cdr x))))
          (mv (cons car-prime cdr-prime)
              (append car-addmods cdr-addmods)))))

  (defmvtypes vl-modulelist-careless-infer-latches/flops-aux
    (true-listp true-listp))

  (local (in-theory (enable vl-modulelist-careless-infer-latches/flops-aux)))

  (defthm vl-modulelist-p-of-vl-modulelist-careless-infer-latches/flops-aux
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (mv-nth 0 (vl-modulelist-careless-infer-latches/flops-aux x)))))

  (defthm vl-modulelist->names-of-vl-modulelist-careless-infer-latches/flops-aux
    (equal (vl-modulelist->names (mv-nth 0 (vl-modulelist-careless-infer-latches/flops-aux x)))
           (vl-modulelist->names x)))

  (defthm vl-modulelist-p-of-vl-modulelist-careless-infer-latches/flops-aux-2
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (mv-nth 1 (vl-modulelist-careless-infer-latches/flops-aux x))))))


(defsection vl-modulelist-careless-infer-latches/flops

  (defund vl-modulelist-careless-infer-latches/flops (x)
    (declare (xargs :guard (and (vl-modulelist-p x)
                                (uniquep (vl-modulelist->names x)))))
    (b* (((mv x-prime addmods)
          (vl-modulelist-careless-infer-latches/flops-aux x))
         (merged
          (mergesort (revappend addmods x-prime)))

         (merged-names (vl-modulelist->names merged))

         ((unless (uniquep merged-names))

; I think it's okay to cause an error in this case.  The only way we would
; destroy uniqueness is if the user has introduced a module named VL_N_BIT_FLOP
; and we're now trying to introduce a competing definition for it.  In the
; logic, we just return X, so that flop inference effectively just completely
; fails and changes no modules if any collisions would be introduced.

          (prog2$
           (er hard? 'vl-modulelist-careless-infer-latches/flops
               "Name collision after flop inference.  Duplicate names are: ~&0."
               (duplicated-members merged-names))
           x)))

        merged))

  (local (in-theory (enable vl-modulelist-careless-infer-latches/flops)))

  (defthm vl-modulelist-p-of-vl-modulelist-careless-infer-latches/flops
    (implies (vl-modulelist-p x)
             (vl-modulelist-p (vl-modulelist-careless-infer-latches/flops x))))

  (defthm unique-names-of-vl-modulelist-careless-infer-latches/flops
    (implies (no-duplicatesp-equal (vl-modulelist->names x))
             (no-duplicatesp-equal (vl-modulelist->names (vl-modulelist-careless-infer-latches/flops x))))))

