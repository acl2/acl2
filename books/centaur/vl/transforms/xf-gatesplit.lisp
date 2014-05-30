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
(include-book "../mlib/expr-tools")
(include-book "../mlib/range-tools")
(include-book "../mlib/namefactory")
(include-book "../mlib/port-tools")
(local (include-book "../util/arithmetic"))
(local (include-book "tools/do-not" :dir :system))
(local (acl2::do-not fertilize))

(defxdoc gatesplit
  :parents (transforms)
  :short "Split up gates with \"extra\" terminals."

  :long "<h3>Gate Splitting</h3>

<p>This transformation is responsible for splitting up multi-input gates into
multiple one-input gates for @('buf') and @('not'), or two-input gates for
@('and'), @('or'), etc.</p>

<p><b>Ordering Notes.</b> This transformation must be done after widths have
been computed, and after @(see replicate) has been run to eliminate any arrays.
Replication is necessary for certain well-formedness checks on the widths to
succeed.</p>

<p>Unlike occforming, we lay down gates directly instead of introducing new
modules.  It might be nicer to do it the other way and introduce modules
instead, since then the module instance could keep the same name as the gate.
On the other hand, the code to just introduce gates is simpler, and it would
probably suffice to just use good names or annotations to explain where the
gates come from.</p>")

(local (xdoc::set-default-parents gatesplit))

;; Some stupid little rules to avoid case splits

(local (defthm vl-gatetype-p-when-not/buf
         (implies (member type '(:vl-not :vl-buf))
                  (vl-gatetype-p type))))

(local (defthm vl-gatetype-p-when-and/etc
         (implies (member type '(:vl-and :vl-or :vl-xor :vl-xnor))
                  (vl-gatetype-p type))))

(local (defthm vl-gatetype-p-when-nand/nor
         (implies (member-eq type '(:vl-nand :vl-nor))
                  (vl-gatetype-p type))))

(local (in-theory (disable acl2::subsetp-of-cons
                           acl2::member-of-cons)))


(define vl-make-temporary-wires
  :short "Generate expressions and declarations for some fresh, one-bit wires."
  ((prefix stringp           "Prefix for name generation.")
   (i      natp              "How many wires to create.")
   (nf     vl-namefactory-p  "Namefactory for generating fresh names.")
   (loc    vl-location-p     "Location for the new wire declarations."))
  :returns
  (mv (exprs    (and (vl-exprlist-p exprs)
                     (equal (len exprs) (nfix i)))
                "Expressions for the new one-bit wires.")
      (netdecls vl-netdecllist-p
                :hyp (force (vl-location-p loc))
                "Declarations for the new wires.")
      (nf       vl-namefactory-p
                :hyp (and (force (stringp prefix))
                          (force (vl-namefactory-p nf)))))
  (b* (((when (zp i))
        (mv nil nil nf))
       ((mv new-name nf)
        (vl-namefactory-indexed-name prefix nf))
       (expr1    (make-vl-atom :guts (make-vl-id :name new-name)
                               :finalwidth 1
                               :finaltype :vl-unsigned))
       (decl1    (make-vl-netdecl :name new-name
                                  :type :vl-wire
                                  :range nil
                                  :loc loc))
       ((mv exprs decls nf)
        (vl-make-temporary-wires prefix (- i 1) nf loc)))

    (mv (cons expr1 exprs)
        (cons decl1 decls)
        nf))
  ///
  (defmvtypes vl-make-temporary-wires (true-listp true-listp))
  (defthm vl-make-temporary-wires-0-under-iff
    (iff (mv-nth 0 (vl-make-temporary-wires prefix i nf loc))
         (not (zp i)))))



(define vl-make-gates-for-buf/not
  :parents (vl-gatesplit-buf/not)
  :short "Produce a list of @('buf') or @('not') gates."
  ((in       vl-plainarg-p      "Input terminal to a multi-output buf/not gate.")
   (outs     vl-plainarglist-p  "Output terminals for the gate.")
   (x        vl-gateinst-p      "The gate itself, used for good error messages,
                                 and also to identify which kind of gate we are
                                 working with, its location, etc.")
   (nf       vl-namefactory-p   "For generating fresh names.")
   (warnings vl-warninglist-p   "Ordinary @(see warnings) accumulator."))
  :returns
  (mv (new-warnings  vl-warninglist-p)
      (new-gateinsts vl-gateinstlist-p :hyp :fguard
                     "New gate instances that individually drive the @('outs').")
      (nf            vl-namefactory-p :hyp :fguard))
  :long "<p>We produce a list of gateinsts of the appropriate type, one to
drive each output in @('outs') with @('in').</p>"

  (b* (((when (atom outs))
        (mv (ok) nil nf))
       (warnings
        ;; The width-checks below only make sense if there is no range.
        ;; Hence, we double-check that there is no range.
        (if (not (vl-gateinst->range x))
            (ok)
          (fatal :type :vl-bad-gate
                 :msg "~a0: expected all instance arrays to have been ~
                       eliminated, but found a range.  Did you forget to run ~
                       the replicate transform?"
                 :args (list x))))
       (warnings
        ;; Cadence does not allow a multi-bit wire to be used as the output of
        ;; a gate.  So, I disallow it as well.
        (let ((expr (vl-plainarg->expr (car outs))))
          (if (and expr (equal (vl-expr->finalwidth expr) 1))
              (ok)
            (fatal :type :vl-bad-gate
                   :msg "~a0: output terminal has width ~x1 but we only ~
                         support 1-bit outputs.  The expression for the bad ~
                         terminal is ~a2."
                   :args (list x (and expr (vl-expr->finalwidth expr)) expr)))))
       ;; Now we make the actual gate for this output.  We add an attribute
       ;; saying the name of the gate instance which was being split up.
       (origname-s     (or (vl-gateinst->name x) "unnamed"))
       (origname-atom  (make-vl-atom :guts (vl-string origname-s)))
       (atts           (cons (cons "VL_GATESPLIT" origname-atom)
                             (vl-gateinst->atts x)))

       ;; We also try to base the new name on the original name of the gate,
       ;; to make it relatively predictable.
       ((mv new-name nf) (vl-namefactory-indexed-name origname-s nf))
       (inst1     (make-vl-gateinst :name new-name
                                    :type (vl-gateinst->type x)
                                    :args (cons in (list (car outs)))
                                    :loc (vl-gateinst->loc x)
                                    :atts atts))
       ((mv warnings rest nf)
        (vl-make-gates-for-buf/not in (cdr outs) x nf warnings)))
    (mv (ok) (cons inst1 rest) nf))
  ///
  (defmvtypes vl-make-gates-for-buf/not (nil true-listp nil)))


(define vl-gatesplit-buf/not
  :short "Split up a multi-output @('buf') or @('not') gate, if necessary."
  ((x        vl-gateinst-p)
   (nf       vl-namefactory-p)
   (warnings vl-warninglist-p))
  :guard (member-eq (vl-gateinst->type x) '(:vl-not :vl-buf))
  :returns
  (mv (warnings      vl-warninglist-p)
      (new-gateinsts vl-gateinstlist-p :hyp :fguard)
      (nf            vl-namefactory-p :hyp :fguard))
  :long "<p>From Section 7.3, @('buf') and @('not') gates have one input (the
last terminal) and one or more outputs (all other terminals).  We split up
multi-output versions of these gates into many single-output versions,
e.g.,</p>

@({
not(o1, o2, ..., on, i);
  -->
not(o1, i);
not(o2, i);
  ...
not(on, i);
})

<p>We verified this with Cadence, in @('xf-gatesplit.v').</p>

<p><b>Signature:</b> @(call vl-gatesplit-buf/not) returns @('(mv warnings'
new-gateinsts nf')').</p>

<ul>

<li>@('x') is an instance of a @('buf') or @('not') gate.</li>

<li>@('nf') is a @(see vl-namefactory-p) for generating fresh names.</li>

</ul>

<p>The @('new-gateinsts') we return should be used to replace @('x') in the
module.</p>"

  (b* ((args  (redundant-list-fix (vl-gateinst->args x)))
       (nargs (length args))

       ((when (< nargs 2))
        ;; Basic sanity check.  Buf/not gate needs at least two terminals.
        (mv (fatal :type :vl-bad-gate
                   :msg "~a0: gate illegally has ~x1 argument(s)."
                   :args (list x nargs))
            (list x)
            nf))

       (input   (car (last args)))
       (outputs (butlast args 1))
       (in-expr (vl-plainarg->expr input))

       ((when (not (and in-expr
                        (equal (vl-expr->finalwidth in-expr) 1))))
        ;; Cadence implicitly bitwise-or's the bits of a gate input when it
        ;; is more than a single bit.  We have decided not to handle this, so
        ;; we check to ensure that the input is only one-bit here.
        (mv (fatal :type :vl-bad-gate
                   :msg "~a0: input terminal has width ~x1, but we only ~
                         support 1-bit inputs."
                   :args (list x (and in-expr (vl-expr->finalwidth in-expr))))
            (list x)
            nf))

       ((when (eql nargs 2))
        ;; Already has only two args.  No need to split it.
        (mv (ok) (list x) nf)))

    ;; Else, more than 2 args.  Split it up.
    (vl-make-gates-for-buf/not input outputs x nf warnings))
  ///
  (defmvtypes vl-gatesplit-buf/not (nil true-listp nil)))



(define vl-make-gates-for-and/etc
  :parents (vl-gatesplit-and/etc)
  :short "Produce a list of two-input @('and'), @('or'), @('xor'), or @('xnor')
gates to replace a multi-input gate."
  ((outs  vl-plainarglist-p "See below.")
   (lhses vl-plainarglist-p "See below.")
   (rhses vl-plainarglist-p "See below.")
   (type  (member-eq type '(:vl-and :vl-or :vl-xor :vl-xnor))
          "Type of gate we're splitting up.")
   (name     stringp          "Name of the original gate (or @('<unnamed gate>').")
   (loc      vl-location-p    "Location of the original gate.")
   (atts     vl-atts-p        "Attributes of the original gate, already updated
                               with the @('VL_GATESPLIT') attribute.")
   (nf       vl-namefactory-p "Name factory for generating names.")
   (warnings vl-warninglist-p "Ordinary @(see warnings) accumulator."))
  :guard (and (same-lengthp outs lhses)
              (same-lengthp outs rhses))
  :returns
  (mv (warnings      vl-warninglist-p)
      (new-gateinsts vl-gateinstlist-p :hyp :fguard)
      (nf            vl-namefactory-p  :hyp :fguard))

  :long "<p>We generate the replacement gates for a multi-input @('and'),
@('or'), @('xor'), or @('xnor') gate.  The main inputs are @(see
vl-plainarglist-p)s which have equal lengths:</p>

@({
 OUTS:  (temp1  temp2  ...     tempN-2  Out)
 LHSES: (i1     temp1  temp2   ...      tempN-2)
 RHSES: (i2     i3     ....    iN-1     iN)
})

<p>We march down the three main input-lists, zipping them together into new
gate instances.  The new gateinsts we return are intended to replace the
original gate.</p>"

  :prepwork ((local (in-theory (enable len))))

  (b* (((when (atom outs))
        (mv (ok) nil nf))

       ;; Sanity checks: is everything a single bit wide?
       (warnings
        (let ((expr (vl-plainarg->expr (car outs))))
          (if (and expr (equal (vl-expr->finalwidth expr) 1))
              (ok)
            (fatal :type :vl-bad-gate
                   :msg "~a0: output terminal expression has width ~x1, but ~
                         should have width 1.  The expression is ~a2."
                   :args (list loc
                               (and expr (vl-expr->finalwidth expr))
                               expr)))))

       (warnings
        (let ((expr (vl-plainarg->expr (car lhses))))
          (if (and expr (equal (vl-expr->finalwidth expr) 1))
              (ok)
            (fatal :type :vl-bad-gate
                   :msg "~a0: input terminal expression has width ~x1, but ~
                         should have width 1.  The expression is ~a2."
                   :args (list loc
                               (and expr (vl-expr->finalwidth expr))
                               expr)))))

       (warnings
        (let ((expr (vl-plainarg->expr (car rhses))))
          (if (and expr (equal (vl-expr->finalwidth expr) 1))
              (ok)
            (fatal :type :vl-bad-gate
                   :msg "~a0: input terminal expression has width ~x1 but ~
                         should have width 1.  The expression is ~a2."
                   :args (list loc
                               (and expr (vl-expr->finalwidth expr))
                               expr)))))

       ((mv new-name nf) (vl-namefactory-indexed-name name nf))
       (gate1 (make-vl-gateinst :name new-name
                                :type type
                                :args (list (car outs)
                                            (car lhses)
                                            (car rhses))
                                :range nil
                                :atts atts
                                :loc loc))
       ((mv warnings rest nf)
        (vl-make-gates-for-and/etc (cdr outs) (cdr lhses) (cdr rhses)
                                   type name loc atts nf warnings)))

    (mv warnings (cons gate1 rest) nf))
  ///
  (defmvtypes vl-make-gates-for-and/etc (nil true-listp nil)))


(define vl-gatesplit-and/etc
  :short "Split up a multi-input @('and'), @('or'), @('xor'), or @('xnor')
gate, if necessary."
  ((x        vl-gateinst-p     "Gate to split (if necessary).")
   (nf       vl-namefactory-p  "For generating fresh names.")
   (warnings vl-warninglist-p  "Ordinary @(see warnings) accumulator."))
  :guard (member-eq (vl-gateinst->type x) '(:vl-and :vl-or :vl-xor :vl-xnor))
  :returns
  (mv (warnings       vl-warninglist-p)
      (new-decls      vl-netdecllist-p :hyp :fguard
                      "New declarations for temporary wires.")
      (new-gateinsts  vl-gateinstlist-p :hyp :fguard
                      "Replacement gate instances.")
      (nf             vl-namefactory-p :hyp :fguard))

  :long "<p>From Section 7.2, @('and'), @('or'), @('xor'), and @('xnor') gates
have one output and many inputs.  The behavior for more than 2 inputs is
described as the \"natural extension\".  We have checked with Verilog-XL that,
at least for @('n = 4'), they behave as follows:</p>

@({
gate(out, i1, i2, ..., iN);
  -->
gate(temp1, i1,      i2);
gate(temp2, temp1,   i3);
 ...
gate(out,   tempN-2, iN);
})"

  :prepwork ((local (in-theory (enable len))))

  (b* ((type     (vl-gateinst->type x))
       (args     (redundant-list-fix (vl-gateinst->args x)))
       (nargs    (length args))
       (range    (vl-gateinst->range x))
       (loc      (vl-gateinst->loc x))
       (origname (or (vl-gateinst->name x) "unnamed"))

       ((when range)
        ;; Sanity check.  For our wire-width checks to make sense, we need to
        ;; have already gotten rid of any instance arrays.
        (mv (fatal :type :vl-bad-gate
                   :msg "~a0: expected no instance arrays; did you forget to ~
                         run the replicate transform?"
                   :args (list x))
            nil (list x) nf))

       ((when (< nargs 3))
        ;; Sanity check.  Gate needs at least 3 args.
        (mv (fatal :type :vl-bad-gate
                   :msg "~a0: expected at least 3 arguments, but found ~x1."
                   :args (list x nargs))
            nil (list x) nf))

       ((when (eql nargs 3))
        ;; If the gate has exactly 3 arguments, we don't need to split it.
        (mv (ok) nil (list x) nf))

       ;; Otherwise, we have more than 3 args.  Okay, split it up.
       ;; Note that the args are out, in1...inN, so we need N-2 temps,
       ;; and N-2 is the same as nargs-3.
       ((mv temp-exprs temp-decls nf)
        (vl-make-temporary-wires origname (- nargs 3) nf loc))

       (atts (cons (cons "VL_GATESPLIT" (make-vl-atom :guts (vl-string origname)))
                   (vl-gateinst->atts x)))

       (temp-args-out (vl-exprlist-to-plainarglist temp-exprs :dir :vl-output))
       (temp-args-in  (vl-exprlist-to-plainarglist temp-exprs :dir :vl-input))

       (o    (car args))
       (i1   (cadr args))
       (i2-n (cddr args))

       ;; OUTS are (temp1, temp2, ..., tempN-2, O)
       (outs  (append temp-args-out (list o)))
       ;; LHSES are (i1,    temp1, temp2,  ...,  tempN-2)
       (lhses (cons i1 temp-args-in))
       ;; RHSES are (i2, ..., iN)
       (rhses i2-n)

       ((mv warnings gateinsts nf)
        (vl-make-gates-for-and/etc outs lhses rhses type origname
                                   loc atts nf warnings)))
    (mv warnings temp-decls gateinsts nf))
  ///
  (defmvtypes vl-gatesplit-and/etc (nil true-listp true-listp nil)))



(define vl-gatesplit-nand/nor
  :short "Split up a multi-input @('nand') or @('nor') gate, if necessary."
  ((x        vl-gateinst-p     "NAND/NOR gate to split up (if necessary).")
   (nf       vl-namefactory-p  "For generating fresh names.")
   (warnings vl-warninglist-p  "Ordinary @(see warnings) accumulator."))
  :guard (member-eq (vl-gateinst->type x) '(:vl-nand :vl-nor))
  :returns
  (mv (warnings       vl-warninglist-p)
      (new-decls      vl-netdecllist-p :hyp :fguard
                      "New declarations for temporary wires.")
      (new-gateinsts  vl-gateinstlist-p :hyp :fguard
                      "Replacement gate instances.")
      (nf             vl-namefactory-p :hyp :fguard))
  :long "<p>From Section 7.2, @('nand') and @('nor') gates have one output and
many inputs.  The behavior for more than 2 inputs is described as the \"natural
extension\".  We have used Verilog-XL to check that they behave as follows, at
least for @('n = 4').</p>

@({
nand(o, i1, i2, ..., iN)
 -->
and(temp, i1, i2, ..., iN)
not(o, temp);
})

@({
nor(o, i1, i2, ..., iN)
 -->
or(temp, i1, i2, ..., iN)
not(o, temp);
})

<p>This is basically similar to @(see vl-gatesplit-and/etc), except that
we need to add a \"not\" gate at the end.</p>"

  :prepwork ((local (in-theory (enable len acl2::member-of-cons))))

  (b* ((args     (redundant-list-fix (vl-gateinst->args x)))
       (nargs    (length args))
       (range    (vl-gateinst->range x))
       (loc      (vl-gateinst->loc x))
       (origname (or (vl-gateinst->name x) "unnamed"))

       ((when range)
        ;; Sanity check.  For our wire-width checks to make sense, we need to
        ;; have already gotten rid of instance arrays.
        (mv (fatal :type :vl-bad-gate
                   :msg "~a0: expected all instance arrays to have been ~
                         eliminated; did you forget to run the argresolve ~
                         transform?"
                   :args (list x))
            nil (list x) nf))

       ((when (< nargs 3))
        ;; Sanity check: gate is malformed unless it has at least 3 args.
        (mv (fatal :type :vl-bad-gate
                   :msg "~a0: expected at least 3 arguments, but found ~x1."
                   :args (list x nargs))
            nil (list x) nf))

       ((when (eql nargs 3))
        ;; Already has 3 arguments, no need to split.
        (mv (ok) nil (list x) nf))

       ;; Otherwise, more than 3 args.  Split it up.  We're going to call the
       ;; same function as used in and/or to create the main signal, then
       ;; negate it.  We create one extra temporary wire, to hold the result of
       ;; this and/or computation.
       (atts (cons (cons "VL_GATESPLIT" (make-vl-atom :guts (vl-string origname)))
                   (vl-gateinst->atts x)))

       ((mv temp-exprs temp-decls nf)
        (vl-make-temporary-wires origname (- nargs 2) nf loc))

       (all-args-out (vl-exprlist-to-plainarglist temp-exprs :dir :vl-output))
       (all-args-in (vl-exprlist-to-plainarglist temp-exprs :dir :vl-input))

       ;; We call the last temporary "main", and the others are as before.
       (temp-args-out (butlast all-args-out 1))
       (temp-args-in  (butlast all-args-in 1))
       (main-arg-out  (car (last all-args-out)))
       (main-arg-in   (car (last all-args-in)))

       ;; The output and inputs for the nand/nor gate.
       (o    (car args))
       (i1   (cadr args))
       (i2-n (cddr args))

       ;; This is close to before.  But instead of outputting directly to o,
       ;; the inner and/or portion outputs to main.
       (outs  (append temp-args-out (list main-arg-out)))
       (lhses (cons i1 temp-args-in))
       (rhses i2-n)

       ;; Now, we generate the main mess of gates.
       ((mv warnings gateinsts nf)
        (vl-make-gates-for-and/etc outs lhses rhses
                                   (case (vl-gateinst->type x)
                                     (:vl-nand :vl-and)
                                     (:vl-nor  :vl-or))
                                   origname loc atts nf warnings))

       ;; Finally, we just need to hook up the "main" wire to
       ;; our output, o.
       ((mv final-name nf) (vl-namefactory-indexed-name origname nf))
       (final-gate (make-vl-gateinst :type :vl-not
                                     :name final-name
                                     :range nil
                                     :atts atts
                                     :args (list o main-arg-in)
                                     :loc loc)))
    (mv (ok)
        temp-decls
        (append gateinsts (list final-gate))
        nf))
  ///
  (defmvtypes vl-gatesplit-nand/nor (nil true-listp true-listp nil)))


(define vl-gateinst-gatesplit
  :short "Main routine for splitting high-arity gate instances."
  ((x        vl-gateinst-p    "Gate instance to perhaps split up.")
   (nf       vl-namefactory-p "Name factory for generating fresh names.")
   (warnings vl-warninglist-p "Ordinary @(see warnings) accumulator."))
  :returns
  (mv (warnings       vl-warninglist-p)
      (new-decls      vl-netdecllist-p :hyp :fguard
                      "New declarations for temporary wires.")
      (new-gateinsts  vl-gateinstlist-p :hyp :fguard
                      "Replacement gate instances.")
      (nf             vl-namefactory-p :hyp :fguard))
  (case (vl-gateinst->type x)
    ((:VL-NOT :VL-BUF)
     ;; Blah, these don't generate new decls so the signature is incompatible
     (b* (((mv warnings new-gateinsts nf)
           (vl-gatesplit-buf/not x nf warnings)))
       (mv warnings nil new-gateinsts nf)))
    ((:VL-AND :VL-OR :VL-XOR :VL-XNOR)
     (vl-gatesplit-and/etc x nf warnings))
    ((:VL-NAND :VL-NOR)
     (vl-gatesplit-nand/nor x nf warnings))
    (otherwise
     (mv (ok) nil (list x) nf)))
  ///
  (defmvtypes vl-gateinst-gatesplit (nil true-listp true-listp nil)))


(define vl-gateinstlist-gatesplit
  ((x vl-gateinstlist-p)
   (nf vl-namefactory-p)
   (warnings vl-warninglist-p))
  :returns
  (mv (warnings       vl-warninglist-p)
      (new-decls      vl-netdecllist-p :hyp :fguard
                      "New declarations for temporary wires.")
      (new-gateinsts  vl-gateinstlist-p :hyp :fguard
                      "Replacement gate instances.")
      (nf             vl-namefactory-p :hyp :fguard))
  (b* (((when (atom x))
        (mv (ok) nil nil nf))
       ((mv warnings decls1 gates1 nf)
        (vl-gateinst-gatesplit (car x) nf warnings))
       ((mv warnings declsN gatesN nf)
        (vl-gateinstlist-gatesplit (cdr x) nf warnings)))
    (mv warnings
        (append decls1 declsN)
        (append gates1 gatesN)
        nf))
  ///
  (defmvtypes vl-gateinstlist-gatesplit (nil true-listp true-listp nil)))

(define vl-module-gatesplit ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard)
  (b* (((when (vl-module->hands-offp x))
        x)
       (gateinsts (vl-module->gateinsts x))
       (warnings  (vl-module->warnings x))
       (netdecls  (vl-module->netdecls x))
       (nf        (vl-starting-namefactory x))
       ((mv warnings new-decls gates nf)
        (vl-gateinstlist-gatesplit gateinsts nf warnings))
       (-         (vl-free-namefactory nf)))
    (change-vl-module x
                      :netdecls (append new-decls netdecls)
                      :gateinsts gates
                      :warnings warnings)))

(defprojection vl-modulelist-gatesplit (x)
  (vl-module-gatesplit x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p)

(define vl-design-gatesplit
  :short "Top-level @(see gatesplit) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-gatesplit x.mods))))
