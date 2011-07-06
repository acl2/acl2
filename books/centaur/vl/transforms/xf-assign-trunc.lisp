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
(include-book "../wf-ranges-resolved-p")
(include-book "../wf-widthsfixed-p")
(include-book "../mlib/namefactory")
(include-book "../mlib/welltyped")
(local (include-book "../util/arithmetic"))


(defxdoc trunc
  :parents (transforms)
  :short "Eliminate implicit truncations in assignments"

  :long "<p>This transformation must occur after expression splitting has
already been applied.  Recall that the @(see split) transformation brings
all assignments into one of the following forms:</p>

<ol>
 <li><tt>lvalue = atom</tt></li>
 <li><tt>lvalue = (op atom1 atom2 ... atomN)</tt></li>
</ol>

<p>Unfortunately, Verilog allows for implicit truncations during assignments,
so that the lvalue's width might be less than the operation's width.  (The
other case is that the widths agree, since the lvalue plays a role in the
ctxsize computation, and so if the lvalue's width is larger than the
expression's, the expression will be expanded to match.</p>

<p>And so we now introduce a rewrite which corrects for this, and results in
assignments where the expressions always agree on the desired sizes.  The basic
transformation is as follows.  We are looking at the assignment <tt>lvalue =
expr</tt>.  If <tt>lvalue</tt> is shorter than <tt>expr</tt>, we replace this
assignment with something like:</p>

<code>
  wire [expr.width-1:0] trunc_12345;
  assign trunc_12345 = expr;
  assign lvalue = trunc_12345[lvalue.width-1:0];
</code>

<p>where <tt>trunc_12345</tt> is a fresh variable name.  All of the resulting
assignments are between lvalues and expressions that agree.</p>")


(defsection vl-make-chopped-id
  :parents (trunc)
  :short "Generate the expression to truncate a wire."

  :long "<p><b>Signature:</b> @(call vl-make-chopped-id) returns a @(see
vl-expr-p).</p>

<p>Given <tt>name</tt>, the name of some unsigned wire, <tt>width</tt>, the
width of the wire, and <tt>trunc</tt>, some number which is strictly less than
<tt>width</tt>, we construct the expression <tt>name[trunc-1:0]</tt>, with all
of the intermediate widths set up correctly.</p>"

  (defund vl-make-chopped-id (name name-width trunc-width)
    (declare (xargs :guard (and (stringp name)
                                (posp name-width)
                                (posp trunc-width)
                                (< trunc-width name-width))))
    (b* ((name-expr (vl-idexpr name name-width :vl-unsigned))
         (left      (vl-make-index (- trunc-width 1)))
         (zero      (vl-make-index 0))
         ;; The goal is to make the expression name[left:zero].
         ((when (equal trunc-width 1))
          ;; In this case, left is 0 so we have name[0:0].  This is the same as
          ;; name[0].  By our guard, 1 < name-width, so there is no chance to
          ;; further simplify this to simply "name".  Hence, build a bitselect
          ;; of name[0].
          (make-vl-nonatom :op :vl-bitselect
                           :args (list name-expr zero)
                           :finalwidth 1
                           :finaltype :vl-unsigned)))

        ;; Otherwise, our goal is name[left:zero], and we cannot simplify this
        ;; any further.  Introduce a real part select.
        (make-vl-nonatom :op :vl-partselect-colon
                         :args (list name-expr left zero)
                         :finalwidth trunc-width
                         :finaltype :vl-unsigned)))

  (local (in-theory (enable vl-make-chopped-id)))

  (defthm vl-expr-p-of-vl-make-chopped-id
    (implies (and (force (stringp name))
                  (force (posp name-width))
                  (force (posp trunc-width))
                  (force (< trunc-width name-width)))
             (vl-expr-p (vl-make-chopped-id name name-width trunc-width)))))




(defsection vl-truncate-constint

  ;; Special support for truncating ordinary, unsigned constant integers, without
  ;; introducing temporary wires.

  (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
  (local (in-theory (enable vl-atom-welltyped-p vl-expr-welltyped-p
                            vl-expr->finalwidth vl-expr->finaltype)))

  (defund vl-truncate-constint (n x)
    (declare (xargs :guard (and (posp n)
                                (vl-atom-p x)
                                (vl-expr-welltyped-p x)
                                (vl-constint-p (vl-atom->guts x))
                                (< n (vl-expr->finalwidth x))
                                (equal (vl-expr->finaltype x) :vl-unsigned))))
    (b* ((guts     (vl-atom->guts x))
         (value    (vl-constint->value guts))
         (val-chop (mod value (expt 2 n)))
         (new-guts (make-vl-constint :value val-chop
                                     :origwidth n
                                     :origtype :vl-unsigned))
         (new-atom (make-vl-atom :guts new-guts
                                 :finalwidth n
                                 :finaltype :vl-unsigned)))
      new-atom))

  (local (in-theory (enable vl-truncate-constint)))

  (defthm vl-truncate-constint-basics
    (implies (and (force (posp n))
                  (force (vl-atom-p x))
                  (force (vl-expr-welltyped-p x))
                  (force (vl-constint-p (vl-atom->guts x)))
                  (force (< n (vl-expr->finalwidth x)))
                  (force (equal (vl-expr->finaltype x) :vl-unsigned)))
             (and (vl-expr-p (vl-truncate-constint n x))
                  (equal (vl-expr->finalwidth (vl-truncate-constint n x)) n)
                  (equal (vl-expr->finaltype (vl-truncate-constint n x)) :vl-unsigned)
                  (vl-expr-welltyped-p (vl-truncate-constint n x))))))


(defsection vl-truncate-weirdint

  ;; Special support for truncating ordinary, unsigned weird integers, without
  ;; introducing temporary wires.

  (local (in-theory (enable vl-atom-welltyped-p vl-expr-welltyped-p
                            vl-expr->finalwidth vl-expr->finaltype)))

  (defund vl-truncate-weirdint (n x)
    (declare (xargs :guard (and (posp n)
                                (vl-atom-p x)
                                (vl-expr-welltyped-p x)
                                (vl-weirdint-p (vl-atom->guts x))
                                (< n (vl-expr->finalwidth x))
                                (equal (vl-expr->finaltype x) :vl-unsigned))))
    (b* ((guts      (vl-atom->guts x))
         ((vl-weirdint guts) guts)
         (bits-chop (nthcdr (- guts.origwidth n)
                            (redundant-list-fix guts.bits)))
         (new-guts (make-vl-weirdint :bits bits-chop
                                     :origwidth n
                                     :origtype :vl-unsigned))
         (new-atom (make-vl-atom :guts new-guts
                                 :finalwidth n
                                 :finaltype :vl-unsigned)))
      new-atom))

  (local (in-theory (enable vl-truncate-weirdint)))

  (defthm vl-truncate-weirdint-basics
    (implies (and (force (posp n))
                  (force (vl-atom-p x))
                  (force (vl-expr-welltyped-p x))
                  (force (vl-weirdint-p (vl-atom->guts x)))
                  (force (< n (vl-expr->finalwidth x)))
                  (force (equal (vl-expr->finaltype x) :vl-unsigned)))
             (and (vl-expr-p (vl-truncate-weirdint n x))
                  (equal (vl-expr->finalwidth (vl-truncate-weirdint n x)) n)
                  (equal (vl-expr->finaltype (vl-truncate-weirdint n x)) :vl-unsigned)
                  (vl-expr-welltyped-p (vl-truncate-weirdint n x))))))





(defsection vl-assign-trunc
  :parents (trunc)
  :short "Make any implicit truncation in an assignment explicit."
  :long "<p><b>Signature:</b> @(call vl-assign-trunc) returns <tt>(mv
warnings-prime netdecls assigns nf-prime)</tt>.</p>

<p>Inputs.</p>

<ul>

<li><tt>x</tt> is the assignment statement which may need to be truncated,
</li>

<li><tt>nf</tt> is a @(see vl-namefactory-p) for generating fresh variable
names, and</li>

<li><tt>warnings</tt> is an accumulator for warnings.</li>

</ul>

<p>Outputs.</p>

<ul>

<li><tt>warnings-prime</tt> is the updated list of warnings,</li>

<li><tt>netdecls</tt> are any new wire declarations that must be added
to the module,</li>

<li><tt>new-assigns</tt> is a new list of assignments which will <b>replace</b>
<tt>x</tt> in the module, and</li>

<li><tt>nf-prime</tt> is the updated name factory.</li>

</ul>"

  (defund vl-assign-trunc (x nf warnings)
    "Returns (MV WARNINGS NETDECLS ASSIGNS NF-PRIME)"
    (declare (xargs :guard (and (vl-assign-p x)
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))
    (b* ((lvalue   (vl-assign->lvalue x))
         (expr     (vl-assign->expr x))
         (loc      (vl-assign->loc x))
         (lw       (vl-expr->finalwidth lvalue))
         (ew       (vl-expr->finalwidth expr))

         ((when (or (not (posp lw))
                    (not (posp ew))
                    (< ew lw)))
          (mv (cons (make-vl-warning
                     :type :vl-programming-error
                     :msg "~a0: expected widths to be computed and never ~
                           thought lvalue would be larger than the expr being ~
                           assigned to it.  Lvalue width: ~x1.  Expr width: ~
                           ~x2.  Lvalue: ~a3.  Expr: ~a4."
                     :args (list x lw ew lvalue expr)
                     :fatalp t
                     :fn 'vl-assign-trunc)
                    warnings)
              nil (list x) nf))

         ((when (= lw ew))
          ;; The widths already agree, so nothing needs to change.
          (mv warnings nil (list x) nf))

         ;; Otherwise, we need to truncate.  We used to issue warnings
         ;; here, but we moved that to the sizing code because we can
         ;; generate better messages there.

         ((when (and (vl-fast-atom-p expr)
                     (vl-fast-constint-p (vl-atom->guts expr))
                     (eq (vl-expr->finaltype expr) :vl-unsigned)
                     (vl-expr-welltyped-p expr)))
          ;; Optimized case for truncating constant integers
          (b* ((new-atom   (vl-truncate-constint lw expr))
               (new-assign (change-vl-assign x :expr new-atom)))
            (mv warnings nil (list new-assign) nf)))

         ((when (and (vl-fast-atom-p expr)
                     (vl-fast-weirdint-p (vl-atom->guts expr))
                     (eq (vl-expr->finaltype expr) :vl-unsigned)
                     (vl-expr-welltyped-p expr)))
          ;; Optimized case for truncating weird integers
          (b* ((new-atom   (vl-truncate-weirdint lw expr))
               (new-assign (change-vl-assign x :expr new-atom)))
            (mv warnings nil (list new-assign) nf)))

         ;; BOZO probably should extend this to allow for truncating any
         ;; sliceable expression without adding wires...

         ;; Ordinary case...
         ((mv new-name nf) (vl-namefactory-indexed-name "trunc" nf))
         (new-name-expr    (vl-idexpr new-name ew :vl-unsigned))

         ;; Make a fake wire, e.g., wire [expr.width-1:0] trunc_12345;
         (new-netdecl (make-vl-netdecl :loc loc
                                       :name new-name
                                       :type :vl-wire
                                       :range (vl-make-n-bit-range ew)))

         ;; Assign the expression to the fake wire, e.g., trunc_12345 = expr;
         ;; We always use 0-delay here.
         (new-assign1 (make-vl-assign :loc loc
                                      :lvalue new-name-expr
                                      :expr expr))

         ;; Make the expression for the chop, i.e., trunc_12345[lvalue.width-1:0];
         (chop-expr   (vl-make-chopped-id new-name ew lw))

         ;; Assign the chopped expression to the lvalue, i.e.,
         ;;   assign lvalue = trunc_12345[lvalue.width-1:0];
         ;; We annotate this assignment with an attribute like (* TRUNC_15 *) when
         ;; we're truncating to 15 bits.
         ;; We now preserve the delay/strength of the assignment
         (new-assign2 (change-vl-assign x
                                        :expr chop-expr
                                        :atts (acons (str::cat "TRUNC_" (str::natstr lw))
                                                     nil nil))))
        (mv warnings
            (list new-netdecl)
            (list new-assign1 new-assign2)
            nf)))

  (defmvtypes vl-assign-trunc (nil true-listp true-listp))

  (local (in-theory (enable vl-assign-trunc)))

  (defthm vl-assign-trunc-basics
    (implies (and (force (vl-assign-p x))
                  (force (vl-namefactory-p nf))
                  (force (vl-warninglist-p warnings)))
             (let ((ret (vl-assign-trunc x nf warnings)))
               (and (vl-warninglist-p (mv-nth 0 ret))
                    (vl-netdecllist-p (mv-nth 1 ret))
                    (vl-assignlist-p  (mv-nth 2 ret))
                    (vl-namefactory-p (mv-nth 3 ret)))))))



(defsection vl-assignlist-trunc
  :parents (trunc)
  :short "Extends @(see vl-assign-trunc) across a list of assignments."

  (defund vl-assignlist-trunc (x nf warnings)
    "Returns (MV WARNINGS-PRIME NETDECLS ASSIGNS NF-PRIME)"
    (declare (xargs :guard (and (vl-assignlist-p x)
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom x))
          (mv warnings nil nil nf))
         ((mv warnings new-netdecls1 new-assigns1 nf)
          (vl-assign-trunc (car x) nf warnings))
         ((mv warnings new-netdecls2 new-assigns2 nf)
          (vl-assignlist-trunc (cdr x) nf warnings))
         (netdecls (append new-netdecls1 new-netdecls2))
         (assigns  (append new-assigns1 new-assigns2)))
        (mv warnings netdecls assigns nf)))

  (defmvtypes vl-assignlist-trunc (nil true-listp true-listp))

  (local (in-theory (enable vl-assignlist-trunc)))

  (defthm vl-assignlist-trunc-basics
    (implies (and (force (vl-assignlist-p x))
                  (force (vl-namefactory-p nf))
                  (force (vl-warninglist-p warnings)))
             (let ((ret (vl-assignlist-trunc x nf warnings)))
               (and (vl-warninglist-p (mv-nth 0 ret))
                    (vl-netdecllist-p (mv-nth 1 ret))
                    (vl-assignlist-p  (mv-nth 2 ret))
                    (vl-namefactory-p (mv-nth 3 ret)))))))


(defund vl-assign-can-skip-trunc-p (x)
  (declare (xargs :guard (vl-assign-p x)))
  (let ((lw (vl-expr->finalwidth (vl-assign->lvalue x)))
        (ew (vl-expr->finalwidth (vl-assign->expr x))))
    (and (posp lw)
         (posp ew)
         (= lw ew))))

(defund vl-assignlist-can-skip-trunc-p (x)
  (declare (xargs :guard (vl-assignlist-p x)))
  (or (atom x)
      (and (vl-assign-can-skip-trunc-p (car x))
           (vl-assignlist-can-skip-trunc-p (cdr x)))))


(defsection vl-module-trunc
  :parents (trunc)
  :short "Eliminate implicit truncations in assignments throughout a module."

  (defund vl-module-trunc (x)
    "Return X-PRIME"
    (declare (xargs :guard (vl-module-p x)))
    (b* (((when (vl-module->hands-offp x))
          x)
         (assigns    (vl-module->assigns x))
         ((when (vl-assignlist-can-skip-trunc-p assigns))
          ;; Optimization.  Don't recons anything if there aren't any implicit
          ;; truncations to make.
          x)
         (warnings   (vl-module->warnings x))
         (netdecls   (vl-module->netdecls x))
         (nf         (vl-starting-namefactory x))
         ((mv warnings new-netdecls new-assigns nf)
          (vl-assignlist-trunc assigns nf warnings))
         (-          (vl-free-namefactory nf)))
        (change-vl-module x
                          :assigns new-assigns
                          :netdecls (append (redundant-list-fix netdecls) new-netdecls)
                          :warnings warnings)))

  (local (in-theory (enable vl-module-trunc)))

  (defthm vl-module-p-of-vl-module-trunc
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-trunc x))))

  (defthm vl-module->name-of-vl-module-trunc
    (equal (vl-module->name (vl-module-trunc x))
           (vl-module->name x))))



(defsection vl-modulelist-trunc
  :parents (trunc)
  :short "Eliminate implicit truncations in assignments throughout a module list."

  (defprojection vl-modulelist-trunc (x)
    (vl-module-trunc x)
    :guard (vl-modulelist-p x)
    :result-type vl-modulelist-p)

  (local (in-theory (enable vl-modulelist-trunc)))

  (defthm vl-modulelist->names-of-vl-modulelist-trunc
    (equal (vl-modulelist->names (vl-modulelist-trunc x))
           (vl-modulelist->names x))))
