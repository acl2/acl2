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
(include-book "../mlib/welltyped")
(include-book "../mlib/delta")
(local (include-book "../util/arithmetic"))
(local (in-theory (enable tag-reasoning)))
(local (std::add-default-post-define-hook :fix))

(defxdoc trunc
  :parents (transforms)
  :short "Eliminate implicit truncations in assignments"

  :long "<p>This transformation must occur after expression splitting has
already been applied.  Recall that the @(see split) transformation brings
all assignments into one of the following forms:</p>

<ol>
 <li>@('lvalue = atom')</li>
 <li>@('lvalue = (op atom1 atom2 ... atomN)')</li>
</ol>

<p>Unfortunately, Verilog allows for implicit truncations during assignments,
so that the lvalue's width might be less than the operation's width.  (The
other case is that the widths agree, since the lvalue plays a role in the
ctxsize computation, and so if the lvalue's width is larger than the
expression's, the expression will be expanded to match.</p>

<p>And so we now introduce a rewrite which corrects for this, and results in
assignments where the expressions always agree on the desired sizes.  The basic
transformation is as follows.  We are looking at the assignment @('lvalue =
expr').  If @('lvalue') is shorter than @('expr'), we replace this assignment
with something like:</p>

@({
  wire [expr.width-1:0] trunc_12345;
  assign trunc_12345 = expr;
  assign lvalue = trunc_12345[lvalue.width-1:0];
})

<p>where @('trunc_12345') is a fresh variable name.  All of the resulting
assignments are between lvalues and expressions that agree.</p>")

(local (xdoc::set-default-parents trunc))

(define vl-make-chopped-id
  :short "Generate the expression to truncate a wire."
  ((name "name of an unsigned wire to be truncated" stringp)
   (name-width "width of @('name')" posp)
   (trunc-width "width to truncate to" posp))
  :guard (< trunc-width name-width)
  :returns (expr "expression like @('name[truncwidth-1:0]')" vl-expr-p)
  :long "<p>We require that @('trunc-width') is strictly less than @('width').
We return the expression to truncate @('name') down to this new
@('trunc-width'), with all of the intermediate widths set up correctly.</p>"

  (b* ((trunc-width (lposfix trunc-width))
       (name-width  (lposfix name-width))
       (name-expr   (vl-idexpr name name-width :vl-unsigned))
       (left        (vl-make-index (- trunc-width 1)))
       (zero        (vl-make-index 0))
       ;; The goal is to make the expression name[left:zero].

       ((when (eql trunc-width 1))
        ;; We can use a bitselect instead of name[0:0].  By our guard, 1 <
        ;; name-width, so there is no chance to further simplify this to
        ;; simply "name".
        (make-vl-nonatom :op         :vl-bitselect
                         :args       (list name-expr zero)
                         :finalwidth 1
                         :finaltype  :vl-unsigned)))

    ;; Otherwise, our goal is name[left:zero], and we cannot simplify this
    ;; any further.  Introduce a real part select.
    (make-vl-nonatom :op         :vl-partselect-colon
                     :args       (list name-expr left zero)
                     :finalwidth trunc-width
                     :finaltype  :vl-unsigned)))


(define vl-truncate-constint
  :short "Special routine for truncating ordinary, unsigned constant integers,
without introducing temporary wires."
  ((n "width to truncate down to" posp)
   (x "resolved, unsigned, constant integer expression to truncate" vl-expr-p))
  :guard (and (vl-atom-p x)
              (vl-expr-welltyped-p x)
              (vl-constint-p (vl-atom->guts x))
              (equal (vl-expr->finaltype x) :vl-unsigned)
              (< n (vl-expr->finalwidth x)))
  :returns (chopped-expr vl-expr-p)
  :long "<p>We can truncate resolved constants by just creating a new constant
that has its width and value chopped down to size.</p>"

  (b* ((n        (lposfix n))
       (guts     (vl-atom->guts x))
       (value    (vl-constint->value guts))
       (val-chop (mod value (expt 2 n)))
       (new-guts (make-vl-constint :value val-chop
                                   :origwidth n
                                   :origtype :vl-unsigned))
       (new-atom (make-vl-atom :guts new-guts
                               :finalwidth n
                               :finaltype :vl-unsigned)))
    new-atom)

  :prepwork
  ((local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
   (local (in-theory (enable vl-atom-welltyped-p
                             vl-expr-welltyped-p
                             vl-expr->finalwidth
                             vl-expr->finaltype))))
  ///
  (defthm vl-truncate-constint-basics
    (implies (and (force (posp n))
                  (force (vl-atom-p x))
                  (force (vl-expr-welltyped-p x))
                  (force (vl-constint-p (vl-atom->guts x)))
                  (force (< n (vl-expr->finalwidth x)))
                  (force (equal (vl-expr->finaltype x) :vl-unsigned)))
             (and (equal (vl-expr->finalwidth (vl-truncate-constint n x)) n)
                  (equal (vl-expr->finaltype (vl-truncate-constint n x)) :vl-unsigned)
                  (vl-expr-welltyped-p (vl-truncate-constint n x))))))


(define vl-truncate-weirdint
  :short "Special routine for truncating unsigned weirdint literals without
introducing temporary wires."
  ((n "width to truncate down to" posp)
   (x "unsigned @(see vl-weirdint-p) to truncate" vl-expr-p))
  :guard (and (vl-atom-p x)
              (vl-expr-welltyped-p x)
              (vl-weirdint-p (vl-atom->guts x))
              (equal (vl-expr->finaltype x) :vl-unsigned)
              (< n (vl-expr->finalwidth x)))
  :returns (chopped-expr vl-expr-p)
  :long "<p>We can truncate a weirdint by just creating a new weirdint that has
its width reduced and that drops the chopped off bits.</p>"
  (b* ((n                  (lposfix n))
       (guts               (vl-atom->guts x))
       ((vl-weirdint guts) guts)
       (bits-chop (nthcdr (- guts.origwidth n)
                          (list-fix guts.bits)))
       (new-guts (make-vl-weirdint :bits bits-chop
                                   :origwidth n
                                   :origtype :vl-unsigned))
       (new-atom (make-vl-atom :guts new-guts
                               :finalwidth n
                               :finaltype :vl-unsigned)))
    new-atom)

  :prepwork
  ((local (in-theory (enable vl-atom-welltyped-p vl-expr-welltyped-p vl-expr->finalwidth vl-expr->finaltype))))
  ///
  (defthm vl-truncate-weirdint-basics
    (implies (and (force (posp n))
                  (force (vl-atom-p x))
                  (force (vl-expr-welltyped-p x))
                  (force (vl-weirdint-p (vl-atom->guts x)))
                  (force (< n (vl-expr->finalwidth x)))
                  (force (equal (vl-expr->finaltype x) :vl-unsigned)))
             (and (equal (vl-expr->finalwidth (vl-truncate-weirdint n x)) n)
                  (equal (vl-expr->finaltype (vl-truncate-weirdint n x)) :vl-unsigned)
                  (vl-expr-welltyped-p (vl-truncate-weirdint n x))))))


(define vl-assign-trunc
  :short "Make any implicit truncation in an assignment explicit."
  ((x vl-assign-p)
   (delta vl-delta-p))
  :returns (mv (assign vl-assign-p)
               (delta  vl-delta-p))
  (b* ((x     (vl-assign-fix x))
       (delta (vl-delta-fix delta))
       ((vl-assign x) x)

       (lhsw (vl-expr->finalwidth x.lvalue))
       (rhsw (vl-expr->finalwidth x.expr))

       ((when (or (not (posp lhsw))
                  (not (posp rhsw))
                  (< rhsw lhsw)))
        (mv x (dwarn :type :vl-programming-error
                     :msg "~a0: expected widths to be computed and never ~
                             thought lhs would never be wider than rhs. LHS ~
                             width: ~x1.  RHS width: ~x2.  LHS: ~a3.  RHS: ~
                             ~a4."
                     :args (list x lhsw rhsw x.lvalue x.expr)
                     :fatalp t)))

       ((when (eql lhsw rhsw))
        ;; The widths already agree, so nothing needs to change.
        (mv x delta))

       ;; If we get this far, we need to truncate.

       ;; We used to issue warnings here, but we moved that to the sizing
       ;; code because we can generate better messages there.

       ((when (and (vl-fast-atom-p x.expr)
                   (vl-fast-constint-p (vl-atom->guts x.expr))
                   (eq (vl-expr->finaltype x.expr) :vl-unsigned)
                   (vl-expr-welltyped-p x.expr)))
        ;; Optimized case for truncating constant integers
        (b* ((new-rhs (vl-truncate-constint lhsw x.expr))
             (x-prime (change-vl-assign x :expr new-rhs)))
          (mv x-prime delta)))

       ((when (and (vl-fast-atom-p x.expr)
                   (vl-fast-weirdint-p (vl-atom->guts x.expr))
                   (eq (vl-expr->finaltype x.expr) :vl-unsigned)
                   (vl-expr-welltyped-p x.expr)))
        ;; Optimized case for truncating weird integers
        (b* ((new-rhs (vl-truncate-weirdint lhsw x.expr))
             (x-prime (change-vl-assign x :expr new-rhs)))
          (mv x-prime delta)))

       ;; BOZO probably should extend this to allow for truncating any
       ;; sliceable expression without adding wires...

       ;; Ordinary case...
       ((vl-delta delta) delta)

       ((mv tmp-name nf) (vl-namefactory-indexed-name "trunc" delta.nf))
       (tmp-expr         (vl-idexpr tmp-name rhsw :vl-unsigned))

       ;; wire [rhsw-1:0] trunc_12345;
       (type       (change-vl-coretype *vl-plain-old-wire-type*
                                       :pdims (list (vl-make-n-bit-range rhsw))))
       (tmp-decl   (make-vl-vardecl :loc   x.loc
                                    :name  tmp-name
                                    :nettype :vl-wire
                                    :type  type))

       ;; assign trunc_12345 = rhs;
       (tmp-assign (make-vl-assign :loc    x.loc
                                   :lvalue tmp-expr
                                   :expr   x.expr))

       (delta      (change-vl-delta delta
                                    :vardecls (cons tmp-decl delta.vardecls)
                                    :assigns  (cons tmp-assign delta.assigns)
                                    :nf       nf))

       ;; trunc_12345[lhsw-1:0];
       (chop-expr  (vl-make-chopped-id tmp-name rhsw lhsw))

       ;; assign lhs = trunc_12345[lhsw-1:0];
       (x-prime
        ;; Using change-vl-assign (vs. make-vl-assign) keeps delay/strength
        (change-vl-assign x
                          :expr chop-expr
                          ;; Add an attribute like (* TRUNC_15 *) when we're
                          ;; truncating to 15 bits.  BOZO should be VL_.
                          :atts (acons (cat "TRUNC_" (natstr lhsw)) nil x.atts))))
    (mv x-prime delta)))

(define vl-assignlist-trunc ((x vl-assignlist-p)
                             (delta vl-delta-p))
  :returns (mv (assigns vl-assignlist-p)
               (detla   vl-delta-p))
  (b* (((when (atom x))
        (mv nil (vl-delta-fix delta)))
       ((mv car delta) (vl-assign-trunc (car x) delta))
       ((mv cdr delta) (vl-assignlist-trunc (cdr x) delta)))
    (mv (cons car cdr) delta)))

(define vl-assign-can-skip-trunc-p ((x vl-assign-p))
  :inline t
  (b* ((lhsw (vl-expr->finalwidth (vl-assign->lvalue x)))
       (rhsw (vl-expr->finalwidth (vl-assign->expr x))))
    (and lhsw
         (eql lhsw rhsw))))

(define vl-assignlist-can-skip-trunc-p ((x vl-assignlist-p))
  (or (atom x)
      (and (vl-assign-can-skip-trunc-p (car x))
           (vl-assignlist-can-skip-trunc-p (cdr x)))))

(define vl-module-trunc ((x vl-module-p))
  :returns (new-x vl-module-p)
  :short "Eliminate implicit truncations in assignments throughout a module."

  (b* ((x (vl-module-fix x))
       ((vl-module x) x)

       ((when (vl-module->hands-offp x))
        ;; Fine, don't do anything.
        x)

       ((when (vl-assignlist-can-skip-trunc-p x.assigns))
        ;; Optimization.  Don't recons anything if there aren't any implicit
        ;; truncations to make.
        x)

       (delta              (vl-starting-delta x))
       (delta              (change-vl-delta delta :vardecls x.vardecls))
       ((mv assigns delta) (vl-assignlist-trunc x.assigns delta))
       ((vl-delta delta)   (vl-free-delta delta)))

    (change-vl-module x
                      ;; We started out with x.vardecls and extended them, so
                      ;; this has everything we want
                      :vardecls delta.vardecls
                      ;; We rewrote all of x's assigns, but there are also
                      ;; assigns in the delta, so merge them.
                      :assigns (revappend-without-guard delta.assigns assigns)
                      ;; The starting delta include's the former warnings for X,
                      ;; so the delta's warnings are fine.
                      :warnings delta.warnings))
  ///
  (defthm vl-module->name-of-vl-module-trunc
    (equal (vl-module->name (vl-module-trunc x))
           (vl-module->name x))))


(defprojection vl-modulelist-trunc ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-trunc x))

(define vl-design-trunc
  :short "Top-level @(see trunc) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-trunc x.mods))))
