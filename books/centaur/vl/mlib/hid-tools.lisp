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
(include-book "expr-tools")
(local (include-book "../util/arithmetic"))



;; BOZO consider automatically generating rules like these in defaggregate
;; when illegible mode is used.  Is it too expensive?  Do they drive proofs
;; in a bad direction?

(local (defthm equal-of-vl-hidpiece-rewrite
         (implies (vl-hidpiece-p x)
                  (equal (equal x (make-vl-hidpiece :name name))
                         (equal (vl-hidpiece->name x) name)))
         :rule-classes ((:rewrite :backchain-limit-lst 1))
         :hints(("Goal" :in-theory (enable vl-hidpiece
                                           vl-hidpiece-p
                                           vl-hidpiece->name)))))

(local (defthm equal-of-vl-atom-rewrite
         (implies (vl-atom-p x)
                  (equal (equal x (make-vl-atom :guts guts
                                                :finalwidth finalwidth
                                                :finaltype finaltype))
                         (and (equal (vl-atom->guts x) guts)
                              (equal (vl-atom->finalwidth x) finalwidth)
                              (equal (vl-atom->finaltype x) finaltype))))
         :rule-classes ((:rewrite :backchain-limit-lst 1))
         :hints(("Goal" :in-theory (enable vl-atom
                                           vl-atom-p
                                           vl-atom->guts
                                           vl-atom->finalwidth
                                           vl-atom->finaltype)))))

(local (defthm equal-of-vl-nonatom-rewrite
         (implies (vl-nonatom-p x)
                  (equal (equal x (make-vl-nonatom :op op
                                                   :atts atts
                                                   :args args
                                                   :finalwidth finalwidth
                                                   :finaltype finaltype))
                         (and (equal (vl-nonatom->op x) op)
                              (equal (vl-nonatom->atts x) atts)
                              (equal (vl-nonatom->args x) args)
                              (equal (vl-nonatom->finalwidth x) finalwidth)
                              (equal (vl-nonatom->finaltype x) finaltype))))
         :rule-classes ((:rewrite :backchain-limit-lst 1))
         :hints(("Goal" :in-theory (enable vl-nonatom
                                           vl-nonatom-p
                                           vl-nonatom->op
                                           vl-nonatom->atts
                                           vl-nonatom->args
                                           vl-nonatom->finalwidth
                                           vl-nonatom->finaltype)))))

(local (defthm equal-of-cons-rewrite
         (equal (equal x (cons a b))
                (and (consp x)
                     (equal (car x) a)
                     (equal (cdr x) b)))))




(defxdoc hid-tools
  :parents (mlib)
  :short "Functions for working with hierarchical identifiers.")


(defsection vl-hidexpr-p
  :parents (hid-tools)
  :short "@(call vl-hidexpr-p) recognizes well-formed hierarchical identifier
expressions."

  :long "<p>We represent hierarchical identifiers like @('foo.bar[3].baz') as
ordinary @(see vl-expr-p) objects.  But @('vl-expr-p') is really too weak, and
it permits nonsensical expressions like @('foo.5.bar.(1+2)').  The function
@('vl-hidexpr-p') provides a stronger check to ensure that an expression is a
well-formed hierarchical identifier.</p>

<p>In particular, @('vl-hidexpr-p') requires three things:</p>

<p>1. Except for indicies like @('3') in @('foo.bar[3].baz'), all atoms
throughout the expression must be @(see vl-hidpiece-p) atoms.  This prohibits
ill-formed expressions like @('foo.5.bar').</p>

<p>2. Except for indicies, the only operators that are permitted are
@(':vl-hid-dot') and @(':vl-hid-arraydot'), which represent expressions like
@('foo.bar') and @('foo[3].bar'), respectively.</p>

<p>3. We require that the HID is always \"right-associated.\"  A picture helps
to make this more clear:</p>

@({
             .          |           .
            / \\         |          / \\
         foo   .        |         .   baz
              / \\       |        / \\
           bar   baz    |     foo   bar
                        |
          Good          |         Bad
})

<p>More formally, we require that the first argument to each @(':vl-hid-dot')
and @(':vl-hid-arraydot') operation is a single @(see vl-hidpiece-p) atom, and
not some more complex expression.  This essentially allows us to traverse any
well-formed HID in a purely linear fashion.</p>

<p>Note that @('vl-hidexpr-p') does <b>not</b> restrict in any way the
expressions may occur in the index positions.  For instance, there is a valid
@('vl-hidexpr-p') that represents @('foo.bar[3+a*b].baz').</p>

<p>Note also that @('vl-hidexpr-p') does not have any length requirement, and
regards even lone @('vl-hidpiece-p') atoms as valid.</p>"

  (defund vl-hidexpr-p (x)
    (declare (xargs :guard (vl-expr-p x)))
    (if (vl-fast-atom-p x)
        (vl-fast-hidpiece-p (vl-atom->guts x))
      (let ((op   (vl-nonatom->op x))
            (args (vl-nonatom->args x)))
        (case op
          (:vl-hid-dot
           ;; foo.bar
           (and (vl-fast-atom-p (first args))
                (vl-fast-hidpiece-p (vl-atom->guts (first args)))
                (vl-hidexpr-p (second args))))
          (:vl-hid-arraydot
           ;; foo[x].bar
           (and (vl-fast-atom-p (first args))
                (vl-fast-hidpiece-p (vl-atom->guts (first args)))
                (vl-hidexpr-p (third args))))
          (otherwise nil)))))

  (local (in-theory (enable vl-hidexpr-p)))

  (defthm vl-hidexpr-p-of-vl-atom->guts-when-vl-hidexpr-p
    (implies (and (vl-hidexpr-p x)
                  (force (vl-atom-p x)))
             (vl-hidpiece-p (vl-atom->guts x))))

  (defthm vl-hidexpr-p-of-first-of-vl-nonatom->args-when-vl-hidexpr-p
    (implies (and (vl-hidexpr-p x)
                  (force (not (vl-atom-p x)))
                  (force (vl-expr-p x)))
             (vl-hidexpr-p (first (vl-nonatom->args x)))))

  (defthm vl-atom-p-of-first-of-vl-nonatom->args-when-vl-hidexpr-p
    (implies (and (vl-hidexpr-p x)
                  (force (not (vl-atom-p x))))
             (vl-atom-p (first (vl-nonatom->args x)))))

  (defthm vl-hidpiece-p-of-vl-atom->guts-of-first-of-vl-nonatom->args-when-vl-hidexpr-p
    (implies (and (vl-hidexpr-p x)
                  (force (not (vl-atom-p x))))
             (vl-hidpiece-p (vl-atom->guts (first (vl-nonatom->args x))))))

; We canonicalize to whether the operator is hid-dot.

  (defthm vl-hidexpr-p-of-second-of-vl-nonatom->args-when-vl-hidexpr-p
    (implies (and (equal (vl-nonatom->op x) :vl-hid-dot)
                  (vl-hidexpr-p x)
                  (force (not (vl-atom-p x))))
             (vl-hidexpr-p (second (vl-nonatom->args x)))))

  (defthm vl-hidexpr-p-of-third-of-vl-nonatom->args-when-vl-hidexpr-p
    (implies (and (not (equal (vl-nonatom->op x) :vl-hid-dot))
                  (vl-hidexpr-p x)
                  (force (not (vl-atom-p x))))
             (vl-hidexpr-p (third (vl-nonatom->args x)))))

  (defthm not-vl-hidexpr-p-by-op
    (implies (and (not (eq (vl-nonatom->op x) :vl-hid-dot))
                  (not (eq (vl-nonatom->op x) :vl-hid-arraydot))
                  (force (not (vl-atom-p x))))
             (not (vl-hidexpr-p x))))

  (defthm vl-op-arity-when-vl-hidexpr-p
    (implies (and (vl-hidexpr-p x)
                  (force (not (vl-atom-p x))))
             (equal (vl-op-arity (vl-nonatom->op x))
                    (if (eq (vl-nonatom->op x) :vl-hid-dot)
                        2
                      3))))

  (defthm vl-nonatom->op-when-vl-hidexpr-p-forward
    (implies (and (vl-hidexpr-p x)
                  (not (vl-atom-p x))
                  (force (vl-expr-p x)))
             (or (equal (vl-nonatom->op x) :vl-hid-arraydot)
                 (equal (vl-nonatom->op x) :vl-hid-dot)))
    :rule-classes :forward-chaining)

  (defthm vl-hidexpr-p-of-vl-atom
    (implies (and (force (vl-atomguts-p guts))
                  (force (vl-maybe-posp finalwidth))
                  (force (vl-maybe-exprtype-p finaltype)))
             (equal (vl-hidexpr-p (make-vl-atom :guts guts
                                                :finalwidth finalwidth
                                                :finaltype finaltype))
                    (vl-hidpiece-p guts)))
    :hints(("goal" :in-theory (enable vl-hidexpr-p))))

  (defthm vl-hidexpr-p-of-vl-nonatom
    (implies (and (equal op :vl-hid-dot)
                  (force (vl-exprlist-p args))
                  (force (equal (len args) 2))
                  (force (vl-atom-p (first args)))
                  (force (vl-hidpiece-p (vl-atom->guts (first args))))
                  (force (vl-hidexpr-p (second args)))
                  (force (vl-atts-p atts))
                  (force (vl-maybe-posp finalwidth))
                  (force (vl-maybe-exprtype-p finaltype)))
             (vl-hidexpr-p (make-vl-nonatom :op op
                                            :args args
                                            :atts atts
                                            :finalwidth finalwidth
                                            :finaltype finaltype))))

  (defthm vl-hidexpr-p-of-vl-nonatom-arraydot
    (implies (and (equal op :vl-hid-arraydot)
                  (force (vl-exprlist-p args))
                  (force (equal (len args) 3))
                  (force (vl-atom-p (first args)))
                  (force (vl-hidpiece-p (vl-atom->guts (first args))))
                  (force (vl-hidexpr-p (third args)))
                  (force (vl-atts-p atts))
                  (force (vl-maybe-posp finalwidth))
                  (force (vl-maybe-exprtype-p finaltype)))
             (vl-hidexpr-p (make-vl-nonatom :op op
                                            :args args
                                            :atts atts
                                            :finalwidth finalwidth
                                            :finaltype finaltype))))

  )



(defsection vl-hid-indicies-resolved-p
  :parents (hid-tools)
  :short "@(call vl-hid-indicies-resolved-p) determines if every indexed
portion of a hierarchical identifier is a resolved expression."

  (defund vl-hid-indicies-resolved-p (x)
    (declare (xargs :guard (and (vl-expr-p x)
                                (vl-hidexpr-p x))))
    (if (vl-fast-atom-p x)
        t
      (let ((op   (vl-nonatom->op x))
            (args (vl-nonatom->args x)))
        (case op
          (:vl-hid-dot ;; foo.bar
           (vl-hid-indicies-resolved-p (second args)))
          (:vl-hid-arraydot ;; foo[3].bar
           (and (vl-expr-resolved-p (second args))
                (natp (vl-resolved->val (second args)))
                (vl-hid-indicies-resolved-p (third args))))))))

  (local (in-theory (enable vl-hid-indicies-resolved-p)))

  (defthm vl-hid-indicies-resolved-p-when-atom
    (implies (vl-atom-p x)
             (vl-hid-indicies-resolved-p x)))

  (defthm vl-hid-indicies-resolved-p-of-vl-nonatom-dot
    (implies (and (equal op :vl-hid-dot)
                  (force (vl-exprlist-p args))
                  (force (equal (len args) 2))
                  (force (vl-atom-p (first args)))
                  (force (vl-hidpiece-p (vl-atom->guts (first args))))
                  (force (vl-hidexpr-p (second args)))
                  (force (vl-hid-indicies-resolved-p (second args)))
                  (force (vl-atts-p atts))
                  (force (vl-maybe-posp finalwidth))
                  (force (vl-maybe-exprtype-p finaltype)))
             (vl-hid-indicies-resolved-p (make-vl-nonatom :op op
                                                          :args args
                                                          :atts atts
                                                          :finalwidth finalwidth
                                                          :finaltype finaltype))))

  (defthm vl-hid-indicies-resolved-p-of-vl-nonatom-arraydot
    (implies (and (equal op :vl-hid-arraydot)
                  (force (vl-exprlist-p args))
                  (force (equal (len args) 3))
                  (force (vl-atom-p (first args)))
                  (force (vl-hidpiece-p (vl-atom->guts (first args))))
                  (force (vl-expr-resolved-p (second args)))
                  (force (natp (vl-resolved->val (second args))))
                  (force (vl-hidexpr-p (third args)))
                  (force (vl-hid-indicies-resolved-p (third args)))
                  (force (vl-atts-p atts))
                  (force (vl-maybe-posp finalwidth))
                  (force (vl-maybe-exprtype-p finaltype)))
             (vl-hid-indicies-resolved-p (make-vl-nonatom :op op
                                                          :args args
                                                          :atts atts
                                                          :finalwidth finalwidth
                                                          :finaltype finaltype))))

  (defthm vl-expr-resolved-p-when-vl-hid-indicies-resolved-p
    (implies (and (vl-hid-indicies-resolved-p x)
                  (equal (vl-nonatom->op x) :vl-hid-arraydot)
                  (force (not (vl-atom-p x))))
             (vl-expr-resolved-p (second (vl-nonatom->args x)))))

  (defthm vl-hid-indicies-resolved-p-of-dot-2
    (implies (and (vl-hid-indicies-resolved-p x)
                  (equal (vl-nonatom->op x) :vl-hid-dot)
                  (force (not (vl-atom-p x))))
             (vl-hid-indicies-resolved-p (second (vl-nonatom->args x)))))

  (defthm vl-hid-indicies-resolved-p-of-arraydot-3
    (implies (and (vl-hid-indicies-resolved-p x)
                  (equal (vl-nonatom->op x) :vl-hid-arraydot)
                  (force (not (vl-atom-p x))))
             (vl-hid-indicies-resolved-p (third (vl-nonatom->args x))))))




(defsection vl-hid-fix
  :parents (hid-tools)
  :short "@(call vl-hid-fix) throws away attributes, widths, and signs from a
hierarchical identifier and normalizes all of its indicies into a common
format."

  (defund vl-hid-fix (x)
    (declare (xargs :guard (and (vl-expr-p x)
                                (vl-hidexpr-p x)
                                (vl-hid-indicies-resolved-p x))))
    (b* (((when (mbe :logic (or (not (vl-expr-p x))
                                (not (vl-hidexpr-p x))
                                (not (vl-hid-indicies-resolved-p x)))
                     :exec nil))
          ;; Funky case to fix any malformed arguments to nil
          nil)
         ((when (vl-fast-atom-p x))
          (let ((name (vl-hidpiece->name (vl-atom->guts x))))
            (make-vl-atom :guts (make-vl-hidpiece :name name))))
         (op   (vl-nonatom->op x))
         (args (vl-nonatom->args x)))
        (case op
          (:vl-hid-dot
           (b* ((name1 (vl-hidpiece->name (vl-atom->guts (first args))))
                (part1 (make-vl-atom :guts (make-vl-hidpiece :name name1)))
                (rest  (vl-hid-fix (second args))))
               (make-vl-nonatom :op :vl-hid-dot
                                :args (list part1 rest))))
          (:vl-hid-arraydot
           (b* ((name1 (vl-hidpiece->name (vl-atom->guts (first args))))
                (part1 (make-vl-atom :guts (make-vl-hidpiece :name name1)))
                (idx   (vl-make-index (vl-resolved->val (second args))))
                (rest  (vl-hid-fix (third args))))
               (make-vl-nonatom :op :vl-hid-arraydot
                                :args (list part1 idx rest)))))))

  (local (in-theory (enable vl-hid-fix)))

  (defthm vl-hid-fix-type
    (implies (and (force (vl-expr-p x))
                  (force (vl-hidexpr-p x))
                  (force (vl-hid-indicies-resolved-p x)))
             (and (vl-expr-p (vl-hid-fix x))
                  (vl-hidexpr-p (vl-hid-fix x))
                  (vl-hid-indicies-resolved-p (vl-hid-fix x)))))

  (local (defthm lemma
           (implies (< i 0)
                    (equal (vl-make-index i)
                           (vl-make-index 0)))
           :hints(("Goal" :in-theory (enable vl-make-index)))))

  (defthm vl-hid-fix-idempotent
    (equal (vl-hid-fix (vl-hid-fix x))
           (vl-hid-fix x))))



(defsection vl-hid-fixed-p
  :parents (hid-tools)
  :short "@(call vl-hid-fixed-p) determines if @('x') is canonical in the sense
of @(see vl-hid-fix)."

  (defund vl-hid-fixed-p (x)
    (declare (xargs :guard (and (vl-expr-p x)
                                (vl-hidexpr-p x)
                                (vl-hid-indicies-resolved-p x))))
    (equal x (vl-hid-fix x)))

  (local (in-theory (enable vl-hid-fixed-p)))

  (defthm vl-hid-fixed-p-of-vl-hid-fix
    (vl-hid-fixed-p (vl-hid-fix x)))

  (defthm vl-hid-fix-when-vl-hid-fixed-p
    (implies (vl-hid-fixed-p x)
             (equal (vl-hid-fix x)
                    x)))

  (local (in-theory (enable vl-hid-fix)))

  (defthm vl-hid-fixed-p-when-vl-atom-p
    (implies (and (vl-hidexpr-p x)
                  (vl-atom-p x))
             (equal (vl-hid-fixed-p x)
                    (and (not (vl-atom->finalwidth x))
                         (not (vl-atom->finaltype x))))))

  (defthm vl-hid-fixed-p-of-second-of-vl-nonatom->args-when-vl-hidexpr-p
    (implies (and (equal (vl-nonatom->op x) :vl-hid-dot)
                  (vl-hid-fixed-p x)
                  (force (not (vl-atom-p x))))
             (vl-hid-fixed-p (second (vl-nonatom->args x)))))

  (defthm vl-hid-fixed-p-of-third-of-vl-nonatom->args-when-vl-hidexpr-p
    (implies (and (equal (vl-nonatom->op x) :vl-hid-arraydot)
                  (vl-hid-fixed-p x)
                  (force (not (vl-atom-p x))))
             (vl-hid-fixed-p (third (vl-nonatom->args x)))))

  (defthm vl-hid-fixed-p-of-vl-atom
    (implies (and (force (vl-atomguts-p guts))
                  (force (vl-maybe-posp finalwidth))
                  (force (vl-maybe-exprtype-p finaltype)))
             (equal (vl-hid-fixed-p (make-vl-atom :guts guts
                                                  :finalwidth finalwidth
                                                  :finaltype finaltype))
                    (and (vl-hidpiece-p guts)
                         (not finalwidth)
                         (not finaltype)))))

  (defthm vl-hid-fixed-p-of-vl-nonatom-dot
    (implies (and (equal op :vl-hid-dot)
                  (force (vl-exprlist-p args))
                  (force (equal (len args) 2))
                  (force (true-listp args))
                  (force (not atts))
                  (force (not finalwidth))
                  (force (not finaltype))

                  (force (vl-atom-p (first args)))
                  (force (vl-hidpiece-p (vl-atom->guts (first args))))
                  (force (not (vl-atom->finalwidth (first args))))
                  (force (not (vl-atom->finaltype (first args))))

                  (force (vl-hidexpr-p (second args)))
                  (force (vl-hid-indicies-resolved-p (second args)))
                  (force (vl-hid-fixed-p (second args))))
             (vl-hid-fixed-p (make-vl-nonatom :op op
                                              :args args
                                              :atts atts
                                              :finalwidth finalwidth
                                              :finaltype finaltype))))

  (defthm vl-hid-fixed-p-of-vl-nonatom-arraydot
    (implies (and (equal op :vl-hid-arraydot)
                  (force (vl-exprlist-p args))
                  (force (equal (len args) 3))
                  (force (true-listp args))
                  (force (not atts))
                  (force (not finalwidth))
                  (force (not finaltype))

                  (force (vl-atom-p (first args)))
                  (force (vl-hidpiece-p (vl-atom->guts (first args))))
                  (force (not (vl-atom->finalwidth (first args))))
                  (force (not (vl-atom->finaltype (first args))))

                  (force (vl-expr-resolved-p (second args)))
                  (force (equal (second args)
                                (vl-make-index (vl-resolved->val (second args)))))

                  (force (vl-hidexpr-p (third args)))
                  (force (vl-hid-indicies-resolved-p (third args)))
                  (force (vl-hid-fixed-p (third args))))

             (vl-hidexpr-p (make-vl-nonatom :op op
                                            :args args
                                            :atts atts
                                            :finalwidth finalwidth
                                            :finaltype finaltype)))))



(defsection vl-hid-final-name
  :parents (hid-tools)
  :short "@(call vl-hid-final-name) returns the final name component of the
hierarchical identifier @('x') as a string.  For example, given
@('top.foo.bar.w'), it returns the string @('\"w\"')."

  :long "<p>This function can be used on any @(see vl-hidexpr-p).</p>"

  (defund vl-hid-final-name (x)
    (declare (xargs :guard (and (vl-expr-p x)
                                (vl-hidexpr-p x))))
    (if (vl-fast-atom-p x)
        ;; Nonsense for unconditional stringp type-prescription
        (mbe :logic (string-fix (vl-hidpiece->name (vl-atom->guts x)))
             :exec (vl-hidpiece->name (vl-atom->guts x)))
      (let ((op   (vl-nonatom->op x))
            (args (vl-nonatom->args x)))
        (case op
          (:vl-hid-dot ;; foo.bar
           (vl-hid-final-name (second args)))
          (:vl-hid-arraydot ;; foo[3].bar
           (vl-hid-final-name (third args)))
          (otherwise
           ;; Nonsense for unconditional stringp type-prescription
           (progn$ (er hard 'vl-hid-final-name "Impossible")
                   ""))))))

  (local (in-theory (enable vl-hid-final-name)))

  (defthm stringp-of-vl-hid-final-name
    (stringp (vl-hid-final-name x))
    :rule-classes :type-prescription))



(defsection vl-flatten-hidexpr
  :parents (hid-tools)
  :short "@(call vl-flatten-hidexpr) converts a hierarchical identifier
expression into a string like @('foo.bar[3].baz')."

  :long "<p>Note that @('x') must satisfy @(see vl-hidexpr-p) and @(see
vl-hid-indicies-resolved-p).</p>"

  (defund vl-flatten-hidexpr (x)
    (declare (xargs :guard (and (vl-expr-p x)
                                (vl-hidexpr-p x)
                                (vl-hid-indicies-resolved-p x))))
    (if (vl-fast-atom-p x)
        ;; Nonsense for unconditional stringp type-prescription
        (mbe :logic (string-fix (vl-hidpiece->name (vl-atom->guts x)))
             :exec (vl-hidpiece->name (vl-atom->guts x)))
      (let ((op   (vl-nonatom->op x))
            (args (vl-nonatom->args x)))
        (case op
          (:vl-hid-dot
           (cat (vl-hidpiece->name (vl-atom->guts (first args)))
                "."
                (vl-flatten-hidexpr (second args))))

          (:vl-hid-arraydot
           ;; BOZO eventually switch to natstr, but for now we don't know it's a
           ;; natural number.
           (cat (vl-hidpiece->name (vl-atom->guts (first args)))
                "["
                (coerce (explode-atom (vl-resolved->val (second args)) 10) 'string)
                "]"
                (vl-flatten-hidexpr (third args))))

          (otherwise
           ;; Nonsense for unconditional stringp type-prescription
           (progn$ (er hard 'vl-flatten-hidexpr "Impossible")
                   ""))))))


  (local (in-theory (enable vl-flatten-hidexpr)))

  (defthm stringp-of-vl-flatten-hidexpr
    (stringp (vl-flatten-hidexpr x))
    :rule-classes :type-prescription))





(defsection vl-expr-tophids
  :parents (hid-tools)
  :short "Collect top-level hierarchical identifiers from an expression (or
expression list)."

  :long "<p><b>Signatures:</b></p>
<ul>
 <li>@(call vl-expr-tophids) returns an expression list.</li>
 <li>@(call vl-exprlist-tophids) returns an expression list.</li>
</ul>

<p>These functions are essentially similar to @(see vl-expr-names), but instead
of returning the names of simple identifiers, we return sub-expressions.</p>

<p>We only return the \"top\" HID expressions we find.  All this means is that
if your expression contains an HID like @('foo.bar.baz'), then the result from
@('tophids') will only include @('foo.bar.baz'), and won't contain @('bar.baz')
or @('baz').</p>

<p>The resulting list is guaranteed to be a list of expressions, but there's no
guarantee that these expressions will satisfy @(see vl-hidexpr-p).</p>

<p>We use a tail-recursive implementation for efficiency, and also optimize
with @('nreverse') under the hood.</p>"

  (local (in-theory (disable (force))))

  (mutual-recursion

   (defund vl-expr-tophids-exec (x acc)
     (declare (xargs :guard (vl-expr-p x)
                     :measure (two-nats-measure (acl2-count x) 1)))
     (if (vl-fast-atom-p x)
         (if (vl-fast-hidpiece-p (vl-atom->guts x))
             (cons x acc)
           acc)
       (case (vl-nonatom->op x)
         ((:vl-hid-dot :vl-hid-arraydot)
          (cons x acc))
         (otherwise
          (vl-exprlist-tophids-exec (vl-nonatom->args x) acc)))))

   (defund vl-exprlist-tophids-exec (x acc)
     (declare (xargs :guard (vl-exprlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (consp x)
         (vl-exprlist-tophids-exec (cdr x)
                                   (vl-expr-tophids-exec (car x) acc))
       acc)))

  (mutual-recursion

   (defund vl-expr-tophids (x)
     (declare (xargs :guard (vl-expr-p x)
                     :measure (two-nats-measure (acl2-count x) 1)
                     :verify-guards nil))
     (mbe :logic (if (vl-atom-p x)
                     (if (vl-hidpiece-p (vl-atom->guts x))
                         (list x)
                       nil)
                   (case (vl-nonatom->op x)
                     ((:vl-hid-dot :vl-hid-arraydot)
                      (list x))
                     (otherwise
                      (vl-exprlist-tophids (vl-nonatom->args x)))))
          :exec (reverse (vl-expr-tophids-exec x nil))))

   (defund vl-exprlist-tophids (x)
     (declare (xargs :guard (vl-exprlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (mbe :logic (if (consp x)
                     (append (vl-expr-tophids (car x))
                             (vl-exprlist-tophids (cdr x)))
                   nil)
          :exec (reverse (vl-exprlist-tophids-exec x nil)))))

  (defthm true-listp-of-vl-expr-tophids
    (true-listp (vl-expr-tophids x))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-exprlist-tophids
    (true-listp (vl-exprlist-tophids x))
    :rule-classes :type-prescription)

  (local (in-theory (enable (force))))

  (FLAG::make-flag vl-fast-flag-expr-tophids
                   vl-expr-tophids-exec
                   :flag-mapping ((vl-expr-tophids-exec . expr)
                                  (vl-exprlist-tophids-exec . list)))

  (defthm-vl-fast-flag-expr-tophids lemma
    (expr (equal (vl-expr-tophids-exec x acc)
                 (revappend (vl-expr-tophids x) acc))
          :name vl-expr-tophids-exec-removal)
    (list (equal (vl-exprlist-tophids-exec x acc)
                 (revappend (vl-exprlist-tophids x) acc))
          :name vl-exprlist-tophids-exec-removal)
    :hints(("Goal"
            :induct (vl-fast-flag-expr-tophids flag x acc)
            :expand ((vl-expr-tophids-exec x acc)
                     (vl-exprlist-tophids-exec x acc)
                     (vl-expr-tophids x)
                     (vl-exprlist-tophids x)))))

  (verify-guards vl-expr-tophids
    :hints(("Goal" :in-theory (enable vl-expr-tophids
                                      vl-expr-tophids-exec
                                      vl-exprlist-tophids
                                      vl-exprlist-tophids-exec))))

  (defttag vl-optimize)
  (progn!
   (set-raw-mode t)
   (setf (gethash 'vl-expr-tophids-exec ACL2::*never-profile-ht*) t)
   (setf (gethash 'vl-exprlist-tophids-exec ACL2::*never-profile-ht*) t)
   (defun vl-expr-tophids (x)
     (nreverse (vl-expr-tophids-exec x nil)))
   (defun vl-exprlist-tophids (x)
     (nreverse (vl-exprlist-tophids-exec x nil))))
  (defttag nil)

  (local (defthm lemma
           (case flag
             (expr (implies (vl-expr-p x)
                            (vl-exprlist-p (vl-expr-tophids x))))
             (atts t)
             (t (implies (vl-exprlist-p x)
                         (vl-exprlist-p (vl-exprlist-tophids x)))))
           :rule-classes nil
           :hints(("Goal"
                   :induct (vl-expr-induct flag x)
                   :expand ((vl-expr-tophids x)
                            (vl-exprlist-tophids x))))))

  (defthm vl-exprlist-p-of-vl-expr-tophids
    (implies (force (vl-expr-p x))
             (vl-exprlist-p (vl-expr-tophids x)))
    :hints(("Goal" :use ((:instance lemma (flag 'expr))))))

  (defthm vl-exprlist-p-of-vl-exprlist-tophids
    (implies (force (vl-exprlist-p x))
             (vl-exprlist-p (vl-exprlist-tophids x)))
    :hints(("Goal" :use ((:instance lemma (flag 'list)))))))




(defsection vl-explode-hid
  :parents (hid-tools)
  :short "Break a hierarchical identifier into a list of strings and numbers."

  :long "<p>@(call vl-explode-hid) is given @('hid'), a @(see vl-hidexpr-p),
and returns a list of strings and numbes corresponding to the components of
@('hid').  For example, the explosion of @('foo.bar.baz') is @('(\"foo\"
\"bar\" \"baz\")').</p>

<p>The elements of the exploded list are typically strings, but may also be
natural numbers.  For instance, the explosion of @('foo.bar[3].baz') is
@('(\"foo\" \"bar\" 3 \"baz\")').</p>"

  (local (in-theory (enable vl-hidexpr-p)))

  (defund vl-explode-hid (hid)
    (declare (xargs :guard (and (vl-expr-p hid)
                                (vl-hidexpr-p hid)
                                (vl-hid-indicies-resolved-p hid))))
    (b* (((when (vl-fast-atom-p hid))
          (list (vl-hidpiece->name (vl-atom->guts hid))))
         (op    (vl-nonatom->op hid))
         (args  (vl-nonatom->args hid))
         (name1 (vl-hidpiece->name (vl-atom->guts (first args)))))
      (case op
        (:vl-hid-dot
         (cons name1
               (vl-explode-hid (second args))))
        (:vl-hid-arraydot
         (list* name1
                (vl-resolved->val (second args))
                (vl-explode-hid (third args)))))))

  (local (in-theory (enable vl-explode-hid)))

  (defthm true-listp-of-vl-explode-hid
    (true-listp (vl-explode-hid hid))
    :rule-classes :type-prescription))



(defsection vl-hid-prefixp
  :parents (hid-tools)
  :short "Recognizes hierarchical identifiers that begin with a certain
prefix."

  :long "<p>@(call vl-hid-prefixp) is a more efficient version of @('(prefixp
pieces (@(see vl-explode-hid) hid))') which avoids the construction of the
intermediate list.</p>"

  (local (in-theory (enable vl-hidexpr-p vl-explode-hid)))

  (defun vl-hid-prefixp (pieces hid)
    (declare (xargs :guard (and (vl-expr-p hid)
                                (vl-hidexpr-p hid)
                                (vl-hid-indicies-resolved-p hid))))
    (mbe :logic
         (prefixp pieces (vl-explode-hid hid))
         :exec
         (b* (((when (atom pieces))
               t)
              ((when (vl-fast-atom-p hid))
               (and (equal (first pieces) (vl-hidpiece->name (vl-atom->guts hid)))
                    (atom (cdr pieces))))
              (op   (vl-nonatom->op hid))
              (args (vl-nonatom->args hid))
              (name1 (vl-hidpiece->name (vl-atom->guts (first args)))))
             (and (equal (first pieces) name1)
                  (case op
                    (:vl-hid-dot
                     (vl-hid-prefixp (cdr pieces) (second args)))
                    (:vl-hid-arraydot
                     (or (atom (cdr pieces))
                         (and (equal (second pieces) (vl-resolved->val (second args)))
                              (vl-hid-prefixp (cddr pieces) (third args)))))))))))

