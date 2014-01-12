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
(include-book "../mlib/ctxexprs")
(include-book "../mlib/writer")
(include-book "../mlib/fix")
(local (include-book "../util/arithmetic"))


(defxdoc leftright-check
  :parents (checkers)
  :short "Check for strange expressions like @('A [op] A')."

  :long "<p>This is a heuristic for generating warnings, inspired by PVS
Studio.  It has found a few pretty minor things that we were able to clean up,
and also found one interesting copy/paste bug.</p>

<p>We look for identical sub-expressions on the left and right of most binary
operations, for instance @('A | A') and @('A == A').  It is usually pretty
strange to write such an expression, and sometimes these indicate copy/paste
errors.  We do similar checking for the then- and else-branches of @('?:')
operators.</p>

<p>We also look for part-selects that use the same expressions for both
indices, e.g., @('foo[3:3]'), but these are somewhat more common and minor, and
sometimes result from macros or parameterized modules, so we generally think
these are pretty minor and uninteresting.</p>")

(defenum vl-op-ac-p
  (:vl-binary-plus
   :vl-binary-times
   :vl-binary-eq
   :vl-binary-neq
   :vl-binary-ceq
   :vl-binary-cne
   :vl-binary-logand
   :vl-binary-logor
   :vl-binary-bitand
   :vl-binary-bitor
   :vl-binary-xor
   :vl-binary-xnor)
  :parents (leftright-check)
  :short "Recognizes the associative/commutative binary @(see vl-op-p)s.")

(defthm vl-op-p-when-vl-op-ac-p
  (implies (vl-op-ac-p x)
           (vl-op-p x))
  :hints(("Goal" :in-theory (enable vl-op-ac-p))))

(defthm vl-op-arity-when-vl-op-ac-p
  (implies (vl-op-ac-p x)
           (equal (vl-op-arity x) 2))
  :hints(("Goal" :in-theory (enable vl-op-ac-p))))



(defsection vl-collect-ac-args
  :parents (leftright-check)
  :short "Collect the nested arguments to an associative/commutative operator."

  :long "<p><b>Signature:</b> @(call vl-collect-ac-args) returns an @(see
vl-exprlist-p).</p>

<p>@('op') should be one of Verilog's associative and commutative binary
operators; see @(see vl-op-ac-p).</p>

<p>@('x') is an expression; typically it is itself an argument to an
@('op').</p>

<p>If @('x') is itself an @('op') expression, we recursively collect up the
ac-args of its sub-expressions.  Otherwise we just collect @('x').  For
instance, if @('op') is @('|') and @('x') is:</p>

@({
 (a | (b + c)) | (d & e)
})

<p>Then we return a list with three expressions: @('a'), @('b + c'), and @('d &
e').</p>"

  (defund vl-collect-ac-args (op x)
    (declare (xargs :guard (and (vl-op-ac-p op)
                                (vl-expr-p x))))
    (b* (((when (vl-fast-atom-p x))
          (list x))

         ((unless (eq (vl-nonatom->op x) op))
          (list x))

         ((when (mbe :logic (atom x)
                     :exec nil))
          (er hard 'vl-collect-ac-args "Impossble."))

         (args (vl-nonatom->args x)))
      (append (vl-collect-ac-args op (first args))
              (vl-collect-ac-args op (second args)))))

  (defthm vl-exprlist-p-of-vl-collect-ac-args
    (implies (and (vl-op-ac-p op)
                  (vl-expr-p x))
             (vl-exprlist-p (vl-collect-ac-args op x)))
    :hints(("Goal" :in-theory (enable vl-collect-ac-args)))))




(defsection vl-expr-leftright-check
  :parents (leftright-check)
  :short "Search for strange expressions like @('A [op] A')."
  :long "<p><b>Signature:</b> @(call vl-expr-leftright-check) returns a
@(see vl-warninglist-p).</p>

<p>We search through the expression @('x') for sub-expressions of the form @('A
[op] A'), and generate a warning whenever we find one.  The @('ctx') is a @(see
vl-context-p) that says where @('x') occurs, for more helpful warnings.  We
also use it to suppress warnings in certain cases.</p>"

  (mutual-recursion

   (defund vl-expr-leftright-check (x ctx)
     (declare (xargs :guard (and (vl-expr-p x)
                                 (vl-context-p ctx))
                     :measure (two-nats-measure (acl2-count x) 1)
                     :hints(("Goal" :in-theory (disable (force))))))
     (b* (((when (vl-fast-atom-p x))
           nil)
          (op   (vl-nonatom->op x))
          (args (vl-nonatom->args x))

          ((when (and (eq op :vl-binary-minus)
                      (member (tag (vl-context->elem ctx))
                              '(:vl-netdecl :vl-regdecl :vl-vardecl))
                      (equal (vl-expr-fix (first args))
                             (vl-expr-fix (second args)))
                      (vl-expr-resolved-p (first args))))
           ;; Special hack: Don't warn about things like 5 - 5 in the context
           ;; of net/reg/var declarations.  This can happen for things like:
           ;;   wire bar[`FOO_MSB-`FOO_LSB:0] = baz[`FOO_MSB:`FOO_LSB]
           ;; and leads to a lot of spurious warnings.
           nil)

          ((when (vl-op-ac-p op))
           ;; For associative commutative ops, collect up all the args and
           ;; see if there are any duplicates.
           (b* ((subexprs     (append (vl-collect-ac-args op (first args))
                                      (vl-collect-ac-args op (second args))))
                (subexprs-fix (vl-exprlist-fix subexprs))
                (dupes        (duplicated-members subexprs-fix))
                ((when dupes)
                 (cons (make-vl-warning
                        :type :vl-warn-leftright
                        :msg "~a0: found an ~s1 expression with duplicated ~
                              arguments, which is ~s2: ~s3"
                        :args (list ctx
                                    (vl-op-string op)
                                    (if (eq op :vl-binary-plus)
                                        "somewhat odd (why not use wiring to double it?)"
                                      "odd")
                                    (with-local-ps (vl-pp-exprlist dupes)))
                        :fatalp nil
                        :fn 'vl-expr-leftright-check)
                       ;; This can result in a pile of redundant warnings, but
                       ;; whatever.  A better alternative would be to recur on
                       ;; subexprs, but then we'd have to argue about the
                       ;; acl2-count of collect-ac-args.... ugh.
                       (vl-exprlist-leftright-check args ctx))))
             ;; Else, no dupes; fine, keep going.
             (vl-exprlist-leftright-check args ctx)))

          ((when (and (member op (list :vl-binary-minus :vl-binary-div :vl-binary-rem
                                       :vl-binary-lt :vl-binary-lte
                                       :vl-binary-gt :vl-binary-gte

                                       ;; There's no reason that these are
                                       ;; necessarily wrong, but it still seems
                                       ;; kind of weird so I include them
                                       :vl-binary-shr :vl-binary-shl
                                       :vl-binary-ashr :vl-binary-ashl))
                      (equal (vl-expr-fix (first args))
                             (vl-expr-fix (second args)))))
           (cons (make-vl-warning
                  :type :vl-warn-leftright
                  :msg "~a0: found an expression of the form FOO ~s1 FOO, which is ~s2: ~a3."
                  :args (list ctx (vl-op-string op)
                              (if (eq op :vl-binary-plus)
                                  "somewhat odd (why not use wiring to double it?)"
                                "odd")
                              x)
                  :fatalp nil
                  :fn 'vl-expr-leftright-check)
                 (vl-exprlist-leftright-check args ctx)))

          ((when (and (member op '(:vl-partselect-colon))
                      (equal (vl-expr-fix (second args))
                             (vl-expr-fix (third args)))))
           (cons (make-vl-warning
                  :type :vl-warn-partselect-same
                  :msg "~a0: slightly odd to have a part-select with the same indices: ~a1."
                  :args (list ctx x)
                  :fatalp nil
                  :fn 'vl-expr-leftright-check)
                 ;; Note: we might want to not recur here, for similar reasons to the
                 ;; special hack above for minuses in net/reg/var decls.
                 (vl-exprlist-leftright-check args ctx)))

          ((when (and (member op '(:vl-qmark))
                      (equal (vl-expr-fix (second args))
                             (vl-expr-fix (third args)))))
           (cons (make-vl-warning
                  :type :vl-warn-leftright
                  :msg "~a0: found an expression of the form FOO ? BAR : BAR, which is odd: ~a1."
                  :args (list ctx x)
                  :fatalp nil
                  :fn 'vl-expr-leftright-check)
                 (vl-exprlist-leftright-check args ctx))))

       (vl-exprlist-leftright-check args ctx)))

   (defund vl-exprlist-leftright-check (x ctx)
     (declare (xargs :guard (and (vl-exprlist-p x)
                                 (vl-context-p ctx))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         nil
       (append (vl-expr-leftright-check (car x) ctx)
               (vl-exprlist-leftright-check (cdr x) ctx)))))

  (flag::make-flag vl-flag-expr-leftright-check
                   vl-expr-leftright-check
                   :flag-mapping ((vl-expr-leftright-check . expr)
                                  (vl-exprlist-leftright-check . list)))

  (defthm-vl-flag-expr-leftright-check
    (defthm vl-warninglist-p-of-vl-expr-leftright-check
      (vl-warninglist-p (vl-expr-leftright-check x ctx))
      :flag expr)
    (defthm vl-warninglist-p-of-vl-exprlist-leftright-check
      (vl-warninglist-p (vl-exprlist-leftright-check x ctx))
      :flag list)
    :hints(("Goal" :expand ((vl-expr-leftright-check x ctx)
                            (vl-exprlist-leftright-check x ctx))))))


(defsection vl-exprctxalist-leftright-check
  :parents (leftright-check)
  :short "@(call vl-exprctxalist-leftright-check) extends @(see
vl-expr-leftright-check) across an @(see vl-exprctxalist-p)."

  (defund vl-exprctxalist-leftright-check (x)
    (declare (xargs :guard (vl-exprctxalist-p x)))
    (if (atom x)
        nil
      (append (vl-expr-leftright-check (caar x) (cdar x))
              (vl-exprctxalist-leftright-check (cdr x)))))

  (defthm vl-warninglist-p-of-vl-exprctxalist-leftright-check
    (vl-warninglist-p (vl-exprctxalist-leftright-check x))
    :hints(("Goal" :in-theory (enable vl-exprctxalist-leftright-check)))))



(defsection vl-module-leftright-check
  :parents (leftright-check)
  :short "@(call vl-module-leftright-check) carries our our @(see
leftright-check) on all the expressions in a module, and adds any resulting
warnings to the module."

  (defund vl-module-leftright-check (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* ((ctxexprs     (vl-module-ctxexprs x))
         (new-warnings (vl-exprctxalist-leftright-check ctxexprs)))
      (change-vl-module x
                        :warnings (append new-warnings (vl-module->warnings x)))))

  (local (in-theory (enable vl-module-leftright-check)))

  (defthm vl-module-p-of-vl-module-leftright-check
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-leftright-check x))))

  (defthm vl-module->name-of-vl-module-leftright-check
    (equal (vl-module->name (vl-module-leftright-check x))
           (vl-module->name x))))


(defprojection vl-modulelist-leftright-check (x)
  (vl-module-leftright-check x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p
  :parents (leftright-check))

(defthm vl-modulelist->names-of-vl-modulelist-leftright-check
  (equal (vl-modulelist->names (vl-modulelist-leftright-check x))
         (vl-modulelist->names x))
  :hints(("Goal" :induct (len x))))







