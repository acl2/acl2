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
(include-book "hid-tools")
(include-book "range-tools")
(include-book "syscalls")
(include-book "../util/sum-nats")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))


(define vl-index-selfsize ((x vl-expr-p "the index expression")
                           (ss vl-scopestack-p)
                           (ctx vl-context-p "context")
                           (warnings vl-warninglist-p))
  :returns (mv (new-warnings vl-warninglist-p)
               (size maybe-posp :rule-classes :type-prescription))
  (declare (ignorable ctx))
  (b* ((warnings  (vl-warninglist-fix warnings))
       ((mv warning type) (vl-index-find-type x ss (vl-context-fix ctx)))
       ((when warning)
        (mv (cons (change-vl-warning warning :fatalp t) warnings) nil))
       ((mv warning size)
        (vl-datatype-size type))
       ((when warning)
        (mv (cons (change-vl-warning warning :fatalp t) warnings) nil)))
    (mv warnings size))
  ///

  (local
   (make-event ;; test: x[8] sizes to 1 for simple net
    (b* ((x-vardecl (make-vl-vardecl :name "x"
                                     :type (make-vl-coretype
                                            :name :vl-logic
                                            :pdims (list
                                                    (make-vl-range
                                                     :msb (vl-make-index 10)
                                                     :lsb (vl-make-index 0))))
                                     :nettype :vl-wire
                                     :loc *vl-fakeloc*))
         (expr (make-vl-nonatom :op :vl-bitselect
                                :args (list (vl-idexpr "x" nil nil)
                                            (vl-make-index 8))))
         (mod (make-vl-module :name "foo" :origname "foo"
                              :vardecls (list x-vardecl)
                              :minloc *vl-fakeloc*
                              :maxloc *vl-fakeloc*))
         (design (make-vl-design :mods (list mod)))
         (ss (vl-scopestack-push mod (vl-scopestack-init design)))
         ((mv warnings size)
          (vl-index-selfsize expr ss x-vardecl nil)))
      (if (and (not warnings)
               (eql size 1))
          '(value-triple :ok)
        (er hard? 'test-vl-index-selfsize
            "Bad result: ~x0~%" (list warnings size))))))

  (defrule warning-irrelevance-of-vl-index-selfsize
    (let ((ret1 (vl-index-selfsize x ss ctx warnings))
          (ret2 (vl-index-selfsize x ss nil nil)))
      (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
               (equal (mv-nth 1 ret1)
                      (mv-nth 1 ret2))))))


(define vl-atom-selfsize
  :parents (vl-expr-selfsize)
  :short "Compute the self-determined size of an atom."
  ((x        vl-expr-p)
   (ss       vl-scopestack-p)
   (ctx     vl-context-p)
   (warnings vl-warninglist-p))
  :guard (vl-atom-p x)
  :verbosep t
  :returns (mv (warnings vl-warninglist-p)
               (size     maybe-natp :rule-classes :type-prescription))

  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

<p>We attempt to compute the \"self-determined size\" of the atom @('x').
Another way to look at this function is as an extension of \"origwidth\" from
constint/weirdint atoms to include identifiers.</p>

<p>We have taken special care in our @(see lexer) to ensure that every
constant, whether it is a @(see vl-weirdint-p) or @(see vl-constint-p), has a
determined width.  As a result, it is easy to determine the self-determined
size of a constant, and we never fail to do so.</p>

<p>For identifiers, we must look up the identifier in the module to try to
determine its size.  This can fail if the identifier is not declared in the
module, or if its size is not resolved.  In these cases, we add a fatal warning
to @('warnings') and return @('nil') as the size.</p>

<p>We do not try to size other atoms, such as real numbers, individual HID
pieces, function names, system function names, etc.; instead we just return
@('nil') as the size.  But we do not issue a warning in this case, because it
seems like these things are not really supposed to have sizes.</p>"
  :guard-hints (("goal" :in-theory (enable vl-hidexpr-p vl-hidname-p)))
  (b* ((x    (vl-expr-fix x))
       (ctx (vl-context-fix ctx))
       (guts (vl-atom->guts x))

       ((when (vl-fast-constint-p guts))
        (mv (ok) (vl-constint->origwidth guts)))

       ((when (vl-fast-weirdint-p guts))
        (mv (ok) (vl-weirdint->origwidth guts)))

       ((when (vl-fast-string-p guts))
        ;; natp, not posp
        (mv (ok) (* 8 (length (vl-string->value guts)))))

       ((when (eq (tag guts) :vl-extint))
        ;; Tests seem to show that these selfdetermine to size 1.
        (mv (ok) 1))

       ((unless (or (vl-fast-id-p guts)
                    (vl-fast-hidpiece-p guts)))
        ;; Reals, function names, hierarchical identifier pieces, etc., for which
        ;; a size is not applicable.

        ;; [Jared] 2015-01-22.  We were formerly causing warnings here.  This
        ;; contradicted the documentation and led to irritating, spurious warnings
        ;; about things like "Couldn't size atom: $finish" in statements, which
        ;; is just silly.  I think it makes more sense NOT to cause any warnings
        ;; here, so let's do that.

        ;; (mv (warn :type :vl-selfsize-fail
        ;;           :msg "~a0: Couldn't size atom: ~a1"
        ;;           :args (list ctx x))
        ;;     nil)
        (mv (ok) nil)))

    (vl-index-selfsize x ss ctx warnings))

  ///
  (defrule warning-irrelevance-of-vl-atom-selfsize
    (let ((ret1 (vl-atom-selfsize x ss ctx warnings))
          (ret2 (vl-atom-selfsize x ss nil nil)))
      (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
               (equal (mv-nth 1 ret1) (mv-nth 1 ret2))))))



(defines vl-interesting-size-atoms
  :parents (vl-tweak-fussy-warning-type)
  :short "Heuristic for tweaking fussy size warnings."
  :long "<p>Our basic goal is to gather all the atoms throughout an expression
that are \"relevant\" to the current self-size computation.  This is a fuzzy
concept and you should never use it for anything semantically meaningful, it's
only meant as a heuristic for generating more useful warnings.</p>"

  :prepwork ((local (in-theory (disable (tau-system)
                                        MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF
                                        double-containment
                                        acl2::subsetp-member
                                        acl2::member-equal-when-all-equalp
                                        default-car
                                        default-cdr
                                        acl2::true-listp-member-equal
                                        ))))

  (define vl-expr-interesting-size-atoms ((x vl-expr-p))
    :measure (vl-expr-count x)
    :verify-guards nil
    :returns (exprs (and (vl-exprlist-p exprs)
                         (vl-atomlist-p exprs)))
    (b* ((x (vl-expr-fix x))
         ((when (vl-fast-atom-p x))
          (list x))
         (op   (vl-nonatom->op x))
         (args (vl-nonatom->args x)))
      (case op
        ((:vl-bitselect
          :vl-unary-bitand :vl-unary-nand :vl-unary-bitor
          :vl-unary-nor :vl-unary-xor :vl-unary-xnor :vl-unary-lognot
          :vl-binary-logand :vl-binary-logor
          :vl-binary-eq :vl-binary-neq :vl-binary-ceq :vl-binary-cne
          :vl-binary-lt :vl-binary-lte :vl-binary-gt :vl-binary-gte
          :vl-partselect-colon :vl-partselect-pluscolon :vl-partselect-minuscolon
          :vl-select-colon :vl-select-pluscolon :vl-select-minuscolon
          :vl-syscall :vl-funcall :vl-mintypmax :vl-hid-dot
          :vl-index :vl-scope

          ;; Eventually many of these may be worth considering...
          :vl-with-index :vl-with-colon :vl-with-pluscolon :vl-with-minuscolon
          :vl-stream-left :vl-stream-right
          :vl-stream-left-sized :vl-stream-right-sized

          :vl-tagged

          :vl-binary-wildeq :vl-binary-wildneq
          :vl-implies :vl-equiv

          ;; This can definitely affect sizes, but I'm not sure what to do
          ;; about it yet.
          :vl-binary-cast
          :vl-pattern-multi
          :vl-pattern-type
          :vl-pattern-positional
          :vl-pattern-keyvalue
          :vl-keyvalue

          ;; Sizing shouldn't encounter these.
          :vl-unary-preinc :vl-unary-predec :vl-unary-postinc :vl-unary-postdec
          :vl-binary-assign
          :vl-binary-plusassign :vl-binary-minusassign
          :vl-binary-timesassign :vl-binary-divassign :vl-binary-remassign
          :vl-binary-andassign :vl-binary-orassign :vl-binary-xorassign
          :vl-binary-shlassign :vl-binary-shrassign :vl-binary-ashlassign :vl-binary-ashrassign

          :vl-inside :vl-valuerange :vl-valuerangelist
          )
         ;; Don't gather anything from here.
         nil)

        ((:vl-binary-power
          :vl-unary-plus :vl-unary-minus :vl-unary-bitnot
          :vl-binary-shl :vl-binary-shr :vl-binary-ashl :vl-binary-ashr)
         ;; Second arg doesn't affect selfsize
         (vl-expr-interesting-size-atoms (first args)))

        ((:vl-qmark :vl-multiconcat)
         ;; First arg is special, don't consider it
         (vl-exprlist-interesting-size-atoms (cdr args)))

        ((:vl-binary-plus :vl-binary-minus :vl-binary-times :vl-binary-div :vl-binary-rem
                          :vl-binary-bitand :vl-binary-bitor :vl-binary-xor :vl-binary-xnor
                          :vl-concat)
         ;; All args affect size
         (vl-exprlist-interesting-size-atoms args))

        (otherwise
         ;; To make us account for all ops
         (impossible)))))

  (define vl-exprlist-interesting-size-atoms ((x vl-exprlist-p))
    :measure (vl-exprlist-count x)
    :returns (exprs (and (vl-exprlist-p exprs)
                         (vl-atomlist-p exprs)))
    (if (consp x)
        (append (vl-expr-interesting-size-atoms (car x))
                (vl-exprlist-interesting-size-atoms (cdr x)))
      nil))
  ///
  (defrule true-listp-of-vl-expr-interesting-size-atoms
    (true-listp (vl-expr-interesting-size-atoms x))
    :rule-classes :type-prescription)

  (defrule true-listp-of-vl-exprlist-interesting-size-atoms
    (true-listp (vl-exprlist-interesting-size-atoms x))
    :rule-classes :type-prescription)

  (verify-guards vl-expr-interesting-size-atoms
    :hints(("Goal" :in-theory (enable vl-nonatom->op-forward
                                      acl2::member-of-cons))))

  (deffixequiv-mutual vl-interesting-size-atoms))


(define vl-collect-unsized-ints ((x vl-exprlist-p))
  :parents (vl-tweak-fussy-warning-type)
  :returns (sub-x vl-exprlist-p)
  (cond ((atom x)
         nil)
        ((and (vl-fast-atom-p (car x))
              (vl-fast-constint-p (vl-atom->guts (car x)))
              (vl-constint->wasunsized (vl-atom->guts (car x))))
         (cons (vl-expr-fix (car x))
               (vl-collect-unsized-ints (cdr x))))
        (t
         (vl-collect-unsized-ints (cdr x))))
  ///
  (defrule vl-exprlist-resolved-p-of-vl-collect-unsized-ints
    (vl-exprlist-resolved-p (vl-collect-unsized-ints x))
    :enable vl-expr-resolved-p))


(define nats-below-p
  :parents (vl-tweak-fussy-warning-type)
  :short "Is every number in a list smaller than some maximum?"
  ((max natp)
   (x   nat-listp))
  :hooks nil
  (if (atom x)
      t
    (and (< (car x) max)
         (nats-below-p max (cdr x)))))

(define vl-expr-extint-p ((x vl-expr-p))
  :returns (extint-p booleanp :rule-classes :type-prescription)
  :prepwork ((local (in-theory (enable tag-reasoning))))
  (mbe :logic (and (vl-atom-p x)
                   (vl-extint-p (vl-atom->guts x)))
       :exec (and (vl-fast-atom-p x)
                  (eq (tag (vl-atom->guts x)) :vl-extint))))

(define vl-tweak-fussy-warning-type
  :parents (vl-op-selfsize)
  :short "Heuristically categorize fussy warnings according to severity."
  ((type  symbolp   "Base warning type, which we may adjust.")
   (a     vl-expr-p "LHS expression, i.e., A in: A + B, or C ? A : B")
   (b     vl-expr-p "RHS expression, i.e., B in: A + B, or C ? A : B")
   (asize natp      "Self-determined size of A.")
   (bsize natp      "Self-determined size of B.")
   (op    vl-op-p   "The particular operation."))
  :returns
  (adjusted-type symbolp :rule-classes :type-prescription
                 "@('NIL') for <i>do not warn</i>, or some other warning type
                  that is derived from @('type').")

  :long "<p>This function is called when we've just noticed that A and B have
different self-sizes but are used in an expression like @('A == B'), @('A &
B'), @('C ? A : B'), or similar, and hence one or the other is going to be
implicitly extended.  We're going to issue a fussy size warning, and we want to
decide what type to give it.  I.e., is this a minor warning, or a normal
warning?</p>

<p>My original approach was just to say: the warning should be minor if ASIZE
or BSIZE is 32.  But this happens in many very common cases where unsized
numbers are used, such as:</p>

@({
    foo[3:0] == 7;          //  4 bits == 32 bits
    foo[0] ? bar[3:0] : 0;  //  foo[0] ? 4 bits : 32 bits
})

<p>Over time I have added many additional tweaks, see the comments for
details.</p>"
  :prepwork ((local (in-theory (disable (tau-system)))))
  (b* ((type  (acl2::symbol-fix type))
       (op    (vl-op-fix op))
       (asize (lnfix asize))
       (bsize (lnfix bsize))
       (a     (vl-expr-fix a))
       (b     (vl-expr-fix b))

       (a-zerop (and (vl-expr-resolved-p a)
                     (eql (vl-resolved->val a) 0)))
       (b-zerop (and (vl-expr-resolved-p b)
                     (eql (vl-resolved->val b) 0)))
       ((when (or a-zerop b-zerop))
        ;; Zeros are very special.  It's very annoying to look at warnings
        ;; telling you that your zeroes aren't the right size.  So, even in
        ;; bitwisey contexts, suppress any warnings about zeroes.
        nil)

       ((when (or (vl-expr-extint-p a)
                  (vl-expr-extint-p b)))
        ;; Suppress warnings because '0, '1, etc., are supposed to grow to the
        ;; size of whatever is around them.
        nil)

       (a-fits-b-p (and (vl-expr-resolved-p a) (unsigned-byte-p bsize (vl-resolved->val a))))
       (b-fits-a-p (and (vl-expr-resolved-p b) (unsigned-byte-p asize (vl-resolved->val b))))
       ((when (and (or a-fits-b-p b-fits-a-p)
                   (member op '(:vl-binary-eq :vl-binary-neq
                                :vl-binary-ceq :vl-binary-cne
                                :vl-binary-lt :vl-binary-lte
                                :vl-binary-gt :vl-binary-gte))))
        ;; Suppress warnings about things like "foo == 3'd7" or "foo == 7"
        ;; where foo is, say, a 5 bit wire.  We know that the value of the 7
        ;; fits into the width of foo, so this isn't really wrong.
        nil)

       (a32p (eql asize 32))
       (b32p (eql bsize 32))
       ((unless (or a32p b32p))
        ;; Neither op is 32 bits, so this doesn't seem like it's related to
        ;; unsized numbers, go ahead and warn.
        type)

       ;; Figure out which one is 32-bit and which one is not.  We assume
       ;; they aren't both 32 bits, since otherwise we shouldn't be called.
       ((mv expr-32 size-other) (if a32p (mv a bsize) (mv b asize)))

       ;; Collect up interesting unsized ints in the 32-bit expression.  If it
       ;; has unsized ints, they're probably the reason it's 32 bits.  After
       ;; collecting them, see if they fit into the size of the other expr.
       (atoms         (vl-expr-interesting-size-atoms expr-32))
       (unsized       (vl-collect-unsized-ints atoms))
       (unsized-fit-p (nats-below-p (ash 1 size-other)
                                    (vl-exprlist-resolved->vals unsized)))
       ((unless unsized-fit-p)
        ;; Well, hrmn, there's some integer here that doesn't fit into the size
        ;; of the other argument.  This is especially interesting because
        ;; there's likely to be some kind of truncation here.  Give it a new
        ;; type.
        (intern-in-package-of-symbol (cat (symbol-name type) "-CONST-TOOBIG") type))

       ((when (consp unsized))
        ;; What does this mean?  Well, there are at least some unsized numbers
        ;; in positions that are affecting our selfsize, and every such unsized
        ;; number does fit into the new size we're going into, so it seems
        ;; pretty safe to make this a minor warning.
        (intern-in-package-of-symbol (cat (symbol-name type) "-MINOR") type)))

    ;; Otherwise, we didn't find any unsized atoms, so just go ahead and do the
    ;; warning.
    type))

(define vl-nonatom->original-operator ((x vl-expr-p))
  :parents (origexprs)
  :short "Get the original operator from a non-atomic expression."
  :guard (not (vl-atom-p x))
  :returns (op vl-op-p)
  (b* ((atts (vl-nonatom->atts x))
       (orig (cdr (hons-assoc-equal "VL_ORIG_EXPR" atts)))
       ((when (and orig
                   (not (vl-fast-atom-p orig))))
        (vl-nonatom->op orig)))
    (vl-nonatom->op x)))

(define vl-fancy-op-str ((x vl-op-p))
  :returns (str stringp :rule-classes :type-prescription)
  (b* ((x (vl-op-fix x)))
    (or (vl-op-text x)
        (symbol-name x))))


(define vl-op-selfsize
  :parents (vl-expr-selfsize)
  :short "Main function for computing self-determined expression sizes."
  ((op        vl-op-p)
   (args      vl-exprlist-p)
   (arg-sizes nat-listp)
   (context   vl-expr-p)
   (ctx       vl-context-p)
   (warnings  vl-warninglist-p))
  :guard
  (and (not (vl-atom-p context))
       (or (not (vl-op-arity op))
           (equal (len args) (vl-op-arity op)))
       (same-lengthp args arg-sizes))
  :returns
  (mv (warnings vl-warninglist-p)
      (size     maybe-natp :rule-classes :type-prescription))
  :verify-guards nil

  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

<p>We attempt to determine the size of the expression formed by applying some
operator, @('op'), to some arguments, @('args').  We assume that each argument
has already had its self-size computed successfully and that the results of
these computations are given as the @('arg-sizes').</p>

<p>The @('context') is irrelevant and is only used to form better error
messages; it is supposed to be the (sub) expression we are trying to size.  The
@('ctx') is similarly irrelevant, and gives the broader context for this
expression.</p>

<p>This function basically implements Verilog-2005 Table 5-22, or
SystemVerilog-2012 Table 11-21. See @(see expression-sizing).</p>"

  (b* ((op      (vl-op-fix op))
       (args    (vl-exprlist-fix args))
       (context (vl-expr-fix context))
       (ctx     (vl-context-fix ctx)))
    (case (vl-op-fix op)
      (( ;; All of these operations have one-bit results, and we have no
        ;; expectations that their argument sizes should agree or anything like
        ;; that.
        :vl-bitselect
        :vl-unary-bitand :vl-unary-nand :vl-unary-bitor :vl-unary-nor
        :vl-unary-xor :vl-unary-xnor :vl-unary-lognot
        :vl-binary-logand :vl-binary-logor

        ;; SystemVerilog-2012 additions.  These also produce 1-bit results and
        ;; we don't care if their arguments have equal sizes.
        :vl-implies :vl-equiv)
       (mv (ok) 1))

      (( ;; These were originally part of the above case; they all return
        ;; one-bit results.  However, we separate them out because,
        ;; intuitively, their arguments "should" be the same size.  So as a
        ;; Linting feature, we add warnings if any implicit size extension will
        ;; occur.
        :vl-binary-eq :vl-binary-neq :vl-binary-ceq :vl-binary-cne
        :vl-binary-lt :vl-binary-lte :vl-binary-gt :vl-binary-gte

        ;; SystemVerilog-2012 additions.  Although Table 11-21 doesn't specify
        ;; what the sizes are here, Section 11.4.6 says these produce a 1-bit
        ;; self-sized result and explains how the arguments are to be widened
        ;; similarly to ordinary equality comparisons.
        :vl-binary-wildeq :vl-binary-wildneq)
       (b* ((type (and (/= (first arg-sizes) (second arg-sizes))
                       (vl-tweak-fussy-warning-type :vl-fussy-size-warning-1
                                                    (first args)
                                                    (second args)
                                                    (first arg-sizes)
                                                    (second arg-sizes)
                                                    op)))
            (warnings
             (if (not type)
                 (ok)
               (warn :type type
                     :msg "~a0: arguments to a ~s1 comparison operator have ~
                             different \"self-sizes\".  The smaller argument ~
                             will be implicitly widened to match the larger ~
                             argument. Arguments:~%     ~
                               - lhs (width ~x2): ~a4~%     ~
                               - rhs (width ~x3): ~a5~%"
                     :args (list ctx
                                 (vl-fancy-op-str (vl-nonatom->original-operator context))
                                 (first arg-sizes)
                                 (second arg-sizes)
                                 (first args)
                                 (second args))))))
         (mv (ok) 1)))

      ((:vl-binary-power
        :vl-unary-plus :vl-unary-minus :vl-unary-bitnot
        :vl-binary-shl :vl-binary-shr :vl-binary-ashl :vl-binary-ashr)
       ;; All of these operations keep the size of their first operands.
       (mv (ok) (lnfix (first arg-sizes))))

      ((:vl-binary-plus :vl-binary-minus :vl-binary-times :vl-binary-div :vl-binary-rem)
       ;; All of these operations take the max size of either operand.
       ;; Practically speaking we will probably never see times, div, or rem
       ;; operators.  However, plus and minus are common.  We probably do not
       ;; want to issue any size warnings in the case of plus or minus, since
       ;; one argument or the other often needs to be expanded.
       (mv (ok) (max (lnfix (first arg-sizes))
                     (lnfix (second arg-sizes)))))

      ((:vl-binary-bitand :vl-binary-bitor :vl-binary-xor :vl-binary-xnor)
       ;; All of these operations take the max size of either operand.  But
       ;; this is a place where implicit widening could be bad.  I mean, you
       ;; probably don't want to be doing A & B when A and B are different
       ;; sizes, right?
       (b* ((max (max (lnfix (first arg-sizes))
                      (lnfix (second arg-sizes))))
            (type (and (/= (first arg-sizes) (second arg-sizes))
                       (vl-tweak-fussy-warning-type :vl-fussy-size-warning-2
                                                    (first args)
                                                    (second args)
                                                    (first arg-sizes)
                                                    (second arg-sizes)
                                                    op)))
            (warnings
             (if (not type)
                 (ok)
               (warn :type type
                     :msg "~a0: arguments to a bitwise ~s1 operator have ~
                             different \"self-sizes\".  The smaller argument ~
                             will be implicitly widened to match the larger ~
                             argument. Arguments:~%     ~
                               - lhs (width ~x2): ~a4~%     ~
                               - rhs (width ~x3): ~a5~%"
                     :args (list ctx
                                 (vl-fancy-op-str (vl-nonatom->original-operator context))
                                 (first arg-sizes)
                                 (second arg-sizes)
                                 (first args)
                                 (second args)
                                 context)))))
         (mv (ok) max)))

      ((:vl-qmark)
       ;; The conditional takes the max size of its true and false branches.
       ;; We now warn if the branches don't agree on their size and hence will
       ;; be widened.
       (b* ((max (max (lnfix (second arg-sizes))
                      (lnfix (third arg-sizes))))
            (type (and (/= (second arg-sizes) (third arg-sizes))
                       (vl-tweak-fussy-warning-type :vl-fussy-size-warning-3
                                                    (second args)
                                                    (third args)
                                                    (second arg-sizes)
                                                    (third arg-sizes)
                                                    op)))
            (warnings
             (if (not type)
                 (ok)
               (warn :type type
                     :msg "~a0: branches of a ?: operator have different ~
                             \"self-sizes\".  The smaller branch will be ~
                             implicitly widened to match the larger branch. ~
                             Arguments:~%     ~
                               - Condition:               ~a1~%     ~
                               - True Branch  (size ~x2): ~a4~%     ~
                               - False Branch (size ~x3): ~a5~%"
                     :args (list ctx
                                 (first args)
                                 (second arg-sizes)
                                 (third arg-sizes)
                                 (second args)
                                 (third args))))))
         (mv (ok) max)))

      ((:vl-concat)
       ;; Concatenations have the sum of their arguments' widths
       (mv (ok) (sum-nats arg-sizes)))

      ((:vl-multiconcat)
       ;; For multiple concatenations, the size is its multiplicity times the
       ;; size of the concatenation-part.  The multiplicity can be zero.
       (b* ((multiplicity (first args))
            (concat-width (lnfix (second arg-sizes)))
            ((unless (vl-expr-resolved-p multiplicity))
             (mv (fatal :type :vl-unresolved-multiplicity
                        :msg "~a0: cannot size ~a1 because its multiplicity ~
                                has not been resolved."
                        :args (list ctx context))
                 nil))
            (size (* (vl-resolved->val multiplicity) concat-width)))
         (mv (ok) size)))

      ((:vl-partselect-colon)
       ;; A part-select's width is one greater than the difference in its
       ;; indices.  For instance, a[3:0] is 4 bits, while a[3:3] is one bit.
       (b* ((left  (second args))
            (right (third args))
            ((unless (and (vl-expr-resolved-p left)
                          (vl-expr-resolved-p right)))
             (mv (fatal :type :vl-unresolved-select
                        :msg "~a0: cannot size ~a1 since it does not have ~
                                resolved indices."
                        :args (list ctx context))
                 nil))
            (left-val  (vl-resolved->val left))
            (right-val (vl-resolved->val right))
            (size      (+ 1 (abs (- left-val right-val)))))
         (mv (ok) size)))

      ((:vl-partselect-pluscolon :vl-partselect-minuscolon)
       ;; foo[base_expr +: width_expr] has the width specified by width_expr,
       ;; which must be a positive constant. (See Section 5.2.1)
       (b* ((width-expr (second args))
            ((unless (and (vl-expr-resolved-p width-expr)
                          (> (vl-resolved->val width-expr) 0)))
             (mv (fatal :type :vl-unresolved-select
                        :msg "~a0: cannot size ~a1 since its width expression ~
                                is not a resolved, positive constant."
                        :args (list ctx context))
                 nil))
            (size (vl-resolved->val width-expr)))
         (mv (ok) size)))

      ((:vl-mintypmax)
       ;; I do not think it makes any sense to think about the size of a
       ;; mintypmax expression.  We just return nil and cause no warnings since
       ;; the width is basically "inapplicable."
       (mv (ok) nil))

      ((:vl-stream-left :vl-stream-right
        :vl-stream-left-sized :vl-stream-right-sized)
       (mv (warn :type :vl-untested-sizing-assumptions
                 :msg "~a0: sizing of streaming concatenations is ~
                         experimental and may not be correct."
                 :args (list ctx))
           (if (member op '(:vl-stream-left-sized :vl-stream-right-sized))
               (sum-nats (mbe :logic (cdr arg-sizes)
                              :exec (and (consp arg-sizes) (cdr arg-sizes))))
             (sum-nats arg-sizes))))

      ((:vl-hid-dot :vl-index :vl-scope

        ;; See vl-expr-selfsize.  We handle function calls and system calls
        ;; separately and should never invoke them in vl-op-selfsize.
        :vl-syscall :vl-funcall

        ;; BOZO these might not belong here, but it seems like the
        ;; safest place to put them until they're implemented
        :vl-with-index :vl-with-colon :vl-with-pluscolon :vl-with-minuscolon
        :vl-tagged :vl-binary-cast
        :vl-select-colon :vl-select-pluscolon :vl-select-minuscolon
        :vl-pattern-multi
        :vl-pattern-type
        :vl-pattern-positional
        :vl-pattern-keyvalue
        :vl-keyvalue

        ;; We shouldn't encounter these in sizing, they should be gotten
        ;; rid of in increment-elim
        :vl-unary-preinc :vl-unary-predec :vl-unary-postinc :vl-unary-postdec
        :vl-binary-assign
        :vl-binary-plusassign :vl-binary-minusassign
        :vl-binary-timesassign :vl-binary-divassign :vl-binary-remassign
        :vl-binary-andassign :vl-binary-orassign :vl-binary-xorassign
        :vl-binary-shlassign :vl-binary-shrassign :vl-binary-ashlassign :vl-binary-ashrassign

        :vl-inside :vl-valuerange :vl-valuerangelist
        )

       ;; We don't handle these here.  They should be handled in
       ;; vl-expr-selfsize specially, because unlike all of the other
       ;; operators, we can't assume that their subexpressions' sizes can be
       ;; computed.  Instead, we need to only try to determine the size of
       ;; "top-level" HIDs, and also specially handle array indexes.
       (mv (fatal :type :vl-programming-error
                  :msg "~a0: vl-op-selfsize should not encounter ~a1"
                  :args (list ctx context))
           nil))

      (otherwise
       (progn$ (impossible)
               (mv (ok) nil)))))
  ///
  (defrule warning-irrelevance-of-vl-op-selfsize
    (let ((ret1 (vl-op-selfsize op args arg-sizes context ctx warnings))
          (ret2 (vl-op-selfsize op args arg-sizes context nil nil)))
      (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
               (equal (mv-nth 1 ret1) (mv-nth 1 ret2)))))

  (local (defun make-vl-op-p-cases (ops)
           (if (atom ops)
               nil
             (cons `(equal op ,(car ops))
                   (make-vl-op-p-cases (cdr ops))))))

  (local (make-event
          `(defthm vl-op-p-forward
             (implies (vl-op-p op)
                      (or . ,(make-vl-op-p-cases (strip-cars (vl-ops-table)))))
             :rule-classes :forward-chaining
             :hints(("Goal" :in-theory (enable hons-assoc-equal
                                               vl-op-p
                                               (vl-ops-table)))))))

  (local (defthm natp-of-first-when-nat-listp
           (implies (nat-listp x)
                    (equal (natp (car x))
                           (<= 1 (len x))))))

  (local (defthm natp-of-second-when-nat-listp
           (implies (nat-listp x)
                    (equal (natp (second x))
                           (<= 2 (len x))))))

  (local (defthm natp-of-third-when-nat-listp
           (implies (nat-listp x)
                    (equal (natp (third x))
                           (<= 3 (len x))))
           :hints(("Goal" :expand ((nat-listp x)
                                   (nat-listp (cdr x))
                                   (nat-listp (cddr x)))))))

  (local (defthm natp-of-abs
           (implies (integerp x)
                    (natp (abs x)))
           :rule-classes :type-prescription))

  (local (in-theory (disable (tau-system)
                             /= abs nfix
                             MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF
                             ACL2::TRUE-LISTP-MEMBER-EQUAL
                             ACL2::MEMBER-EQUAL-WHEN-ALL-EQUALP
                             acl2::subsetp-member
                             double-containment
                             acl2::consp-member-equal
                             default-car
                             default-cdr
                             ACL2::CONSP-UNDER-IFF-WHEN-TRUE-LISTP
                             ACL2::CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP
                             )))
  (with-output :off (event)
    (verify-guards vl-op-selfsize
      :hints(("Goal"
              :do-not '(generalize fertilize eliminate-destructors)
              :do-not-induct t)))))


(define vl-partselect-selfsize ((x vl-expr-p "the partselect expression")
                                (ss vl-scopestack-p)
                                (ctx vl-context-p "context")
                                (warnings vl-warninglist-p))
  :guard (not (eq (vl-expr-kind x) :atom))
  :returns (mv (new-warnings vl-warninglist-p)
               (size maybe-posp :rule-classes :type-prescription))
  (b* ((warnings  (vl-warninglist-fix warnings))
       ((mv warning type) (vl-partselect-expr-type x ss ctx))
       ((when warning)
        (mv (cons (change-vl-warning warning :fatalp t) warnings) nil))
       ((mv warning size)
        (vl-datatype-size type))
       ((when warning)
        (mv (cons (change-vl-warning warning :fatalp t) warnings) nil)))
    (mv warnings size))
  ///

  (local
   (make-event ;; test: x[8:4] sizes to 5 for simple net
    (b* ((x-vardecl (make-vl-vardecl :name "x"
                                     :type (make-vl-coretype
                                            :name :vl-logic
                                            :pdims (list
                                                    (make-vl-range
                                                     :msb (vl-make-index 10)
                                                     :lsb (vl-make-index 0))))
                                     :nettype :vl-wire
                                     :loc *vl-fakeloc*))
         (expr (make-vl-nonatom :op :vl-partselect-colon
                                :args (list (vl-idexpr "x" nil nil)
                                            (vl-make-index 8)
                                            (vl-make-index 4))))
         (mod (make-vl-module :name "foo" :origname "foo"
                              :vardecls (list x-vardecl)
                              :minloc *vl-fakeloc*
                              :maxloc *vl-fakeloc*))
         (design (make-vl-design :mods (list mod)))
         (ss (vl-scopestack-push mod (vl-scopestack-init design)))
         ((mv warnings size)
          (vl-partselect-selfsize expr ss x-vardecl nil)))
      (if (and (not warnings)
               (eql size 5))
          '(value-triple :ok)
        (er hard? 'test-vl-index-selfsize
            "Bad result: ~x0~%" (list warnings size))))))

  (defrule warning-irrelevance-of-vl-partselect-selfsize
    (let ((ret1 (vl-partselect-selfsize x ss ctx warnings))
          (ret2 (vl-partselect-selfsize x ss nil nil)))
      (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
               (equal (mv-nth 1 ret1)
                      (mv-nth 1 ret2))))))


(define vl-funcall-selfsize ((x vl-expr-p)
                             (ss vl-scopestack-p)
                             (ctx vl-context-p)
                             (warnings vl-warninglist-p))
  :guard (and (not (vl-atom-p x))
              (eq (vl-nonatom->op x) :vl-funcall))
  :returns (mv (warnings vl-warninglist-p)
               (size maybe-natp :rule-classes :type-prescription))
  (b* ((ctx (vl-context-fix ctx))
       ((vl-nonatom x) (vl-expr-fix x))
       ((unless (and (consp x.args)
                     (vl-fast-atom-p (first x.args))
                     (vl-funname-p (vl-atom->guts (first x.args)))))
        (raise "Programming error: function call without function name: ~x0" x)
        (mv (warn :type :vl-programming-error
                  :msg "~a0: Function call without function name: ~a1"
                  :args (list ctx x))
            nil))
       (fnname (vl-funname->name (vl-atom->guts (first x.args))))
       (decl (vl-scopestack-find-item fnname ss))
       ((unless (and decl (eq (tag decl) :vl-fundecl)))
        (mv (warn :type :vl-function-not-found
                  :msg "~a0: Function not found: ~a1"
                  :args (list ctx x))
            nil))
       ((vl-fundecl decl))
       ((mv warning size)
        (vl-datatype-size decl.rettype))
       ((when warning)
        (mv (cons (change-vl-warning warning :fatalp t) (ok)) nil)))
    (mv (ok) size))
  ///
  (defrule warning-irrelevance-of-vl-funcall-selfsize
    (let ((ret1 (vl-funcall-selfsize x ss ctx warnings))
          (ret2 (vl-funcall-selfsize x ss nil nil)))
      (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
               (equal (mv-nth 1 ret1)
                      (mv-nth 1 ret2))))))

(define vl-syscall-selfsize ((x        vl-expr-p)
                             (ss       vl-scopestack-p)
                             (ctx      vl-context-p)
                             (warnings vl-warninglist-p))
  :guard (and (not (vl-atom-p x))
              (eq (vl-nonatom->op x) :vl-syscall))
  :returns (mv (warnings vl-warninglist-p)
               (size maybe-natp :rule-classes :type-prescription))
  (declare (ignorable ss ctx))
  (b* ((retinfo (vl-syscall->returninfo x))
       ((unless retinfo)
        (mv (ok) nil))
       (size (vl-coredatatype-info->size retinfo)))
    (mv (ok) size))
  ///
  (defrule warning-irrelevance-of-vl-syscall-selfsize
    (let ((ret1 (vl-syscall-selfsize x ss ctx warnings))
          (ret2 (vl-syscall-selfsize x ss nil nil)))
      (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
               (equal (mv-nth 1 ret1)
                      (mv-nth 1 ret2))))))

(defines vl-expr-selfsize
  :parents (vl-expr-size)
  :short "Computation of self-determined expression sizes."

  :long "<p><b>Warning</b>: these functions should typically only be called by
the @(see expression-sizing) transform.</p>

<p>Some failures are expected, e.g., we do not know how to size some system
calls.  In these cases we do not cause any warnings.  But in other cases, a
failure might mean that the expression is malformed in some way, e.g., maybe it
references an undefined wire or contains a raw, \"unindexed\" reference to an
array.  In these cases we generate fatal warnings.</p>

<p>BOZO we might eventually add as inputs the full list of modules and a
modalist so that we can look up HIDs.  An alternative would be to use the
annotations left by transforms such as the now-defunct
@('vl-design-follow-hids'), e.g., @('VL_HID_RESOLVED_RANGE_P'), to see how wide
HIDs are.</p>"

  (define vl-expr-selfsize
    ((x        vl-expr-p        "Expression whose size we are to compute.")
     (ss       vl-scopestack-p  "Scope where the expression occurs.")
     (ctx      vl-context-p     "Context for warnings.")
     (warnings vl-warninglist-p "Ordinary @(see warnings) accumulator."))
    :returns
    (mv (warnings vl-warninglist-p)
        (size     maybe-natp :rule-classes :type-prescription
                  :hints ('(:in-theory (disable vl-expr-selfsize
                                                vl-exprlist-selfsize)
                            :expand ((vl-expr-selfsize x ss ctx warnings))))))
    :verify-guards nil
    :measure (vl-expr-count x)
    :flag :expr
    (b* ((x (vl-expr-fix x))

         ((when (vl-fast-atom-p x))
          (vl-atom-selfsize x ss ctx warnings))

         (op   (vl-nonatom->op x))
         (args (vl-nonatom->args x))

         ((when (member op '(:vl-hid-dot :vl-index :vl-bitselect)))
          (vl-index-selfsize x ss ctx warnings))

         ((when (member op '(:vl-partselect-colon :vl-partselect-pluscolon :vl-partselect-minuscolon
                             :vl-select-colon :vl-select-pluscolon :vl-select-minuscolon)))
          (vl-partselect-selfsize x ss ctx warnings))

         ((when (eq op :vl-syscall))
          (vl-syscall-selfsize x ss ctx warnings))

         ((when (eq op :vl-funcall))
          (vl-funcall-selfsize x ss ctx warnings))

         ((mv warnings arg-sizes)
          (vl-exprlist-selfsize args ss ctx warnings))

         ((when (member nil arg-sizes))
          ;; Some subexpression was not given its size.  We don't try to
          ;; produce a size.
          (mv warnings nil))

         ;; Otherwise, all subexpressions sized successfully.  Call
         ;; vl-op-selfsize to do all the work.
         ((mv warnings size)
          (vl-op-selfsize op args arg-sizes x ctx warnings)))

      (mv warnings size)))

  (define vl-exprlist-selfsize
    ((x        vl-exprlist-p    "Expressions whose sizes we are to compute.")
     (ss       vl-scopestack-p  "Scope where these expressions occur.")
     (ctx      vl-context-p     "Context for warnings.")
     (warnings vl-warninglist-p "Ordinary @(see warnings) accumulator."))
    :returns
    (mv (warnings vl-warninglist-p)
        (size-list (and (vl-maybe-nat-listp size-list)
                        (equal (len size-list) (len x)))
                  :hints ('(:in-theory (disable vl-expr-selfsize
                                                vl-exprlist-selfsize)
                            :expand ((vl-exprlist-selfsize x ss ctx warnings))))))
    :measure (vl-exprlist-count x)
    :flag :list
    (b* (((when (atom x))
          (mv (ok) nil))
         ((mv warnings car-size)
          (vl-expr-selfsize (car x) ss ctx warnings))
         ((mv warnings cdr-sizes)
          (vl-exprlist-selfsize (cdr x) ss ctx warnings))
         (sizes (cons car-size cdr-sizes)))
      (mv warnings sizes)))
  ///

  (local (in-theory (disable vl-expr-selfsize
                             vl-exprlist-selfsize)))

  (local
   (defthm-vl-expr-selfsize-flag
     (defthm true-listp-of-vl-exprlist-selfsize
       (true-listp (mv-nth 1 (vl-exprlist-selfsize x ss ctx warnings)))
       :hints ('(:expand ((vl-exprlist-selfsize x ss ctx warnings))))
       :rule-classes :type-prescription
       :flag :list)
     :skip-others t))

  (verify-guards vl-expr-selfsize)

  (local
   (defthm-vl-expr-selfsize-flag
     ;; This is pretty subtle.  The induction scheme that the flag function
     ;; would generate if we tried to directly use warnings and NIL isn't right
     ;; in the list case.  We have to generalize this to an arbitrary warnings1
     ;; and warnings2.  Then, ACL2's induction heuristic is smart enough to get
     ;; the right scheme, but only when we tell it to consider the flag function
     ;; for both warnings1 and warnings2.  Ugh.  This took a long time to figure
     ;; out.
     (defthm l0
       (let ((ret1 (vl-expr-selfsize x ss ctx warnings1))
             (ret2 (vl-expr-selfsize x ss ctx warnings2)))
         (equal (mv-nth 1 ret1)
                (mv-nth 1 ret2)))
       :rule-classes nil
       :flag :expr)

     (defthm l1
       (let ((ret1 (vl-exprlist-selfsize x ss ctx warnings1))
             (ret2 (vl-exprlist-selfsize x ss ctx warnings2)))
         (equal (mv-nth 1 ret1)
                (mv-nth 1 ret2)))
       :rule-classes nil
       :flag :list)

     :hints(("Goal"
             :do-not '(generalize fertilize)
             :induct (and (vl-expr-selfsize-flag flag x ss ctx warnings1)
                          (vl-expr-selfsize-flag flag x ss ctx warnings2))
             :expand ((vl-expr-selfsize x ss ctx warnings1)
                      (vl-expr-selfsize x ss ctx warnings2)
                      (:free (warnings)
                       (vl-exprlist-selfsize x ss ctx warnings)))))))

  (local (flag::def-doublevar-induction vl-expr-selfsize-double-ctx
           :orig-fn vl-expr-selfsize-flag
           :old-var ctx :new-var ctx1))

  (local (defthm warning-irrelevance-of-vl-exprlist-selfsize-tmp
           (let ((ret1 (vl-exprlist-selfsize x ss ctx warnings))
                 (ret2 (vl-exprlist-selfsize x ss ctx nil)))
             (implies (syntaxp (not (equal warnings ''nil)))
                      (equal (mv-nth 1 ret1)
                             (mv-nth 1 ret2))))
           :hints (("goal" :use ((:instance l1 (warnings1 warnings) (warnings2 nil)))))))

  (deffixequiv-mutual vl-expr-selfsize
    :hints (("goal" :in-theory (e/d (vl-exprlist-fix)
                                    (vl-expr-selfsize
                                        vl-exprlist-selfsize))
             :expand ((:free (ss ctx warnings)
                       (vl-expr-selfsize x ss ctx warnings))
                      (:free (ss ctx warnings)
                       (vl-expr-selfsize (vl-expr-fix x) ss ctx warnings))
                      (:free (ss ctx warnings)
                       (vl-exprlist-selfsize x ss ctx warnings))
                      (:free (a b ss ctx warnings)
                       (vl-exprlist-selfsize (cons a b) ss ctx warnings))))))

  (local
   (defthm-vl-expr-selfsize-flag
     (defthm l2
       (let ((ret1 (vl-expr-selfsize x ss ctx1 warnings))
             (ret2 (vl-expr-selfsize x ss ctx2 warnings)))
         (equal (mv-nth 1 ret1)
                (mv-nth 1 ret2)))
       :rule-classes nil
       :flag :expr)

     (defthm l3
       (let ((ret1 (vl-exprlist-selfsize x ss ctx1 warnings))
             (ret2 (vl-exprlist-selfsize x ss ctx2 warnings)))
         (equal (mv-nth 1 ret1)
                (mv-nth 1 ret2)))
       :rule-classes nil
       :flag :list)

     :hints(("Goal"
             :do-not '(generalize fertilize)
             :induct (vl-expr-selfsize-double-ctx flag x ss ctx1 warnings ctx2)
             :expand ((vl-expr-selfsize x ss ctx1 warnings)
                      (vl-expr-selfsize x ss ctx2 warnings)
                      (vl-exprlist-selfsize x ss ctx1 warnings)
                      (vl-exprlist-selfsize x ss ctx2 warnings))))))

  (defrule warning-irrelevance-of-vl-expr-selfsize
    (let ((ret1 (vl-expr-selfsize x ss ctx warnings))
          (ret2 (vl-expr-selfsize x ss nil nil)))
      (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
               (equal (mv-nth 1 ret1)
                      (mv-nth 1 ret2))))
    :use ((:instance l0 (warnings1 warnings) (warnings2 nil))
          (:instance l2 (ctx1 ctx) (ctx2 nil) (warnings nil))))

  (defrule warning-irrelevance-of-vl-exprlist-selfsize
    (let ((ret1 (vl-exprlist-selfsize x ss ctx warnings))
          (ret2 (vl-exprlist-selfsize x ss nil nil)))
      (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
               (equal (mv-nth 1 ret1)
                      (mv-nth 1 ret2))))
    :use ((:instance l1 (warnings1 warnings) (warnings2 nil))
          (:instance l3 (ctx1 ctx) (ctx2 nil) (warnings nil)))))

