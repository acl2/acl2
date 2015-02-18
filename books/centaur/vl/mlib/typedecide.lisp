; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "VL")
(include-book "hid-tools")
(include-book "expr-tools")
(include-book "syscalls")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable member-equal-when-member-equal-of-cdr-under-iff
                           acl2::consp-under-iff-when-true-listp)))

(local (in-theory (disable acl2::hons-assoc-equal-of-cons
                           acl2::member-of-cons
                           integerp-when-natp
                           not nfix acl2::zp-open)))
(local (in-theory (disable (tau-system))))






#|

(trace$
 #!vl (vl-index-typedecide
       :entry (list 'vl-index-typedecide
                    (with-local-ps (vl-pp-expr x)))
       :exit (b* (((list warnings-out type) values))
               (list 'vl-index-typedecide
                     (with-local-ps
                       (vl-print-warnings (butlast warnings-out (len warnings))))
                     type))))





|#

(define vl-signedness-ambiguity-warning ((x vl-expr-p)
                                         (ctx acl2::any-p)
                                         (signedness vl-maybe-exprtype-p)
                                         (caveat-flag)
                                         (warnings vl-warninglist-p))
  :returns (new-warnings vl-warninglist-p)
  (b* ((x (vl-expr-fix x))
       (signedness (vl-maybe-exprtype-fix signedness)))
    (if (and signedness caveat-flag)
        (warn :type :vl-signedness-ambiguity
              :msg "~a0: Signedness of ~a1 is potentially ~
                                 ambiguous.  NCVerilog regards packed arrays ~
                                 of signed usertypes as unsigned, and index ~
                                 expressions that result in signed usertypes ~
                                 as signed, whereas VCS regards packed arrays ~
                                 of signed usertypes as signed, and index ~
                                 expressions that result in signed usertypes ~
                                 as unsigned.  We think the SystemVerilog ~
                                 spec agrees with NCVerilog's interpretation, ~
                                 so we have labeled this expression as ~s2."
              :args (list ctx x (if (eq signedness :vl-signed)
                                    "signed"
                                  "unsigned")))
      (ok))))


(define vl-index-typedecide ((x        vl-expr-p)
                             (ss       vl-scopestack-p)
                             (ctx     acl2::any-p "context")
                             (warnings vl-warninglist-p))
  :guard (vl-expr-case x :vl-index)
  :returns (mv (new-warnings vl-warninglist-p)
               (type vl-maybe-exprtype-p))
  (b* ((x (vl-expr-fix x))
       (?ctx (vl-context-fix ctx))
       ((mv err caveat1 type & type-ss) (vl-index-expr-type x ss))
       ((when err)
        (mv (fatal :type :vl-typedecide-fail
                   :msg "~a0: Failed to find the type of ~a1: ~@2"
                   :args (list ctx x err))
            nil))
       ;; we don't need to check that usertypes are ok because
       ;; vl-index-expr-type ensures this
       ((unless (vl-datatype-packedp type type-ss))
        (mv (ok) nil))
       ((mv caveat2 signedness) (vl-datatype-signedness type type-ss))
       (warnings (vl-signedness-ambiguity-warning
                  x ctx signedness (or caveat1 caveat2) warnings)))
    (mv warnings signedness))
  ///
  (defrule warning-irrelevance-of-vl-index-typedecide
    (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
             (equal (mv-nth 1 (vl-index-typedecide x ss ctx warnings))
                    (mv-nth 1 (vl-index-typedecide x ss nil nil))))))


(define vl-value-typedecide ((x vl-value-p))
  :returns (type vl-maybe-exprtype-p)
  (vl-value-case x
    :vl-constint x.origtype
    :vl-weirdint x.origtype
    :vl-extint   :vl-signed
    :vl-string   :vl-unsigned
    :otherwise   nil))


(define vl-funcall-typedecide ((x vl-expr-p)
                               (ss vl-scopestack-p)
                               (ctx acl2::any-p)
                               (warnings vl-warninglist-p))
  :guard (vl-expr-case x :vl-call (not x.systemp) :otherwise nil)
  :returns (mv (warnings vl-warninglist-p)
               (type (and (vl-maybe-exprtype-p type)
                          (iff (vl-exprtype-p type) type))))
  (b* (((vl-call x) (vl-expr-fix x))
       ((mv err trace ?tail)
        (vl-follow-scopeexpr x.name ss))
       ((when err)
        (mv (fatal :type :vl-typedecide-fail
                   :msg "~a0: Failed to find function ~a1: ~@2"
                   :args (list ctx (vl-scopeexpr->expr x.name) err))
            nil))
       ((vl-hidstep lookup) (car trace))
       ((unless (eq (tag lookup.item) :vl-fundecl))
        (mv (fatal :type :vl-typedecide-fail
                  :msg "~a0: In function call ~a1, function name does not ~
                        refer to a fundecl but instead ~a2"
                  :args (list ctx x lookup.item))
            nil))
       ((vl-fundecl lookup.item))
       (err (vl-datatype-check-usertypes lookup.item.rettype lookup.ss))
       ((when err)
        (mv (fatal :type :vl-typedecide-fail
                   :msg "~a0: In function call ~a1, the function's return ~
                         type ~a2 had unresolvable usertypes: ~@3"
                   :args (list ctx x lookup.item.rettype err))
            nil))
       ((unless (vl-datatype-packedp lookup.item.rettype lookup.ss))
        (mv (ok) nil))
       ((mv caveat signedness) (vl-datatype-signedness  lookup.item.rettype lookup.ss))
       (warnings (vl-signedness-ambiguity-warning x ctx signedness caveat warnings)))
    (mv (ok) signedness))
  ///
  (defrule warning-irrelevance-of-vl-funcall-typedecide
    (let ((ret1 (vl-funcall-typedecide x ss ctx warnings))
          (ret2 (vl-funcall-typedecide x ss nil nil)))
      (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
               (equal (mv-nth 1 ret1)
                      (mv-nth 1 ret2))))))


(define vl-syscall-typedecide ((x vl-expr-p)
                               (ss vl-scopestack-p)
                               (ctx acl2::any-p)
                               (warnings vl-warninglist-p))
  :guard (vl-expr-case x :vl-call x.systemp :otherwise nil)
  :returns (mv (warnings vl-warninglist-p)
               (type (and (vl-maybe-exprtype-p type)
                          (iff (vl-exprtype-p type) type))))
  (declare (ignorable ss ctx))
  (b* ((retinfo (vl-syscall->returninfo x))
       ((unless retinfo)
        (mv (ok) nil))
       ((vl-coredatatype-info retinfo))
       ((unless retinfo.size)
        ;; Could be something like void or a real number!
        (mv (ok) nil))
       (signedp (vl-coredatatype-info->default-signedp retinfo)))
    (mv (ok)
        (if signedp :vl-signed :vl-unsigned)))
  ///
  (defrule warning-irrelevance-of-vl-syscall-typedecide
    (let ((ret1 (vl-syscall-typedecide x ss ctx warnings))
          (ret2 (vl-syscall-typedecide x ss nil nil)))
      (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
               (equal (mv-nth 1 ret1)
                      (mv-nth 1 ret2))))))


(deflist vl-maybe-exprtype-list-p (x)
  (vl-maybe-exprtype-p x))


#|

(trace$
 #!vl (vl-expr-typedecide-aux
       :entry (list 'vl-expr-typedecide-aux
                    x (vl-pps-expr x))
       :exit (b* (((list warnings type) values))
               (list 'vl-expr-typedecide-aux
                     type))))

|#

(define vl-unaryop-typedecide
  :parents (vl-expr-typedecide)
  ((x         vl-expr-p)
   (arg-type  vl-maybe-exprtype-p)
   (ctx       acl2::any-p)
   (warnings  vl-warninglist-p)
   (mode      (or (eq mode :probably-right)
                  (eq mode :probably-wrong))))
  :prepwork ((local (defthm vl-unary->op-forward
                      (vl-unaryop-p (vl-unary->op x))
                      :rule-classes ((:forward-chaining :trigger-terms ((vl-unary->op x)))))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable acl2::member-of-cons))))
  :guard (vl-expr-case x :vl-unary)
  :returns (mv (warnings vl-warninglist-p)
               (exprtype vl-maybe-exprtype-p))
  (b* (((vl-unary x) (vl-expr-fix x))
       (arg-type (vl-maybe-exprtype-fix arg-type)))
    (case x.op
      ((:vl-unary-plus :vl-unary-minus)
       ;; From 5.5.1, I believe these fall into the "all other operators"
       ;; rule and just take on the signedness of their argument.
       (mv (ok) arg-type))

      ((:vl-unary-lognot :vl-unary-bitnot :vl-unary-bitand :vl-unary-bitor
        :vl-unary-nand :vl-unary-nor :vl-unary-xor :vl-unary-xnor)
       (cond ((eq mode :probably-right)
              ;; We believe the result is always unsigned; see "minutia".
              ;; If we ever decide this is not right, review the rules in
              ;; oprewrite that introduce concatenations like !a -> {~(|a)}
              ;; since they are not supposed to change signs.
              (mv (ok) :vl-unsigned))
             (t
              ;; Probably-wrong mode: we act like the operand type matters and
              ;; treat this like a unary plus or minus.
              (mv (ok) arg-type))))

      ((:vl-unary-preinc :vl-unary-predec :vl-unary-postinc :vl-unary-postdec)
       (mv (fatal :type :vl-typedecide-fail
                  :msg  "~a0: Programming error: Increment/decrement ~
                         operators should be handled before now. (~a1)"
                  :args (list ctx x))
           nil))
      (otherwise (progn$ (impossible) (mv (ok) nil)))))
  ///
  
  (defrule warning-irrelevance-of-vl-unaryop-typedecide
    (let ((ret1 (vl-unaryop-typedecide x arg-size ctx warnings mode))
          (ret2 (vl-unaryop-typedecide x arg-size nil nil mode)))
      (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
               (equal (mv-nth 1 ret1) (mv-nth 1 ret2))))))

(define vl-binaryop-typedecide
  ((x           vl-expr-p)
   (left-type   vl-maybe-exprtype-p)
   (right-type  vl-maybe-exprtype-p)
   (ctx         acl2::any-p)
   (warnings    vl-warninglist-p)
   (mode        (or (eq mode :probably-right)
                    (eq mode :probably-wrong))))
  :prepwork ((local (defthm vl-binary->op-forward
                      (vl-binaryop-p (vl-binary->op x))
                      :rule-classes ((:forward-chaining :trigger-terms ((vl-binary->op x)))))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable acl2::member-of-cons))))
  :guard (vl-expr-case x :vl-binary)
  :returns (mv (warnings vl-warninglist-p)
               (exprtype vl-maybe-exprtype-p))
  (b* (((vl-binary x) (vl-expr-fix x))
       (left-type (vl-maybe-exprtype-fix left-type))
       (right-type (vl-maybe-exprtype-fix right-type)))
    (case x.op
      ((:vl-binary-eq :vl-binary-neq :vl-binary-ceq :vl-binary-cne
        :vl-binary-lt :vl-binary-lte :vl-binary-gt :vl-binary-gte

        ;; SystemVerilog-2012 extensions: I believe (although it's hard to
        ;; find good evidence in the spec to support this) that these are
        ;; also producing 1-bit unsigned answers.
        :vl-binary-wildneq :vl-binary-wildeq
        )

       (mv (ok) :vl-unsigned))

      ((:vl-binary-logand :vl-binary-logor :vl-implies :vl-equiv)
       (cond ((eq mode :probably-right)
              ;; We believe the result is always unsigned; see "minutia".
              (mv (ok) :vl-unsigned))
             (t
              ;; Probably wrong mode: we act like the operand types matter and
              ;; treat this like a regular binary op.
              (b* ((type  (and left-type right-type
                               (vl-exprtype-max left-type right-type))))
                (mv (ok) type)))))

      ((:vl-binary-plus :vl-binary-minus :vl-binary-times :vl-binary-div :vl-binary-rem
        :vl-binary-bitand :vl-binary-bitor :vl-binary-xor :vl-binary-xnor)
       ;; Simple context-determined binary ops.
       (b* ((type  (and left-type right-type
                        (vl-exprtype-max left-type right-type))))
         (mv (ok) type)))

      ((:vl-binary-shr :vl-binary-shl :vl-binary-ashr :vl-binary-ashl :vl-binary-power)
       (cond ((eq mode :probably-right)
              ;; We believe the second op's type does NOT affect the result
              ;; type; see "minutia"
              (mv (ok) left-type))
             (t
              ;; Probably-wrong mode: we act like the second op's type matters
              ;; and treat this like a regular binary op.
              (b* ((type  (and left-type right-type
                               (vl-exprtype-max left-type right-type))))
                (mv (ok) type)))))

      ((:vl-binary-assign :vl-binary-plusassign :vl-binary-minusassign
        :vl-binary-timesassign :vl-binary-divassign :vl-binary-remassign
        :vl-binary-andassign :vl-binary-orassign :vl-binary-xorassign
        :vl-binary-shlassign :vl-binary-shrassign :vl-binary-ashlassign
        :vl-binary-ashrassign)
       (mv (fatal :type :vl-typedecide-fail
                  :msg  "~a0: Programming error: Assignment operators should ~
                         be handled before now. (~a1)"
                  :args (list ctx x))
           nil))
      (otherwise (progn$ (impossible) (mv (ok) nil)))))
  ///
  (defrule warning-irrelevance-of-vl-binaryop-typedecide
    (let ((ret1 (vl-binaryop-typedecide x left-size right-size ctx warnings mode))
          (ret2 (vl-binaryop-typedecide x left-size right-size nil nil mode)))
      (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
               (equal (mv-nth 1 ret1) (mv-nth 1 ret2))))))


(with-output :off (event)
  :evisc (:gag-mode (evisc-tuple 3 4 nil nil))
  (define vl-expr-typedecide-aux
    ((x        vl-expr-p)
     (ss       vl-scopestack-p)
     (ctx      acl2::any-p)
     (warnings vl-warninglist-p)
     (mode     (or (eq mode :probably-wrong)
                   (eq mode :probably-right))))
    :parents (vl-expr-typedecide)
    :short "Core of computing expression signedness."

    :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

<p>These are the same arguments as @(see vl-expr-typedecide) except for
@('mode').  You should probably read @(see expression-sizing-minutia) to
understand the valid modes:</p>

<ul>

<li>In @(':probably-wrong') mode, we treat reduction/logical operations as if
they produce signed values when their argument is signed, and we allow the
types of self-determined operands in conditional operators, shifts, and so
forth to affect the resulting expression type.  We do not think this is how
sizing is supposed to be done, but a Verilog implementation that was based on a
reading of the specification might mistakenly do it this way.</li>

<li>In @(':probably-right') mode, we try to behave like other Verilog systems
and ignore the type of self-determined operands when computing the resulting
types of expressions, and we also treat reduction/logical operations as if they
produce unsigned values.</li>

</ul>"

    :prepwork ((local (in-theory (disable acl2::true-listp-member-equal
                                          acl2::consp-member-equal
                                          vl-warninglist-p-when-not-consp
                                          vl-warninglist-p-when-subsetp-equal
                                          cons-equal
                                          acl2::subsetp-member
                                          (:t member-equal)))))
    :verify-guards nil
    :returns (mv (warnings vl-warninglist-p)
                 (type     (and (vl-maybe-exprtype-p type)
                                (iff (vl-exprtype-p type) type))
                           :hints ('(:in-theory (disable (:d vl-expr-typedecide-aux))
                                     :expand ((:free (mode)
                                               (vl-expr-typedecide-aux
                                                x ss ctx warnings mode)))))))
    :measure (vl-expr-count x)
    (b* ((x        (vl-expr-fix x))
         (warnings (vl-warninglist-fix warnings)))
      (vl-expr-case x
        :vl-special (mv (ok) nil)
        :vl-value   (mv (ok) (vl-value-typedecide x.val))
        :vl-index   (vl-index-typedecide x ss ctx warnings)

        :vl-unary   (b* (((mv warnings arg-type)
                          (vl-expr-typedecide-aux x.arg ss ctx warnings mode)))
                      (vl-unaryop-typedecide x arg-type ctx warnings mode))

        :vl-binary (b* (((mv warnings left-type)
                         (vl-expr-typedecide-aux x.left ss ctx warnings mode))
                        ((mv warnings right-type)
                         (vl-expr-typedecide-aux x.right ss ctx warnings mode)))
                     (vl-binaryop-typedecide x left-type right-type ctx warnings mode))

        :vl-qmark (b* (((mv warnings test-type)
                        (vl-expr-typedecide-aux x.test ss ctx warnings mode))
                       ((mv warnings then-type)
                        (vl-expr-typedecide-aux x.then ss ctx warnings mode))
                       ((mv warnings else-type)
                        (vl-expr-typedecide-aux x.else ss ctx warnings mode)))
                    (cond ((eq mode :probably-right)
                           ;; We believe the first op's type does NOT affect the result type;
                           ;; see "minutia".
                           (mv warnings (and then-type else-type
                                             (vl-exprtype-max then-type else-type))))
                          (t
                           ;; Probably-wrong mode: we allow the first op's type to affect the
                           ;; result type.
                           (mv warnings (and test-type then-type else-type
                                             (vl-exprtype-max test-type then-type else-type))))))

        ;; I think it makes no sense to try to assign a type to these.
        :vl-mintypmax (mv (ok) nil)

        ;; From Verilog-2005 5.5.1, bit-selects, part-selects,
        ;; concatenations, and comparisons always produce unsigned results,
        ;; no matter the signedness of their operands.
        :vl-concat      (mv (ok) :vl-unsigned)
        :vl-multiconcat (mv (ok) :vl-unsigned)

        ;; See the comment about stream expressions in vl-expr-selfsize...
        :vl-stream      (mv (ok) nil)

        :vl-call        (if x.systemp
                            (vl-syscall-typedecide x ss ctx warnings)
                          (vl-funcall-typedecide x ss ctx warnings))

        :vl-cast (b* ((err (vl-datatype-check-usertypes x.to ss))
                      ((when err)
                       (mv (fatal :type :vl-typedecide-fail
                                  :msg "~a0: Failed to resolve usertypes for ~
                                        cast expression ~a1: ~@2."
                                  :args (list ctx x err))
                           nil))
                      ((unless (vl-datatype-packedp x.to ss))
                       (mv (ok) nil))
                      ((mv ?caveat signedness)
                       (vl-datatype-signedness x.to ss)))
                   (mv (ok) signedness))

        ;; By the spec, it seems this always returns a 1-bit unsigned (test this)
        :vl-inside (mv (ok) :vl-unsigned)

        ;; Tagged unions aren't vector types
        :vl-tagged (mv (ok) nil)

        ;; Assignment patterns need context to determine type
        :vl-pattern (mv (ok) nil)))

    ///
    (local (in-theory (disable member-equal-when-member-equal-of-cdr-under-iff
                               vl-warninglist-p-when-subsetp-equal
                               set::double-containment
                               default-car
                               default-cdr
                               (:d vl-expr-typedecide-aux))))

    (verify-guards vl-expr-typedecide-aux)


    ;; Trick for avoiding the horrendous induction scheme necessary to prove
    ;; warning and context irrelevance directly.  The problem with the direct
    ;; proof is that the induction scheme doesn't always choose the right
    ;; instantiations of the warnings in the induction hyps.  Instead, we
    ;; basically just want to induct by saying "assuming that all possible
    ;; warnings/contexts are irrelevant in the recursive calls, all possible
    ;; warnings/contexts are irrelevant in the top-level call."  So instead of
    ;; inductively proving "the warnings and context are irrelevant" (with
    ;; implicit universal quantification) we prove "for all warnings and
    ;; context, they're irrelevant" (with explicit universal quantification
    ;; that gets instantiated in the induction hyps as well).
    (local (defun-sk all-warnings-and-context-irrelevant (x ss mode)
             (forall (ctx warnings)
                     (implies (syntaxp (not (and (equal warnings ''nil)
                                                 (equal ctx ''nil))))
                              (b* (((mv & type1)
                                    (vl-expr-typedecide-aux x ss ctx warnings mode))
                                   ((mv & type2)
                                    (vl-expr-typedecide-aux x ss nil nil mode)))
                                (equal type1 type2))))
             :rewrite :direct))

    (local (in-theory (disable all-warnings-and-context-irrelevant)))

    (local
     (defthmd warning-irrelevance-of-vl-expr-typedecide-aux-1
       (all-warnings-and-context-irrelevant x ss mode)
       :hints (("goal"
                :in-theory (enable (:i vl-expr-typedecide-aux))
                :induct (vl-expr-typedecide-aux x ss ctx warnings mode)
                :expand ((:free (ctx warnings mode) (vl-expr-typedecide-aux x ss ctx warnings mode))
                         (:free (mode) (all-warnings-and-context-irrelevant x ss mode)))))))

    (defthm warning-irrelevance-of-vl-expr-typedecide-aux
      (implies (syntaxp (not (and (equal warnings ''nil)
                                  (equal ctx ''nil))))
               (b* (((mv & type1)
                     (vl-expr-typedecide-aux x ss ctx warnings mode))
                    ((mv & type2)
                     (vl-expr-typedecide-aux x ss nil nil mode)))
                 (equal type1 type2)))
      :hints (("goal" :use warning-irrelevance-of-vl-expr-typedecide-aux-1)))


    (defrule symbolp-of-vl-expr-typedecide-aux
      (symbolp (mv-nth 1 (vl-expr-typedecide-aux x ss ctx warnings mode)))
      :in-theory (enable (tau-system))
      :rule-classes :type-prescription)))



(define vl-expr-typedecide
  :parents (vl-expr-size)
  :short "Computation of expression signedness (main routine)."
  ((x        vl-expr-p)
   (ss vl-scopestack-p)
   (ctx     acl2::any-p)
   (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p)
               (type     (and (vl-maybe-exprtype-p type)
                              (equal (vl-exprtype-p type) (if type t nil)))))

  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

<p>We determine the signedness of an expression.  This function must
<b>only</b> be used on \"top-level\" and self-determined portions of
expressions.  That is, consider an assignment like:</p>

@({
  assign w = {foo + bar, a + b} | (baz + 1) ;
})

<p>Here, it is legitimate to call @('vl-expr-typedecide') to determine the
signs of:</p>

<ul>
 <li>@('foo + bar'), because it is self-determined,</li>
 <li>@('a + b'), because it is self-determined, and</li>
 <li>@('{foo + bar, a + b} | (baz + 1)'), because it is top-level.</li>
</ul>

<p>But it is <b>not</b> legitimate to try to decide the sign of, @('baz + 1')
in isolation, and doing so could yield an nonsensical result.  For instance, if
@('baz') is signed then, by itself, @('baz + 1') looks like a signed addition.
But concatenations are always unsigned, so in the larger context we can see
that this addition is in fact unsigned.</p>

<p>The @('sign') we return is only a @(see vl-maybe-exprtype-p).  We might
return @('nil') for two reasons.  First, there could be some kind of actual
error with the module or the expression, e.g., the use of a wire which is not
declared; in these cases we add fatal @(see warnings).  But we may also
encounter expressions whose type we do not know how to compute (e.g., perhaps
the expression is an unsupported system call).  In such cases we just return
@('nil') for the sign without adding any warnings.</p>"

  (b* ((x    (vl-expr-fix x))
       (ctx (vl-context-fix ctx))
       ((mv warnings right-type) (vl-expr-typedecide-aux x ss ctx warnings :probably-right))
       ((mv warnings wrong-type) (vl-expr-typedecide-aux x ss ctx warnings :probably-wrong))
       (warnings
        (if (eq right-type wrong-type)
            warnings
          (warn :type :vl-warn-vague-spec
                :msg "~a0: expression ~a1 has a type which is not necessarily ~
                      clear according to the discussion in the Verilog-2005 ~
                      standard.  We believe its type should be ~s2, but think ~
                      it would be easy for other Verilog systems to ~
                      mistakenly interpret the expression as ~s3.  To reduce ~
                      any potential confusion, you may wish to rewrite this ~
                      expression to make its signedness unambiguous.  Some ~
                      typical causes of signedness are plain decimal numbers ~
                      like 10, and the use of integer variables instead of ~
                      regs."
                :args (list ctx x right-type wrong-type)))))
    (mv warnings right-type))

  ///
  (defrule warning-irrelevance-of-vl-expr-typedecide
    (let ((ret1 (vl-expr-typedecide x ss ctx warnings))
          (ret2 (vl-expr-typedecide x ss nil nil)))
      (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
               (equal (mv-nth 1 ret1)
                      (mv-nth 1 ret2))))))






