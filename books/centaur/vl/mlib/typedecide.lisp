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

(local (xdoc::set-default-parents vl-expr-typedecide))





#|

(trace$
 #!vl (vl-index-typedecide
       :entry (list 'vl-index-typedecide
                    (with-local-ps (vl-pp-expr x)))
       :exit (b* (((list warnings-out type) values))
               (list 'vl-index-typedecide
                     (with-local-ps
                       (vl-print-warnings warnings-out))
                     type))))





|#

(define vl-signedness-ambiguity-warning ((x vl-expr-p)
                                         (signedness vl-arithclass-p)
                                         (caveat-flag))
  :returns (new-warnings vl-warninglist-p)
  (b* ((x (vl-expr-fix x))
       (signedness (vl-arithclass-fix signedness))
       (warnings nil))
    (if (and signedness caveat-flag)
        (warn :type :vl-signedness-ambiguity
              :msg "Signedness of ~a0 is potentially ambiguous.  NCVerilog ~
                    regards packed arrays of signed usertypes as unsigned, ~
                    and index expressions that result in signed usertypes as ~
                    signed, whereas VCS regards packed arrays of signed ~
                    usertypes as signed, and index expressions that result in ~
                    signed usertypes as unsigned.  We think the SystemVerilog ~
                    spec agrees with NCVerilog's interpretation, so we have ~
                    labeled this expression as ~s1."
              :args (list x (cond ((vl-arithclass-equiv signedness :vl-signed-int-class)
                                   "signed")
                                  ((vl-arithclass-equiv signedness :vl-unsigned-int-class)
                                   "unsigned")
                                  (t
                                   ;; We should never do this, right?
                                   (symbol-name signedness)))))
      (ok))))

(define vl-operandinfo-signedness-caveat ((x vl-operandinfo-p))
  (b* (((vl-operandinfo x)))
    (and (vl-partselect-case x.part :none)
         (consp x.seltrace)
         (vl-selstep->caveat (car x.seltrace)))))

(define vl-index-typedecide ((x        vl-expr-p)
                             (ss       vl-scopestack-p)
                             (scopes   vl-elabscopes-p))
  :guard (vl-expr-case x :vl-index)
  :returns (mv (new-warnings vl-warninglist-p)
               (class vl-arithclass-p))
  (b* ((x (vl-expr-fix x))
       (warnings nil)
       ((mv err opinfo) (vl-index-expr-typetrace x ss scopes))
       ((when err)
        (mv (fatal :type :vl-typedecide-fail
                   :msg "Failed to find the type of ~a0: ~@1"
                   :args (list x err))
            :vl-other-class))
       ((vl-operandinfo opinfo))
       ;; we don't need to check that usertypes are ok because
       ;; vl-index-expr-type ensures this
       ((unless (vl-datatype-packedp opinfo.type))
        ;; Some unpacked thing, no sensible arithmetic class.
        (mv (ok) :vl-other-class))
       (caveat1 (vl-operandinfo-signedness-caveat opinfo))
       ((mv caveat2 arithclass) (vl-datatype-arithclass opinfo.type))
       (warnings (vl-signedness-ambiguity-warning x arithclass (or caveat1 caveat2))))
    (mv warnings arithclass)))



(define vl-value-typedecide ((x vl-value-p))
  :returns (class vl-arithclass-p)
  (vl-value-case x
    :vl-constint (vl-exprsign->arithclass x.origsign)
    :vl-weirdint (vl-exprsign->arithclass x.origsign)
    ;; [Jared] bug fix 2016-03-18: we were formerly returning signed for
    ;; extint, but that was wrong: per SystemVerilog-2012 5.7.1: "In a
    ;; self-determined context, an unsized single-bit value shall have a width
    ;; of 1 bit, and the value shall be treated as unsigned."  See also
    ;; cosims/extint2.
    :vl-extint   :vl-unsigned-int-class
    ;; See SystemVerilog-2012 section 5.7.2.  Real literal constant numbers
    ;; represent double-precision floats (i.e., they are always reals, not
    ;; shortreals).  There's no way to write a shortreal as a literal.
    ;; Instead, 5.7.2 notes that "A cast can be used to convert literal real
    ;; values to the shortreal type (e.g., shortreal'(1.2))."
    :vl-real     :vl-real-class
    ;; See SystemVerilog-2012 section 5.8, time literals are interpreted as
    ;; realtime values (which are reals).
    :vl-time     :vl-real-class
    ;; See SystemVerilog-2012 section 5.9.  String literals (unlike the fancy
    ;; dynamic "string" data type) are treated as unsigned integer constants.
    :vl-string   :vl-unsigned-int-class))

(define vl-funcall-typedecide ((x vl-expr-p)
                               (ss vl-scopestack-p)
                               (scopes vl-elabscopes-p))
  :guard (vl-expr-case x :vl-call (not x.systemp) :otherwise nil)
  :returns (mv (warnings vl-warninglist-p)
               (class    vl-arithclass-p))
  (b* (((vl-call x) (vl-expr-fix x))
       (warnings nil)
       ((mv err trace ?context ?tail)
        (vl-follow-scopeexpr x.name ss))
       ((when err)
        (mv (fatal :type :vl-typedecide-fail
                   :msg "Failed to find function ~a0: ~@1"
                   :args (list (vl-scopeexpr->expr x.name) err))
            :vl-error-class))
       ((vl-hidstep lookup) (car trace))
       ((unless (eq (tag lookup.item) :vl-fundecl))
        (mv (fatal :type :vl-typedecide-fail
                  :msg "In function call ~a0, function name does not ~
                        refer to a fundecl but instead ~a1"
                  :args (list x lookup.item))
            :vl-error-class))
       ((vl-fundecl lookup.item))
       (fnscopes (vl-elabscopes-traverse (rev lookup.elabpath) scopes))
       (info (vl-elabscopes-item-info lookup.item.name fnscopes))
       (item (or info lookup.item))
       ((unless (eq (tag item) :vl-fundecl))
        ;; note: it looks like we're doing this twice but it's different this time
        (mv (fatal :type :vl-selfsize-fail
                   :msg "In function call ~a0, function name does not ~
                        refer to a fundecl but instead ~a1"
                   :args (list x item))
            :vl-error-class))
       ((vl-fundecl item))
       ((mv err rettype)
        (vl-datatype-usertype-resolve item.rettype lookup.ss))
       ((when err)
        (mv (fatal :type :vl-typedecide-fail
                   :msg "In function call ~a0, the function's return ~
                         type ~a1 had unresolvable usertypes: ~@2"
                   :args (list x item.rettype err))
            :vl-error-class))
       ((unless (vl-datatype-packedp rettype))
        ;; Unpacked return type so it's just other.
        (mv (ok) :vl-other-class))
       ((mv caveat class) (vl-datatype-arithclass rettype))
       (warnings (vl-signedness-ambiguity-warning x class caveat)))
    (mv (ok) class)))

(define vl-syscall-typedecide ((x vl-expr-p))
  :guard (vl-expr-case x :vl-call x.systemp :otherwise nil)
  :returns (mv (warnings vl-warninglist-p)
               (class    vl-arithclass-p))
  (b* ((warnings nil)

       ;; For most system functions that we support, we can just look
       ;; up their return type with vl-syscall->returninfo.
       ;;
       ;; However, some functions are special.  For instance, what is the
       ;; return type of $signed or $unsigned?  They are weird polymorphic
       ;; functions that don't have a well-defined datatype because the size of
       ;; the thing they return depends on the size of their input.  But, we
       ;; *do* know that they always return signed/unsigned results.  So,
       ;; handle these specially here.
       (name (vl-simple-id-name (vl-call->name x)))
       ((when (equal name "$signed"))   (mv (ok) :vl-signed-int-class))
       ((when (equal name "$unsigned")) (mv (ok) :vl-unsigned-int-class))

       (retinfo (vl-syscall->returninfo x))
       ((unless retinfo)
        ;; We don't know about this system function.  I think it makes the
        ;; most sense to just call this an error.
        (mv (ok) :vl-error-class))

       ;; If know the return type of this system function, so just use
       ;; our datatype arithclass determination for that type.
       ((vl-coredatatype-info retinfo)))
    (mv (ok) (vl-coretype-arithclass retinfo retinfo.default-signedp))))


;; (deflist vl-maybe-exprsign-list-p (x)
;;   (vl-maybe-exprsign-p x))


#|

(trace$
 #!vl (vl-expr-typedecide-aux
       :entry (list 'vl-expr-typedecide-aux
                    x (vl-pps-expr x))
       :exit (b* (((list warnings type) values))
               (list 'vl-expr-typedecide-aux
                     type))))

|#

(define vl-unaryop-typedecide ((x          vl-expr-p)
                               (arg-class  vl-arithclass-p))
  :prepwork ((local (defthm vl-unary->op-forward
                      (vl-unaryop-p (vl-unary->op x))
                      :rule-classes ((:forward-chaining :trigger-terms ((vl-unary->op x)))))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable acl2::member-of-cons))))
  :guard (vl-expr-case x :vl-unary)
  :returns (mv (warnings vl-warninglist-p)
               (class    vl-arithclass-p))
  (b* (((vl-unary x) (vl-expr-fix x))
       (warnings nil)
       (arg-class (vl-arithclass-fix arg-class)))
    (case x.op
      ((:vl-unary-plus :vl-unary-minus :vl-unary-bitnot)
       ;; From 5.5.1, I believe these fall into the "all other operators"
       ;; rule and just take on the signedness of their argument.
       (mv (ok) arg-class))

      ((:vl-unary-lognot :vl-unary-bitand :vl-unary-bitor
        :vl-unary-nand :vl-unary-nor :vl-unary-xor :vl-unary-xnor)
       ;; We believe the result is always unsigned; see "minutia".  If we ever
       ;; decide this is not right, review the rules in oprewrite that
       ;; introduce concatenations like !a -> {~(|a)} since they are not
       ;; supposed to change signs.
       (mv (ok) :vl-unsigned-int-class))

      ((:vl-unary-preinc :vl-unary-predec :vl-unary-postinc :vl-unary-postdec)
       (mv (fatal :type :vl-typedecide-fail
                  :msg  "Programming error: Increment/decrement ~
                         operators should be handled before now. (~a0)"
                  :args (list x))
           :vl-error-class))

      (otherwise
       (progn$ (impossible)
               (mv (ok) :vl-error-class))))))

(define vl-binaryop-typedecide ((x           vl-expr-p)
                                (left-class  vl-arithclass-p)
                                (right-class vl-arithclass-p))
  :prepwork ((local (defthm vl-binary->op-forward
                      (vl-binaryop-p (vl-binary->op x))
                      :rule-classes ((:forward-chaining :trigger-terms ((vl-binary->op x)))))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable acl2::member-of-cons))))
  :guard (vl-expr-case x :vl-binary)
  :returns (mv (warnings vl-warninglist-p)
               (class    vl-arithclass-p))
  (b* (((vl-binary x) (vl-expr-fix x))
       (warnings nil)
       (left-class  (vl-arithclass-fix left-class))
       (right-class (vl-arithclass-fix right-class)))
    (case x.op
      ((:vl-binary-eq :vl-binary-neq :vl-binary-ceq :vl-binary-cne
        :vl-binary-lt :vl-binary-lte :vl-binary-gt :vl-binary-gte

        ;; SystemVerilog-2012 extensions: I believe (although it's hard to
        ;; find good evidence in the spec to support this) that these are
        ;; also producing 1-bit unsigned answers.
        :vl-binary-wildneq :vl-binary-wildeq
        )

       (mv (ok) :vl-unsigned-int-class))

      ((:vl-binary-logand :vl-binary-logor :vl-implies :vl-equiv)
       ;; We believe the result is always unsigned; see "minutia".
       (mv (ok) :vl-unsigned-int-class))

      ((:vl-binary-plus :vl-binary-minus :vl-binary-times :vl-binary-div :vl-binary-rem
        :vl-binary-bitand :vl-binary-bitor :vl-binary-xor :vl-binary-xnor)
       ;; Simple context-determined binary ops.
       (mv (ok) (vl-arithclass-max left-class right-class)))

      ((:vl-binary-shr :vl-binary-shl :vl-binary-ashr :vl-binary-ashl :vl-binary-power)
       ;; We believe the second op's type does NOT affect the result type; see
       ;; "minutia"
       (mv (ok) left-class))

      ((:vl-binary-assign :vl-binary-plusassign :vl-binary-minusassign
        :vl-binary-timesassign :vl-binary-divassign :vl-binary-remassign
        :vl-binary-andassign :vl-binary-orassign :vl-binary-xorassign
        :vl-binary-shlassign :vl-binary-shrassign :vl-binary-ashlassign
        :vl-binary-ashrassign)
       (mv (fatal :type :vl-typedecide-fail
                  :msg  "Programming error: Assignment operators should ~
                         be handled before now. (~a0)"
                  :args (list x))
           :vl-error-class))

      (otherwise
       (progn$ (impossible)
               (mv (ok) :vl-error-class))))))


(define vl-expr-typedecide ((x        vl-expr-p)
                            (ss       vl-scopestack-p)
                            (scopes   vl-elabscopes-p))
  :parents (expr-tools)
  :short "Determine the arithmetic class (signed or unsigned integer, shortreal
or real, or something else) of an top-level or self-determined expression."

  :long "<p>This function must <b>only</b> be used on \"top-level\" and
self-determined portions of expressions.  That is, consider an assignment
like:</p>

@({
  assign w = {foo + bar, a + b} | (baz + 1) ;
})

<p>Here, it is legitimate to call @('vl-expr-typedecide') to determine the
arithmetic class of:</p>

<ul>
 <li>@('foo + bar'), because it is self-determined,</li>
 <li>@('a + b'), because it is self-determined, and</li>
 <li>@('{foo + bar, a + b} | (baz + 1)'), because it is top-level.</li>
</ul>

<p>But it is <b>not</b> legitimate to try to decide the class of, @('baz + 1')
in isolation, and doing so could yield an nonsensical result.  For instance, if
@('baz') is signed then, by itself, @('baz + 1') looks like a signed addition.
But concatenations are always unsigned, so in the larger context we can see
that this addition is in fact unsigned.</p>

<p>The @('class') we return is only a @(see vl-arithclass-p).  We might return
an error class if there is some kind of actual error with the module or the
expression, e.g., the use of a wire which is not declared; in these cases we
add fatal @(see warnings).  But we may also encounter expressions whose type we
do not know how to compute (e.g., perhaps the expression is an unsupported
system call).  In such cases we just return an error class without adding any
warnings.</p>

<p>See @(see vl2014::expression-sizing-minutia) for many relevant notes on
expression signedness.</p>"

  :verify-guards nil
  :returns (mv (warnings vl-warninglist-p)
               (class    vl-arithclass-p))
  :measure (vl-expr-count x)
  (b* ((x        (vl-expr-fix x))
       (warnings nil))
    (vl-expr-case x
      :vl-special
      ;; Things like $, null, and empty queues are valid but not any kind of
      ;; sensible arithmetic objects.
      (mv (ok) :vl-other-class)

      :vl-literal (mv (ok) (vl-value-typedecide x.val))
      :vl-index   (vl-index-typedecide x ss scopes)

      :vl-unary   (b* (((mv warnings arg-class) (vl-expr-typedecide x.arg ss scopes))
                       ((wmv warnings ans)      (vl-unaryop-typedecide x arg-class)))
                    (mv warnings ans))

      :vl-binary (b* (((mv warnings left-class)   (vl-expr-typedecide x.left ss scopes))
                      ((wmv warnings right-class) (vl-expr-typedecide x.right ss scopes))
                      ((wmv warnings ans)         (vl-binaryop-typedecide x left-class right-class)))
                   (mv warnings ans))

      :vl-qmark
      ;; SystemVerilog-2012 Section 11.4.11 explains rules for non-integral types:
      ;;    foo ? real : real      --> real
      ;;    foo ? real : int       --> cast int to real, real result
      ;;    foo ? real : shortreal --> cast shortreal to real, real result
      ;;    foo ? int : castable-to-integral --> cast to integral, integral result
      ;;    and then tons of crazy rules for assignment-compatible things
      ;;
      ;; I think this basically jives with just arithclass-max on the
      ;; then/else branches, although I'm not entirely sure about when things
      ;; are castable to integers and that sort of stuff.
      (b* (((mv warnings then-class)  (vl-expr-typedecide x.then ss scopes))
           ((wmv warnings else-class) (vl-expr-typedecide x.else ss scopes)))
        (mv warnings (vl-arithclass-max then-class else-class)))

      ;; I think it makes no sense to try to assign a type to these.
      :vl-mintypmax (mv (ok) :vl-other-class)

      ;; From Verilog-2005 5.5.1, bit-selects, part-selects,
      ;; concatenations, and comparisons always produce unsigned results,
      ;; no matter the signedness of their operands.
      :vl-concat      (mv (ok) :vl-unsigned-int-class)
      :vl-multiconcat (mv (ok) :vl-unsigned-int-class)

      ;; See the comment about stream expressions in vl-expr-selfsize...
      :vl-stream      (mv (ok) :vl-other-class)

      :vl-call        (if x.systemp
                          (vl-syscall-typedecide x)
                        (vl-funcall-typedecide x ss scopes))

      :vl-cast (vl-casttype-case x.to
                 :type
                 (b* (((mv err to-type) (vl-datatype-usertype-resolve x.to.type ss))
                      ((when err)
                       (mv (fatal :type :vl-typedecide-fail
                                  :msg "Failed to resolve usertypes for ~
                                          cast expression ~a0: ~@1."
                                  :args (list x err))
                           :vl-error-class))
                      ((unless (vl-datatype-packedp to-type))
                       ;; Cast to some unpacked type.  BOZO is there some reason not
                       ;; to just call vl-datatype-arithclass?
                       (mv (ok) :vl-other-class))
                      ((mv ?caveat class) (vl-datatype-arithclass to-type)))
                   (mv (ok) class))
                 :signedness
                 (mv (ok) (if x.to.signedp :vl-signed-int-class :vl-unsigned-int-class))
                 :otherwise
                 (vl-expr-typedecide x.expr ss scopes))

      ;; It seems this should always returns a 1-bit unsigned.
      :vl-inside (mv (ok) :vl-unsigned-int-class)

      ;; Tagged unions aren't vector types.
      :vl-tagged (mv (ok) :vl-other-class)

      ;; these are special like streaming concatenations, only well typed by
      ;; context, unless they have a datatype.
      :vl-pattern (b* (((unless x.pattype) (mv (ok) :vl-other-class))
                       ((mv err pattype) (vl-datatype-usertype-resolve x.pattype ss))
                       ((when err)
                        (mv (fatal :type :vl-selfsize-fail
                                   :msg "Failed to resolve usertypes for ~
                                        pattern expression ~a0: ~@1"
                                   :args (list x err))
                            :vl-error-class))
                       ((unless (vl-datatype-packedp pattype))
                        (mv (ok) :vl-other-class))
                       ((mv ?caveat class) (vl-datatype-arithclass pattype)))
                    (mv (ok) class))

      ;; These aren't vector types
      :vl-eventexpr
      (mv (ok) :vl-other-class)))

    ///
    (verify-guards vl-expr-typedecide))


