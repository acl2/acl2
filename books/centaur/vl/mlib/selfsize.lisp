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
(include-book "../util/sum-nats")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable (tau-system))))

(define vl-value-selfsize ((x vl-value-p))
  :returns (width maybe-posp)
  (vl-value-case x
    :vl-constint x.origwidth
    :vl-weirdint (len x.bits)
    :vl-extint   1
    ;; Implementations always make strings at least 1 character wide -- the
    ;; empty string is equivalent to a string containing 1 null character.
    :vl-string   (* 8 (max 1 (length x.value)))
    :otherwise   nil))

(define vl-index-selfsize ((x vl-expr-p "the index expression")
                           (ss vl-scopestack-p)
                           (scopes vl-elabscopes-p))
  :guard (vl-expr-case x :vl-index)
  :returns (mv (new-warnings vl-warninglist-p)
               (size maybe-natp :rule-classes :type-prescription))
  (b* ((x (vl-expr-fix x))
       (warnings  nil)
       ;; We'll leave complaining about the signedness caveats to typedecide
       ((mv err opinfo) (vl-index-expr-typetrace x ss scopes))
       ((when err)
        (mv (fatal :type :vl-selfsize-fail
                   :msg "Failed to find the type of ~a0: ~@1"
                   :args (list x err))
            nil))
       ((vl-operandinfo opinfo))
       ((mv err size)
        (vl-datatype-size opinfo.type))

       ((when err)
        (mv (fatal :type :vl-selfsize-fail
                   :msg "Failed to find the size of datatype ~a0 for expression ~a1: ~@2"
                   :args (list opinfo.type x err))
            nil))

       ((unless (vl-datatype-packedp opinfo.type))
        ;; not a sizable datatype
        (mv (ok) nil)))

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
         (x-expr (vl-idexpr "x"))
         (expr (change-vl-index x-expr
                                :indices (list (vl-make-index 8))))
         (mod (make-vl-module :name "foo" :origname "foo"
                              :vardecls (list x-vardecl)
                              :minloc *vl-fakeloc*
                              :maxloc *vl-fakeloc*))
         (design (make-vl-design :mods (list mod)))
         (ss (vl-scopestack-push mod (vl-scopestack-init design)))
         ((mv warnings size)
          (vl-index-selfsize expr ss (vl-elabscopes-init))))
      (if (and (not warnings)
               (eql size 1))
          '(value-triple :ok)
        (er hard? 'test-vl-index-selfsize
            "Bad result: ~x0~%" (list warnings size)))))))


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
                                        acl2::member-of-cons
                                        ))))

  (define vl-expr-interesting-size-atoms ((x vl-expr-p))
    :measure (vl-expr-count x)
    :verify-guards nil
    :returns (vals vl-exprlist-p)
    (vl-expr-case x
      :vl-literal (list (vl-expr-fix x))
      :vl-index   (list (vl-expr-fix x))
      :vl-unary
      (case x.op
        ((:vl-unary-plus :vl-unary-minus :vl-unary-bitnot)
         ;; These are "transparent" to sizing, so yes, go inside
         ;; and get the interesting atoms in the argument.
         (vl-expr-interesting-size-atoms x.arg))
        ((:vl-unary-lognot :vl-unary-bitand :vl-unary-nand
          :vl-unary-bitor :vl-unary-nor :vl-unary-xor
          :vl-unary-xnor)
         ;; These all just generate 1-bit results, so anything
         ;; inside of them is not interesting to sizing.
         nil)
        ((:vl-unary-preinc :vl-unary-predec
          :vl-unary-postinc :vl-unary-postdec)
         ;; I think we want to go through these.
         (vl-expr-interesting-size-atoms x.arg))
        (otherwise (impossible)))
      :vl-binary
      (case x.op
        ((:vl-binary-logand :vl-binary-logor
          :vl-binary-lt :vl-binary-lte :vl-binary-gt :vl-binary-gte
          :vl-binary-eq :vl-binary-neq :vl-binary-ceq :vl-binary-cne
          :vl-binary-wildeq :vl-binary-wildneq
          :vl-implies :vl-equiv)
         ;; These always generate one-bit results, so there's no
         ;; reason to go into their args.
         nil)
        ((:vl-binary-plus :vl-binary-minus
          :vl-binary-times :vl-binary-div :vl-binary-rem
          :vl-binary-bitand :vl-binary-bitor :vl-binary-xor :vl-binary-xnor
          )
         ;; Both arguments affect sizing,
         (append (vl-expr-interesting-size-atoms x.left)
                 (vl-expr-interesting-size-atoms x.right)))
        ((:vl-binary-power :vl-binary-shr :vl-binary-shl
          :vl-binary-ashr :vl-binary-ashl)
         ;; Only the first argument affects the self-size.
         (vl-expr-interesting-size-atoms x.left))
        ((:vl-binary-assign
          :vl-binary-plusassign :vl-binary-minusassign
          :vl-binary-timesassign :vl-binary-divassign :vl-binary-remassign
          :vl-binary-andassign :vl-binary-orassign :vl-binary-xorassign
          :vl-binary-shlassign :vl-binary-shrassign
          :vl-binary-ashlassign :vl-binary-ashrassign)
         ;; Only the left hand side affects the size.
         (vl-expr-interesting-size-atoms x.left))
        (otherwise (impossible)))

      :vl-qmark
      ;; Size of the condition is irrelevant.
      (append (vl-expr-interesting-size-atoms x.then)
              (vl-expr-interesting-size-atoms x.else))

      ;; sswords: changed vl-concat and vl-multiconcat to not return any atoms.
      ;; If there is an unsized integer in a concatenation, that's a bit
      ;; strange to begin with.
      :vl-concat nil
      :vl-multiconcat nil
      :vl-mintypmax nil
      :vl-call      nil
      :vl-stream    nil
      :vl-cast      (vl-casttype-case x.to
                      :type nil :size nil
                      :otherwise (vl-expr-interesting-size-atoms x.expr))
      :vl-inside    nil
      :vl-tagged    nil ;; bozo?
      :vl-pattern   nil
      :vl-special   nil
      :vl-eventexpr nil))

  (define vl-exprlist-interesting-size-atoms ((x vl-exprlist-p))
    :measure (vl-exprlist-count x)
    :returns (vals vl-exprlist-p)
    (if (atom x)
        nil
      (append (vl-expr-interesting-size-atoms (car x))
              (vl-exprlist-interesting-size-atoms (cdr x)))))
  ///
  (defrule true-listp-of-vl-expr-interesting-size-atoms
    (true-listp (vl-expr-interesting-size-atoms x))
    :rule-classes :type-prescription)
  (defrule true-listp-of-vl-exprlist-interesting-size-atoms
    (true-listp (vl-exprlist-interesting-size-atoms x))
    :rule-classes :type-prescription)
  (verify-guards vl-expr-interesting-size-atoms
    :hints(("Goal" :in-theory (enable (:e tau-system) member-equal))))
  (deffixequiv-mutual vl-interesting-size-atoms))

#||
(trace$ #!vl (vl-operandinfo->type$inline :entry (list 'vl-operandinfo->type)
                                          :exit (list 'vl-operandinfo->type
                                                      (with-local-ps (vl-pp-datatype value)))))
(trace$ #!Vl (vl-is-unsized-int :entry (list 'vl-is-unsized-int (with-local-ps (vl-pp-expr x)) x)))
||#



;; BOZO this should look at the elabscopes too
(define vl-unsized-index-p
  :short "Identify occurrences of basic, unsized parameters."
  :parents (vl-tweak-fussy-warning-type)
  ((x  vl-expr-p)
   (ss vl-scopestack-p))
  :long "<p>We often run into cases like</p>

@({
    parameter foo = 5;
    ...
    assign w[3:0] = foo;
})

<p>It was annoying to get truncation warnings about this sort of thing.  So,
here, as a heuristic, we are looking for expression like @('foo') which are
references to untyped parameters.</p>"
  :prepwork ((local (in-theory (enable vl-paramdecl-p-when-wrong-tag
                                       vl-vardecl-p-when-wrong-tag))))
  (vl-expr-case x
    :vl-index
    (b* (((when (or x.indices
                    (not (vl-partselect-case x.part :none))))
          ;; something like foo[3] or foo[3:0] is not a plain parameter
          nil)
         ((mv err trace ?context tail) (vl-follow-scopeexpr x.scope ss))
         ((when err)
          ;; don't know what it is, don't assume it's a plain parameter
          nil)
         ((when (vl-hidexpr-case tail :dot))
          ;; reference into a structure or something, not a plain parameter
          nil)
         (item (vl-hidstep->item (car trace)))
         ((when (mbe :logic (vl-paramdecl-p item)
                     :exec (eq (tag item) :vl-paramdecl)))
          (b* (((vl-paramdecl item)))
            (vl-paramtype-case item.type
              :vl-implicitvalueparam t
              :vl-typeparam nil
              :vl-explicitvalueparam
              (and (vl-datatype-resolved-p item.type.type)
                   (b* (((mv err size) (vl-datatype-size item.type.type)))
                     (and (not err)
                          (equal size 32)))))))
         ((when (mbe :logic (vl-vardecl-p item)
                     :exec (eq (tag item) :vl-vardecl)))
          (b* (((vl-vardecl item)))
            (vl-datatype-case item.type
              :vl-coretype (member item.type.name '(:vl-int :vl-integer))
              :otherwise nil))))
      nil)
    :otherwise nil))

;; (b* (((mv err opinfo) (vl-index-expr-typetrace x1 ss scopes))
;;                      ((when err) nil)
;;                      ((vl-operandinfo opinfo)))
;;                   (vl-datatype-case opinfo.type
;;                     :vl-coretype (or (and (atom opinfo.type.pdims)
;;                                           (atom opinfo.type.udims)
;;                                           (or (vl-coretypename-equiv opinfo.type.name :vl-int)
;;                                               (vl-coretypename-equiv opinfo.type.name :vl-integer)))
;;                                      (and (eql (len opinfo.type.pdims) 1)
;;                                           (vl-coretypename-equiv opinfo.type.name :vl-logic)
;;                                           (eql 
;;                     :vl-enum (vl-datatype-case opinfo.type.basetype
;;                                :vl-coretype (and (atom opinfo.type.basetype.pdims)
;;                                                  (atom opinfo.type.basetype.udims)
;;                                                  (or (vl-coretypename-equiv opinfo.type.basetype.name :vl-int)
;;                                                      (vl-coretypename-equiv opinfo.type.basetype.name :vl-integer)))
;;                                :otherwise nil)
;;                     :otherwise nil))

(define vl-is-integer-valued-syscall ((x vl-expr-p))
  :guard (vl-expr-case x :vl-call)
  ;; Many system functions (e.g., $countones, $clog2, $test$plusargs) return
  ;; integers.  Treating these as 32 bits would make very little sense.  So,
  ;; treat any integer-valued system functions as if they were unsized atoms.
  (b* (((vl-call x)))
    (and x.systemp
         (b* ((info (vl-syscall->returninfo x))
              ((unless info)
               nil)
              ((vl-coredatatype-info info)))
           (or (vl-coretypename-equiv info.coretypename :vl-integer)
               (vl-coretypename-equiv info.coretypename :vl-int))))))

(define vl-is-unsized-int ((x vl-expr-p)
                           (ss vl-scopestack-p)
                           (scopes vl-elabscopes-p))
  (declare (ignore scopes)) ;; bozo should be using scopes in vl-unsized-parameter-index-p
  (b* ((x1 (vl-expr-fix x)))
    (vl-expr-case x1
      :vl-literal (vl-value-case x1.val
                    :vl-constint x1.val.wasunsized
                    :otherwise
                    ;; Note.  We treat these differently here (for fussy
                    ;; warnings) than in vl-unsized-atom-p (for truncation
                    ;; warnings).  The rationale is that if we are truncating
                    ;; something like 'bx (which is 32 bits of Xes) then that
                    ;; is OK -- the user is going to get the desired number of
                    ;; Xes.  However, for fussy warnings, if we are doing
                    ;; something like (a[3:0] == 'bx) then this is almost
                    ;; surely an error, because a[3:0] gets zero extended
                    ;; and these will not match with the Xes.
                    nil)
      :vl-index (vl-unsized-index-p x ss)
      :vl-call  (vl-is-integer-valued-syscall x)
      :otherwise nil)))

(define vl-collect-unsized-ints
  ((x vl-exprlist-p)
   (ss       vl-scopestack-p  "Scope where the expression occurs.")
   (scopes   vl-elabscopes-p "Precomputed overrides for parameter and function types"))
  :parents (vl-tweak-fussy-warning-type)
  :returns (sub-x vl-exprlist-p)
  (b* (((when (atom x))
        nil)
       (x1 (vl-expr-fix (car x)))
       (keep (vl-is-unsized-int x1 ss scopes)))
    (if keep
        (cons x1 (vl-collect-unsized-ints (cdr x) ss scopes))
      (vl-collect-unsized-ints (cdr x) ss scopes))))

(define vl-collect-resolved-exprs ((x vl-exprlist-p))
  :parents (vl-tweak-fussy-warning-type)
  :returns (sub-x vl-exprlist-p)
  (if (atom x)
      nil
    (if (vl-expr-resolved-p (car x))
        (cons (vl-expr-fix (car x))
              (vl-collect-resolved-exprs (cdr x)))
      (vl-collect-resolved-exprs (cdr x))))
  ///
  (defret vl-exprlist-resolved-p-of-vl-collect-resolved-exprs
    (vl-exprlist-resolved-p sub-x)
    :hints(("Goal" :in-theory (enable vl-expr-resolved-p)))))


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
  (vl-expr-case x
    :vl-literal (vl-value-case x.val :vl-extint)
    :otherwise nil))

(define ints-probably-fit-p ((size natp)
                             (consts integer-listp))
  (if (atom consts)
      t
    (and (b* ((size (lnfix size)))
           (or (unsigned-byte-p size (lifix (car consts)))
               (and (< 0 size)
                    (signed-byte-p size (lifix (car consts))))))
         (ints-probably-fit-p size (cdr consts)))))


(define logrepeat ((times natp)
                   (width natp)
                   (data integerp))
  ;; BOZO move to bitops/ihs?
  :returns (ans integerp :rule-classes :type-prescription)
  (if (zp times)
      0
    (acl2::logapp width data
                  (logrepeat (1- times) width data)))
  ///
  (local (include-book "centaur/bitops/ihsext-basics" :dir :system))
  (local (include-book "centaur/bitops/signed-byte-p" :dir :system))
  (local (include-book "centaur/bitops/signed-byte-p" :dir :system))
  (defthm natp-of-logrepeat
    (implies (natp data)
             (natp (logrepeat times width data)))
    :rule-classes :type-prescription)
  (defthm unsigned-byte-p-of-logrepeat
    (implies (and (natp times)
                  (natp width)
                  (natp data))
             (unsigned-byte-p (* times width) (logrepeat times width data)))
    :hints(("Goal"
            :in-theory (disable unsigned-byte-p)
            :induct (logrepeat times width data)))))


(define vl-tweak-fussy-warning-type-preclean ((x vl-expr-p))
  :parents (vl-tweak-fussy-warning-type)
  :short "Preliminary, minor heuristic cleanups for the arguments to a fussy size warning."
  :returns (new-x vl-expr-p)
  (let ((x (vl-expr-fix x)))
    (vl-expr-case x
      :vl-concat
      ;; This is meant to clean up things like ``foo ? {bar} : baz`` to just
      ;; ``foo ? bar : baz``.  This isn't sound in general because it would
      ;; affect signedness, but should be fine for fussy size warnings where
      ;; we're only concerned about the width.
      (if (equal (len x.parts) 1)
          (first x.parts)
        x)
      :vl-multiconcat
      ;; Simplify things like {4{1'b1}} into 4'b1111.  This style is sometimes
      ;; used in parameterized code.
      (b* (((unless (and (vl-expr-resolved-p x.reps)
                         (posp (vl-resolved->val x.reps))
                         (equal (len x.parts) 1)))
            x)
           (reps  (vl-resolved->val x.reps))
           (inner (first x.parts))
           ((unless (vl-expr-case inner :vl-literal))
            x)
           (value (vl-literal->val inner)))
        (vl-value-case value
          :vl-constint
          (b* ((new-value (change-vl-constint value
                                              :origwidth (* value.origwidth reps)
                                              :value (logrepeat reps value.origwidth value.value))))
            (make-vl-literal :val new-value))
          :otherwise
          ;; Something weird, don't simplify it
          x))
      :otherwise
      x)))

(define vl-tweak-fussy-warning-expr-size ((a     vl-expr-p)
                                          (asize natp))
  :returns (mv (new-a     vl-expr-p)
               (new-asize natp :rule-classes :type-prescription))
  (b* ((a     (vl-expr-fix a))
       (asize (lnfix asize)))
    (vl-expr-case a
      :vl-binary
      (cond
       ((and (vl-binaryop-equiv a.op :vl-binary-shr)
             (vl-expr-resolved-p a.right))
        ;; Right shifts are trouble for fussy size warnings.  When a user
        ;; writes something like foo >> 3 where foo is 5 bits, the Verilog
        ;; self-sizing rules say the result of the shift is also 5 bits, even
        ;; though only the low 2 bits can be nonzero.  It's particularly
        ;; unhelpful to be shown warnings about mismatches between this
        ;; "padded" size and other expressions, e.g., ((foo >> 3) & 2'b10) is a
        ;; perfectly reasonable thing to write.
        ;;
        ;; To try to reduce this, if we see a shift by a resolved amount like
        ;; this, then as a preliminary step we will artificially treat it as if
        ;; it has a self size of 2 bits, instead of 5.
        (let ((shift-amount (vl-resolved->val a.right)))
          (if (< shift-amount asize)
              (mv a
                  (- asize shift-amount))
            ;; BOZO it might be good to separately warn about constant shift
            ;; amounts that are so large they will wipe out all the bits.  For
            ;; fussy warnings, we'll just reduce these to zeroes.
            (mv (make-vl-literal :val
                                 (make-vl-constint :value 0
                                                   :origwidth 1
                                                   :origsign :vl-unsigned))
                1))))
       (t
        (mv a asize)))
      :otherwise
      (mv a asize))))

(define vl-tweak-fussy-warning-type-arithop ((x vl-binaryop-p))
  :parents (vl-tweak-fussy-warning-type)
  (or (vl-binaryop-equiv x :vl-binary-plus)
      (vl-binaryop-equiv x :vl-binary-minus)
      (vl-binaryop-equiv x :vl-binary-times)
      (vl-binaryop-equiv x :vl-binary-shl)
      (vl-binaryop-equiv x :vl-binary-ashl)))

(define vl-fussy-may-as-well-be-extint-p ((x vl-expr-p))
  ;; Is X something like '0, '1, {'0,...}, etc.
  :measure (vl-expr-count x)
  (or (vl-expr-extint-p x)
      (vl-expr-case x
        :vl-concat
        (and (consp x.parts)
             (vl-fussy-may-as-well-be-extint-p (car x.parts)))
        :vl-qmark
        (and (vl-fussy-may-as-well-be-extint-p x.then)
             (vl-fussy-may-as-well-be-extint-p x.else))
        :otherwise nil)))

(define vl-suppress-fussy-warning-for-shift-of-mask ((op symbolp)
                                                     (a vl-expr-p)
                                                     (b vl-expr-p))
  :returns (suppress booleanp)
  ;; For now, just never ever warn about cases like "(a >> 3) & mask", because
  ;; it's hard to have any idea what the intent is.  Maybe some day tweak this
  ;; and warn if there are particular cases of this that seem troublesome, but
  ;; it seems difficult to infer the intent here.
  (and (eq (acl2::symbol-fix op) :vl-binary-bitand)
       (or (vl-expr-case a
             :vl-binary (vl-binaryop-equiv a.op :vl-binary-shr)
             :otherwise nil)
           (vl-expr-case b
             :vl-binary (vl-binaryop-equiv b.op :vl-binary-shr)
             :otherwise nil))))

(define vl-tweak-fussy-warning-type
  :parents (vl-expr-selfsize)
  :short "Heuristically categorize fussy warnings according to severity."
  ((type  symbolp   "Base warning type, which we may adjust.")
   (a     vl-expr-p "LHS expression, i.e., A in: A + B, or C ? A : B")
   (b     vl-expr-p "RHS expression, i.e., B in: A + B, or C ? A : B")
   (asize natp      "Self-determined size of A.")
   (bsize natp      "Self-determined size of B.")
   (op    symbolp   "The particular operation.")
   (ss       vl-scopestack-p  "Scope where the expression occurs.")
   (scopes   vl-elabscopes-p "Precomputed overrides for parameter and function types"))
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
       (op    (acl2::symbol-fix op))
       (asize (lnfix asize))
       (bsize (lnfix bsize))
       (ss (vl-scopestack-fix ss))
       (scopes (vl-elabscopes-fix scopes))

       ;; Note that throughout this function, you can freely rewrite A and B in
       ;; any crazy, unsound, heuristic way you please.  Also this function is
       ;; called infrequently (only when we have noticed a problem) so you
       ;; should not be very concerned with efficiency here.
       (a            (vl-tweak-fussy-warning-type-preclean a))
       (b            (vl-tweak-fussy-warning-type-preclean b))
       ((mv a asize) (vl-tweak-fussy-warning-expr-size a asize))
       ((mv b bsize) (vl-tweak-fussy-warning-expr-size b bsize))
       ((when (equal asize bsize))
        ;; After adjusting sizes, it looks like there is no problem, so do
        ;; not issue a warning.
        nil)

       (a-zerop (and (vl-expr-resolved-p a)
                     (eql (vl-resolved->val a) 0)))
       (b-zerop (and (vl-expr-resolved-p b)
                     (eql (vl-resolved->val b) 0)))
       ((when (or a-zerop b-zerop))
        ;; Zeros are very special.  It's very annoying to look at warnings
        ;; telling you that your zeroes aren't the right size.  So, even in
        ;; bitwisey contexts, suppress any warnings about zeroes.
        nil)

       ((when (or (vl-fussy-may-as-well-be-extint-p a)
                  (vl-fussy-may-as-well-be-extint-p b)))
        ;; Suppress warnings because '0, '1, etc., are supposed to grow to the
        ;; size of whatever is around them.
        nil)

       ((when (vl-suppress-fussy-warning-for-shift-of-mask op a b))
        ;; Suppress warnings about (a >> b) & mask, since they are annoying
        ;; to look through and difficult to warn about sensibly
        nil)

       (a-fits-b-p (and (vl-expr-resolved-p a)
                        (or (unsigned-byte-p bsize (vl-resolved->val a))
                            (and (< 0 bsize) (signed-byte-p bsize (vl-resolved->val a))))))
       (b-fits-a-p (and (vl-expr-resolved-p b)
                        (or (unsigned-byte-p asize (vl-resolved->val b))
                            (and (< 0 asize)
                                 (signed-byte-p asize (vl-resolved->val b))))))
       ((when (and (or a-fits-b-p b-fits-a-p)
                   (member op '(:vl-binary-eq :vl-binary-neq
                                :vl-binary-ceq :vl-binary-cne
                                :vl-binary-lt :vl-binary-lte
                                :vl-binary-gt :vl-binary-gte))))
        ;; Suppress warnings about things like "foo == 3'd7" or "foo == 7"
        ;; where foo is, say, a 5 bit wire.  We know that the value of the 7
        ;; fits into the width of foo, so this isn't really wrong.
        nil)

       ;; If the lesser-sized argument is an arithmetic operator like +, -, or
       ;; *, it's probably intended that the size of that plus be increased to
       ;; accomodate carry-outs.  We could refine this by checking whether the
       ;; maximum possible value of the sum requires the greater number of
       ;; bits, but for now we'll make it a minor warning anyway.
       (a-plusp (vl-expr-case a
                  :vl-binary (vl-tweak-fussy-warning-type-arithop a.op)
                  :otherwise nil))
       (b-plusp (vl-expr-case b
                  :vl-binary (vl-tweak-fussy-warning-type-arithop b.op)
                  :otherwise nil))
       ;; Change the type to return if unmodified by the tests below.
       (ret-type (if (if (< asize bsize) a-plusp b-plusp)
                     (intern-in-package-of-symbol (cat (symbol-name type) "-MINOR") type)
                   type))

       (a32p (eql asize 32))
       (b32p (eql bsize 32))
       ((unless (or a32p b32p))
        ;; Neither op is 32 bits, so this doesn't seem like it's related to
        ;; unsized numbers, go ahead and warn.
        ret-type)

       ;; Figure out which one is 32-bit and which one is not.  We assume
       ;; they aren't both 32 bits, since otherwise we shouldn't be called.
       ((mv expr-32 size-other) (if a32p (mv a bsize) (mv b asize)))

       ;; Collect up interesting unsized ints in the 32-bit expression.  If it
       ;; has unsized ints, they're probably the reason it's 32 bits.  After
       ;; collecting them, see if they fit into the size of the other expr.
       (atoms         (vl-expr-interesting-size-atoms expr-32))
       (unsized       (vl-collect-unsized-ints atoms ss scopes))
       (unsized-vals  (vl-exprlist-resolved->vals (vl-collect-resolved-exprs unsized)))
       (unsized-fit-p (ints-probably-fit-p size-other unsized-vals))

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
        (intern-in-package-of-symbol (cat (symbol-name type) "-MINOR-INTSIZE") type)))

    ;; Otherwise, we didn't find any unsized atoms, so just go ahead and do the
    ;; warning.
    ret-type))


(define vl-binary->original-operator ((x vl-expr-p))
  :guard (vl-expr-case x :vl-binary)
  :parents (vl-binaryop-selfsize)
  :short "Get the original operator from a binary expression."
  :returns (op vl-binaryop-p)
  (b* (((vl-binary x))
       (orig (cdr (hons-assoc-equal "VL_ORIG_EXPR" x.atts))))
    (if orig
        (vl-expr-case orig
          :vl-binary orig.op
          :otherwise x.op)
      x.op)))


(define vl-binaryop-selfsize
  :parents (vl-expr-selfsize)
  :short "Main function for computing self-determined expression sizes."
  ((x         vl-expr-p)
   (left-size  maybe-natp)
   (right-size maybe-natp)
   (ss       vl-scopestack-p  "Scope where the expression occurs.")
   (scopes   vl-elabscopes-p "Precomputed overrides for parameter and function types"))
  :guard
  (vl-expr-case x :vl-binary)
  :returns
  (mv (warnings vl-warninglist-p)
      (size     maybe-natp :rule-classes :type-prescription))
  :verify-guards nil

  :long "<p>We attempt to determine the size of the binary operator expression.
We assume that each argument has already had its self-size computed
successfully and that the results of these computations are given as the
@('arg-sizes').</p>

<p>This function basically implements Verilog-2005 Table 5-22, or
SystemVerilog-2012 Table 11-21.</p>"
  :prepwork ((local (in-theory (disable acl2::member-of-cons))))


  (b* (((vl-binary x) (vl-expr-fix x))
       (warnings nil)
       (left-size (maybe-natp-fix left-size))
       (right-size (maybe-natp-fix right-size)))
    (case x.op
      (( ;; All of these operations have one-bit results, and we have no
        ;; expectations that their argument sizes should agree or anything like
        ;; that.
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
       (b* (((unless (and left-size right-size))
             ;; [Jared]: historically we returned NIL here as the size.
             ;; However, I found that this sometimes caused problems in lint
             ;; checks like oddexpr, where even if we have trouble figuring out
             ;; the size of some subexpression, we should still be able to know
             ;; that a comparison always produces a single-bit answer.  I think
             ;; it should be OK to return 1 here.  Otherwise, why would it be OK
             ;; to return 1 above, for things like :vl-binary-logand, without
             ;; checking their argument sizes?
             (mv (ok) 1))
            (type (and (/= left-size right-size)
                       (vl-tweak-fussy-warning-type :vl-fussy-size-warning-1
                                                    x.left
                                                    x.right
                                                    left-size
                                                    right-size
                                                    x.op ss scopes)))
            (warnings
             (if (not type)
                 (ok)
               (warn :type type
                     :msg "arguments to a ~s0 comparison operator have ~
                             different \"self-sizes\".  The smaller argument ~
                             will be implicitly widened to match the larger ~
                             argument. Arguments:~%     ~
                               - lhs (width ~x1): ~a3~%     ~
                               - rhs (width ~x2): ~a4~%"
                     :args (list
                                 (vl-binaryop-string (vl-binary->original-operator x))
                                 left-size right-size x.left x.right)))))
         (mv (ok) 1)))

      ((:vl-binary-power
        :vl-binary-shl :vl-binary-shr :vl-binary-ashl :vl-binary-ashr)
       ;; All of these operations keep the size of their first operands.
       (mv (ok) left-size))

      ((:vl-binary-plus :vl-binary-minus :vl-binary-times :vl-binary-div :vl-binary-rem)
       ;; All of these operations take the max size of either operand.
       ;; Practically speaking we will probably never see times, div, or rem
       ;; operators.  However, plus and minus are common.  We probably do not
       ;; want to issue any size warnings in the case of plus or minus, since
       ;; one argument or the other often needs to be expanded.
       (mv (ok) (and left-size right-size
                     (max left-size
                          right-size))))

      ((:vl-binary-bitand :vl-binary-bitor :vl-binary-xor :vl-binary-xnor)
       ;; All of these operations take the max size of either operand.  But
       ;; this is a place where implicit widening could be bad.  I mean, you
       ;; probably don't want to be doing A & B when A and B are different
       ;; sizes, right?
       (b* (((unless (and left-size right-size))
             (mv (ok) nil))
            (max (max left-size
                      right-size))
            (type (and (/= left-size right-size)
                       (vl-tweak-fussy-warning-type :vl-fussy-size-warning-2
                                                    x.left
                                                    x.right
                                                    left-size
                                                    right-size
                                                    x.op ss scopes)))
            (warnings
             (if (not type)
                 (ok)
               (warn :type type
                     :msg "arguments to a bitwise ~s0 operator have ~
                             different \"self-sizes\".  The smaller argument ~
                             will be implicitly widened to match the larger ~
                             argument. Arguments:~%     ~
                               - lhs (width ~x1): ~a3~%     ~
                               - rhs (width ~x2): ~a4~%"
                     :args (list
                                 (vl-binaryop-string (vl-binary->original-operator x))
                                 left-size
                                 right-size
                                 x.left
                                 x.right
                                 x)))))
         (mv (ok) max)))

      ((;; We shouldn't encounter these in sizing, they should be gotten
        ;; rid of in increment-elim
        :vl-binary-assign
        :vl-binary-plusassign :vl-binary-minusassign
        :vl-binary-timesassign :vl-binary-divassign :vl-binary-remassign
        :vl-binary-andassign :vl-binary-orassign :vl-binary-xorassign
        :vl-binary-shlassign :vl-binary-shrassign :vl-binary-ashlassign :vl-binary-ashrassign
        )

       (mv (fatal :type :vl-programming-error
                  :msg "vl-binaryop-selfsize should not encounter ~a0"
                  :args (list x))
           nil))

      (otherwise
       (progn$ (impossible)
               (mv (ok) nil)))))
  ///
  ;; (defrule warning-irrelevance-of-vl-binaryop-selfsize
  ;;   (let ((ret1 (vl-binaryop-selfsize x left-size right-size ctx warnings))
  ;;         (ret2 (vl-binaryop-selfsize x left-size right-size nil nil)))
  ;;     (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
  ;;              (equal (mv-nth 1 ret1) (mv-nth 1 ret2)))))

  ;; (local (defun make-vl-op-p-cases (ops)
  ;;          (if (atom ops)
  ;;              nil
  ;;            (cons `(equal op ,(car ops))
  ;;                  (make-vl-op-p-cases (cdr ops))))))

  ;; (local (make-event
  ;;         `(defthm vl-op-p-forward
  ;;            (implies (vl-op-p op)
  ;;                     (or . ,(make-vl-op-p-cases (strip-cars (vl-ops-table)))))
  ;;            :rule-classes :forward-chaining
  ;;            :hints(("Goal" :in-theory (enable hons-assoc-equal
  ;;                                              vl-op-p
  ;;                                              (vl-ops-table)))))))

  ;; (local (defthm natp-of-first-when-nat-listp
  ;;          (implies (nat-listp x)
  ;;                   (equal (natp (car x))
  ;;                          (<= 1 (len x))))))

  ;; (local (defthm natp-of-second-when-nat-listp
  ;;          (implies (nat-listp x)
  ;;                   (equal (natp (second x))
  ;;                          (<= 2 (len x))))))

  ;; (local (defthm natp-of-third-when-nat-listp
  ;;          (implies (nat-listp x)
  ;;                   (equal (natp (third x))
  ;;                          (<= 3 (len x))))
  ;;          :hints(("Goal" :expand ((nat-listp x)
  ;;                                  (nat-listp (cdr x))
  ;;                                  (nat-listp (cddr x)))))))

  ;; (local (defthm natp-of-abs
  ;;          (implies (integerp x)
  ;;                   (natp (abs x)))
  ;;          :rule-classes :type-prescription))

  (local (defthm vl-binary->op-forward
           (vl-binaryop-p (vl-binary->op x))
           :rule-classes ((:forward-chaining :trigger-terms ((vl-binary->op x))))))

  ;; (local (defthm member-cons-forward
  ;;          (implies (not (member x (cons a b)))
  ;;                   (and (not (equal x a))
  ;;                        (not (member x b))))
  ;;          :hints(("Goal" :in-theory (enable acl2::member-of-cons)))
  ;;          :rule-classes ((:forward-chaining :trigger-terms ((member x (cons a b)))))))

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
    (verify-guards vl-binaryop-selfsize
      :hints(("Goal"
              :do-not '(generalize fertilize eliminate-destructors)
              :do-not-induct t)
             (and stable-under-simplificationp
                  '(:in-theory (enable acl2::member-of-cons)))))))

(define vl-exprlist-has-extensional-const ((x vl-exprlist-p))
  (if (atom x)
      nil
    (or (b* ((x1 (car x)))
          (vl-expr-case x1
            :vl-literal (vl-value-case x1.val :vl-extint x1.val.value :otherwise nil)
            :otherwise nil))
        (vl-exprlist-has-extensional-const (cdr x)))))


(define vl-extensional-const-in-concat-check ((orig vl-expr-p)
                                              (x vl-exprlist-p))
  :returns (warnings vl-warninglist-p)
  (b* ((constval (vl-exprlist-has-extensional-const (and (consp x) (cdr x))))
       (warnings nil))
    (and constval
         (warn :type :vl-concat-with-extensional-integer
               :msg "The following concatenation contains the extensional ~
                     integer ~s0, which is not allowed except as the most ~
                     significant element of the concatenation: ~a1"
               :args (list (case constval
                             (:vl-0val "'0")
                             (:vl-1val "'1")
                             (:vl-zval "'z")
                             (otherwise "'x"))
                           (vl-expr-fix orig))))))
  


(define vl-unaryop-selfsize
  :parents (vl-expr-selfsize)
  :short "Main function for computing self-determined expression sizes."
  ((x         vl-expr-p)
   (arg-size  maybe-natp))
  :guard
  (vl-expr-case x :vl-unary)
  :returns
  (mv (warnings vl-warninglist-p)
      (size     maybe-natp :rule-classes :type-prescription))
  :verify-guards nil

  :long "<p>We attempt to determine the size of the unary operator expression.
We assume that each argument has already had its self-size computed
successfully and that the results of these computations are given as the
@('arg-sizes').</p>

<p>This function basically implements Verilog-2005 Table 5-22, or
SystemVerilog-2012 Table 11-21.</p>"
  :prepwork ((local (in-theory (disable acl2::member-of-cons))))

  (b* (((vl-unary x) (vl-expr-fix x))
       (arg-size (maybe-natp-fix arg-size))
       (warnings nil))
    (case x.op
      (( ;; All of these operations have one-bit results.
        :vl-unary-bitand :vl-unary-nand :vl-unary-bitor :vl-unary-nor
        :vl-unary-xor :vl-unary-xnor :vl-unary-lognot)
       (mv (ok) 1))

      ((:vl-unary-plus :vl-unary-minus :vl-unary-bitnot)
       ;; All of these operations keep the size of their first operands.
       (mv (ok) arg-size))

      ((;; We shouldn't encounter these in sizing, they should be gotten
        ;; rid of in increment-elim
        :vl-unary-preinc :vl-unary-predec :vl-unary-postinc :vl-unary-postdec)

       (mv (fatal :type :vl-programming-error
                  :msg "vl-op-selfsize should not encounter ~a0"
                  :args (list x))
           nil))

      (otherwise
       (progn$ (impossible)
               (mv (ok) nil)))))
  ///

  ;; (local (defun make-vl-op-p-cases (ops)
  ;;          (if (atom ops)
  ;;              nil
  ;;            (cons `(equal op ,(car ops))
  ;;                  (make-vl-op-p-cases (cdr ops))))))

  ;; (local (make-event
  ;;         `(defthm vl-op-p-forward
  ;;            (implies (vl-op-p op)
  ;;                     (or . ,(make-vl-op-p-cases (strip-cars (vl-ops-table)))))
  ;;            :rule-classes :forward-chaining
  ;;            :hints(("Goal" :in-theory (enable hons-assoc-equal
  ;;                                              vl-op-p
  ;;                                              (vl-ops-table)))))))

  ;; (local (defthm natp-of-first-when-nat-listp
  ;;          (implies (nat-listp x)
  ;;                   (equal (natp (car x))
  ;;                          (<= 1 (len x))))))

  ;; (local (defthm natp-of-second-when-nat-listp
  ;;          (implies (nat-listp x)
  ;;                   (equal (natp (second x))
  ;;                          (<= 2 (len x))))))

  ;; (local (defthm natp-of-third-when-nat-listp
  ;;          (implies (nat-listp x)
  ;;                   (equal (natp (third x))
  ;;                          (<= 3 (len x))))
  ;;          :hints(("Goal" :expand ((nat-listp x)
  ;;                                  (nat-listp (cdr x))
  ;;                                  (nat-listp (cddr x)))))))

  ;; (local (defthm natp-of-abs
  ;;          (implies (integerp x)
  ;;                   (natp (abs x)))
  ;;          :rule-classes :type-prescription))

  (local (defthm vl-unary->op-forward
           (vl-unaryop-p (vl-unary->op x))
           :rule-classes ((:forward-chaining :trigger-terms ((vl-unary->op x))))))

  ;; (local (defthm member-cons-forward
  ;;          (implies (not (member x (cons a b)))
  ;;                   (and (not (equal x a))
  ;;                        (not (member x b))))
  ;;          :hints(("Goal" :in-theory (enable acl2::member-of-cons)))
  ;;          :rule-classes ((:forward-chaining :trigger-terms ((member x (cons a b)))))))

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
    (verify-guards vl-unaryop-selfsize
      :hints(("Goal"
              :do-not '(generalize fertilize eliminate-destructors)
              :do-not-induct t)
             (and stable-under-simplificationp
                  '(:in-theory (enable acl2::member-of-cons)))))))



(define vl-funcall-selfsize ((x vl-expr-p)
                             (ss vl-scopestack-p)
                             (scopes vl-elabscopes-p))
  :guard (vl-expr-case x :vl-call (not x.systemp) :otherwise nil)
  :returns (mv (warnings vl-warninglist-p)
               (size maybe-natp :rule-classes :type-prescription))
  (b* (((vl-call x) (vl-expr-fix x))
       (warnings nil)
       ((mv err trace ?context ?tail)
        (vl-follow-scopeexpr x.name ss))
       ((when err)
        (mv (fatal :type :vl-selfsize-fail
                   :msg "Failed to find function ~a0: ~@1"
                   :args (list (vl-scopeexpr->expr x.name) err))
            nil))
       ((vl-hidstep lookup) (car trace))
       ((unless (eq (tag lookup.item) :vl-fundecl))
        (mv (fatal :type :vl-selfsize-fail
                   :msg "In function call ~a0, function name does not ~
                        refer to a fundecl but instead ~a1"
                   :args (list x lookup.item))
            nil))
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
            nil))
       ((vl-fundecl item))
       ((mv err rettype)
        (vl-datatype-usertype-resolve item.rettype lookup.ss))
       ((when err)
        (mv (fatal :type :vl-selfsize-fail
                   :msg "Couldn't resolve return type ~a0 of function ~a1: ~@2"
                   :args (list item.rettype
                               (vl-scopeexpr->expr x.name)
                               err))
            nil))
       ((mv warning size)
        (vl-datatype-size rettype))
       ((when warning)
        (mv (fatal :type :vl-selfsize-fail
                   :msg "Error computing the size of type ~a0 of function ~a1: ~@2"
                   :args (list rettype
                               (vl-scopeexpr->expr x.name) err))
            nil))
       ((unless (vl-datatype-packedp rettype))
        (mv (ok) nil)))
    (mv (ok) size)))

(define vl-syscall-selfsize ((x        vl-expr-p))
  :guard (vl-expr-case x :vl-call x.systemp :otherwise nil)
  :returns (mv (warnings vl-warninglist-p)
               (size maybe-posp :rule-classes :type-prescription))
  (b* ((retinfo (vl-syscall->returninfo x))
       (warnings nil)
       ((unless retinfo)
        (mv (ok) nil))
       (size (vl-coredatatype-info->size retinfo)))
    (mv (ok) size)))

(local (defthm cdr-of-vl-exprlist-fix
         (equal (cdr (vl-exprlist-fix x))
                (vl-exprlist-fix (cdr x)))
         :hints(("Goal" :in-theory (enable vl-exprlist-fix)))))

(local (defthm car-of-vl-exprlist-fix
         (implies (consp x)
                  (equal (car (vl-exprlist-fix x))
                         (vl-expr-fix (car x))))
         :hints(("Goal" :in-theory (enable vl-exprlist-fix)))))

#||
(trace$ #!vl (vl-expr-selfsize
              :entry (list 'vl-expr-selfsize
                           (with-local-ps (vl-pp-expr x))
                           (vl-scopestack->hashkey ss)
                           (strip-cars scopes))
              :exit (b* (((list ?warnings ?size) values))
                      (list 'vl-expr-selfsize
                            (with-local-ps (vl-print-warnings warnings))
                            size))))

||#

(defines vl-expr-selfsize
  :parents (expr-tools)
  :short "Computation of self-determined expression sizes."

  :long "<p>Some failures are expected, e.g., we do not know how to size some
system calls.  In these cases we do not cause any warnings.  But in other
cases, a failure might mean that the expression is malformed in some way, e.g.,
maybe it references an undefined wire or contains a raw, \"unindexed\"
reference to an array.  In these cases we generate fatal warnings.</p>"

  (define vl-expr-selfsize
    ((x        vl-expr-p        "Expression whose size we are to compute.")
     (ss       vl-scopestack-p  "Scope where the expression occurs.")
     (scopes   vl-elabscopes-p "Precomputed overrides for parameter and function types"))
    :returns
    (mv (warnings vl-warninglist-p)
        (size     maybe-natp :rule-classes :type-prescription))
    :verify-guards nil
    :measure (vl-expr-count x)
    :flag :expr
    (b* ((x (vl-expr-fix x))
         (warnings nil))
      (vl-expr-case x
        :vl-special (mv (ok) nil)
        :vl-literal (mv (ok) (vl-value-selfsize x.val))
        :vl-index (vl-index-selfsize x ss scopes)

        ;; BOZO In some cases we could deduce a size for the expression even if
        ;; we can't get the size of an operand -- e.g. unary bitand, etc.  Are we
        ;; type-checking or just trying to get the size?
        :vl-unary (b* (((mv warnings argsize) (vl-expr-selfsize x.arg ss scopes))
                       ((wmv warnings ans) (vl-unaryop-selfsize x argsize)))
                    (mv warnings ans))

        :vl-binary (b* (((wmv warnings leftsize) (vl-expr-selfsize x.left ss scopes))
                        ((wmv warnings rightsize) (vl-expr-selfsize x.right ss scopes))
                        ((wmv warnings ans) (vl-binaryop-selfsize x leftsize
                                                                  rightsize
                                                                  ss scopes)))
                     (mv warnings ans))

        ;; Note: We used to fail if we couldn't size the test.  Should we?
        :vl-qmark (b* (((wmv warnings thensize) (vl-expr-selfsize x.then ss scopes))
                       ((wmv warnings elsesize) (vl-expr-selfsize x.else ss scopes))
                       ((unless (and thensize elsesize))
                        (mv (ok) nil))
                       (warningtype (and (/= thensize elsesize)
                                         (vl-tweak-fussy-warning-type
                                          :vl-fussy-size-warning-3
                                          x.then x.else thensize elsesize :vl-qmark ss scopes)))
                       (warnings
                        (if warningtype
                            (warn :type warningtype
                                  :msg "branches of a ?: operator have different ~
                                       \"self-sizes\".  The smaller branch will be ~
                                       implicitly widened to match the larger branch. ~
                                       Arguments:~%     ~

                                         - Condition:               ~a0~%     ~
                                         - True Branch  (size ~x1): ~a3~%     ~
                                         - False Branch (size ~x2): ~a4~%"
                                  :args (list
                                              x.test
                                              thensize
                                              elsesize
                                              x.then
                                              x.else))
                          (ok))))
                    (mv (ok) (max thensize elsesize)))

        :vl-mintypmax (mv (ok) nil)

        :vl-concat (b* (((mv warnings part-sizes) (vl-exprlist-selfsize x.parts ss scopes))
                        ((wmv warnings) (vl-extensional-const-in-concat-check x x.parts))
                        ((when (member nil part-sizes))
                         (mv warnings nil)))
                     (mv warnings (sum-nats part-sizes)))

        :vl-multiconcat (b* (((unless (vl-expr-resolved-p x.reps))
                              (mv (fatal :type :vl-unresolved-multiplicity
                                         :msg "cannot size ~a0 because its ~
                                             multiplicity has not been ~
                                             resolved."
                                         :args (list x))
                                  nil))
                             (reps (vl-resolved->val x.reps))
                             ((unless (<= 0 reps))
                              (mv (fatal :type :vl-unresolved-multiplicity
                                         :msg "cannot size ~a0 because its ~
                                             multiplicity is negative."
                                         :args (list x))
                                  nil))
                             ((mv warnings part-sizes)
                              (vl-exprlist-selfsize x.parts ss scopes))
                             ((wmv warnings) (vl-extensional-const-in-concat-check x x.parts))
                             ((when (member nil part-sizes))
                              (mv warnings nil)))
                          (mv (ok) (* reps (sum-nats part-sizes))))

        ;; Streaming concatenations need to be treated specially.  They sort of
        ;; have a self-size -- the number of bits available -- but can't be
        ;; used as an operand without casting or assignment context.  Then, if
        ;; the size of the casted type / assignment target is too small, it's
        ;; an error, and if too big, the bits are **left**-aligned and
        ;; zero-filled on the right.  I think if we return a size here it will
        ;; be tricky to only use it where it makes sense, so we'll return nil.
        :vl-stream (mv (ok) nil)

        :vl-call (if x.systemp
                     (b* ((name (vl-simple-id-name x.name))
                          ((unless (member-equal name '("$signed" "$unsigned")))
                           (vl-syscall-selfsize x))
                          ((unless (and (consp x.plainargs)
                                        (car x.plainargs)
                                        (atom (cdr x.plainargs))
                                        (not x.typearg)
                                        (not x.namedargs)))
                           (mv (fatal :type :vl-selfsize-fail
                                      :msg "Bad arguments to system call ~a0"
                                      :args (list x))
                               nil)))
                       (vl-expr-selfsize (car x.plainargs) ss scopes))
                   (vl-funcall-selfsize x ss scopes))

        :vl-cast (vl-casttype-case x.to
                   :type (b* (((mv err to-type)
                               (vl-datatype-usertype-resolve x.to.type ss :scopes scopes))
                              ((when err)
                               (mv (fatal :type :vl-selfsize-fail
                                          :msg "Failed to resolve the type in ~
                                        cast expression ~a0: ~@1"
                                          :args (list x err))
                                   nil))
                              ((mv err size) (vl-datatype-size to-type))
                              ((when err)
                               (mv (fatal :type :vl-selfsize-fail
                                          :msg "Failed to size the type in ~
                                        cast expression ~a0: ~@1"
                                          :args (list x err))
                                   nil))
                              ((unless (vl-datatype-packedp to-type))
                               (mv (ok) nil)))
                           (mv (ok) size))
                   :size (b* (((unless (vl-expr-resolved-p x.to.size))
                               (mv (fatal :type :vl-selfsize-fail
                                          :msg "Unresolved size in cast expression ~a0"
                                          :args (list x))
                                   nil))
                              (size (vl-resolved->val x.to.size))
                              ((unless (<= 0 size))
                               (mv (fatal :type :vl-selfsize-fail
                                          :msg "Negative size in cast expression ~a0"
                                          :args (list x))
                                   nil)))
                           (mv (ok) size))
                   :otherwise (vl-expr-selfsize x.expr ss scopes))


        ;; returns a single bit
        :vl-inside (mv (ok) 1)

        ;; these create tagged unions, which are not vector types
        :vl-tagged (mv (ok) nil)

        ;; these are special like streaming concatenations, only well typed by
        ;; context, unless they have a datatype.
        :vl-pattern (b* (((unless x.pattype) (mv (ok) nil))
                         ((mv err pattype) (vl-datatype-usertype-resolve x.pattype ss :scopes scopes))
                         ((when err)
                          (mv (fatal :type :vl-selfsize-fail
                                     :msg "Failed to resolve the type in ~
                                        pattern expression ~a0: ~@1"
                                     :args (list x err))
                              nil))
                         ((mv err size) (vl-datatype-size pattype))
                         ((when err)
                          (mv (fatal :type :vl-selfsize-fail
                                  :msg "Failed to size the type in ~
                                        pattern expression ~a0: ~@1"
                                  :args (list x err))
                           nil))
                         ((unless (vl-datatype-packedp pattype))
                          (mv (ok) nil)))
                      (mv (ok) size))

        ;; I don't think these should get a size.
        :vl-eventexpr (mv (ok) nil))))

  (define vl-exprlist-selfsize
    ((x vl-exprlist-p)
     (ss       vl-scopestack-p  "Scope where the expression occurs.")
     (scopes vl-elabscopes-p))
    :returns
    (mv (warnings vl-warninglist-p)
        (sizes     maybe-nat-list-p))
    :measure (vl-exprlist-count x)
    :flag :list
    (b* ((warnings nil)
         ((when (atom x)) (mv (ok) nil))
         ((wmv warnings first) (vl-expr-selfsize (car x) ss scopes))
         ((wmv warnings rest) (vl-exprlist-selfsize (cdr x) ss scopes)))
      (mv warnings (cons first rest))))

  ///

  (local (in-theory (disable vl-expr-selfsize
                             vl-exprlist-selfsize)))

  (local
   (defthm-vl-expr-selfsize-flag
     (defthm true-listp-of-vl-exprlist-selfsize
       (true-listp (mv-nth 1 (vl-exprlist-selfsize x ss scopes)))
       :hints ('(:expand ((vl-exprlist-selfsize x ss scopes))))
       :rule-classes :type-prescription
       :flag :list)
     :skip-others t))

  (verify-guards vl-expr-selfsize)

  (deffixequiv-mutual vl-expr-selfsize))


(defenum vl-opacity-p
  (:transparent
   :opaque
   :special))

(define vl-expr-opacity ((x vl-expr-p))
  :parents (vl-expr-selfsize)
  :short "Returns the \"opacity\" of the expression, a way of categorizing the
          expression for sizing."
  :long "<p>We are sorting expressions into three categories here:</p>

<ul>

<li>\"Transparent\" vector expressions, for which one
or more immediate subexpressions must have the same size as the outer
expression.  These include vector-valued binary operations such as @('+'),
@('&'), and @('<<'), unary vector-valued operations such as @('+') and @('~'),
and ternary @('? :') expressions.  When such an expression is sized, these
subexpressions are extended to the required size, and usually the other
immediate subexpressions (if any) are self-sized.</li>

<li>\"Opaque\" vector expressions, for which the outer expression's size
doesn't affect the sizes of its subexpressions.  These include constants,
variables, indexing operations, function calls, concatenations, binary
comparisons and logical operations (e.g. @('&&')), and unary bit-reductions.
There may be sizing constraints among the subexpressions, but they don't
involve the size of the outer expression.</li>

<li>\"Special\" expressions, whose type is determined in some other way; e.g.,
a streaming concatenation or an assignment-pattern can take on a
context-determined type.</li>

</ul>

<p>This distinction is a useful one because this second group are the
expressions that may need to be sign- or zero-extended.  E.g., if I have an
expression whose self-size is 4 and I use it in a context where it needs to be
extended to 8 bits, this happens differently depending which group it is in.
For example, if it is a (transparent) @('+') expression, we extend it by
extending its operands.  If it is an (opaque) expression, we just zero- or
sign-extend it and don't change any of its operands.</p>"

  :returns (opacity vl-opacity-p)

  (vl-expr-case x
    :vl-literal :opaque
    :vl-index :opaque
    :vl-unary (if (member x.op
                          '( ;; All of these operations have one-bit results.
                            :vl-unary-bitand :vl-unary-nand :vl-unary-bitor :vl-unary-nor
                            :vl-unary-xor :vl-unary-xnor :vl-unary-lognot))
                  :opaque
                :transparent)
    :vl-binary (if (member x.op
                           '( ;; All of these operations have one-bit results, and
                             ;; we have no expectations that their argument sizes
                             ;; should agree or anything like that.
                             :vl-binary-logand :vl-binary-logor

                             ;; SystemVerilog-2012 additions.  These also produce
                             ;; 1-bit results and we don't care if their arguments
                             ;; have equal sizes.
                             :vl-implies :vl-equiv

                             ;; These were originally part of the above case; they
                             ;; all return one-bit results.  However, we separate
                             ;; them out because, intuitively, their arguments
                             ;; "should" be the same size.  So as a Linting
                             ;; feature, we add warnings if any implicit size
                             ;; extension will occur.
                             :vl-binary-eq :vl-binary-neq :vl-binary-ceq :vl-binary-cne
                             :vl-binary-lt :vl-binary-lte :vl-binary-gt :vl-binary-gte

                             ;; SystemVerilog-2012 additions.  Although Table
                             ;; 11-21 doesn't specify what the sizes are here,
                             ;; Section 11.4.6 says these produce a 1-bit
                             ;; self-sized result and explains how the arguments
                             ;; are to be widened similarly to ordinary equality
                             ;; comparisons.
                             :vl-binary-wildeq :vl-binary-wildneq))
                   :opaque
                 :transparent)

    :vl-qmark :transparent

    :vl-concat :opaque
    :vl-multiconcat :opaque
    :vl-inside :opaque

    ;; Arguably these two are only applicable if the type is packed, but it's
    ;; not this function's job to make that distinction.
    :vl-call :opaque

    ;; Subtle! It could well be that a signedness-only cast could be
    ;; transparent where a size or datatype cast is opaque, but vcs and
    ;; ncverilog seem to treat them all as opaque.
    :vl-cast :opaque
    :vl-pattern :opaque

    :vl-mintypmax :transparent ;; BOZO I don't actually know how these work

    :vl-special :special
    :vl-stream :special
    :vl-tagged :special
    :vl-eventexpr :special

    ))


