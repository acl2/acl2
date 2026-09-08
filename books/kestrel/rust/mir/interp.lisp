; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST")

(include-book "limits")
(include-book "states")

(include-book "kestrel/fty/defresult" :dir :system)

; These allow the definitions below to prove
; their theorems under the controlled configuration,
; as in ../syntax/token-trees.lisp.
(local (include-book "kestrel/arithmetic-light/fix" :dir :system))
(local (include-book "kestrel/arithmetic-light/ifix" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/utilities/acl2-count" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/update-nth" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/repeat" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The result types (before the controlled configuration,
; whose default theory the defresult proofs need,
; as in ../syntax/tokenizer.lisp).
; The two disabled rules loop with fty::equal-of-len
; during the defresult proofs:
; len-of-cdr turns (len (cdr x)) into (+ -1 (len x)),
; arithmetic normalization turns the resulting equality
; back into an (equal (len x) constant) that
; fty::equal-of-len expands again, with a larger constant.

(local (in-theory (disable acl2::equal-of-+-when-negative-constant
                           acl2::len-of-cdr)))

(fty::defresult value-result
  :short "Fixtype of runtime values and errors."
  :ok value
  :pred value-resultp)

(fty::defresult value-list-result
  :short "Fixtype of lists of runtime values and errors."
  :ok value-list
  :pred value-list-resultp)

(fty::defresult frame-result
  :short "Fixtype of frames and errors."
  :ok frame
  :pred frame-resultp)

(fty::defresult frame-list-result
  :short "Fixtype of frame stacks and errors."
  :ok frame-list
  :pred frame-list-resultp)

(fty::defresult address-result
  :short "Fixtype of addresses and errors."
  :ok address
  :pred address-resultp)

(acl2::controlled-configuration)

; The bridge rules from the result types to their ok types
; are generated disabled; the definitions below use them
; throughout (after each not-reserrp test).

(local (in-theory (enable valuep-when-result-not-error
                          value-listp-when-result-not-error
                          framep-when-result-not-error
                          frame-listp-when-result-not-error
                          addressp-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ mir-interpreter
  :parents (mir)
  :short "A defensive small-step interpreter for MIR."
  :long
  (xdoc::topstring
   (xdoc::p
    "The interpreter executes the runtime-MIR dialect
     described in @(see mir-abstract-syntax),
     over the values of @(see mir-values)
     and the states of @(see mir-states).
     It is <i>defensive</i>:
     every operation checks the conditions it needs,
     and execution ends in a distinguished outcome
     rather than proceeding silently
     when a condition fails.
     The outcomes distinguish")
   (xdoc::ul
    (xdoc::li
     "normal termination with a value;")
    (xdoc::li
     "a panic (a failed @('assert') terminator &mdash;
      under @('panic=abort'), the program aborts);")
    (xdoc::li
     "undefined behavior of the executed program
      (reaching @('unreachable'),
      reading an uninitialized local,
      an out-of-bounds index projection,
      using a dangling reference,
      division by zero, or signed division overflow);")
    (xdoc::li
     "a stuck state: the program is outside
      the modeled subset or ill-formed
      (e.g. an out-of-range local or block index,
      or a type mismatch in an operation).
      Static well-formedness and typing judgments, to come,
      will rule these out by theorem;")
    (xdoc::li
     "fuel exhaustion of the step-counting driver."))
   (xdoc::p
    "Within the evaluation functions,
     errors are @(tsee fty::reserr) values whose information starts with
     @(':ub'), @(':panic'), or @(':stuck')
     to indicate the outcome kind;
     the step function turns them into outcomes.")
   (xdoc::p
    "Calls to standard library functions that
     the program does not define are executed by
     built-in <i>shims</i> (see @(tsee exec-shim)):
     first-order models of the small std surface
     that the modeled subset uses.
     A function body in the program always takes precedence,
     so imported real bodies supersede the shims.")
   (xdoc::p
    "The arithmetic follows Rust's monomorphic semantics
     on the current subset:
     the plain arithmetic operators wrap
     (rustc emits them when overflow checks are off),
     the @('...-with-overflow') operators return
     a @('(result, overflowed)') pair
     (rustc emits them, with a following assert,
     when overflow checks are on),
     division and remainder are
     undefined behavior on zero divisors and signed overflow
     (rustc guards them with asserts),
     and the shift operators mask the shift amount
     by the width of the left operand,
     as runtime MIR defines."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Typed-list positional lemmas that the fixtype machinery
; does not generate; local, as in states.lisp.

(local
 (defthm valuep-of-nth-when-value-listp
   (implies (and (value-listp l)
                 (< (nfix i) (len l)))
            (valuep (nth i l)))
   :hints (("Goal" :induct (nth i l)
                   :in-theory (e/d (nth nfix) (acl2::nth-of-cdr))))))

(local
 (defthm value-listp-of-update-nth-when-value-listp
   (implies (and (value-listp l)
                 (valuep v)
                 (< (nfix i) (len l)))
            (value-listp (update-nth i v l)))
   :hints (("Goal" :induct (update-nth i v l)
                   :in-theory (enable update-nth nfix)))))

(local
 (defthm basic-blockp-of-nth-when-basic-block-listp
   (implies (and (basic-block-listp l)
                 (< (nfix i) (len l)))
            (basic-blockp (nth i l)))
   :hints (("Goal" :induct (nth i l)
                   :in-theory (e/d (nth nfix) (acl2::nth-of-cdr))))))

(local
 (defthm statementp-of-nth-when-statement-listp
   (implies (and (statement-listp l)
                 (< (nfix i) (len l)))
            (statementp (nth i l)))
   :hints (("Goal" :induct (nth i l)
                   :in-theory (e/d (nth nfix) (acl2::nth-of-cdr))))))

(local
 (defthm value-option-listp-when-value-listp
   (implies (value-listp l)
            (value-option-listp l))
   :hints (("Goal" :induct (len l)
                   :in-theory (enable value-option-listp
                                      value-listp
                                      value-optionp
                                      len)))))

(local
 (defthm value-option-listp-of-repeat-nil
   (value-option-listp (acl2::repeat n nil))
   :hints (("Goal" :in-theory (enable acl2::repeat)
                   :induct (acl2::repeat n nil)))))

(local
 (defthm value-option-listp-of-append-when-value-option-listps
   (implies (and (value-option-listp a)
                 (value-option-listp b))
            (value-option-listp (append a b)))
   :hints (("Goal" :induct (append a b)
                   :in-theory (enable append)))))

(local
 (defthm framep-of-nth-when-frame-listp
   (implies (and (frame-listp l)
                 (< (nfix i) (len l)))
            (framep (nth i l)))
   :hints (("Goal" :induct (nth i l)
                   :in-theory (e/d (nth nfix) (acl2::nth-of-cdr))))))

(local
 (defthm frame-listp-of-update-nth-when-frame-listp
   (implies (and (frame-listp l)
                 (framep v)
                 (< (nfix i) (len l)))
            (frame-listp (update-nth i v l)))
   :hints (("Goal" :induct (update-nth i v l)
                   :in-theory (enable update-nth nfix)))))

(local
 (defthm path-elem-listp-of-append-when-path-elem-listps
   (implies (and (path-elem-listp a)
                 (path-elem-listp b))
            (path-elem-listp (append a b)))
   :hints (("Goal" :induct (append a b)
                   :in-theory (enable append)))))

(local
 (defthm value-listp-of-repeat-when-valuep
   (implies (valuep v)
            (value-listp (acl2::repeat n v)))
   :hints (("Goal" :in-theory (enable acl2::repeat)
                   :induct (acl2::repeat n v)))))

; Guard obligations state acl2-numberp/integerp/rationalp of
; quantities whose natp is known only by rewrite rules
; (mv-nth returns of the shim helpers), which type-set cannot see;
; these bridges let the rewriter close them
; (same as in c/syntax/lexer.lisp).

(local
 (defthm acl2-numberp-when-natp
   (implies (natp x) (acl2-numberp x))))

(local
 (defthm rationalp-when-natp
   (implies (natp x) (rationalp x))))

(local
 (defthm integerp-when-natp
   (implies (natp x) (integerp x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-arith-uint ((op bin-opp)
                         (l acl2::natp)
                         (r acl2::natp)
                         (type uint-typep))
  :returns (result value-resultp)
  :short "Evaluate an arithmetic or bitwise operation
          on unsigned integers of the same type."
  (b* ((l (acl2::nfix l))
       (r (acl2::nfix r)))
    (bin-op-case
     op
     :add (value-uint (uint-wrap (+ l r) type) type)
     :sub (value-uint (uint-wrap (- l r) type) type)
     :mul (value-uint (uint-wrap (* l r) type) type)
     :div (if (= r 0)
              (fty::reserr (list :ub :division-by-zero))
            (value-uint (uint-wrap (floor l r) type) type))
     :rem (if (= r 0)
              (fty::reserr (list :ub :remainder-by-zero))
            (value-uint (uint-wrap (mod l r) type) type))
     :add-with-overflow
     (b* ((exact (+ l r))
          (wrapped (uint-wrap exact type)))
       (value-tuple (list (value-uint wrapped type)
                          (value-bool (not (= exact wrapped))))))
     :sub-with-overflow
     (b* ((exact (- l r))
          (wrapped (uint-wrap exact type)))
       (value-tuple (list (value-uint wrapped type)
                          (value-bool (not (= exact wrapped))))))
     :mul-with-overflow
     (b* ((exact (* l r))
          (wrapped (uint-wrap exact type)))
       (value-tuple (list (value-uint wrapped type)
                          (value-bool (not (= exact wrapped))))))
     :bit-xor (value-uint (uint-wrap (logxor l r) type) type)
     :bit-and (value-uint (uint-wrap (logand l r) type) type)
     :bit-or (value-uint (uint-wrap (logior l r) type) type)
     :otherwise (fty::reserr (list :stuck :non-arith-op-on-uints)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-arith-int ((op bin-opp)
                        (l acl2::integerp)
                        (r acl2::integerp)
                        (type int-typep))
  :returns (result value-resultp)
  :short "Evaluate an arithmetic or bitwise operation
          on signed integers of the same type."
  (b* ((l (acl2::ifix l))
       (r (acl2::ifix r)))
    (bin-op-case
     op
     :add (value-int (int-wrap (+ l r) type) type)
     :sub (value-int (int-wrap (- l r) type) type)
     :mul (value-int (int-wrap (* l r) type) type)
     :div (cond ((= r 0)
                 (fty::reserr (list :ub :division-by-zero)))
                ((and (= l (int-type-min type))
                      (= r -1))
                 (fty::reserr (list :ub :division-overflow)))
                (t (value-int (int-wrap (truncate l r) type) type)))
     :rem (cond ((= r 0)
                 (fty::reserr (list :ub :remainder-by-zero)))
                ((and (= l (int-type-min type))
                      (= r -1))
                 (fty::reserr (list :ub :remainder-overflow)))
                (t (value-int (int-wrap (- l (* r (truncate l r))) type)
                              type)))
     :add-with-overflow
     (b* ((exact (+ l r))
          (wrapped (int-wrap exact type)))
       (value-tuple (list (value-int wrapped type)
                          (value-bool (not (= exact wrapped))))))
     :sub-with-overflow
     (b* ((exact (- l r))
          (wrapped (int-wrap exact type)))
       (value-tuple (list (value-int wrapped type)
                          (value-bool (not (= exact wrapped))))))
     :mul-with-overflow
     (b* ((exact (* l r))
          (wrapped (int-wrap exact type)))
       (value-tuple (list (value-int wrapped type)
                          (value-bool (not (= exact wrapped))))))
     :bit-xor (value-int (int-wrap (logxor l r) type) type)
     :bit-and (value-int (int-wrap (logand l r) type) type)
     :bit-or (value-int (int-wrap (logior l r) type) type)
     :otherwise (fty::reserr (list :stuck :non-arith-op-on-ints)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-integerp ((value valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is an integer (signed or unsigned)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This checks dynamically what @(tsee value-integer->get)
     then assumes as its guard,
     following the two-layer pattern of
     the C language formalization's operations."))
  (or (value-case value :int)
      (value-case value :uint)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-integer->get ((value valuep))
  :guard (value-integerp value)
  :returns (int acl2::integerp)
  :short "Mathematical integer of an integer value."
  (value-case value
              :int value.val
              :uint value.val
              :otherwise 0) ; unreachable under the guard
  :guard-hints (("Goal" :in-theory (enable value-integerp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-shift ((op bin-opp) (left valuep) (right valuep))
  :returns (result value-resultp)
  :short "Evaluate a shift operation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The left operand may be signed or unsigned;
     the right operand may independently be signed or unsigned.
     Runtime MIR's plain shift operators mask the shift amount
     by the width of the left operand's type
     (the overflow checks that reject large shift amounts
     are separate assert terminators, when enabled).
     A right shift is logical for unsigned left operands and
     arithmetic for signed ones, as in Rust."))
  (b* (((unless (value-integerp right))
        (fty::reserr (list :stuck :non-integer-shift-amount)))
       (amount (value-integer->get right)))
    (value-case
     left
     :uint (b* ((bits (uint-type-bits left.type))
                (sh (mod amount bits)))
             (bin-op-case
              op
              :shl (value-uint (uint-wrap (ash left.val sh) left.type)
                               left.type)
              :shr (value-uint (uint-wrap (ash left.val (- sh)) left.type)
                               left.type)
              :otherwise (fty::reserr (list :stuck :non-shift-op))))
     :int (b* ((bits (int-type-bits left.type))
               (sh (mod amount bits)))
            (bin-op-case
             op
             :shl (value-int (int-wrap (ash left.val sh) left.type)
                             left.type)
             :shr (value-int (int-wrap (ash left.val (- sh)) left.type)
                             left.type)
             :otherwise (fty::reserr (list :stuck :non-shift-op))))
     :otherwise (fty::reserr (list :stuck :shift-of-non-integer)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-scalarp ((value valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is scalar:
          a boolean, character, or integer."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the values that
     comparisons and switch terminators operate on.
     This checks dynamically what @(tsee value-scalar->int)
     then assumes as its guard."))
  (or (value-case value :bool)
      (value-case value :char)
      (value-case value :int)
      (value-case value :uint)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-scalar->int ((value valuep))
  :guard (value-scalarp value)
  :returns (int acl2::integerp)
  :short "Mathematical integer of a scalar value,
          preserving order within each type."
  :long
  (xdoc::topstring
   (xdoc::p
    "Booleans map to 0 and 1 (@('false < true') in Rust),
     characters to their code points,
     integers to their values.
     This is what comparisons compare and switches test;
     the callers ensure that only values of the same kind
     (and, for integers, the same type) are compared
     with each other."))
  (value-case value
              :bool (if value.val 1 0)
              :char value.val
              :int value.val
              :uint value.val
              :otherwise 0) ; unreachable under the guard
  :guard-hints (("Goal" :in-theory (enable value-scalarp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-same-comparable-kind-p ((left valuep) (right valuep))
  :returns (yes/no booleanp)
  :short "Check that two values are comparable with each other:
          same kind, and for integers also the same type."
  (or (and (value-case left :bool) (value-case right :bool))
      (and (value-case left :char) (value-case right :char))
      (and (value-case left :int)
           (value-case right :int)
           (int-type-equiv (value-int->type left)
                           (value-int->type right)))
      (and (value-case left :uint)
           (value-case right :uint)
           (uint-type-equiv (value-uint->type left)
                            (value-uint->type right)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-compare ((op bin-opp) (left valuep) (right valuep))
  :returns (result value-resultp)
  :short "Evaluate a comparison operation."
  (b* (((unless (value-same-comparable-kind-p left right))
        (fty::reserr (list :stuck :comparison-of-mismatched-values)))
       (l (value-scalar->int left))
       (r (value-scalar->int right)))
    (bin-op-case op
                 :eq (value-bool (= l r))
                 :ne (value-bool (not (= l r)))
                 :lt (value-bool (< l r))
                 :le (value-bool (<= l r))
                 :ge (value-bool (>= l r))
                 :gt (value-bool (> l r))
                 :otherwise (fty::reserr (list :stuck :non-comparison-op))))
  :guard-hints (("Goal" :in-theory (enable value-same-comparable-kind-p
                                           value-scalarp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-binop ((op bin-opp) (left valuep) (right valuep))
  :returns (result value-resultp)
  :short "Evaluate a binary operation on two values."
  (b* ((kind (bin-op-kind op)))
    (cond ((member-eq kind '(:shl :shr))
           (eval-shift op left right))
          ((member-eq kind '(:eq :ne :lt :le :ge :gt))
           (eval-compare op left right))
          ((and (value-case left :uint)
                (value-case right :uint)
                (uint-type-equiv (value-uint->type left)
                                 (value-uint->type right)))
           (eval-arith-uint op
                            (value-uint->val left)
                            (value-uint->val right)
                            (value-uint->type left)))
          ((and (value-case left :int)
                (value-case right :int)
                (int-type-equiv (value-int->type left)
                                (value-int->type right)))
           (eval-arith-int op
                           (value-int->val left)
                           (value-int->val right)
                           (value-int->type left)))
          (t (fty::reserr (list :stuck :binop-on-mismatched-values))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-unop ((op un-opp) (value valuep))
  :returns (result value-resultp)
  :short "Evaluate a unary operation on a value."
  :long
  (xdoc::topstring
   (xdoc::p
    "Logical not on booleans,
     bitwise not on integers,
     and arithmetic negation on signed integers
     (wrapping: negating the minimum value gives itself,
     matching Rust's wrapping negation;
     with overflow checks on, rustc guards negation
     with an assert)."))
  (un-op-case
   op
   :not (value-case value
                    :bool (value-bool (not value.val))
                    :uint (value-uint (uint-wrap (lognot value.val) value.type)
                                      value.type)
                    :int (value-int (int-wrap (lognot value.val) value.type)
                                    value.type)
                    :otherwise (fty::reserr (list :stuck :not-of-non-integer)))
   :neg (value-case value
                    :int (value-int (int-wrap (- value.val) value.type)
                                    value.type)
                    :otherwise (fty::reserr
                                (list :stuck :neg-of-non-signed-integer)))
   :ptr-metadata
   (value-case value
               :slice-ref (value-uint (value-slice-ref->len value)
                                      (uint-type-usize))
               :ref (value-unit)
               :otherwise (fty::reserr
                           (list :stuck :ptr-metadata-of-non-reference)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-frame-abs ((k acl2::natp) (frames frame-listp))
  :returns (result frame-resultp)
  :short "Fetch a frame by its absolute (from-the-bottom) number."
  :long
  (xdoc::topstring
   (xdoc::p
    "Frame 0 is the bottom of the stack;
     the currently executing frame has the number
     one less than the stack height
     (and is the first element of the frames list,
     which is topmost-first).
     Frames are numbered from the bottom so that
     an address stays meaningful while frames are
     pushed and popped above its frame.
     A number at or above the stack height denotes
     a frame that has been popped:
     the reference that led here is dangling,
     and using it is undefined behavior."))
  (b* ((k (acl2::nfix k))
       (frames (frame-list-fix frames))
       ((unless (< k (len frames)))
        (fty::reserr (list :ub :dangling-frame-reference k))))
    (frame-fix (nth (- (len frames) (1+ k)) frames)))
  :guard-hints (("Goal" :in-theory (enable acl2::nfix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define set-frame-abs ((k acl2::natp) (frame framep) (frames frame-listp))
  :returns (new-frames frame-listp
                       :hints (("Goal" :in-theory (enable acl2::nfix))))
  :short "Replace a frame by its absolute (from-the-bottom) number."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the number is out of range, the stack is returned unchanged;
     the callers fetch the frame (checking the range)
     before storing an updated version back."))
  (b* ((k (acl2::nfix k))
       (frames (frame-list-fix frames))
       ((unless (< k (len frames)))
        frames))
    (update-nth (- (len frames) (1+ k))
                (frame-fix frame)
                frames))
  :guard-hints (("Goal" :in-theory (enable acl2::nfix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define load-path ((path path-elem-listp) (value valuep))
  :returns (result value-resultp)
  :short "Read through a concrete path within a value."
  :long
  (xdoc::topstring
   (xdoc::p
    "A field element reads a component of
     a tuple or (possibly downcast) enum value;
     an index element reads an element of an array value,
     with an out-of-bounds index being undefined behavior
     (in-bounds asserts are separate, earlier terminators);
     a downcast checks the active variant
     (a wrong-variant downcast read is undefined behavior)
     and continues on the same value."))
  (b* (((when (endp path)) (value-fix value))
       (elem (car path)))
    (path-elem-case
     elem
     :field
     (value-case
      value
      :tuple (if (< elem.index (len value.elems))
                 (load-path (cdr path) (nth elem.index value.elems))
               (fty::reserr (list :stuck :field-index-out-of-range)))
      :variant (if (< elem.index (len value.fields))
                   (load-path (cdr path) (nth elem.index value.fields))
                 (fty::reserr (list :stuck :field-index-out-of-range)))
      :otherwise (fty::reserr (list :stuck :field-of-non-aggregate)))
     :index
     (value-case
      value
      :array (if (< elem.index (len value.elems))
                 (load-path (cdr path) (nth elem.index value.elems))
               (fty::reserr (list :ub :index-out-of-bounds)))
      :otherwise (fty::reserr (list :stuck :index-of-non-array)))
     :downcast
     (value-case
      value
      :variant (if (= elem.variant value.index)
                   (load-path (cdr path) value)
                 (fty::reserr (list :ub :downcast-to-inactive-variant)))
      :otherwise (fty::reserr (list :stuck :downcast-of-non-enum))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define store-path ((path path-elem-listp) (old valuep) (new valuep))
  :returns (result value-resultp)
  :verify-guards :after-returns
  :short "Write through a concrete path within a value,
          returning the updated value."
  :long
  (xdoc::topstring
   (xdoc::p
    "The checks are as in @(tsee load-path);
     the updated component is rebuilt at each level."))
  (b* (((when (endp path)) (value-fix new))
       (elem (car path)))
    (path-elem-case
     elem
     :field
     (value-case
      old
      :tuple
      (b* (((unless (< elem.index (len old.elems)))
            (fty::reserr (list :stuck :field-index-out-of-range)))
           (new-sub (store-path (cdr path) (nth elem.index old.elems) new))
           ((when (fty::reserrp new-sub)) new-sub))
        (value-tuple (update-nth elem.index new-sub old.elems)))
      :variant
      (b* (((unless (< elem.index (len old.fields)))
            (fty::reserr (list :stuck :field-index-out-of-range)))
           (new-sub (store-path (cdr path) (nth elem.index old.fields) new))
           ((when (fty::reserrp new-sub)) new-sub))
        (value-variant old.index (update-nth elem.index new-sub old.fields)))
      :otherwise (fty::reserr (list :stuck :field-of-non-aggregate)))
     :index
     (value-case
      old
      :array
      (b* (((unless (< elem.index (len old.elems)))
            (fty::reserr (list :ub :index-out-of-bounds)))
           (new-sub (store-path (cdr path) (nth elem.index old.elems) new))
           ((when (fty::reserrp new-sub)) new-sub))
        (value-array (update-nth elem.index new-sub old.elems)))
      :otherwise (fty::reserr (list :stuck :index-of-non-array)))
     :downcast
     (value-case
      old
      :variant (if (= elem.variant old.index)
                   (store-path (cdr path) old new)
                 (fty::reserr (list :ub :downcast-to-inactive-variant)))
      :otherwise (fty::reserr (list :stuck :downcast-of-non-enum))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define load-address ((address addressp) (frames frame-listp))
  :returns (result value-resultp)
  :short "Load the value at an address."
  (b* (((address address) address)
       (frame (get-frame-abs address.frame frames))
       ((when (fty::reserrp frame)) frame)
       ((unless (local-in-range-p address.local frame))
        (fty::reserr (list :stuck :local-out-of-range address.local)))
       (root (read-local address.local frame))
       ((unless root)
        (fty::reserr (list :ub :read-of-uninitialized-local
                           address.local))))
    (load-path address.path root)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define store-address ((address addressp) (value valuep) (frames frame-listp))
  :returns (result frame-list-resultp)
  :short "Store a value at an address,
          returning the updated frame stack."
  :long
  (xdoc::topstring
   (xdoc::p
    "A store to a bare local (empty path) is
     an initializing write: the local may be uninitialized.
     A store through a nonempty path requires
     the root local to be initialized."))
  (b* (((address address) address)
       (frame (get-frame-abs address.frame frames))
       ((when (fty::reserrp frame)) frame)
       ((unless (local-in-range-p address.local frame))
        (fty::reserr (list :stuck :local-out-of-range address.local)))
       ((when (endp address.path))
        (set-frame-abs address.frame
                       (write-local address.local (value-fix value) frame)
                       frames))
       (root (read-local address.local frame))
       ((unless root)
        (fty::reserr (list :ub :write-through-uninitialized-local
                           address.local)))
       (new-root (store-path address.path root value))
       ((when (fty::reserrp new-root)) new-root))
    (set-frame-abs address.frame
                   (write-local address.local new-root frame)
                   frames)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define address-add ((address addressp) (elem path-elemp))
  :returns (new-address addressp)
  :short "Extend an address's path by one element."
  (change-address address
                  :path (append (address->path address)
                                (list (path-elem-fix elem)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The dereference case of eval-place-elems consumes two projection
;; elements at once (the dereference and the index into the slice
;; window), which breaks the built-in-clause pattern that discharges
;; cdr-style measures without the prover.  The measure goal reaches
;; the prover with o< unopened (it is disabled in this configuration),
;; so this rewrite rule is stated in o< form to match it directly.
(local
 (defthm o<-of-acl2-count-of-cddr
   (implies (consp (cdr x))
            (o< (acl2-count (cddr x)) (acl2-count x)))
   :hints (("Goal"
            :in-theory (enable o< o-finp)
            :expand ((acl2-count x)
                     (acl2-count (cdr x)))))))

(define eval-place-elems ((elems proj-elem-listp)
                          (address addressp)
                          (frames frame-listp))
  :returns (result address-resultp)
  :short "Resolve place projections onto an address."
  :long
  (xdoc::topstring
   (xdoc::p
    "Field and downcast projections extend the address path;
     an index projection reads its index local &mdash;
     always a local of the currently executing (top) frame,
     as in rustc, even after a dereference &mdash;
     and extends the path with the concrete index;
     a dereference loads the reference value at
     the address resolved so far and
     continues from the address it denotes."))
  (b* (((when (endp elems)) (address-fix address))
       ((when (endp frames))
        (fty::reserr (list :stuck :empty-frame-stack)))
       (elem (car elems)))
    (proj-elem-case
     elem
     :field (eval-place-elems (cdr elems)
                              (address-add address
                                           (path-elem-field elem.index))
                              frames)
     :downcast (eval-place-elems (cdr elems)
                                 (address-add address
                                              (path-elem-downcast
                                               elem.variant))
                                 frames)
     :index
     (b* ((index-value (read-local elem.local (car frames)))
          ((unless index-value)
           (fty::reserr (list :ub :uninitialized-index-local)))
          ((unless (value-case index-value :uint))
           (fty::reserr (list :stuck :non-integer-index))))
       (eval-place-elems (cdr elems)
                         (address-add address
                                      (path-elem-index
                                       (value-uint->val index-value)))
                         frames))
     :deref
     (b* ((value (load-address address frames))
          ((when (fty::reserrp value)) value))
       (value-case
        value
        :ref (eval-place-elems (cdr elems)
                               (value-ref->address value)
                               frames)
        ;; Dereferencing a slice reference: the referent is
        ;; a window into an array, so the only place shape
        ;; the modeled subset allows on top of the dereference
        ;; is an index into that window.  The index is offset by
        ;; the window start and checked against the window length
        ;; (an out-of-window access through a slice reference is
        ;; undefined behavior at the machine level; the in-language
        ;; bounds checks are separate assert terminators).
        ;; Whole-slice dereferences (reborrows) do not reach here:
        ;; they copy the fat pointer as a value instead.
        :slice-ref
        (b* (((when (endp (cdr elems)))
              (fty::reserr (list :stuck :bare-deref-of-slice-reference)))
             (next (car (cdr elems)))
             ((unless (proj-elem-case next :index))
              (fty::reserr (list :stuck :non-index-after-slice-deref)))
             (index-value (read-local (proj-elem-index->local next)
                                      (car frames)))
             ((unless index-value)
              (fty::reserr (list :ub :uninitialized-index-local)))
             ((unless (value-case index-value :uint))
              (fty::reserr (list :stuck :non-integer-index)))
             (i (value-uint->val index-value))
             ((unless (< i (value-slice-ref->len value)))
              (fty::reserr (list :ub :slice-index-out-of-window i)))
             (start (value-slice-ref->start value)))
          (eval-place-elems (cddr elems)
                            (address-add (value-slice-ref->address value)
                                         (path-elem-index (+ start i)))
                            frames))
        :otherwise (fty::reserr (list :stuck :deref-of-non-reference)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-place ((place placep) (frames frame-listp))
  :returns (result address-resultp)
  :short "Evaluate a place to the address it denotes."
  (b* (((place place) place)
       ((when (endp frames))
        (fty::reserr (list :stuck :empty-frame-stack)))
       ((unless (local-in-range-p place.local (car frames)))
        (fty::reserr (list :stuck :local-out-of-range place.local))))
    (eval-place-elems place.projection
                      (make-address :frame (1- (len frames))
                                    :local place.local
                                    :path nil)
                      frames)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-place ((place placep) (frames frame-listp))
  :returns (result value-resultp)
  :short "Read the value of a place."
  (b* ((address (eval-place place frames))
       ((when (fty::reserrp address)) address))
    (load-address address frames)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-place ((place placep) (value valuep) (frames frame-listp))
  :returns (result frame-list-resultp)
  :short "Write a value to a place,
          returning the updated frame stack."
  (b* ((address (eval-place place frames))
       ((when (fty::reserrp address)) address))
    (store-address address value frames)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-operand ((operand operandp) (frames frame-listp))
  :returns (result value-resultp)
  :short "Evaluate an operand against the frame stack."
  :long
  (xdoc::topstring
   (xdoc::p
    "Copy and move operands both read their place;
     we do not model move deinitialization yet
     (borrow-checked programs never read a moved-from place,
     so on them the difference is unobservable;
     the distinction will come with
     the byte-level machine layer)."))
  (operand-case operand
                :copy (read-place operand.place frames)
                :move (read-place operand.place frames)
                :constant (const-to-value operand.const)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-operand-list ((operands operand-listp) (frames frame-listp))
  :returns (result value-list-resultp)
  :short "Evaluate a list of operands against the frame stack."
  (b* (((when (endp operands)) nil)
       (value (eval-operand (car operands) frames))
       ((when (fty::reserrp value)) value)
       (rest (eval-operand-list (cdr operands) frames))
       ((when (fty::reserrp rest)) rest))
    (cons value rest)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-rvalue ((rvalue rvaluep) (frames frame-listp))
  :returns (result value-resultp)
  :short "Evaluate an rvalue against the frame stack."
  :long
  (xdoc::topstring
   (xdoc::p
    "A reference rvalue evaluates its place to an address
     and wraps it as a reference value.
     An integer-to-integer cast wraps the operand's
     mathematical value into the target type
     (Rust's @('as'): two's-complement truncation or extension).
     An unsizing cast takes a reference to an array
     and produces a slice reference covering the whole array,
     reading the length from the referenced array itself.
     A repeat rvalue evaluates its operand once and
     replicates it."))
  (rvalue-case
   rvalue
   :use (eval-operand rvalue.operand frames)
   :ref
   (b* ((address (eval-place rvalue.place frames))
        ((when (fty::reserrp address)) address))
     (value-ref address))
   :binary-op
   (b* ((left (eval-operand rvalue.left frames))
        ((when (fty::reserrp left)) left)
        (right (eval-operand rvalue.right frames))
        ((when (fty::reserrp right)) right))
     (eval-binop rvalue.op left right))
   :unary-op
   (b* ((value (eval-operand rvalue.operand frames))
        ((when (fty::reserrp value)) value))
     (eval-unop rvalue.op value))
   :cast
   (b* ((value (eval-operand rvalue.operand frames))
        ((when (fty::reserrp value)) value)
        (kind rvalue.kind))
     (cast-kind-case
      kind
      :int-to-int
      (b* (((unless (value-integerp value))
            (fty::reserr (list :stuck :int-cast-of-non-integer)))
           (n (value-integer->get value))
           (ty rvalue.ty))
        (ty-case ty
                 :int (value-int (int-wrap n ty.type) ty.type)
                 :uint (value-uint (uint-wrap n ty.type) ty.type)
                 :otherwise (fty::reserr
                             (list :stuck :int-cast-to-non-integer-type))))
      :unsize
      (b* (((unless (value-case value :ref))
            (fty::reserr (list :stuck :unsize-of-non-reference)))
           (address (value-ref->address value))
           (target (load-address address frames))
           ((when (fty::reserrp target)) target)
           ((unless (value-case target :array))
            (fty::reserr (list :stuck :unsize-of-non-array-reference))))
        (value-slice-ref address 0 (len (value-array->elems target))))))
   :aggregate
   (b* ((values (eval-operand-list rvalue.operands frames))
        ((when (fty::reserrp values)) values)
        (kind rvalue.kind))
     (agg-kind-case kind
                    :tuple (value-tuple values)
                    :array (value-array values)
                    :adt (value-variant (agg-kind-adt->variant kind)
                                        values)))
   :repeat
   (b* ((value (eval-operand rvalue.operand frames))
        ((when (fty::reserrp value)) value))
     (value-array (acl2::repeat rvalue.count value)))
   :discriminant
   (b* ((value (read-place rvalue.place frames))
        ((when (fty::reserrp value)) value))
     (value-case
      value
      :variant (value-uint value.index (uint-type-usize))
      :otherwise (fty::reserr (list :stuck :discriminant-of-non-enum))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-statement ((stmt statementp) (frames frame-listp))
  :returns (result frame-list-resultp)
  :short "Execute a statement, returning the updated frame stack."
  :long
  (xdoc::topstring
   (xdoc::p
    "Assignments may write through references into deeper frames,
     which is why statements update the whole stack.
     The storage markers reset their local
     (a local of the currently executing, top frame)
     to uninitialized:
     a @(':storage-live') (re)starts the local's live range
     with no value yet, and a @(':storage-dead') ends it.
     Setting discriminants is not yet in the modeled subset
     (rustc emits it together with constructs we do not cover yet)."))
  (b* (((when (endp frames))
        (fty::reserr (list :stuck :empty-frame-stack))))
    (statement-case
     stmt
     :assign
     (b* ((value (eval-rvalue stmt.rvalue frames))
          ((when (fty::reserrp value)) value))
       (write-place stmt.place value frames))
     :storage-live
     (if (local-in-range-p stmt.local (car frames))
         (cons (write-local stmt.local nil (car frames))
               (frame-list-fix (cdr frames)))
       (fty::reserr (list :stuck :local-out-of-range stmt.local)))
     :storage-dead
     (if (local-in-range-p stmt.local (car frames))
         (cons (write-local stmt.local nil (car frames))
               (frame-list-fix (cdr frames)))
       (fty::reserr (list :stuck :local-out-of-range stmt.local)))
     :set-discriminant (fty::reserr (list :stuck
                                          :set-discriminant-not-in-subset))
     :nop (frame-list-fix frames))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Standard library shims.
;
; First-order models of the standard library functions that
; the modeled subset calls.  The value conventions for
; the standard types involved (positional fields):
;   Option:  variant 0 = None [],  variant 1 = Some [v]
;   Result:  variant 0 = Ok [v],   variant 1 = Err [e]
;   Range:   variant 0, fields [start, end]
;   RangeTo: variant 0, fields [end]
;   RangeFrom: variant 0, fields [start]
;   StepBy:  variant 0, fields [range, step-minus-1, first-take]
;   Iter/IterMut: variant 0, fields [slice-ref, position]
;   Zip:     variant 0, fields [iter-a, iter-b]
; (Rev is an identity newtype: a reversed range is
; represented by the range itself, and its next is next_back.)
; The importer maps the monomorphized std names to
; the shim names in *shim-names*.

(define mk-none ()
  :returns (value valuep)
  :short "The @('None') value."
  (value-variant 0 nil))

(define mk-some ((value valuep))
  :returns (some valuep)
  :short "A @('Some') value."
  (value-variant 1 (list (value-fix value))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define as-slice-window ((value valuep) (frames frame-listp))
  :returns (result value-resultp)
  :short "Normalize a slice or array reference to a slice reference."
  :long
  (xdoc::topstring
   (xdoc::p
    "The slice shims accept either a slice reference
     or a (thin) reference to an array
     (rustc inserts the unsizing coercion in most positions,
     but array impls can also reach the slice methods directly);
     the latter becomes a whole-array window."))
  (value-case
   value
   :slice-ref (value-fix value)
   :ref
   (b* ((target (load-address value.address frames))
        ((when (fty::reserrp target)) target)
        ((unless (value-case target :array))
         (fty::reserr (list :stuck :not-a-slice-or-array-reference))))
     (value-slice-ref value.address 0 (len (value-array->elems target))))
   :otherwise (fty::reserr (list :stuck :not-a-slice-or-array-reference)))
  ///

  (defret value-kind-of-as-slice-window
    (implies (not (fty::reserrp result))
             (equal (value-kind result) :slice-ref))
    :hints (("Goal" :in-theory (enable as-slice-window)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define take-window ((elems value-listp) (start acl2::natp) (count acl2::natp))
  :returns (values value-listp)
  :measure (acl2-count count)
  :short "Extract a window of elements."
  (if (or (zp count)
          (>= (acl2::nfix start) (len elems)))
      nil
    (cons (value-fix (nth (acl2::nfix start) elems))
          (take-window elems (1+ (acl2::nfix start)) (1- count))))
  ;; the automatic fix congruences do not prove for
  ;; this two-counter recursion (cf. switch-pick)
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define splice-window ((elems value-listp) (start acl2::natp)
                       (new value-listp))
  :returns (values value-listp)
  :measure (acl2-count new)
  :short "Overwrite a window of elements."
  (cond ((endp new) (value-list-fix elems))
        ((>= (acl2::nfix start) (len elems)) (value-list-fix elems))
        (t (splice-window (update-nth (acl2::nfix start)
                                      (value-fix (car new))
                                      (value-list-fix elems))
                          (1+ (acl2::nfix start))
                          (cdr new))))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define slice-window-elems ((sref valuep) (frames frame-listp))
  :guard (value-case sref :slice-ref)
  :returns (result value-list-resultp)
  :short "Read the element values of a slice reference's window."
  (b* (((unless (mbt (value-case sref :slice-ref)))
        (fty::reserr (list :stuck :not-a-slice-reference)))
       (array (load-address (value-slice-ref->address sref) frames))
       ((when (fty::reserrp array)) array)
       ((unless (value-case array :array))
        (fty::reserr (list :stuck :slice-into-non-array)))
       (elems (value-array->elems array))
       (start (value-slice-ref->start sref))
       (len (value-slice-ref->len sref))
       ((unless (<= (+ start len) (len elems)))
        (fty::reserr (list :ub :slice-window-out-of-bounds))))
    (take-window elems start len)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define slice-window-write ((sref valuep)
                            (new value-listp)
                            (frames frame-listp))
  :guard (value-case sref :slice-ref)
  :returns (result frame-list-resultp)
  :short "Overwrite the window of a slice reference
          with new element values."
  (b* ((new (value-list-fix new))
       ((unless (mbt (value-case sref :slice-ref)))
        (fty::reserr (list :stuck :not-a-slice-reference)))
       (address (value-slice-ref->address sref))
       (array (load-address address frames))
       ((when (fty::reserrp array)) array)
       ((unless (value-case array :array))
        (fty::reserr (list :stuck :slice-into-non-array)))
       (elems (value-array->elems array))
       (start (value-slice-ref->start sref))
       (len (value-slice-ref->len sref))
       ((unless (and (<= (+ start len) (len elems))
                     (equal (len new) len)))
        (fty::reserr (list :ub :slice-window-out-of-bounds))))
    (store-address address
                   (value-array (splice-window elems start new))
                   frames)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uint-rotate-right ((n acl2::natp) (k acl2::natp) (type uint-typep))
  :returns (result acl2::natp)
  :short "Rotate an unsigned integer right within its width."
  (b* ((bits (uint-type-bits type))
       (s (mod (acl2::nfix k) bits)))
    (uint-wrap (logior (ash (acl2::nfix n) (- s))
                       (ash (acl2::nfix n) (- bits s)))
               type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-u8-byte ((value valuep))
  :returns (mv (okp booleanp)
               (byte acl2::natp
                     :rule-classes (:rewrite :type-prescription)))
  :short "The byte of a @('u8') value."
  (if (and (value-case value :uint)
           (uint-type-case (value-uint->type value) :u8))
      (mv t (value-uint->val value))
    (mv nil 0)))

(define values-le-word ((bytes value-listp))
  :returns (mv (okp booleanp)
               (word acl2::natp
                     :rule-classes (:rewrite :type-prescription)))
  :short "Combine little-endian byte values into a word."
  (b* (((when (endp bytes)) (mv t 0))
       ((mv okp byte) (value-u8-byte (car bytes)))
       ((unless okp) (mv nil 0))
       ((mv okp rest) (values-le-word (cdr bytes)))
       ((unless okp) (mv nil 0)))
    (mv t (+ (acl2::nfix byte) (* 256 (acl2::nfix rest))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define range-fields ((value valuep))
  :returns (mv (okp booleanp)
               (start acl2::natp
                      :rule-classes (:rewrite :type-prescription))
               (end acl2::natp
                    :rule-classes (:rewrite :type-prescription)))
  :short "The start and end of a @('Range<usize>') value."
  (b* (((unless (and (value-case value :variant)
                     (equal (value-variant->index value) 0)
                     (equal (len (value-variant->fields value)) 2)))
        (mv nil 0 0))
       (fields (value-variant->fields value))
       (start (nth 0 fields))
       (end (nth 1 fields))
       ((unless (and (value-case start :uint)
                     (value-case end :uint)))
        (mv nil 0 0)))
    (mv t (value-uint->val start) (value-uint->val end)))
  :guard-hints (("Goal" :in-theory (enable acl2::nfix))))

(define mk-range ((start acl2::natp) (end acl2::natp))
  :returns (range valuep)
  :short "Build a @('Range<usize>') value."
  (value-variant 0 (list (value-uint (acl2::nfix start) (uint-type-usize))
                         (value-uint (acl2::nfix end) (uint-type-usize)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define shim-ref-arg ((value valuep) (frames frame-listp))
  :returns (mv (result value-resultp) (address addressp))
  :short "Dereference a by-reference shim argument."
  :long
  (xdoc::topstring
   (xdoc::p
    "Many shims take @('&mut') arguments
     (iterators being advanced, values being updated in place):
     this loads the referenced value and
     also returns its address for writing back."))
  (b* (((unless (value-case value :ref))
        (mv (fty::reserr (list :stuck :shim-expected-a-reference))
            (irr-address)))
       (address (value-ref->address value))
       (target (load-address address frames))
       ((when (fty::reserrp target)) (mv target (irr-address))))
    (mv target address)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define shim-range-next ((args value-listp)
                         (frames frame-listp)
                         (backp acl2::booleanp))
  :returns (mv (result value-resultp) (new-frames frame-listp))
  :short "Shim for @('Range<usize>')'s @('next') and @('next_back')."
  (b* ((frames (frame-list-fix frames))
       (args (value-list-fix args))
       ((unless (equal (len args) 1))
        (mv (fty::reserr (list :stuck :shim-arity)) frames))
       ((mv range address) (shim-ref-arg (car args) frames))
       ((when (fty::reserrp range)) (mv range frames))
       ((mv okp start end) (range-fields range))
       ((unless okp)
        (mv (fty::reserr (list :stuck :not-a-range)) frames))
       ((unless (< start end))
        (mv (mk-none) frames))
       ((mv yield new-range)
        (if backp
            (mv (1- end) (mk-range start (1- end)))
          (mv start (mk-range (1+ start) end))))
       (new-frames (store-address address new-range frames))
       ((when (fty::reserrp new-frames)) (mv new-frames frames)))
    (mv (mk-some (value-uint yield (uint-type-usize)))
        new-frames))
  :guard-hints (("Goal" :in-theory (enable natp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define shim-step-by-next ((args value-listp) (frames frame-listp))
  :returns (mv (result value-resultp) (new-frames frame-listp))
  :short "Shim for @('StepBy<Range<usize>>')'s @('next')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first call yields the range's start;
     each later call advances the start by the step
     (jumping over step-minus-1 elements)
     and yields the new start if it is still in range,
     parking the range at @('(end, end)') otherwise."))
  (b* ((frames (frame-list-fix frames))
       (args (value-list-fix args))
       ((unless (equal (len args) 1))
        (mv (fty::reserr (list :stuck :shim-arity)) frames))
       ((mv stepby address) (shim-ref-arg (car args) frames))
       ((when (fty::reserrp stepby)) (mv stepby frames))
       ((unless (and (value-case stepby :variant)
                     (equal (value-variant->index stepby) 0)
                     (equal (len (value-variant->fields stepby)) 3)))
        (mv (fty::reserr (list :stuck :not-a-step-by)) frames))
       (fields (value-variant->fields stepby))
       (range (nth 0 fields))
       (stepm1v (nth 1 fields))
       (firstv (nth 2 fields))
       ((unless (and (value-case stepm1v :uint)
                     (value-case firstv :bool)))
        (mv (fty::reserr (list :stuck :not-a-step-by)) frames))
       (stepm1 (value-uint->val stepm1v))
       (firstp (value-bool->val firstv))
       ((mv okp start end) (range-fields range))
       ((unless okp)
        (mv (fty::reserr (list :stuck :not-a-step-by)) frames))
       ((mv yieldp yield new-start)
        (if firstp
            (if (< start end)
                (mv t start (1+ start))
              (mv nil 0 start))
          (b* ((jump (+ start stepm1)))
            (if (< jump end)
                (mv t jump (1+ jump))
              (mv nil 0 end)))))
       (new-stepby (value-variant
                    0
                    (list (mk-range new-start end)
                          (value-uint stepm1 (uint-type-usize))
                          (value-bool nil))))
       (new-frames (store-address address new-stepby frames))
       ((when (fty::reserrp new-frames)) (mv new-frames frames)))
    (mv (if yieldp
            (mk-some (value-uint yield (uint-type-usize)))
          (mk-none))
        new-frames)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mk-iter ((sref valuep) (pos acl2::natp))
  :returns (iter valuep)
  :short "Build a slice iterator value."
  (value-variant 0 (list (value-fix sref)
                         (value-uint (acl2::nfix pos) (uint-type-usize)))))

(define iter-fields ((value valuep))
  :returns (mv (okp booleanp)
               (sref valuep)
               (pos acl2::natp
                    :rule-classes (:rewrite :type-prescription)))
  :short "The slice reference and position of a slice iterator value."
  (b* (((unless (and (value-case value :variant)
                     (equal (value-variant->index value) 0)
                     (equal (len (value-variant->fields value)) 2)))
        (mv nil (irr-value) 0))
       (fields (value-variant->fields value))
       (sref (nth 0 fields))
       (posv (nth 1 fields))
       ((unless (and (value-case sref :slice-ref)
                     (value-case posv :uint)))
        (mv nil (irr-value) 0)))
    (mv t (value-fix sref) (value-uint->val posv)))
  ///

  (defret value-kind-of-iter-fields-sref
    (implies okp
             (equal (value-kind sref) :slice-ref))
    :hints (("Goal" :in-theory (enable iter-fields)))))

(define iter-next-value ((sref valuep) (pos acl2::natp))
  :guard (value-case sref :slice-ref)
  :returns (mv (yieldp booleanp) (elem-ref valuep) (new-iter valuep))
  :short "Advance a slice iterator, yielding a reference to
          the next element."
  (b* ((pos (acl2::nfix pos))
       ((unless (mbt (value-case sref :slice-ref)))
        (mv nil (irr-value) (irr-value)))
       ((unless (< pos (value-slice-ref->len sref)))
        (mv nil (irr-value) (mk-iter sref pos)))
       (elem-ref (value-ref
                  (address-add (value-slice-ref->address sref)
                               (path-elem-index
                                (+ (value-slice-ref->start sref) pos))))))
    (mv t elem-ref (mk-iter sref (1+ pos)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define shim-iter-next ((args value-listp) (frames frame-listp))
  :returns (mv (result value-resultp) (new-frames frame-listp))
  :short "Shim for slice @('Iter')/@('IterMut')'s @('next')."
  (b* ((frames (frame-list-fix frames))
       (args (value-list-fix args))
       ((unless (equal (len args) 1))
        (mv (fty::reserr (list :stuck :shim-arity)) frames))
       ((mv iter address) (shim-ref-arg (car args) frames))
       ((when (fty::reserrp iter)) (mv iter frames))
       ((mv okp sref pos) (iter-fields iter))
       ((unless okp)
        (mv (fty::reserr (list :stuck :not-a-slice-iterator)) frames))
       ((mv yieldp elem-ref new-iter) (iter-next-value sref pos))
       ((unless yieldp) (mv (mk-none) frames))
       (new-frames (store-address address new-iter frames))
       ((when (fty::reserrp new-frames)) (mv new-frames frames)))
    (mv (mk-some elem-ref) new-frames)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define shim-iterator-arg ((value valuep) (frames frame-listp))
  :returns (result value-resultp)
  :short "Coerce an iterator-position argument to an iterator value."
  :long
  (xdoc::topstring
   (xdoc::p
    "The iterator-consuming shims can receive
     an iterator value (a range, slice iterator, or adapter),
     which passes through unchanged,
     or a slice or array reference,
     which becomes a fresh iterator over its elements &mdash;
     the conversion that the standard library's
     @('IntoIterator') implementations perform
     inside @('zip') and in @('for') loops over references."))
  (b* ((value (value-fix value))
       ((when (value-case value :variant)) value)
       (sref (as-slice-window value frames))
       ((when (fty::reserrp sref)) sref))
    (mk-iter sref 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define shim-zip-next ((args value-listp) (frames frame-listp))
  :returns (mv (result value-resultp) (new-frames frame-listp))
  :short "Shim for @('Zip')'s @('next') over two slice iterators."
  (b* ((frames (frame-list-fix frames))
       (args (value-list-fix args))
       ((unless (equal (len args) 1))
        (mv (fty::reserr (list :stuck :shim-arity)) frames))
       ((mv zip address) (shim-ref-arg (car args) frames))
       ((when (fty::reserrp zip)) (mv zip frames))
       ((unless (and (value-case zip :variant)
                     (equal (value-variant->index zip) 0)
                     (equal (len (value-variant->fields zip)) 2)))
        (mv (fty::reserr (list :stuck :not-a-zip)) frames))
       (fields (value-variant->fields zip))
       ((mv okp-a sref-a pos-a) (iter-fields (nth 0 fields)))
       ((mv okp-b sref-b pos-b) (iter-fields (nth 1 fields)))
       ((unless (and okp-a okp-b))
        (mv (fty::reserr (list :stuck :not-a-zip)) frames))
       ((mv yieldp-a ref-a iter-a) (iter-next-value sref-a pos-a))
       ((mv yieldp-b ref-b iter-b) (iter-next-value sref-b pos-b))
       ((unless (and yieldp-a yieldp-b)) (mv (mk-none) frames))
       (new-zip (value-variant 0 (list iter-a iter-b)))
       (new-frames (store-address address new-zip frames))
       ((when (fty::reserrp new-frames)) (mv new-frames frames)))
    (mv (mk-some (value-tuple (list ref-a ref-b))) new-frames)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define shim-slice-index-range ((args value-listp)
                                (frames frame-listp)
                                (kind acl2::symbolp))
  :returns (mv (result value-resultp) (new-frames frame-listp))
  :short "Shim for slice indexing by
          @('Range'), @('RangeTo'), or @('RangeFrom'):
          a subwindow slice reference, with bounds panics."
  (b* ((frames (frame-list-fix frames))
       (args (value-list-fix args))
       ((unless (equal (len args) 2))
        (mv (fty::reserr (list :stuck :shim-arity)) frames))
       (sref (as-slice-window (car args) frames))
       ((when (fty::reserrp sref)) (mv sref frames))
       (len (value-slice-ref->len sref))
       (rangev (cadr args))
       ((unless (and (value-case rangev :variant)
                     (equal (value-variant->index rangev) 0)))
        (mv (fty::reserr (list :stuck :not-a-range)) frames))
       (fields (value-variant->fields rangev))
       ((mv okp lo hi)
        (case kind
          (:range (if (and (equal (len fields) 2)
                           (value-case (nth 0 fields) :uint)
                           (value-case (nth 1 fields) :uint))
                      (mv t
                          (value-uint->val (nth 0 fields))
                          (value-uint->val (nth 1 fields)))
                    (mv nil 0 0)))
          (:range-to (if (and (equal (len fields) 1)
                              (value-case (nth 0 fields) :uint))
                         (mv t 0 (value-uint->val (nth 0 fields)))
                       (mv nil 0 0)))
          (:range-from (if (and (equal (len fields) 1)
                                (value-case (nth 0 fields) :uint))
                           (mv t (value-uint->val (nth 0 fields)) len)
                         (mv nil 0 0)))
          (otherwise (mv nil 0 0))))
       ((unless okp)
        (mv (fty::reserr (list :stuck :not-a-range)) frames))
       ((unless (and (<= lo hi) (<= hi len)))
        (mv (fty::reserr (list :panic :slice-range-out-of-bounds lo hi len))
            frames)))
    (mv (value-slice-ref (value-slice-ref->address sref)
                         (+ (value-slice-ref->start sref) lo)
                         (- hi lo))
        frames))
  :guard-hints (("Goal" :in-theory (enable natp)))
  ;; the kind is a static dispatch symbol; no congruence needed
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-shim ((name acl2::stringp)
                   (args value-listp)
                   (frames frame-listp))
  :returns (mv (result value-resultp) (new-frames frame-listp))
  :short "Execute a standard library shim."
  :long
  (xdoc::topstring
   (xdoc::p
    "The shim names, listed in @(see *shim-names*),
     are canonical monomorphic names;
     the importer maps rustc's monomorphized names to them.
     Shims can read and write through reference arguments
     (hence the frame stack in and out),
     return references into arrays
     (indexing and iteration),
     and panic (slice bounds, unwrap of an error,
     explicit panics), reported as
     @(':panic') errors."))
  (b* ((name (acl2::str-fix name))
       (frames (frame-list-fix frames))
       (args (value-list-fix args))
       (arity-err (fty::reserr (list :stuck :shim-arity name))))
    (cond
     ((equal name "u32::wrapping_add")
      (b* (((unless (and (equal (len args) 2)
                         (value-case (nth 0 args) :uint)
                         (value-case (nth 1 args) :uint)
                         (uint-type-equiv (value-uint->type (nth 0 args))
                                          (value-uint->type (nth 1 args)))))
            (mv arity-err frames))
           (type (value-uint->type (nth 0 args))))
        (mv (value-uint (uint-wrap (+ (value-uint->val (nth 0 args))
                                      (value-uint->val (nth 1 args)))
                                   type)
                        type)
            frames)))
     ((equal name "u32::wrapping_sub")
      (b* (((unless (and (equal (len args) 2)
                         (value-case (nth 0 args) :uint)
                         (value-case (nth 1 args) :uint)
                         (uint-type-equiv (value-uint->type (nth 0 args))
                                          (value-uint->type (nth 1 args)))))
            (mv arity-err frames))
           (type (value-uint->type (nth 0 args))))
        (mv (value-uint (uint-wrap (- (value-uint->val (nth 0 args))
                                      (value-uint->val (nth 1 args)))
                                   type)
                        type)
            frames)))
     ((equal name "u32::rotate_right")
      (b* (((unless (and (equal (len args) 2)
                         (value-case (nth 0 args) :uint)
                         (value-case (nth 1 args) :uint)))
            (mv arity-err frames))
           (type (value-uint->type (nth 0 args))))
        (mv (value-uint (uint-rotate-right (value-uint->val (nth 0 args))
                                           (value-uint->val (nth 1 args))
                                           type)
                        type)
            frames)))
     ((equal name "u32::from_le_bytes")
      (b* (((unless (and (equal (len args) 1)
                         (value-case (nth 0 args) :array)))
            (mv arity-err frames))
           (bytes (value-array->elems (nth 0 args)))
           ((unless (equal (len bytes) 4))
            (mv (fty::reserr (list :stuck :from-le-bytes-arity)) frames))
           ((mv okp word) (values-le-word bytes))
           ((unless okp)
            (mv (fty::reserr (list :stuck :from-le-bytes-non-bytes))
                frames)))
        (mv (value-uint word (uint-type-u32)) frames)))
     ((equal name "u32::to_le_bytes")
      (b* (((unless (and (equal (len args) 1)
                         (value-case (nth 0 args) :uint)))
            (mv arity-err frames))
           (n (value-uint->val (nth 0 args))))
        (mv (value-array
             (list (value-uint (mod n 256) (uint-type-u8))
                   (value-uint (mod (floor n 256) 256) (uint-type-u8))
                   (value-uint (mod (floor n 65536) 256) (uint-type-u8))
                   (value-uint (mod (floor n 16777216) 256) (uint-type-u8))))
            frames)))
     ((equal name "slice::len")
      (b* (((unless (equal (len args) 1)) (mv arity-err frames))
           (sref (as-slice-window (car args) frames))
           ((when (fty::reserrp sref)) (mv sref frames)))
        (mv (value-uint (value-slice-ref->len sref) (uint-type-usize))
            frames)))
     ((or (equal name "slice::index")
          (equal name "slice::index_mut"))
      (b* (((unless (and (equal (len args) 2)
                         (value-case (nth 1 args) :uint)))
            (mv arity-err frames))
           (sref (as-slice-window (car args) frames))
           ((when (fty::reserrp sref)) (mv sref frames))
           (i (value-uint->val (nth 1 args)))
           ((unless (< i (value-slice-ref->len sref)))
            (mv (fty::reserr (list :panic :index-out-of-bounds i))
                frames)))
        (mv (value-ref (address-add (value-slice-ref->address sref)
                                    (path-elem-index
                                     (+ (value-slice-ref->start sref) i))))
            frames)))
     ((or (equal name "slice::index_range")
          (equal name "slice::index_range_mut"))
      (shim-slice-index-range args frames :range))
     ((or (equal name "slice::index_range_to")
          (equal name "slice::index_range_to_mut"))
      (shim-slice-index-range args frames :range-to))
     ((or (equal name "slice::index_range_from")
          (equal name "slice::index_range_from_mut"))
      (shim-slice-index-range args frames :range-from))
     ((equal name "slice::copy_from_slice")
      (b* (((unless (equal (len args) 2)) (mv arity-err frames))
           (dest (as-slice-window (nth 0 args) frames))
           ((when (fty::reserrp dest)) (mv dest frames))
           (src (as-slice-window (nth 1 args) frames))
           ((when (fty::reserrp src)) (mv src frames))
           ((unless (equal (value-slice-ref->len dest)
                           (value-slice-ref->len src)))
            (mv (fty::reserr (list :panic :copy-from-slice-length-mismatch))
                frames))
           (values (slice-window-elems src frames))
           ((when (fty::reserrp values)) (mv values frames))
           (new-frames (slice-window-write dest values frames))
           ((when (fty::reserrp new-frames)) (mv new-frames frames)))
        (mv (value-unit) new-frames)))
     ((equal name "slice::try_into_array4")
      (b* (((unless (equal (len args) 1)) (mv arity-err frames))
           (sref (as-slice-window (car args) frames))
           ((when (fty::reserrp sref)) (mv sref frames))
           ((unless (equal (value-slice-ref->len sref) 4))
            (mv (value-variant 1 (list (value-unit))) frames))
           (values (slice-window-elems sref frames))
           ((when (fty::reserrp values)) (mv values frames)))
        (mv (value-variant 0 (list (value-array values))) frames)))
     ((equal name "Result::unwrap")
      (b* (((unless (and (equal (len args) 1)
                         (value-case (nth 0 args) :variant)))
            (mv arity-err frames))
           (result (nth 0 args))
           ((unless (and (equal (value-variant->index result) 0)
                         (equal (len (value-variant->fields result)) 1)))
            (mv (fty::reserr (list :panic :unwrap-of-err)) frames)))
        (mv (value-fix (nth 0 (value-variant->fields result))) frames)))
     ((equal name "Range::into_iter")
      (b* (((unless (equal (len args) 1)) (mv arity-err frames)))
        (mv (shim-iterator-arg (car args) frames) frames)))
     ((equal name "Range::next")
      (shim-range-next args frames nil))
     ((equal name "Range::next_back")
      (shim-range-next args frames t))
     ((equal name "Iterator::rev")
      (b* (((unless (equal (len args) 1)) (mv arity-err frames)))
        (mv (value-fix (car args)) frames)))
     ((equal name "Rev::next")
      (shim-range-next args frames t))
     ((equal name "Iterator::step_by")
      (b* (((unless (and (equal (len args) 2)
                         (value-case (nth 1 args) :uint)))
            (mv arity-err frames))
           (step (value-uint->val (nth 1 args)))
           ((when (equal step 0))
            (mv (fty::reserr (list :panic :step-by-zero)) frames)))
        (mv (value-variant 0
                           (list (value-fix (nth 0 args))
                                 (value-uint (1- step) (uint-type-usize))
                                 (value-bool t)))
            frames)))
     ((equal name "StepBy::next")
      (shim-step-by-next args frames))
     ((or (equal name "slice::iter")
          (equal name "slice::iter_mut"))
      (b* (((unless (equal (len args) 1)) (mv arity-err frames))
           (sref (as-slice-window (car args) frames))
           ((when (fty::reserrp sref)) (mv sref frames)))
        (mv (mk-iter sref 0) frames)))
     ((or (equal name "Iter::next")
          (equal name "IterMut::next"))
      (shim-iter-next args frames))
     ((equal name "Iterator::zip")
      (b* (((unless (equal (len args) 2)) (mv arity-err frames))
           (iter-a (shim-iterator-arg (nth 0 args) frames))
           ((when (fty::reserrp iter-a)) (mv iter-a frames))
           (iter-b (shim-iterator-arg (nth 1 args) frames))
           ((when (fty::reserrp iter-b)) (mv iter-b frames)))
        (mv (value-variant 0 (list iter-a iter-b)) frames)))
     ((equal name "Zip::next")
      (shim-zip-next args frames))
     ((equal name "u32::bitxor_assign")
      (b* (((unless (equal (len args) 2)) (mv arity-err frames))
           ((mv target address) (shim-ref-arg (nth 0 args) frames))
           ((when (fty::reserrp target)) (mv target frames))
           (rhs (nth 1 args))
           (rhs (if (value-case rhs :ref)
                    (b* (((mv loaded &) (shim-ref-arg rhs frames)))
                      loaded)
                  (value-fix rhs)))
           ((when (fty::reserrp rhs)) (mv rhs frames))
           ((unless (and (value-case target :uint)
                         (value-case rhs :uint)
                         (uint-type-equiv (value-uint->type target)
                                          (value-uint->type rhs))))
            (mv (fty::reserr (list :stuck :bitxor-assign-mistype)) frames))
           (type (value-uint->type target))
           (new-frames
            (store-address address
                           (value-uint (uint-wrap
                                        (logxor (value-uint->val target)
                                                (value-uint->val rhs))
                                        type)
                                       type)
                           frames))
           ((when (fty::reserrp new-frames)) (mv new-frames frames)))
        (mv (value-unit) new-frames)))
     ((or (equal name "core::panicking::panic")
          (equal name "core::panicking::assert_failed"))
      (mv (fty::reserr (list :panic :explicit-panic name)) frames))
     (t (mv (fty::reserr (list :stuck :unknown-shim name)) frames)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *shim-names*
  :short "The names of the standard library shims."
  (list "u32::wrapping_add"
        "u32::wrapping_sub"
        "u32::rotate_right"
        "u32::from_le_bytes"
        "u32::to_le_bytes"
        "slice::len"
        "slice::index"
        "slice::index_mut"
        "slice::index_range"
        "slice::index_range_mut"
        "slice::index_range_to"
        "slice::index_range_to_mut"
        "slice::index_range_from"
        "slice::index_range_from_mut"
        "slice::copy_from_slice"
        "slice::try_into_array4"
        "Result::unwrap"
        "Range::into_iter"
        "Range::next"
        "Range::next_back"
        "Iterator::rev"
        "Rev::next"
        "Iterator::step_by"
        "StepBy::next"
        "slice::iter"
        "slice::iter_mut"
        "Iter::next"
        "IterMut::next"
        "Iterator::zip"
        "Zip::next"
        "u32::bitxor_assign"
        "core::panicking::panic"
        "core::panicking::assert_failed"))

(define shimp ((name acl2::stringp))
  :returns (yes/no booleanp)
  :short "Check if a name is a standard library shim's."
  (and (member-equal (acl2::str-fix name) *shim-names*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum stepout
  :short "Fixtype of step outcomes."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result of one step of the machine:
     a next state, or a final outcome
     (see @(see mir-interpreter) for the outcome taxonomy)."))
  (:next ((mstate mstate)))
  (:done ((value value)))
  (:panic ((info any)))
  (:ub ((info any)))
  (:stuck ((info any)))
  :pred stepoutp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stepout-from-reserr ((err fty::reserrp))
  :returns (out stepoutp)
  :short "Turn an evaluation error into a step outcome."
  :long
  (xdoc::topstring
   (xdoc::p
    "Evaluation errors carry information starting with
     @(':ub'), @(':panic') (from the standard library shims),
     or @(':stuck'); anything else is a stuck state
     (it indicates an interpreter-internal convention violation)."))
  (b* ((info (fty::reserr->info err)))
    (cond ((and (consp info)
                (eq (car info) :ub))
           (stepout-ub info))
          ((and (consp info)
                (eq (car info) :panic))
           (stepout-panic info))
          (t (stepout-stuck info)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define frame-jump ((target acl2::natp) (frame framep))
  :returns (new-frame framep)
  :short "Continue a frame at the start of a block."
  (change-frame frame
                :cur-block (acl2::nfix target)
                :cur-stmt 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define switch-pick ((val acl2::integerp)
                     (values acl2::integer-listp)
                     (targets acl2::nat-listp)
                     (otherwise acl2::natp))
  :returns (target acl2::natp)
  :short "Pick the target block of a switch."
  (cond ((or (endp values) (endp targets))
         (acl2::nfix otherwise))
        ((= (acl2::ifix val) (acl2::ifix (car values)))
         (acl2::nfix (car targets)))
        (t (switch-pick val (cdr values) (cdr targets) otherwise)))
  ;; the automatic fix congruences do not prove for
  ;; this parallel two-list recursion (cf. ../syntax/tokenizer.lisp)
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-call-locals ((args value-listp) (num-locals acl2::natp))
  :returns (locals value-option-listp)
  :short "Build the initial locals of a callee frame."
  :long
  (xdoc::topstring
   (xdoc::p
    "Local 0 (the return place) starts uninitialized,
     locals 1 through the argument count hold the arguments,
     and the remaining locals start uninitialized.
     The caller checks that the counts fit before calling this."))
  (cons nil
        (append (value-list-fix args)
                (acl2::repeat (acl2::nfix (- (acl2::nfix num-locals)
                                             (1+ (len args))))
                              nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-terminator ((term terminatorp)
                         (mstate mstatep)
                         (program mir-programp))
  :guard (consp (mstate->frames mstate))
  :returns (out stepoutp)
  :short "Execute the terminator of the current block."
  (b* ((frames (mstate->frames mstate))
       ((unless (mbt (consp frames)))
        (stepout-stuck (list :stuck :empty-frame-stack)))
       (frame (car frames)))
    (terminator-case
     term
     :goto
     (stepout-next (change-mstate mstate
                                  :frames (cons (frame-jump term.target frame)
                                                (cdr frames))))
     :switch-int
     (b* ((discr (eval-operand term.discr frames))
          ((when (fty::reserrp discr)) (stepout-from-reserr discr))
          ((unless (value-scalarp discr))
           (stepout-stuck (list :stuck :switch-on-non-scalar)))
          (int (value-scalar->int discr))
          ((switch-targets targets) term.targets)
          (target (switch-pick int
                               targets.values
                               targets.targets
                               targets.otherwise)))
       (stepout-next (change-mstate mstate
                                    :frames (cons (frame-jump target frame)
                                                  (cdr frames)))))
     :return
     (b* (((unless (local-in-range-p 0 frame))
           (stepout-stuck (list :stuck :no-return-local)))
          (value (read-local 0 frame))
          ((unless value)
           (stepout-ub (list :ub :return-of-uninitialized-value)))
          ((when (endp (cdr frames)))
           (stepout-done value))
          (rest (write-place (frame->dest frame) value (cdr frames)))
          ((when (fty::reserrp rest)) (stepout-from-reserr rest))
          ((unless (consp rest))
           (stepout-stuck (list :stuck :empty-frame-stack)))
          (caller (frame-jump (frame->target frame) (car rest))))
       (stepout-next (change-mstate mstate
                                    :frames (cons caller (cdr rest)))))
     :call
     (b* ((func (eval-operand term.func frames))
          ((when (fty::reserrp func)) (stepout-from-reserr func))
          ((unless (value-case func :fn))
           (stepout-stuck (list :stuck :call-of-non-function)))
          (name (value-fn->name func))
          ((unless (omap::assoc name (mir-program->funs program)))
           ;; a function body in the program takes precedence;
           ;; otherwise a standard library shim may apply
           (if (shimp name)
               (b* ((args (eval-operand-list term.args frames))
                    ((when (fty::reserrp args)) (stepout-from-reserr args))
                    ((mv result new-frames) (exec-shim name args frames))
                    ((when (fty::reserrp result))
                     (stepout-from-reserr result))
                    (final (write-place term.dest result new-frames))
                    ((when (fty::reserrp final))
                     (stepout-from-reserr final))
                    ((unless (consp final))
                     (stepout-stuck (list :stuck :empty-frame-stack)))
                    (top (frame-jump term.target (car final))))
                 (stepout-next (change-mstate mstate
                                              :frames (cons top
                                                            (cdr final)))))
             (stepout-stuck (list :stuck :call-of-unknown-function name))))
          (body (omap::lookup name (mir-program->funs program)))
          (args (eval-operand-list term.args frames))
          ((when (fty::reserrp args)) (stepout-from-reserr args))
          ((body body) body)
          ((unless (and (equal (len args) body.arg-count)
                        (<= (1+ body.arg-count) (len body.locals))))
           (stepout-stuck (list :stuck :call-arity-mismatch name)))
          (callee (make-frame :fn name
                              :locals (make-call-locals args
                                                        (len body.locals))
                              :cur-block 0
                              :cur-stmt 0
                              :dest term.dest
                              :target term.target)))
       (stepout-next (change-mstate mstate
                                    :frames (cons callee frames))))
     :assert
     (b* ((cond (eval-operand term.cond frames))
          ((when (fty::reserrp cond)) (stepout-from-reserr cond))
          ((unless (value-case cond :bool))
           (stepout-stuck (list :stuck :assert-of-non-boolean)))
          (holds (equal (value-bool->val cond) term.expected))
          ((unless holds)
           (stepout-panic (list :assertion-failed))))
       (stepout-next (change-mstate mstate
                                    :frames (cons (frame-jump term.target
                                                              frame)
                                                  (cdr frames)))))
     :drop
     (stepout-next (change-mstate mstate
                                  :frames (cons (frame-jump term.target frame)
                                                (cdr frames))))
     :abort
     (stepout-panic (list :abort term.name))
     :unreachable
     (stepout-ub (list :ub :reached-unreachable)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mstep ((mstate mstatep) (program mir-programp))
  :returns (out stepoutp)
  :short "One step of the machine:
          execute the next statement or terminator
          of the top frame."
  (b* ((frames (mstate->frames mstate))
       ((when (endp frames))
        (stepout-stuck (list :stuck :empty-frame-stack)))
       (frame (car frames))
       ((frame frame) frame)
       ((unless (omap::assoc frame.fn (mir-program->funs program)))
        (stepout-stuck (list :stuck :unknown-function frame.fn)))
       (body (omap::lookup frame.fn (mir-program->funs program)))
       (blocks (body->blocks body))
       ((unless (< frame.cur-block (len blocks)))
        (stepout-stuck (list :stuck :block-out-of-range frame.cur-block)))
       (block1 (nth frame.cur-block blocks))
       (stmts (basic-block->statements block1))
       ((when (< frame.cur-stmt (len stmts)))
        (b* ((new-frames (exec-statement (nth frame.cur-stmt stmts) frames))
             ((when (fty::reserrp new-frames))
              (stepout-from-reserr new-frames))
             ((unless (consp new-frames))
              (stepout-stuck (list :stuck :empty-frame-stack)))
             (new-top (change-frame (car new-frames)
                                    :cur-stmt (1+ frame.cur-stmt))))
          (stepout-next (change-mstate mstate
                                       :frames (cons new-top
                                                     (cdr new-frames))))))
       ((unless (= frame.cur-stmt (len stmts)))
        (stepout-stuck (list :stuck :statement-index-out-of-range))))
    (exec-terminator (basic-block->terminator block1) mstate program)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum runout
  :short "Fixtype of run outcomes."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result of running the machine to completion
     (or to fuel exhaustion, which carries the state reached,
     for resumption and debugging)."))
  (:done ((value value)))
  (:panic ((info any)))
  (:ub ((info any)))
  (:stuck ((info any)))
  (:limit ((mstate mstate)))
  :pred runoutp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mrun ((fuel acl2::natp) (mstate mstatep) (program mir-programp))
  :returns (out runoutp)
  :short "Run the machine for at most a given number of steps."
  (b* (((when (zp fuel)) (runout-limit mstate))
       (out (mstep mstate program)))
    (stepout-case out
                  :next (mrun (1- fuel) out.mstate program)
                  :done (runout-done out.value)
                  :panic (runout-panic out.info)
                  :ub (runout-ub out.info)
                  :stuck (runout-stuck out.info)))
  ;; the automatic fix congruence for the fuel does not prove
  ;; for this recursion (cf. ../syntax/tokenizer.lisp)
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define run-fn ((name acl2::stringp)
                (args value-listp)
                (program mir-programp)
                (fuel acl2::natp))
  :returns (out runoutp)
  :short "Run a named function of a program on argument values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level entry point:
     it builds the initial one-frame state for the function
     (checking that the argument count matches)
     and runs the machine.
     The bottom frame's caller-continuation components
     are irrelevant witnesses."))
  (b* ((name (acl2::str-fix name))
       (args (value-list-fix args))
       (program (mir-program-fix program))
       (fuel (acl2::nfix fuel))
       ((unless (omap::assoc name (mir-program->funs program)))
        (runout-stuck (list :stuck :unknown-function name)))
       (body (omap::lookup name (mir-program->funs program)))
       ((body body) body)
       ((unless (and (equal (len args) body.arg-count)
                     (<= (1+ body.arg-count) (len body.locals))))
        (runout-stuck (list :stuck :arity-mismatch)))
       (frame (make-frame :fn name
                          :locals (make-call-locals args (len body.locals))
                          :cur-block 0
                          :cur-stmt 0
                          :dest (irr-place)
                          :target 0)))
    (mrun fuel (make-mstate :frames (list frame)) program)))
