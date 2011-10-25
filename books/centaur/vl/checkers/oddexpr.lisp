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
(include-book "../transforms/xf-sizing")
(include-book "../mlib/fmt")
(local (include-book "../util/arithmetic"))


; Rough code for finding expressions that might have precedence problems.
;
; Consider the expression a & b < c.  Due to the Verilog precedence rules, this
; gets parsed as a & (b < c).  Well, that might be quite surprising.  We try to
; look for expressions like this and, unless the code contains explicit parens
; around the (b < c) part, we issue a warning that it might not have the
; expected precedence.
;
; This has found a few good bugs!

(defsection vl-expr-probable-selfsize

; This returns a size or nil for failure.  There's no reason to believe the
; size it returns will be the eventual size of the expression because size
; propagation hasn't been taken into account; in fact we may just fail and
; return nil for a number of reasons (for instance the wire ranges may not be
; resolved yet), there's no way to get the failure reason.
;
; On the other hand, I think it should be the case that the final size of the
; expression will always be at least as much as this selfsize, if it returns a
; non-nil value.  And we can use this before resolving ranges, etc., which
; makes it useful for simple linting.

  (defconst *fake-modelement*
    (make-vl-netdecl :name "Fake module element"
                     :type :vl-wire
                     :loc *vl-fakeloc*))

  (defund vl-expr-probable-selfsize (x mod ialist)
    (declare (xargs :guard (and (vl-expr-p x)
                                (vl-module-p mod)
                                (equal ialist (vl-moditem-alist mod)))))
    (b* (((mv & size)
          (vl-expr-selfsize x mod ialist *fake-modelement* nil)))
      size))

  (local (in-theory (enable vl-expr-probable-selfsize)))

  (defthm vl-maybe-natp-of-vl-expr-probable-selfsize
    (vl-maybe-natp (vl-expr-probable-selfsize x mod ialist))
    :rule-classes :type-prescription))


; -----------------------------------------------------------------------------
;
;                    Precedence-Error Prone Expressions
;
; -----------------------------------------------------------------------------

(defun vl-odd-binop-class (x)
  ;; Groups binary operators into classes
  (declare (xargs :guard (vl-op-p x)))
  (case x
    ((:vl-binary-times :vl-binary-div :vl-binary-mod :vl-binary-power)
     :mult-class)
    ((:vl-binary-plus)
     :plus-class)
    ((:vl-binary-minus)
     :minus-class)
    ((:vl-binary-shl :vl-binary-shr :vl-binary-ashl :vl-binary-ashr)
     :shift-class)
    ((:vl-binary-lt :vl-binary-lte :vl-binary-gt :vl-binary-gte)
     :rel-class)
    ((:vl-binary-eq :vl-binary-neq)
     :cmp-class)
    ((:vl-binary-ceq :vl-binary-cne)
     :ceq-class)
    ((:vl-binary-bitand)
     :bitand-class)
    ((:vl-binary-xor :vl-binary-xnor)
     :xor-class)
    ((:vl-binary-bitor)
     :bitor-class)
    ((:vl-binary-logand)
     :logand-class)
    ((:vl-binary-logor)
     :logor-class)
    (otherwise
     nil)))

(defconst *vl-odd-binops-table*

; This is the main table that controls whether we warn about certain
; combinations of binary operators.  If you want to NOT issue a warning about a
; particular combination of operators, then just leave it out of the table.
;
; The keys in the table have the form (outer-op . inner-op).  Loosely speaking,
; a key like
;
;    (:shift-class . :plus-class)
;
; matches expressions of the following forms:
;
;    1. (a + b) << c
;    2. a << (b + c)
;
; Whereas a key like (:plus-class . :shift-class) would match expressions of
; the following forms:
;
;    1. (a << b) + c
;    2. a + (b << c)
;
; In other words, the inner-op is the "sub" operation, and the outer-op is the
; "top" operation.
;
; Note that we never have keys where the outer-op has a higher precedence than
; the inner operation, such as (:plus-class . :shift-class).  Why not?
;
; Because of the precedence rules, a << b + c gets parsed as a << (b + c).  In
; other words, the only reason we'd ever get an expression that matches
; (:plus-class . :shift-class) is that the user explicitly put in their own
; parens around the shift operator.  If they've done that, then they are
; explicitly saying what precedence they want, and there's no chance they are
; going to be surprised by Verilog's precedence rules.  This same reasoning
; holds for any combination of operators where the outer op is higher
; precedence than the inner op.


  '(

; PLUS OPERATOR.
;
;   a op1 b op2 c |  parsed as        bad-type?   error-prone?
; ----------------+----------------------------------------------------------------------------------------------------
;   a + b + c     |  (a + b) + c      no          no
;   a + b - c     |  (a + b) - c      no          no
;   a + b << c    |  (a + b) << c     no          yes              warn
;   a + b < c     |  (a + b) < c      no          no
;   a + b == c    |  (a + b) == c     no          no
;   a + b & c     |  (a + b) & c      no          maybe            } I was worried these would be too noisy, but they
;   a + b ^ c     |  (a + b) ^ c      no          maybe            } seem not to cause too much trouble.
;   a + b | c     |  (a + b) | c      no          maybe            }
;   a + b && c    |  (a + b) && c     yes         --               warn
;   a + b || c    |  (a + b) || c     yes         --               warn
; ----------------+----------------------------------------------------------------------------------------------------

    ;; (outer-op     .  inner-op)    .   action
    ((:shift-class   . :plus-class)  .   :check-precedence)
    ((:bitand-class  . :plus-class)  .   :check-precedence)
    ((:xor-class     . :plus-class)  .   :check-precedence)
    ((:bitor-class   . :plus-class)  .   :check-precedence)
    ((:logand-class  . :plus-class)  .   :check-type)
    ((:logor-class   . :plus-class)  .   :check-type)



; Special case for Plus and Minus.
;
;   1. a + b - c seems fine.
;   2. a - b + c gets parsed as (a - b) + c, which might occasionally be misunderstood.
;
; So, we don't want to warn about #1, but we do want to warn about #2.
; In this case, the outer-op is + and the inner-op is minus.
; We use a special action to cover this one odd case.

    ((:plus-class . :minus-class) . :check-precedence-plusminus)


; MINUS OPERATOR.
;
;   a op1 b op2 c |  parsed as        bad-type?   error-prone?
; ----------------+----------------------------------------------------------------------------------------------------
;   a - b + c     |  (a - b) + c      see above
;   a - b - c     |  (a - b) - c      no          yes              warn
;   a - b << c    |  (a - b) << c     no          yes              warn
;   a - b < c     |  (a - b) < c      no          no
;   a - b == c    |  (a - b) == c     no          no
;   a - b & c     |  (a - b) & c      no          yes              warn
;   a - b ^ c     |  (a - b) ^ c      no          yes              warn
;   a - b | c     |  (a - b) | c      no          yes              warn
;   a - b && c    |  (a - b) && c     yes         --               warn
;   a - b || c    |  (a - b) || c     yes         --               warn
; ----------------+----------------------------------------------------------------------------------------------------

    ;; (outer-op     .  inner-op)    .   action
    ((:minus-class   . :minus-class)  . :check-precedence)
    ((:shift-class   . :minus-class)  . :check-precedence)
    ((:bitand-class  . :minus-class)  . :check-precedence)
    ((:xor-class     . :minus-class)  . :check-precedence)
    ((:bitor-class   . :minus-class)  . :check-precedence)
    ((:logand-class  . :minus-class)  . :check-type)
    ((:logor-class   . :minus-class)  . :check-type)


; SHIFT OPERATORS. (<< >> <<< >>>)
;
;   a op1 b op2 c |  parsed as        bad-type?   error-prone?
; ----------------+----------------------------------------------------------------------------------
;   a << b + c    |  a << (b + c)     see above
;   a << b - c    |  a << (b - c)     see above
;   a << b << c   |  (a << b) << c    no          yes              warn
;   a << b < c    |  (a << b) < c     no          no
;   a << b == c   |  (a << b) == c    no          no
;   a << b & c    |  (a << b) & c     no          yes              warn
;   a << b ^ c    |  (a << b) ^ c     no          yes              warn
;   a << b | c    |  (a << b) | c     no          yes              warn
;   a << b && c   |  (a << b) && c    yes         --               warn
;   a << b || c   |  (a << b) || c    yes         --               warn
; ----------------+----------------------------------------------------------------------------------

    ;; (outer-op     . inner-op)      . action
    ((:shift-class   . :shift-class)  . :check-precedence)
    ((:bitand-class  . :shift-class)  . :check-precedence)
    ((:xor-class     . :shift-class)  . :check-precedence)
    ((:bitor-class   . :shift-class)  . :check-precedence)
    ((:logand-class  . :shift-class)  . :check-type)
    ((:logor-class   . :shift-class)  . :check-type)


; RELATIONAL OPERATORS. (< <= > >=)
;
;   a op1 b op2 c |  parsed as        bad-type?   error-prone?
; ----------------+----------------------------------------------------------------------------------
;   a < b + c     |  a < (b + c)      see above
;   a < b - c     |  a < (b - c)      see above
;   a < b << c    |  a < (b << c)     see above
;   a < b < c     |  (a < b) < c      yes         --               warn
;   a < b == c    |  (a < b) == c     yes         --               warn
;   a < b & c     |  (a < b) & c      yes         yes              warn especially if sizeof(c) > 1
;   a < b ^ c     |  (a < b) ^ c      yes         yes              warn especially if sizeof(c) > 1
;   a < b | c     |  (a < b) | c      yes         yes              warn especially if sizeof(c) > 1
;   a < b && c    |  (a < b) && c     no          no
;   a < b || c    |  (a < b) || c     no          no
; ----------------+----------------------------------------------------------------------------------

    ;; (outer-op     .  inner-op)    . action
    ((:rel-class     . :rel-class)   . :check-type)
    ((:cmp-class     . :rel-class)   . :check-type)
    ((:bitand-class  . :rel-class)   . :check-type-unless-topargs-boolean)  ; permit (a < b) & c when c seems boolean
    ((:xor-class     . :rel-class)   . :check-type)
    ((:bitor-class   . :rel-class)   . :check-type-unless-topargs-boolean)  ; permit (a < b) | c when c seems boolean


; COMPARISON OPERATORS. (== !=)
;
;   a op1 b op2 c |  parsed as        bad-type?   error-prone?
; ----------------+----------------------------------------------------------------------------------
;   a == b + c    |  a == (b + c)     see above
;   a == b - c    |  a == (b - c)     see above
;   a == b << c   |  a == (b << c)    see above
;   a == b < c    |  a == (b < c)     see above
;   a == b == c   |  (a == b) == c    yes         --               warn
;   a == b & c    |  (a == b) & c     maybe       yes              warn especially if sizeof(c) > 1
;   a == b ^ c    |  (a == b) ^ c     maybe       yes              warn especially if sizeof(c) > 1
;   a == b | c    |  (a == b) | c     maybe       yes              warn especially if sizeof(c) > 1
;   a == b && c   |  (a == b) && c    no          no
;   a == b || c   |  (a == b) || c    no          no
; ----------------+----------------------------------------------------------------------------------

    ;; (outer-op    .  inner-op)      . action
    ((:cmp-class    .  :cmp-class)    . :check-type)
    ((:bitand-class .  :cmp-class)    . :check-type-unless-topargs-boolean)  ; permit (a == b) & c when c seems boolean
    ((:xor-class    .  :cmp-class)    . :check-type)
    ((:bitor-class  .  :cmp-class)    . :check-type-unless-topargs-boolean)  ; permit (a == b) | c when c seems boolean


; BITWISE AND. (&)
;
;   a op1 b op2 c |  parsed as        bad-type?   error-prone?
; ----------------+----------------------------------------------------------------------------------
;   a & b + c     |  a & (b + c)      see above
;   a & b - c     |  a & (b - c)      see above
;   a & b << c    |  a & (b << c)     see above
;   a & b < c     |  a & (b < c)      see above
;   a & b == c    |  a & (b == c)     see above
;   a & b & c     |  (a & b) & c      no          no
;   a & b ^ c     |  (a & b) ^ c      no          maybe            warn?
;   a & b | c     |  (a & b) | c      no          no
;   a & b && c    |  (a & b) && c     yes         --               warn
;   a & b || c    |  (a & b) || c     yes         --               warn
; ----------------+----------------------------------------------------------------------------------

    ;; (outer-op    .  inner-op)      . action
    ((:xor-class    .  :bitand-class) . :check-precedence)   ; maybe too frequent
    ((:logand-class .  :bitand-class) . :check-type-unless-topargs-boolean) ; permit a && (b & c) when args are one bit
    ((:logor-class  .  :bitand-class) . :check-type-unless-topargs-boolean) ; permit a || (b & c) when args are one bit



; BITWISE XOR. (^)
;
;   a op1 b op2 c |  parsed as        bad-type?   error-prone?
; ----------------+----------------------------------------------------------------------------------
;   a ^ b + c     |  a ^ (b + c)      see above
;   a ^ b - c     |  a ^ (b - c)      see above
;   a ^ b << c    |  a ^ (b << c)     see above
;   a ^ b < c     |  a ^ (b < c)      see above
;   a ^ b == c    |  a ^ (b == c)     see above
;   a ^ b & c     |  a ^ (b & c)      see above
;   a ^ b ^ c     |  (a ^ b) ^ c      no          no
;   a ^ b | c     |  (a ^ b) | c      no          yes
;   a ^ b && c    |  (a ^ b) && c     yes         --
;   a ^ b || c    |  (a ^ b) || c     yes         --
; ----------------+----------------------------------------------------------------------------------

    ;; (outer-op    .  inner-op)      . action
    ((:logand-class .  :xor-class)    . :check-type)
    ((:logor-class  .  :xor-class)    . :check-type)


; BITWISE OR. (|)
;
;   a op1 b op2 c |  parsed as        bad-type?   error-prone?
; ----------------+----------------------------------------------------------------------------------
;   a | b + c     |  a | (b + c)      see above
;   a | b - c     |  a | (b - c)      see above
;   a | b << c    |  a | (b << c)     see above
;   a | b < c     |  a | (b < c)      see above
;   a | b == c    |  a | (b == c)     see above
;   a | b & c     |  a | (b & c)      see above
;   a | b ^ c     |  a | (b ^ c)      see above
;   a | b | c     |  (a | b) | c      no          no
;   a | b && c    |  (a | b) && c     yes         --
;   a | b || c    |  (a | b) || c     yes         --
; ----------------+----------------------------------------------------------------------------------

    ;; (outer-op    .  inner-op)      . action
    ((:logand-class .  :bitor-class)  . :check-type-unless-topargs-boolean) ; permit a && (b | c) when args are one bit
    ((:logor-class  .  :bitor-class)  . :check-type-unless-topargs-boolean) ; permit a || (b | c) when args are one bit


; LOGICAL AND (&&)
;
;   a op1 b op2 c |  parsed as        bad-type?   error-prone?
; ----------------+----------------------------------------------------------------------------------
;   a && b + c    |  a && (b + c)     see above
;   a && b - c    |  a && (b - c)     see above
;   a && b << c   |  a && (b << c)    see above
;   a && b < c    |  a && (b < c)     see above
;   a && b == c   |  a && (b == c)    see above
;   a && b & c    |  a && (b & c)     see above
;   a && b ^ c    |  a && (b ^ c)     see above
;   a && b | c    |  a && (b | c)     see above
;   a && b && c   |  (a && b) && c    no         no
;   a && b || c   |  (a && b) || c    no         maybe?
; ----------------+----------------------------------------------------------------------------------

    ((:logor-class . :logand-class) . :check-precedence)

; LOGICAL OR (||)
;
;   a op1 b op2 c |  parsed as        bad-type?   error-prone?
; ----------------+----------------------------------------------------------------------------------
;   a || b + c    |  a || (b + c)     see above
;   a || b - c    |  a || (b - c)     see above
;   a || b << c   |  a || (b << c)    see above
;   a || b < c    |  a || (b < c)     see above
;   a || b == c   |  a || (b == c)    see above
;   a || b & c    |  a || (b & c)     see above
;   a || b ^ c    |  a || (b ^ c)     see above
;   a || b | c    |  a || (b | c)     see above
;   a || b && c   |  a || (b && c)    see above
;   a || b || c   |  (a || b) || c    no          no
; ----------------+----------------------------------------------------------------------------------

    ))




; Note.  Any particular binary expression, say P OP Q, might have sub-structure in
; either the P argument or in the Q argument.  To deal with this, we call this
; function twice: first with (OP P Q) and FLIPPED=NIL, then with (OP Q P) and
; FLIPPED=T.
;
; The first argument, A, we regard as the "simple" argument; we don't try to
; decompose it any more.  However, we try to match X against B OP2 C.  Then, we
; see if we think the sequence A op (B op2 C) seems reasonable.

(defund vl-warn-odd-binary-expression-main (op1 a x flipped mod ialist)
  (declare (xargs :guard (and (vl-op-p op1)
                              (vl-expr-p a)
                              (vl-expr-p x)
                              (booleanp flipped)
                              (vl-module-p mod)
                              (equal ialist (vl-moditem-alist mod)))
                  :guard-debug t)
           (ignorable a flipped))
  (b* (((when (or (vl-fast-atom-p x)
                  (not (eql (vl-op-arity (vl-nonatom->op x)) 2))))
        nil)
       (op2        (vl-nonatom->op x))
       (op1-class  (vl-odd-binop-class op1))
       (op2-class  (vl-odd-binop-class op2))
       (key        (cons op1-class op2-class))
       (look       (assoc-equal key *vl-odd-binops-table*))
       ((unless look)
        nil))
    (case (cdr look)
      ((:check-precedence)
       ;; We've run into something like a + b << c which parses in a way that
       ;; might sometimes be surprising, viz. (a + b) << c.  We want to check
       ;; whether there are explicit parens around the sub-op (op2).  If so,
       ;; this seems to be what the user wants; else issue a warning.
       (if (assoc-equal "VL_EXPLICIT_PARENS" (vl-nonatom->atts x))
           nil
         :check-precedence))

      (:check-type
       ;; Hrmn.  Well, even in the case of type errors, parens seem to be pretty
       ;; indicative that the designer wants to do something weird.
       (if (assoc-equal "VL_EXPLICIT_PARENS" (vl-nonatom->atts x))
           nil
         :check-type))

      (:check-type-unless-topargs-boolean
       (b* (((when (assoc-equal "VL_EXPLICIT_PARENS" (vl-nonatom->atts x)))
             nil)
            (asize (vl-expr-probable-selfsize a mod ialist))
            (xsize (vl-expr-probable-selfsize x mod ialist))
            ((when (and (or (not asize) (eql asize 1))
                        (or (not xsize) (eql xsize 1))))
             ;; Skip it since args are boolean or there was some error determining
             ;; their sizes.
             nil))
         :check-type))

      ((:check-precedence-plusminus)
       ;; Special case for plus of minus.  We want to warn about (a - b) + c without
       ;; explicit parens.  We know OP1 is + and OP2 is -.
       ;;
       ;; If FLIPPED=NIL, the expression we found was A + (B - C).  We know there must
       ;; be explicit parens or it wouldn't have gotten parsed this way, so there's
       ;; nothing to do.
       ;;
       ;; If FLIPPED=T, the expression we found was (B - C) + A.  This is the case we
       ;; want to warn about, unless there were explicit parens around (B - C).
       (if (and flipped
                (not (assoc-equal "VL_EXPLICIT_PARENS" (vl-nonatom->atts x))))
           :check-precedence
         nil))

      (nil
       nil)

      (otherwise
       (er hard? 'vl-warn-odd-binary-expression-main
           "Unexpected action type ~x0.~%" (cdr look))))))








(mutual-recursion

 (defun vl-warn-odd-binary-expression (x mod ialist)
   (declare (xargs :guard (and (vl-expr-p x)
                               (vl-module-p mod)
                               (equal ialist (vl-moditem-alist mod)))
                   :measure (vl-expr-count x)))
   (b* (((when (vl-fast-atom-p x))
         nil)
        (op    (vl-nonatom->op x))
        (arity (vl-op-arity op))
        (args  (vl-nonatom->args x))
        ((unless (eql arity 2))
         (vl-warn-odd-binary-expression-list args mod ialist))
        ((list a b) args)
        (msg1 (vl-warn-odd-binary-expression-main op a b nil mod ialist))
        (msg2 (vl-warn-odd-binary-expression-main op b a t   mod ialist)))
     (append (if msg1 (list (cons msg1 x)) nil)
             (if msg2 (list (cons msg2 x)) nil)
             (vl-warn-odd-binary-expression-list args mod ialist))))

 (defun vl-warn-odd-binary-expression-list (x mod ialist)
   (declare (xargs :guard (and (vl-exprlist-p x)
                               (vl-module-p mod)
                               (equal ialist (vl-moditem-alist mod)))
                   :measure (vl-exprlist-count x)))
   (if (atom x)
       nil
     (append (vl-warn-odd-binary-expression (car x) mod ialist)
             (vl-warn-odd-binary-expression-list (cdr x) mod ialist)))))





; Bleh, this doesn't really seem to do anything useful:

;; (mutual-recursion

;;  (defund vl-expr-find-oddsizes (x mod ialist)
;;    (declare (xargs :guard (and (vl-expr-p x)
;;                                (vl-module-p mod)
;;                                (equal ialist (vl-moditem-alist mod)))
;;                    :measure (vl-expr-count x)))
;;    (b* (((when (vl-fast-atom-p x))
;;          nil)
;;         (op   (vl-nonatom->op x))
;;         (args (vl-nonatom->args x))
;;         (others (vl-exprlist-find-oddsizes args mod ialist))

;;         ((when (eq op :vl-unary-plus))
;;          ;; Unary plus is always weird.
;;          (cons (cons :weird-operator x)
;;                others))

;;         ;; No checks for unary minus.
;;         ;; No checks for unary bitwise not.
;;         ;; No checks for unary logical not.

;;         ((when (member op '(:vl-unary-bitand
;;                             ;; :vl-unary-bitor  -- seems to mostly generate spurious warnings
;;                             :vl-unary-xor
;;                             :vl-unary-nand
;;                             :vl-unary-nor
;;                             :vl-unary-xnor)))
;;          ;; Reduction operators.  It'd be weird to apply these to 1-bit operands.
;;          ;; It'd be kind of weird to apply these to 1-bit arguments.
;;          (b* ((arg-size (vl-expr-probable-selfsize (first args) mod ialist)))
;;            (if (eql arg-size 1)
;;                (cons (cons :check-size x) others)
;;              others)))

;;         ;; No checks for binary plus, minus, times, divide, remainder, power.

;;         ((when (member op '(:vl-binary-lt :vl-binary-lte :vl-binary-gt :vl-binary-gte)))
;;          ;; Weird to do a relational comparison on a 1-bit argument.
;;          ;; BOZO maybe also compare whether the sizes are the same?
;;          (b* (((list a b) args)
;;               (a-size (vl-expr-probable-selfsize a mod ialist))
;;               (b-size (vl-expr-probable-selfsize b mod ialist)))
;;            ;; Originally I just tested (OR (eql a-size 1) (eql b-size 1)) here, but that
;;            ;; didn't seem right because we can get into situations where A is the sum of
;;            ;; a bunch of one-bit things, e.g., (a1 + a2 + a3 > 1), so the self-size looks
;;            ;; like it's just one.  We may want to consider the outer context, too, and not
;;            ;; try to do this size check based on self-sizes.
;;            (if (and (eql a-size 1)
;;                     (eql b-size 1))
;;                (cons (cons :check-size x) others)
;;              others)))

;;         ((when (member op '(:vl-binary-shr :vl-binary-shl :vl-binary-ashl :vl-binary-ashr)))
;;          ;; Weird to shift a one-bit bus left or right.
;;          (b* (((list a ?b) args)
;;               (a-size (vl-expr-probable-selfsize a mod ialist)))
;;            (if (eql a-size 1)
;;                (cons (cons :check-size x) others)
;;              others)))

;;         ;; BOZO weird to bitwise and/or/xor things of different widths.

;;         ;; WEird to have ternary operator with different true/false sizes or non-1 test size
;;         )
;;      others))

;;  (defund vl-exprlist-find-oddsizes (x mod ialist)
;;    (declare (xargs :guard (and (vl-exprlist-p x)
;;                                (vl-module-p mod)
;;                                (equal ialist (vl-moditem-alist mod)))
;;                    :measure (vl-exprlist-count x)))
;;    (if (atom x)
;;        nil
;;      (append (vl-expr-find-oddsizes (car x) mod ialist)
;;              (vl-exprlist-find-oddsizes (cdr x) mod ialist)))))


(defsection vl-oddexpr-check

  (defpp vl-pp-oddexpr-details (x)
    :body
    (cond ((atom x)
           ps)
          ((atom (car x))
           (prog2$
            (er hard? 'vl-pp-oddexpr-details "Bad details.~%")
            ps))
          (t
           (vl-ps-seq
            (vl-print " - ")
            (vl-cw "~s0: ~a1~%" (caar x) (cdar x))
            (vl-pp-oddexpr-details (cdr x))))))


  (defund vl-oddexpr-check (x ctx mod ialist)
    (declare (xargs :guard (and (vl-expr-p x)
                                (vl-context-p ctx)
                                (vl-module-p mod)
                                (equal ialist (vl-moditem-alist mod)))))
    (b* ((details (append (vl-warn-odd-binary-expression x mod ialist)
                          ;;(vl-expr-find-oddsizes x mod ialist)
                          ))
         ((unless details)
          nil))
      (list (make-vl-warning
             :type :vl-warn-oddexpr
             :msg (str::cat "~a0: found ~s1 that suggest precedence problems ~
                             may be present.  Details:~%"
                            (with-local-ps
                             (vl-pp-oddexpr-details details)))
             :args (list ctx
                         (if (vl-plural-p details) "subexpressions" "a subexpression"))
             :fatalp nil
             :fn 'vl-oddexpr-check))))

  (defthm vl-warninglist-p-of-vl-oddexpr-check
    (vl-warninglist-p (vl-oddexpr-check x ctx mod ialist))
    :hints(("Goal" :in-theory (enable vl-oddexpr-check)))))


(defsection vl-exprctxalist-oddexpr-check

  (defund vl-exprctxalist-oddexpr-check (x mod ialist)
    (declare (xargs :guard (and (vl-exprctxalist-p x)
                                (vl-module-p mod)
                                (equal ialist (vl-moditem-alist mod)))))
    (if (atom x)
        nil
      (append (vl-oddexpr-check (caar x) (cdar x) mod ialist)
              (vl-exprctxalist-oddexpr-check (cdr x) mod ialist))))

  (defthm vl-warninglist-p-of-vl-exprctxalist-oddexpr-check
    (vl-warninglist-p (vl-exprctxalist-oddexpr-check x mod ialist))
    :hints(("Goal" :in-theory (enable vl-exprctxalist-oddexpr-check)))))



(defsection vl-module-oddexpr-check
  :parents (oddexpr-check)
  :short "@(call vl-module-oddexpr-check) carries our our @(see
oddexpr-check) on all the expressions in a module, and adds any resulting
warnings to the module."

  (defund vl-module-oddexpr-check (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* (((when (vl-module->hands-offp x))
          ;; don't check things like vl_1_bit_latch if they're already defined somehow
          x)
         (ialist       (vl-moditem-alist x))
         (ctxexprs     (vl-module-ctxexprs x))
         (new-warnings (vl-exprctxalist-oddexpr-check ctxexprs x ialist))
         (-            (fast-alist-free ialist)))
      (change-vl-module x
                        :warnings (append new-warnings (vl-module->warnings x)))))

  (local (in-theory (enable vl-module-oddexpr-check)))

  (defthm vl-module-p-of-vl-module-oddexpr-check
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-oddexpr-check x))))

  (defthm vl-module->name-of-vl-module-oddexpr-check
    (equal (vl-module->name (vl-module-oddexpr-check x))
           (vl-module->name x))))


(defsection vl-modulelist-oddexpr-check

  (defprojection vl-modulelist-oddexpr-check (x)
    (vl-module-oddexpr-check x)
    :guard (vl-modulelist-p x)
    :result-type vl-modulelist-p
    :parents (oddexpr-check))

  (defthm vl-modulelist->names-of-vl-modulelist-oddexpr-check
    (equal (vl-modulelist->names (vl-modulelist-oddexpr-check x))
           (vl-modulelist->names x))
    :hints(("Goal" :induct (len x)))))


