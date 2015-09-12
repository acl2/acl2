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
(include-book "../mlib/ctxexprs")
(include-book "../transforms/expr-size")
(include-book "../mlib/fmt")
(local (include-book "../util/arithmetic"))

(defsection oddexpr-check
  :parents (lint)
  :short "Check for odd expressions that might indicate precedence problems."

  :long "<p>This is some rough code for finding expressions that might have
precedence problems.</p>

<p>Consider the expression @('a & b < c').  Due to the Verilog precedence
rules, this gets parsed as @('a & (b < c)').  Well, that might be quite
surprising.  We try to look for expressions like this and, unless the code
contains explicit parens around the @('(b < c)') part, we issue a warning that
it might not have the expected precedence.</p>

<p>This has found a few good bugs!</p>")

(local (xdoc::set-default-parents oddexpr-check))

(defval *fake-modelement*
  (make-vl-vardecl :name "Fake_Module_Element"
                   :type (make-vl-coretype :name :vl-logic)
                   :loc *vl-fakeloc*))

(define vl-expr-probable-selfsize
  :short "Heuristically estimate an expression's size."
  ((x      vl-expr-p)
   (ss     vl-scopestack-p))
  :returns (size maybe-natp :rule-classes :type-prescription
                 "The probable size of this expression, or @('nil') for
                  failure.")

  :long "<p>There's no reason to believe the size it returns will be the
eventual size of the expression because size propagation hasn't been taken into
account; in fact we may just fail and return @('nil') for a number of
reasons (for instance the wire ranges may not be resolved yet), there's no way
to get the failure reason.</p>

<p>On the other hand, I think it should be the case that the final size of the
expression will always be at least as much as this selfsize, if it returns a
non-@('nil') value.  And we can use this before resolving ranges, etc., which
makes it useful for simple linting.</p>"

  (b* (((mv & size)
        (vl-expr-selfsize x ss *fake-modelement* nil)))
    size))

(define vl-odd-binop-class
  :short "Group binary operators into classes."
  ((x vl-op-p))
  :returns (class symbolp :rule-classes :type-prescription)
  :long "<p>This lets us come up with a basic abstraction for an expression,
where, e.g., we treat any kind of shift operation as equivalent, etc.</p>"
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

(defval *vl-odd-binops-table*
  :short "The actual intelligence behind the oddexpr check."

  :long "<p>This is the main table that controls whether we warn about certain
combinations of binary operators.  If you want to NOT issue a warning about a
particular combination of operators, then just leave it out of the table.</p>

<p>The keys in the table have the form (outer-class . inner-class).  For
details about these classes see @(see vl-odd-binop-class).  Loosely speaking, a
key like @('(:shift-class . :plus-class)') matches expressions of the following
forms:</p>

<ol>
<li>@('(a + b) << c')</li>
<li>@('a << (b + c)')</li>
</ol>

<p>Whereas a key like (:plus-class . :shift-class) would match expressions of
the following forms:</p>

<ol>
<li>@('(a << b) + c')</li>
<li>@('a + (b << c)')</li>
</ol>

<p>In other words, the inner-op is the \"sub\" operation, and the outer-op is
the \"top\" operation.</p>

<p>Note that we never have keys where the outer-op has a higher precedence than
the inner operation, such as @('(:plus-class . :shift-class)').  Why not?</p>

<p>Because of the precedence rules, @('a << b + c') gets parsed as @('a << (b +
c)').  In other words, the only reason we'd ever get an expression that matches
@('(:plus-class . :shift-class)') is that the user explicitly put in their own
parens around the shift operator.  If they've done that, then they are
explicitly saying what precedence they want, and there's no chance they are
going to be surprised by Verilog's precedence rules.  This same reasoning holds
for any combination of operators where the outer op is higher precedence than
the inner op.</p>

<p><b>NOTE</b> see the source code for this table for additional comments
giving motivation for these actions, etc.</p>

@(def *vl-odd-binops-table*)"

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
;   a - b - c     |  (a - b) - c      no          maybe, see below
;   a - b << c    |  (a - b) << c     no          yes              warn
;   a - b < c     |  (a - b) < c      no          no
;   a - b == c    |  (a - b) == c     no          no
;   a - b & c     |  (a - b) & c      no          yes              warn
;   a - b ^ c     |  (a - b) ^ c      no          yes              warn
;   a - b | c     |  (a - b) | c      no          yes              warn
;   a - b && c    |  (a - b) && c     yes         --               warn
;   a - b || c    |  (a - b) || c     yes         --               warn
; ----------------+----------------------------------------------------------------------------------------------------
;
; For a long time we warned about A - B - C, but this seems to be a common
; cause of false positives.  My takeaway is that our logic designers do seem to
; be comfortable with the associativity of minus, so I'm not going to warn
; about this.

    ;; (outer-op     .  inner-op)    .   action
    ;; ((:minus-class   . :minus-class)  . :check-precedence)
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
    ((:bitand-class  . :rel-class)   . :check-type-unless-topargs-boolean) ; permit (a < b) & c when c seems boolean
    ((:xor-class     . :rel-class)   . :check-type)
    ((:bitor-class   . :rel-class)   . :check-type-unless-topargs-boolean) ; permit (a < b) | c when c seems boolean


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
    ((:bitand-class .  :cmp-class)    . :check-type-unless-topargs-boolean) ; permit (a == b) & c when c seems boolean
    ((:xor-class    .  :cmp-class)    . :check-type)
    ((:bitor-class  .  :cmp-class)    . :check-type-unless-topargs-boolean) ; permit (a == b) | c when c seems boolean


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
    ((:xor-class    .  :bitand-class) . :check-precedence) ; maybe too frequent
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

(define vl-warn-odd-binary-expression-main
  :short "Check the top-level of a binary expression for precedence problems."
  ((op1     vl-op-p)
   (a       vl-expr-p)
   (x       vl-expr-p)
   (flipped booleanp)
   (ss      vl-scopestack-p))
  (declare (ignorable a flipped))

  :long "<p>Note that any particular binary expression, say @('P OP Q'), might
have sub-structure in either the P argument or in the Q argument.  To deal with
this, in @(see vl-warn-odd-binary-expression), we call this function twice:</p>

<ul>
<li>First with @('(OP P Q)') and @('FLIPPED=NIL'),</li>
<li>Then with @('(OP Q P)') and @('FLIPPED=T').</li>
</ul>

<p>The first argument, A, we regard as the \"simple\" argument; we don't try to
decompose it any more.  However, we try to match X against @('B OP2 C').  Then,
we see if we think the sequence @('A op (B op2 C)') seems reasonable.</p>"

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
            (asize (vl-expr-probable-selfsize a ss))
            (xsize (vl-expr-probable-selfsize x ss))
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
       (raise "Unexpected action type ~x0.~%" (cdr look))))))


(defines vl-warn-odd-binary-expression
  :short "Recursively check through an expression for precedence problems."

  (define vl-warn-odd-binary-expression
    ((x      vl-expr-p)
     (ss     vl-scopestack-p))
    :measure (vl-expr-count x)
    (b* (((when (vl-fast-atom-p x))
          nil)
         (op    (vl-nonatom->op x))
         (arity (vl-op-arity op))
         (args  (vl-nonatom->args x))
         ((unless (eql arity 2))
          (vl-warn-odd-binary-expression-list args ss))
         ((list a b) args)
         (msg1 (vl-warn-odd-binary-expression-main op a b nil ss))
         (msg2 (vl-warn-odd-binary-expression-main op b a t   ss)))
      (append (if msg1 (list (cons msg1 x)) nil)
              (if msg2 (list (cons msg2 x)) nil)
              (vl-warn-odd-binary-expression-list args ss))))

  (define vl-warn-odd-binary-expression-list
    ((x      vl-exprlist-p)
     (ss     vl-scopestack-p))
    :measure (vl-exprlist-count x)
    (if (atom x)
        nil
      (append (vl-warn-odd-binary-expression (car x) ss)
              (vl-warn-odd-binary-expression-list (cdr x) ss)))))


; Bleh, this doesn't really seem to do anything useful:

;; (mutual-recursion

;;  (defund vl-expr-find-oddsizes (x ss)
;;    (declare (xargs :guard (and (vl-expr-p x)
;;                                (vl-module-p mod)
;;                                (equal ialist (vl-make-moditem-alist mod)))
;;                    :measure (vl-expr-count x)))
;;    (b* (((when (vl-fast-atom-p x))
;;          nil)
;;         (op   (vl-nonatom->op x))
;;         (args (vl-nonatom->args x))
;;         (others (vl-exprlist-find-oddsizes args ss))

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
;;          (b* ((arg-size (vl-expr-probable-selfsize (first args) ss)))
;;            (if (eql arg-size 1)
;;                (cons (cons :check-size x) others)
;;              others)))

;;         ;; No checks for binary plus, minus, times, divide, remainder, power.

;;         ((when (member op '(:vl-binary-lt :vl-binary-lte :vl-binary-gt :vl-binary-gte)))
;;          ;; Weird to do a relational comparison on a 1-bit argument.
;;          ;; BOZO maybe also compare whether the sizes are the same?
;;          (b* (((list a b) args)
;;               (a-size (vl-expr-probable-selfsize a ss))
;;               (b-size (vl-expr-probable-selfsize b ss)))
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
;;               (a-size (vl-expr-probable-selfsize a ss)))
;;            (if (eql a-size 1)
;;                (cons (cons :check-size x) others)
;;              others)))

;;         ;; BOZO weird to bitwise and/or/xor things of different widths.

;;         ;; WEird to have ternary operator with different true/false sizes or non-1 test size
;;         )
;;      others))

;;  (defund vl-exprlist-find-oddsizes (x ss)
;;    (declare (xargs :guard (and (vl-exprlist-p x)
;;                                (vl-module-p mod)
;;                                (equal ialist (vl-make-moditem-alist mod)))
;;                    :measure (vl-exprlist-count x)))
;;    (if (atom x)
;;        nil
;;      (append (vl-expr-find-oddsizes (car x) ss)
;;              (vl-exprlist-find-oddsizes (cdr x) ss)))))


(define vl-pp-oddexpr-details (x &key (ps 'ps))
  (cond ((atom x)
         ps)
        ((atom (car x))
         (prog2$ (raise "Bad details: ~x0~%" x)
                 ps))
        (t
         (vl-ps-seq
          (vl-print "     - ")
          (vl-cw "~s0: ~a1~%" (caar x) (cdar x))
          (vl-pp-oddexpr-details (cdr x))))))

(define vl-oddexpr-check ((x      vl-expr-p)
                          (ctx    vl-context-p)
                          (ss     vl-scopestack-p))
  :returns (warnings vl-warninglist-p)
  (b* ((details (append (vl-warn-odd-binary-expression x ss)
                        ;;(vl-expr-find-oddsizes x ss)
                        ))
       ((unless details)
        nil))
    (list (make-vl-warning
           :type :vl-warn-oddexpr
           :msg (cat "~a0: found ~s1 that suggest precedence problems may be ~
                      present.  Maybe add explicit parens?  Details:~%"
                     (with-local-ps (vl-pp-oddexpr-details details)))
           :args (list ctx
                       (if (vl-plural-p details)
                           "subexpressions"
                         "a subexpression"))))))

(define vl-exprctxalist-oddexpr-check ((x      vl-exprctxalist-p)
                                       (ss     vl-scopestack-p))
  :returns (warnings vl-warninglist-p)
  (if (atom x)
      nil
    (append (vl-oddexpr-check (caar x) (cdar x) ss)
            (vl-exprctxalist-oddexpr-check (cdr x) ss))))

(define vl-module-oddexpr-check
  :short "@(call vl-module-oddexpr-check) carries our our @(see oddexpr-check)
on all the expressions in a module, and adds any resulting warnings to the
module."
  ((x vl-module-p)
   (ss vl-scopestack-p))
  :returns (new-x vl-module-p)

  (b* ((x (vl-module-fix x))
       ((when (vl-module->hands-offp x))
        ;; don't check things like vl_1_bit_latch if they're already defined somehow
        x)
       (ss           (vl-scopestack-push (vl-module-fix x) ss))
       (ctxexprs     (vl-module-ctxexprs x))
       (new-warnings (vl-exprctxalist-oddexpr-check ctxexprs ss)))
    (change-vl-module x
                      :warnings (append new-warnings (vl-module->warnings x)))))

(defprojection vl-modulelist-oddexpr-check ((x vl-modulelist-p)
                                            (ss vl-scopestack-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-oddexpr-check x ss))

(define vl-design-oddexpr-check ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       (ss (vl-scopestack-init x))
       ((vl-design x) x)
       (mods (vl-modulelist-oddexpr-check x.mods ss)))
    (vl-scopestacks-free)
    (change-vl-design x :mods mods)))
