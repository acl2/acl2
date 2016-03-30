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
(include-book "../mlib/selfsize")
(include-book "../mlib/fmt")
(include-book "../mlib/ctxexprs")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defsection oddexpr-check
  :parents (vl-lint)
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
        (vl-expr-selfsize x ss (vl-elabscopes-init-ss ss))))
    size))

(define vl-odd-binop-class
  :short "Group binary operators into classes."
  ((x vl-binaryop-p))
  :returns (class symbolp :rule-classes :type-prescription)
  :long "<p>This lets us come up with a basic abstraction for an expression,
where, e.g., we treat any kind of shift operation as equivalent, etc.</p>"
  (case (vl-binaryop-fix x)
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
    ((:xor-class     . :rel-class)   . :check-type-unless-topargs-boolean) ; permit (a < b) ^ c when c seems boolean
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

(defprod vl-oddinfo
  ((type     symbolp)
   (subexpr  vl-expr-p "The whole subexpression")
   (simple   vl-expr-p "The simple side of the subexpression")
   (complex  vl-expr-p "The complex side of the subexpression")
   (swidth   maybe-natp "Simple side width")
   (cwidth   maybe-natp "Complex side width")))

(fty::deflist vl-oddinfolist :elt-type vl-oddinfo)

(define vl-warn-odd-binary-expression-main
  :short "Check the top-level of a binary expression for precedence problems."
  ((op1     vl-binaryop-p "Outer operator, joins @('a') and @('x').")
   (a       vl-expr-p     "The simple argument (not to be looked inside).")
   (x       vl-expr-p     "The complex argument (contains the inner operator, if any).")
   (flipped booleanp      "Nil means the original expression was @('a op x'),
                           T means it was @('x op a').")
   (origx   vl-expr-p)
   (ss      vl-scopestack-p))
  :returns (oddinfos vl-oddinfolist-p)

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

  (declare (ignorable flipped))

  (b* ((x (vl-expr-fix x))
       (a (vl-expr-fix a))
       (origx (vl-expr-fix origx)))
    (vl-expr-case x
      :vl-binary
      (b* ((op2        x.op)
           (op1-class  (vl-odd-binop-class op1))
           (op2-class  (vl-odd-binop-class op2))
           (key        (cons op1-class op2-class))
           (look       (assoc-equal key *vl-odd-binops-table*))
           ((unless (cdr look))
            nil)
           (asize (vl-expr-probable-selfsize a ss))
           (xsize (vl-expr-probable-selfsize x ss)))
        (case (cdr look)
          ((:check-precedence)
           ;; We've run into something like a + b << c which parses in a way that
           ;; might sometimes be surprising, viz. (a + b) << c.  We want to check
           ;; whether there are explicit parens around the sub-op (op2).  If so,
           ;; this seems to be what the user wants; else issue a warning.
           (if (assoc-equal "VL_EXPLICIT_PARENS" x.atts)
               nil
             (list (make-vl-oddinfo :type :check-precedence
                                    :subexpr origx
                                    :simple a
                                    :swidth asize
                                    :complex x
                                    :cwidth xsize))))

          (:check-type
           ;; Hrmn.  Well, even in the case of type errors, parens seem to be pretty
           ;; indicative that the designer wants to do something weird.
           (if (assoc-equal "VL_EXPLICIT_PARENS" x.atts)
               nil
             (list (make-vl-oddinfo :type :check-type
                                    :subexpr origx
                                    :simple a
                                    :swidth asize
                                    :complex x
                                    :cwidth xsize))))

          (:check-type-unless-topargs-boolean
           (b* (((when (assoc-equal "VL_EXPLICIT_PARENS" x.atts))
                 nil)
                (asize (vl-expr-probable-selfsize a ss))
                (xsize (vl-expr-probable-selfsize x ss))
                ((when (and (or (eql asize 1) (not asize))
                            (or (eql xsize 1) (not xsize))))
                 ;; Skip it since args are Boolean or there was some error
                 ;; determining their sizes.
                 nil))
             (list (make-vl-oddinfo :type :check-type
                                    :subexpr origx
                                    :simple a
                                    :swidth asize
                                    :complex x
                                    :cwidth xsize))))


          ((:check-precedence-plusminus)
           ;; [Jared] Historically we had the folloiwng special case here for
           ;; (a - b) + c.  However, this was pretty chatty and it doesn't seem
           ;; like it was actually finding errors.  I'm turning it off now.

           ;;  ;; Special case for plus of minus.  We want to warn about (a - b) + c without
           ;;  ;; explicit parens.  We know OP1 is + and OP2 is -.
           ;;  ;;
           ;;  ;; If FLIPPED=NIL, the expression we found was A + (B - C).  We know there must
           ;;  ;; be explicit parens or it wouldn't have gotten parsed this way, so there's
           ;;  ;; nothing to do.
           ;;  ;;
           ;;  ;; If FLIPPED=T, the expression we found was (B - C) + A.  This is the case we
           ;;  ;; want to warn about, unless there were explicit parens around (B - C).
           ;;  (if (and flipped
           ;;           (not (assoc-equal "VL_EXPLICIT_PARENS" x.atts)))
           ;;      (list (make-vl-oddinfo :type :check-precedence
           ;;                             :subexpr origx
           ;;                             :simple a
           ;;                             :swidth asize
           ;;                             :complex x
           ;;                             :cwidth xsize))
           ;;    nil))

           nil)

          (otherwise
           (raise "Unexpected action type ~x0.~%" (cdr look)))))

      :otherwise
      nil)))


(defines vl-warn-odd-binary-expression
  :short "Recursively check through an expression for precedence problems."

  (define vl-warn-odd-binary-expression
    ((x      vl-expr-p        "Subexpression we're recurring through.")
     (ss     vl-scopestack-p))
    :measure (vl-expr-count x)
    :returns (infos vl-oddinfolist-p)
    (b* ((x (vl-expr-fix x)))
      (vl-expr-case x
        :vl-binary
        (append (vl-warn-odd-binary-expression-main x.op x.left  x.right nil x ss)
                (vl-warn-odd-binary-expression-main x.op x.right x.left  t   x ss)
                (vl-warn-odd-binary-expression x.left ss)
                (vl-warn-odd-binary-expression x.right ss))
        :otherwise
        (vl-warn-odd-binary-expression-list (vl-expr->subexprs x) ss))))

  (define vl-warn-odd-binary-expression-list
    ((x      vl-exprlist-p)
     (ss     vl-scopestack-p))
    :measure (vl-exprlist-count x)
    :returns (infos vl-oddinfolist-p)
    (if (atom x)
        nil
      (append (vl-warn-odd-binary-expression (car x) ss)
              (vl-warn-odd-binary-expression-list (cdr x) ss))))
  ///
  (deffixequiv-mutual vl-warn-odd-binary-expression))


(define vl-oddinfo-details ((n natp) (x vl-oddinfo-p) &key (ps 'ps))
  (b* (((vl-oddinfo x)))
    (vl-ps-seq
     (vl-cw "[Issue #~x0] ~s1.  Expression:~%"
            (lnfix n)
            (if (eq x.type :check-type)
                "(flagged based on widths)"
              "(flagged based on operators)"))
     (vl-ps-update-copious-parens nil)
     (vl-indent 4)
     (vl-pp-expr x.subexpr)
     (vl-cw "~|Will be parsed as:~%")
     (vl-ps-update-copious-parens t)
     (vl-indent 4)
     (vl-pp-expr x.subexpr)
     (if (eq x.type :check-type)
         (vl-ps-seq
          (vl-cw "~|Self-width ~x0 for ~a1.~%" x.swidth x.simple)
          (vl-cw "~|Self-width ~x0 for ~a1.~%" x.cwidth x.complex))
       ps)
     (vl-cw "~%"))))

(define vl-oddinfolist-details ((n natp) (x vl-oddinfolist-p) &key (ps 'ps))
  :measure (len (vl-oddinfolist-fix x))
  (b* ((n (lnfix n))
       (x (vl-oddinfolist-fix x))
       ((when (atom x))
        ps))
    (vl-ps-seq (vl-oddinfo-details n (car x))
               (vl-oddinfolist-details (+ 1 n) (cdr x)))))

(define vl-expr-oddexpr-check ((x  vl-expr-p)
                               (ss vl-scopestack-p))
  :returns (warnings vl-warninglist-p)
  (b* ((details (mergesort (vl-warn-odd-binary-expression x ss)))
       ((unless details)
        nil))
    (list (make-vl-warning
           :type :vl-warn-oddexpr
           :msg (cat "possible precedence problems; consider explicit parens.  Details:~%~%"
                     (str::prefix-lines (with-local-ps (vl-oddinfolist-details 1 details))
                                        "     "))
           ;; The argument isn't used, but allows warning suppression to work.
           :args (list (vl-expr-fix x))
           :fn __function__))))

#||
(include-book
 "../mlib/print-warnings")

(top-level
 (with-local-ps
   (vl-print-warnings
    (let* ((a (vl-idexpr "a"))
           (b (vl-idexpr "b"))
           (c (vl-idexpr "c"))
           (a<b<c (make-vl-binary :op :vl-binary-lt
                                  :left (make-vl-binary :op :vl-binary-lt
                                                        :left a
                                                        :right b)
                                  :right c)))
      (vl-expr-oddexpr-check a<b<c nil)))))
||#

(def-expr-check oddexpr-check)

