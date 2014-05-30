; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
(include-book "util/defs")
(include-book "util/bits")
(include-book "util/echars")
(include-book "util/defoption")
(include-book "util/deftranssum")
(local (include-book "util/arithmetic"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (std::add-default-post-define-hook :fix))


(defsection vl-expr-p
  :parents (syntax)
  :short "Representation of Verilog expressions."

  :long "<p>One goal of our expression representation was for the recursive
structure of expressions to be as simple as possible.  More specifically, I did
not want to have a different representation for a unary expression than for a
binary expression, etc.  Instead, I just wanted each operator to take a list of
arguments, each of which were themselves valid subexpressions.</p>

<h3>Basic Terminology</h3>

<h5>Atomic Expressions</h5>

<p>The atomic expressions are recognized by @(see vl-atom-p).  Each
atomic expression includes some <b>guts</b>, which refer to either an:</p>

<ul>

<li>@(see vl-id-p): a simple, non-hierarchical identifier,</li>

<li>@(see vl-constint-p): an integer literal with no X or Z bits,</li>
<li>@(see vl-weirdint-p): an integer literal with some X or Z bits,</li>
<li>@(see vl-extint-p): an unbased, unsized integer literal like @(''0') or
@(''x'),</li>

<li>@(see vl-real-p): a \"real literal\", i.e., a floating point number,</li>

<li>@(see vl-string-p): a string literal,</li>

<li>@(see vl-time-p): time literals like @('3ns'),</li>

<li>@(see vl-keyguts-p): special atomic expressions like @('null'), @('this'),
@('super'), @('$'), @('local'), etc.</li>

<li>@(see vl-hidpiece-p): one piece of a hierarchical identifier,</li>

<li>@(see vl-funname-p): the name of an ordinary function, or</li>

<li>@(see vl-sysfunname-p): the name of a system function (e.g.,
@('$display')).</li>

<li>@(see vl-basictype-p): simple type names like @('byte'), @('shortint'),
@('time'), @('logic'), etc.</li>

<li>@(see vl-tagname-p): the name of a tagged union type member.</li>

</ul>

<p>Some of these are probably not things you would ordinarily think of as
atomic expressions.  However, accepting them as atomic expressions lets us
achieve the straightforward recursive structure we desire for expressions.</p>

<p>In addition to their guts, each @(see vl-atom-p) includes a</p>

<ul>

<li>@('finalwidth'), which is a @(see maybe-natp), and</li>

<li>@('finaltype'), which is a @(see vl-maybe-exprtype-p).</li>

</ul>

<p>Typically, when we have just parsed the modules, these fields are left
@('nil'): their values are only filled in during our expression typing and
sizing computations.</p>

<h5>Non-Atomic Expressions</h5>

<p>All non-atomic expressions share a common cons structure, and @(see
vl-nonatom-p) is a simple, non-recursive, structural validity check to see if
this structure is obeyed at the top level.  Note that @(see vl-nonatom-p) is
<b>not</b> sufficient to ensure that the object is a valid expression, because
additional constraints (e.g., arity checks, recursive well-formedness) are
imposed by @('vl-expr-p').</p>

<p>Like atomic expressions, each @('vl-nonatom-p') includes @('finalwidth') and
@('finaltype') fields, which are @('nil') upon parsing and may later be filled
in by our expression typing and sizing computations.  To be accepted by
@('vl-nonatom-p'), the @('finalwidth') and @('finaltype') must be valid @(see
maybe-natp) and @(see vl-maybe-exprtype-p) objects, respectively.</p>

<p>Additionally, each non-atomic expression includes:</p>

<ul>

<li>@('op'), the operation being applied.  For structural validity, @('op')
must be one of the known operators found in @(see *vl-ops-table*).</li>

<li>@('args'), the arguments the operation is being applied to.  No structural
constraints are imposed upon @('args').</li>

<li>@('atts'), which represent any attributes written in the @('(* foo = bar,
baz *)') style that Verilog-2005 permits.  No structural constraints are placed
upon @('atts').</li>

</ul>

<h5>Valid Expressions</h5>

<p>The valid expressions are recognized by @(see vl-expr-p), which extends our
basic structural checks recursively over the expression, and also ensures that
each operator has the proper arity.</p>

<h3>Definition</h3>

@(def vl-expr-p)

<h3>Basic Theorems</h3>")

(local (xdoc::set-default-parents vl-expr-p))

(defval *vl-ops-table*
  :short "Table of operators and their arities."

  :long "<p>The constant @(srclink *vl-ops-table*) defines the valid operators
for @(see vl-nonatom-p) expressions.  It is preferred not to access this table
directly, but rather to use @(see vl-op-p) and @(see vl-op-arity).</p>

<p>The @('*vl-ops-table*') is an alist that maps our operators (keyword
symbols) to their arities.  For operations that do not have fixed
arities (e.g., concatenation, function calls, ...), we map the operator to
@('nil').</p>

<p>Here is how we represent the various Verilog operators:</p>

<h5>Basic Unary Operators (arity 1)</h5>

<ul>
<li>@(' +  ') becomes @(':vl-unary-plus')</li>
<li>@(' -  ') becomes @(':vl-unary-minus')</li>
<li>@(' !  ') becomes @(':vl-unary-lognot')</li>
<li>@(' ~  ') becomes @(':vl-unary-bitnot')</li>
<li>@(' &  ') becomes @(':vl-unary-bitand')</li>
<li>@(' ~& ') becomes @(':vl-unary-nand')</li>
<li>@(' |  ') becomes @(':vl-unary-bitor')</li>
<li>@(' ~| ') becomes @(':vl-unary-nor')</li>
<li>@(' ^  ') becomes @(':vl-unary-xor')</li>
<li>@(' ^~ ') or @(' ~^ ') becomes @(':vl-unary-xnor')</li>
</ul>

<h5>Basic Binary Operators (arity 2)</h5>

<ul>
<li>@(' +   ') becomes @(':vl-binary-plus')</li>
<li>@(' -   ') becomes @(':vl-binary-minus')</li>
<li>@(' *   ') becomes @(':vl-binary-times')</li>
<li>@(' /   ') becomes @(':vl-binary-div')</li>
<li>@(' %   ') becomes @(':vl-binary-rem')</li>
<li>@(' ==  ') becomes @(':vl-binary-eq')</li>
<li>@(' !=  ') becomes @(':vl-binary-neq')</li>
<li>@(' === ') becomes @(':vl-binary-ceq')</li>
<li>@(' !== ') becomes @(':vl-binary-cne')</li>
<li>@(' &&  ') becomes @(':vl-binary-logand')</li>
<li>@(' ||  ') becomes @(':vl-binary-logor')</li>
<li>@(' **  ') becomes @(':vl-binary-power')</li>
<li>@(' <   ') becomes @(':vl-binary-lt')</li>
<li>@(' <=  ') becomes @(':vl-binary-lte')</li>
<li>@(' >   ') becomes @(':vl-binary-gt')</li>
<li>@(' >=  ') becomes @(':vl-binary-gte')</li>
<li>@(' &   ') becomes @(':vl-binary-bitand')</li>
<li>@(' |   ') becomes @(':vl-binary-bitor')</li>
<li>@(' ^   ') becomes @(':vl-binary-xor')</li>
<li>@(' ^~  ') or @(' ~^ ') becomes @(':vl-binary-xnor')</li>
<li>@(' >>  ') becomes @(':vl-binary-shr')</li>
<li>@(' <<  ') becomes @(':vl-binary-shl')</li>
<li>@(' >>> ') becomes @(':vl-binary-ashr')</li>
<li>@(' <<< ') becomes @(':vl-binary-ashl')</li>
</ul>

<h5>Basic Ternary Operators (arity 3)</h5>

<ul>
<li>@('a ? b : c') becomes @(':vl-qmark')     (conditional operator)</li>
<li>@('a : b : c') becomes @(':vl-mintypmax') (min/typ/max delay operator)</li>
</ul>

<h5>Selection Operators</h5>

<ul>
<li>@('foo[1]') initially becomes @(':vl-index').  Later these should be
changed to @(':vl-bitselect') or @(':vl-array-index'), as appropriate.</li>
<li>@('foo[3 : 1]')  becomes @(':vl-partselect-colon') (arity 3)</li>
<li>@('foo[3 +: 1]') becomes @(':vl-partselect-pluscolon') (arity 3)</li>
<li>@('foo[3 -: 1]') becomes @(':vl-partselect-minuscolon') (arity 3)</li>
</ul>

<p>Note that upon parsing, there are no @(':vl-bitselect') or
@(':vl-array-index') operators; these must be introduced by the @(see
resolve-indexing) transform.</p>

<h5>Concatenation and Replication Operators</h5>

<ul>
<li>@('{1, 2, 3, ...}') becomes @(':vl-concat') (arity @('nil'))</li>
<li>@('{ 3 { 2, 1 } }') becomes @(':vl-multiconcat') (arity 2)</li>
</ul>

<h5>Streaming Concatenations</h5>

<p>For SystemVerilog streaming concatenations we add new variable-arity
operators:</p>

@({
     {<< [size] { arg1 arg2 ... }}
       -->
     (:vl-stream-left [size] arg1 arg2 ...)

     {>> [size] { arg1 arg2 ... }}
       -->
     (:vl-stream-right [size] arg1 arg2 ...)
})

<p>For the special @('with') expressions, we add four new operators:</p>

<ul>
<li>@('foo with [1]') becomes @(':vl-with-index') (arity 2)</li>
<li>@('foo with [3:1]') becomes @(':vl-with-colon') (arity 3)</li>
<li>@('foo with [3+:1]') becomes @(':vl-with-pluscolon') (arity 3)</li>
<li>@('foo with [3-:1]') becomes @(':vl-with-minuscolon') (arity 3)</li>
</ul>

<h5>Function Calls</h5>

<ul>
<li>@('foo(1,2,3)') becomes @(':vl-funcall') (arity @('nil'))</li>
<li>@('$foo(1,2,3)') becomes @(':vl-syscall') (arity @('nil'))</li>
</ul>

<h5>Hierarchical Identifiers</h5>

<p>Note: see @(see vl-hidpiece-p) for some additional discussion about
hierarchical identifiers.</p>

<ul>
<li>@('foo.bar') becomes @(':vl-hid-dot') (arity 2)</li>
<li>@('foo[3][4].bar') becomes a @(':vl-hid-dot') whose @('from') argument
is a tree of @(':vl-index') operators.</li>
</ul>"

  (list
   ;; Basic Unary Operators
   (cons :vl-unary-plus            1)   ;;; +
   (cons :vl-unary-minus           1)   ;;; -
   (cons :vl-unary-lognot          1)   ;;; !
   (cons :vl-unary-bitnot          1)   ;;; ~
   (cons :vl-unary-bitand          1)   ;;; &
   (cons :vl-unary-nand            1)   ;;; ~&
   (cons :vl-unary-bitor           1)   ;;; |
   (cons :vl-unary-nor             1)   ;;; ~|
   (cons :vl-unary-xor             1)   ;;; ^
   (cons :vl-unary-xnor            1)   ;;; ~^ or ^~

   ;; Basic Binary Operators
   (cons :vl-binary-plus           2)   ;;; +
   (cons :vl-binary-minus          2)   ;;; -
   (cons :vl-binary-times          2)   ;;; *
   (cons :vl-binary-div            2)   ;;; /
   (cons :vl-binary-rem            2)   ;;; %
   (cons :vl-binary-eq             2)   ;;; ==
   (cons :vl-binary-neq            2)   ;;; !=
   (cons :vl-binary-ceq            2)   ;;; ===
   (cons :vl-binary-cne            2)   ;;; !==
   (cons :vl-binary-wildeq         2)   ;;; ==?
   (cons :vl-binary-wildneq        2)   ;;; !=?
   (cons :vl-binary-logand         2)   ;;; &&
   (cons :vl-binary-logor          2)   ;;; ||
   (cons :vl-binary-power          2)   ;;; **
   (cons :vl-binary-lt             2)   ;;; <
   (cons :vl-binary-lte            2)   ;;; <=
   (cons :vl-binary-gt             2)   ;;; >
   (cons :vl-binary-gte            2)   ;;; >=
   (cons :vl-binary-bitand         2)   ;;; &
   (cons :vl-binary-bitor          2)   ;;; |
   (cons :vl-binary-xor            2)   ;;; ^
   (cons :vl-binary-xnor           2)   ;;; ~^ or ^~
   (cons :vl-binary-shr            2)   ;;; >>
   (cons :vl-binary-shl            2)   ;;; <<
   (cons :vl-binary-ashr           2)   ;;; >>>
   (cons :vl-binary-ashl           2)   ;;; <<<

   ;; Special Binary Operators (these associate right to left)
   (cons :vl-implies               2)   ;;; ->
   (cons :vl-equiv                 2)   ;;; <->

   ;; Basic Ternary Operators
   (cons :vl-qmark                 3)   ;;; e.g., 1 ? 2 : 3
   (cons :vl-mintypmax             3)   ;;; e.g., (1 : 2 : 3)

   ;; Selection Operators
   (cons :vl-index                 2) ;;; e.g., foo[1] before determining array/wire
   (cons :vl-bitselect             2) ;;; e.g., foo[1] for wire bit selections
   (cons :vl-array-index           2) ;;; e.g., foo[1] for array indexing
   (cons :vl-partselect-colon      3) ;;; e.g., foo[3 : 1]
   (cons :vl-partselect-pluscolon  3) ;;; e.g., foo[3 +: 1]
   (cons :vl-partselect-minuscolon 3) ;;; e.g., foo[3 -: 1]

   ;; Concatenation and Replication Operators
   (cons :vl-concat                nil) ;;; e.g., { 1, 2, 3 }
   (cons :vl-multiconcat           2)   ;;; e.g., { 3 { 2, 1 } }

   ;; Streaming Concatenations (SystemVerilog)
   (cons :vl-stream-left           nil)   ;;; {<<{...args...}}
   (cons :vl-stream-right          nil)   ;;; {>>{...args...}}
   (cons :vl-stream-left-sized     nil)   ;;; {<< size {...args...}}
   (cons :vl-stream-right-sized    nil)   ;;; {>> size {...args...}}
   (cons :vl-with-index            2)     ;;; e.g., foo with [1]
   (cons :vl-with-colon            3)     ;;; e.g., foo with [3 : 1]
   (cons :vl-with-pluscolon        3)     ;;; e.g., foo with [3 +: 1]
   (cons :vl-with-minuscolon       3)     ;;; e.g., foo with [3 -: 1]

   ;; Function Calls
   (cons :vl-funcall               nil)   ;;; e.g., foo(1,2,3)
   (cons :vl-syscall               nil)   ;;; e.g., $foo(1,2,3)

   ;; Hierarchical Identifiers and Scoping
   (cons :vl-hid-dot               2)   ;;; e.g., foo.bar
   (cons :vl-scope                 2)   ;;; e.g., foo::bar

   ;; Tagged Union Expressions, should have arity 1 or 2
   (cons :vl-tagged nil) ;; e.g., "tagged Valid 13" or "tagged Invalid"

   ))



(define vl-op-p (x)
  :short "Recognizer for valid operators."
  :long "<p>@(call vl-op-p) checks that @('x') is one of the operators listed
in the @(see *vl-ops-table*).  We prefer to use @('vl-op-p') instead of looking
up operators directly in the table, since this way we can disable @('vl-op-p')
and avoid large case splits.</p>"
  :inline t
  ;; Per basic testing, assoc is faster than hons-get here.
  (if (assoc x *vl-ops-table*)
      t
    nil)
  ///
  (defthm type-when-vl-op-p
    (implies (vl-op-p x)
             (and (symbolp x)
                  (not (equal x t))
                  (not (equal x nil))))
    :rule-classes :compound-recognizer))

(define vl-op-fix ((x vl-op-p))
  :returns (op vl-op-p)
  :parents (vl-op-p)
  :inline t
  (mbe :logic (if (vl-op-p x)
                  x
                ;; Subtle horrible thing to ensure we don't have arity
                ;; requirements when op-fixing.
                :vl-concat)
       :exec x)
  ///
  (defthm vl-op-fix-when-vl-op-p
    (implies (vl-op-p x)
             (equal (vl-op-fix x) x))))

(deffixtype vl-op
  :pred vl-op-p
  :fix vl-op-fix
  :equiv vl-op-equiv
  :define t
  :forward t)


(fty::deflist vl-oplist
              :elt-type vl-op-p
              :true-listp nil)

(deflist vl-oplist-p (x)
  (vl-op-p x)
  :elementp-of-nil nil)


(define vl-op-arity ((x vl-op-p))
  :returns (arity maybe-natp :rule-classes :type-prescription)
  :short "Look up the arity of an operator."
  :long "<p>@(call vl-op-arity) determines the arity of the operator @('x') by
consulting the @(see *vl-ops-table*).  If @('x') does not have a fixed
arity (e.g., it might be a function call or concatenation operation), then we
return @('nil').</p>

<p>We prefer to use @('vl-op-arity') instead of looking up operators directly
in the table, since this way we can disable @('vl-op-arity') and avoid large
case splits.</p>"

  :inline t
  (cdr (assoc (vl-op-fix x) *vl-ops-table*)))


(defenum vl-exprtype-p
  (:vl-signed :vl-unsigned)
  :short "Valid types for expressions."
  :long "<p>Each expression should be either @(':vl-signed') or
@(':vl-unsigned').  We may eventually expand this to include other types, such
as real and string.</p>")

(defoption vl-maybe-exprtype-p vl-exprtype-p
  :short "Recognizer for an @(see vl-exprtype-p) or @('nil')."
  :long "<p>We use this for the @('finaltype') fields in our expressions.  It
allows us to represent expressions whose types have not yet been computed.</p>"
  ///
  (defthm type-when-vl-maybe-exprtype-p
    (implies (vl-maybe-exprtype-p x)
             (and (symbolp x)
                  (not (equal x t))))
    :rule-classes :compound-recognizer))


(defprod vl-constint
  :short "Representation for constant integer literals with no X or Z bits."
  :tag :vl-constint
  :hons t
  :layout :tree

  ((origwidth  posp
               :rule-classes :type-prescription
               "Subtle; generally should <b>not be used</b>; see below.")

   (value      natp
               :rule-classes :type-prescription
               "The most important part of a constant integer.  Even
                immediately upon parsing the value has already been determined
                and is available to you as an ordinary natural number."
               :reqfix (acl2::loghead (pos-fix origwidth) value))

   (origtype   vl-exprtype-p
               :rule-classes
               ((:rewrite)
                (:type-prescription
                 :corollary
                 (implies (force (vl-constint-p x))
                          (and (symbolp (vl-constint->origtype x))
                               (not (equal (vl-constint->origtype x) nil))
                               (not (equal (vl-constint->origtype x) t))))))
               "Subtle; generally should <b>not be used</b>; see below.")

   (wasunsized booleanp
               :rule-classes :type-prescription
               "Set to @('t') by the parser for unsized constants like @('5')
                and @(''b0101'), but not for sized ones like @('4'b0101')."))

  :require
  (< value (expt 2 origwidth))

  :long "<p>Constant integers are produced from source code constructs like
@('5'), @('4'b0010'), and @('3'h0').</p>

<p>Note that the value of a constant integer is never negative.  In Verilog
there are no negative literals; instead, an expression like @('-5') is
basically parsed the same as @('-(5)'), so the negative sign is not part of the
literal.  See Section 3.5.1 of the Verilog-2005 standard.</p>

<p>The @('origwidth') and @('origtype') fields are subtle.  They indicate the
<i>original</i> width and signedness of the literal as specified in the source
code, e.g., if the source code contains @('8'sd 65'), then the origwidth will
be 8 and the origtype will be @(':vl-signed.')  These fields are subtle because
@(see expression-sizing) generally alters the widths and types of
subexpressions, so these may not represent the final widths and types of these
constants in the context of the larger expression.  Instead, the preferred way
to determine a constint's final width and sign is to inspect the @('vl-atom-p')
that contains it.</p>

<p>We insist that @('0 <= value <= 2^origwidth') for every constant integer.
If our @(see lexer) encounters something ill-formed like @('3'b 1111'), it
emits a warning and truncates from the left, as required by Section 3.5.1 (page
10) of the Verilog-2005 standard.</p>

<p>Note that in Verilog, unsized integer constants like @('5') or @(''b101')
have an implementation-dependent size of at least 32 bits.  VL historically
tried to treat such numbers in an abstract way, saying they had \"integer
size\".  But we eventually decided that this was too error-prone and we now
instead act like a 32-bit implementation even at the level of our lexer.  This
conveniently makes the width of a constant integer just a positive number.  On
the other hand, some expressions may produce different results on 32-bit
versus, say, 64-bit implementations.  Because of this, we added the
@('wasunsized') field so that we might later statically check for problematic
uses of unsized constants.</p>

<p>All constints are automatically created with @(see hons).  This is probably
pretty trivial, but it seems nice.  For instance, the constant integers from
0-32 are probably used thousands of times throughout a design for bit-selects
and wire ranges, so sharing their memory may be useful.</p>")

(defthm vl-constint-bound-linear
  (< (vl-constint->value x)
     (expt 2 (vl-constint->origwidth x)))
  :rule-classes :linear)


(define vl-nbits-fix ((n    posp)
                      (bits vl-bitlist-p))
  :returns (bits-fix vl-bitlist-p)
  :guard (equal (len bits) (pos-fix n))
  :inline t
  :hooks nil
  (mbe :logic (if (and (vl-bitlist-p bits)
                       (equal (len bits) (pos-fix n)))
                  bits
                (replicate (pos-fix n) :vl-xval))
       :exec bits)
  ///
  (defthm consp-of-vl-nbits-fix
    (consp (vl-nbits-fix n bits))
    :rule-classes :type-prescription)
  (defthm len-of-vl-nbits-fix
    (equal (len (vl-nbits-fix n bits))
           (pos-fix n)))
  (defthm vl-nbitsfix-identity
    (implies (and (vl-bitlist-p bits)
                  (equal (len bits) (pos-fix n)))
             (equal (vl-nbits-fix n bits)
                    bits)))
  (defthm vl-nbits-fix-of-pos-fix
    (equal (vl-nbits-fix (pos-fix n) bits)
           (vl-nbits-fix n bits))))

(defprod vl-weirdint
  :short "Representation for constant integer literals with X or Z bits."
  :tag :vl-weirdint
  :hons t
  :layout :tree

  ;; BOZO consider eliminating origwidth here and just using (len bits) when we
  ;; need to know how many there are

  ((origwidth   posp
                :rule-classes :type-prescription
                "Subtle; generally should <b>not be used</b>; see below.")

   (bits        vl-bitlist-p
                "An MSB-first list of the four-valued Verilog bits making up
                 this constant's value; see @(see vl-bit-p)."
                :reqfix (vl-nbits-fix origwidth bits))

   (origtype    vl-exprtype-p
                :rule-classes
                ((:rewrite)
                 (:type-prescription
                  :corollary
                  (implies (force (vl-weirdint-p x))
                           (and (symbolp (vl-weirdint->origtype x))
                                (not (equal (vl-weirdint->origtype x) nil))
                                (not (equal (vl-weirdint->origtype x) t))))))
                "Subtle; generally should <b>not be used</b>; see below.")

   (wasunsized  booleanp
                :rule-classes :type-prescription
                "Did this constant have an explicit size?"))

  :require
  (equal (len bits) origwidth)

  :long "<p>Weird integers are produced by source code constructs like
@('1'bz'), @('3'b0X1'), and so on.</p>

<p>The @('origwidth'), @('origtype'), and @('wasunsized') fields are analogous
to those from @(see vl-constint-p); see the discussion there for details.  But
unlike a constint, a weirdint does not have a natural-number @('value').
Instead it has a list of four-valued @('bits') that may include X and Z
values.</p>

<p>Like constinsts, all weirdints are automatically constructed with @(see
hons).  This may not be worthwhile since there are probably usually not too
many weirdints, but by the same reasoning it shouldn't be too harmful.</p>")

(defthm consp-of-vl-weirdint->bits
  (consp (vl-weirdint->bits x))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (disable vl-weirdint-requirements)
          :use ((:instance vl-weirdint-requirements)))))


(defprod vl-extint
  :short "Representation for unbased, unsized integer literals, viz. @(''0'),
@(''1'), @(''x'), and @(''z')."
  :tag :vl-extint
  :hons t
  :layout :tree
  ((value vl-bit-p "The kind of extended integer this is.")))


(defprod vl-string
  :short "Representation for string literals."
  :tag :vl-string
  :layout :Tree

  ((value stringp
          :rule-classes :type-prescription
          "An ordinary ACL2 string where, e.g., special sequences like @('\\n')
           and @('\\t') have been resolved into real newline and tab
           characters, etc.")))


(defprod vl-real
  :short "Representation of real (floating point) literals."
  :tag :vl-real
  :layout :tree

  ((value   stringp
            :rule-classes :type-prescription
            "The actual characters found in the source code, i.e., it might be
             a string such as @('\"3.41e+12\"')."))

  :long "<p>We have almost no support for working with real numbers.  You
should probably not rely on our current representation, since we will almost
certainly want to change it as soon as we want to do anything with real
numbers.</p>")

(defprod vl-time
  :short "Representation of time amounts."
  :tag :vl-time
  :hons t
  :layout :tree

  ((quantity stringp
             :rule-classes :type-prescription
             "An ACL2 string with the amount.  In practice, the amount should
              match either @('unsigned_number') or @('fixed_point_number'),
              e.g., @('\"3\"') or @('\"45.617\"').  We don't try to process
              this further because (1) we don't expect it to matter for much,
              and (2) ACL2 doesn't really support fixed point numbers.")
   (units     vl-timeunit-p
              "The kind of time unit this is, e.g., seconds, milliseconds,
               microseconds, ..."))

  :long "<p>We barely support this.  You should probably not rely on our
current representation, since we will almost certainly want to change it as
soon as we do anything with time units.</p>")

(defprod vl-id
  :short "Representation for simple identifiers."
  :tag :vl-id
  :hons t
  :layout :tree

  ((name stringp
         :rule-classes :type-prescription
         "This identifier's name.  Our structure only requires that this is an
          ACL2 string; in practice the name can include <b>any character</b>
          besides whitespace and should be non-empty.  Note that for escaped
          identifiers like @('\\foo '), the @('\\') and trailing space are not
          included in the name; see @(see vl-read-escaped-identifier)."))

  :long "<p>@('vl-id-p') objects are used to represent identifiers used in
expressions which might be the names of wires, ports, parameters, registers,
and so on.</p>

<p>A wonderful feature of our representation @('vl-id-p') atoms are guaranteed
to not be part of any hierarchical identifier, nor are they the names of
functions or system functions.  See the discussion in @(see vl-hidpiece-p) for
more information.</p>

<p>Like @(see vl-constint-p)s, we automatically create these structures with
@(see hons).  This seems quite nice, since the same names may be used many
times throughout all the expressions in a design.</p>")

(defprod vl-hidpiece
  :short "Represents one piece of a hierarchical identifier."
  :tag :vl-hidpiece
  :layout :tree

  ((name stringp :rule-classes :type-prescription))

  :long "<p>We represent hierarchical identifiers like
@('top.processor[2][3].reset') as non-atomic expressions.  To represent this
particular expression, we build a @(see vl-expr-p) that is something like
this:</p>

@({
 (:vl-hid-dot top
              (vl-hid-dot
                  (:vl-index (:vl-index processor 2)
                             3)
                  reset))
})

<p>In other words, the @(':vl-hid-dot') operator is used to join pieces of a
hierarchical identifier, and @(':vl-index') operators are used when
arrays or instance arrays are being accessed.</p>

<p>To add slightly more precision, our representation is really more like the
following:</p>

@({
 (:vl-hid-dot (hidpiece \"top\")
              (vl-hid-dot
                 (:vl-index (:vl-index (hidpiece \"processor\") (constint 2))
                            (constint 3))
                 (hidpiece \"reset\")))
})

<p>In other words, the individual identifiers used throughout a hierarchical
identifier are actually @('vl-hidpiece-p') objects instead of @(see vl-id-p)
objects.</p>

<p>We make this distinction so that in the ordinary course of working with the
parse tree, you can freely assume that any @('vl-id-p') you come across really
refers to some module item, and not to some part of a hierarchical
identifier.</p>")

(defprod vl-sysfunname
  :short "Represents a system function name."
  :tag :vl-sysfunname
  :layout :tree

  ((name stringp :rule-classes :type-prescription
         "The name of this system function, e.g., @('$display').  Includes the
          dollar sign."))

  :long "<p>We use a custom representation for the names of system functions,
so that we do not confuse them with ordinary @(see vl-id-p) objects.</p>")

(defprod vl-funname
  :short "Represents a (non-system) function name."
  :tag :vl-funname
  :layout :tree

  ((name stringp :rule-classes :type-prescription))

  :long "<p>We use a custom representation for the names of functions, so that
we do not confuse them with ordinary @(see vl-id-p) objects.</p>")


(defprod vl-tagname
  :short "Represents a tagged union member name."
  :tag :vl-tagname
  :layout :tree

  ((name stringp :rule-classes :type-prescription
         "The name of this member.  E.g., for @('tagged foo 3'), this would
          just be @('\"foo\"')."))

  :long "<p>We use a custom representation for the names of tagged union member
names so that we do not confuse them with ordinary @(see vl-id-p)
objects.</p>")


(defenum vl-keygutstype-p
  (:vl-null
   :vl-this
   :vl-super
   :vl-local
   :vl-$
   :vl-$root
   :vl-$unit
   :vl-emptyqueue)
  :parents (vl-keyguts-p)
  :short "Special kinds of atomic expressions.")

(defprod vl-keyguts
  :short "Representation of special, atomic SystemVerilog expressions,
distinguished by keywords such as @('null'), @('this'), @('super'), @('$'),
@('local'), etc."
  :tag :vl-keyguts
  :hons t ;; because there are just a few of them
  :layout :tree

  ((type vl-keygutstype-p
         "Which kind of expression this is.")))


(defenum vl-basictypekind-p
  (:vl-byte
   :vl-shortint
   :vl-int
   :vl-longint
   :vl-integer
   :vl-time
   :vl-bit
   :vl-logic
   :vl-reg
   :vl-shortreal
   :vl-real
   :vl-realtime)
  :parents (vl-basictype-p)
  :short "The various kinds of basic, atomic, built-in SystemVerilog types.")

(defprod vl-basictype
  :short "Atomic SystemVerilog types, like @('byte'), @('int').  These can be
used, e.g., in casting and streaming concatenation expressions."
  :tag :vl-basictype
  :hons t ;; because there are just a few of them
  :layout :tree

  ((kind vl-basictypekind-p
         "Which kind of type this is.")))

(deftranssum vl-atomguts
  :short "The main contents of a @(see vl-atom-p)."
  :long "<p>The guts of an atom are its main contents.  See @(see vl-expr-p)
for a discussion of the valid types.</p>"
  (vl-constint
   vl-weirdint
   vl-extint
   vl-string
   vl-real
   vl-id
   vl-hidpiece
   vl-funname
   vl-sysfunname
   vl-keyguts
   vl-time
   vl-basictype
   vl-tagname
   ))

(define vl-fast-id-p ((x vl-atomguts-p))
  :parents (vl-atomguts-p vl-id-p)
  :short "Faster version of @(see vl-id-p), given that @(see vl-atomguts-p) is
already known."
  :long "<p>We leave this function enabled and reason about @('vl-id-p')
instead.</p>"
  :inline t
  :enabled t
  :hooks nil
  (mbe :logic (vl-id-p x)
       :exec (eq (tag x) :vl-id)))

(define vl-fast-constint-p ((x vl-atomguts-p))
  :parents (vl-atomguts-p vl-constint-p)
  :short "Faster version of @(see vl-constint-p), given that @(see
vl-atomguts-p) is already known."
  :long "<p>We leave this function enabled and reason about @('vl-constint-p')
instead.</p>"
  :inline t
  :enabled t
  :hooks nil
  (mbe :logic (vl-constint-p x)
       :exec (eq (tag x) :vl-constint)))

(define vl-fast-weirdint-p ((x vl-atomguts-p))
  :parents (vl-atomguts-p vl-weirdint-p)
  :short "Faster version of @(see vl-weirdint-p), given that @(see
vl-atomguts-p) is already known."
  :long "<p>We leave this function enabled and reason about @('vl-weirdint-p')
instead.</p>"
  :inline t
  :enabled t
  :hooks nil
  (mbe :logic (vl-weirdint-p x)
       :exec (eq (tag x) :vl-weirdint)))

(define vl-fast-string-p ((x vl-atomguts-p))
  :parents (vl-atomguts-p vl-string-p)
  :short "Faster version of @(see vl-string-p), given that @(see
vl-atomguts-p) is already known."
  :long "<p>We leave this function enabled and reason about @('vl-string-p')
instead.</p>"
  :inline t
  :enabled t
  :hooks nil
  (mbe :logic (vl-string-p x)
       :exec (eq (tag x) :vl-string)))

(define vl-fast-hidpiece-p ((x vl-atomguts-p))
  :parents (vl-atomguts-p vl-hidpiece-p)
  :short "Faster version of @(see vl-hidpiece-p), given that @(see
vl-atomguts-p) is already known."
  :long "<p>We leave this function enabled and reason about @('vl-hidpiece-p')
instead.</p>"
  :inline t
  :enabled t
  :hooks nil
  (mbe :logic (vl-hidpiece-p x)
       :exec (eq (tag x) :vl-hidpiece)))

(define vl-fast-funname-p ((x vl-atomguts-p))
  :parents (vl-atomguts-p vl-funname-p)
  :short "Faster version of @(see vl-funname-p), given that @(see
vl-atomguts-p) is already known."
  :long "<p>We leave this function enabled and reason about @('vl-funname-p')
instead.</p>"
  :inline t
  :enabled t
  :hooks nil
  (mbe :logic (vl-funname-p x)
       :exec (eq (tag x) :vl-funname)))

(define vl-fast-sysfunname-p ((x vl-atomguts-p))
  :parents (vl-atomguts-p vl-sysfunname-p)
  :short "Faster version of @(see vl-sysfunname-p), given that @(see
vl-atomguts-p) is already known."
  :long "<p>We leave this function enabled and reason about
@('vl-sysfunname-p') instead.</p>"
  :inline t
  :enabled t
  :hooks nil
  (mbe :logic (vl-sysfunname-p x)
       :exec (eq (tag x) :vl-sysfunname)))

(defoption maybe-natp natp) ;; BOZO misplaced


(define vl-arity-ok-p ((op vl-op-p) (args))
  (let ((arity (vl-op-arity op)))
    (or (not arity)
        (equal (len args) arity)))
  ///
  (defthm vl-arity-ok-p-when-op-arity-known
    (implies (equal (vl-op-arity op) n)
             (equal (vl-arity-ok-p op args)
                    (or (not n)
                        (equal (len args) n)))))

  (defthm vl-arity-ok-p-for-specific-operator
    (implies (syntaxp (quotep op))
             (equal (vl-arity-ok-p op args)
                    (let ((arity (vl-op-arity op)))
                      (or (not arity)
                          (equal (len args) arity)))))))


(defval *vl-default-expr*
  (let ((guts (make-vl-constint :origwidth 1
                                :value 0
                                :origtype :vl-unsigned))
        (finalwidth nil)
        (finaltype nil))
    ;; Black magic horrible thing -- make sure this agrees with the resulting
    ;; definition of vl-expr-p.
    (cons :atom (cons guts (cons finalwidth finaltype)))))

(define vl-arity-fix ((op vl-op-p) (args))
  :inline t
  :guard (vl-arity-ok-p op args)
  :prepwork ((local (in-theory (enable vl-arity-ok-p))))
  (mbe :logic
       (let ((arity (vl-op-arity op))
             (len   (len args)))
         (cond ((or (not arity)
                    (equal len arity))
                args)
               ((< arity len)
                (take arity args))
               (t
                (append args (replicate (- arity len) *vl-default-expr*)))))
       :exec
       args)
  ///
  (defthm vl-arity-ok-p-of-vl-arity-fix
    (vl-arity-ok-p op (vl-arity-fix op args)))

  (defthm vl-arity-fix-when-vl-arity-ok-p
    (implies (vl-arity-ok-p op args)
             (equal (vl-arity-fix op args) args))))


(deftypes vl-expr

  (deftagsum vl-expr
    (:atom
     ;; :short "Representation of atomic expressions."
     ;; :long "<p>See the discussion in @(see vl-expr-p).</p>"
     :layout :tree
     :base-name vl-atom
     ((guts       vl-atomguts-p)
      (finalwidth maybe-natp
                  :rule-classes :type-prescription)
      (finaltype  vl-maybe-exprtype-p
                  :rule-classes
                  ((:rewrite)
                   ;; BOZO fix me
                   ;; (:type-prescription
                   ;;  :corollary
                   ;;  (and (symbolp (vl-atom->finaltype x))
                   ;;       (not (equal (vl-atom->finaltype x) t)))))))
                   ))))

    (:nonatom
     ;;      :short "Structural validity of non-atomic expressions."
     ;;      :long "<p>This is only a simple structural check, and does not imply
     ;; @('vl-expr-p').  See @(see vl-expr-p) for details.</p>"
     :layout :tree
     :base-name vl-nonatom
     ((op   vl-op-p
            :rule-classes
            ((:rewrite)
             ;; BOZO fix me
             ;; (:type-prescription
             ;;  :corollary
             ;;  ;; I previously forced the hyp, but it got irritating because it
             ;;  ;; kept screwing up termination proofs.  Consider case-split?
             ;;  (implies (vl-nonatom-p x)
             ;;           (and (symbolp (vl-nonatom->op x))
             ;;                (not (equal (vl-nonatom->op x) t))
             ;;                (not (equal (vl-nonatom->op x) nil)))))))
             ))

      (atts vl-atts-p)
      (args vl-exprlist-p :reqfix (vl-arity-fix op args))
      (finalwidth maybe-natp :rule-classes :type-prescription)
      (finaltype  vl-maybe-exprtype-p
                  :rule-classes
                  ((:rewrite)
                   ;; BOZO fix me
                   ;; (:type-prescription
                   ;;  :corollary
                   ;;  ;; I previously forced this, but maybe that's a bad idea for
                   ;;  ;; the same reasons as vl-op-p-of-vl-nonatom->op?
                   ;;  (implies (vl-nonatom-p x)
                   ;;           (and (symbolp (vl-nonatom->finaltype x))
                   ;;                (not (equal (vl-nonatom->finaltype x) t))))))
                   ))
      )
     :require
     (vl-arity-ok-p op args))
    :count     vl-expr-count-raw
    :measure (two-nats-measure (acl2-count x) 2))

  (fty::deflist vl-exprlist
    :elt-type vl-expr-p
    :true-listp nil
    :measure (two-nats-measure (acl2-count x) 0)
    :count   vl-exprlist-count-raw)


  (fty::defalist vl-atts
    :key-type stringp
    :val-type vl-maybe-expr
    :measure (two-nats-measure (acl2-count x) 0)
    :count   vl-atts-count-raw
    :true-listp t)

  (fty::defflexsum vl-maybe-expr
    (:null :cond (not x)
     :ctor-body nil)
    (:expr :cond t
     :fields ((expr :type vl-expr-p :acc-body x))
     :ctor-body expr)
    :kind nil
    :measure (two-nats-measure (acl2-count x) 3)
    :count vl-maybe-expr-count-raw

    :post-pred-events
    ((defthm vl-expr-p-of-vl-default-expression
       (vl-expr-p *vl-default-expr*))
     (deflist vl-exprlist-p (x)
       (vl-expr-p x)
       :elementp-of-nil nil)
     (defthm vl-exprlist-p-of-vl-arity-fix
       (implies (vl-exprlist-p x)
                (vl-exprlist-p (vl-arity-fix op x)))
       :hints(("Goal" :in-theory (enable vl-arity-fix
                                         vl-exprlist-p)))))

    :post-fix-events
    ((defthm vl-arity-ok-p-of-vl-exprlist-fix
       (equal (vl-arity-ok-p op (vl-exprlist-fix x))
              (vl-arity-ok-p op x))
       :hints(("Goal" :in-theory (enable vl-arity-ok-p)))))))



(define vl-atom-p ((x vl-expr-p))
  :long "<p>We leave this function enabled and reason about @('vl-expr-kind')
instead.</p>"
  :inline t
  :enabled t
  (eq (vl-expr-kind x) :atom))

(deflist vl-atomlist-p (x)
  (vl-atom-p x)
  :guard (vl-exprlist-p x))





;; BOZO horrible, fixtypes stuff doesn't enable tag theorems.
;; (local (in-theory (enable tag-when-vl-atom-p
;;                           vl-atom-p-when-wrong-tag)))


;(defsection vl-expr-p-basics
;  :extension vl-expr-p

;  (local (in-theory (enable vl-expr-p)))

  ;; don't want?
  ;; (defthm vl-expr-p-when-vl-atom-p
  ;;   (implies (vl-atom-p x)
  ;;            (vl-expr-p x)))

  ;; don't want?
  ;; (defthm vl-atom-p-by-tag-when-vl-expr-p
  ;;   (implies (and (equal (tag x) :vl-atom)
  ;;                 (vl-expr-p x))
  ;;            (vl-atom-p x)))

  ;; already have
  ;; (defthm consp-when-vl-expr-p
  ;;   (implies (vl-expr-p x)
  ;;            (consp x))
  ;;   :rule-classes :compound-recognizer
  ;;   :hints(("Goal" :expand (vl-expr-p x))))

  ;; (defthm vl-expr-p-of-vl-nonatom
  ;;   (implies (and (force (vl-op-p op))
  ;;                 (force (vl-atts-p atts))
  ;;                 (force (vl-exprlist-p args))
  ;;                 (force (implies (vl-op-arity op)
  ;;                                 (equal (len args) (vl-op-arity op))))
  ;;                 (force (maybe-natp finalwidth))
  ;;                 (force (vl-maybe-exprtype-p finaltype)))
  ;;            (vl-expr-p (make-vl-nonatom :op op
  ;;                                        :atts atts
  ;;                                        :args args
  ;;                                        :finalwidth finalwidth
  ;;                                        :finaltype finaltype))))

(defthm len-of-vl-nonatom->args
  (implies (vl-op-arity (vl-nonatom->op x))
           (equal (len (vl-nonatom->args x))
                  (vl-op-arity (vl-nonatom->op x))))
  :hints(("Goal"
          :in-theory (e/d (vl-arity-ok-p)
                          (vl-nonatom-requirements))
          :use ((:instance vl-nonatom-requirements)))))

(defthm vl-arity-ok-p-after-change-args
  (implies (equal (len args) (len (vl-nonatom->args x)))
           (vl-arity-ok-p (vl-nonatom->op x) args))
  :hints(("Goal" :in-theory (enable vl-arity-ok-p))))


;; built in, automatically true
  ;; (defthm vl-exprlist-p-of-vl-nonatom->args
  ;;   (implies (and (force (vl-expr-p x))
  ;;                 (force (vl-nonatom-p x)))
  ;;            (vl-exprlist-p (vl-nonatom->args x))))

;; (defthm vl-nonatom-p-when-not-vl-atom-p
;;     ;; BOZO strengthen?  rewrite vl-nonatom-p to "not vl-atom-p"?
;;     (implies (and (not (vl-atom-p x))
;;                   (vl-expr-p x))
;;              (vl-nonatom-p x)))

;; (defthm vl-atts-p-of-vl-nonatom->atts
;;   ;; (implies (and (force (vl-expr-p x))
;;   ;;               (force (vl-nonatom-p x)))
;;   (vl-atts-p (vl-nonatom->atts x)))
;; )


(defmacro vl-fast-atom-p (x)
  ;; Historically this did something faster than vl-atom-p.  With the new
  ;; fixtypes representation it doesn't do anything different.  We keep it only
  ;; for compatibility with legacy code.
  `(vl-atom-p ,x))

(define vl-expr->finalwidth ((x vl-expr-p))
  :returns (width? maybe-natp :rule-classes :type-prescription)
  :short "Get the @('finalwidth') from an expression."
  :long "<p>See @(see vl-expr-p) for a discussion of widths.  The result is a
@(see maybe-natp).</p>"
  :inline t
  (vl-expr-case x
    :atom    x.finalwidth
    :nonatom x.finalwidth)
  :prepwork ((local (in-theory (enable vl-expr-p))))
  ///
  (defthm vl-expr->finalwidth-of-vl-atom
    (equal (vl-expr->finalwidth (make-vl-atom :guts guts
                                              :finalwidth finalwidth
                                              :finaltype finaltype))
           (maybe-natp-fix finalwidth)))

  (defthm vl-expr->finalwidth-of-vl-nonatom
    (equal (vl-expr->finalwidth (make-vl-nonatom :op op
                                            :atts atts
                                            :args args
                                            :finalwidth finalwidth
                                            :finaltype finaltype))
           (maybe-natp-fix finalwidth))))

(define vl-expr->finaltype ((x vl-expr-p))
  :returns (type? vl-maybe-exprtype-p
                  :rule-classes ((:rewrite)
                                 (:type-prescription :corollary
                                  (and (symbolp (vl-expr->finaltype x))
                                       (not (equal (vl-expr->finaltype x) t))))))
  :short "Get the @('finaltype') from an expression."
  :long "<p>See @(see vl-expr-p) for a discussion of types.  The result
is a @(see vl-maybe-exprtype-p).</p>"
  :inline t
  (vl-expr-case x
    :atom x.finaltype
    :nonatom x.finaltype)
  :prepwork ((local (in-theory (enable vl-expr-p))))
  ///
  (defthm vl-expr->finaltype-of-vl-atom
    (equal (vl-expr->finaltype (make-vl-atom :guts guts
                                             :finalwidth finalwidth
                                             :finaltype finaltype))
           (vl-maybe-exprtype-fix finaltype)))

  (defthm vl-expr->finaltype-of-vl-nonatom
    (equal (vl-expr->finaltype (make-vl-nonatom :op op
                                                :atts atts
                                                :args args
                                                :finalwidth finalwidth
                                                :finaltype finaltype))
           (vl-maybe-exprtype-fix finaltype))))

;; (defoption vl-maybe-expr-p vl-expr-p
;;   :parents (syntax vl-expr-p)
;;   :short "Representation for a @(see vl-expr-p) or @('nil')."
;;   :long "<p>This is a basic option type for expressions.</p>"
;;   )

(defsection vl-maybe-expr-p-rules

  (defthm vl-maybe-expr-p-when-vl-expr-p
    (implies (vl-expr-p x)
             (vl-maybe-expr-p x))
    :hints(("Goal" :in-theory (enable vl-maybe-expr-p))))

  (defthm vl-expr-p-when-vl-maybe-expr-p
    (implies (vl-maybe-expr-p x)
             (equal (vl-expr-p x)
                    (if (double-rewrite x) t nil)))
    :hints(("Goal" :in-theory (enable vl-maybe-expr-p))))

  (defthm type-when-vl-maybe-expr-p
    (implies (vl-maybe-expr-p x)
             (or (consp x)
                 (not x)))
    :rule-classes :compound-recognizer
    :hints(("Goal" :in-theory (enable vl-maybe-expr-p))))

  (defrefinement vl-maybe-expr-equiv vl-expr-equiv
    :hints(("Goal" :in-theory (enable vl-maybe-expr-fix))))

  ;; (local (defthm vl-expr-fix-of-vl-maybe-expr-fix
  ;;          (equal (vl-expr-fix (vl-maybe-expr-fix x))
  ;;                 (if x
  ;;                     (vl-expr-fix x)
  ;;                   (vl-expr-fix nil)))
  ;;          :hints(("Goal" :in-theory (enable vl-maybe-expr-fix)))))

  )

(defsection vl-atts-p
  :short "Representation of @('(* foo = 3, bar *)') style attributes."

  :long "<p>Verilog-2005 and SystemVerilog-2012 allow many constructs, (e.g.,
module instances, wire declarations, assignments, subexpressions, and so on) to
be annotated with <b>attributes</b>.</p>

<p>Each individual attribute can either be a single key with no value (e.g.,
@('baz') above), or can have the form @('key = value').  The keys are always
identifiers, and the values (if provided) are expressions.  Both Verilog-2005
and SystemVerilog-2012 agree that an attribute with no explicit value is to be
treated as having value @('1').</p>


<h3>Representation</h3>

<p>We represent attributes as alists mapping names to their values.  We use
ordinary ACL2 strings to represent the keys.  These strings are typically
honsed to improve memory sharing.  Each explicit value is represented by an
ordinary @(see vl-expr-p), and keys with no values are bound to @('nil')
instead.</p>

@(def vl-atts-p)


<h3>Size/Types of Attribute Values</h3>

<p>Verilog-2005 doesn't say anything about the types of attribute
expressions.</p>

<p>SystemVerilog-2012 says (Section 5.12) that the type of an attribute with no
value is @('bit'), and that otherwise its type is the (presumably
self-determined) type of the expression.</p>

<p>This is not really an adequate spec.  Consider for instance an attribute
like:</p>

@({
    (* foo = a + b *)
})

<p>Attributes live in their own namespace and are generally not very
well-specified.  It isn't clear what @('a') and @('b') refer to here.  For
instance, are they wires in this module, or perhaps global values that are
known by the Verilog tool.  It doesn't seem at all clear what the type or size
of such an expression is supposed to be.</p>

<p>Well, no matter.  Attributes are not used for much and if their sizes and
types aren't well specified, that's not necessarily any kind of problem.  For
VL's part, our sizing code simply ignores attributes and does not try to
determine their sizes and types at all.</p>


<h3>Nesting Attributes</h3>

<p>Note that both Verilog-2005 and SystemVerilog-2012 prohibit the nesting of
attributes.  That is, expressions like the following are not allowed:</p>

@({
     (* foo = a + (* bar *) b *)
})

<p>VL's parser enforces this restriction and will not allow expressions to have
nested attributes; see @(see vl-parse-0+-attribute-instances).</p>

<p>Internally we make <b>no such restriction</b>.  Our @(see vl-expr-p)
structures can have attributes nested to any arbitrary depth.</p>


<h3>Redundant and Conflicting Attributes</h3>

<p>When the same attribute name is given repeatedly, both Verilog-2005 and
SystemVerilog-2012 agree that the last occurrences of the attribute should be
used.  That is, the value of @('foo') below should be 5:</p>

@({
     (* foo = 1, foo = 5 *)
     assign w = a + b;
})

<p>VL's parser properly handles this case.  It issues warnings when duplicate
attributes are used, and always produces @('vl-atts-p') structures that are
free from duplicate keys, and where the entry for each attribute corresponds to
the last occurrence of it; see @(see vl-parse-0+-attribute-instances).</p>

<p>Internally we make <b>no such restriction</b>.  We treat @('vl-atts-p')
structures as ordinary alists.</p>


<h3>Internal Use of Attributes by VL</h3>

<p>VL transformations occasionally add attributes throughout modules.  As a
couple of examples:</p>

<ul>

<li>The @('VL_HANDS_OFF') attribute is used to say that a module is somehow
special and should not be modified by transformations.</li>

<li>VL may add @('VL_ORIG_EXPR') annotations to remember the \"original\"
versions of expressions, before any rewriting or other simplification has taken
place; these annotations can be useful in error messages.</li>

</ul>

<p>As a general rule, attributes added by VL <i>should</i> be prefixed with
@('VL_').  In practice, we may sometimes forget to follow this rule.</p>"

  (local (in-theory (enable vl-atts-p)))

  (defthm vl-atts-p-when-not-consp
    (implies (not (consp x))
             (equal (vl-atts-p x)
                    (not x))))

  (defthm vl-atts-p-of-cons
    (equal (vl-atts-p (cons a x))
           (and (consp a)
                (stringp (car a))
                (vl-maybe-expr-p (cdr a))
                (vl-atts-p x))))

  (defalist vl-atts-p (x)
    :key (stringp x)
    :val (vl-maybe-expr-p x)
    :keyp-of-nil nil
    :valp-of-nil t
    :already-definedp t
    :true-listp t)

  (defthm alistp-when-vl-atts-p-rewrite
    ;; This is potentially expensive, but without it we sometimes fail to
    ;; relieve guards for things like assoc-equal into (vl-whatever->atts x).
    (implies (vl-atts-p x)
             (alistp x)))

  (defthm vl-expr-p-of-cdr-of-hons-assoc-equal-when-vl-atts-p
    (implies (vl-atts-p atts)
             (equal (vl-expr-p (cdr (hons-assoc-equal key atts)))
                    (if (cdr (hons-assoc-equal key atts))
                        t
                      nil)))
    :hints(("Goal"
            :in-theory (enable hons-assoc-equal)
            :induct (hons-assoc-equal key atts))))

  (defthm vl-atts-p-of-vl-remove-keys
    (implies (force (vl-atts-p x))
             (vl-atts-p (vl-remove-keys keys x)))
    :hints(("Goal" :induct (len x)))))


(defsection vl-exprlist-p

;; (deflist vl-exprlist-p (x)
;;   (vl-expr-p x)
;;   :elementp-of-nil nil
;;   :verify-guards nil
;;   :parents (syntax)

;;   :rest
;;   ( ;; These are useful for seeing that arguments exist.
   (defthm first-under-iff-when-vl-exprlist-p
     (implies (vl-exprlist-p x)
              (iff (first x)
                   (consp x)))
     :rule-classes ((:rewrite :backchain-limit-lst 1)))

   (defthm second-under-iff-when-vl-exprlist-p
     (implies (vl-exprlist-p x)
              (iff (second x)
                   (consp (cdr x))))
     :rule-classes ((:rewrite :backchain-limit-lst 1)))

   (defthm third-under-iff-when-vl-exprlist-p
     (implies (vl-exprlist-p x)
              (iff (third x)
                   (consp (cddr x))))
     :rule-classes ((:rewrite :backchain-limit-lst 1))))

(defprojection vl-exprlist->finalwidths ((x vl-exprlist-p))
  (vl-expr->finalwidth x)
  :returns (widths vl-maybe-nat-listp)
  :nil-preservingp t
  :parents (vl-exprlist-p))

(defprojection vl-exprlist->finaltypes ((x vl-exprlist-p))
  (vl-expr->finaltype x)
  :nil-preservingp t
  :parents (vl-exprlist-p))

(fty::deflist vl-exprlistlist
              :elt-type vl-exprlist-p
              :true-listp nil)

(deflist vl-exprlistlist-p (x)
  (vl-exprlist-p x)
  :elementp-of-nil t
  :rest
  ((defthm vl-exprlist-p-of-flatten
     (implies (vl-exprlistlist-p x)
              (vl-exprlist-p (flatten x))))

   (defthm vl-exprlistlist-p-of-pairlis$
     (implies (and (vl-exprlist-p a)
                   (vl-exprlistlist-p x))
              (vl-exprlistlist-p (pairlis$ a x)))
     :hints(("Goal" :in-theory (enable pairlis$))))))



;; (define vl-expr-induct (flag x)
;;   :short "A basic induction scheme for @(see vl-expr-p)."
;;   :long "<p>BOZO should we really have this, or would make-flag be better?  I
;; guess this is in some ways cleaner.</p>"
;;   :verify-guards nil
;;   :enabled t
;;   :measure (two-nats-measure (acl2-count x)
;;                              (if (eq flag 'expr) 1 0))
;;   (cond ((eq flag 'expr)
;;          (if (vl-atom-p x)
;;              nil
;;            (list (vl-expr-induct 'atts (vl-nonatom->atts x))
;;                  (vl-expr-induct 'list (vl-nonatom->args x)))))
;;         ((eq flag 'atts)
;;          (if (consp x)
;;              (list (vl-expr-induct 'expr (cdar x))
;;                    (vl-expr-induct 'atts (cdr x)))
;;            nil))
;;         (t
;;          (if (consp x)
;;              (list (vl-expr-induct 'expr (car x))
;;                    (vl-expr-induct 'list (cdr x)))
;;            nil))))


(defsection arity-reasoning
  :parents (vl-op-arity vl-expr-p vl-nonatom-p)
  :short "Rules for reasoning about how many arguments an expression has."

  :long "<p>These rules have evolved a lot over time.  The current iteration
seems to be fairly good and fixes some problems with previous versions.</p>

<p>One previous approach was just to separately recognize each unary, binary,
and ternary operator, e.g.,</p>

@({
    (implies (and (or (equal (vl-nonatom->op x) :vl-unary-plus)
                      (equal (vl-nonatom->op x) :vl-unary-minus)
                      ...)
                 ...)
             (and (vl-nonatom->args x)
                  ...))
})

<p>These rules seemed to be pretty effective, but they were slow.  To fix the
slowness, I tried using a free variable to only apply the rule when the op was
exactly known, e.g.,</p>

@({
    (implies (and (equal (vl-nonatom->op x) op)
                  (<= (vl-op-arity op) 1)
                  ...)
             (and (vl-nonatom->args x)
                  ...))
})

<p>This did seem to be quite a bit faster and also seemed to wrok well when the
operands were known precisely.  But it did not handle cases like VL-HIDEXPR-P
very well, where if we know</p>

@({
    (not (equal (vl-nonatom->op x) :vl-hid-dot))
})

<p>then we should be able to infer that this is a @(':vl-hid-arraydot').  I had
trouble getting ACL2 to always canonicalize such things the \"positive\"
form.</p>

<p>The new rules don't have a free variable, but still avoid the big case
split.  We don't ask about particular operands, but instead just ask whether
the arity is known.  This works and should be pretty efficient when a direct
equality is known, e.g., if we know</p>

@({
    (equal (vl-nonatom->op x) :vl-binary-times),
})

<p>then we'll backchain to @('(vl-op-arity (vl-nonatom->op x))'), which
type-set should settle to @('(vl-op-arity :vl-binary-times)') and which we
should then get by evaluation.</p>

<p>But since there isn't a free variable, we'll also get a chance to apply any
rules that tell us what the arity is in some other way, which allows us to
fairly easily solve the HIDEXPR problem.</p>"

  (local (defthm iff-when-vl-expr-p
           (implies (vl-expr-p x)
                    (iff x t))
           :rule-classes nil))

  (local (in-theory (enable len)))

  (defthm arg1-exists-by-arity
    (let ((arity (vl-op-arity (vl-nonatom->op x))))
      (implies arity
               (and (implies (<= 1 arity)
                             (vl-nonatom->args x))
                    (iff (first (vl-nonatom->args x))
                         (<= 1 arity))
                    (equal (consp (vl-nonatom->args x))
                           (<= 1 arity)))))
    :hints(("Goal"
            :in-theory (e/d (vl-arity-ok-p)
                            (vl-nonatom-requirements len-of-vl-nonatom->args))
            :use ((:instance vl-nonatom-requirements)))))

  (defthm arg2-exists-by-arity
    (let ((arity (vl-op-arity (vl-nonatom->op x))))
      (implies arity
               (and (implies (<= 2 arity) (cdr (vl-nonatom->args x)))
                    (iff (second (vl-nonatom->args x)) (<= 2 arity))
                    (equal (consp (cdr (vl-nonatom->args x))) (<= 2 arity)))))
    :hints(("Goal"
            :in-theory (e/d (vl-arity-ok-p)
                            (vl-nonatom-requirements len-of-vl-nonatom->args))
            :use ((:instance vl-nonatom-requirements)))))

  (defthm arg3-exists-by-arity
    (let ((arity (vl-op-arity (vl-nonatom->op x))))
      (implies arity
               (and (implies (<= 3 arity) (cddr (vl-nonatom->args x)))
                    (iff (third (vl-nonatom->args x)) (<= 3 arity))
                    (equal (consp (cddr (vl-nonatom->args x))) (<= 3 arity)))))
    :hints(("Goal"
            :in-theory (e/d (vl-arity-ok-p)
                            (vl-nonatom-requirements len-of-vl-nonatom->args))
            :use ((:instance vl-nonatom-requirements))))))

