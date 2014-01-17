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
(local (include-book "util/arithmetic"))

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

<li>@(see vl-constint-p): an integer literal with no X or Z bits,</li>

<li>@(see vl-weirdint-p): an integer literal with some X or Z bits,</li>

<li>@(see vl-real-p): a \"real literal\", i.e., a floating point number,</li>

<li>@(see vl-string-p): a string literal,</li>

<li>@(see vl-id-p): a simple, non-hierarchical identifier,</li>

<li>@(see vl-hidpiece-p): one piece of a hierarchical identifier,</li>

<li>@(see vl-funname-p): the name of an ordinary function, or</li>

<li>@(see vl-sysfunname-p): the name of a system function (e.g.,
@('$display')).</li>

</ul>

<p>The last three of these are probably not things you would ordinarily think
of as atomic expressions.  However, by accepting them as atomic expressions, we
are able to achieve the straightforward recursive structure we desire.</p>

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

(defsection *vl-ops-table*
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
<li>@('foo[1]')      becomes @(':vl-bitselect') or @(':vl-array-index') (arity 2)</li>
<li>@('foo[3 : 1]')  becomes @(':vl-partselect-colon') (arity 3)</li>
<li>@('foo[3 +: 1]') becomes @(':vl-partselect-pluscolon') (arity 3)</li>
<li>@('foo[3 -: 1]') becomes @(':vl-partselect-minuscolon') (arity 3)</li>
</ul>

<p>Note that upon parsing, there are no @(':vl-array-index') operators; these
must be introduced by the @(see array-indexing) transform.</p>

<h5>Concatenation and Replication Operators</h5>

<ul>
<li>@('{1, 2, 3, ...}') becomes @(':vl-concat') (arity @('nil'))</li>
<li>@('{ 3 { 2, 1 } }') becomes @(':vl-multiconcat') (arity 2)</li>
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
<li>@('foo[3].bar') becomes @(':vl-hid-arraydot') (arity 3)</li>
</ul>"

  (defconst *vl-ops-table*
    (list
     ;; Basic Unary Operators
     (cons :vl-unary-plus            1) ;;; +
     (cons :vl-unary-minus           1) ;;; -
     (cons :vl-unary-lognot          1) ;;; !
     (cons :vl-unary-bitnot          1) ;;; ~
     (cons :vl-unary-bitand          1) ;;; &
     (cons :vl-unary-nand            1) ;;; ~&
     (cons :vl-unary-bitor           1) ;;; |
     (cons :vl-unary-nor             1) ;;; ~|
     (cons :vl-unary-xor             1) ;;; ^
     (cons :vl-unary-xnor            1) ;;; ~^ or ^~

     ;; Basic Binary Operators
     (cons :vl-binary-plus           2) ;;; +
     (cons :vl-binary-minus          2) ;;; -
     (cons :vl-binary-times          2) ;;; *
     (cons :vl-binary-div            2) ;;; /
     (cons :vl-binary-rem            2) ;;; %
     (cons :vl-binary-eq             2) ;;; ==
     (cons :vl-binary-neq            2) ;;; !=
     (cons :vl-binary-ceq            2) ;;; ===
     (cons :vl-binary-cne            2) ;;; !==
     (cons :vl-binary-logand         2) ;;; &&
     (cons :vl-binary-logor          2) ;;; ||
     (cons :vl-binary-power          2) ;;; **
     (cons :vl-binary-lt             2) ;;; <
     (cons :vl-binary-lte            2) ;;; <=
     (cons :vl-binary-gt             2) ;;; >
     (cons :vl-binary-gte            2) ;;; >=
     (cons :vl-binary-bitand         2) ;;; &
     (cons :vl-binary-bitor          2) ;;; |
     (cons :vl-binary-xor            2) ;;; ^
     (cons :vl-binary-xnor           2) ;;; ~^ or ^~
     (cons :vl-binary-shr            2) ;;; >>
     (cons :vl-binary-shl            2) ;;; <<
     (cons :vl-binary-ashr           2) ;;; >>>
     (cons :vl-binary-ashl           2) ;;; <<<

     ;; Basic Ternary Operators
     (cons :vl-qmark                 3) ;;; e.g., 1 ? 2 : 3
     (cons :vl-mintypmax             3) ;;; e.g., (1 : 2 : 3)

     ;; Selection Operators
     (cons :vl-bitselect             2) ;;; e.g., foo[1]
     (cons :vl-array-index           2) ;;; e.g., foo[1]
     (cons :vl-partselect-colon      3) ;;; e.g., foo[3:1]
     (cons :vl-partselect-pluscolon  3) ;;; e.g., foo[3 +: 1]
     (cons :vl-partselect-minuscolon 3) ;;; e.g., foo[3 -: 1]

     ;; Concatenation and Replication Operators
     (cons :vl-concat                nil) ;;; e.g., { 1, 2, 3 }
     (cons :vl-multiconcat           2)   ;;; e.g., { 3 { 2, 1 } }

     ;; Function Calls
     (cons :vl-funcall               nil) ;;; e.g., foo(1,2,3)
     (cons :vl-syscall               nil) ;;; e.g., $foo(1,2,3)

     ;; Hierarchical Identifiers
     (cons :vl-hid-dot               2) ;;; e.g., foo.bar
     (cons :vl-hid-arraydot          3) ;;; e.g., foo[3].bar
     )))


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

(deflist vl-oplist-p (x)
  (vl-op-p x))


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
  (cdr (assoc x *vl-ops-table*)))



(defenum vl-exprtype-p
  (:vl-signed :vl-unsigned)
  :short "Valid types for expressions."
  :long "<p>Each expression should be either @(':vl-signed') or
@(':vl-unsigned').  We may eventually expand this to include other types, such
as real and string.</p>")


(define vl-maybe-exprtype-p (x)
  :short "Recognizer for an @(see vl-exprtype-p) or @('nil')."
  :long "<p>We use this for the @('finaltype') fields in our expressions.  It
allows us to represent expressions whose types have not yet been computed.</p>"
  :inline t
  (or (not x)
      (vl-exprtype-p x))
  ///
  (defthm vl-maybe-exprtype-p-when-vl-exprtype-p
    (implies (vl-exprtype-p x)
             (vl-maybe-exprtype-p x)))

  (defthm vl-exprtype-p-when-vl-maybe-exprtype-p
    (implies (vl-maybe-exprtype-p x)
             (equal (vl-exprtype-p x)
                    (if x t nil))))

  (defthm type-when-vl-maybe-exprtype-p
    (implies (vl-maybe-exprtype-p x)
             (and (symbolp x)
                  (not (equal x t))))
    :rule-classes :compound-recognizer))


(defaggregate vl-constint
  :short "Representation for constant integer literals with no X or Z bits."
  :tag :vl-constint
  :hons t
  :legiblep nil

  ((value      natp
               :rule-classes :type-prescription
               "The most important part of a constant integer.  Even
                immediately upon parsing the value has already been determined
                and is available to you as an ordinary natural number.")

   (origwidth  posp
               :rule-classes :type-prescription
               "Subtle; generally should <b>not be used</b>; see below.")

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
  ((upper-bound-of-vl-constint->value
    (< value (expt '2 origwidth))
    :rule-classes ((:rewrite) (:linear))))

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


(defaggregate vl-weirdint
  :short "Representation for constant integer literals with X or Z bits."
  :tag :vl-weirdint
  :hons t
  :legiblep nil

  ((bits        vl-bitlist-p
                "An MSB-first list of the four-valued Verilog bits making up
                 this constant's value; see @(see vl-bit-p).")

   (origwidth   posp
                :rule-classes :type-prescription
                "Subtle; generally should <b>not be used</b>; see below.")

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
  ((len-of-vl-weirdint->bits
    (equal (len bits) origwidth)
    :rule-classes ((:rewrite)
                   (:type-prescription
                    :corollary (implies (force (vl-weirdint-p x))
                                        (consp (vl-weirdint->bits x)))))))

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


(defaggregate vl-string
  :short "Representation for string literals."
  :tag :vl-string
  :legiblep nil

  ((value stringp
          :rule-classes :type-prescription
          "An ordinary ACL2 string where, e.g., special sequences like @('\\n')
           and @('\\t') have been resolved into real newline and tab
           characters, etc.")))


(defaggregate vl-real
  :short "Representation of real (floating point) literals."
  :tag :vl-real
  :legiblep nil

  ((value   stringp
            :rule-classes :type-prescription
            "The actual characters found in the source code, i.e., it might be
             a string such as @('\"3.41e+12\"')."))

  :long "<p>We have almost no support for working with real numbers.  You
should probably not rely on our current representation, since q we will almost
certainly want to change it as soon as we want to do anything with real
numbers.</p>")


(defaggregate vl-id
  :short "Representation for simple identifiers."
  :tag :vl-id
  :hons t
  :legiblep nil

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


(defaggregate vl-hidpiece
  :short "Represents one piece of a hierarchical identifier."
  :tag :vl-hidpiece
  :legiblep nil

  ((name stringp :rule-classes :type-prescription))

  :long "<p>We represent hierarchical identifiers like
@('top.processor[2].reset') as non-atomic expressions.  To represent this
particular expression, we build a @(see vl-expr-p) that is something like
this:</p>

@({
 (:vl-hid-dot top (:vl-hid-arraydot processor 2 reset))
})

<p>In other words, the @(':vl-hid-dot') operator is used to join pieces of a
hierarchical identifier, and @(':vl-hid-arraydot') is used when instance arrays
are accessed.</p>

<p>To add slightly more precision, our representation is really more like the
following:</p>

@({
 (:vl-hid-dot (hidpiece \"top\")
              (:vl-hid-arraydot (hidpiece \"processor\")
                                (constint 2)
                                (hidpiece \"reset\")))
})

<p>In other words, the individual identifiers used throughout a hierarchical
identifier are actually @('vl-hidpiece-p') objects instead of @(see vl-id-p)
objects.</p>

<p>We make this distinction so that in the ordinary course of working with the
parse tree, you can freely assume that any @('vl-id-p') you come across really
refers to some module item, and not to some part of a hierarchical
identifier.</p>")


(defaggregate vl-sysfunname
  :short "Represents a system function name."
  :tag :vl-sysfunname
  :legiblep nil

  ((name stringp :rule-classes :type-prescription))

  :long "<p>We use a custom representation for the names of system functions,
so that we do not confuse them with ordinary @(see vl-id-p) objects.</p>")


(defaggregate vl-funname
  :short "Represents a (non-system) function name."
  :tag :vl-funname
  :legiblep nil

  ((name stringp :rule-classes :type-prescription))

  :long "<p>We use a custom representation for the names of functions, so that
we do not confuse them with ordinary @(see vl-id-p) objects.</p>")


(define vl-atomguts-p (x)
  :short "The main contents of a @(see vl-atom-p)."
  :long "<p>The guts of an atom are its main contents.  See @(see vl-expr-p)
for a discussion of the valid types.</p>"

  ;; BOZO some kind of defsum macro could eliminate a lot of this boilerplate

  (mbe :logic (or (vl-constint-p x)
                  (vl-weirdint-p x)
                  (vl-string-p x)
                  (vl-real-p x)
                  (vl-id-p x)
                  (vl-hidpiece-p x)
                  (vl-funname-p x)
                  (vl-sysfunname-p x))
       :exec (case (tag x)
               (:vl-id       (vl-id-p x))
               (:vl-constint (vl-constint-p x))
               (:vl-weirdint (vl-weirdint-p x))
               (:vl-string   (vl-string-p x))
               (:vl-real     (vl-real-p x))
               (:vl-hidpiece (vl-hidpiece-p x))
               (:vl-funname  (vl-funname-p x))
               (otherwise    (vl-sysfunname-p x))))

  ///

  (defthm consp-when-vl-atomguts-p
    (implies (vl-atomguts-p x)
             (consp x))
    :rule-classes :compound-recognizer)

  (defthm vl-atomguts-p-when-vl-constint-p
    (implies (vl-constint-p x)
             (vl-atomguts-p x)))

  (defthm vl-atomguts-p-when-vl-weirdint-p
    (implies (vl-weirdint-p x)
             (vl-atomguts-p x)))

  (defthm vl-atomguts-p-when-vl-real-p
    (implies (vl-real-p x)
             (vl-atomguts-p x)))

  (defthm vl-atomguts-p-when-vl-string-p
    (implies (vl-string-p x)
             (vl-atomguts-p x)))

  (defthm vl-atomguts-p-when-vl-id-p
    (implies (vl-id-p x)
             (vl-atomguts-p x)))

  (defthm vl-atomguts-p-when-vl-hidpiece-p
    (implies (vl-hidpiece-p x)
             (vl-atomguts-p x)))

  (defthm vl-atomguts-p-when-vl-sysfunname-p
    (implies (vl-sysfunname-p x)
             (vl-atomguts-p x)))

  (defthm vl-atomguts-p-when-vl-funname-p
    (implies (vl-funname-p x)
             (vl-atomguts-p x)))

  (defthm vl-constint-p-by-tag-when-vl-atomguts-p
    (implies (and (equal (tag x) :vl-constint)
                  (vl-atomguts-p x))
             (vl-constint-p x)))

  (defthm vl-weirdint-p-by-tag-when-vl-atomguts-p
    (implies (and (equal (tag x) :vl-weirdint)
                  (vl-atomguts-p x))
             (vl-weirdint-p x)))

  (defthm vl-string-p-by-tag-when-vl-atomguts-p
    (implies (and (equal (tag x) :vl-string)
                  (vl-atomguts-p x))
             (vl-string-p x)))

  (defthm vl-real-p-by-tag-when-vl-atomguts-p
    (implies (and (equal (tag x) :vl-real)
                  (vl-atomguts-p x))
             (vl-real-p x)))

  (defthm vl-id-p-by-tag-when-vl-atomguts-p
    (implies (and (equal (tag x) :vl-id)
                  (vl-atomguts-p x))
             (vl-id-p x)))

  (defthm vl-hidpiece-p-by-tag-when-vl-atomguts-p
    (implies (and (equal (tag x) :vl-hidpiece)
                  (vl-atomguts-p x))
             (vl-hidpiece-p x)))

  (defthm vl-funname-p-by-tag-when-vl-atomguts-p
    (implies (and (equal (tag x) :vl-funname)
                  (vl-atomguts-p x))
             (vl-funname-p x)))

  (defthm vl-sysfunname-p-by-tag-when-vl-atomguts-p
    (implies (and (equal (tag x) :vl-sysfunname)
                  (vl-atomguts-p x))
             (vl-sysfunname-p x))))


(define vl-fast-id-p ((x vl-atomguts-p))
  :parents (vl-atomguts-p vl-id-p)
  :short "Faster version of @(see vl-id-p), given that @(see vl-atomguts-p) is
already known."
  :long "<p>We leave this function enabled and reason about @('vl-id-p')
instead.</p>"
  :inline t
  :enabled t
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
  (mbe :logic (vl-sysfunname-p x)
       :exec (eq (tag x) :vl-sysfunname)))


(defaggregate vl-atom
  :short "Representation of atomic expressions."
  :long "<p>See the discussion in @(see vl-expr-p).</p>"
  :tag :vl-atom
  :legiblep nil

  ((guts       vl-atomguts-p)

   (finalwidth maybe-natp
               :rule-classes :type-prescription)

   (finaltype  vl-maybe-exprtype-p
               :rule-classes
               ((:rewrite)
                (:type-prescription
                 :corollary
                 (implies (force (vl-atom-p x))
                          (and (symbolp (vl-atom->finaltype x))
                               (not (equal (vl-atom->finaltype x) t)))))))))

(deflist vl-atomlist-p (x)
  (vl-atom-p x)
  :elementp-of-nil nil)


(defaggregate vl-nonatom
  :short "Structural validity of non-atomic expressions."
  :long "<p>This is only a simple structural check, and does not imply
@('vl-expr-p').  See @(see vl-expr-p) for details.</p>"
  :tag :vl-nonatom
  :legiblep nil

  ((op   vl-op-p
         :rule-classes
         ((:rewrite)
          (:type-prescription
           :corollary
           ;; I previously forced the hyp, but it got irritating because it
           ;; kept screwing up termination proofs.  Consider case-split?
           (implies (vl-nonatom-p x)
                    (and (symbolp (vl-nonatom->op x))
                         (not (equal (vl-nonatom->op x) t))
                         (not (equal (vl-nonatom->op x) nil)))))))

   (atts "No requirements (yet) due to mutual recursion.")
   (args "No requirements (yet) due to mutual recursion.")

   (finalwidth maybe-natp
               :rule-classes :type-prescription)

   (finaltype  vl-maybe-exprtype-p
               :rule-classes
               ((:rewrite)
                (:type-prescription
                 :corollary
                 ;; I previously forced this, but maybe that's a bad idea for
                 ;; the same reasons as vl-op-p-of-vl-nonatom->op?
                 (implies (vl-nonatom-p x)
                          (and (symbolp (vl-nonatom->finaltype x))
                               (not (equal (vl-nonatom->finaltype x) t))))))))

  :rest
  ((defthm acl2-count-of-vl-nonatom->args
     (and (<= (acl2-count (vl-nonatom->args x))
              (acl2-count x))
          (implies (consp x)
                   (< (acl2-count (vl-nonatom->args x))
                      (acl2-count x))))
     :hints(("Goal" :in-theory (enable vl-nonatom->args)))
     :rule-classes ((:rewrite) (:linear)))

   (defthm acl2-count-of-vl-nonatom->args-when-vl-nonatom->op
     ;; This is a funny rule that is occasionally useful in avoiding artificial
     ;; termination checks for functions that recur over expressions.
     (implies (vl-nonatom->op x)
              (not (equal (acl2-count (vl-nonatom->args x))
                          (acl2-count x))))
     :hints(("Goal" :in-theory (enable vl-nonatom->op vl-nonatom->args))))

   (defthm acl2-count-of-vl-nonatom->atts
     (and (<= (acl2-count (vl-nonatom->atts x))
              (acl2-count x))
          (implies (consp x)
                   (< (acl2-count (vl-nonatom->atts x))
                      (acl2-count x))))
     :hints(("Goal" :in-theory (enable vl-nonatom->atts)))
     :rule-classes ((:rewrite) (:linear)))))


(mutual-recursion
 (defund vl-expr-p (x)
   (declare (xargs :guard t))
   (or (vl-atom-p x)
       (and (vl-nonatom-p x)
            (let ((name  (vl-nonatom->op x))
                  (atts  (vl-nonatom->atts x))
                  (args  (vl-nonatom->args x)))
              (and (vl-atts-p atts)
                   (vl-exprlist-p args)
                   (let ((arity (vl-op-arity name)))
                     (or (not arity)
                         (equal (len args) arity))))))))

 (defund vl-atts-p (x)
   ;; Search for "defsection vl-atts-p" below for documentation.
   (declare (xargs :guard t))
   (if (consp x)
       (and (consp (car x))
            (stringp (caar x))
            (or (not (cdar x))
                (vl-expr-p (cdar x)))
            (vl-atts-p (cdr x)))
     (eq x nil)))

 (defund vl-exprlist-p (x)
   (declare (xargs :guard t))
   (if (consp x)
       (and (vl-expr-p (car x))
            (vl-exprlist-p (cdr x)))
     t)))

(defsection vl-expr-p-basics
  :extension vl-expr-p

  (local (in-theory (enable vl-expr-p)))

  (defthm vl-expr-p-when-vl-atom-p
    (implies (vl-atom-p x)
             (vl-expr-p x)))

  (defthm vl-atom-p-by-tag-when-vl-expr-p
    (implies (and (equal (tag x) :vl-atom)
                  (vl-expr-p x))
             (vl-atom-p x)))

  (defthm consp-when-vl-expr-p
    (implies (vl-expr-p x)
             (consp x))
    :rule-classes :compound-recognizer
    :hints(("Goal" :expand (vl-expr-p x))))

  (defthm vl-expr-p-of-vl-nonatom
    (implies (and (force (vl-op-p op))
                  (force (vl-atts-p atts))
                  (force (vl-exprlist-p args))
                  (force (implies (vl-op-arity op)
                                  (equal (len args) (vl-op-arity op))))
                  (force (maybe-natp finalwidth))
                  (force (vl-maybe-exprtype-p finaltype)))
             (vl-expr-p (make-vl-nonatom :op op
                                         :atts atts
                                         :args args
                                         :finalwidth finalwidth
                                         :finaltype finaltype))))

  (defthm len-of-vl-nonatom->args-when-vl-expr-p
    (implies (and (vl-op-arity (vl-nonatom->op x))
                  (force (vl-expr-p x))
                  (force (vl-nonatom-p x)))
             (equal (len (vl-nonatom->args x))
                    (vl-op-arity (vl-nonatom->op x)))))

  (defthm vl-exprlist-p-of-vl-nonatom->args
    (implies (and (force (vl-expr-p x))
                  (force (vl-nonatom-p x)))
             (vl-exprlist-p (vl-nonatom->args x))))

  (defthm vl-nonatom-p-when-not-vl-atom-p
    ;; BOZO strengthen?  rewrite vl-nonatom-p to "not vl-atom-p"?
    (implies (and (not (vl-atom-p x))
                  (vl-expr-p x))
             (vl-nonatom-p x)))

  (defthm vl-atts-p-of-vl-nonatom->atts
    (implies (and (force (vl-expr-p x))
                  (force (vl-nonatom-p x)))
             (vl-atts-p (vl-nonatom->atts x)))))


(define vl-fast-atom-p ((x vl-expr-p))
  :parents (vl-atom-p vl-expr-p)
  :short "Faster version of @(see vl-atom-p), given that @(see vl-expr-p) is
already known."
  :long "<p>We leave this function enabled and reason about @('vl-atom-p')
instead.</p>"
  :inline t
  :enabled t
  (mbe :logic (vl-atom-p x)
       :exec (eq (tag x) :vl-atom)))

(define vl-expr->finalwidth ((x vl-expr-p))
  :returns (width? maybe-natp :hyp :fguard :rule-classes :type-prescription)
  :short "Get the @('finalwidth') from an expression."
  :long "<p>See @(see vl-expr-p) for a discussion of widths.  The result is a
@(see maybe-natp).</p>"
  :inline t
  (if (eq (tag x) :vl-atom)
      (vl-atom->finalwidth x)
    (vl-nonatom->finalwidth x))
  :prepwork ((local (in-theory (enable vl-expr-p))))
  ///
  (defthm vl-expr->finalwidth-of-vl-atom
    (equal (vl-expr->finalwidth (vl-atom guts finalwidth finaltype))
           finalwidth))

  (defthm vl-expr->finalwidth-of-vl-nonatom
    (equal (vl-expr->finalwidth (make-vl-nonatom :op op
                                            :atts atts
                                            :args args
                                            :finalwidth finalwidth
                                            :finaltype finaltype))
           finalwidth)))

(define vl-expr->finaltype ((x vl-expr-p))
  :returns (type? vl-maybe-exprtype-p
                  :hyp :fguard
                  :rule-classes ((:rewrite)
                                 (:type-prescription
                                  :corollary (implies (force (vl-expr-p x))
                                                      (and (symbolp (vl-expr->finaltype x))
                                                           (not (equal (vl-expr->finaltype x) t)))))))
  :short "Get the @('finaltype') from an expression."
  :long "<p>See @(see vl-expr-p) for a discussion of types.  The result
is a @(see vl-maybe-exprtype-p).</p>"
  :inline t
  (if (eq (tag x) :vl-atom)
      (vl-atom->finaltype x)
    (vl-nonatom->finaltype x))

  :prepwork ((local (in-theory (enable vl-expr-p))))
  ///
  (defthm vl-expr->finaltype-of-vl-atom
    (equal (vl-expr->finaltype (vl-atom guts finalwidth finaltype))
           finaltype))

  (defthm vl-expr->finaltype-of-vl-nonatom
    (equal (vl-expr->finaltype (make-vl-nonatom :op op
                                                :atts atts
                                                :args args
                                                :finalwidth finalwidth
                                                :finaltype finaltype))
           finaltype)))


(defsection vl-atts-p
  :short "Representation of @('(* foo = 3, baz *)') style attributes."

  :long "<p>Verilog 2005 allows many constructs, (e.g., module instances, wire
declarations, assignments, subexpressions, and so on) to be annotated with
<i>attributes</i>.  Each individual attribute can either be a single key with
no value (e.g., @('baz') above), or can have the form @('key = value').  The
keys are always identifiers, and the values (if provided) are expressions.</p>

<p>We represent attributes as alists mapping keys to their values.  We use
ordinary ACL2 strings to represent the keys.  Each value is represented by a
@(see vl-expr-p) object, and keys with no values are bound to @('nil')
instead.</p>

<h3>Attributes Used by VL</h3>

<p><b>BOZO</b> this list may not be complete.  Try to keep it up to date.</p>

<dl>

<dt>Modules</dt>

<dd>@('VL_HANDS_OFF') indicates that the module is special and should be left
alone by transformations.  It is generally intended to be used for built-in VL
modules like @('VL_1_BIT_FLOP') and @('VL_1_BIT_LATCH').</dd>


<dt>Expressions</dt>

<dd>@('VL_ORIG_EXPR'), with some value, is added to many expressions in the
@(see origexprs) transformation.  It allows us to remember the \"original
version\" of the expression before simplification has taken place.</dd>

<dd>@('VL_ZERO_EXTENSION') is added when we create certain zero-extension
expressions, mainly to pad operands during @(see expression-sizing).</dd>


<dt>Net Declarations</dt>

<dd>@('VL_IMPLICIT'), with no value, is given to implicitly declared wires by
@(see make-implicit-wires).  This attribute also plays a role in @(see
typo-detection).</dd>

<dd>@('VL_PORT_IMPLICIT'), with no value, is given to wires that are declared
to be ports (i.e., @('input a;')) but which are not also declared to be
wires (i.e., @('wire a;')) by @(see make-implicit-wires)</dd>

<dd>@('VL_UNUSED') and @('VL_MAYBE_UNUSED') may be added by @(see use-set) when
a wire appears to be unused.</dd>

<dd>@('VL_UNSET') and @('VL_MAYBE_UNSET') may be added by @(see use-set) when a
wire appears to be unset.</dd>

<dd>@('VL_ACTIVE_HIGH') and @('VL_ACTIVE_LOW') may be declared by the user or
inferred in the cross-active transformation.</dd>

<dd>@('VL_CONVERTED_REG') may be attached during latch/flop inference, when a
@('reg') is turned into a @('wire').</dd>


<dt>Port Declarations</dt>

<dd>@('VL_ACTIVE_HIGH') and @('VL_ACTIVE_LOW') may be declared by the user or
inferred in the cross-active transformation.</dd>


<dt>Assignments</dt>

<dd>@('TRUNC_<i>WIDTH</i>') attributes are given to assignment statements which
are involve implicit truncations, by @(see trunc).  <b>BOZO</b> probably change
to @('VL_TRUNC = width') format.</dd>


<dt>Gate Instances</dt>

<dd>@('VL_FROM_GATE_ARRAY'), with no value, is given to gate instances that are
the result of splitting an array such as @('buf foo [13:0] (o, i);') by @(see
replicate).  This property is also given to module instances as described
below.</dd>

<dd>@('VL_GATESPLIT') is added when certain gates are simplified, e.g., when we
split @('not(o1,o2,...,on, i);') into @('not(o1,i);'), @('not(o2,i)'), ...,
@('not(on, i);') in @(see gatesplit).  <b>BOZO</b> make this annotation more
consistent.</dd>


<dt>Module Instances</dt>

<dd>@('VL_FROM_GATE_ARRAY'), with no value, is given to module instances that
are the result of splitting an array such as @('mymod foo [13:0] (o, i);') by
@(see replicate).  This property is also given to gate instances as described
above.  <b>BOZO</b> probably switch this to VL_FROM_MOD_ARRAY.</dd>

<dd>@('VL_GATE_REDUX'), with no value, is given to module instances that are
the result of converting gates such as @('bufif0'), @('notif1'), @('pmos'),
etc., into module instances.  It is also given to certain gate instances as
described above.</dd>


<dt>Plain Arguments</dt>

<dd>@('VL_ACTIVE_HIGH') or @('VL_ACTIVE_LOW') may be added during @(see
argresolve), and indicate whether the corresponding formal is considered active
high or low.</dd>

</dl>"

  (local (in-theory (enable vl-atts-p)))

  (defthm vl-atts-p-when-not-consp
    (implies (not (consp x))
             (equal (vl-atts-p x)
                    (not x))))

  (defthm vl-atts-of-cons
    (equal (vl-atts-p (cons a x))
           (and (consp a)
                (stringp (car a))
                (or (not (cdr a))
                    (vl-expr-p (cdr a)))
                (vl-atts-p x))))

  (defthm vl-atts-p-of-append
    (implies (and (vl-atts-p x)
                  (vl-atts-p y))
             (vl-atts-p (append x y)))
    :hints(("Goal" :induct (len x))))

  (defthm true-listp-when-vl-atts-p
    (implies (vl-atts-p x)
             (true-listp x))
    :hints(("Goal" :induct (len x)))
    :rule-classes ((:rewrite) (:compound-recognizer)))

  (defthm alistp-when-vl-atts-p
    (implies (vl-atts-p x)
             (alistp x))
    :hints(("Goal" :induct (len x))))

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


(deflist vl-exprlist-p (x)
  (vl-expr-p x)
  :elementp-of-nil nil
  :verify-guards nil
  :already-definedp t
  :parents (syntax)

  :rest
  ( ;; These are useful for seeing that arguments exist.
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
     :rule-classes ((:rewrite :backchain-limit-lst 1)))))

(defprojection vl-exprlist->finalwidths (x)
  (vl-expr->finalwidth x)
  :guard (vl-exprlist-p x)
  :result-type vl-maybe-nat-listp
  :nil-preservingp t
  :parents (vl-exprlist-p))

(defprojection vl-exprlist->finaltypes (x)
  (vl-expr->finaltype x)
  :guard (vl-exprlist-p x)
  :nil-preservingp t
  :parents (vl-exprlist-p))


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


(define vl-maybe-expr-p (x)
  :parents (syntax vl-expr-p)
  :short "Representation for a @(see vl-expr-p) or @('nil')."
  :long "<p>This is a basic option type for expressions.</p>"
  :inline t
  (or (not x)
      (vl-expr-p x))
  ///
  (defthm vl-maybe-expr-p-when-vl-expr-p
    (implies (vl-expr-p x)
             (vl-maybe-expr-p x)))

  (defthm vl-expr-p-when-vl-maybe-expr-p
    (implies (vl-maybe-expr-p x)
             (equal (vl-expr-p x)
                    (if x t nil))))

  (defthm type-when-vl-maybe-expr-p
    (implies (vl-maybe-expr-p x)
             (or (consp x)
                 (not x)))
    :rule-classes :compound-recognizer))


(define vl-expr-induct (flag x)
  :short "A basic induction scheme for @(see vl-expr-p)."
  :long "<p>BOZO should we really have this, or would make-flag be better?  I
guess this is in some ways cleaner.</p>"
  :verify-guards nil
  :enabled t
  :measure (two-nats-measure (acl2-count x)
                             (if (eq flag 'expr) 1 0))
  (cond ((eq flag 'expr)
         (if (vl-atom-p x)
             nil
           (list (vl-expr-induct 'atts (vl-nonatom->atts x))
                 (vl-expr-induct 'list (vl-nonatom->args x)))))
        ((eq flag 'atts)
         (if (consp x)
             (list (vl-expr-induct 'expr (cdar x))
                   (vl-expr-induct 'atts (cdr x)))
           nil))
        (t
         (if (consp x)
             (list (vl-expr-induct 'expr (car x))
                   (vl-expr-induct 'list (cdr x)))
           nil))))


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
      (implies (and arity
                    (force (vl-expr-p x))
                    (force (not (vl-atom-p x))))
               (and (implies (<= 1 arity)
                             (vl-nonatom->args x))
                    (iff (first (vl-nonatom->args x))
                         (<= 1 arity))
                    (equal (consp (vl-nonatom->args x))
                           (<= 1 arity)))))
    :hints(("Goal"
            :expand ((vl-expr-p x))
            :use ((:instance iff-when-vl-expr-p (x (car (vl-nonatom->args x))))))))

  (defthm arg2-exists-by-arity
    (let ((arity (vl-op-arity (vl-nonatom->op x))))
      (implies (and arity
                    (force (vl-expr-p x))
                    (force (not (vl-atom-p x))))
               (and (implies (<= 2 arity) (cdr (vl-nonatom->args x)))
                    (iff (second (vl-nonatom->args x)) (<= 2 arity))
                    (equal (consp (cdr (vl-nonatom->args x))) (<= 2 arity)))))
    :hints(("Goal"
            :expand ((vl-expr-p x))
            :use ((:instance iff-when-vl-expr-p (x (car (vl-nonatom->args x))))
                  (:instance iff-when-vl-expr-p (x (cadr (vl-nonatom->args x))))))))

  (defthm arg3-exists-by-arity
    (let ((arity (vl-op-arity (vl-nonatom->op x))))
      (implies (and arity
                    (force (vl-expr-p x))
                    (force (not (vl-atom-p x))))
               (and (implies (<= 3 arity) (cddr (vl-nonatom->args x)))
                    (iff (third (vl-nonatom->args x)) (<= 3 arity))
                    (equal (consp (cddr (vl-nonatom->args x))) (<= 3 arity)))))
    :hints(("Goal"
            :expand ((vl-expr-p x))
            :use ((:instance iff-when-vl-expr-p (x (car (vl-nonatom->args x))))
                  (:instance iff-when-vl-expr-p (x (cadr (vl-nonatom->args x))))
                  (:instance iff-when-vl-expr-p (x (caddr (vl-nonatom->args x)))))))))

