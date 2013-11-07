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
(include-book "util/defs")
(include-book "util/bits")
(include-book "util/commentmap")
(include-book "util/warnings")
(include-book "util/echars")
(include-book "tools/flag" :dir :system)
(local (include-book "util/arithmetic"))

(defxdoc modules
  :parents (vl)
  :short "Representation of Verilog modules."

  :long "<p>We now describe our representation of Verilog modules.  For each
kind of Verilog construct (expressions, statements, declarations, instances,
etc.) we introduce recognizer, constructor, and accessor functions that enforce
certain basic well-formedness criteria.</p>

<p>These structures correspond fairly closely to parse trees in the Verilog
grammar, although we make many simplifcations and generally present a much more
regular view of the source code.</p>")



(defsection *vl-ops-table*
  :parents (vl-expr-p)
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
  :parents (vl-expr-p)
  :short "Recognizer for valid operators."

  :long "<p>@(call vl-op-p) checks that @('x') is one of the operators listed
in the @(see *vl-ops-table*).</p>

<p>We prefer to use @('vl-op-p') instead of looking up operators directly in
the table, since this way we can disable @('vl-op-p') and avoid large case
splits.</p>"

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
  (vl-op-p x)
  :guard t
  :parents (vl-expr-p))




(define vl-op-arity ((x vl-op-p))
  :inline t
  :parents (vl-expr-p)
  :short "Look up the arity of an operator."

  :long "<p>@(call vl-op-arity) determines the arity of the operator @('x') by
consulting the @(see *vl-ops-table*).  If @('x') does not have a fixed
arity (e.g., it might be a function call or concatenation operation), then we
return @('nil').</p>

<p>We prefer to use @('vl-op-arity') instead of looking up operators directly
in the table, since this way we can disable @('vl-op-arity') and avoid large
case splits.</p>"

  (cdr (assoc x *vl-ops-table*))

  ///
  (defthm type-of-vl-op-arity
    (vl-maybe-natp (vl-op-arity x))
    :rule-classes :type-prescription))



(defenum vl-exprtype-p (:vl-signed :vl-unsigned)
  :parents (vl-expr-p)
  :short "Valid types for expressions."
  :long "<p>Each expression should be either @(':vl-signed') or
@(':vl-unsigned').  We may eventually expand this to include other types, such
as real and string.</p>")



(define vl-maybe-exprtype-p (x)
  :inline t
  :parents (vl-expr-p)
  :short "Recognizer for an @(see vl-exprtype-p) or @('nil')."

  :long "<p>We use this for the @('sign') fields in our expressions.  It allows
us to represent expressions whose signs have not yet been computed.</p>"

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
  :parents (vl-expr-p)
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
literal.  See Section 3.5.1 of the spec.</p>

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
10) of the spec.</p>

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
  :parents (vl-expr-p)
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
  :parents (vl-expr-p)
  :short "Representation for string literals."
  :tag :vl-string
  :legiblep nil

  ((value stringp
          :rule-classes :type-prescription
          "An ordinary ACL2 string where, e.g., special sequences like @('\\n')
           and @('\\t') have been resolved into real newline and tab
           characters, etc.")))


(defaggregate vl-real
  :parents (vl-expr-p)
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
  :parents (vl-expr-p)
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
  :parents (vl-expr-p)
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
  :parents (vl-expr-p)
  :short "Represents a system function name."
  :tag :vl-sysfunname
  :legiblep nil

  ((name stringp :rule-classes :type-prescription))

  :long "<p>We use a custom representation for the names of system functions,
so that we do not confuse them with ordinary @(see vl-id-p) objects.</p>")


(defaggregate vl-funname
  :parents (vl-expr-p)
  :short "Represents a (non-system) function name."
  :tag :vl-funname
  :legiblep nil

  ((name stringp :rule-classes :type-prescription))

  :long "<p>We use a custom representation for the names of functions, so that
we do not confuse them with ordinary @(see vl-id-p) objects.</p>")


(define vl-atomguts-p (x)
  :parents (vl-expr-p)
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
  :inline t
  :enabled t
  :parents (vl-atomguts-p vl-id-p)
  :short "Faster version of @(see vl-id-p), given that @(see vl-atomguts-p) is
already known."
  :long "<p>We leave this function enabled and reason about @('vl-id-p')
instead.</p>"
  (mbe :logic (vl-id-p x)
       :exec (eq (tag x) :vl-id)))

(define vl-fast-constint-p ((x vl-atomguts-p))
  :inline t
  :enabled t
  :parents (vl-atomguts-p vl-constint-p)
  :short "Faster version of @(see vl-constint-p), given that @(see
vl-atomguts-p) is already known."
  :long "<p>We leave this function enabled and reason about @('vl-constint-p')
instead.</p>"
  (mbe :logic (vl-constint-p x)
       :exec (eq (tag x) :vl-constint)))

(define vl-fast-weirdint-p ((x vl-atomguts-p))
  :inline t
  :enabled t
  :parents (vl-atomguts-p vl-weirdint-p)
  :short "Faster version of @(see vl-weirdint-p), given that @(see
vl-atomguts-p) is already known."
  :long "<p>We leave this function enabled and reason about @('vl-weirdint-p')
instead.</p>"
  (mbe :logic (vl-weirdint-p x)
       :exec (eq (tag x) :vl-weirdint)))

(define vl-fast-string-p ((x vl-atomguts-p))
  :inline t
  :enabled t
  :parents (vl-atomguts-p vl-string-p)
  :short "Faster version of @(see vl-string-p), given that @(see
vl-atomguts-p) is already known."
  :long "<p>We leave this function enabled and reason about @('vl-string-p')
instead.</p>"
  (mbe :logic (vl-string-p x)
       :exec (eq (tag x) :vl-string)))

(define vl-fast-hidpiece-p ((x vl-atomguts-p))
  :inline t
  :enabled t
  :parents (vl-atomguts-p vl-hidpiece-p)
  :short "Faster version of @(see vl-hidpiece-p), given that @(see
vl-atomguts-p) is already known."
  :long "<p>We leave this function enabled and reason about @('vl-hidpiece-p')
instead.</p>"
  (mbe :logic (vl-hidpiece-p x)
       :exec (eq (tag x) :vl-hidpiece)))

(define vl-fast-funname-p ((x vl-atomguts-p))
  :inline t
  :enabled t
  :parents (vl-atomguts-p vl-funname-p)
  :short "Faster version of @(see vl-funname-p), given that @(see
vl-atomguts-p) is already known."
  :long "<p>We leave this function enabled and reason about @('vl-funname-p')
instead.</p>"
  (mbe :logic (vl-funname-p x)
       :exec (eq (tag x) :vl-funname)))

(define vl-fast-sysfunname-p ((x vl-atomguts-p))
  :inline t
  :enabled t
  :parents (vl-atomguts-p vl-sysfunname-p)
  :short "Faster version of @(see vl-sysfunname-p), given that @(see
vl-atomguts-p) is already known."
  :long "<p>We leave this function enabled and reason about
@('vl-sysfunname-p') instead.</p>"
  (mbe :logic (vl-sysfunname-p x)
       :exec (eq (tag x) :vl-sysfunname)))


(defaggregate vl-atom
  :parents (vl-expr-p)
  :short "Representation of atomic expressions."
  :long "<p>See the discussion in @(see vl-expr-p).</p>"
  :tag :vl-atom
  :legiblep nil

  ((guts       vl-atomguts-p)

   (finalwidth vl-maybe-natp
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
  :guard t
  :elementp-of-nil nil
  :parents (vl-expr-p))


(defaggregate vl-nonatom
  :parents (vl-expr-p)
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

   (finalwidth vl-maybe-natp
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



(defsection vl-expr-p
  :parents (modules)
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

<li>@('finalwidth'), which is a @(see vl-maybe-natp), and</li>

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
vl-maybe-natp) and @(see vl-maybe-exprtype-p) objects, respectively.</p>

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
each operator has the proper arity.</p>"

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
                  (force (vl-maybe-natp finalwidth))
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
  :inline t
  :enabled t
  :parents (vl-atom-p vl-expr-p)
  :short "Faster version of @(see vl-atom-p), given that @(see vl-expr-p) is
already known."
  :long "<p>We leave this function enabled and reason about @('vl-atom-p')
instead.</p>"
  (mbe :logic (vl-atom-p x)
       :exec (eq (tag x) :vl-atom)))

(define vl-expr->finalwidth ((x vl-expr-p))
  :inline t
  :parents (vl-expr-p)
  :short "Get the @('finalwidth') from an expression."
  :long "<p>See @(see vl-expr-p) for a discussion of widths.  The result is a
@(see vl-maybe-natp).</p>"
  (if (eq (tag x) :vl-atom)
      (vl-atom->finalwidth x)
    (vl-nonatom->finalwidth x))

  :prepwork ((local (in-theory (enable vl-expr-p))))

  ///

  (defthm vl-maybe-natp-of-vl-expr->finalwidth
    (implies (force (vl-expr-p x))
             (vl-maybe-natp (vl-expr->finalwidth x)))
    :rule-classes :type-prescription)

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
  :inline t
  :parents (vl-expr-p)
  :short "Get the @('finaltype') from an expression."
  :long "<p>See @(see vl-expr-p) for a discussion of types.  The result
is a @(see vl-maybe-exprtype-p).</p>"
  (if (eq (tag x) :vl-atom)
      (vl-atom->finaltype x)
    (vl-nonatom->finaltype x))

  :prepwork ((local (in-theory (enable vl-expr-p))))
  ///
  (defthm vl-maybe-exprtype-p-of-vl-expr->finaltype
    (implies (force (vl-expr-p x))
             (vl-maybe-exprtype-p (vl-expr->finaltype x)))
    :rule-classes ((:rewrite)
                   (:type-prescription
                    :corollary (implies (force (vl-expr-p x))
                                        (and (symbolp (vl-expr->finaltype x))
                                             (not (equal (vl-expr->finaltype x) t)))))))

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
  :parents (vl-expr-p)
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

<dd>@('VL_GATE_REDUX'), with no value, is added when, e.g., @('pullup') and
@('pulldown') gates are converted into @('buf') gates, during @(see gateredux).
It is also given to certain module instances as described below.</dd>

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
  :parents (modules)

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
  :guard t
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
  :inline t
  :parents (modules vl-expr-p)
  :short "Representation for a @(see vl-expr-p) or @('nil')."
  :long "<p>This is a basic option type for expressions.</p>"
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


(defun vl-expr-induct (flag x)

; BOZO should we really have this, or would make-flag be better?  I guess this
; is in some ways cleaner.

  (declare (xargs :measure (two-nats-measure (acl2-count x)
                                             (if (eq flag 'expr) 1 0))))
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

; These rules have evolved a lot over time.  The current iteration seems to be
; fairly good and fixes some problems with previous versions.
;
; One previous approach was just to separately recognize each unary, binary,
; and ternary operator, e.g.,
;
;    (implies (and (or (equal (vl-nonatom->op x) :vl-unary-plus)
;                      (equal (vl-nonatom->op x) :vl-unary-minus)
;                      ...)
;                 ...)
;             (and (vl-nonatom->args x)
;                  ...))
;
; These rules seemed to be pretty effective, but they were slow.  To fix the
; slowness, I tried using a free variable to only apply the rule when the op was
; exactly known, e.g.,
;
;   (implies (and (equal (vl-nonatom->op x) op)
;                 (<= (vl-op-arity op) 1)
;                 ...)
;            (and (vl-nonatom->args x)
;                 ...))
;
; This did seem to be quite a bit faster and also seemed to wrok well when the
; operands were known precisely.  But it did not handle cases like VL-HIDEXPR-P
; very well, where if we know (not (equal (vl-nonatom->op x) :vl-hid-dot)) then
; we should be able to infer that this is a :vl-hid-arraydot.  I had trouble
; getting ACL2 to always canonicalize such things the "positive" form.
;
; The new rules don't have a free-variable, but still avoid the big case split.
; We don't ask about particular operands, but instead just ask whether the
; arity is known.  This works and should be pretty efficient when a direct
; equality is known, e.g., if we know (equal (vl-nonatom->op x)
; :vl-binary-times), then we'll backchain to (vl-op-arity (vl-nonatom->op x)),
; which type-set should settle to (vl-op-arity :vl-binary-times) and which we
; should then get by evaluation.
;
; But since there isn't a free-variable, we'll also get a chance to apply any
; rules that tell us what the arity is in some other way, which allows us to
; fairly easily solve the HIDEXPR problem.

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


(defaggregate vl-range
  :parents (modules)
  :short "Representation of ranges on wire declarations, instance array
declarations, and so forth."
  :tag :vl-range
  :legiblep nil

  ((msb vl-expr-p)
   (lsb vl-expr-p))

  :long "<p>Ranges are discussed in Section 7.1.5.</p>

<p>Ranges in declarations and array instances look like @('[msb:lsb]'), but do
not confuse them with part-select expressions which have the same syntax.</p>

<p>The expressions in the @('msb') and @('lsb') positions are expected to
resolve to constants.  Note that the parser does not try to simplify these
expressions, but some simplification is performed in transformations such as
@(see rangeresolve) and @(see unparameterization).</p>

<p>Even after the expressions have become constants, the Verilog specification
does not require @('msb') to be greater than @('lsb'), and neither index is
required to be zero.  In fact, even negative indicies seem to be permitted,
which is quite amazing and strange.</p>

<p>While we do not impose any restrictions in @('vl-range-p') itself, some
transformations expect the indices to be resolved to integers.  However, we now
try to support the use of both ascending and descending ranges.</p>")



(define vl-maybe-range-p (x)
  :inline t
  :parents (modules vl-range-p)
  :short "Representation for a @(see vl-range-p) or @('nil')."
  :long "<p>This is a basic option type for ranges.</p>"
  (or (not x)
      (vl-range-p x))
  ///
  (defthm vl-maybe-range-p-when-vl-range-p
    (implies (vl-range-p x)
             (vl-maybe-range-p x)))

  (defthm vl-range-p-when-vl-maybe-range-p
    (implies (vl-maybe-range-p x)
             (equal (vl-range-p x)
                    (if x t nil))))

  (defthm type-when-vl-maybe-range-p
    (implies (vl-maybe-range-p x)
             (or (consp x)
                 (not x)))
    :rule-classes :compound-recognizer))

(deflist vl-maybe-range-list-p (x)
  (vl-maybe-range-p x)
  :elementp-of-nil t
  :parents (modules))

(deflist vl-rangelist-p (x)
  (vl-range-p x)
  :elementp-of-nil nil
  :parents (modules))

(deflist vl-rangelist-list-p (x)
  (vl-rangelist-p x)
  :elementp-of-nil t
  :parents (modules))


(defaggregate vl-port
  :parents (modules)
  :short "Representation of a single Verilog port."
  :tag :vl-port
  :legiblep nil

  ((name vl-maybe-string-p
         :rule-classes
         ((:type-prescription)
          (:rewrite :corollary
                    ;; BOZO horrible gross stupid hack because type rule isn't forcing
                    (implies (force (vl-port-p x))
                             (equal (stringp (vl-port->name x))
                                    (if (vl-port->name x)
                                        t
                                      nil)))))
         "The \"externally visible\" name of this port, for use in named module
          instances.  Usually it is best to avoid this; see below.")

   (expr vl-maybe-expr-p
         "How the port is wired internally within the module.  Most of the time,
          this is a simple identifier expression that is just @('name').  But
          it can also be more complex; see below.")

   (loc  vl-location-p
         "Where this port came from in the Verilog source code."))

  :long "<p>Ports are described in Section 12.3 of the standard.  In simple
cases, a module's ports look like this:</p>

@({
module mod(a,b,c) ;  <-- ports are a, b, and c
  ...
endmodule
})

<p>A more modern, less repetitive syntax can be used instead:</p>

@({
module mod(
  input [3:0] a;   <-- ports are a, b, and c
  input b;
  output c;
) ;
   ...
endmodule
})

<p>More complex ports are also possible, e.g., here are some ports whose
external names are distinct from their internal wiring:</p>

@({
module mod (a, .b(w), c[3:0], .d(c[7:4])) ;
  input a;
  input w;
  input [7:0] c;
  ...
endmodule
})

<p>In this example, the @('name')s of these ports would be, respectively:
@('\"a\"'), @('\"b\"'), @('nil') (because this port has no externally visible
name), and @('\"d\"').  Meanwhile, the first two ports are internally wired to
@('a') and @('w'), respectively, while the third and fourth ports collectively
specify the bits of @('c').</p>

<h3>Using Ports</h3>

<p>It is generally best to <b>avoid using port names</b> except perhaps for
things like error messages.  Why?  As shown above, some ports might not have
names, and even when a port does have a name, it does not necessarily
correspond to any wires in the module.  But these cases are exotic, so code
based on port names is likely to work for simple test cases and then fail later
when more complex examples are encountered!</p>

<p>Usually you should not need to deal with port names.  The @(see argresolve)
transform converts module instances that use named arguments into their plain
equivalents, and once this has been done there really isn't much reason to have
port names anymore.  Instead, you can work directly with the port's
expression.</p>

<p>Our @('vl-port-p') structures do not restrict the kinds of expressions that
may be used as the internal wiring, but we generally expect that each such
expression should satisfy @(see vl-portexpr-p).</p>

<p>A \"blank\" port expression (represented by @('nil')) means the port is not
connected to any wires within the module.  Our @(see argresolve) transform will
issue non-fatal @(see warnings) if any non-blank arguments are connected to
blank ports, or if blank arguments are connected to non-blank ports.  It is
usually not hard to support blank ports in other transformations.</p>

<p>The direction of a port can most safely be obtained by @(see
vl-port-direction).  Note that directions are not particularly reliable in
Verilog: one can assign to a input or read from an output, and in simulators
like Cadence this can actually impact values on wires in the supermodule as if
the ports have no buffers.  We call this \"backflow.\" <b>BOZO</b> eventually
implement a comprehensive approach to detecting and dealing with backflow.</p>

<p>The width of a port can be determined after expression sizing has been
performed by examining the width of the port expression.  See @(see
expression-sizing) for details.</p>")

(deflist vl-portlist-p (x)
  (vl-port-p x)
  :elementp-of-nil nil
  :parents (modules))

(defprojection vl-portlist->exprs (x)
  (vl-port->expr x)
  :guard (vl-portlist-p x)
  :nil-preservingp t
  :parents (vl-portlist-p)
  :rest
  ((defthm vl-exprlist-p-of-vl-portlist->exprs
     (implies (force (vl-portlist-p x))
              (equal (vl-exprlist-p (vl-portlist->exprs x))
                     (not (member nil (vl-portlist->exprs x))))))

   (defthm vl-exprlist-p-of-remove-equal-of-vl-portlist->exprs
     (implies (force (vl-portlist-p x))
              (vl-exprlist-p (remove-equal nil (vl-portlist->exprs x)))))))

(defprojection vl-portlist->names (x)
  (vl-port->name x)
  :guard (vl-portlist-p x)
  :nil-preservingp t
  :parents (vl-portlist-p))


(defenum vl-direction-p (:vl-input :vl-output :vl-inout)
  :parents (modules)
  :short "Direction for a port declaration (input, output, or inout)."

  :long "<p>Each port declaration (see @(see vl-portdecl-p)) includes a
direction to indicate that the port is either an input, output, or inout.  We
represent these directions with the keyword @(':vl-input'), @(':vl-output'),
and @(':vl-inout'), respectively.</p>

<p>In our @(see argresolve) transformation, directions are also assigned to all
arguments of gate instances and most arguments of module instances.  See our
@(see vl-plainarg-p) structures for more information.</p>")


(define vl-maybe-direction-p (x)
  :inline t
  :parents (modules)
  :short "Representation for a @(see vl-direction-p) or @('nil')."
  :long "<p>This is a basic option type for directions.</p>"
  (or (not x)
      (vl-direction-p x))
  ///
  (defthm vl-maybe-direction-p-when-vl-direction-p
    (implies (vl-direction-p x)
             (vl-maybe-direction-p x)))

  (defthm vl-direction-p-when-vl-maybe-direction-p
    (implies (vl-maybe-direction-p x)
             (equal (vl-direction-p x)
                    (if x t nil))))

  (defthm type-when-vl-maybe-direction-p
    (implies (vl-direction-p x)
             (and (symbolp x)
                  (not (equal x t))))
    :rule-classes :compound-recognizer))


(defaggregate vl-portdecl
  :parents (modules)
  :short "Representation of Verilog port declarations."
  :tag :vl-portdecl
  :legiblep nil

  ((name     stringp
             :rule-classes :type-prescription
             "An ordinary string that should agree with some identifier used in
              the \"internal\" wiring expressions from some port(s) in the
              module.")

   (dir      vl-direction-p
             "Says whether this port is an input, output, or bidirectional
              (inout) port.")

   (signedp  booleanp
             :rule-classes :type-prescription
             "Whether the @('signed') keyword was present in the declaration;
              but <b>warning</b>: per page 175, port declarations and net/reg
              declarations must be checked against one another: if either
              declaration includes the @('signed') keyword, then both are to be
              considered signed.  The @(see loader) DOES NOT do this
              cross-referencing automatically; instead the @(see portdecl-sign)
              transformation needs to be run.")

   (range    vl-maybe-range-p
             "Indicates whether the input is a vector and, if so, how large the
              input is.  Per page 174, if there is also a net declaration, then
              the range must agree.  This is checked in @(see
              vl-overlap-compatible-p) as part of our notion of @(see
              reasonable) modules.")

   (atts     vl-atts-p
             "Any attributes associated with this declaration.")

   (loc      vl-location-p
             "Where the port was declared in the source code."))

  :long "<p>Port declarations, described in Section 12.3.3 of the
specification, ascribe certain properties (direction, signedness, size, and so
on) to the ports of a module.  Here is an example:</p>

@({
module m(a, b) ;
  input [3:0] a ;  // <--- port declaration
  ...
endmodule
})

<p>Although Verilog allows multiple ports to be declared simultaneously, i.e.,
@('input a, b ;'), our parser splits these merged declarations to create
separate @('vl-portdecl-p') objects for each port.  Because of this, every
@('vl-portdecl-p') has only a single name.</p>

<h4>A Note about Port Types</h4>

<p>If you look at the grammar for port declarations, you will see that you
can also do things like:</p>

@({
input wire a;
input supply0 b;
})

<p>And so on.  For some time, our @('vl-port-p') structures included a
@('type') field.  However, upon a closer reading of the specification, we have
learned that the proper way to handle these is to simultaneously introduce a
@(see vl-netdecl-p) alongside the @('vl-portdecl-p') that we would ordinarily
create for a port declaration.  See, e.g., the second paragraph from the bottom
on Page 174.</p>")

(deflist vl-portdecllist-p (x)
  (vl-portdecl-p x)
  :elementp-of-nil nil
  :parents (modules))



(defaggregate vl-gatedelay
  :parents (modules)
  :short "Representation of delay expressions."
  :tag :vl-gatedelay
  :legiblep nil

  ((rise vl-expr-p
         "Rising delay.")

   (fall vl-expr-p
         "Falling delay.")

   (high vl-maybe-expr-p
         "High-impedence delay or charge decay time." ))

  :long "<p><b>WARNING</b>.  We have not paid much attention to delays, and our
transformations probably do not handle them properly.</p>

<p>Delays are mainly discussed in 7.14 and 5.3, with some other discussion in
6.13 and the earlier parts of Section 7.  In short:</p>

<ul>
<li>A \"delay expression\" can be an arbitrary expression.  Of particular note,
    mintypmax expression such as 1:2:3 mean \"the delay is at least 1, usually
    2, and at most 3.\"</li>

<li>Up to three delay expressions are associated with each gate.  These are,
    in order,
      <ol>
        <li>a \"rise delay\",</li>
        <li>a \"fall delay\", and</li>
        <li>for regular gates, a \"high impedence\" delay; <br/>
            for triregs, a \"charge decay time\" delay</li>
      </ol></li>
</ul>

<p>The parser does not attempt to determine (3) in some cases, so it may be
left as @('nil').  Simulators that care about this will need to carefully
review the rules for correctly computing these delays.</p>")


(define vl-maybe-gatedelay-p (x)
  :inline t
  :parents (modules)
  :short "Representation for a @(see vl-gatedelay-p) or @('nil')."
  :long "<p>This is a basic option type for gatedelays.</p>"
  (or (not x)
      (vl-gatedelay-p x))
  ///
  (defthm vl-maybe-gatedelay-p-when-vl-gatedelay-p
    (implies (vl-gatedelay-p x)
             (vl-maybe-gatedelay-p x)))

  (defthm vl-gatedelay-p-when-vl-maybe-gatedelay-p
    (implies (vl-maybe-gatedelay-p x)
             (equal (vl-gatedelay-p x)
                    (if x t nil))))

  (defthm type-when-vl-maybe-gatedelay-p
    (implies (vl-maybe-gatedelay-p x)
             (or (not x)
                 (consp x)))
    :rule-classes :compound-recognizer))


(defenum vl-dstrength-p
  (:vl-supply
   :vl-strong
   :vl-pull
   :vl-weak
   :vl-highz)
  :parents (vl-gatestrength-p)
  :short "Representation of a drive strength for @(see vl-gatestrength-p)
objects."
  :long "<p>We represent Verilog's drive strengths with the keyword symbols
recognized by @(call vl-dstrength-p).</p>

<p>BOZO add references to the Verilog standard, description of what these
are.</p>")


(defaggregate vl-gatestrength
  :parents (modules)
  :short "Representation of strengths for a assignment statements, gate
instances, and module instances."
  :tag :vl-gatestrength
  :legiblep nil

  ((zero vl-dstrength-p "Drive strength toward logical zero.")
   (one  vl-dstrength-p "Drive strength toward logical one."))

  :long "<p><b>WARNING</b>.  We have not paid much attention to strengths, and
our transformations probably do not handle them properly.</p>

<p>See sections 7.1.2 and 7.9 for discussion of strength modelling.  Every
regular gate has, associated with it, two drive strengths; a \"strength0\"
which says how strong its output is when it is a logical zero, and
\"strength1\" which says how strong the output is when it is a logical one.
Strengths also seem to be used on assignments and module instances.</p>

<p>There seem to be some various rules for default strengths in 7.1.2, and also
in 7.13.  But our parser does not try to implement these defaults, and we only
associate strengths onto module items where they are explicitly
specified.</p>")


(defsection vl-maybe-gatestrength-p
  :parents (modules)
  :short "Representation for a @(see vl-gatestrength-p) or @('nil')."
  :long "<p>This is a basic option type for gatestrengths.</p>"

  (defund vl-maybe-gatestrength-p (x)
    (declare (xargs :guard t))
    (or (not x)
        (vl-gatestrength-p x)))

  (local (in-theory (enable vl-maybe-gatestrength-p)))

  (defthm vl-maybe-gatestrength-p-when-vl-gatestrength-p
    (implies (vl-gatestrength-p x)
             (vl-maybe-gatestrength-p x)))

  (defthm vl-gatestrength-p-when-vl-maybe-gatestrength-p
    (implies (vl-maybe-gatestrength-p x)
             (equal (vl-gatestrength-p x)
                    (if x t nil))))

  (defthm type-when-vl-maybe-gatestrength-p
    (implies (vl-maybe-gatestrength-p x)
             (or (not x)
                 (consp x)))
    :rule-classes :compound-recognizer))


(defenum vl-cstrength-p (:vl-large :vl-medium :vl-small)
  :parents (modules)
  :short "Representation of charge strengths."

  :long "<p>We represent Verilog's charge strengths with the keyword symbols
recognized by @(call vl-cstrength-p).</p>

<p>BOZO add references to the Verilog standard, description of what these
are.</p>")


(define vl-maybe-cstrength-p (x)
  :inline t
  :parents (modules)
  :short "Representation for a @(see vl-cstrength-p) or @('nil')."
  :long "<p>This is a basic option type for cstrengths.</p>"
  (or (not x)
      (vl-cstrength-p x))
  ///
  (defthm vl-maybe-cstrength-p-when-vl-cstrength-p
    (implies (vl-cstrength-p x)
             (vl-maybe-cstrength-p x)))

  (defthm vl-cstrength-p-when-vl-maybe-cstrength-p
    (implies (vl-maybe-cstrength-p x)
             (equal (vl-cstrength-p x)
                    (if x t nil))))

  (defthm type-when-vl-maybe-cstrength-p
    (implies (vl-maybe-cstrength-p x)
             (and (symbolp x)
                  (not (equal x t))))
    :rule-classes :compound-recognizer))


(defaggregate vl-assign
  :parents (modules)
  :short "Representation of a continuous assignment statement."
  :tag :vl-assign
  :legiblep nil

  ((lvalue   vl-expr-p "The location being assigned to.")
   (expr     vl-expr-p "The right-hand side.")
   (strength vl-maybe-gatestrength-p)
   (delay    vl-maybe-gatedelay-p)
   (atts     vl-atts-p
             "Any attributes associated with this assignment.")
   (loc      vl-location-p
             "Where the assignment was found in the source code."))

  :long "<p>In the Verilog sources, continuous assignment statements can take
two forms, as illustrated below.</p>

@({
module m (a, b, c) ;
  wire w1 = a & b ;     // <-- continuous assignment in a declaration
  wire w2;
  assign w2 = w1;       // <-- continuous assignment
endmodule
})

<p>Regardless of which form is used, the @(see parser) generates a
@('vl-assign-p') object.  Note that the following is also legal Verilog:</p>

@({
  assign foo = 1, bar = 2;
})

<p>But in such cases, the parser will create two @('vl-assign-p') objects, one
to represent the assignment to @('foo'), and the other to represent the
assignment to @('bar').  Hence, each @('vl-assign-p') represents only a single
assignment.</p>


<h4>Lvalue</h4>

<p>The @('lvalue') field must be an expression, and represents the location
being assigned to.  The formal syntax definition for Verilog only permits
lvalues to be:</p>

<ul>
 <li>identifiers,</li>
 <li>bit- or part-selects, and</li>
 <li>concatenations of the above.</li>
</ul>

<p>Furthermore, from Table 6.1, (p. 68), we find that only @('net')
declarations are permitted in continuous assignments; @('reg')s, @('integer')s,
and other variables must be assigned only using procedural assignments.  We
have experimentally verified (see @('test-assign.v')) that Cadence enforces
these rules.</p>

<p>Our parser does impose these syntactic restrictions, but in @('vl-assign-p')
we are perhaps overly permissive, and we only require that the @('lvalue') is
an expression.  Even so, some transforms may cause fatal warnings if these
semantic restrictions are violated, so one must be careful when generating
assignments.</p>

<h4>Expr</h4>

<p>The @('expr') is the expression being assigned to this lvalue.  We do not in
any way restrict the expression, nor have we found any restrictions discussed
in the Verilog standard.  Even so, it seems there must be some limits.  For
instance, what does it mean to assign, say, a minimum/typical/maximum delay
expression?  For these sorts of reasons, some transforms may wish to only
permit a subset of all expressions here.</p>


<h4>Delay</h4>

<p>The @('delay') for a continuous assignment is discussed in 6.1.3 (page 71),
and specifies how long it takes for a change in the value of the right-hand
side to be propagated into the lvalue.  We represent the delay using a @(see
vl-maybe-gatedelay-p); if the @('delay') is @('nil'), it means that no delay
was specified.</p>

<p>Note (6.1.3) that when delays are provided in the combined declaration and
assignment statement, e.g., </p>

@({
  wire #10 a = 1, b = 2;
})

<p>that the delay is to be associated with each assignment, and NOT with the
net declaration for @('a').  Net delays are different than assignment delays;
see @(see vl-netdecl-p) for additional discussion.</p>

<p><b>Warning:</b> Although the parser is careful to handle the delay
correctly, we are generally uninterested in delays and our transforms may not
properly preserve them.</p>

<p><b>BOZO</b> Presumably the default delay is zero?  Haven't seen that yet,
though.</p>

<h4>Strength</h4>

<p>Strengths on continuous assignments are discussed in 6.1.4.  We represent
the strength using a @(see vl-maybe-gatestrength-p).  If a strength is not
provided, the parser sets this to @('nil').</p>

<p><b>Warning:</b> Although the parser is careful to handle the strength
correctly, we are generally uninterested in strengths and our transforms may not
properly preserve them.</p>")

(deflist vl-assignlist-p (x)
  (vl-assign-p x)
  :elementp-of-nil nil
  :parents (modules))

(defprojection vl-assignlist->lvalues (x)
  (vl-assign->lvalue x)
  :guard (vl-assignlist-p x)
  :result-type vl-exprlist-p
  :nil-preservingp t
  :parents (vl-assignlist-p))

; BOZO I'm not going to introduce this yet.  I think we shoudl rename the expr
; field to rhs first, to prevent confusion between this and allexprs.

;; (defprojection vl-assignlist->exprs (x)
;;   (vl-assign->expr x)
;;   :guard (vl-assignlist-p x)
;;   :nil-preservingp t)


(defenum vl-netdecltype-p
  (:vl-wire ;; Most common so it goes first.
   :vl-supply0
   :vl-supply1
   :vl-tri
   :vl-triand
   :vl-trior
   :vl-tri0
   :vl-tri1
   :vl-trireg
   :vl-uwire
   :vl-wand
   :vl-wor)
  :parents (modules)
  :short "Representation of wire types."

  :long "<p>Wires in Verilog can be given certain types.  We
represent these types using certain keyword symbols, whose names
correspond to the possible types.</p>")



(define vl-maybe-netdecltype-p (x)
  :inline t
  :parents (modules)
  :short "Representation for a @(see vl-netdecltype-p) or @('nil')."
  :long "<p>This is a basic option type for netdecltypes.</p>"
  (or (not x)
      (vl-netdecltype-p x))
  ///
  (defthm vl-maybe-netdecltype-p-when-vl-netdecltype-p
    (implies (vl-netdecltype-p x)
             (vl-maybe-netdecltype-p x)))

  (defthm vl-netdecltype-p-when-vl-maybe-netdecltype-p
    (implies (vl-maybe-netdecltype-p x)
             (equal (vl-netdecltype-p x)
                    (if x t nil))))

  (defthm type-when-vl-maybe-netdecltype-p
    (implies (vl-netdecltype-p x)
             (and (symbolp x)
                  (not (equal x t))))
    :rule-classes :compound-recognizer))


(defaggregate vl-netdecl
  :parents (modules)
  :short "Representation of net (wire) declarations."
  :tag :vl-netdecl
  :legiblep nil
  ((name       stringp
               :rule-classes :type-prescription
               "Name of the wire being declared.")

   (type       vl-netdecltype-p
               "Wire type, e.g., @('wire'), @('supply1'), etc.")

   (range      vl-maybe-range-p
               "A single, optional range that preceeds the wire name; this
                ordinarily governs the \"size\" of a wire.")

   (arrdims    vl-rangelist-p
               "Used for arrays like memories; see below.")

   (vectoredp  booleanp
               :rule-classes :type-prescription
               "True if the @('vectored') keyword was explicitly provided.")

   (scalaredp  booleanp
               :rule-classes :type-prescription
               "True if the @('scalared') keyword was explicitly provided.")

   (signedp    booleanp
               :rule-classes :type-prescription
               "Indicates whether the @('signed') keyword was supplied on this
                declaration.  But <b>warning</b>: per page 175, port
                declarations and net/reg declarations must be checked against
                one another: if either declaration includes the @('signed')
                keyword, then both are to be considered signed.  The parser
                DOES NOT do this cross-referencing automatically; instead the
                @(see portdecl-sign) transformation needs to be run.")

   (delay      vl-maybe-gatedelay-p)
   (cstrength  vl-maybe-cstrength-p)
   (atts       vl-atts-p
               "Any attributes associated with this declaration.")
   (loc        vl-location-p
               "Where the declaration was found in the source code."))

  :long "<p>Net declarations introduce new wires with certain properties (type,
signedness, size, and so on).  Here are some examples of basic net
declarations.</p>

@({
module m (a, b, c) ;
  wire [4:0] w ;       // <-- plain net declaration
  wire ab = a & b ;    // <-- net declaration with assignment
  ...
endmodule
})

<p>Net declarations can also arise from using the combined form of port
declarations.</p>

@({
module m (a, b, c) ;
  input wire a;    // <-- net declaration in a port declaration
  ...
endmodule
})

<p>You can also string together net declarations, e.g., by writing @('wire w1,
w2;').</p>

<p>In all of these cases, our parser generates a @('vl-netdecl-p') object for
each declared wire.  That is, each @('vl-netdecl-p') is a declaration of a
single wire.</p>

<p>Note that when an assignment is also present, the parser creates a
corresponding, separate @(see vl-assign-p) object to contain the assignment.
Similarly, when using the combined net/port declaration format, a separate
@(see vl-portdecl-p) object is generated.  Hence, each @('vl-netdecl-p') really
and truly only represents a declaration.</p>


<h4>Arrays</h4>

<p>The @('arrdims') fields is for arrays.  Normally, you do not encounter
these.  For instance, a wide wire declaration like this is <b>not</b> an
array:</p>

@({
  wire [4:0] w;
})

<p>Instead, the @('[4:0]') part here is the @('range') of the wire and its
@('arrdims') are just @('nil').</p>

<p>In contrast, the @('arrdims') are a list of ranges, also optional, which
follow the wire name.  For instance, the arrdims of @('v') below is a singleton
list with the range @('[4:0]').</p>

@({
  wire v [4:0];
})

<p>Be aware that range and arrdims really are <b>different</b> things; @('w')
and @('v') are <i>not</i> equivalent except for their names.  In particular,
@('w') is a single, 5-bit wire, while @('v') is an array of five one-bit
wires.</p>

<p>Things are more complicated when a declaration includes both a range and
arrdims.  For instance</p>

@({
wire [4:0] a [10:0];
})

<p>declares @('a') to be an 11-element array of five-bit wires.  The @('range')
for @('a') is @('[4:0]'), and the arrdims are a list with one entry, namely the
range @('[10:0]').</p>

<p>At present, the translator has almost no support for arrdims.  However, the
parser should handle them just fine.</p>


<h4>Vectorness and Signedness</h4>

<p>These are only set to @('t') when the keywords @('vectored') or
@('scalared') are explicitly provided; i.e., they may both be @('nil').</p>

<p>I do not know what these keywords are supposed to mean; the Verilog
specification says almost nothing about it, and does not even say what the
default is.</p>

<p>According to some random guy on the internet, it's supposed to be a syntax
error to try to bit- or part-select from a vectored net.  Maybe I can find a
more definitive explanation somewhere.  Hey, in 6.1.3 there are some
differences mentioned w.r.t. how delays go to scalared and vectored nets.
4.3.2 has a little bit more.</p>


<h4>Delay</h4>

<p>Net delays are described in 7.14, and indicate the time it takes for any
driver on the net to change its value.  The default delay is zero when no delay
is specified.  Even so, we represent the delay using a @(see
vl-maybe-gatedelay-p), and use @('NIL') when no delay is specified.</p>

<p>Note (from 6.1.3) that when delays are provided in the combined declaration
and assignment statement, e.g., </p>

@({
  wire #10 a = 1, b = 2;
})

<p>that the delay is to be associated with each assignment, and NOT with the
net declaration for @('a').  See @(see vl-assign-p) for more information.</p>

<p><b>BOZO</b> consider making it an explicit @(see vl-gatedelay-p) and setting
it to zero in the parser when it's not specified.</p>

<p><b>Warning:</b> we have not really paid attention to delays, and our
transformations probably do not preserve them correctly.</p>


<h4>Strengths</h4>

<p>If you look at the grammar for net declarations, you may notice drive
strengths.  But these are only used when the declaration includes assignments,
and in such cases the drive strength is a property of the assignments and is
not a property of the declaration.  Hence, there is no drive strength field
for net declarations.</p>

<p>The @('cstrength') field is only applicable to @('trireg')-type nets.  It
will be @('nil') for all other nets, and will also be @('nil') on @('trireg')
nets that do not explicitly give a charge strength.  Note that
@('vl-netdecl-p') does not enforce the requirement that only triregs have
charge strengths, but the parser does.</p>

<p><b>Warning:</b> we have not really paid attention to charge strengths, and
our transformations may not preserve it correctly.</p>")

(deflist vl-netdecllist-p (x)
  (vl-netdecl-p x)
  :elementp-of-nil nil
  :parents (modules))


(defaggregate vl-plainarg
  :parents (modules vl-arguments-p)
  :short "Representation of a single argument in a plain argument list."
  :tag :vl-plainarg
  :legiblep nil

  ((expr     vl-maybe-expr-p
             "Expression being connected to the port.  In programming languages
              parlance, this is the <i>actual</i>.  Note that this may be
              @('nil') because Verilog allows expressions to be \"blank\", in
              which case they represent an unconnected wire.")

   (portname vl-maybe-string-p
             :rule-classes
             ((:type-prescription)
              (:rewrite
               :corollary (implies (force (vl-plainarg-p x))
                                   (equal (stringp (vl-plainarg->portname x))
                                          (if (vl-plainarg->portname x)
                                              t
                                            nil)))))
             "Not part of the Verilog syntax.  This <b>may</b> indicate the
              name of the port (i.e., the <i>formal</i>) that this expression
              is connected to; see below.")

   (dir      vl-maybe-direction-p
             "Not part of the Verilog syntax.  This <b>may</b> indicate the
              direction of this port; see below.")

   (atts     vl-atts-p
             "Any attributes associated with this argument."))

  :long "<p>There are two kinds of argument lists for module instantiations,
which we call <i>plain</i> and <i>named</i> arguments.</p>

@({
  modname instname ( 1, 2, 3 );             <-- \"plain\" arguments
  modname instname ( .a(1), .b(2), .c(3) ); <-- \"named\" arguments
})

<p>A @('vl-plainarg-p') represents a single argument in a plain argument
list.</p>

<p>The @('dir') is initially @('nil') but may get filled in by the @(see
argresolve) transformation to indicate whether this port for this argument is
an input, output, or inout for the module or gate being instantiated.  After
@(see argresolve), all well-formed <b>gate</b> instances will have their
direction information computed and so you may rely upon the @('dir') field for
gate instances.  <b>HOWEVER</b>, for <b>module</b> instances the direction of a
port may not be apparent; see @(see vl-port-direction) for details.  So even
after @(see argresolve) some arguments to module instances may not have a
@('dir') annotation, and you should generally not rely on the @('dir') field
for module instances.</p>

<p>The @('portname') is similar.  The @(see argresolve) transformation may
sometimes be able to fill in the name of the port, but this is meant only as a
convenience for error message generation.  This field should <b>never</b> be
used for anything that is semantically important.  No argument to a gate
instance will ever have a portname.  Also, since not every @(see vl-port-p) has
a name, some arguments to module instances may also not be given
portnames.</p>")

(deflist vl-plainarglist-p (x)
  (vl-plainarg-p x)
  :elementp-of-nil nil
  :parents (modules))

(deflist vl-plainarglistlist-p (x)
  (vl-plainarglist-p x)
  :elementp-of-nil t
  :parents (modules)
  :rest
  ((defthm vl-plainarglist-p-of-strip-cars
     (implies (and (vl-plainarglistlist-p x)
                   (all-have-len x n)
                   (not (zp n)))
              (vl-plainarglist-p (strip-cars x))))

   (defthm vl-plainarglistlist-p-of-strip-cdrs
     (implies (vl-plainarglistlist-p x)
              (vl-plainarglistlist-p (strip-cdrs x))))))

(defprojection vl-plainarglist->exprs (x)
  (vl-plainarg->expr x)
  :guard (vl-plainarglist-p x)
  :nil-preservingp t
  :rest
  ((defthm vl-exprlist-p-of-vl-plainarglist->exprs
     (implies (force (vl-plainarglist-p x))
              (equal (vl-exprlist-p (vl-plainarglist->exprs x))
                     (not (member nil (vl-plainarglist->exprs x))))))

   (defthm vl-exprlist-p-of-remove-nil-of-plainarglist->exprs
     (implies (vl-plainarglist-p x)
              (vl-exprlist-p (remove nil (vl-plainarglist->exprs x)))))))



(defaggregate vl-namedarg
  :parents (modules)
  :short "Representation of a single argument in a named argument list."
  :tag :vl-namedarg
  :legiblep nil

  ((name stringp
         :rule-classes :type-prescription
         "Name of the port being connected to, e.g., @('foo') in
          @('.foo(3)')")

   (expr vl-maybe-expr-p
         "The <i>actual</i> being connected to this port; may be
          @('nil') for blank ports.")

   (atts vl-atts-p
         "Any attributes associated with this argument."))

  :long "<p>See @(see vl-plainarg-p) for a general discussion of arguments.
Each @('vl-namedarg-p') represents a single argument in a named argument
list.</p>

<p>Unlike plain arguments, our named arguments do not have a direction field.
Our basic transformation strategy is to quickly eliminate named arguments and
rewrite everything as plain arguments; see the @(see argresolve) transform.
Because of this, we don't bother to annotate named arguments with their
directions.</p>")

(deflist vl-namedarglist-p (x)
  (vl-namedarg-p x)
  :elementp-of-nil nil
  :parents (modules))



(defsection vl-arguments-p
  :parents (modules)
  :short "Representation of arguments to a module instance (for ports and also
for parameters)."

  :long "<p>There are two kinds of argument lists for module instantiations,
which we call <i>plain</i> and <i>named</i> arguments.</p>

@({
  modname instname ( 1, 2, 3 );             <-- \"plain\" arguments
  modname instname ( .a(1), .b(2), .c(3) ); <-- \"named\" arguments
})

<p>Similarly, named or plain argument lists can be used in order to give
parameters to a module, e.g.,</p>

@({
  modname #(.width(6)) instname(o, a, b);
  modname #(6) instname(o, a, b);
})

<p>A @('vl-arguments-p') structure represents an argument list of either
variety.  Each @('vl-arguments-p') structure is an aggregate of two fields:</p>

<ul>

<li>@('namedp'), which says whether named or plain arguments are used, and
</li>

<li>@('args'), the actual list of named or plain arguments.</li>

</ul>"

  (defund vl-arguments-p (x)
    (declare (xargs :guard t))
    (and (tuplep 3 x)
         (eq (first x) :vl-arguments)
         (booleanp (second x))
         (if (second x)
             (vl-namedarglist-p (third x))
           (vl-plainarglist-p (third x)))))

  (definlined vl-arguments (namedp args)
    (declare (xargs :guard (and (booleanp namedp)
                                (if namedp
                                    (vl-namedarglist-p args)
                                  (vl-plainarglist-p args)))))
    (list :vl-arguments namedp args))

  (local (in-theory (enable vl-arguments-p vl-arguments)))

  (definlined vl-arguments->namedp (x)
    (declare (xargs :guard (vl-arguments-p x)))
    (second x))

  (definlined vl-arguments->args (x)
    (declare (xargs :guard (vl-arguments-p x)))
    (third x))

  (local (in-theory (enable vl-arguments->namedp vl-arguments->args)))

  (defmacro patbind-vl-arguments (args forms rest-expr)
    (std::da-patbind-fn 'vl-arguments '(namedp args) args forms rest-expr))

  (defthm booleanp-of-vl-arguments-p
    (booleanp (vl-arguments-p x))
    :rule-classes :type-prescription)

  (defthm tag-of-vl-arguments
    (equal (tag (vl-arguments namedp args))
           :vl-arguments)
    :hints(("Goal" :in-theory (enable tag))))

  (defthm tag-when-vl-arguments-p
    (implies (vl-arguments-p x)
             (equal (tag x) :vl-arguments))
    :rule-classes ((:rewrite :backchain-limit-lst 0)
                   (:forward-chaining))
    :hints(("Goal" :in-theory (enable tag))))

  (defthm consp-when-vl-arguments-p
    (implies (vl-arguments-p x)
             (consp x))
    :rule-classes :compound-recognizer)

  (defthm vl-arguments->namedp-of-vl-arguments
    (equal (vl-arguments->namedp (vl-arguments namedp args))
           namedp))

  (defthm vl-arguments->args-of-vl-arguments
    (equal (vl-arguments->args (vl-arguments namedp args))
           args))

  (defthm vl-arguments-p-of-vl-arguments
    (implies (and (force (booleanp namedp))
                  (force (if namedp
                             (vl-namedarglist-p args)
                           (vl-plainarglist-p args))))
             (vl-arguments-p (vl-arguments namedp args))))

  (defthm booleanp-of-vl-arguments->namedp
    (implies (force (vl-arguments-p x))
             (booleanp (vl-arguments->namedp x)))
    :rule-classes :type-prescription)

  (defthm vl-namedarglist-p-of-vl-arguments->args
    (implies (and (force (vl-arguments-p x))
                  (case-split (vl-arguments->namedp x)))
             (vl-namedarglist-p (vl-arguments->args x))))

  (defthm vl-plainarglist-p-of-vl-arguments->args
    (implies (and (force (vl-arguments-p x))
                  (case-split (not (vl-arguments->namedp x))))
             (vl-plainarglist-p (vl-arguments->args x)))))

(deflist vl-argumentlist-p (x)
  (vl-arguments-p x)
  :elementp-of-nil nil
  :parents (modules))



(defaggregate vl-modinst
  :parents (modules)
  :short "Representation of a single module (or user-defined primitive)
instance."
  :tag :vl-modinst
  :legiblep nil

  ((instname  vl-maybe-string-p
              :rule-classes
              ((:type-prescription)
               (:rewrite :corollary
                         (implies (force (vl-modinst-p x))
                                  (equal (stringp (vl-modinst->instname x))
                                         (if (vl-modinst->instname x)
                                             t
                                           nil)))))
              "Either the name of this instance or @('nil') if the instance has
               no name.  See also the @(see addinstnames) transform.")

   (modname   stringp
              :rule-classes :type-prescription
              "Name of the module or user-defined primitive that is being
               instantiated.")

   (range     vl-maybe-range-p
              "When present, indicates that this is an array of instances,
               instead of a single instance.")

   (paramargs vl-arguments-p
              "Values to use for module parameters, e.g., this might specify
               the width to use for an adder module, etc.")

   (portargs  vl-arguments-p
              "Connections to use for the submodule's input, output, and inout
               ports.")

   (str       vl-maybe-gatestrength-p
              "Strength for user-defined primitive instances.  Does not make
               sense for module instances.  VL mostly ignores this.")

   (delay     vl-maybe-gatedelay-p
              "Delay for user-defined primitive instances.  Does not make sense
               for module instances.  VL mostly ignores this.")

   (atts      vl-atts-p
              "Any attributes associated with this instance.")

   (loc       vl-location-p
              "Where the instance was found in the source code."))

  :long "<p>We represent module and user-defined primitive instances in a
uniform manner with @('vl-modinst-p') structures.  Because of this, certain
fields do not make sense in one context or another.  In particular, a UDP
instance should never have any parameter arguments, its port arguments should
always be an plain argument list, and it may not have a instname.  Meanwhile, a
module instance should never have a drive strength or a delay, and should
always have a instname.</p>

<p>As with variables, nets, etc., we split up combined instantiations such as
@('modname inst1 (...), inst2 (...)') into separate, individual structures, one
for @('inst1'), and one for @('inst2'), so that each @('vl-modinst-p')
represents exactly one instance (or instance array).</p>")

(deflist vl-modinstlist-p (x)
  (vl-modinst-p x)
  :elementp-of-nil nil
  :parents (modules))


(defenum vl-gatetype-p
  (:vl-cmos
   :vl-rcmos
   :vl-bufif0
   :vl-bufif1
   :vl-notif0
   :vl-notif1
   :vl-nmos
   :vl-pmos
   :vl-rnmos
   :vl-rpmos
   :vl-and
   :vl-nand
   :vl-or
   :vl-nor
   :vl-xor
   :vl-xnor
   :vl-buf
   :vl-not
   :vl-tranif0
   :vl-tranif1
   :vl-rtranif1
   :vl-rtranif0
   :vl-tran
   :vl-rtran
   :vl-pulldown
   :vl-pullup)
  :parents (modules)
  :short "Representation of gate types."
  :long "<p>We represent Verilog's gate types with the keyword symbols
recognized by @(call vl-gatetype-p).</p>")

(defaggregate vl-gateinst
  :parents (modules)
  :short "Representation of a single gate instantiation."
  :tag :vl-gateinst
  :legiblep nil
  ((type     vl-gatetype-p
             "What kind of gate this is, e.g., @('and'), @('xor'), @('rnmos'),
              etc."
             :rule-classes
             ((:rewrite)
              (:type-prescription
               :corollary
               ;; BOZO may not want to force this
               (implies (force (vl-gateinst-p x))
                        (and (symbolp (vl-gateinst->type x))
                             (not (equal (vl-gateinst->type x) t))
                             (not (equal (vl-gateinst->type x) nil)))))))

   (name     vl-maybe-string-p
             :rule-classes
             ((:type-prescription)
              (:rewrite :corollary
                        (implies (force (vl-gateinst-p x))
                                 (equal (stringp (vl-gateinst->name x))
                                        (if (vl-gateinst->name x)
                                            t
                                          nil)))))
             "The name of this gate instance, or @('nil') if it has no name;
              see also the @(see addinstnames) transform.")

   (range    vl-maybe-range-p
             "When present, indicates that this is an array of instances
              instead of a single instance.")

   (strength vl-maybe-gatestrength-p
             "The parser leaves this as @('nil') unless it is explicitly provided.
              Note from Section 7.8 that pullup and pulldown gates are special
              in that the strength0 from a pullup source and the strength1 on a
              pulldown source are supposed to be ignored.  <b>Warning:</b> in
              general we have not paid much attention to strengths, so we may
              not handle them correctly in our various transforms.")

   (delay    vl-maybe-gatedelay-p
             "The parser leaves this as @('nil') unless it is explicitly provided.
              Certain gates (tran, rtran, pullup, and pulldown) never have
              delays according to the Verilog grammar, but this is only
              enforced by the parser, and is not part of our @('vl-gateinst-p')
              definition.  <b>Warning:</b> as with strengths, we have not paid
              much attention to delays, and our transforms may not handle them
              correctly.")

   (args     vl-plainarglist-p
             "Arguments to the gate instance.  Note that this differs from
              module instances where @(see vl-arguments-p) structures are used,
              because gate arguments are never named.  The grammar restricts
              how many arguments certain gates can have, but we do not enforce
              these restrictions in the definition of @('vl-gateinst-p').")

   (atts     vl-atts-p
             "Any attributes associated with this gate instance.")

   (loc      vl-location-p
             "Where the gate instance was found in the source code."))

  :long "<p>@('vl-gateinst-p') is our representation for any single gate
instance (or instance array).</p>

<p>The grammar for gate instantiations is quite elaborate, but the various
cases are so regular that a unified representation is possible.  Note that the
Verilog grammar restricts the list of expressions in certain cases, e.g., for
an @('and') gate, the first expression must be an lvalue.  Although our parser
enforces these restrictions, we do not encode them into the definition of
@('vl-gateinst-p').</p>")

(deflist vl-gateinstlist-p (x)
  (vl-gateinst-p x)
  :elementp-of-nil nil
  :parents (modules))



(defenum vl-vardecltype-p
  (:vl-integer
   :vl-real
   :vl-time
   :vl-realtime)
  :parents (modules)
  :short "Representation of variable types."
  :long "<p>We represent Verilog's variable types with the keyword symbols
recognized by @(call vl-vardecltype-p).</p>

<p><b>BOZO</b> consider consolidating variable and register declarations into a
single parse tree element by adding an extra reg type to vl-vardecl-p.</p>")


(defaggregate vl-vardecl
  :parents (modules)
  :short "Representation of a single variable declaration."
  :tag :vl-vardecl
  :legiblep nil

  ((name    stringp
            :rule-classes :type-prescription
            "Name of the variable being declared.")

   (type    vl-vardecltype-p
            "Kind of variable, e.g., integer, real, etc.")

   (arrdims vl-rangelist-p
            "A list of array dimensions; empty unless this is an array or
             multi-dimensional array of variables.")

   (initval vl-maybe-expr-p
            ;; BOZO eliminate initval and replace with an initial statement.
            ;; Update the docs for vl-initial-p and also below when this is
            ;; done.
            "When present, indicates the initial value for the variable, e.g.,
             if one writes @('integer i = 3;'), then the @('initval') will be
             the @(see vl-expr-p) for @('3').")

   (atts    vl-atts-p
            "Any attributes associated with this declaration.")

   (loc     vl-location-p
            "Where the declaration was found in the source code."))

  :long "<p>We use @('vl-vardecl-p')s to represent @('integer'), @('real'),
@('time'), and @('realtime') variable declarations.  As with nets and ports,
our parser splits up combined declarations such as \"integer a, b\" into
multiple, individual declarations, so each @('vl-vardecl-p') represents only
one declaration.</p>")


(defaggregate vl-regdecl
  :parents (modules)
  :short "Representation of a single @('reg') declaration."
  :tag :vl-regdecl
  :legiblep nil
  ((name    stringp
            :rule-classes :type-prescription
            "Name of the register being declared.")

   (signedp booleanp
            :rule-classes :type-prescription
            "Indicates whether they keyword @('signed') was used in the
             declaration of the register.  By default, registers are
             unsigned.")

   (range   vl-maybe-range-p
            "Size for wide registers; see also @(see vl-netdecl-p) for
             more discussion of @('range') versus @('arrdims').")

   (arrdims vl-rangelist-p
            "Array dimensions for arrays of registers; see @(see
             vl-netdecl-p) for more discussion.")

   (initval vl-maybe-expr-p
            ;; BOZO eliminate initval and replace with an initial statement.
            ;; Update the docs for vl-initial-p and also below when this is
            ;; done.
            "When present, indicates the initial value for this register.")

   (atts    vl-atts-p
            "Any attributes associated with this declaration.")

   (loc     vl-location-p
            "Where the declaration was found in the source code."))

  :long "<p>@('vl-regdecl-p') is our representation for a single @('reg')
declaration.  Our parser splits up combined declarations such as \"reg a, b\"
into multiple, individual declarations, so each @('vl-regdecl-p') represents
only one declaration.</p>")


(defaggregate vl-eventdecl
  :parents (modules)
  :short "Representation of a single event declaration."
  :tag :vl-eventdecl
  :legiblep nil

  ((name    stringp
            :rule-classes :type-prescription
            "Name of the event being declared.")
   (arrdims vl-rangelist-p
            "Indicates that this is an array of events?  Because that makes
             sense?")
   (atts    vl-atts-p
            "Any attributes associated with this declaration.")
   (loc     vl-location-p
            "Where the declaration was found in the source code."))

  :long "<p>BOZO document event declarations.</p>")


(defenum vl-paramdecltype-p
  (:vl-plain
   :vl-integer
   :vl-real
   :vl-realtime
   :vl-time
   :vl-signed)
  :parents (modules)
  :short "Representation of parameter types."
  :long "<p>We represent Verilog's parameter types with the keyword symbols
recognized by @(call vl-paramdecltype-p).  The valid keywords are visible in
its definition:</p>

@(def vl-paramdecltype-p)

<p>What do these types mean?  Here is the syntax for parameters:</p>

@({
parameter_declaration ::=
    'parameter' ['signed'] [range] list_of_param_assignments
  | 'parameter' parameter_type list_of_param_assignments

parameter_type ::=
   'integer' | 'real' | 'realtime' | 'time'
})

<p>In other words, every declaration either has:</p>

<ul>

<li>A \"parameter_type\" (@('integer'), @('real'), @('realtime'), or
@('time')), in which case we use the symbols @(':vl-integer'), @(':vl-real'),
@(':vl-time'), or @(':vl-realtime'); <b>OR</b></li>

<li>A @('signed') declaration without any other type, in which case we use
@(':vl-signed'), <b>OR</b></li>

<li>(most commonly) No type or sign declaration whatsoever, in which case we
use @(':vl-plain').</li>

</ul>")

(defaggregate vl-paramdecl
  :parents (modules)
  :short "Representation of a single @('parameter') or @('localparam')
declaration."
  :tag :vl-paramdecl
  :legiblep nil

  ((name   stringp
           :rule-classes :type-prescription
           "Name of the parameter being declared.")

   (expr   vl-expr-p
           "Default value for this parameter.")

   (type   vl-paramdecltype-p
           "Indicates the type of the parameter, e.g., @('signed'), @('integer'),
            @('realtime'), etc.")

   (localp booleanp
           :rule-classes :type-prescription
           "True for @('localparam') declarations, @('nil') for @('parameter')
            declarations.  The difference is apparently that @('localparam')s
            such as @('TWICE_WIDTH') below cannot be overridden from outside
            the module, except insofar as that they depend upon non-local
            parameters.  (These @('localparam') declarations are a way to
            introduce named constants without polluting the @('`define')
            namespace.)")

   (range  vl-maybe-range-p
           "Some ridiculous thing allowed by the grammar and who knows what it
            means.  Some description of it in 12.2.")

   (atts   vl-atts-p
           "Any attributes associated with this declaration.")

   (loc    vl-location-p
           "Where the declaration was found in the source code."))

  :long "<p>Parameters are discussed in 12.2.  Some examples of parameter
declarations include:</p>

@({
module mymod (a, b, ...) ;
  parameter WIDTH = 3;
  localparam TWICE_WIDTH = 2 * WIDTH;
  ...
endmodule
})")

(deflist vl-vardecllist-p (x)
  (vl-vardecl-p x)
  :elementp-of-nil nil
  :parents (modules))

(deflist vl-regdecllist-p (x)
  (vl-regdecl-p x)
  :elementp-of-nil nil
  :parents (modules))

(deflist vl-eventdecllist-p (x)
  (vl-eventdecl-p x)
  :elementp-of-nil nil
  :parents (modules))

(deflist vl-paramdecllist-p (x)
  (vl-paramdecl-p x)
  :elementp-of-nil nil
  :parents (modules))

(deflist vl-paramdecllist-list-p (x)
  (vl-paramdecllist-p x)
  :elementp-of-nil t
  :parents (modules))



(define vl-blockitem-p (x)
  :parents (modules)
  :short "Recognizer for a valid block item."
  :long "<p>@('vl-blockitem-p') is a sum-of-products style type for recognizing
valid block items.  The valid block item declarations are register
declarations, variable declarations (integer, real, time, and realtime), event
declarations, and parameter declarations (parameter and localparam), which we
represent as @(see vl-regdecl-p), @(see vl-vardecl-p), @(see vl-eventdecl-p),
and @(see vl-paramdecl-p) objects, respectively.</p>"
  (mbe :logic
       (or (vl-regdecl-p x)
           (vl-vardecl-p x)
           (vl-eventdecl-p x)
           (vl-paramdecl-p x))
       :exec
       (case (tag x)
         (:vl-regdecl (vl-regdecl-p x))
         (:vl-vardecl (vl-vardecl-p x))
         (:vl-eventdecl (vl-eventdecl-p x))
         (:vl-paramdecl (vl-paramdecl-p x))
         (otherwise nil)))
  ///
  (defthm vl-regdecl-p-by-tag-when-vl-blockitem-p
    (implies (and (equal (tag x) :vl-regdecl)
                  (vl-blockitem-p x))
             (vl-regdecl-p x)))

  (defthm vl-vardecl-p-by-tag-when-vl-blockitem-p
    (implies (and (equal (tag x) :vl-vardecl)
                  (vl-blockitem-p x))
             (vl-vardecl-p x)))

  (defthm vl-eventdecl-p-by-tag-when-vl-blockitem-p
    (implies (and (equal (tag x) :vl-eventdecl)
                  (vl-blockitem-p x))
             (vl-eventdecl-p x)))

  (defthm vl-paramdecl-p-by-tag-when-vl-blockitem-p
    (implies (and (equal (tag x) :vl-paramdecl)
                  (vl-blockitem-p x))
             (vl-paramdecl-p x)))

  (defthm vl-blockitem-p-when-invalid-tag
    (implies (and (not (equal (tag x) :vl-regdecl))
                  (not (equal (tag x) :vl-vardecl))
                  (not (equal (tag x) :vl-eventdecl))
                  (not (equal (tag x) :vl-paramdecl)))
             (equal (vl-blockitem-p x)
                    nil))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm vl-blockitem-p-when-vl-regdecl-p
    (implies (vl-regdecl-p x)
             (vl-blockitem-p x)))

  (defthm vl-blockitem-p-when-vl-vardecl-p
    (implies (vl-vardecl-p x)
             (vl-blockitem-p x)))

  (defthm vl-blockitem-p-when-vl-eventdecl-p
    (implies (vl-eventdecl-p x)
             (vl-blockitem-p x)))

  (defthm vl-blockitem-p-when-vl-paramdecl-p
    (implies (vl-paramdecl-p x)
             (vl-blockitem-p x))))


(deflist vl-blockitemlist-p (x)
  (vl-blockitem-p x)
  :elementp-of-nil nil
  :parents (modules)
  :rest
  ((defthm vl-blockitemlist-p-when-vl-regdecllist-p
     (implies (vl-regdecllist-p x)
              (vl-blockitemlist-p x)))
   (defthm vl-blockitemlist-p-when-vl-vardecllist-p
     (implies (vl-vardecllist-p x)
              (vl-blockitemlist-p x)))
   (defthm vl-blockitemlist-p-when-vl-eventdecllist-p
     (implies (vl-eventdecllist-p x)
              (vl-blockitemlist-p x)))
   (defthm vl-blockitemlist-p-when-vl-paramdecllist-p
     (implies (vl-paramdecllist-p x)
              (vl-blockitemlist-p x)))))



;                              EVENT CONTROLS
;
; Delay controls are represented just using tagged expressions.
;
; Repeat event controls are represented using simple aggregates.
;

(defenum vl-evatomtype-p
  (:vl-noedge
   :vl-posedge
   :vl-negedge)
  :parents (vl-evatom-p)
  :short "Type of an item in an event control list."
  :long "<p>Any particular atom in the event control list might have a
@('posedge'), @('negedge'), or have no edge specifier at all, e.g., for plain
atoms like @('a') and @('b') in @('always @(a or b)').</p>")

(defaggregate vl-evatom
  :parents (modules)
  :short "A single item in an event control list."
  :tag :vl-evatom
  :legiblep nil

  ((type vl-evatomtype-p
         "Kind of atom, e.g., posedge, negedge, or plain.")

   (expr vl-expr-p
         "Associated expression, e.g., @('foo') for @('posedge foo')."))

  :long "<p>Event expressions and controls are described in Section 9.7.</p>

<p>We represent the expressions for an event control (see @(see
vl-eventcontrol-p)) as a list of @('vl-evatom-p') structures.  Each individual
evatom is either a plain Verilog expression, or is @('posedge') or @('negedge')
applied to a Verilog expression.</p>")

(deflist vl-evatomlist-p (x)
  (vl-evatom-p x)
  :elementp-of-nil nil
  :parents (modules))



(defaggregate vl-eventcontrol
  :parents (modules)
  :short "Representation of an event controller like @('@(posedge clk)') or
@('@(a or b)')."
  :tag :vl-eventcontrol
  :legiblep nil

  ((starp booleanp
          :rule-classes :type-prescription
          "True to represent @('@(*)'), or @('nil') for any other kind of
           event controller.")

   (atoms vl-evatomlist-p
          "A list of @(see vl-evatom-p)s that describe the various
           events. Verilog allows two kinds of syntax for these lists, e.g.,
           one can write @('@(a or b)') or @('@(a, b)').  The meaning is
           identical in either case, so we just use a list of atoms."))

  :long "<p>Event controls are described in Section 9.7.  We represent each
event controller as a @('vl-eventcontrol-p') aggregates.</p>")

(defaggregate vl-delaycontrol
  :parents (modules)
  :short "Representation of a delay controller like @('#6')."
  :tag :vl-delaycontrol
  :legiblep nil
  ((value vl-expr-p "The expression that governs the delay amount."))

  :long "<p>Delay controls are described in Section 9.7.  An example is</p>

@({
  #10 foo = 1;   <-- The #10 is a delay control
})")

(defaggregate vl-repeateventcontrol
  :parents (modules)
  :short "Representation of @('repeat') constructs in intra-assignment delays."
  :tag :vl-repeat-eventcontrol
  :legiblep nil
  ((expr vl-expr-p
         "The number of times to repeat the control, e.g., @('3') in the below
          example.")

   (ctrl vl-eventcontrol-p
         "Says which event to wait for, e.g., @('@(posedge clk)') in the below
          example."))

  :long "<p>See Section 9.7.7.  These are used to represent special
intra-assignment delays, where the assignment should not occur until some
number of occurrences of an event.  For instance:</p>

@({
   a = repeat(3) @(posedge clk)   <-- repeat expr ctrl
         b;                       <-- statement to repeat
})

<p><b>BOZO</b> Consider consolidating all of these different kinds of
controls into a single, unified representation.  E.g., you could at
least extend eventcontrol with a maybe-expr that is its count, and get
rid of repeateventcontrol.</p>")

(define vl-delayoreventcontrol-p (x)
  :parents (modules)
  :short "BOZO document this."
  (mbe :logic
       (or (vl-delaycontrol-p x)
           (vl-eventcontrol-p x)
           (vl-repeateventcontrol-p x))
       :exec
       (case (tag x)
         (:vl-delaycontrol (vl-delaycontrol-p x))
         (:vl-eventcontrol (vl-eventcontrol-p x))
         (:vl-repeat-eventcontrol (vl-repeateventcontrol-p x))))
  ///
  (defthm vl-delayoreventcontrol-p-when-vl-delaycontrol-p
    (implies (vl-delaycontrol-p x)
             (vl-delayoreventcontrol-p x)))

  (defthm vl-delayoreventcontrol-p-when-vl-eventcontrol-p
    (implies (vl-eventcontrol-p x)
             (vl-delayoreventcontrol-p x)))

  (defthm vl-delayoreventcontrol-p-when-vl-repeateventcontrol-p
    (implies (vl-repeateventcontrol-p x)
             (vl-delayoreventcontrol-p x)))

  (defthm vl-delaycontrol-p-by-tag-when-vl-delayoreventcontrol-p
    (implies (and (equal (tag x) :vl-delaycontrol)
                  (vl-delayoreventcontrol-p x))
             (vl-delaycontrol-p x)))

  (defthm vl-eventcontrol-p-by-tag-when-vl-delayoreventcontrol-p
    (implies (and (equal (tag x) :vl-eventcontrol)
                  (vl-delayoreventcontrol-p x))
             (vl-eventcontrol-p x)))

  (defthm vl-repeateventcontrol-p-by-tag-when-vl-delayoreventcontrol-p
    (implies (and (equal (tag x) :vl-repeat-eventcontrol)
                  (vl-delayoreventcontrol-p x))
             (vl-repeateventcontrol-p x)))

  (defthm vl-delayoreventcontrol-p-cases
    (implies (and (not (equal (tag x) :vl-delaycontrol))
                  (not (equal (tag x) :vl-eventcontrol))
                  (not (equal (tag x) :vl-repeat-eventcontrol)))
             (equal (vl-delayoreventcontrol-p x)
                    nil))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))


(define vl-maybe-delayoreventcontrol-p (x)
  :inline t
  :parents (modules)
  :short "BOZO document this."
  (or (not x)
      (vl-delayoreventcontrol-p x))
  ///
  (defthm vl-maybe-delayoreventcontrol-p-when-vl-delayoreventcontrol-p
    (implies (vl-delayoreventcontrol-p x)
             (vl-maybe-delayoreventcontrol-p x)))

  (defthm vl-delayoreventcontrol-p-when-vl-maybe-delayoreventcontrol-p
    (implies (vl-maybe-delayoreventcontrol-p x)
             (equal (vl-delayoreventcontrol-p x)
                    (if x t nil)))))


(defenum vl-assign-type-p
  (:vl-blocking
   :vl-nonblocking
   :vl-assign
   :vl-force)
  :parents (vl-stmt-p)
  :short "Type of an assignment statement."
  :long "<p>@(':vl-blocking') and @(':vl-nonblocking') are for
blocking/nonblocking procedural assignments, e.g., @('foo = bar') and @('foo <=
bar'), respectively.</p>

<p>@(':vl-assign') and @(':vl-force') are for procedural continuous
assignments, e.g., @('assign foo = bar') or @('force foo = bar'),
respectivley.</p>")

(defaggregate vl-assignstmt
  :parents (vl-stmt-p)
  :short "Representation of an assignment statement."
  :tag :vl-assignstmt
  :legiblep nil

  ((type   vl-assign-type-p
           "Kind of assignment statement, e.g., blocking, nonblocking, etc.")

   (lvalue vl-expr-p
           "Location being assigned to.  Note that the specification places
            various restrictions on lvalues, e.g., for a procedural assignment
            the lvalue may contain only plain variables, and bit-selects,
            part-selects, memory words, and nested concatenations of these
            things.  We do not enforce these restrictions in
            @('vl-assignstmt-p'), but only require that the lvalue is an
            expression.")

   (expr   vl-expr-p
           "The right-hand side expression that should be assigned to the
            lvalue.")

   (ctrl   vl-maybe-delayoreventcontrol-p
           "Control that affects when the assignment is done, if any.  These
            controls can be a delay like @('#(6)') or an event control like
            @('@(posedge clk)').  The rules for this are covered in Section
            9.2 and appear to perhaps be different depending upon the type of
            assignment.  Further coverage seems to be available in Section
            9.7.7.")

   (atts   vl-atts-p
           "Any attributes associated with this statement.")

   (loc    vl-location-p
           "Where the statement was found in the source code."))

  :long "<p>Assignment statements are covered in Section 9.2.  There are two
major types of assignment statements.</p>

<h4>Procedural Assignments</h4>

<p>Procedural assignment statements may only be used to assign to @('reg'),
@('integer'), @('time'), @('realtime'), and memory data types, and cannot be
used to assign to ordinary nets such as @('wire')s.  There are two kinds of
procedural assignments: </p>

@({
   foo = bar ;     // \"blocking\" -- do the assignment now
   foo <= bar ;    // \"nonblocking\" -- schedule the assignment to occur
})

<p>The difference between these two statements has to do with Verilog's timing
model and simulation semantics.  In particular, a blocking assignment
\"executes before the statements that follow it,\" whereas a non-blocking
assignment only \"schedules\" an assignment to occur and can be thought of as
executing in parallel with what follows it.</p>

<h4>Continuous Procedural Assignments</h4>

<p>Continuous procedural assignment statements may apparently be used to assign
to either nets or variables.  There are two kinds:</p>

@({
  assign foo = bar ;  // only for variables
  force foo = bar ;   // for variables or nets
})

<p>We represent all of these kinds of assignment statements uniformly as
@('vl-assignstmt-p') objects.</p>")

(defenum vl-deassign-type-p
  (:vl-deassign :vl-release)
  :parents (vl-stmt-p)
  :short "Type of an deassignment statement.")

(defaggregate vl-deassignstmt
  :parents (vl-stmt-p)
  :short "Representation of a deassign or release statement."
  :tag :vl-deassignstmt
  :legiblep nil
  ((type   vl-deassign-type-p)
   (lvalue vl-expr-p)
   (atts   vl-atts-p "Any attributes associated with this statement."))
  :long "<p>Deassign and release statements are described in Section 9.3.1 and
9.3.2.</p>")

(defaggregate vl-enablestmt
  :parents (vl-stmt-p)
  :short "Representation of an enable statement."
  :tag :vl-enablestmt
  :legiblep nil
  ((id   vl-expr-p)
   (args vl-exprlist-p)
   (atts vl-atts-p "Any attributes associated with this statement."))
  :long "<p>Enable statements have an identifier (which should be either a
hierarchial identifier or a system identifier), which we represent as an
expression.  They also have a list of arguments, which are expressions.</p>")

(defaggregate vl-disablestmt
  :parents (vl-stmt-p)
  :short "Representation of a disable statement."
  :tag :vl-disablestmt
  :legiblep nil
  ((id   vl-expr-p)
   (atts vl-atts-p "Any attributes associated with this statement."))
  :long "<p>Disable statements are simpler and just have a hierarchial
identifier.  Apparently there are no disable statements for system
identifiers.</p>")

(defaggregate vl-eventtriggerstmt
  :parents (vl-stmt-p)
  :short "Representation of an event trigger."
  :tag :vl-eventtriggerstmt
  :legiblep nil
  ((id   vl-expr-p
         "Typically a name like @('foo') and @('bar'), but may instead be a
          hierarchical identifier.")
   (atts vl-atts-p
         "Any attributes associated with this statement."))

  :long "<p>Event trigger statements are used to explicitly trigger named
events.  They are discussed in Section 9.7.3 and looks like this:</p>

@({
 -> foo;
 -> bar[1][2][3];  // I think?
})

<p><b>BOZO</b> are we handling the syntax correctly?  What about the
expressions that can follow the trigger?  Maybe they just become part of the
@('id')?</p>")

(defaggregate vl-nullstmt
  :parents (vl-stmt-p)
  :short "Representation of an empty statement."
  :tag :vl-nullstmt
  :legiblep nil
  ((atts vl-atts-p "Any attributes associated with this statement."))
  :long "<p>We allow explicit null statements.  This allows us to canonicalize
@('if') expressions so that any missing branches are turned into null
statements.</p>")

(define vl-atomicstmt-p (x)
  :parents (vl-stmt-p)
  :short "Representation of an atomic statement."
  :long "<p>@('vl-atomicstmt-p') is a sum-of-products style recognizer for the
different kinds of atomic statements.</p>"
  (mbe :logic (or (vl-nullstmt-p x)
                  (vl-assignstmt-p x)
                  (vl-deassignstmt-p x)
                  (vl-enablestmt-p x)
                  (vl-disablestmt-p x)
                  (vl-eventtriggerstmt-p x))
       :exec (case (tag x)
               (:vl-nullstmt         (vl-nullstmt-p x))
               (:vl-assignstmt       (vl-assignstmt-p x))
               (:vl-deassignstmt     (vl-deassignstmt-p x))
               (:vl-enablestmt       (vl-enablestmt-p x))
               (:vl-disablestmt      (vl-disablestmt-p x))
               (:vl-eventtriggerstmt (vl-eventtriggerstmt-p x))
               (otherwise            nil)))
  ///
  (defthm consp-when-vl-atomicstmt-p
    (implies (vl-atomicstmt-p x)
             (consp x))
    :rule-classes :compound-recognizer)

  (defthm vl-nullstmt-p-by-tag-when-vl-atomicstmt-p
    (implies (and (equal (tag x) :vl-nullstmt)
                  (vl-atomicstmt-p x))
             (vl-nullstmt-p x)))

  (defthm vl-assignstmt-p-by-tag-when-vl-atomicstmt-p
    (implies (and (equal (tag x) :vl-assignstmt)
                  (vl-atomicstmt-p x))
             (vl-assignstmt-p x)))

  (defthm vl-deassignstmt-p-by-tag-when-vl-atomicstmt-p
    (implies (and (equal (tag x) :vl-deassignstmt)
                  (vl-atomicstmt-p x))
             (vl-deassignstmt-p x)))

  (defthm vl-enablestmt-p-by-tag-when-vl-atomicstmt-p
    (implies (and (equal (tag x) :vl-enablestmt)
                  (vl-atomicstmt-p x))
             (vl-enablestmt-p x)))

  (defthm vl-disablestmt-p-by-tag-when-vl-atomicstmt-p
    (implies (and (equal (tag x) :vl-disablestmt)
                  (vl-atomicstmt-p x))
             (vl-disablestmt-p x)))

  (defthm vl-eventtriggerstmt-p-by-tag-when-vl-atomicstmt-p
    (implies (and (equal (tag x) :vl-eventtriggerstmt)
                  (vl-atomicstmt-p x))
             (vl-eventtriggerstmt-p x)))

  (defthm vl-atomicstmt-p-when-invalid-tag
    ;; This is useful for safe-case, to show that all of the cases have been
    ;; covered.  Hopefully the backchain limit keeps it from being too expensive.
    (implies (and (not (equal (tag x) :vl-nullstmt))
                  (not (equal (tag x) :vl-assignstmt))
                  (not (equal (tag x) :vl-deassignstmt))
                  (not (equal (tag x) :vl-enablestmt))
                  (not (equal (tag x) :vl-disablestmt))
                  (not (equal (tag x) :vl-eventtriggerstmt)))
             (equal (vl-atomicstmt-p x)
                    nil))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm vl-atomicstmt-p-when-vl-nullstmt-p
    (implies (vl-nullstmt-p x)
             (vl-atomicstmt-p x)))

  (defthm vl-atomicstmt-p-when-vl-assignstmt-p
    (implies (vl-assignstmt-p x)
             (vl-atomicstmt-p x)))

  (defthm vl-atomicstmt-p-when-vl-deassignstmt-p
    (implies (vl-deassignstmt-p x)
             (vl-atomicstmt-p x)))

  (defthm vl-atomicstmt-p-when-vl-enablestmt-p
    (implies (vl-enablestmt-p x)
             (vl-atomicstmt-p x)))

  (defthm vl-atomicstmt-p-when-vl-disablestmt-p
    (implies (vl-disablestmt-p x)
             (vl-atomicstmt-p x)))

  (defthm vl-atomicstmt-p-when-vl-eventtriggerstmt-p
    (implies (vl-eventtriggerstmt-p x)
             (vl-atomicstmt-p x))))


(defenum vl-compoundstmttype-p
  (:vl-casestmt
   :vl-ifstmt
   :vl-foreverstmt
   :vl-waitstmt
   :vl-repeatstmt
   :vl-whilestmt
   :vl-forstmt
   :vl-blockstmt
   :vl-timingstmt)
  :parents (vl-stmt-p)
  :short "Recognizes the possible types for compound statements."

  :long "<p>See @(see vl-compoundstmt-p) for a description of compound
statements.  The @('type') of each compound statement is one of the keyword
symbols recognized by @('vl-compoundstmttype-p').</p>

<p>Most of these are obvious, but note that:</p>

<ul>

<li>@(':vl-casestmt') is used for @('case'), @('casex'), and @('casez')
statements.  See the compound statement's @('casetype') field for the detailed
type.</li>

<li>@(':vl-blockstmt') is used for both sequential (@('begin ... end')) and
parallel (@('fork ... join')) blocks.  See the compound statement's
@('sequentialp') field for the detailed type.</li>

<li>Timing statements are used for things like @('@(posedge clk) substmt'),
@('@(foo or bar) substmt'), and @('#6 substmt').</li>

</ul>")

(defenum vl-casetype-p
  (nil
   :vl-casex
   :vl-casez)
  :parents (vl-stmt-p)
  :short "Recognizes the possible kinds of case statements."
  :long "<ul>

<li>@('nil') for ordinary @('case') statements,</li>

<li>@(':vl-casex') for @('casex') statements, and</li>

<li>@(':vl-casez') for @('casez') statements.</li>

</ul>")

(define vl-compoundstmt-basic-checksp
  ((type        vl-compoundstmttype-p)
   (exprs       vl-exprlist-p)
   (stmts       "no guard due to mutual recursion")
   (name        vl-maybe-string-p)
   (decls       vl-blockitemlist-p)
   (ctrl        vl-maybe-delayoreventcontrol-p)
   (sequentialp booleanp)
   (casetype    vl-casetype-p))
  :returns okp
  :parents (vl-compoundstmt-p)
  :short "Additional structural checks for compound statements."
  :long "<p>This is a well-formedness constraint imposed on @(see
vl-compoundstmt-p) structures.  It is responsible for ensuring that, e.g., an
@('if') statement properly has a single expression (its condition), two
sub-statements (its true and false branches), and no inappropriate fields such
as @('name'), @('decls'), or @('ctrl') which are only appropriate for other
kinds of statements.</p>"

  (let ((num-exprs (len exprs))
        (num-stmts (len stmts)))
      (case type
        ((:vl-casestmt)
         ;; Format is:
         ;;   EXPRS = TEST-EXPR, MATCH1-EXPR, MATCH2-EXPR, ..., MATCHN-EXPR
         ;;   STMTS = DEFAULT-STMT, MATCH1-STMT, MATCH2-STMT, ..., MATCHN-STMT
         ;; This lets us quickly get at any of the things we want; see
         ;; mu-stmt-tools.lisp
         (and (not name)
              (not ctrl)
              (not sequentialp)
              (atom decls)
              (consp exprs)
              (= num-exprs num-stmts)))
        (:vl-ifstmt
         ;; (IF expr stmt stmt)
         (and (not name)
              (not ctrl)
              (not sequentialp)
              (not casetype)
              (atom decls)
              (= num-exprs 1)
              (= num-stmts 2)))
        ((:vl-foreverstmt)
         ;; (FOREVER stmt)
         (and (not name)
              (not ctrl)
              (not sequentialp)
              (not casetype)
              (atom decls)
              (atom exprs)
              (= num-stmts 1)))
        ((:vl-waitstmt :vl-repeatstmt :vl-whilestmt)
         ;; (REPEAT expr stmt)
         ;; (WHILE expr stmt)
         ;; (WAIT expr stmt)
         (and (not name)
              (not ctrl)
              (not sequentialp)
              (not casetype)
              (atom decls)
              (= num-exprs 1)
              (= num-stmts 1)))
        ((:vl-forstmt)
         ;; (FOR var_assignment; expr; var_assignment) body
         (and (not name)
              (not ctrl)
              (not sequentialp)
              (not casetype)
              (atom decls)
              (= num-exprs 5) ;; init-lhs, init-rhs, test, next-lhs, next-rhs
              (= num-stmts 1) ;; body
              ))
        ((:vl-blockstmt)
         ;; BEGIN ... END, or FORK ... JOIN, per sequentialp
         (and (not ctrl)
              (not casetype)
              (atom exprs)))
        ((:vl-timingstmt)
         ;; ctrl stmt
         (and (not name)
              (not sequentialp)
              (not casetype)
              (atom exprs)
              (atom decls)
              ctrl
              (= num-stmts 1))))))


(defaggregate vl-compoundstmt
  :parents (vl-stmt-p)
  :short "Representation of a compound statement."
  :tag :vl-compoundstmt
  :legiblep nil
  ((type        vl-compoundstmttype-p
                "Keyword symbol that says what kind of statement this is,
                 e.g., an @('if') statement, @('while') loop, etc.")

   (exprs       vl-exprlist-p
                "A list of expressions associated with the statement. Some
                 statements (e.g., @('begin ... end') blocks) have no
                 expressions, but other statements, such as @('if'),
                 @('while'), and @('case') statements, may have one or many.")

   (stmts       "Any sub-statements that are associated with the statement.
                 Every kind of compound statement may have sub-statements,
                 since otherwise it would be an atomic statement.  Note that
                 there is no restriction on @('stmts') in
                 @('vl-compoundstmt-p') itself due to mutual recursion; see
                 @(see vl-stmt-p).")

   (name        vl-maybe-string-p
                :rule-classes
                ((:type-prescription)
                 (:rewrite :corollary
                           (implies (force (vl-compoundstmt-p x))
                                    (equal (stringp (vl-compoundstmt->name x))
                                           (if (vl-compoundstmt->name x)
                                               t
                                             nil)))))
                "Only valid on block statements (i.e., @('begin ... end') and
                 @('fork ... join') statements).  If present, it is a string
                 that names this block.")

   (decls       vl-blockitemlist-p
                "Only valid on block statements.  Contains any declarations for
                 the block; see @(see vl-blockitem-p).")

   (ctrl        vl-maybe-delayoreventcontrol-p
                :rule-classes
                ((:rewrite)
                 (:rewrite
                  :corollary
                  (implies (force (vl-compoundstmt-p x))
                           (iff (vl-delayoreventcontrol-p (vl-compoundstmt->ctrl x))
                                (vl-compoundstmt->ctrl x)))))
                "Only valid on procedural timing control statements like
                 @('@(posedge clk) substmt') or @('#6 substmt').  If present,
                 describes what to wait for, e.g., this is the @('@(posedge
                 clk)') or @('#6') part.")

   (sequentialp booleanp
                :rule-classes :type-prescription
                "Only valid on block statements.  This is @('t') for a
                 @('begin/end') block, or @('nil') if this is a @('fork/join')
                 block.")

   (casetype    vl-casetype-p
                "Only valid on case statements.  Indicates whether this is a
                 @('case'), @('casex'), or @('casez') statement.")

   (atts        vl-atts-p
                "Any attributes associated with this statement."))
  :require
  ((vl-compoundstmt-basic-checksp-of-vl-compoundstmt
    (vl-compoundstmt-basic-checksp type exprs stmts name decls
                                   ctrl sequentialp casetype)))

  :long "<h3>Introduction</h3>

<p>My original approach to statements was essentially in the SDT (\"syntax
definition tree\") style.  I had a separate kind of node for each statement,
e.g., I had a @('vl-ifstmt-p'), a @('vl-whilestmt-p'), and so on.  This was
extraordinarily unwieldy and difficult to work with.  I ended up needing to
introduce something like an 11-part mutual-recursion to work with any
statement, and this was quite cumbersome.</p>

<p>My new approach is to merge the different kinds of compound statements into
a single @('vl-compoundstmt-p') type.  This is a more of an AST (\"abstract
syntax tree\") style, and is basically similar to how <see topic=\"@(url
vl-expr-p)\">expressions</see> are handled.</p>

<p>In the new representation, each compound statement has several components,
some of which may not be applicable depending upon the particular kind of
statement we are dealing with.  The advantage of combining all of these things
together is that we can recur over statements while largely ignoring their
actual types, etc., making the mutually recursive scheme much simpler.</p>

<h3>Basic Well-Formedness Checks</h3>

<p>A \"problem\" with using a combined representation is that, for instance, an
@('if') statement has various fields like @('name'), @('decls'), and @('ctrl')
which it really should not have.  A somewhat similar problem is that, e.g.,
@('for') statements need a certain number of expressions, so how do we know it
has the right number?</p>

<p>To address these kinds of concerns, in addition to the simple type checks
for each field, we use @(see vl-compoundstmt-basic-checksp) to carry out
additional well-formedness checking on a per-field basis.  This check ensures
that, for instance, an @('if') statement has no @('name'), and that a @('for')
statement has the right number of expressions.</p>"

  :rest
  ((defthm acl2-count-of-vl-compoundstmt->stmts
     (and (<= (acl2-count (vl-compoundstmt->stmts x))
              (acl2-count x))
          (implies (consp x)
                   (< (acl2-count (vl-compoundstmt->stmts x))
                      (acl2-count x))))
     :hints(("Goal" :in-theory (enable vl-compoundstmt->stmts)))
     :rule-classes ((:rewrite) (:linear)))

   (defthm type-of-vl-compoundstmt->type
     (implies (force (vl-compoundstmt-p x))
              (and (symbolp (vl-compoundstmt->type x))
                   (not (equal (vl-compoundstmt->type x) nil))
                   (not (equal (vl-compoundstmt->type x) t))))
     :hints(("Goal"
             :in-theory (disable type-when-vl-compoundstmttype-p)
             :use ((:instance type-when-vl-compoundstmttype-p
                              (x (vl-compoundstmt->type x)))))))

   (defthm vl-atomicstmt-p-tag-not-compoundstmt
     ;; Hrmn.  This is kind of ugly.  I guess it's not so bad.
     (implies (vl-atomicstmt-p x)
              (not (equal :vl-compoundstmt (tag x))))
     :rule-classes :forward-chaining
     :hints(("Goal" :in-theory (enable vl-atomicstmt-p))))))



(defsection vl-stmt-p
  :parents (modules)
  :short "Representation of a statement."

  :long "<p>Verilog includes a number of statements for behavioral modelling.
Some of these (assignments, event triggers, enables and disables) are
<b>atomic</b> in that they do not contain any sub-statements.  We call the
other statements (loops, cases, if statements, etc.) <b>compound</b> since they
contain sub-statements and are mutually-recursive with @('vl-stmt-p').</p>

<p>Atomic statements are recognized with @(see vl-atomicstmt-p), while compound
statements are recognized with @(see vl-compoundstmt-p).</p>"

  (mutual-recursion

   (defund vl-stmt-p (x)
     (declare (xargs :guard t))
     (mbe :logic (or (vl-atomicstmt-p x)
                     (and (vl-compoundstmt-p x)
                          (vl-stmtlist-p (vl-compoundstmt->stmts x))))
          :exec (if (eq (tag x) :vl-compoundstmt)
                    (and (vl-compoundstmt-p x)
                         (vl-stmtlist-p (vl-compoundstmt->stmts x)))
                  (vl-atomicstmt-p x))))

   (defund vl-stmtlist-p (x)
     (declare (xargs :guard t))
     (if (consp x)
         (and (vl-stmt-p (car x))
              (vl-stmtlist-p (cdr x)))
       t)))

  ;; I'm not exactly sure what to put here, and what to put in mlib/stmt-tools.
  ;; I'm going to try to keep most stuff in stmt-tools, and just leave a few
  ;; basics here.

  (FLAG::make-flag vl-flag-stmt-p
                   vl-stmt-p
                   :flag-mapping ((vl-stmt-p . stmt)
                                  (vl-stmtlist-p . list)))

  (defthm vl-stmtlist-p-when-not-consp
    (implies (not (consp x))
             (equal (vl-stmtlist-p x)
                    t))
    :hints(("Goal" :in-theory (enable vl-stmtlist-p))))

  (defthm vl-stmtlist-p-of-cons
    (equal (vl-stmtlist-p (cons a x))
           (and (vl-stmt-p a)
                (vl-stmtlist-p x)))
    :hints(("Goal" :in-theory (enable vl-stmtlist-p))))

  (deflist vl-stmtlist-p (x)
    (vl-stmt-p x)
    :already-definedp t)

  (local (in-theory (enable vl-stmt-p)))

  (defthm consp-when-vl-stmt-p
    (implies (vl-stmt-p x)
             (consp x))
    :rule-classes :compound-recognizer)

  (defthm vl-compoundstmt-p-when-not-vl-atomicstmt-p
    (implies (vl-stmt-p x)
             (equal (vl-compoundstmt-p x)
                    (not (vl-atomicstmt-p x)))))

  (defthm vl-atomicstmt-p-by-tag-when-vl-stmt-p
    (implies (and (not (equal (tag x) :vl-compoundstmt))
                  (vl-stmt-p x))
             (vl-atomicstmt-p x))
    :hints(("Goal" :in-theory (enable vl-stmt-p))))

  (defthm vl-stmt-p-when-vl-atomicstmt-p
    (implies (vl-atomicstmt-p x)
             (vl-stmt-p x)))

  (defthm vl-stmtlist-p-of-vl-compoundstmt->stmts
    (implies (and (force (vl-compoundstmt-p x))
                  (force (vl-stmt-p x)))
             (vl-stmtlist-p (vl-compoundstmt->stmts x))))

  (defthm vl-stmt-p-of-vl-compoundstmt
    (implies (and (force (vl-compoundstmttype-p type))
                  (force (vl-exprlist-p exprs))
                  (force (vl-stmtlist-p stmts))
                  (force (vl-maybe-string-p name))
                  (force (vl-blockitemlist-p decls))
                  (force (vl-maybe-delayoreventcontrol-p ctrl))
                  (force (booleanp sequentialp))
                  (force (vl-casetype-p casetype))
                  (force (vl-atts-p atts))
                  (force (vl-compoundstmt-basic-checksp type exprs stmts name decls ctrl
                                                        sequentialp casetype)))
             (vl-stmt-p (vl-compoundstmt type exprs stmts name decls ctrl
                                         sequentialp casetype atts)))
    :hints(("Goal" :in-theory (enable vl-stmt-p)))))



(define vl-fast-atomicstmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  :parents (vl-atomicstmt-p vl-stmt-p)
  :short "Faster version of @(see vl-atomicstmt-p), given that @(see vl-stmt-p)
is already known."
  :long "<p>We leave this function enabled and reason about
@('vl-atomicstmt-p') instead.</p>"

  (mbe :logic (vl-atomicstmt-p x)
       :exec (not (eq (tag x) :vl-compoundstmt))))

(define vl-fast-compoundstmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  :parents (vl-compoundstmt-p vl-stmt-p)
  :short "Faster version of @(see vl-compoundstmt-p), given that @(see
vl-stmt-p) is already known."
  :long "<p>We leave this function enabled and reason about
@('vl-compoundstmt-p') instead.</p>"
  (mbe :logic (vl-compoundstmt-p x)
       :exec (eq (tag x) :vl-compoundstmt)))

(define vl-fast-nullstmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  :parents (vl-nullstmt-p vl-stmt-p)
  :short "Faster version of @(see vl-nullstmt-p), given that @(see vl-stmt-p)
is already known."
  :long "<p>We leave this function enabled and reason about @('vl-nullstmt-p')
instead.</p>"
  (mbe :logic (vl-nullstmt-p x)
       :exec (eq (tag x) :vl-nullstmt)))

(define vl-fast-assignstmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  :parents (vl-assignstmt-p vl-stmt-p)
  :short "Faster version of @(see vl-assignstmt-p), given that @(see vl-stmt-p)
is already known."
  :long "<p>We leave this function enabled and reason about
@('vl-assignstmt-p') instead.</p>"
  (mbe :logic (vl-assignstmt-p x)
       :exec (eq (tag x) :vl-assignstmt)))

(define vl-fast-enablestmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  :parents (vl-enablestmt-p vl-stmt-p)
  :short "Faster version of @(see vl-enablestmt-p), given that @(see vl-stmt-p)
is already known."
  :long "<p>We leave this function enabled and reason about
@('vl-enablestmt-p') instead.</p>"
  (mbe :logic (vl-enablestmt-p x)
       :exec (eq (tag x) :vl-enablestmt)))

(define vl-atomicstmt->atts ((x vl-atomicstmt-p))
  :returns (atts vl-atts-p :hyp :fguard)
  :parents (vl-atomicstmt-p vl-stmt->atts)
  :short "Get the attributes from any atomic statement."
  (mbe :logic
       (cond ((vl-nullstmt-p x)         (vl-nullstmt->atts x))
             ((vl-assignstmt-p x)       (vl-assignstmt->atts x))
             ((vl-deassignstmt-p x)     (vl-deassignstmt->atts x))
             ((vl-enablestmt-p x)       (vl-enablestmt->atts x))
             ((vl-disablestmt-p x)      (vl-disablestmt->atts x))
             ((vl-eventtriggerstmt-p x) (vl-eventtriggerstmt->atts x)))
       :exec
       (case (tag x)
         (:vl-nullstmt         (vl-nullstmt->atts x))
         (:vl-assignstmt       (vl-assignstmt->atts x))
         (:vl-deassignstmt     (vl-deassignstmt->atts x))
         (:vl-enablestmt       (vl-enablestmt->atts x))
         (:vl-disablestmt      (vl-disablestmt->atts x))
         (:vl-eventtriggerstmt (vl-eventtriggerstmt->atts x)))))

(define vl-stmt->atts ((x vl-stmt-p))
  :inline t
  :returns (atts vl-atts-p :hyp :fguard)
  :parents (vl-stmt-p)
  :short "Get the attributes from any statement."
  (if (vl-fast-atomicstmt-p x)
      (vl-atomicstmt->atts x)
    (vl-compoundstmt->atts x)))



;                       INITIAL AND ALWAYS BLOCKS
;
; Initial and always blocks just have a statement and, perhaps, some
; attributes.

(defaggregate vl-initial
  :parents (modules)
  :short "Representation of an initial statement."
  :tag :vl-initial
  :legiblep nil

  ((stmt vl-stmt-p
         "Represents the actual statement, e.g., @('r = 0') below.")

   (atts vl-atts-p
         "Any attributes associated with this @('initial') block.")

   (loc  vl-location-p
         "Where the initial block was found in the source code."))

  :long "<p>Initial statements in Verilog are used to set up initial values for
simulation.  For instance,</p>

@({
module mymod (a, b, ...) ;
   reg r, s;
   initial r = 0;   <-- initial statement
endmodule
})

<p><b>BOZO</b> Our plan is to eventually generate @('initial') statements from
register and variable declarations with initial values, i.e., @('reg r =
0;').</p>")


(defaggregate vl-always
  :parents (modules)
  :short "Representation of an always statement."
  :tag :vl-always
  :legiblep nil

  ((stmt vl-stmt-p
         "The actual statement, e.g., @('@(posedge clk) myreg <= in')
          below. The statement does not have to include a timing control like
          @('@(posedge clk)') or @('@(a or b or c)'), but often does.")

   (atts vl-atts-p
         "Any attributes associated with this @('always') block.")

   (loc  vl-location-p
         "Where the always block was found in the source code."))

  :long "<p>Always statements in Verilog are often used to model latches and
flops, and to set up other simulation events.  A simple example would be:</p>

@({
module mymod (a, b, ...) ;
  always @(posedge clk) myreg <= in;
endmodule
})")

(deflist vl-initiallist-p (x)
  (vl-initial-p x)
  :elementp-of-nil nil
  :parents (modules))

(deflist vl-alwayslist-p (x)
  (vl-always-p x)
  :elementp-of-nil nil
  :parents (modules))



(defenum vl-taskporttype-p
  (:vl-unsigned
   :vl-signed
   :vl-integer
   :vl-real
   :vl-realtime
   :vl-time)
  :parents (modules)
  :short "Representation for the type of task ports, function return types, and
function inputs."

  :long "<p>These are the various return types that can be used with a Verilog
task's input, output, or inout declarations.  For instance, a task can have
ports such as:</p>

@({
  task mytask;
    input integer count;  // type :vl-integer
    output signed value;  // type :vl-signed
    inout x;              // type :vl-unsigned
    ...
  endtask
})

<p>There isn't an explicit @('unsigned') type that you can write; so note that
@(':vl-unsigned') is really the type for \"plain\" ports that don't have an
explicit type label.</p>

<p>These same types are used for the return values of Verilog functions.  For
instance, we use @(':vl-unsigned') for a function like:</p>

@({ function [7:0] add_one ; ... endfunction })

<p>whereas we use @(':vl-real') for a function like:</p>

@({ function real get_ratio ; ... endfunction })

<p>Likewise, the inputs to Verilog functions use these same kinds of
types.</p>")

(defaggregate vl-taskport
  :parents (modules)
  :short "Representation of a task port or a function input."
  :tag :vl-taskport
  :legiblep nil

  ((name  stringp
          :rule-classes :type-prescription
          "The name of this task port.")

   (dir   vl-direction-p
          :rule-classes
          ((:rewrite)
           (:type-prescription
            :corollary
            (implies (force (vl-taskport-p x))
                     (and (symbolp (vl-taskport->dir x))
                          (not (equal (vl-taskport->dir x) t))
                          (not (equal (vl-taskport->dir x) nil))))))
          "Says whether this is an input, output, or inout port.  Note that
           tasks can have all three kinds of ports, but functions only have
           inputs.")

   (type  vl-taskporttype-p
          :rule-classes
          ((:rewrite)
           (:type-prescription
            :corollary
            (implies (force (vl-taskport-p x))
                     (and (symbolp (vl-taskport->type x))
                          (not (equal (vl-taskport->type x) t))
                          (not (equal (vl-taskport->type x) nil))))))
          "Says what kind of port this is, i.e., @('integer'), @('real'),
          etc.")

   (range vl-maybe-range-p
          "The size of this input.  A range only makes sense when the type is
           @(':vl-unsigned') or @(':vl-signed').  It should be @('nil') when
           other types are used.")

   (atts  vl-atts-p
          "Any attributes associated with this input.")

   (loc   vl-location-p
          "Where this input was found in the source code."))

  :long "<p>Verilog tasks have ports that are similar to the ports of a module.
We represent these ports with their own @('vl-taskport-p') structures, rather
than reusing @(see vl-portdecl-p), because unlike module port declarations,
task ports can have types like @('integer') or @('real').</p>

<p>While Verilog functions don't have @('output') or @('inout') ports, they do
have input ports that are very similar to task ports.  So, we reuse
@('vl-taskport-p') structures for function inputs.</p>")

(deflist vl-taskportlist-p (x)
  (vl-taskport-p x)
  :guard t
  :elementp-of-nil nil)

(defprojection vl-taskportlist->names (x)
  (vl-taskport->name x)
  :guard (vl-taskportlist-p x)
  :nil-preservingp t
  :result-type string-listp)



(defaggregate vl-fundecl
  :parents (modules)
  :short "Representation of a single Verilog function."
  :tag :vl-fundecl
  :legiblep nil

  ((name       stringp
               :rule-classes :type-prescription
               "Name of this function, e.g., @('lower_bits') below.")

   (automaticp booleanp
               :rule-classes :type-prescription
               "Says whether the @('automatic') keyword was provided.  This
                keyword indicates that the function should be reentrant and
                have its local parameters dynamically allocated for each
                function call, with various consequences.")

   (rtype      vl-taskporttype-p
               "Return type of the function, e.g., a function might return an
                ordinary unsigned or signed result of some width, or might
                return a @('real') value, etc.  For instance, the return type
                of @('lower_bits') below is @(':vl-unsigned').")

   (rrange     vl-maybe-range-p
               "Range for the function's return value.  This only makes sense
                when the @('rtype') is @(':vl-unsigned') or @(':vl-signed').
                For instance, the return range of @('lower_bits') below is
                @('[7:0]').")

   (inputs     vl-taskportlist-p
               "The arguments to the function, e.g., @('input [7:0] a') below.
                Functions must have at least one input.  We check this in our
                parser, but we don't syntactically enforce this requirement in
                the @('vl-fundecl-p') structure.  Furthermore, functions may
                only have inputs (i.e., they can't have outputs or inouts), but
                our @(see vl-taskport-p) structures have a direction.  This
                direction should always be @(':vl-input') for a function's
                input; we again check this in our parser, but not in the
                @('vl-fundecl-p') structure itself.")

   (decls      vl-blockitemlist-p
               "Any local variable declarations for the function, e.g., the
                declarations of @('lowest_pair') and @('next_lowest_pair')
                below.  We represent the declarations as an ordinary @(see
                vl-blockitemlist-p), and it appears that it may even contain
                event declarations, parameter declarations, etc., which seems
                pretty absurd.")

   (body       vl-stmt-p
               "The body of the function.  We represent this as an ordinary statement,
                but it must follow certain rules as outlined in 10.4.4, e.g.,
                it cannot have any time controls, cannot enable tasks, cannot
                have non-blocking assignments, etc.")

   (atts       vl-atts-p
               "Any attributes associated with this function declaration.")

   (loc        vl-location-p
               "Where this declaration was found in the source code."))

  :long "<p>Functions are described in Section 10.4 of the standard.  An
example of a function is:</p>

@({
function [3:0] lower_bits;
  input [7:0] a;
  reg [1:0] lowest_pair;
  reg [1:0] next_lowest_pair;
  begin
    lowest_pair = a[1:0];
    next_lowest_pair = a[3:2];
    lower_bits = {next_lowest_pair, lowest_pair};
  end
endfunction
})

<p>Note that functions don't have any inout or output ports.  Instead, you
assign to a function's name to indicate its return value.</p>")

(deflist vl-fundecllist-p (x)
  (vl-fundecl-p x)
  :guard t
  :elementp-of-nil nil)

(defprojection vl-fundecllist->names (x)
  (vl-fundecl->name x)
  :guard (vl-fundecllist-p x)
  :nil-preservingp t
  :result-type string-listp)



(defaggregate vl-taskdecl
  :parents (modules)
  :short "Representation of a single Verilog task."
  :tag :vl-taskdecl
  :legiblep nil

  ((name       stringp
               :rule-classes :type-prescription
               "The name of this task.")

   (automaticp booleanp
               :rule-classes :type-prescription
               "Says whether the @('automatic') keyword was provided.  This
                keyword indicates that each invocation of the task has its own
                copy of its variables.  For instance, the task below had
                probably better be automatic if it there are going to be
                concurrent instances of it running, since otherwise @('temp')
                could be corrupted by the other task.")

   (ports      vl-taskportlist-p
               "The input, output, and inout ports for the task.")

   (decls      vl-blockitemlist-p
               "Any local declarations for the task, e.g., for the task below,
                the declaration of @('temp') would be found here.")

   (body       vl-stmt-p
               "The statement that gives the actions for this task, i.e., the
                entire @('begin/end') statement in the below task.")

   (atts       vl-atts-p
               "Any attributes associated with this task declaration.")

   (loc        vl-location-p
               "Where this task was found in the source code."))

  :long "<p>Tasks are described in Section 10.2 of the standard.  An example
of a task is:</p>

@({
task automatic dostuff;
  input [3:0] count;
  output inc;
  output onehot;
  output more;
  reg [2:0] temp;
  begin
    temp = count[0] + count[1] + count[2] + count[3];
    onehot = temp == 1;
    if (!onehot) $display(\"onehot is %b\", onehot);
    #10;
    inc = count + 1;
    more = count > prev_count;
  end
endtask
})

<p>Tasks are somewhat like <see topic='@(url vl-fundecl-p)'>functions</see>,
but they can have fewer restrictions, e.g., they can have multiple outputs, can
include delays, etc.</p>")

(deflist vl-taskdecllist-p (x)
  (vl-taskdecl-p x)
  :guard t
  :elementp-of-nil nil)

(defprojection vl-taskdecllist->names (x)
  (vl-taskdecl->name x)
  :guard (vl-taskdecllist-p x)
  :nil-preservingp t
  :result-type string-listp)



(defaggregate vl-module
  :parents (modules)
  :short "Representation of a single module."
  :tag :vl-module
  :legiblep nil

  ((name       stringp
               :rule-classes :type-prescription
               "The name of this module as a string.  The name is used to
                instantiate this module, so generally we require that modules
                in our list have unique names.  A module's name is initially
                set when it is parsed, but it may not remain fixed throughout
                simplification.  For instance, during @(see unparameterization)
                a module named @('adder') might become @('adder$size=12').")

   (params     "Any @('defparam') statements for this module.  BOZO these are
                bad form anyway, but eventually we should provide better
                support for them and proper structures.")

   (ports      vl-portlist-p
               "The module's ports list, i.e., @('a'), @('b'), and @('c') in
                @('module mod(a,b,c);').")

   (portdecls  vl-portdecllist-p
               "The input, output, and inout declarations for this module,
                e.g., @('input [3:0] a;').")

   (netdecls   vl-netdecllist-p
               "Wire declarations like @('wire [3:0] w;') and @('tri v;').
                Does not include registers and variables (integer, real,
                ...).")

   (vardecls   vl-vardecllist-p
               "Variable declarations like @('integer i;') and @('real
               foo;').")

   (regdecls   vl-regdecllist-p
               "Register declarations like @('reg [3:0] r;').")

   (eventdecls vl-eventdecllist-p
               "Event declarations like @('event foo ...')")

   (paramdecls vl-paramdecllist-p
               "The parameter declarations for this module, e.g., @('parameter
                width = 1;').")

   (fundecls   vl-fundecllist-p
               "Function declarations like @('function f ...').")

   (taskdecls  vl-taskdecllist-p
               "Task declarations, e.g., @('task foo ...').")

   (assigns    vl-assignlist-p
               "Top-level continuous assignments like @('assign lhs = rhs;').")

   (modinsts   vl-modinstlist-p
               "Instances of modules and user-defined primitives, e.g.,
                @('adder my_adder1 (...);').")

   (gateinsts  vl-gateinstlist-p
               "Instances of primitive gates, e.g., @('and (o, a, b);').")

   (alwayses   vl-alwayslist-p
               "Always blocks like @('always @(posedge clk) ...').")

   (initials   vl-initiallist-p
               "Initial blocks like @('initial begin ...').")

   (atts       vl-atts-p
               "Any attributes associated with this top-level module.")

   (minloc     vl-location-p
               "Where we found the @('module') keyword for this module, i.e.,
                the start of this module's source code.")

   (maxloc     vl-location-p
               "Where we found the @('endmodule') keyword for this module, i.e.,
                the end of this module's source code.")

   (origname   stringp
               :rule-classes :type-prescription
               "Original name of the module from parse time.  Unlike the
                module's @('name'), this is meant to remain fixed throughout
                all simplifications.  That is, while a module named @('adder')
                might be renamed to @('adder$size=12') during @(see
                unparameterization), its origname will always be @('adder').
                The @('origname') is only intended to be used for display
                purposes such as hyperlinking.")

   (warnings   vl-warninglist-p
               "A @(see warnings) accumulator that stores any problems we have
                with this module.  Warnings are semantically meaningful only in
                that any <i>fatal</i> warning indicates the module is invalid
                and should not be discarded.  The list of warnings may be
                extended by any transformation or well-formedness check.")

   (comments   vl-commentmap-p
               "A map from locations to source-code comments that occurred in
                this module.  We expect that comments are never consulted for
                any semantic meaning.  This field is mainly intended for
                displaying the transformed module with comments preserved,
                e.g., see @(see vl-ppc-module).")

   (esim       "This is meant to be @('nil') until @(see esim) conversion, at
                which point it becomes the E module corresponding to this
                VL module.")))

(deflist vl-modulelist-p (x)
  (vl-module-p x)
  :elementp-of-nil nil
  :parents (modules))

(defthm vl-module-identity
  ;; This is occasionally useful when we want to prove that some optimized
  ;; version of a transform, that doesn't re-cons the module, is equivalent to
  ;; the naive version that does.
  (implies (vl-module-p x)
           (equal (change-vl-module x)
                  x))
  :hints(("Goal"
          ;; I'm okay with this hint being hideous since this isn't really
          ;; something anyone should ever do.
          :in-theory (union-theories
                      (union-theories (current-theory :here)
                                      '(vl-module-p vl-module))
                      (b* (((std::agginfo agg)
                            (std::get-aggregate 'vl-module world)))
                          (std::da-accessor-names 'vl-module agg.fields))))))

(define vl-module->hands-offp ((x vl-module-p))
  :inline t
  :returns hands-offp
  :parents (vl-module-p)
  :short "Attribute that says a module should not be transformed."

  :long "<p>We use the ordinary <see topic='@(url vl-atts-p)'>attribute</see>
@('VL_HANDS_OFF') to say that a module should not be changed by @(see
transforms).</p>

<p>This is generally meant for use in VL @(see primitives).  The Verilog
definitions of these modules sometimes make use of fancy Verilog constructs.
Normally our transforms would try to remove these constructs, replacing them
with instances of primitives.  This can lead to funny sorts of problems if we
try to transform the primitives themselves.</p>

<p>For instance, consider the @(see *vl-1-bit-delay-1*) module.  This module
has a delayed assignment, @('assign #1 out = in').  If we hit this module with
the @(see delayredux) transform, we'll try to replace the delay with an
explicit instance of @('VL_1_BIT_DELAY_1').  But that's crazy: now the module
is trying to instantiate itself!</p>

<p>Similar issues can arise from trying to replace the @('always') statements
in a primitive flop/latch with instances of flop/latch primitives, etc.  So as
a general rule, we mark the primitives with @('VL_HANDS_OFF') and code our
transforms to not modules with this attribute.</p>"

  (consp (assoc-equal "VL_HANDS_OFF" (vl-module->atts x))))

(defprojection vl-modulelist->names (x)
  (vl-module->name x)
  :guard (vl-modulelist-p x)
  :result-type string-listp
  :nil-preservingp t
  :parents (vl-modulelist-p))


(defprojection vl-modulelist->paramdecls (x)
  (vl-module->paramdecls x)
  :guard (vl-modulelist-p x)
  :result-type vl-paramdecllist-list-p
  :nil-preservingp t
  :parents (vl-modulelist-p))

(defmapappend vl-modulelist->modinsts (x)
  (vl-module->modinsts x)
  :guard (vl-modulelist-p x)
  :transform-true-list-p nil
  :parents (vl-modulelist-p)
  :rest
  ((defthm vl-modinstlist-p-of-vl-modulelist->modinsts
     (implies (force (vl-modulelist-p x))
              (vl-modinstlist-p (vl-modulelist->modinsts x))))))

(defprojection vl-modulelist->esims (x)
  (vl-module->esim x)
  :guard (vl-modulelist-p x)
  :nil-preservingp t
  :parents (vl-modulelist-p))



(define vl-maybe-module-p (x)
  :inline t
  :parents (vl-expr-p)
  :short "Recognizer for an @(see vl-module-p) or @('nil')."
  (or (not x)
      (vl-module-p x))
  ///
  (defthm vl-maybe-module-p-when-vl-module-p
    (implies (vl-module-p x)
             (vl-maybe-module-p x)))

  (defthm vl-module-p-when-vl-maybe-module-p
    (implies (vl-maybe-module-p x)
             (equal (vl-module-p x)
                    (if x t nil))))

  (defthm type-when-vl-maybe-module-p
    (implies (vl-maybe-module-p x)
             (or (not x)
                 (consp x)))
    :rule-classes :compound-recognizer))
