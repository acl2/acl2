; VL Verilog Toolkit
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

(in-package "VL")
(include-book "util/bits")
(include-book "util/locations")
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (xdoc::set-default-parents expressions-and-datatypes))

(defxdoc new-expression-representation
  :short "Notes about the new expression representation in @(see vl), and how
and why it diverges from the @(see vl2014::expressions)."

  :long "<p>In earlier versions of VL such as @(see vl2014), we used a fairly
<see topic='@(url vl2014::expressions)'>simple, AST-like representation</see>.
This representation had some nice features: it kept mutual recursion to a
minimum and made it easy to recur through expressions.  However, it also had
some severe weaknesses.</p>

<p>The most significant of these was the lack of type safety.  We often
expected expressions to have certain shapes.  For instance, we typically
expected that any hierarchical identifier, like @('foo.bar[2].baz'), would
consist of special \"hid pieces\" joined together by certain \"hid dot\" and
\"hid array index\" operators with a certain recursive structure.  But the
expression representation did not enforce this, so nothing prevented you from
creating nonsensical expressions like @('foo.(3 + 4).baz').</p>

<p>The ability to create degenerate/nonsense expressions is not necessarily so
bad&mdash;just don't create nonsense expressions and what's the a problem?  But
the possibility of these degenerate expressions might exist turned out to have
a pervasive impact when writing code to process expressions: VL's many
transforms and utilities always had to defend against such malformed
expressions.</p>

<p>This defense was generally carried out by adding guards or explicit run-time
tests that expressions were sensible.  The result was copious error handling
code, difficult and tedious proofs about well-formedness (e.g., see @(see
vl2014::welltyped)), and additional interfacing layers such as the @(see
vl2014::hid-tools) to hide the problem.  These layers became ever more complex
as we implemented more of SystemVerilog, e.g., scope expressions and datatype
indexing greatly complicated the handling of hierarchical identifiers.</p>

<p>Reflecting on these problems, and considering our improving ability to
handle @(see mutual-recursion) via macro libraries such as @(see fty::fty) and
@(see defines), we decided to overhaul the expression representation and
replace it with a much more strongly typed, mutually recursive approach.</p>

<p>Our new expression format is much more complex than before.  However, it
also intrinsically rules out many expressions that were previously allowed,
which helps to avoid needing error checking code when processing expressions,
and generally makes it easier to write safe expression-processing code.</p>")

(define vl-bitlist-nonempty-fix ((x vl-bitlist-p))
  :guard (consp x)
  :parents (vl-weirdint)
  :short "Fixing function for non-empty @(see vl-bitlist)s."
  :long "<p>This is just a technical helper function that supports the @(see
         fty::fty-discipline).  It is used to ensure that the @('bits') of a
         @(see vl-weirdint) are always nonempty.</p>"
  :returns (x-fix vl-bitlist-p)
  :inline t
  (mbe :logic
       (if (atom x)
           (list :vl-0val)
         (vl-bitlist-fix x))
       :exec x)
  ///
  (defret consp-of-vl-bitlist-nonempty-fix
    (consp x-fix)
    :rule-classes :type-prescription)

  (defret vl-bitlist-nonempty-fix-idempotent
    (implies (consp x)
             (equal x-fix (vl-bitlist-fix x)))))


(defxdoc vl-exprsign
  :parents (vl-expr)
  :short "An indication of an integer expression's signedness (signed or
          unsigned)."

  :long "<p>On the surface there is not much to this: a literal, wire, or some
         other kind of expression might be regarded as either signed or
         unsigned.  These notes about the signedness of things occur in the
         representation of certain expressions like @(see vl-constint) and
         @(see vl-weirdint) literals.  There is some special handling for the
         signedness of ports; see @(see portdecl-sign), but signedness is most
         critically used in @(see vl-expr-typedecide).</p>

         <p>Note about the word ``<b>type</b>.''  The Verilog-2005 and
         SystemVerilog-2012 standards sometimes use the word ``type'' to refer
         to the signedness of things.  Back in Verilog-2005 there were no fancy
         types like structs and unions and the ``type'' of an expression
         generally meant whether it was a real number, a signed integer, an
         unsigned integer, and maybe other vaguely specified things.</p>

         <p>With SystemVerilog-2012 adding much richer variable datatypes (see
         @(see vl-datatype)), it gets very confusing to use the word ``type''
         in place of signedness.  However, this is still done occasionally.
         Most notably, it happens in SystemVerilog-2012 Section 11.8.1, which
         is adapted from Verilog-2005's Section 5.5.1.  This section explains
         how to compute the ``type'' of an expression, but in this context
         ``type'' still means signedness and has little to do with any kind of
         fancy SystemVerilog @(see vl-datatype)-like types.</p>

         <p>The signedness of wires and variables in VL is now generally part
         of their @(see vl-datatype).  Historically the way to query a type for
         its signedness was to use @('vl-datatype-signedness').  More recently,
         in order to add at least some support for non-integer expressions like
         @('real') and @('shortreal')s, the signedness of a datatype has been
         folded into the more general notion of its @('arithclass').  See in
         particular @(see vl-datatype-arithclass).</p>")


(defenum vl-exprsign-p
  (:vl-signed :vl-unsigned)
  :short "Recognizer for @(see vl-exprsign) symbols."
  :parents (vl-exprsign))

(defoption vl-maybe-exprsign
  vl-exprsign-p
  :parents (vl-exprsign)
  ///
  (defthm type-when-vl-maybe-exprsign-p
    (implies (vl-maybe-exprsign-p x)
             (and (symbolp x)
                  (not (equal x t))))
    :hints(("Goal" :in-theory (enable vl-maybe-exprsign-p)))
    :rule-classes :compound-recognizer))


(deftagsum vl-value
  :parents (vl-literal)
  :short "The actual value of a @(see vl-literal) expression, e.g., @('42'),
          @('3'bxxx'), @(''1'), @('\"foo\"'), @('3.14'), @('45.12ns'), etc."

  (:vl-constint
   :short "Representation for constant integer literals with no X or Z bits,
           e.g., @('42'), @('5'b1'), etc."
   :hons t
   :layout :tree
   :base-name vl-constint
   ((origwidth  posp
                :rule-classes :type-prescription
                "Subtle; generally should <b>not be used</b>; see below.")
    (value      natp
                :rule-classes :type-prescription
                "The most important part of a constant integer.  Even
                immediately upon parsing the value has already been determined
                and is available to you as an ordinary natural number."
                :reqfix (acl2::loghead (pos-fix origwidth) value))
    (origsign   vl-exprsign-p
                "Subtle; generally should <b>not be used</b>; see below.")
    (wasunsized booleanp
                :rule-classes :type-prescription
                "Set to @('t') by the parser for unsized constants like @('5')
                 and @(''b0101'), but not for sized ones like @('4'b0101')."))
   :require (unsigned-byte-p origwidth value)

   :long "<h3>Detailed Explanation</h3>

          <p>Constant integers are produced from source code constructs like
          @('5'), @('4'b0010'), and @('3'h0').</p>

          <p>Note that the value of a constant integer is never negative.  In
          Verilog there are no negative literals; instead, an expression like
          @('-5') is basically parsed the same as @('-(5)'), so the negative
          sign is not part of the literal.  See Section 3.5.1 of the
          Verilog-2005 standard.</p>

          <p>The @('origwidth') and @('origsign') fields are subtle and you
          usually <b>should not</b> be looking at the @('origwidth') and
          @('origsign') of an expression unless you have really studied how
          sizing works in and you really know what you are doing.</p>

          <p>These fields indicate the <i>original</i> width and signedness of
          the literal as specified in the source code.  For instance, if the
          source code contains @('8'sd 65'), then we will get a value whose
          @('origwidth') is 8 and whose @('origsign') is @(':vl-signed.')
          <b>However</b>, in general, the process for sizing Verilog
          expressions can effectively ``change'' the widths and types of the
          operands within that expression.  For instance, if @('a') and @('b')
          are unsigned 10-bit wires and we have:</p>

          @({
               assign a = b + 3'sb1;
          })

          <p>Then even though @('3'sb1') looks like a signed 3-bit integer, the
          sizing process will convert it into a 10-bit unsigned number!  The
          takeaway: you can't really rely on the original size and signedness
          to tell you the real story, so unless you're implementing the sizing
          algorithm you should probably avoid them.</p>

          <p>We insist that @('0 <= value <= 2^origwidth') for every constant
          integer.  If our @(see lexer) encounters something ill-formed like
          @('3'b 1111'), it emits a warning and truncates the value to the
          specified width as required by Section 3.5.1 (page 10) of the
          Verilog-2005 standard and Section 5.7.1 (page 37) of the
          SystemVerilog standard.</p>

          <p>Note that in Verilog, unsized integer constants like @('5') or
          @(''b101') have an implementation-dependent size of at least 32 bits.
          Early versions of VL tried to treat such numbers in an abstract way,
          saying they had \"integer size\".  But we eventually decided that
          this was too error-prone and we now instead act like a 32-bit
          implementation even at the level of our lexer.  This conveniently
          makes the width of a constant integer just a positive number.</p>

          <p>There is some risk to this.  Certain expressions may produce
          different results on 32-bit versus, say, 64-bit implementations.
          Because of this, we added the @('wasunsized') field so that we might,
          some day, statically check for problematic uses of unsized
          constants.</p>

          <p>All constints are automatically created with @(see hons).  This is
          probably pretty trivial, but it seems nice.  For instance, the
          constant integers from 0-32 are probably used thousands of times
          throughout a design for bit-selects and wire ranges, so sharing their
          memory may be useful.</p>")


  (:vl-weirdint
   :short "Representation for constant integer literals with any X or Z bits,
           e.g., @('4'b11xx')."
   :hons t
   :layout :tree
   :base-name vl-weirdint
   ((bits        vl-bitlist-p
                 "An MSB-first list of the four-valued Verilog bits making up
                  this constant's value; see @(see vl-bit-p)."
                 :reqfix (vl-bitlist-nonempty-fix bits))
    (origsign     vl-exprsign-p
                  "Subtle; generally should <b>not be used</b>; see below.")
    (wasunsized  booleanp
                 :rule-classes :type-prescription
                 "Did this constant have an explicit size?"))
   :require (consp bits)
   :long "<h3>Detailed Explanation</h3>

          <p>Weird integers are produced by source code constructs like
          @('1'bz'), @('3'b0X1'), and so on.</p>

          <p>Weirdints are mostly like @(see vl-constint)s except that instead
          of having a natural number @('value') they have @('bits'), a list of
          four-valued @(see vl-bit)s, which are always represented in MSB-first
          order.</p>

          <p>The @('origsign') and @('wasunsized') fields are analogous to
          those from a @(see vl-constint); see the discussion there for
          details.</p>

          <p>Unlike a constint, a weirdint has no @('origwidth').  Instead, its
          original width is implicitly just the length of its bits.  When our
          @(see lexer) encounters a weirdint like @('5'b1x'), it automatically
          extends it to the desired width; see for instance @(see
          vl-correct-bitlist).  Note that, as with constints, you usually
          <b>should not</b> be looking at this length or at the @('origsign')
          field, because these original values are not necessarily the correct
          post-sizing sizes and signedness.</p>

          <p>Like constinsts, all weirdints are automatically constructed with
          @(see hons).  This may not be worthwhile since there are probably
          usually not too many weirdints, but by the same reasoning it
          shouldn't be too harmful.</p>")


  (:vl-extint
   :short "Representation for unbased, unsized integer literals, viz. @(''0'),
           @(''1'), @(''x'), and @(''z')."
   :hons t
   :layout :tree
   :base-name vl-extint
   ((value vl-bit-p "The kind of extended integer this is."))
   :long "<p>We call SystemVerilog's fancy integer literals like @(''1')
          <i>extension integers</i> and represent them with just their @(see
          vl-bit) value.  Since there are only four distinct extension
          integers, we always create them with @(see hons).</p>")


  (:vl-real
   :short "Representation of real (floating point) literals like @('3.41e+12')."
   :layout :tree
   :base-name vl-real
   ((value   stringp
             :rule-classes :type-prescription
             "The actual characters found in the source code, i.e., it might be
              a string such as @('\"3.41e+12\"')."))
   :long "<p>We have almost no support for working with real numbers.  You
          should probably not rely on our current representation, since we will
          almost certainly want to change it as soon as we want to do anything
          with real numbers.</p>")


  (:vl-time
   :short "Representation of time amounts like @('45.12ns')."
   :base-name vl-time
   :hons t
   :layout :tree
   ((quantity stringp
              :rule-classes :type-prescription
              "An ACL2 string with the amount.  In practice, the amount should
               match either @('unsigned_number') or @('fixed_point_number'),
               e.g., @('\"3\"') or @('\"45.617\"').  We don't try to process
               this further because (1) we don't expect it to matter for much,
               and (2) ACL2 doesn't really support fixed point numbers.")
    (units    vl-timeunit-p
              "The kind of time unit this is, e.g., seconds, milliseconds,
               microseconds, ..."))
   :long "<p>We barely support this.  You should probably not rely on our
          current representation, since we will almost certainly want to change
          it as soon as we do anything with time units.</p>")

  (:vl-string
   :short "Representation for string literals like @('\"hello\"')."
   :base-name vl-string
   :layout :tree
   ((value stringp
           :rule-classes :type-prescription
           "An ordinary ACL2 string where, e.g., special sequences like
            @('\\n') and @('\\t') have been resolved into real newline and tab
            characters, etc."))))

(fty::deflist vl-valuelist
  :elt-type vl-value
  :elementp-of-nil nil
  :parents (vl-value))



(defenum vl-randomqualifier-p
  (nil
   :vl-rand
   :vl-randc)
  :parents (vl-structmember)
  :short "Random qualifiers that can be put on struct or union members.")


(defenum vl-coretypename-p
  (;; integer vector types, i put these first since they're common
   :vl-logic
   :vl-reg
   :vl-bit
   ;; integer atom types:
   :vl-byte
   :vl-shortint
   :vl-int
   :vl-longint
   :vl-integer
   :vl-time
   ;; non integer types:
   :vl-shortreal
   :vl-real
   :vl-realtime
   ;; misc core datatypes
   :vl-string
   :vl-chandle
   :vl-event
   ;; it's convenient to include void here even though it's not part
   ;; of the grammar for data_type
   :vl-void
   ;; it's convenient to include untyped, sequence, and property here,
   ;; even though they aren't part of the grammar for data_type, to
   ;; help simplify the representation of property/sequence ports.
   :vl-sequence
   :vl-property
   :vl-untyped
   )
  :parents (vl-coretype)
  :short "Basic kinds of datatypes."
  :long "<p>Our <i>core types</i> basically correspond to the following small
         subset of the valid @('data_type')s:</p>

         @({
             data_type_or_void ::= data_type | 'void'
             data_type ::=
                integer_vector_type [signing] { packed_dimension }
              | integer_atom_type [signing]
              | non_integer_type
              | 'string'
              | 'chandle'
              | 'event'
              | <non core types>
         })

         <p>We include certain additional keywords here to represent @('void'),
         and also for @('property'), @('sequence'), and @('untyped') (which can
         occur in the property/sequence ports for SystemVerilog assertions).
         This is mostly a convenience that allows us to unify the
         representation of types in other places throughout the parse
         tree.</p>")


(defxdoc vl-scopename
  :parents (vl-scopeexpr-colon)
  :short "Leading names that can be used in a scope operator (::), viz.
          @('local'), @('unit'), or a user-defined name.")

(define vl-scopename-p (x)
  :parents (vl-scopename)
  :short "Recognizer for scope names."
  :returns bool
  (or (eq x :vl-local)
      (eq x :vl-$unit)
      (stringp x))
  ///
  (defthm vl-scopename-p-when-stringp
    (implies (stringp x)
             (vl-scopename-p x))
    :hints(("Goal" :in-theory (enable vl-scopename-p)))))

(define vl-scopename-fix ((x vl-scopename-p))
  :parents (vl-scopename)
  :short "Fixing function for @(see vl-scopename)s."
  :returns (name vl-scopename-p)
  :inline t
  (mbe :logic (if (vl-scopename-p x)
                  x
                :vl-local)
       :exec x)
  ///
  (defthm vl-scopename-fix-when-vl-scopename-p
    (implies (vl-scopename-p x)
             (equal (vl-scopename-fix x) x))))

(defsection vl-scopename-equiv
  :parents (vl-scopename)
  :short "Equivalence relation for @(see vl-scopename)s."
  (deffixtype vl-scopename
    :pred vl-scopename-p
    :fix vl-scopename-fix
    :equiv vl-scopename-equiv
    :define t
    :forward t))

(fty::deflist vl-scopenamelist
  :elt-type vl-scopename
  :elementp-of-nil nil
  :parents (vl-scopename)
  ///
  (defthm vl-scopenamelist-p-when-string-listp
    (implies (string-listp x)
             (vl-scopenamelist-p x))
    :hints(("Goal" :in-theory (enable vl-scopenamelist-p)))))


(defsection vl-hidname
  :parents (vl-index)
  :short "Leading names that can be used in a @(see vl-hidindex): @('$root') or
          a user-defined name.")

(define vl-hidname-p (x)
  :parents (vl-hidname)
  :short "Recognizer for hid names."
  :returns bool
  (or (eq x :vl-$root)
      (stringp x)))

(define vl-hidname-fix ((x vl-hidname-p))
  :parents (vl-hidname)
  :returns (name vl-hidname-p)
  :short "Fixing function for @(see vl-hidname)s."
  :inline t
  (mbe :logic (if (vl-hidname-p x)
                  x
                :vl-$root)
       :exec x)
  ///
  (defthm vl-hidname-fix-when-vl-hidname-p
    (implies (vl-hidname-p x)
             (equal (vl-hidname-fix x) x))))

(defsection vl-hidname-equiv
  :parents (vl-hidname)
  :short "Equivalence relation for @(see vl-hidname)s."
  (deffixtype vl-hidname
    :pred vl-hidname-p
    :fix vl-hidname-fix
    :equiv vl-hidname-equiv
    :define t
    :forward t))

(fty::deflist vl-hidnamelist
  :elt-type vl-hidname
  :elementp-of-nil nil
  :parents (vl-hidname))


(defval *vl-unary-ops*
  :parents (vl-unary)
  :short "Table of unary operator internal symbols and their source code text."
  '((:vl-unary-plus     . "+")
    (:vl-unary-minus    . "-")
    (:vl-unary-lognot   . "!")
    (:vl-unary-bitnot   . "~")
    (:vl-unary-bitand   . "&")
    (:vl-unary-nand     . "~&")
    (:vl-unary-bitor    . "|")
    (:vl-unary-nor      . "~|")
    (:vl-unary-xor      . "^")
    (:vl-unary-xnor     . "~^")
    (:vl-unary-preinc   . "++")
    (:vl-unary-predec   . "--")
    (:vl-unary-postinc  . "++")
    (:vl-unary-postdec  . "--")))

(make-event
 `(defenum vl-unaryop-p
    ,(strip-cars *vl-unary-ops*)
    :parents (vl-unary)
    :short "Recognizer for basic unary operators."))

(define vl-unaryop-string ((x vl-unaryop-p))
  :parents (vl-unary)
  :short "Get the source code text for a basic unary operator."
  :returns (str stringp :rule-classes :type-prescription)
  :prepwork ((local (defthm vl-unaryop-fix-forward
                      (vl-unaryop-p (vl-unaryop-fix x))
                      :rule-classes
                      ((:forward-chaining :trigger-terms ((vl-unaryop-fix x)))))))
  (cdr (assoc (vl-unaryop-fix x) *vl-unary-ops*)))


(defval *vl-binary-ops*
  :parents (vl-binary)
  :short "Table of binary operator internal symbols and their source code text."
  '((:vl-binary-plus        . "+")
    (:vl-binary-minus       . "-")
    (:vl-binary-times       . "*")
    (:vl-binary-div         . "/")
    (:vl-binary-rem         . "%")
    (:vl-binary-eq          . "==")
    (:vl-binary-neq         . "!=")
    (:vl-binary-ceq         . "===")
    (:vl-binary-cne         . "!==")
    (:vl-binary-wildeq      . "==?")
    (:vl-binary-wildneq     . "!=?")
    (:vl-binary-logand      . "&&")
    (:vl-binary-logor       . "||")
    (:vl-binary-power       . "**")
    (:vl-binary-lt          . "<")
    (:vl-binary-lte         . "<=")
    (:vl-binary-gt          . ">")
    (:vl-binary-gte         . ">=")
    (:vl-binary-bitand      . "&")
    (:vl-binary-bitor       . "|")
    (:vl-binary-xor         . "^")
    (:vl-binary-xnor        . "~^")
    (:vl-binary-shr         . ">>")
    (:vl-binary-shl         . "<<")
    (:vl-binary-ashr        . ">>>")
    (:vl-binary-ashl        . "<<<")
    (:vl-binary-assign      . "=")
    (:vl-binary-plusassign  . "+=")
    (:vl-binary-minusassign . "-=")
    (:vl-binary-timesassign . "*=")
    (:vl-binary-divassign   . "/=")
    (:vl-binary-remassign   . "%=")
    (:vl-binary-andassign   . "&=")
    (:vl-binary-orassign    . "|=")
    (:vl-binary-xorassign   . "^=")
    (:vl-binary-shlassign   . "<<=")
    (:vl-binary-shrassign   . ">>=")
    (:vl-binary-ashlassign  . "<<<=")
    (:vl-binary-ashrassign  . ">>>=")
    (:vl-implies            . "->")
    (:vl-equiv              . "<->")))

(make-event
 `(defenum vl-binaryop-p
    ,(strip-cars *vl-binary-ops*)
    :parents (vl-binary)
    :short "Recognizer for basic binary operators."))

(define vl-binaryop-string ((x vl-binaryop-p))
  :parents (vl-binary)
  :short "Get the source code text for a basic binary operator."
  :returns (str stringp :rule-classes :type-prescription)
  :prepwork ((local (defthm vl-binaryop-fix-forward
                      (vl-binaryop-p (vl-binaryop-fix x))
                      :rule-classes
                      ((:forward-chaining :trigger-terms ((vl-binaryop-fix x)))))))
  (cdr (assoc (vl-binaryop-fix x) *vl-binary-ops*)))

(defenum vl-specialkey-p
  (:vl-null
   ;; :vl-this
   ;; :vl-super
   ;; :vl-local
   ;; :vl-default
   :vl-$
   ;; :vl-$root
   ;; :vl-$unit
   :vl-emptyqueue
   ;; To make any SystemVerilog-2012 delay_value just an expression, it's
   ;; convenient to add 1step here.
   :vl-1step
   )
  :parents (vl-special))

(defenum vl-leftright-p
  (:left :right)
  :parents (vl-stream)
  :short "The direction for streaming operators: @(':left') for @('<<') or
          @(':right') for @('>>').")


(defenum vl-evatomtype-p
  (:vl-noedge
   :vl-edge
   :vl-posedge
   :vl-negedge)
  :parents (vl-evatom-p)
  :short "Type of an item in an event control list."
  :long "<p>Any particular atom in the event control list might have a
@('posedge'), @('negedge'), @('edge'), or have no edge specifier at all, e.g.,
for plain atoms like @('a') and @('b') in @('always @(a or b)').</p>")


(local (std::set-returnspec-mrec-default-hints nil))

(local (in-theory (disable (:t acl2::nil-fn)
                           default-car
                           default-cdr
                           default-+-2
                           default-+-1
                           o< o-finp
                           acl2::nfix-when-not-natp
                           (:t acl2::acl2-count-of-consp-positive))))

(local (xdoc::set-default-parents))


(local (defthm tag-of-cons
         (equal (tag (cons x y)) x)
         :hints(("Goal" :in-theory (enable tag)))))

(deftypes expressions-and-datatypes
  :parents (syntax)
  :short "Representation of expressions, datatypes, and other related,
          mutually recursive concepts."

  :long "<p>SystemVerilog has a very rich expression language.  For
         instance:</p>

         <ul>

         <li>It has many kinds of literals, including integer literals that can
         be sized and unsized, ``weird'' integers like @('4'10xz'), infinitely
         extended integers like @(''0'), reals, times, strings, etc.  See @(see
         vl-literal).</li>

         <li>It has a rich operand syntax that allows for scoping, indexing
         into the module hierarchy and structures, and for many kinds of
         bit/range selects into wires, arrays, etc.  See @(see vl-index).</li>

         <li>It has many familiar C-like operators (@('+'), @('&'), etc.) and
         numerous extended C-like operators (@('==='), @('!=?'), @('>>>'),
         etc.)  See @(see vl-unary), @(see vl-binary), and @(see vl-qmark).</li>

         <li>It has certain casting and function call operators that allow for
         the use of <b>datatypes directly in expressions</b>, which makes
         expressions and datatypes <b>mutually recursive</b> concepts.</li>

         <li>It has several esoteric operators like @('inside') and the
         streaming operators, which have their own sub-syntax of sorts.</li>

         <li>It has nested attributes like <tt>(* foo, bar = 5 *)</tt> that can
         be attached to almost any expression as annotations for tools.  See
         @(see vl-atts).</li>

         </ul>

         <p>These expressions occur pretty much everywhere throughout a
         SystemVerilog design&mdash;ports, parameters, assignments, instances,
         statements, you name it.  This complexity and frequency of usage makes
         a good representation of expressions especially important.</p>

         <p>A major differences between @(see vl2014) and @(see vl) is that VL
         uses a new, more mutually recursive, and more strongly typed
         expression representation.  See @(see new-expression-representation)
         for some discussion about the motivation for this change.</p>

         <p>Note that there are many useful functions for working with
         expressions in @(see mlib).  See most especially @(see expr-tools)
         which contains many basic functions.</p>"

  :post-pred-events
  ((local (defthm impossible-cars-of-vl-expr
            (implies (vl-expr-p x)
                     (and (not (equal (car x) :vl-range))
                          (not (equal (car x) :vl-plusminus))
                          (not (equal (car x) :none))))
            :hints (("goal" :expand ((vl-expr-p x))))))
   (local (defthm car-is-vl-range
            (implies (vl-range-p x)
                     (equal (car x) :vl-range))
            :hints (("goal" :expand ((vl-range-p x))))
            :rule-classes :forward-chaining))
   (local (defthm car-is-vl-plusminus
            (implies (vl-plusminus-p x)
                     (equal (car x) :vl-plusminus))
            :hints (("goal" :expand ((vl-plusminus-p x))))
            :rule-classes :forward-chaining))
   (local (defthm hidexpr-car-not-colon
            (implies (vl-hidexpr-p x)
                     (not (equal (car x) :colon)))
            :hints(("Goal" :in-theory (enable vl-hidexpr-p
                                              vl-hidindex-p))))))


; -----------------------------------------------------------------------------
;
;                         ** Top-Level Expressions **
;
; -----------------------------------------------------------------------------

  (deftagsum vl-expr
    :short "Representation of a single SystemVerilog expression."
    :long "<p>For more general background, see @(see expressions-and-datatypes)
           and @(see new-expression-representation).  Also note that there are
           many functions for working with expressions throughout @(see mlib);
           see especially @(see expr-tools).</p>"
    :measure (two-nats-measure (acl2-count x) 50)
    :base-case-override :vl-literal
    :layout :tree

    (:vl-literal
     :base-name vl-literal
     :short "A literal value of any kind, such as integer constants, string
             literals, time literals, real numbers, etc."
     ((val  vl-value
            "The guts of the literal.  This explains what kind of literal it
             is, its value, and has other related information.")
      (atts vl-atts-p
            "Any attributes associated with this literal.  These are generally
             @('nil') upon parsing since the Verilog or SystemVerilog grammars
             don't really provide anywhere for <tt>(* foo = bar, baz *)</tt>
             style attributes to be attached to literals.  However, we found
             that it was convenient for every kind of expression to support
             attributes, so we include them for internal use.")))

    (:vl-index
     :base-name vl-index
     :short "A reference to some part of something that is somewhere in the
             design.  Could be a simple wire name like @('foo'), or something
             much fancier with scoping, hierarchy, indexing, and part-selects
             like @('ape::bat::cat.dog[3][2][1].elf[6][5][10:0]')."
     ((scope   vl-scopeexpr
               "Captures the scoping that leads to some object in the
                design. This captures the @('ape::bat::cat.dog[3][2][1].elf')
                part of the example above.")
      (indices vl-exprlist-p
               "Captures any subsequent indexing once we get to the thing
                pointed to by @('scope').  This captures the @('[6][5]') part
                of the example above.")
      (part    vl-partselect-p
               "Captures any subsequent part-selection once we get past all of
                the indexing.  This captures the @('[10:0]') part of the
                example above.")
      (atts    vl-atts-p
               "Any associated attributes.  BOZO where would you put such
                attributes?"))
     :long "<p>SystemVerilog provides a very rich syntax for referring to things
           in different scopes and throughout the module hierarchy.  Any such
           reference&mdash;whether it is a very simple identifier like @('foo')
           or a very complex scoped, hierarchical, indexed, mess of
           indirection&mdash;is ultimately represented as a single
           @('vl-index') expression.</p>")

    (:vl-unary
     :base-name vl-unary
     :short "A simple unary operator applied to some argument, like @('&a') or @('-b')."
     ((op     vl-unaryop-p "The operator being applied.")
      (arg    vl-expr-p    "The argument to the operator.")
      (atts   vl-atts-p    "Any <tt>(* foo = bar, baz *)</tt> style attributes.")))

    (:vl-binary
     :base-name vl-binary
     :short "A simple binary operator applied to some arguments, like @('a +
             b') or @('a & b')."
     ((op     vl-binaryop-p "The operator being applied.")
      (left   vl-expr-p     "The left-hand side argument, e.g., @('a') in @('a + b').")
      (right  vl-expr-p     "The right-hand side argument, e.g., @('b') in @('a + b').")
      (atts   vl-atts-p     "Any <tt>(* foo = bar, baz *)</tt> style attributes.")))

    (:vl-qmark
     :base-name vl-qmark
     :short "A ternary/conditional operator, e.g., @('a ? b : c')."
     ((test  vl-expr-p "The test expression, e.g., @('a').")
      (then  vl-expr-p "The true-branch expression, e.g., @('b').")
      (else  vl-expr-p "The else-branch expression, e.g., @('c').")
      (atts  vl-atts-p "Any <tt>(* foo = bar, baz *)</tt> style attributes.")))

    (:vl-concat
     :base-name vl-concat
     :short "A basic concatenation expression, e.g., @('{a, b, c}')."
     ((parts vl-exprlist-p "The expressions being concatenated together, e.g., the
                            expressions for @('a'), @('b'), and @('c'), in order.")
      (atts  vl-atts-p     "Any <tt>(* foo = bar, baz *)</tt> style attributes."))
     :long "<p>BOZO: Some day, investigate whether we can require the
            @('parts') to be non-empty.</p>")

    (:vl-multiconcat
     :base-name vl-multiconcat
     :short "A multiple concatenation (a.k.a. replication) expression, e.g., @('{4{a,b,c}}')."
     ((reps  vl-expr-p     "The replication amount, e.g., @('4').")
      (parts vl-exprlist-p "The expressions being concatenated together, e.g, the
                            expressions for @('a'), @('b'), and @('c'), in order.")
      (atts  vl-atts-p     "Any <tt>(* foo = bar, baz *)</tt> style attributes."))
     :long "<p>BOZO: Some day, investigate whether we can require the
            @('parts') to be non-empty.</p>")

    (:vl-mintypmax
     :base-name vl-mintypmax
     :short "A minimum/typical/maximum delay operator, e.g., @('3 : 4 : 5')."
     ((min   vl-expr-p "The minimum delay, e.g., @('a').")
      (typ   vl-expr-p "The typical delay, e.g., @('b').")
      (max   vl-expr-p "The maximum delay, e.g., @('c').")
      (atts  vl-atts-p "Any <tt>(* foo = bar, baz *)</tt> style attributes.")))

    (:vl-call
     :base-name vl-call
     :short "A call of a function or a system function, e.g., @('myencode(foo,
             3)') or @('$bits(foo_t)')."
     :long "<p>SystemVerilog allows named arguments and a combination of named
and ordered arguments.  In general, a function call can have some
unnamed (plain) arguments followed by some named arguments.</p>"
     ((name    vl-scopeexpr-p
               "The function being called.  Typically this is just the function
                name, but in general it is possible to call functions from
                other scopes and other places in the hierarchy, say
                @('foo::top.bar.myencode(baz, 3)'), so to be sufficiently
                general we represent this as a @(see vl-scopeexpr).")
      (plainargs vl-maybe-exprlist-p
                 "The unnamed arguments to the function, in order.")
      (namedargs vl-call-namedargs-p
                 "The named arguments to the function.")
      (typearg vl-maybe-datatype-p
               "Most function calls just take expressions as arguments, in
                which case @('typearg') will be @('nil').  However, certain
                system functions can take a datatype argument.  For instance,
                you can write @('$bits(struct { ...})').  In such cases, we put
                that datatype here.")
      (systemp booleanp :rule-classes :type-prescription
               "Indicates that this is a system function like @('$bits') or
                @('$display') instead of a user-defined function like
                @('myencode').")
      (atts    vl-atts-p
               "Any <tt>(* foo = bar, baz *)</tt> style attributes.")))

    (:vl-stream
     :base-name vl-stream
     :short "A streaming concatenation (pack or unpack) operation, e.g.,
             @('{<< 16 {a,b,c}}')."
     ((dir   vl-leftright-p
             "The kind of stream operator: @(':left') for @('<<') or
              @(':right') for @('>>').")
      (size  vl-slicesize-p
             "The slice size or an indication that there is no slice size.
              For instance, the @('16') in @('{<< 16 {a,b,c}}').")
      (parts vl-streamexprlist-p
             "The @('stream_expression')s that make up the @('stream_concatenation'),
              i.e., @('a'), @('b'), and @('c') for @('{<< 16 {a,b,c}}').  These
              aren't just ordinary expressions since they can have @('with')
              clauses.")
      (atts  vl-atts-p
             "Any <tt>(* foo = bar, baz *)</tt> style attributes.")))

    (:vl-cast
     :base-name vl-cast
     :short "A casting expression, e.g., @('int'(2.0 * 3.0)')."
     ((to      vl-casttype-p "The new type/size/signedness/constness to cast the
                              argument to, e.g., @('int') above.")
      (expr    vl-expr-p     "The expression being cast to something else, e.g.,
                              @('2.0 * 3.0') above.")
      (atts    vl-atts-p     "Any <tt>(* foo = bar, baz *)</tt> style attributes.")))

    (:vl-inside
     :base-name vl-inside
     :short "A set membership @('inside') operator, e.g., @('a inside { 5, [16:23] }')."
     ((elem   vl-expr-p            "The element to test, e.g., @('a') above.")
      (set    vl-valuerangelist-p  "The values and ranges making up the set, e.g.,
                                    @('5') and @('[16:23]').")
      (atts   vl-atts-p            "Any <tt>(* foo = bar, baz *)</tt> style attributes.")))

    (:vl-tagged
     :base-name vl-tagged
     :short "A tagged union expression, e.g., @('tagged Some (12+34)') or @('tagged None')."
     ((tag     stringp :rule-classes :type-prescription
               "The tag name, e.g., @('Some') or @('None') above.")
      (expr    vl-maybe-expr-p
               "The expression being tagged.")
      (atts    vl-atts-p
               "Any <tt>(* foo = bar, baz *)</tt> style attributes.")))

    (:vl-pattern
     :base-name vl-pattern
     :short "A (possibly typed) assignment pattern expression, for instance,
             @(''{a:1, b:2}') or @('foo_t'{head+1, tail-1}')."
     ((pat     vl-assignpat-p
               "The inner part of the pattern, i.e., everything but the type.")
      (pattype vl-maybe-datatype-p
               "The type for this assignment pattern, if applicable.  For
                instance, @('foo_t') in the example above.")
      (atts    vl-atts-p
               "Any <tt>(* foo = bar, baz *)</tt> style attributes."))

     :long "<p>This essentially corresponds to the SystemVerilog-2012 grammar
            rule for @('assignment_pattern_expression'):</p>

            @({
                assignment_pattern_expression ::=
                  [assignment_pattern_expression_type] assignment_pattern
            })")

    (:vl-special
     :base-name vl-special
     :short "Representation of a few special things like @('$'), @('null'), etc."
     ((key  vl-specialkey-p)
      (atts vl-atts-p
            "Any attribute associated with this expression.  As with literals,
             these attributes are not accessible in the Verilog or
             SystemVerilog grammars.  However, it is generally convenient to be
             able to associate attributes with any expression, so we include an
             attributes field in our internal representation.")))

    (:vl-eventexpr
     :base-name vl-eventexpr
     :short "Representation of an event expression, e.g., @('@(posedge foo)')."
     :long "<p>This is useful for, e.g., @('$past') calls like:</p>
            @({
                  $past(a,,,@(posedge clock))
            })"
     ((atoms vl-evatomlist)
      (atts  vl-atts-p)))

    )

  (fty::deflist vl-exprlist
    :measure (two-nats-measure (acl2-count x) 10)
    :elt-type vl-expr
    :elementp-of-nil nil
    ;; true-listp to get nice update identities like
    ;; (vl-expr-update-subexprs x (vl-expr->subexprs x)) = (vl-expr-fix x)
    :true-listp t
    :parents (vl-expr))

  (defoption vl-maybe-expr vl-expr
    :measure (two-nats-measure (acl2-count x) 100)
    :parents (vl-expr))

  (fty::deflist vl-maybe-exprlist
    :measure (two-nats-measure (acl2-count x) 10)
    :elt-type vl-maybe-expr
    :elementp-of-nil t
    :true-listp t
    :parents (vl-expr))

  (fty::defalist vl-call-namedargs
    :measure (two-nats-measure (acl2-count x) 10)
    :key-type stringp
    :val-type vl-maybe-expr
    :true-listp t
    :short "Representation of any named arguments of a function call."
    :long "<p>This is really the same type as @(see vl-atts), but we use a different
           name because the purposes they're used for are so different.</p>")

  (fty::defalist vl-atts
    :measure (two-nats-measure (acl2-count x) 10)
    :key-type stringp
    :val-type vl-maybe-expr
    :true-listp t
    ;; Note: In the docs here we use <tt>...</tt> and <code>...</code> instead
    ;; of @('...') and @({...}) to avoid having XDOC insert hyperlinks to the
    ;; '*' function when it sees the '(*' at the start of these attributes.
    :short "Representation of <tt>(* foo = 3, bar *)</tt> style attributes."
    :long "<p>Verilog-2005 and SystemVerilog-2012 allow many constructs, (e.g.,
           module instances, wire declarations, assignments, subexpressions,
           and so on) to be annotated with <b>attributes</b>.</p>

           <p>Each individual attribute can either be a single key with no
           value (e.g., @('baz') above), or can have the form @('key = value').
           The keys are always identifiers, and the values (if provided) are
           expressions.  Both Verilog-2005 and SystemVerilog-2012 agree that an
           attribute with no explicit value is to be treated as having value
           @('1').</p>


           <h3>Representation</h3>

           <p>We represent attributes as alists mapping names to their values.
           We use ordinary ACL2 strings to represent the keys.  These strings
           are typically honsed to improve memory sharing.  Each explicit value
           is represented by an ordinary @(see vl-expr-p), and keys with no
           values are bound to @('nil') instead.</p>

           @(def vl-atts-p)


           <h3>Size/Types of Attribute Values</h3>

           <p>Verilog-2005 doesn't say anything about the types of attribute
           expressions.  SystemVerilog-2012 says (Section 5.12) that the type
           of an attribute with no value is @('bit'), and that otherwise its
           type is the (presumably self-determined) type of the expression.
           But this is not really an adequate spec.  Consider for instance an
           attribute like:</p>

           <code>
                    (* foo = a + b *)
           </code>

           <p>Since attributes live in their own namespace, it isn't clear what
           @('a') and @('b') refer to here.  For instance, are they wires in
           this module, or perhaps global values that are known by the Verilog
           tool.  It doesn't seem at all clear what the type or size of such an
           expression is supposed to be.</p>

           <p>Well, no matter.  Attributes are not used for much and if their
           sizes and types aren't well specified, that's not necessarily any
           kind of problem.  We generally expect to be able to ignore
           attributes and do not expect to need to size them or determine their
           types.</p>


           <h3>Nesting Attributes</h3>

           <p>Note that both Verilog-2005 and SystemVerilog-2012 prohibit the
           nesting of attributes.  That is, expressions like the following are
           not allowed:</p>

           <code>
                   (* foo = a + (* bar *) b *)
           </code>

           <p>VL's parser enforces this restriction and will not allow
           expressions to have nested attributes; see @(see
           vl-parse-0+-attribute-instances).  However, we make <b>no such
           restriction</b> internally&mdash;our @(see vl-expr-p) structures can
           have attributes nested to any arbitrary depth.</p>


           <h3>Redundant and Conflicting Attributes</h3>

           <p>When the same attribute name is given repeatedly, both
           Verilog-2005 and SystemVerilog-2012 agree that the last occurrences
           of the attribute should be used.  That is, the value of @('foo')
           below should be 5:</p>

           <code>
                    (* foo = 1, foo = 5 *)
                    assign w = a + b;
           </code>

           <p>VL's parser properly handles this case.  It issues warnings when
           duplicate attributes are used, and always produces @('vl-atts-p')
           structures that are free from duplicate keys, and where the entry
           for each attribute corresponds to the last occurrence of it; see
           @(see vl-parse-0+-attribute-instances).</p>

           <p>Internally we make <b>no such restriction</b>.  We treat
           @('vl-atts-p') structures as ordinary alists.</p>


           <h3>Internal Use of Attributes by VL</h3>

           <p>Certain VL transformations may occasionally add attributes
           throughout modules.  For instance, the @(see make-implicit-wires)
           transformation will add @('VL_IMPLICIT') attributes to the wire
           declarations that added implicitly.</p>

           <p>We once tried to record the different kinds of attributes that VL
           used here, but that list became quickly out of date as we forgot to
           maintain it, so we no longer try to do this.  As a general rule,
           attributes added by VL <i>should</i> be prefixed with @('VL_').  In
           practice, we may sometimes forget to follow this rule.</p>")


; -----------------------------------------------------------------------------
;
;                        ** Ranges, Dimensions **
;
; -----------------------------------------------------------------------------

  (defprod vl-range
    :parents (syntax)
    :measure (two-nats-measure (acl2-count x) 100)
    :short "A simple @('[msb:lsb]') style range."
    :tag :vl-range
    :layout :tree
    ((msb vl-expr-p "Most significant bit of the range.")
     (lsb vl-expr-p "Least significant bit of the range."))

    :long "<p>Ranges are discussed in Section 7.1.5 of the Verilog-2005
           standard.  Typically a range looks like @('[msb:lsb]').  This same
           syntax is used in many places, such as part selects, @('with')
           expressions in streaming expressions, etc.</p>

           <p>In general, the @('msb') is not required to be greater than
           @('lsb'), and neither index is required to be zero.  However, for
           instance, if a wire is declared with a range such as @('[7:0]'),
           then it should be selected from using ranges such as @('[3:0]') and
           attempting to select from it using a \"backwards\" part-select such
           as @('[0:3]') is an error.</p>

           <p>See @(see range-tools) for many functions for working with
           ranges.</p>")

  (defoption vl-maybe-range vl-range
    :measure (two-nats-measure (acl2-count x) 110)
    :parents (vl-range))

  (defflexsum vl-dimension
    :parents (syntax)
    :measure (two-nats-measure (acl2-count x) 105)
    :short "Representation of a single packed or unpacked dimension.  These
            could be a range like @('[3:0]') or something more exotic, like
            @('[]'), @('[*]'), or @('[logic [3:0]]')."
    ;; [Jared] This was originally called vl-packeddimension and lacked the
    ;; star, datatype, and queue cases.  When adding the new dimension types, I
    ;; originally considered distinguishing between packed and other
    ;; dimensions, adding a vl-variabledimension type here.  This seemed to
    ;; bring a lot of trouble for no gain.  When processing dimensions in any
    ;; real way, the question is always: "are these dimensions all nicely
    ;; resolved simple ranges?" so even with just packed_dimension, you already
    ;; have unsized dimensions and unresolved ranges to handle as error cases.
    ;; It's generally easy to extend these error cases to queues and
    ;; associative dimensions as well.
    (:unsized
     :short "An unsized dimension, e.g., @('[]')."
     :long "<p>See SystemVerilog-2012 section 7.5.  These are for dynamic
            arrays whose size can be changed at runtime.</p>"
     :cond (eq x :vl-unsized-dimension)
     :fields nil
     :ctor-body ':vl-unsized-dimension)
    (:star
     :short "The @('associative_dimension') @('[*]')."
     :long "<p>See SystemVeriog-2012 section 7.8.1 on the wildcard index type
            for associative (sparse) arrays.  This allows the array to be
            indexed by any integer-valued expression of arbitrary size.</p>"
     :cond (eq x :vl-star-dimension)
     :fields nil
     :ctor-body ':vl-star-dimension)
    (:datatype
     :short "An @('associative_dimension') based on a data type."
     :long "<p>See SystemVerilog-2012 section 7.8 on Associative Arrays.  The
            type is an index type for a sparse array.</p>"
     :cond (eq (tag x) :vl-type-dimension)
     :fields ((type :acc-body (cdr x)
                    :type vl-datatype
                    :acc-name vl-dimension->type))
     :ctor-body (cons :vl-type-dimension type))
    (:queue
     :short "A queue dimension, e.g., @('[$]') or @('[$ : 5]')"
     :cond (eq (tag x) :vl-queue-dimension)
     :fields ((maxsize :acc-body (cdr x)
                       :acc-name vl-dimension->maxsize
                       :type vl-maybe-expr-p
                       :doc "For bounded queues, this is the maximum index of
                             any element in the queue, e.g., it is the @('5')
                             in @('[$ : 5]').  For unbounded queues, this is
                             just @('nil')."))
     :ctor-body (cons :vl-queue-dimension maxsize))
    (:range
     :short "A dimension that is a range, e.g., @('[3:0]') or @('[3]')."
     :cond t
     :fields ((range :acc-body x
                     :type vl-range
                     :acc-name vl-dimension->range
                     :doc "The whole dimension as an atomic @(see vl-range).
                           Note (SystemVerilog-2012 page 109): unpacked
                           dimensions like @('[size]') are the same as
                           @('[0:size-1]').  We therefore convert them into
                           ranges at parse-time."))
     :ctor-body range
     :ctor-name vl-range->dimension
     :extra-binder-names (msb lsb)
     :long "<p>Note that the @(see b*) binder sets up extra bindings for
            @('.msb') and @('.lsb'), so you can typically access the guts of
            the interior range directly.</p>"))

  (fty::deflist vl-dimensionlist
    :elt-type vl-dimension
    :measure (two-nats-measure (acl2-count x) 10)
    :elementp-of-nil nil
    :parents (vl-dimension))

  (defoption vl-maybe-dimension vl-dimension
    :measure (two-nats-measure (acl2-count x) 110)
    :parents (vl-dimension))


; -----------------------------------------------------------------------------
;
;                          ** Index Expressions **
;
; -----------------------------------------------------------------------------

  (defprod vl-hidindex
    :parents (vl-index)
    :short "Representation of a leading piece of a hierarchical reference to
            something, perhaps with associated indices."
    :measure (two-nats-measure (acl2-count x) 110)
    :measure-debug t
    :layout :tree

    ((name    vl-hidname    "Leading name before the dot.")
     (indices vl-exprlist-p "Any associated indices."))

    :long "<p>A @('vl-hidindex') only makes sense in the context of a larger
           @(see vl-hidexpr).  Consider an hierarchical indexing expression
           like</p>

           @({ cat . (dog [3][2][1]) . elf) })

           <p>The @('dog[3][2][1]') part of this will be represented by a
           @('vl-hidindex') whose @('name') is @('dog') and whose indices are
           the expressions for @('3'), @('2'), and @('1').</p>

           <p>The @('cat') part of this will be represented by a
           @('vl-hidindex') whose @('name') is @('cat') and whose @('indices')
           are @('nil').</p>")

  (defflexsum vl-hidexpr
    :parents (vl-index)
    :short "Representation of a (possibly) hierarchical reference to something
            in the design.  For example: @('cat.dog[3][2][1].elf')."
    :measure (two-nats-measure (acl2-count x) 100)
    (:end
     :short "A lone identifier, or the final part of a hierarchical identifier."
     :cond (atom x)
     :fields ((name :acc-body x :type stringp
                    :rule-classes :type-prescription))
     :ctor-body name)
    (:dot
     :cond t
     :short "A single dot operation, perhaps with associated indices, that
             connects parts of a hierarchical identifier."
     :fields ((first :acc-body (car x) :type vl-hidindex-p
                     :doc "The part before the dot and any associated indices.")
              (rest :acc-body (cdr x) :type  vl-hidexpr-p
                    :doc "The part after the dot and indices."))
     :ctor-body (cons first rest)))

  (defflexsum vl-scopeexpr
    :parents (vl-index)
    :short "Representation of a (possibly scoped, possibly hierarchical)
            reference to something in the design.  For example:
            @('ape::bat::cat.dog[3][2][1].elf')."
    :measure (two-nats-measure (acl2-count x) 110)
    (:colon
     :cond (and (consp x)
                (eq (car x) :colon))
     :short "Represents a single scoping operator (@('::') being applied to
             some interior scopeexpr."
     :shape (consp (cdr x))
     :fields ((first :acc-body (cadr x) :type  vl-scopename-p
                     :doc "The outer scope name, e.g., @('ape')")
              (rest :acc-body (cddr x) :type  vl-scopeexpr-p
                    :doc "The inner scope expression, e.g., @('bat::cat.dog[3][2][1].elf')."))
     :ctor-body (cons :colon (cons first rest)))
    (:end
     :cond t
     :short "A scope expression that has no scoping operators.  For instance,
             plain identifiers or hierarchical identifiers with no scopes."
     :fields ((hid :acc-body x :type vl-hidexpr-p))
     :ctor-body hid)

    :long "<p>A <b>scope expression</b> extends a <b>hid expression</b> with
           arbitrarily many levels of scoping.  For instance, in the
           expression:</p>

           @({
                ape::bat::cat.dog[3][2][1].elf
           })

           <p>The @('cat.dog[3][2][1].elf') part is a plain hierarchical
           identifier with no scoping.  It will be wrapped up into an @(':end')
           scope expression.  Meanwhile, the @('ape::') and @('bat::') portions
           will be represented with two recursive @(':colon') scopeexprs, with
           the @('ape::') expression on the outside.</p>")

  (defprod vl-plusminus
    :parents (vl-partselect)
    :short "Representation of a select of the form @('[base +: width]') or
            @('[base -: width]')."
    :tag :vl-plusminus
    :layout :tree
    :measure (two-nats-measure (acl2-count x) 100)
    ((base  vl-expr-p
            "The left-hand side, base expression; typically variable.")
     (width vl-expr-p
            "The right-hand side, width expression; typically constant.")
     (minusp booleanp :rule-classes :type-prescription
             "Indicates @('-:') or @('+:').")))

  (defflexsum vl-partselect
    :parents (vl-index)
    :short "Representation of any kind of part-select that is being applied to
            a some object in the design."
    :measure (two-nats-measure (acl2-count x) 105)
    (:none
     :short "No part select."
     :cond (atom x)
     :shape (not x)
     :fields nil
     :ctor-body nil)
    (:range
     :short "A typical @('[msb:lsb]') style part-select, e.g., @('[3:0]') or
             @('[1:5]')."
     :cond (eq (car x) :vl-range)
     :fields ((range :type vl-range
                     :acc-body x
                     :acc-name vl-partselect->range
                     :doc "The whole range being selected, as an atomic @(see
                           vl-range)."))
     :ctor-body range
     :ctor-name vl-range->partselect
     :extra-binder-names (msb lsb)
     :long "<p>Note that the @(see b*) binder sets up extra bindings for
            @('.msb') and @('.lsb'), so you can typically access the guts of
            the interior range directly.</p>")
    (:plusminus
     :short "An indexed part-select like @('[foo +: 3]') or @('[bar -: 4]')."
     :cond t
     :fields ((plusminus :type vl-plusminus
                         :acc-body x
                         :acc-name vl-partselect->plusminus
                         :doc "The whole indexed part select, e.g., @('[foo +:
                               3]'), as an atomic @(see vl-plusminus)."))
     :ctor-body plusminus
     :ctor-name vl-plusminus->partselect
     :extra-binder-names (base width minusp)
     :long "<p>Note that the @(see b*) binder sets up extra bindings for
            @('.base'), @('.width'), and @('.minusp'), so you can typically
            access the guts of the interior @('plusminus') directly.</p>"))


; -----------------------------------------------------------------------------
;
;                         ** Inside Expressions **
;
; -----------------------------------------------------------------------------

  (deftagsum vl-valuerange
    :parents (vl-inside)
    :measure (two-nats-measure (acl2-count x) 105)
    :base-case-override :valuerange-single
    :short "A value or a range used in an @('inside') expression.  For instance,
            the @('8') or @('[16:20]') from @('a inside { 8, [16:20] }')."
    :layout :tree
    (:valuerange-range
     :base-name vl-valuerange-range
     :short "A range of values from an @('inside') expression's set.  For
             instance, the @('[16:20]') part of @('a inside { 8, [16:20] }')."
     ((low  vl-expr-p "Always the left component, e.g., @('16') in @('[16:20]').")
      (high vl-expr-p "Always the high component, e.g., @('20') in @('[16:20]').")))

    (:valuerange-single
     :base-name vl-valuerange-single
     :short "A single value from an @('inside') expression's set.  For
             instance, the @('8') part of @('a inside { 8, [16:20] }')."
     ((expr vl-expr-p))))


  (fty::deflist vl-valuerangelist
    :measure (two-nats-measure (acl2-count x) 10)
    :elt-type vl-valuerange
    :elementp-of-nil nil
    :parents (vl-inside))



; -----------------------------------------------------------------------------
;
;                         ** Streaming Expressions **
;
; -----------------------------------------------------------------------------

  (deftagsum vl-slicesize
    :measure (two-nats-measure (acl2-count x) 100)
    :parents (vl-stream)
    :short "The slice size (or an indicator that there is no size) for a
            streaming expression."
    :layout :tree
    (:expr
     :short "A slice size that is an expression, e.g., @('{<< 16 {a,b}}')
             has an expression slice size of @('16')."
     ((expr vl-expr-p)))
    (:type
     :short "A slice size that is a datatype, e.g., @('{<< byte {a,b}}')
             has a slice size of @('byte')."
     ((type vl-datatype-p)))
    (:none
     :short "An indication that this streaming expression does not have
             any slice size, e.g., @('{<< {a}}')."
     ()))

  (defprod vl-streamexpr
    :parents (vl-stream)
    :measure (two-nats-measure (acl2-count x) 110)
    :short "A part of the stream in a streaming operator.  For instance,
            in @('{<< 16 {a, b with [0 +: size]}}'), the streamexprs are
            @('a') and @('b with [0 +: size]')."
    :layout :tree
    ((expr  vl-expr-p
            "The expression part without the @('with').  Example: in the
             expression @('{<< 16 {a, b with [0 +: size]}}'), the exprs are
             @('a') and @('b').")

     (part  vl-arrayrange-p
            "The @('with') information, if any.  Example: in the expression
             @('{<< 16 {a, b with [0 +: size]}}'), the @('part') for @('a') is
             the special @(':none') arrayrange, which indicates that there is
             no @('with') part.  The @('part') for @('b') is an arrayrange that
             captures the @('[0 +: size]') information.")))

  (fty::deflist vl-streamexprlist
    :measure (two-nats-measure (acl2-count x) 10)
    :elt-type vl-streamexpr
    :elementp-of-nil nil
    :parents (vl-streamexpr))

  (defflexsum vl-arrayrange
    :parents (vl-stream)
    :short "Representation of an array range for use in @('with') operators in
            streaming packing/unpacking expressions."
    :measure (two-nats-measure (acl2-count x) 105)
    (:none
     :short "Used for plain stream expressions with no @('with') part."
     :cond (or (atom x)
               (eq (car x) :none))
     :shape (and (consp x)
                 (not (cdr x)))
     :fields nil
     :ctor-body '(:none))
    (:range
     :short "A @('with [msb:lsb]') stream expression part."
     :cond (eq (car x) :vl-range)
     :fields ((range :type vl-range
                     :acc-body x
                     :acc-name vl-arrayrange->range
                     :doc "The whole range, e.g., @('[20:16]'), as an atomic
                           @(see vl-range)."))
     :ctor-body range
     :ctor-name vl-range->arrayrange
     :extra-binder-names (msb lsb)
     :long "<p>Note that the @(see b*) binder sets up extra bindings for
            @('.msb') and @('.lsb'), so you can typically access the guts of
            the interior range directly.</p>")
    (:plusminus
     :short "A @('with [base +: width]') or @('with [base -: width]') stream
             expression part."
     :cond (eq (car x) :vl-plusminus)
     :fields ((plusminus :type vl-plusminus
                         :acc-body x
                         :acc-name vl-arrayrange->plusminus
                         :doc "The whole @('[base +: width]') or @('[base -:
                               width]') information as an atomic @(see
                               vl-plusminus)."))
     :ctor-body plusminus
     :ctor-name vl-plusminus->arrayrange
     :extra-binder-names (base width minusp)
     :long "<p>Note that the @(see b*) binder sets up extra bindings for
            @('.base'), @('.width'), and @('.minusp'), so you can typically
            access the guts of the interior @('plusminus') directly.</p>")
    (:index
     :short "A @('with index') stream expression part."
     :cond t
     :fields ((expr :type vl-expr
                    :acc-body x
                    :acc-name vl-arrayrange->expr
                    :doc "The index being used."))
     :ctor-body expr
     :ctor-name vl-expr->arrayrange))


; -----------------------------------------------------------------------------
;
;                              ** Casting **
;
; -----------------------------------------------------------------------------

  (deftagsum vl-casttype
    :parents (vl-cast)
    :measure (two-nats-measure (acl2-count x) 10)
    :short "The new type/size/signedness/constness to cast an expression to."
    :layout :tree
    (:type
     :short "A cast to a datatype, like @('int'(foo)')."
     ((type vl-datatype-p "The datatype to cast to.")))
    (:size
     :short "A cast to a size, like @('mywidth'(foo)')."
     ((size vl-expr-p "The size expression.")))
    (:signedness
     :short "A cast to a signedness, like @('signed'(foo)') or @('unsigned'(foo)')."
     ((signedp booleanp :rule-classes :type-prescription)))
    (:const
     :short "A cast to a constant, like @('const'(foo)')."
     ()))


; -----------------------------------------------------------------------------
;
;                         ** Assignment Patterns **
;
; -----------------------------------------------------------------------------

  (deftagsum vl-patternkey
    :measure (two-nats-measure (acl2-count x) 100)
    :parents (vl-pattern)
    :short "A key in an assignment pattern."
    :layout :tree
    (:expr
     :short "An unambiguous array index pattern key like @('5') or @('foo +
             bar')."
     ((key vl-expr-p)))
    (:structmem
     :short "A struct member pattern key like @('opcode').  Note that until
             @(see annotate) is done, this may be a type name which needs to be
             disambiguated."
     ((name stringp :rule-classes :type-prescription)))
    (:type
     :short "A type pattern key like @('integer') or @('mytype_t')."
     ((type vl-datatype-p)))
    (:default
     :short "The special @('default') pattern key."
     ())
    :long "<p>A @('vl-patternkey') represents a single key in an key/value
           style assignment pattern, such as:</p>

           @({
                '{ 0: a, 1: b, 2: c, default: 0 }    // assign to some array indices, default others...
                '{ foo: 3, bar: 5 }                  // assign to struct members by name (maybe)
                '{ integer: 5, opcode_t: 7 }         // assign to struct members by type (maybe)
           })

           <p>These kinds of pattern keys are, in general, somewhat ambiguous
           and difficult to resolve until elaboration time.  To avoid the worst
           of these ambiguities we impose certain restrictions on the kinds of
           assignment patterns we support; @(see vl-patternkey-ambiguity) for
           some notes about this.</p>")

  (fty::defalist vl-keyvallist
    :measure (two-nats-measure (acl2-count x) 10)
    :key-type vl-patternkey
    :val-type vl-expr-p
    :parents (vl-pattern))

  (deftagsum vl-assignpat
    :measure (two-nats-measure (acl2-count x) 100)
    :parents (vl-pattern)
    :short "The (untyped) guts of an assignment pattern, e.g., @(''{1,2,3}'),
            @(''{a:1, b:2}'), or similar."
    :layout :tree
    (:positional
     :short "A positional assignment pattern like @(''{1, 2, 3}')."
     ((vals  vl-exprlist-p
             "The expressions that make up the pattern, in order.")))
    (:keyval
     :short "An assignment pattern using named keys, e.g., @(''{foo:1, bar:2}')."
     ((pairs vl-keyvallist-p
             "The key/value pairs making up the pattern.")))
    (:repeat
     :short "A replication-style array assignment pattern like @(''{2{y}}')."
     ((reps  vl-expr-p     "Number of times the values are being replicated.")
      (vals  vl-exprlist-p "The list of values to replicate.")))
    :base-case-override :positional)



  (deftagsum vl-paramvalue
    :parents (vl-paramargs)
    :short "Representation for the actual values given to parameters."
    :long "<p>In Verilog-2005, the values for a parameterized module were always
ordinary expressions, e.g., 3 and 5 below.</p>

@({
      myalu #(.delay(3), .width(5)) alu1 (...);
})

<p>However, in SystemVerilog-2012 there can also be type parameters.  For
instance, a valid instance might look like:</p>

@({
      myalu #(.delay(3), .Bustype(logic [63:0])) myinst (...);
})

<p>The @('vl-paramvalue-p') is a sum-of-products style type that basically
corresponds to the SystemVerilog @('param_exprewssion') grammar rule:</p>

@({
     param_expression ::= mintypmax_expression | data_type | '$'
})

<p>But note that @('$') is a valid @(see vl-expr-p) so this essentially
collapses into only two cases: expression or data type.</p>"
    :measure (two-nats-measure (acl2-count x) 60)
    :base-case-override :expr
    (:type ((type vl-datatype)))
    (:expr ((expr vl-expr))))


  (fty::deflist vl-paramvaluelist
    :elt-type vl-paramvalue-p
    :true-listp nil
    :elementp-of-nil nil
    :measure (two-nats-measure (acl2-count x) 0)
    ///
    ;; (defthm vl-paramvaluelist-p-when-vl-exprlist-p
    ;;   (implies (vl-exprlist-p x)
    ;;            (vl-paramvaluelist-p x))
    ;;   :hints(("Goal" :induct (len x))))
    )

  (defoption vl-maybe-paramvalue vl-paramvalue-p
    :parents (vl-paramargs)
    :measure (two-nats-measure (acl2-count x) 65)
    ///
    (defthm type-when-vl-maybe-paramvalue-p
      (implies (vl-maybe-paramvalue-p x)
               (or (consp x)
                   (not x)))
      :hints(("Goal" :in-theory (enable vl-maybe-paramvalue-p)))
      :rule-classes :compound-recognizer))

  (defprod vl-namedparamvalue
    :parents (vl-paramargs)
    :short "Representation of a single, named parameter argument."
    :tag :vl-namedparamvalue
    :layout :tree
    :measure (two-nats-measure (acl2-count x) 70)

    ((name     stringp :rule-classes :type-prescription
               "The name of the parameter, e.g., @('size') in @('.size(3)')")

     (value    vl-maybe-paramvalue-p
               "The value being given to this parameter, e.g., @('3') in @('.size(3)').
              In Verilog-2005 this is usually an expression but might also be
              @('nil') because the value can be omitted.  SystemVerilog-2012
              extends this to also allow data types.")))

  (fty::deflist vl-namedparamvaluelist
              :elt-type vl-namedparamvalue-p
              :true-listp nil
              :elementp-of-nil nil
              :measure (two-nats-measure (acl2-count x) 0))

  (deftagsum vl-paramargs
    :short "Representation of the values to use for a module instance's
  parameters (not ports)."

    :long "<p>There are two kinds of argument lists for the parameters of module
instantiations, which we call <i>plain</i> and <i>named</i> arguments.</p>

@({
  myalu #(3, 6) alu1 (...);                  <-- \"plain\" arguments
  myalu #(.size(3), .delay(6)) alu2 (...);   <-- \"named\" arguments
})

<p>A @('vl-paramargs-p') structure represents an argument list of either
variety.</p>"

    :measure (two-nats-measure (acl2-count x) 5)
    :base-case-override :vl-paramargs-plain
    (:vl-paramargs-named
     :base-name vl-paramargs-named
     ((args vl-namedparamvaluelist-p)))

    (:vl-paramargs-plain
     :base-name vl-paramargs-plain
     ((args vl-paramvaluelist-p))))

  (defoption vl-maybe-paramargs vl-paramargs
    :measure (two-nats-measure (acl2-count x) 10))

; -----------------------------------------------------------------------------
;
;                             ** Datatypes **
;
; -----------------------------------------------------------------------------

  (deftagsum vl-datatype
    :measure (two-nats-measure (acl2-count x) 30)
    :base-case-override :vl-coretype
    :short "Representation of a SystemVerilog variable datatype, e.g., @('logic
    [7:0][3:0]'), @('string'), @('mystruct_t [3:0]'), etc."

    (:vl-coretype
     :layout :tree
     :base-name vl-coretype
     :hons t
     :short "A built-in SystemVerilog datatype like @('integer'), @('string'),
             @('void'), etc., or an array of such a type."
     ((name    vl-coretypename-p
               "Kind of primitive datatype, e.g., @('byte'), @('string'),
                etc.")
      (pdims   vl-dimensionlist-p
               "Only valid for integer vector types (bit, logic, reg).  If
                present, these are the 'packed' array dimensions, i.e., the
                [7:0] part of a declaration like @('bit [7:0] memory [255:0]').
                There can be arbitrarily many of these.")
      (udims   vl-dimensionlist-p
               "Unpacked array dimensions, for instance, the @('[255:0]') part
                of a declaration like @('bit [7:0] memory [255:0]').  There can
                be arbitrarily many of these.")
      (signedp booleanp :rule-classes :type-prescription
               "Only valid for integer types.  Roughly indicates whether the
                integer type is signed or not.  Usually you shouldn't use this;
                see @(see vl-datatype-arithclass) instead.")))

    (:vl-struct
     :layout :tree
     :base-name vl-struct
     :short "A SystemVerilog @('struct') datatype, or an array of structs."
     ((members vl-structmemberlist-p
               "The list of structure members, i.e., the fields of the structure,
                in order.")
      (packedp booleanp :rule-classes :type-prescription
               "Roughly: says whether this struct is @('packed') or not,
                but <b>warning!</b> this is complicated and generally
                should not be used; see below for details.")
      (pdims    vl-dimensionlist-p
                "Packed dimensions for the structure.")
      (udims    vl-dimensionlist-p
                "Unpacked dimensions for the structure.")
      (signedp booleanp :rule-classes :type-prescription
               "Roughly: says whether this struct is @('signed') or not,
                but <b>warning!</b> this is really complicated and generally
                should not be used; see below for details."))
     :long "<p>If you look at the SystemVerilog grammar you might notice that
            there aren't unpacked dimensions:</p>

            @({
                data_type ::= ... | struct_union [ 'packed' [signing] ] '{'
                                      struct_union_member { struct_union_member }
                                    '}' { packed_dimension }
            })

            <p>But it seems much cleaner to make the unpacked dimensions part
            of a structure, so when we deal with a variable declaration
            like:</p>

            @({
                mystruct_t [3:0] foo [4:0];
            })

            <p>We can record, in the type of @('foo') itself, all of the
            relevant type information, instead of having to keep the unpacked
            dimensions separated.</p>

            <h3>Warning about Packedp and Signedp</h3>

            <p>The packedness/signedness of structures/arrays is complicated;
            you should usually use utilities like @(see vl-datatype-packedp)
            and @(see vl-datatype-arithclass) instead of directly using the
            @('packedp') and @('signedp') fields.</p>

            <p>What are the issues?  At parse time, we use the @('packedp') and
            @('signedp') fields to record whether the struct was declared to be
            packed and/or signed.</p>

            <p>For a single (non-array) structure, @('packedp') is basically
            correct, except that BOZO really we should be checking that all of
            the members of the struct are packed as well.  But for arrays of
            structs, even if the struct itself is packed, the array itself
            might be unpacked.  For instance, if we write:</p>

            @({
                 struct packed { logic [3:0] a; logic [3:0] b; } myvar [3:0];
            })

            <p>then @('myvar') will be marked as packed, but this packedness
            refers to the <i>elements</i> of @('myvar') instead of to
            @('myvar') itself!</p>

            <p>Signedness has similar issues except that it is more
            complicated; see the documentation in @(see vl-datatype-arithclass)
            and also @(see vl-usertype) for more details.</p>")

    (:vl-union
     :layout :tree
     :base-name vl-union
     :short "A SystemVerilog @('union') datatype, or an array of @('union')s."
     ((members  vl-structmemberlist-p
                "The list of union members.")
      (packedp  booleanp :rule-classes :type-prescription
                "Roughly: says whether this union is @('packed') or not, but
                 <b>warning!</b> this should normally not be used as it has the
                 same problems as @('packedp') for structs; see @(see
                 vl-struct).")
      (pdims    vl-dimensionlist-p
                "Packed dimensions for this union type.")
      (udims    vl-dimensionlist-p
                "Unpacked dimensions for the union type.  See also @(see
                 vl-struct) and the notes about unpacked dimensions there.")
      (signedp  booleanp :rule-classes :type-prescription
                "Roughly: says whether this union is @('signed') or not, but
                 <b>warning!</b> this should normally not be used as it has the
                 same problems as @('signedp') for structs; see @(see
                 vl-struct).")
      (taggedp  booleanp :rule-classes :type-prescription
                "Says whether this union is 'tagged' or not.")))

    (:vl-enum
     :layout :tree
     :base-name vl-enum
     :short "A SystemVerilog @('enum') datatype, or an array of @('enum')s."
     ((basetype vl-datatype-p
                "The base type for the enum.  Note that, in the SystemVerilog
                 syntax, enums are only allowed to have certain base types that
                 are very basic.  But for simplicity, in our representation we
                 just use an arbitrary @(see vl-datatype) here.")
      (items    vl-enumitemlist-p
                "The items of the enumeration.")
      (values vl-exprlist-p
              "List of all valid values of this enum, generated by enumnames transform")
      (pdims    vl-dimensionlist-p
                "Packed dimensions for this enum type.")
      (udims    vl-dimensionlist-p
                "Unpacked dimensions for this enum type.")))

    (:vl-usertype
     :layout :tree
     :base-name vl-usertype
     :short "Represents a reference to some user-defined SystemVerilog datatype."
     ;; data_type ::= ... | [ class_scope | package_scope ] type_identifier { packed_dimension }
     ((name   vl-scopeexpr-p
              "Typedef name, like @('foo_t').  May have a package scope, but
               should not otherwise be hierarchical.")
      (res    vl-maybe-datatype-p
              "The resolved type that name refers to.  If present, it means
               we've already looked up the type and resolved its value.  See
               below for more notes.")
      (pdims  vl-dimensionlist-p
              "Packed dimensions for this user type.")
      (udims  vl-dimensionlist-p
              "Unpacked dimensions for this user type.")
      (virtual-intfc booleanp
                     "Indicates a virtual interface type, which we don't really support.")
      (intfc-params vl-maybe-paramargs
                    "Parameter values -- relevant for the virtual-intfc case"))
     :long "<h3>Notes about the @('res') Field</h3>

            <p>Originally, to deal with user-defined types, we tried to just
            substitute definitions for usertypes.  However, it turns out that
            this isn't correct: e.g.</p>

            @({
                typedef logic signed [3:0] snib;
                snib [3:0] foo1;
            })

            <p>is <b>not</b> the same as just</p>

            @({
                logic signed [3:0] [3:0] foo2;
            })

            <p>Here, @('foo1') is an unsigned array of signed slots, whereas
            @('foo2') is a signed array of unsigned slots.  (NCV and VCS also
            treat them differently; we believe NCV gets it right with respect
            to the spec, whereas VCS seems to do the substitution.)</p>

            <p>We then decided we'd just deal with usertypes directly.  We
            rewrote all our type-manipulating functions to operate on a
            datatype and scopestack simultaneously.  However, we don't want to
            store scopestacks between transformations.  So there's a problem
            with e.g. type parameters: e.g.</p>

            @({
                 module sub #(type and_t = logic [3:0])
                             (input and_t a, b, output and_t o);
                   assign o = a & b;
                 endmodule

                 module super ();
                   typedef logic signed [5:0] my_and_t;
                   my_and_t a, b;
                   my_and_t o;
                   sub #(.and_t(my_and_t)) inst (a, b, o);
                 endmodule
            })

            <p>Here, we want to transform @('sub'), replacing the @('and_t')
            parameter with the overridden version @('my_and_t').  But
            @('my_and_t') is only defined in @('super')!  So we might want to
            do something like replacing the @('and_t') type parameter with
            @('typedef my_and_t and_t;'), or leaving it as a @('parameter
            #(type and_t = my_and_t)').  But neither of these work, because
            @('my_and_t') isn't defined in the scope of @('sub').</p>

            <p>Our solution is to go back to doing substitution, but instead of
            strictly substituting @('usertype <- definition'), we leave the
            @('usertype') but add the @('res') field, a @(see
            vl-maybe-datatype) which, if present, means we've resolved this
            usertype and its definition is the @('res').</p>")

    :long "<h3>Introduction</h3>

           <p>A @('vl-datatype') may represent a SystemVerilog variable
           datatype such as @('logic [3:0]'), @('integer'), @('string'),
           @('struct { ...}'), @('mybus_t'), etc.  It may also represent arrays
           of such types with packed and/or unpacked dimensions.</p>

           <p>Some higher-level functions for working with datatypes are found
           in @(see mlib); see in particular @(see datatype-tools).</p>

           <p>Note about the word ``<b>type</b>.''  The Verilog-2005 and
           SystemVerilog-2012 standards sometimes use the word ``type'' to
           refer to other things.  In particular:</p>

           <ul>

           <li>For historical reasons, the standards sometimes refer to the
           ``type'' of an expression when they really mean something more like
           its <b>signedness</b>.  Signedness is captured by @('vl-datatype'),
           but there are some nuances; see @(see vl-datatype-arithclass), @(see
           vl-exprsign), and @(see portdecl-sign).</li>

           <li>Net and port declarations can have a notion of a ``net type''
           such as @('wire'), @('wor'), @('supply1'), etc., which govern how
           multiple assignments to the net are resolved.  This information is
           <b>not</b> part of a @('vl-datatype').  See @(see vl-vardecl) for
           additional discussion.</li>

           </ul>

           <p>Note that we do not yet implement some of the more advanced
           SystemVerilog datatypes, including at least the following:</p>

           @({
                data_type ::= ...
                  | 'virtual' [ 'interface' ] interface_identifier [ parameter_value_assignment ] [ '.' modport_identifier ]
                  | class_type
                  | type_reference
           })")

  (defoption vl-maybe-datatype vl-datatype
    :measure (two-nats-measure (acl2-count x) 40)
    :parents (vl-datatype))

  (defprod vl-structmember
    :parents (vl-struct vl-union)
    :measure (two-nats-measure (acl2-count x) 110)
    :tag :vl-structmember
    :layout :tree
    :short "A single member of a struct or union."
    ;;   struct_union_member ::=  { attribute_instance } [random_qualifier]
    ;;                            data_type_or_void
    ;;                            list_of_variable_decl_assignments ';'
    ((type vl-datatype-p
           "Type of the struct member, including any unpacked dimensions (even
            though they normally come after the name.)")
     ;; now we want a single variable_decl_assignment
     (name stringp :rule-classes :type-prescription)
     (rhs  vl-maybe-expr-p
           "Right-hand side expression that gives the default value to this
            member, if applicable.")
     (rand vl-randomqualifier-p
           "Indicates whether a @('rand') or @('randc') keyword was used.")
     (atts vl-atts-p
           "Any <tt>(* foo = bar, baz *)</tt> style attributes."))
    :long "<p>Currently our structure members are very limited.  In the long
           run we may want to support more of the SystemVerilog grammar.  It
           allows a list of variable declaration assignments, which can have
           fancy dimensions and different kinds of @('new') operators.</p>

           <p>Notes for the future:</p>

           @({
              variable_decl_assignment ::=
                    variable_identifier { variable_dimension } [ '=' expression ]
                  | dynamic_array_variable_identifier unsized_dimension { variable_dimension } [ '=' dynamic_array_new ]
                  | class_variable_identifier [ '=' class_new ]
           })

           <p>These fancy @('_identifiers') are all just identifiers.  So
           really this is:</p>

           @({
                variable_decl_assignment ::=
                    identifier { variable_dimension }                   [ '=' expression ]
                  | identifier unsized_dimension { variable_dimension } [ '=' dynamic_array_new ]
                  | identifier                                          [ '=' class_new ]
           })

           <p>The @('new') keyword can occur in a variety of places.  One of
           these is related to defining constructors for classes, e.g., in
           class constructor prototypes/declarations we can have things
           like</p>

           @({
                function ... new (...) ...
           })

           <p>And @('super.new(...)') and so on.  But for now let's think of
           these as separate cases; that is, our approach to @('new') in other
           contexts doesn't necessarily need to have anything to do with these
           constructors, which we might instead handle more explicitly.</p>

           <p>The other places where @('new') can occur are in:</p>

           @({
               dynamic_array_new ::= new '[' expression ']' [ '(' expression ')' ]

               class_new ::= [ class_scope ] 'new' [ '(' list_of_arguments ')' ]
                           | 'new' expression
           })

           <p>Which in turn can occur in blocking assignments:</p>

           @({
                    [some fancy lhs] = dynamic_array_new
                 or [some other fancy lhs] = class_new
                 or other things not involving new
           })

           <p>(Which is interesting because we also have to support a lot of
           other new kinds of assignments like @('+=') and @('*='), so maybe
           this could become a @('new=') kind of assignment or something.)</p>

           <p>And they can also occur in variable decl assignments:</p>

           @({
                     simple id [ = expression ]
                 or  some fancy lhs with some various dimensions [= dynamic_array_new]
                 or  some simple lhs [= class_new]
           })

           <p>Which can occur in:</p>

           <ul>
           <li>SVA assertion variable declarations</li>
           <li>Data declarations (e.g., top-level @('const suchandso = new ...')</li>
           <li>Structure members in structs and unions.</li>
           </ul>

           <p>So maybe we don't so much need these to be expressions.  Maybe we
           can get away with them as alternate kinds of assignments.</p>")

  (fty::deflist vl-structmemberlist
    :measure (two-nats-measure (acl2-count x) 10)
    :elt-type vl-structmember
    :elementp-of-nil nil
    :parents (vl-structmember))

  (defprod vl-enumitem
    :parents (vl-enum)
    :measure (two-nats-measure (acl2-count x) 120)
    :tag :vl-enumitem
    :layout :tree
    :short "A single member of an @('enum')."
    ;; enum_name_declaration ::=
    ;;   enum_identifier [ [ integral_number [ : integral_number ] ] ] [ = constant_expression ]
    ((name  stringp :rule-classes :type-prescription
            "Name of this enumeration item.  For instance, in @('enum { red,
             yellow, green }'), the individual enumitems would be named
             @('\"red\"'), @('\"yellow\"'), and @('\"green\"').")
     (range vl-maybe-range-p
            "For simple enumeration items this is @('nil'), but for a fancy
             item, e.g., for @('enum { color[6:2] }'), the range would be
             @('[6:2]').  These might later be converted into their expanded
             out names, e.g., @('color6'), @('color5'), ..., @('color2').")
     (value vl-maybe-expr-p
            "For simple enumeration items without an explicit value expression
             this is just @('nil').  For fancier items with explicit values
             like @('enum { foo=5, ... }') this is the right-hand side
             expression, i.e., @('5').")))

  (fty::deflist vl-enumitemlist
    :elt-type vl-enumitem
    :measure (two-nats-measure (acl2-count x) 10)
    :elementp-of-nil nil
    :parents (vl-enum))


; -----------------------------------------------------------------------------
;
;                          ** Event Expressions **
;
; -----------------------------------------------------------------------------

  (defprod vl-evatom
    :short "A single item in an event control list."
    :tag :vl-evatom
    :layout :tree
    :measure (two-nats-measure (acl2-count x) 60)

    ((type vl-evatomtype-p
           "Kind of atom, e.g., posedge, negedge, edge, or plain.")

     (expr vl-expr-p
           "Associated expression, e.g., @('foo') for @('posedge foo')."))

    :long "<p>Event expressions and controls are described in Section 9.7.</p>

           <p>We represent the expressions for an event control (see @(see
           vl-eventcontrol-p)) as a list of @('vl-evatom-p') structures.  Each
           individual evatom is either a plain Verilog expression, or is
           @('posedge') or @('negedge') applied to a Verilog expression.</p>")

  (fty::deflist vl-evatomlist
    :elt-type vl-evatom-p
    :measure (two-nats-measure (acl2-count x) 75)
    :true-listp nil
    :elementp-of-nil nil)

  ) ;; End of the huge mutual recursion.



; -----------------------------------------------------------------------------
;
;                         ** Extra Range Binders **
;
;   These are used to provide things like the .msb and .lsb b* binders for
;   things that have ranges or plusminuses in them, like partselects.
;
; -----------------------------------------------------------------------------

(define vl-partselect-range->msb ((x vl-partselect-p))
  :parents (vl-partselect-range)
  :guard (eq (vl-partselect-kind x) :range)
  :short "Directly get the @('msb') of a @(see vl-partselect-range)'s range."
  :long "<p>This is also available as a @('.msb') @(see b*) binding.</p>"
  :inline t
  :enabled t
  (vl-range->msb (vl-partselect->range x)))

(define vl-partselect-range->lsb ((x vl-partselect-p))
  :parents (vl-partselect-range)
  :guard (eq (vl-partselect-kind x) :range)
  :short "Directly get the @('lsb') of a @(see vl-partselect-range)'s range."
  :long "<p>This is also available as a @('.lsb') @(see b*) binding.</p>"
  :inline t
  :enabled t
  (vl-range->lsb (vl-partselect->range x)))


(define vl-partselect-plusminus->base ((x vl-partselect-p))
  :parents (vl-partselect-plusminus)
  :guard (eq (vl-partselect-kind x) :plusminus)
  :short "Directly get the @('base') of a @(see vl-partselect-plusminus)'s plusminus."
  :long "<p>This is also available as a @('.base') @(see b*) binding.</p>"
  :inline t
  :enabled t
  (vl-plusminus->base (vl-partselect->plusminus x)))

(define vl-partselect-plusminus->width ((x vl-partselect-p))
  :parents (vl-partselect-plusminus)
  :guard (eq (vl-partselect-kind x) :plusminus)
  :short "Directly get the @('width') of a @(see vl-partselect-plusminus)'s plusminus."
  :long "<p>This is also available as a @('.width') @(see b*) binding.</p>"
  :inline t
  :enabled t
  (vl-plusminus->width (vl-partselect->plusminus x)))

(define vl-partselect-plusminus->minusp ((x vl-partselect-p))
  :parents (vl-partselect-plusminus)
  :guard (eq (vl-partselect-kind x) :plusminus)
  :short "Directly get the @('minusp') of a @(see vl-partselect-plusminus)'s plusminus."
  :long "<p>This is also available as a @('.minusp') @(see b*) binding.</p>"
  :inline t
  :enabled t
  (vl-plusminus->minusp (vl-partselect->plusminus x)))


(define vl-arrayrange-range->msb ((x vl-arrayrange-p))
  :parents (vl-arrayrange)
  :guard (eq (vl-arrayrange-kind x) :range)
  :short "Directly get the @('msb') of a @(see vl-arrayrange-range)'s range."
  :long "<p>This is also available as a @('.msb') @(see b*) binding.</p>"
  :inline t
  :enabled t
  (vl-range->msb (vl-arrayrange->range x)))

(define vl-arrayrange-range->lsb ((x vl-arrayrange-p))
  :parents (vl-arrayrange)
  :guard (eq (vl-arrayrange-kind x) :range)
  :short "Directly get the @('lsb') of a @(see vl-arrayrange-range)'s range."
  :long "<p>This is also available as a @('.lsb') @(see b*) binding.</p>"
  :inline t
  :enabled t
  (vl-range->lsb (vl-arrayrange->range x)))


(define vl-arrayrange-plusminus->base ((x vl-arrayrange-p))
  :parents (vl-arrayrange)
  :guard (eq (vl-arrayrange-kind x) :plusminus)
  :short "Directly get the @('base') of a @(see vl-arrayrange-plusminus)'s plusminus."
  :long "<p>This is also available as a @('.base') @(see b*) binding.</p>"
  :inline t
  :enabled t
  (vl-plusminus->base (vl-arrayrange->plusminus x)))

(define vl-arrayrange-plusminus->width ((x vl-arrayrange-p))
  :parents (vl-arrayrange)
  :guard (eq (vl-arrayrange-kind x) :plusminus)
  :short "Directly get the @('width') of a @(see vl-arrayrange-plusminus)'s plusminus."
  :long "<p>This is also available as a @('.width') @(see b*) binding.</p>"
  :inline t
  :enabled t
  (vl-plusminus->width (vl-arrayrange->plusminus x)))

(define vl-arrayrange-plusminus->minusp ((x vl-arrayrange-p))
  :parents (vl-arrayrange)
  :guard (eq (vl-arrayrange-kind x) :plusminus)
  :short "Directly get the @('minusp') of a @(see vl-arrayrange-plusminus)'s plusminus."
  :long "<p>This is also available as a @('.minusp') @(see b*) binding.</p>"
  :inline t
  :enabled t
  (vl-plusminus->minusp (vl-arrayrange->plusminus x)))

(define vl-dimension-range->msb ((x vl-dimension-p))
  :parents (vl-dimension)
  :guard (eq (vl-dimension-kind x) :range)
  :short "Directly get the @('msb') of a @(see vl-dimension-range)'s range."
  :long "<p>This is also available as a @('.msb') @(see b*) binding.</p>"
  :inline t
  :enabled t
  (vl-range->msb (vl-dimension->range x)))

(define vl-dimension-range->lsb ((x vl-dimension-p))
  :parents (vl-dimension)
  :guard (eq (vl-dimension-kind x) :range)
  :short "Directly get the @('lsb') of a @(see vl-dimension-range)'s range."
  :long "<p>This is also available as a @('.lsb') @(see b*) binding.</p>"
  :inline t
  :enabled t
  (vl-range->lsb (vl-dimension->range x)))



; -----------------------------------------------------------------------------
;
;                       ** Miscellaneous Lemmas **
;
; -----------------------------------------------------------------------------

(defthm vl-constint-bound-linear
  (< (vl-constint->value x)
     (expt 2 (vl-constint->origwidth x)))
  :hints (("goal" :use vl-constint-requirements
           :in-theory (e/d (unsigned-byte-p)
                           (vl-constint-requirements))))
  :rule-classes :linear)

(defthm consp-of-vl-weirdint->bits
  (consp (vl-weirdint->bits x))
  :rule-classes :type-prescription
  :hints(("Goal"
          :in-theory (disable vl-weirdint-requirements)
          :use ((:instance vl-weirdint-requirements)))))

(defthm type-when-vl-maybe-expr-p
  (implies (vl-maybe-expr-p x)
           (or (consp x)
               (not x)))
  :rule-classes :compound-recognizer
  :hints(("Goal" :in-theory (enable vl-maybe-expr-p))))

(defthm vl-expr-count-of-maybe-expr
  (implies x
           (< (vl-expr-count x) (vl-maybe-expr-count x)))
  :rule-classes :linear
  :hints(("Goal"
          :expand ((vl-maybe-expr-count x))
          :in-theory (enable vl-maybe-expr-some->val))))

(defthm type-when-vl-maybe-range-p
  (implies (vl-maybe-range-p x)
           (or (consp x)
               (not x)))
  :rule-classes :compound-recognizer
  :hints(("Goal" :in-theory (enable vl-maybe-range-p))))

(defthm vl-range-count-of-maybe-range
  (implies x
           (< (vl-range-count x) (vl-maybe-range-count x)))
  :rule-classes :linear
  :hints(("Goal"
          :expand ((vl-maybe-range-count x))
          :in-theory (enable vl-maybe-range-some->val))))

(defthm type-when-vl-maybe-datatype-p
  (implies (vl-maybe-datatype-p x)
           (or (consp x)
               (not x)))
  :rule-classes :compound-recognizer
  :hints(("Goal" :in-theory (enable vl-maybe-datatype-p))))

(defthm vl-datatype-count-of-maybe-datatype
  (implies x
           (< (vl-datatype-count x) (vl-maybe-datatype-count x)))
  :rule-classes :linear
  :hints(("Goal"
          :expand ((vl-maybe-datatype-count x))
          :in-theory (enable vl-maybe-datatype-some->val))))

(defthm type-when-vl-dimension-p
  (implies (vl-dimension-p x)
           (or (consp x)
               (and (symbolp x)
                    x
                    (not (equal x t)))))
  :rule-classes :compound-recognizer
  :hints(("Goal" :in-theory (enable vl-dimension-p tag))))

(defthm type-when-vl-maybe-dimension-p
  (implies (vl-maybe-dimension-p x)
           (or (consp x)
               (and (symbolp x)
                    (not (eq x t)))))
  :rule-classes :compound-recognizer
  :hints(("Goal" :in-theory (enable vl-maybe-dimension-p))))

(defthm vl-dimension-count-of-maybe-dimension
  (implies x
           (< (vl-dimension-count x) (vl-maybe-dimension-count x)))
  :rule-classes :linear
  :hints(("Goal"
          :expand ((vl-maybe-dimension-count x))
          :in-theory (enable vl-maybe-dimension-some->val))))



(defthm vl-expr-p-of-cdr-of-hons-assoc-equal-when-vl-atts-p
  (implies (vl-atts-p atts)
           (equal (vl-expr-p (cdr (hons-assoc-equal key atts)))
                  (if (cdr (hons-assoc-equal key atts))
                      t
                    nil)))
  :hints(("Goal"
          :in-theory (enable hons-assoc-equal)
          :induct (hons-assoc-equal key atts))))


(defsection vl-exprlist-fix-basics
  :extension (vl-exprlist-fix)

  ;; BOZO should FTY automatically prove this kind of stuff?

  (defthm vl-exprlist-fix-of-list-fix
    (equal (vl-exprlist-fix (list-fix x))
           (list-fix (vl-exprlist-fix x)))
    :hints(("Goal" :induct (len x))))

  (defthm vl-exprlist-fix-of-rev
    (equal (vl-exprlist-fix (rev x))
           (rev (vl-exprlist-fix x)))
    :hints(("Goal" :induct (len x))))

  (defthm vl-exprlist-fix-of-nthcdr
    (equal (vl-exprlist-fix (nthcdr n x))
           (nthcdr n (vl-exprlist-fix x)))
    :hints(("Goal"
            :in-theory (e/d (nthcdr vl-exprlist-fix default-cdr)
                            (acl2::nthcdr-of-cdr))
            :do-not '(generalize fertilize))))

  (defthm vl-exprlist-fix-of-take
    (equal (take n (vl-exprlist-fix x))
           (if (<= (nfix n) (len x))
               (vl-exprlist-fix (take n x))
             (append (vl-exprlist-fix x)
                     (replicate (- (nfix n) (len x)) nil))))
    :hints(("Goal" :in-theory (enable acl2::take))))

  (defcong vl-exprlist-equiv vl-exprlist-equiv (list-fix x) 1)
  (defcong vl-exprlist-equiv vl-exprlist-equiv (rev x) 1))



; -----------------------------------------------------------------------------
;
;                       ** Generic Expression Stuff **
;
; -----------------------------------------------------------------------------

(define vl-expr->atts ((x vl-expr-p))
  :returns (atts vl-atts-p)
  :parents (vl-expr)
  :short "Get the attributes from any expression."
  (vl-expr-case x
    :vl-special x.atts
    :vl-literal x.atts
    :vl-index x.atts
    :vl-unary x.atts
    :vl-binary x.atts
    :vl-qmark x.atts
    :vl-mintypmax x.atts
    :vl-concat x.atts
    :vl-multiconcat x.atts
    :vl-stream x.atts
    :vl-call x.atts
    :vl-cast x.atts
    :vl-inside x.atts
    :vl-tagged x.atts
    :vl-pattern x.atts
    :vl-eventexpr x.atts)
  ///
  (deffixequiv vl-expr->atts)

  "<p>The following are goofy rules: normally we want to normalize things to
  @('(vl-expr->atts <term>)'), but if @('<term>') is a call of one of the
  particular expression constructors, we'll rewrite the other way so that we
  can simplify it to just whatever @('atts') are being given to the
  constructor.</p>"

  (defthm vl-expr-atts-when-vl-special
    (implies (vl-expr-case x :vl-special)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-special)))
                           (equal (vl-expr->atts x)
                                  (vl-special->atts x)))
                  (implies (syntaxp (not (and (consp x)
                                              (eq (car x) 'vl-special))))
                           (equal (vl-special->atts x)
                                  (vl-expr->atts x))))))

  (defthm vl-expr-atts-when-vl-literal
    (implies (vl-expr-case x :vl-literal)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-literal)))
                           (equal (vl-expr->atts x)
                                  (vl-literal->atts x)))
                  (implies (syntaxp (not (and (consp x)
                                              (eq (car x) 'vl-literal))))
                           (equal (vl-literal->atts x)
                                  (vl-expr->atts x))))))

  (defthm vl-expr-atts-when-vl-index
    (implies (vl-expr-case x :vl-index)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-index)))
                           (equal (vl-expr->atts x)
                                  (vl-index->atts x)))
                  (implies (syntaxp (not (and (consp x)
                                              (eq (car x) 'vl-index))))
                           (equal (vl-index->atts x)
                                  (vl-expr->atts x))))))

  (defthm vl-expr-atts-when-vl-unary
    (implies (vl-expr-case x :vl-unary)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-unary)))
                           (equal (vl-expr->atts x)
                                  (vl-unary->atts x)))
                  (implies (syntaxp (not (and (consp x)
                                              (eq (car x) 'vl-unary))))
                           (equal (vl-unary->atts x)
                                  (vl-expr->atts x))))))

  (defthm vl-expr-atts-when-vl-binary
    (implies (vl-expr-case x :vl-binary)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-binary)))
                           (equal (vl-expr->atts x)
                                  (vl-binary->atts x)))
                  (implies (syntaxp (not (and (consp x)
                                              (eq (car x) 'vl-binary))))
                           (equal (vl-binary->atts x)
                                  (vl-expr->atts x))))))

  (defthm vl-expr-atts-when-vl-qmark
    (implies (vl-expr-case x :vl-qmark)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-qmark)))
                           (equal (vl-expr->atts x)
                                  (vl-qmark->atts x)))
                  (implies (syntaxp (not (and (consp x)
                                              (eq (car x) 'vl-qmark))))
                           (equal (vl-qmark->atts x)
                                  (vl-expr->atts x))))))

  (defthm vl-expr-atts-when-vl-mintypmax
    (implies (vl-expr-case x :vl-mintypmax)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-mintypmax)))
                           (equal (vl-expr->atts x)
                                  (vl-mintypmax->atts x)))
                  (implies (syntaxp (not (and (consp x)
                                              (eq (car x) 'vl-mintypmax))))
                           (equal (vl-mintypmax->atts x)
                                  (vl-expr->atts x))))))

  (defthm vl-expr-atts-when-vl-concat
    (implies (vl-expr-case x :vl-concat)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-concat)))
                           (equal (vl-expr->atts x)
                                  (vl-concat->atts x)))
                  (implies (syntaxp (not (and (consp x)
                                              (eq (car x) 'vl-concat))))
                           (equal (vl-concat->atts x)
                                  (vl-expr->atts x))))))

  (defthm vl-expr-atts-when-vl-multiconcat
    (implies (vl-expr-case x :vl-multiconcat)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-multiconcat)))
                           (equal (vl-expr->atts x)
                                  (vl-multiconcat->atts x)))
                  (implies (syntaxp (not (and (consp x)
                                              (eq (car x) 'vl-multiconcat))))
                           (equal (vl-multiconcat->atts x)
                                  (vl-expr->atts x))))))

  (defthm vl-expr-atts-when-vl-stream
    (implies (vl-expr-case x :vl-stream)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-stream)))
                           (equal (vl-expr->atts x)
                                  (vl-stream->atts x)))
                  (implies (syntaxp (not (and (consp x)
                                              (eq (car x) 'vl-stream))))
                           (equal (vl-stream->atts x)
                                  (vl-expr->atts x))))))

  (defthm vl-expr-atts-when-vl-call
    (implies (vl-expr-case x :vl-call)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-call)))
                           (equal (vl-expr->atts x)
                                  (vl-call->atts x)))
                  (implies (syntaxp (not (and (consp x)
                                              (eq (car x) 'vl-call))))
                           (equal (vl-call->atts x)
                                  (vl-expr->atts x))))))

  (defthm vl-expr-atts-when-vl-cast
    (implies (vl-expr-case x :vl-cast)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-cast)))
                           (equal (vl-expr->atts x)
                                  (vl-cast->atts x)))
                  (implies (syntaxp (not (and (consp x)
                                              (eq (car x) 'vl-cast))))
                           (equal (vl-cast->atts x)
                                  (vl-expr->atts x))))))

  (defthm vl-expr-atts-when-vl-inside
    (implies (vl-expr-case x :vl-inside)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-inside)))
                           (equal (vl-expr->atts x)
                                  (vl-inside->atts x)))
                  (implies (syntaxp (not (and (consp x)
                                              (eq (car x) 'vl-inside))))
                           (equal (vl-inside->atts x)
                                  (vl-expr->atts x))))))

  (defthm vl-expr-atts-when-vl-tagged
    (implies (vl-expr-case x :vl-tagged)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-tagged)))
                           (equal (vl-expr->atts x)
                                  (vl-tagged->atts x)))
                  (implies (syntaxp (not (and (consp x)
                                              (eq (car x) 'vl-tagged))))
                           (equal (vl-tagged->atts x)
                                  (vl-expr->atts x))))))

  (defthm vl-expr-atts-when-vl-pattern
    (implies (vl-expr-case x :vl-pattern)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-pattern)))
                           (equal (vl-expr->atts x)
                                  (vl-pattern->atts x)))
                  (implies (syntaxp (not (and (consp x)
                                              (eq (car x) 'vl-pattern))))
                           (equal (vl-pattern->atts x)
                                  (vl-expr->atts x))))))

  (defthm vl-expr-atts-when-vl-eventexpr
    (implies (vl-expr-case x :vl-eventexpr)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-eventexpr)))
                           (equal (vl-expr->atts x)
                                  (vl-eventexpr->atts x)))
                  (implies (syntaxp (not (and (consp x)
                                              (eq (car x) 'vl-eventexpr))))
                           (equal (vl-eventexpr->atts x)
                                  (vl-expr->atts x))))))

  "<p>For recurring into the atts we may need to know this.</p>"

  (defthm vl-atts-count-of-vl-expr->atts
    (< (vl-atts-count (vl-expr->atts x))
       (vl-expr-count x))
    :hints(("Goal" :in-theory (disable vl-expr->atts)
            :expand ((vl-expr-count x))))
    :rule-classes :linear))

(define vl-expr-update-atts
  :parents (vl-expr)
  :short "Change the attributes of any expression."
  ((x    vl-expr-p "Expression to modify.")
   (atts vl-atts-p "New attributes to install.  Any previous attributes will be
                    overwritten."))
  :returns (new-x vl-expr-p)
  (vl-expr-case x
    :vl-special (change-vl-special x :atts atts)
    :vl-literal (change-vl-literal x :atts atts)
    :vl-index (change-vl-index x :atts atts)
    :vl-unary (change-vl-unary x :atts atts)
    :vl-binary (change-vl-binary x :atts atts)
    :vl-qmark (change-vl-qmark x :atts atts)
    :vl-mintypmax (change-vl-mintypmax x :atts atts)
    :vl-concat (change-vl-concat x :atts atts)
    :vl-multiconcat (change-vl-multiconcat x :atts atts)
    :vl-stream (change-vl-stream x :atts atts)
    :vl-call (change-vl-call x :atts atts)
    :vl-cast (change-vl-cast x :atts atts)
    :vl-inside (change-vl-inside x :atts atts)
    :vl-tagged (change-vl-tagged x :atts atts)
    :vl-pattern (change-vl-pattern x :atts atts)
    :vl-eventexpr (change-vl-eventexpr x :atts atts))
  ///
  (defret vl-expr->atts-of-vl-expr-update-atts
    (equal (vl-expr->atts new-x)
           (vl-atts-fix atts)))

  (defret vl-expr-kind-of-vl-expr-update-atts
    (equal (vl-expr-kind new-x)
           (vl-expr-kind x))))


; -----------------------------------------------------------------------------
;
;                       ** Generic Datatype Stuff **
;
; -----------------------------------------------------------------------------

(define vl-datatype->pdims
  :parents (vl-datatype)
  :short "Get the packed dimensions from any datatype."
  ((x vl-datatype-p))
  :returns (pdims vl-dimensionlist-p)
  (vl-datatype-case x
    :vl-coretype x.pdims
    :vl-struct x.pdims
    :vl-union x.pdims
    :vl-enum x.pdims
    :vl-usertype x.pdims)
  ///
  (deffixequiv vl-datatype->pdims)

  "<p>These are goofy rules: normally we want to normalize things to
  @('(vl-datatype->pdims <term>)'), but if @('<term>') is a call of one of the
  particular datatype constructors, we'll rewrite the other way so that we can
  simplify it to just whatever @('pdims') are being given to the
  constructor.</p>"

  (defthm vl-datatype-pdims-when-vl-coretype
    (implies (vl-datatype-case x :vl-coretype)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-coretype)))
                           (equal (vl-datatype->pdims x)
                                  (vl-coretype->pdims x)))
                  (implies (syntaxp (not (and (consp x)
                                              (eq (car x) 'vl-coretype))))
                           (equal (vl-coretype->pdims x)
                                  (vl-datatype->pdims x))))))

  (defthm vl-datatype-pdims-when-vl-struct
    (implies (vl-datatype-case x :vl-struct)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-struct)))
                           (equal (vl-datatype->pdims x)
                                  (vl-struct->pdims x)))
                  (implies (syntaxp (not (and (consp x)
                                              (eq (car x) 'vl-struct))))
                           (equal (vl-struct->pdims x)
                                  (vl-datatype->pdims x))))))

  (defthm vl-datatype-pdims-when-vl-union
    (implies (vl-datatype-case x :vl-union)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-union)))
                           (equal (vl-datatype->pdims x)
                                  (vl-union->pdims x)))
                  (implies (syntaxp (not (and (consp x)
                                              (eq (car x) 'vl-union))))
                           (equal (vl-union->pdims x)
                                  (vl-datatype->pdims x))))))

  (defthm vl-datatype-pdims-when-vl-enum
    (implies (vl-datatype-case x :vl-enum)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-enum)))
                           (equal (vl-datatype->pdims x)
                                  (vl-enum->pdims x)))
                  (implies (syntaxp (not (and (consp x)
                                              (eq (car x) 'vl-enum))))
                           (equal (vl-enum->pdims x)
                                  (vl-datatype->pdims x))))))

  (defthm vl-datatype-pdims-when-vl-usertype
    (implies (vl-datatype-case x :vl-usertype)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-usertype)))
                           (equal (vl-datatype->pdims x)
                                  (vl-usertype->pdims x)))
                  (implies (syntaxp (not (and (consp x)
                                              (eq (car x) 'vl-usertype))))
                           (equal (vl-usertype->pdims x)
                                  (vl-datatype->pdims x)))))))


(define vl-datatype->udims ((x vl-datatype-p))
  :parents (vl-datatype)
  :short "Get the unpacked dimensions from any datatype."
  :returns (udims vl-dimensionlist-p)
  (vl-datatype-case x
    :vl-coretype x.udims
    :vl-struct x.udims
    :vl-union x.udims
    :vl-enum x.udims
    :vl-usertype x.udims)
  ///
  (deffixequiv vl-datatype->udims)

  (defret vl-dimensionlist-count-of-vl-datatype->pdims/udims
    (< (+ (vl-dimensionlist-count (vl-datatype->pdims x))
          (vl-dimensionlist-count (vl-datatype->udims x)))
       (vl-datatype-count x))
    :hints (("goal"
             :expand ((vl-datatype-count x))))
    :rule-classes :linear)

  "<p>These are goofy rules: normally we want to normalize things to
  @('(vl-datatype->udims <term>)'), but if @('<term>') is a call of one of the
  particular datatype constructors, we'll rewrite the other way so that we can
  simplify it to just whatever @('udims') are being given to the
  constructor.</p>"

  (defthm vl-datatype-udims-when-vl-coretype
    (implies (vl-datatype-case x :vl-coretype)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-coretype)))
                           (equal (vl-datatype->udims x)
                                  (vl-coretype->udims x)))
                  (implies (syntaxp (not (and (consp x)
                                              (eq (car x) 'vl-coretype))))
                           (equal (vl-coretype->udims x)
                                  (vl-datatype->udims x))))))

  (defthm vl-datatype-udims-when-vl-struct
    (implies (vl-datatype-case x :vl-struct)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-struct)))
                           (equal (vl-datatype->udims x)
                                  (vl-struct->udims x)))
                  (implies (syntaxp (not (and (consp x)
                                              (eq (car x) 'vl-struct))))
                           (equal (vl-struct->udims x)
                                  (vl-datatype->udims x))))))

  (defthm vl-datatype-udims-when-vl-union
    (implies (vl-datatype-case x :vl-union)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-union)))
                           (equal (vl-datatype->udims x)
                                  (vl-union->udims x)))
                  (implies (syntaxp (not (and (consp x)
                                              (eq (car x) 'vl-union))))
                           (equal (vl-union->udims x)
                                  (vl-datatype->udims x))))))

  (defthm vl-datatype-udims-when-vl-enum
    (implies (vl-datatype-case x :vl-enum)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-enum)))
                           (equal (vl-datatype->udims x)
                                  (vl-enum->udims x)))
                  (implies (syntaxp (not (and (consp x)

                                              (eq (car x) 'vl-enum))))
                           (equal (vl-enum->udims x)
                                  (vl-datatype->udims x))))))

  (defthm vl-datatype-udims-when-vl-usertype
    (implies (vl-datatype-case x :vl-usertype)
             (and (implies (syntaxp (and (consp x)
                                         (eq (car x) 'vl-usertype)))
                           (equal (vl-datatype->udims x)
                                  (vl-usertype->udims x)))
                  (implies (syntaxp (not (and (consp x)
                                              (eq (car x) 'vl-usertype))))
                           (equal (vl-usertype->udims x)
                                  (vl-datatype->udims x)))))))


(define vl-datatype-update-dims
  :parents (vl-datatype)
  :short "Update the dimensions of any datatype, no matter its kind."
  ((pdims vl-dimensionlist-p   "New packed dimensions to install.")
   (udims vl-dimensionlist-p "New unpacked dimensions to install.")
   (x     vl-datatype-p              "Datatype to update."))
  :returns
  (newx "Updated version of @('x') with new dimensions installed."
        (and (vl-datatype-p newx)
             (eq (vl-datatype-kind newx) (vl-datatype-kind x))))
  (vl-datatype-case x
    :vl-coretype (change-vl-coretype x :pdims pdims :udims udims)
    :vl-struct   (change-vl-struct   x :pdims pdims :udims udims)
    :vl-union    (change-vl-union    x :pdims pdims :udims udims)
    :vl-enum     (change-vl-enum     x :pdims pdims :udims udims)
    :vl-usertype (change-vl-usertype x :pdims pdims :udims udims))
  ///
  (defthm vl-datatype-update-dims-of-own
    (equal (vl-datatype-update-dims (vl-datatype->pdims x)
                                    (vl-datatype->udims x)
                                    x)
           (vl-datatype-fix x)))

  (defthm vl-datatype->pdims-of-vl-datatype-update-dims
    (equal (vl-datatype->pdims (vl-datatype-update-dims pdims udims x))
           (vl-dimensionlist-fix pdims))
    :hints(("Goal" :in-theory (enable vl-datatype->pdims))))

  (defthm vl-datatype->udims-of-vl-datatype-update-dims
    (equal (vl-datatype->udims (vl-datatype-update-dims pdims udims x))
           (vl-dimensionlist-fix udims))
    :hints(("Goal" :in-theory (enable vl-datatype->udims)))))

(define vl-datatype-update-pdims ((pdims vl-dimensionlist-p) (x vl-datatype-p))
  :parents (vl-datatype)
  :enabled t
  :prepwork ((local (in-theory (enable vl-datatype-update-dims))))
  :returns (newx (and (vl-datatype-p newx)
                      (eq (vl-datatype-kind newx) (vl-datatype-kind x))))
  (mbe :logic (vl-datatype-update-dims pdims (vl-datatype->udims x) x)
       :exec  (vl-datatype-case x
                  :vl-coretype (change-vl-coretype x :pdims pdims)
                  :vl-struct (change-vl-struct x :pdims pdims)
                  :vl-union (change-vl-union x :pdims pdims)
                  :vl-enum (change-vl-enum x :pdims pdims)
                  :vl-usertype (change-vl-usertype x :pdims pdims))))

(define vl-datatype-update-udims ((udims vl-dimensionlist-p) (x vl-datatype-p))
  :parents (vl-datatype)
  :enabled t
  :prepwork ((local (in-theory (enable vl-datatype-update-dims))))
  :returns (newx (and (vl-datatype-p newx)
                      (eq (vl-datatype-kind newx) (vl-datatype-kind x))))
  (mbe :logic (vl-datatype-update-dims (vl-datatype->pdims x) udims x)
       :exec  (vl-datatype-case x
                  :vl-coretype (change-vl-coretype x :udims udims)
                  :vl-struct (change-vl-struct x :udims udims)
                  :vl-union (change-vl-union x :udims udims)
                  :vl-enum (change-vl-enum x :udims udims)
                  :vl-usertype (change-vl-usertype x :udims udims))))


; -----------------------------------------------------------------------------
;
;                       ** Miscellaneous Stuff **
;
;  Maybe we can move this elsewhere.
;
; -----------------------------------------------------------------------------

(fty::deflist vl-rangelist
  :elt-type vl-range
  :parents (vl-range))

(define vl-scopeexpr->expr ((x vl-scopeexpr-p))
  :parents (vl-index vl-scopeexpr)
  :short "Promote an @(see vl-scopeexpr) into a proper @(see vl-index) without
          any part select."
  :returns (expr vl-expr-p)
  (make-vl-index :scope x
                 :indices nil
                 :part (make-vl-partselect-none)
                 :atts nil))



(defval *vl-plain-old-logic-type*
  :parents (vl-datatype)
  :short "The @(see vl-datatype) for a plain @('wire') or @('logic') variable."
  :long "<p>It might seem weird to think of a @('wire') as having a datatype;
         see @(see vl-vardecl).</p>"
  (hons-copy (make-vl-coretype :name    :vl-logic
                               :signedp nil
                               :pdims   nil)))

(defval *vl-plain-old-reg-type*
  :parents (vl-datatype)
  :short "The @(see vl-datatype) for a plain @('reg') variable."
  (hons-copy (make-vl-coretype :name    :vl-reg
                               :signedp nil
                               :pdims   nil)))

(defval *vl-plain-old-integer-type*
  :parents (vl-datatype)
  :short "The @(see vl-datatype) for a plain @('integer') variable."
  (hons-copy (make-vl-coretype :name    :vl-integer
                               :signedp t    ;; integer type is signed
                               :pdims    nil ;; Not applicable to integers
                               )))

(defval *vl-plain-old-real-type*
  :parents (vl-datatype)
  :short "The @(see vl-datatype) for a plain @('real') variable."
  (hons-copy (make-vl-coretype :name    :vl-real
                               :signedp nil ;; Not applicable to reals
                               :pdims   nil ;; Not applicable to reals
                               )))

(defval *vl-plain-old-time-type*
  :parents (vl-datatype)
  :short "The @(see vl-datatype) for a plain @('time') variable."
  (hons-copy (make-vl-coretype :name    :vl-time
                               :signedp nil ;; Not applicable to times
                               :pdims    nil ;; Not applicable to times
                               )))

(defval *vl-plain-old-realtime-type*
  :parents (vl-datatype)
  :short "The @(see vl-datatype) for a plain @('realtime') variable."
  (hons-copy (make-vl-coretype :name    :vl-realtime
                               :signedp nil ;; Not applicable to realtimes
                               :pdims    nil ;; Not applicable to realtimes
                               )))


(deftagsum vl-rhs
  :short "A right-hand side for a variable initialization or procedural assignment."
  :long "<p>This is meant to represent things that can come to the right of an
equal sign in a variable declaration or procedural assignment.  This might be a
simple expression, or a @('new') expression.</p>"

    (:vl-rhsexpr
     :short "A simple expression being used as a right-hand-side, e.g., the @('5')
             in something like @('integer foo = 5')."
     :base-name vl-rhsexpr
     ((guts vl-expr-p)))

    (:vl-rhsnew
     :short "A 'new' invocation being used as a right-hand-side."
     :base-name vl-rhsnew
     ((arrsize vl-maybe-expr-p
               "For @('new') arrays, this is the dimension of the array.  For instance,
                in @('arr[0] = new [4]') this would be the @('4').  For
                ordinary @('new') instances of classes, this is just @('nil').")
      (args vl-exprlist-p
            "Arguments to the new class or array."))))

(defoption vl-maybe-rhs vl-rhs)



