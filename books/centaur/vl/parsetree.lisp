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

<p>The <tt>*vl-ops-table*</tt> is an alist that maps our operators (keyword
symbols) to their arities.  For operations that do not have fixed
arities (e.g., concatenation, function calls, ...), we map the operator to
<tt>nil</tt>.</p>

<p>Here is how we represent the various Verilog operators:</p>

<h5>Basic Unary Operators (arity 1)</h5>

<ul>
<li><tt> +        </tt> becomes <tt>:vl-unary-plus</tt></li>
<li><tt> -        </tt> becomes <tt>:vl-unary-minus</tt></li>
<li><tt> !        </tt> becomes <tt>:vl-unary-lognot</tt></li>
<li><tt> ~        </tt> becomes <tt>:vl-unary-bitnot</tt></li>
<li><tt> &amp;    </tt> becomes <tt>:vl-unary-bitand</tt></li>
<li><tt> ~&amp;   </tt> becomes <tt>:vl-unary-nand</tt></li>
<li><tt> |        </tt> becomes <tt>:vl-unary-bitor</tt></li>
<li><tt> ~|       </tt> becomes <tt>:vl-unary-nor</tt></li>
<li><tt> ^        </tt> becomes <tt>:vl-unary-xor</tt></li>
<li><tt> ^~ </tt> or <tt> ~^ </tt> becomes <tt>:vl-unary-xnor</tt></li>
</ul>

<h5>Basic Binary Operators (arity 2)</h5>

<ul>
<li><tt> +        </tt> becomes <tt>:vl-binary-plus</tt></li>
<li><tt> -        </tt> becomes <tt>:vl-binary-minus</tt></li>
<li><tt> *        </tt> becomes <tt>:vl-binary-times</tt></li>
<li><tt> /        </tt> becomes <tt>:vl-binary-div</tt></li>
<li><tt> %        </tt> becomes <tt>:vl-binary-rem</tt></li>
<li><tt> ==       </tt> becomes <tt>:vl-binary-eq</tt></li>
<li><tt> !=       </tt> becomes <tt>:vl-binary-neq</tt></li>
<li><tt> ===      </tt> becomes <tt>:vl-binary-ceq</tt></li>
<li><tt> !==      </tt> becomes <tt>:vl-binary-cne</tt></li>
<li><tt> &amp;&amp; </tt> becomes <tt>:vl-binary-logand</tt></li>
<li><tt> ||       </tt> becomes <tt>:vl-binary-logor</tt></li>
<li><tt> **       </tt> becomes <tt>:vl-binary-power</tt></li>
<li><tt> &lt;     </tt> becomes <tt>:vl-binary-lt</tt></li>
<li><tt> &lt;=    </tt> becomes <tt>:vl-binary-lte</tt></li>
<li><tt> &gt;     </tt> becomes <tt>:vl-binary-gt</tt></li>
<li><tt> &gt;=    </tt> becomes <tt>:vl-binary-gte</tt></li>
<li><tt> &amp;    </tt> becomes <tt>:vl-binary-bitand</tt></li>
<li><tt> |        </tt> becomes <tt>:vl-binary-bitor</tt></li>
<li><tt> ^        </tt> becomes <tt>:vl-binary-xor</tt></li>
<li><tt> ^~ </tt> or <tt> ~^ </tt> becomes <tt>:vl-binary-xnor</tt></li>
<li><tt> &gt;&gt;     </tt> becomes <tt>:vl-binary-shr</tt></li>
<li><tt> &lt;&lt;     </tt> becomes <tt>:vl-binary-shl</tt></li>
<li><tt> &gt;&gt;&gt; </tt> becomes <tt>:vl-binary-ashr</tt></li>
<li><tt> &lt;&lt;&lt; </tt> becomes <tt>:vl-binary-ashl</tt></li>
</ul>

<h5>Basic Ternary Operators (arity 3)</h5>

<ul>
<li><tt>a ? b : c</tt> becomes <tt>:vl-qmark</tt>
      (conditional operator)</li>
<li><tt>a : b : c</tt> becomes <tt>:vl-mintypmax</tt>
      (min/typ/max delay operator)</li>
</ul>

<h5>Selection Operators</h5>

<ul>
<li><tt>foo[1]</tt> becomes <tt>:vl-bitselect</tt> or <tt>:vl-array-index</tt> (arity 2)</li>
<li><tt>foo[3 : 1]</tt> becomes <tt>:vl-partselect-colon</tt> (arity 3)</li>
<li><tt>foo[3 +: 1]</tt> becomes <tt>:vl-partselect-pluscolon</tt> (arity 3)</li>
<li><tt>foo[3 -: 1]</tt> becomes <tt>:vl-partselect-minuscolon</tt> (arity 3)</li>
</ul>

<p>Note that upon parsing, there are no <tt>:vl-array-index</tt> operators;
these must be introduced by the @(see array-indexing) transform.</p>

<h5>Concatenation and Replication Operators</h5>

<ul>
<li><tt>{1, 2, 3, ...}</tt> becomes <tt>:vl-concat</tt> (arity <tt>nil</tt>)</li>
<li><tt>{ 3 { 2, 1 } }</tt> becomes <tt>:vl-multiconcat</tt> (arity 2)</li>
</ul>

<h5>Function Calls</h5>

<ul>
<li><tt>foo(1,2,3)</tt> becomes <tt>:vl-funcall</tt> (arity <tt>nil</tt>)</li>
<li><tt>$foo(1,2,3)</tt> becomes <tt>:vl-syscall</tt> (arity <tt>nil</tt>)</li>
</ul>

<h5>Hierarchical Identifiers</h5>

<p>Note: see @(see vl-hidpiece-p) for some additional discussion about
hierarchical identifiers.</p>

<ul>
<li><tt>foo.bar</tt> becomes <tt>:vl-hid-dot</tt> (arity 2)</li>
<li><tt>foo[3].bar</tt> becomes <tt>:vl-hid-arraydot</tt> (arity 3)</li>
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


(defsection vl-op-p
  :parents (vl-expr-p)
  :short "Recognizer for valid operators."

  :long "<p>@(call vl-op-p) checks that <tt>x</tt> is one of the operators
listed in the @(see *vl-ops-table*).</p>

<p>We prefer to use <tt>vl-op-p</tt> instead of looking up operators directly
in the table, since this way we can disable <tt>vl-op-p</tt> and avoid large
case splits.</p>"

  ;; Per basic testing, assoc is faster than hons-get here.

  (definlined vl-op-p (x)
    (declare (xargs :guard t))
    (if (assoc x *vl-ops-table*)
        t
      nil))

  (local (in-theory (enable vl-op-p)))

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




(defsection vl-op-arity
  :parents (vl-expr-p)
  :short "Look up the arity of an operator."

  :long "<p>@(call vl-op-arity) determines the arity of the operator
<tt>x</tt> by consulting the @(see *vl-ops-table*).  If <tt>x</tt> does
not have a fixed arity (e.g., it might be a function call or concatenation
operation), then we return <tt>nil</tt>.</p>

<p>We prefer to use <tt>vl-op-arity</tt> instead of looking up operators
directly in the table, since this way we can disable <tt>vl-op-arity</tt> and
avoid large case splits.</p>"

  (definlined vl-op-arity (x)
    (declare (xargs :guard (vl-op-p x)))
    (cdr (assoc x *vl-ops-table*)))

  (local (in-theory (enable vl-op-arity)))

  (defthm type-of-vl-op-arity
    (vl-maybe-natp (vl-op-arity x))
    :rule-classes :type-prescription))



(defenum vl-exprtype-p (:vl-signed :vl-unsigned)
  :parents (vl-expr-p)
  :short "Valid types for expressions."
  :long "<p>Each expression should be either <tt>:vl-signed</tt> or
<tt>:vl-unsigned</tt>.  We may eventually expand this to include other types,
such as real and string.</p>")



(defsection vl-maybe-exprtype-p
  :parents (vl-expr-p)
  :short "Recognizer for an @(see vl-exprtype-p) or <tt>nil</tt>."

  :long "<p>As with @(see vl-maybe-exprwidth-p), we use this for the
<tt>sign</tt> fields in our expressions, which allows us to represent
expressions whose signs have not yet been computed.</p>"

  (definlined vl-maybe-exprtype-p (x)
    (declare (xargs :guard t))
    (or (not x)
        (vl-exprtype-p x)))

  (local (in-theory (enable vl-maybe-exprtype-p)))

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
  (origwidth origtype value wasunsized)
  :tag :vl-constint
  :hons t
  :legiblep nil
  :require
  ((posp-of-vl-constint->origwidth
    (posp origwidth)
    :rule-classes :type-prescription)
   (vl-exprtype-p-of-vl-constint->origtype
    (vl-exprtype-p origtype)
    :rule-classes ((:rewrite)
                   (:type-prescription
                    :corollary (implies (force (vl-constint-p x))
                                        (and (symbolp (vl-constint->origtype x))
                                             (not (equal (vl-constint->origtype x) nil))
                                             (not (equal (vl-constint->origtype x) t)))))))
   (natp-of-vl-constint->value
    (natp value)
    :rule-classes :type-prescription)
   (upper-bound-of-vl-constint->value
    (< value (expt '2 origwidth))
    :rule-classes ((:rewrite) (:linear)))
   (booleanp-of-vl-constint->wasunsized
    (booleanp wasunsized)
    :rule-classes :type-prescription))
  :parents (vl-expr-p)
  :short "Representation for constant integer literals with no X or Z bits."

  :long "<p>Constant integers are produced from source code constructs like
<tt>5</tt>, <tt>4'b0010</tt>, and <tt>3'h0</tt>.</p>

<p>The most important part of a constant integer is its <tt>value</tt>, which
even immediately upon parsing has already been determined and is available to
you as an ordinary natural number.  Note that the value of a constant integer
is never negative.  In Verilog there are no negative literals; instead, an
expression like <tt>-5</tt> is basically parsed the same as <tt>-(5)</tt>, so
the negative sign is not part of the literal.  See Section 3.5.1 of the
spec.</p>

<p>The <tt>origwidth</tt> and <tt>origtype</tt> fields are subtle and should
generally <b>not be used</b> unless you think you know what you are doing.
These fields indicate the <i>original</i> width and signedness of the literal
as specified in the source code, e.g., if the source code contains <tt>8'sd
65</tt>, then the origwidth will be 8 and the origtype will be
<tt>:vl-signed.</tt> These fields are subtle because expression sizing will
generally alter the widths and types of subexpressions, so these may not
represent the final widths and types used in expressions.  Instead, the
preferred way to determine a constint's final width and sign is to inspect the
<tt>vl-atom-p</tt> that contains it.</p>

<p>We insist that <tt>0 &lt;= value &lt;= 2^origwidth</tt> for every constant
integer.  If our @(see lexer) encounters something ill-formed like <tt>3'b
1111</tt>, it emits a warning and truncates from the left, as required by
Section 3.5.1 (page 10) of the spec.</p>

<p>Note that in Verilog, unsized integer constants like <tt>5</tt> or
<tt>'b101</tt> have an implementation-dependent size of at least 32 bits.  VL
historically tried to treat such numbers in an abstract way, saying they had
\"integer size\".  But we eventually decided that this was too error-prone and
we now instead act like a 32-bit implementation even at the level of our lexer.
This conveniently makes the width of a constant integer just a positive number.
On the other hand, some expressions may produce different results on 32-bit
versus, say, 64-bit implementations.  Because of this, we added the
<tt>wasunsized</tt> attribute so that we might later statically check for
problematic uses of unsized constants.  This attribute will be set for unsized
constants like <tt>5</tt> and <tt>'b0101</tt>, but not for sized constants like
<tt>4'b0101</tt>.</p>

<p>All constints are automatically created with @(see hons).  This is probably
pretty trivial, but it seems nice.  For instance, the constant integers from
0-32 are probably used thousands of times throughout a design for bit-selects
and wire ranges, so sharing their memory may be useful.</p>")

(defaggregate vl-weirdint
  (origwidth origtype bits wasunsized)
  :tag :vl-weirdint
  :hons t
  :legiblep nil
  :require
  ((posp-of-vl-weirdint->origwidth
    (posp origwidth)
    :rule-classes :type-prescription)
   (vl-exprtype-p-of-vl-weirdint->origtype
    (vl-exprtype-p origtype)
    :rule-classes ((:rewrite)
                   (:type-prescription
                    :corollary (implies (force (vl-weirdint-p x))
                                        (and (symbolp (vl-weirdint->origtype x))
                                             (not (equal (vl-weirdint->origtype x) nil))
                                             (not (equal (vl-weirdint->origtype x) t)))))))
   (vl-bitlist-p-of-vl-weirdint->bits
    (vl-bitlist-p bits))
   (len-of-vl-weirdint->bits
    (equal (len bits) origwidth)
    :rule-classes ((:rewrite)
                   (:type-prescription
                    :corollary (implies (force (vl-weirdint-p x))
                                        (consp (vl-weirdint->bits x)))))))
  :parents (vl-expr-p)
  :short "Representation for constant integer literals with X or Z bits."

  :long "<p>Weird integers are produced by source code constructs like
<tt>1'bz</tt>, <tt>3'b0X1</tt>, and so on.</p>

<p>The <tt>origwidth</tt>, <tt>origtype</tt>, and <tt>wasunsized</tt> fields
are analogous to those from @(see vl-constint-p); see the discussion there for
details.</p>

<p>Unlike a constint, a weirdint does not have a <tt>value</tt> but instead has
a list of <tt>bits</tt>, stored in MSB-first order as a @(see vl-bitlist-p) of
the appropriate width.</p>

<p>Like constinsts, all weirdints are automatically constructed with @(see
hons).  This may not be worthwhile since there are probably usually not too
many weirdints, but by the same reasoning it shouldn't be too harmful.</p>")



(defaggregate vl-string
  (value)
  :tag :vl-string
  :legiblep nil
  :require ((stringp-of-vl-string->value
             (stringp value)
             :rule-classes :type-prescription))
  :parents (vl-expr-p)
  :short "Representation for string literals."

  :long "<p>The <tt>value</tt> of a string literal is an ordinary ACL2 string,
where special sequences like <tt>\\n</tt> and <tt>\\t</tt> have been replaced
with actual newline and tab characters, etc.</p>")



(defaggregate vl-real
  (value)
  :tag :vl-real
  :legiblep nil
  :require ((stringp-of-vl-real->value
             (stringp value)
             :rule-classes :type-prescription))
  :parents (vl-expr-p)
  :short "Representation of real (floating point) literals."

  :long "<p>We currently provide virtually no support for working with real
numbers.  The <tt>value</tt> field simply stores the actual characters found in
the source code, i.e., it might be a string such as <tt>\"3.41e+12\"</tt>.  Do
not rely on this representation; we will almost certainly want to change it as
soon as we want to do anything with real numbers.</p>")



(defaggregate vl-id
  (name)
  :tag :vl-id
  :hons t
  :legiblep nil
  :require ((stringp-of-vl-id->name
             (stringp name)
             :rule-classes :type-prescription))
  :parents (vl-expr-p)
  :short "Representation for simple identifiers."

  :long "<p><tt>vl-id-p</tt> objects are used to represent identifiers used in
expressions, which might be the names of wires, ports, parameters, registers,
and so on.  The <tt>name</tt> of the identifier is a string, which should
generally correspond to one of these items.</p>

<p>A wonderful feature of our representation <tt>vl-id-p</tt> atoms are
guaranteed to not be part of any hierarchical identifier, nor are they the
names of functions or system functions.  See the discussion in @(see
vl-hidpiece-p) for more information.</p>

<p>Note that names created at parse time may include <b>any character</b>
except for whitespace, and will not be empty.  One might eventually add these
restrictions to vl-id tokens, and in other places such as port names, but we
have not done so since this is all relatively obscure.</p>

<p>Like @(see vl-constint-p)s, we automatically create these structures with
@(see hons).  This seems quite nice, since the same names may be used many
times throughout all the expressions in a design.</p>")



(defaggregate vl-hidpiece
  (name)
  :tag :vl-hidpiece
  :legiblep nil
  :require ((stringp-of-vl-hidpiece->name
             (stringp name)
             :rule-classes :type-prescription))
  :parents (vl-expr-p)
  :short "Represents one piece of a hierarchical identifier."

  :long "<p>We represent hierarchical identifiers like
<tt>top.processor[2].reset</tt> as non-atomic expressions.  To represent this
particular expression, we build a @(see vl-expr-p) that is something like
this:</p>

<code>
 (:vl-hid-dot top (:vl-hid-arraydot processor 2 reset))
</code>

<p>In other words, the <tt>:vl-hid-dot</tt> operator is used to join pieces
of a hierarchical identifier, and <tt>:vl-hid-arraydot</tt> is used when
instance arrays are accessed.</p>

<p>To add slightly more precision, our representation is really more like
the following:</p>

<code>
 (:vl-hid-dot (hidpiece \"top\")
              (:vl-hid-arraydot (hidpiece \"processor\")
                                (constint 2)
                                (hidpiece \"reset\")))
</code>

<p>In other words, the individual identifiers used throughout a hierarchical
identifier are actually <tt>vl-hidpiece-p</tt> objects instead of @(see
vl-id-p) objects.</p>

<p>We make this distinction so that in the ordinary course of working with the
parse tree, you can freely assume that any <tt>vl-id-p</tt> you come across
really refers to some module item, and not to some part of a hierarchical
identifier.</p>")



(defaggregate vl-sysfunname
  (name)
  :tag :vl-sysfunname
  :legiblep nil
  :require ((stringp-of-vl-sysfunname->name
             (stringp name)
             :rule-classes :type-prescription))
  :parents (vl-expr-p)
  :short "Represents a system function name."

  :long "<p>We use a custom representation for the names of system functions,
so that we do not confuse them with ordinary @(see vl-id-p) objects.</p>")



(defaggregate vl-funname
  (name)
  :tag :vl-funname
  :legiblep nil
  :require ((stringp-of-vl-funname->name
             (stringp name)
             :rule-classes :type-prescription))
  :parents (vl-expr-p)
  :short "Represents a (non-system) function name."

  :long "<p>We use a custom representation for the names of functions, so that
we do not confuse them with ordinary @(see vl-id-p) objects.</p>")




(defsection vl-atomguts-p
  :parents (vl-expr-p)
  :short "The main contents of a @(see vl-atom-p)."
  :long "<p>The guts of an atom are its main contents.  See @(see vl-expr-p)
for a discussion of the valid types.</p>"

  (defund vl-atomguts-p (x)
    (declare (xargs :guard t))
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
                 (otherwise    (vl-sysfunname-p x)))))

  (local (in-theory (enable vl-atomguts-p)))

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



(defsection vl-fast-id-p
  :parents (vl-atomguts-p vl-id-p)
  :short "Faster version of @(see vl-id-p), given that @(see vl-atomguts-p) is
already known."

  :long "<p>We leave this function enabled and reason about <tt>vl-id-p</tt>
instead.</p>"

  (definline vl-fast-id-p (x)
    (declare (xargs :guard (vl-atomguts-p x)))
    (mbe :logic (vl-id-p x)
         :exec (eq (tag x) :vl-id))))


(defsection vl-fast-constint-p
  :parents (vl-atomguts-p vl-constint-p)
  :short "Faster version of @(see vl-constint-p), given that @(see
vl-atomguts-p) is already known."

  :long "<p>We leave this function enabled and reason about
<tt>vl-constint-p</tt> instead.</p>"

  (definline vl-fast-constint-p (x)
    (declare (xargs :guard (vl-atomguts-p x)))
    (mbe :logic (vl-constint-p x)
         :exec (eq (tag x) :vl-constint))))


(defsection vl-fast-weirdint-p
  :parents (vl-atomguts-p vl-weirdint-p)
  :short "Faster version of @(see vl-weirdint-p), given that @(see
vl-atomguts-p) is already known."

  :long "<p>We leave this function enabled and reason about
<tt>vl-weirdint-p</tt> instead.</p>"

  (definline vl-fast-weirdint-p (x)
    (declare (xargs :guard (vl-atomguts-p x)))
    (mbe :logic (vl-weirdint-p x)
         :exec (eq (tag x) :vl-weirdint))))


(defsection vl-fast-string-p
  :parents (vl-atomguts-p vl-string-p)
  :short "Faster version of @(see vl-string-p), given that @(see
vl-atomguts-p) is already known."

  :long "<p>We leave this function enabled and reason about
<tt>vl-string-p</tt> instead.</p>"

  (definline vl-fast-string-p (x)
    (declare (xargs :guard (vl-atomguts-p x)))
    (mbe :logic (vl-string-p x)
         :exec (eq (tag x) :vl-string))))


(defsection vl-fast-hidpiece-p
  :parents (vl-atomguts-p vl-hidpiece-p)
  :short "Faster version of @(see vl-hidpiece-p), given that @(see
vl-atomguts-p) is already known."

  :long "<p>We leave this function enabled and reason about
<tt>vl-hidpiece-p</tt> instead.</p>"

  (definline vl-fast-hidpiece-p (x)
    (declare (xargs :guard (vl-atomguts-p x)))
    (mbe :logic (vl-hidpiece-p x)
         :exec (eq (tag x) :vl-hidpiece))))


(defsection vl-fast-funname-p
  :parents (vl-atomguts-p vl-funname-p)
  :short "Faster version of @(see vl-funname-p), given that @(see
vl-atomguts-p) is already known."

  :long "<p>We leave this function enabled and reason about
<tt>vl-funname-p</tt> instead.</p>"

  (definline vl-fast-funname-p (x)
    (declare (xargs :guard (vl-atomguts-p x)))
    (mbe :logic (vl-funname-p x)
         :exec (eq (tag x) :vl-funname))))


(defsection vl-fast-sysfunname-p
  :parents (vl-atomguts-p vl-sysfunname-p)
  :short "Faster version of @(see vl-sysfunname-p), given that @(see
vl-atomguts-p) is already known."

  :long "<p>We leave this function enabled and reason about
<tt>vl-sysfunname-p</tt> instead.</p>"

  (definline vl-fast-sysfunname-p (x)
    (declare (xargs :guard (vl-atomguts-p x)))
    (mbe :logic (vl-sysfunname-p x)
         :exec (eq (tag x) :vl-sysfunname))))


(defaggregate vl-atom
  (guts finalwidth finaltype)
  :tag :vl-atom
  :legiblep nil
  :require
  ((vl-atomguts-p-of-vl-atom->guts
    (vl-atomguts-p guts))
   (vl-maybe-natp-of-vl-atom->finalwidth
    (vl-maybe-natp finalwidth)
    :rule-classes :type-prescription)
   (vl-maybe-exprtype-p-of-vl-atom->finaltype
    (vl-maybe-exprtype-p finaltype)
    :rule-classes ((:rewrite)
                   (:type-prescription
                    :corollary (implies (force (vl-atom-p x))
                                        (and (symbolp (vl-atom->finaltype x))
                                             (not (equal (vl-atom->finaltype x) t))))))))
  :parents (vl-expr-p)
  :short "Representation of atomic expressions."
  :long "<p>See the discussion in @(see vl-expr-p).</p>")

(deflist vl-atomlist-p (x)
  (vl-atom-p x)
  :guard t
  :elementp-of-nil nil
  :parents (vl-expr-p))



(defaggregate vl-nonatom
  (op atts args finalwidth finaltype)
  :tag :vl-nonatom
  :legiblep nil
  :require
  ((vl-op-p-of-vl-nonatom->op
    (vl-op-p op)
    :rule-classes ((:rewrite)
                   (:type-prescription
                    ;; I previously forced this, but it got irritating because it
                    ;; kept screwing up termination proofs.  Consider case-split?
                    :corollary (implies (vl-nonatom-p x)
                                        (and (symbolp (vl-nonatom->op x))
                                             (not (equal (vl-nonatom->op x) t))
                                             (not (equal (vl-nonatom->op x) nil)))))))
   (vl-maybe-natp-of-vl-nonatom->finalwidth
    (vl-maybe-natp finalwidth)
    :rule-classes :type-prescription)
   (vl-maybe-exprtype-p-of-vl-nonatom->finaltype
    (vl-maybe-exprtype-p finaltype)
    :rule-classes ((:rewrite)
                   (:type-prescription
                    ;; I previously forced this, but maybe that's a bad idea for
                    ;; the same reasons as vl-op-p-of-vl-nonatom->op?
                    :corollary (implies (vl-nonatom-p x)
                                        (and (symbolp (vl-nonatom->finaltype x))
                                             (not (equal (vl-nonatom->finaltype x) t))))))))
  :parents (vl-expr-p)
  :short "Structural validity of non-atomic expressions."
  :long "<p>This is only a simple structural check, and does not imply
<tt>vl-expr-p</tt>.  See @(see vl-expr-p) for details.</p>")

(defthm acl2-count-of-vl-nonatom->args
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
  :rule-classes ((:rewrite) (:linear)))




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
     <tt>$display</tt>).</li>
</ul>

<p>The last three of these are probably not things you would ordinarily think
of as atomic expressions.  However, by accepting them as atomic expressions, we
are able to achieve the straightforward recursive structure we desire.</p>

<p>In addition to their guts, each @(see vl-atom-p) includes a</p>

<ul>
 <li><tt>finalwidth</tt>, which is a @(see vl-maybe-natp-p), and</li>
 <li><tt>finaltype</tt>, which is a @(see vl-maybe-exprtype-p).</li>
</ul>

<p>Typically, when we have just parsed the modules, these fields are left
<tt>nil</tt>: their values are only filled in during our expression typing and
sizing computations.</p>

<h5>Non-Atomic Expressions</h5>

<p>All non-atomic expressions share a common cons structure, and @(see
vl-nonatom-p) is a simple, non-recursive, structural validity check to see if
this structure is obeyed at the top level.  Note that @(see vl-nonatom-p) is
<b>not</b> sufficient to ensure that the object is a valid expression, because
additional constraints (e.g., arity checks, recursive well-formedness) are
imposed by <tt>vl-expr-p</tt>.</p>

<p>Like atomic expressions, each <tt>vl-nonatom-p</tt> includes
<tt>finalwidth</tt> and <tt>finaltype</tt> fields, which are <tt>nil</tt> upon
parsing and may later be filled in by our expression typing and sizing
computations.  To be accepted by <tt>vl-nonatom-p</tt>, the <tt>finalwidth</tt>
and <tt>finaltype</tt> must be valid @(see vl-maybe-natp) and @(see
vl-maybe-exprtype-p) objects, respectively.</p>

<p>Additionally, each non-atomic expression includes:</p>

<ul>

<li><tt>op</tt>, the operation being applied.  For structural validity,
<tt>op</tt> must be one of the known operators found in @(see
*vl-ops-table*).</li>

<li><tt>args</tt>, the arguments the operation is being applied to.  No
structural constraints are imposed upon <tt>args</tt>.</li>

<li><tt>atts</tt>, which represent any attributes written in the <tt>(* foo =
bar, baz *)</tt> style that Verilog-2005 permits.  No structural constraints
are placed upon <tt>atts</tt>.</li>

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


(defsection vl-fast-atom-p
  :parents (vl-atom-p vl-expr-p)
  :short "Faster version of @(see vl-atom-p), given that @(see vl-expr-p) is
already known."

  :long "<p>We leave this function enabled and reason about <tt>vl-atom-p</tt>
instead.</p>"

  (definline vl-fast-atom-p (x)
    (declare (xargs :guard (vl-expr-p x)))
    (mbe :logic (vl-atom-p x)
         :exec (eq (tag x) :vl-atom))))


(defsection vl-expr->finalwidth
  :parents (vl-expr-p)
  :short "Get the <tt>finalwidth</tt> from an expression."

  :long "<p>See @(see vl-expr-p) for a discussion of widths.  The result is a
@(see vl-maybe-exprwidth-p).</p>"

  (definlined vl-expr->finalwidth (x)
    (declare (xargs :guard (vl-expr-p x)
                    :verify-guards nil))
    (if (eq (tag x) :vl-atom)
        (vl-atom->finalwidth x)
      (vl-nonatom->finalwidth x)))

  (local (in-theory (enable vl-expr->finalwidth
                            vl-expr-p)))

  (verify-guards vl-expr->finalwidth)

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



(defsection vl-expr->finaltype
  :parents (vl-expr-p)
  :short "Get the <tt>finaltype</tt> from an expression."

  :long "<p>See @(see vl-expr-p) for a discussion of types.  The result
is a @(see vl-maybe-exprtype-p).</p>"

  (definlined vl-expr->finaltype (x)
    (declare (xargs :guard (vl-expr-p x)
                    :verify-guards nil))
    (if (eq (tag x) :vl-atom)
        (vl-atom->finaltype x)
      (vl-nonatom->finaltype x)))

  (local (in-theory (enable vl-expr-p vl-expr->finaltype)))

  (verify-guards vl-expr->finaltype)

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
  :short "Representation of <tt>(* foo = 3, baz *)</tt> style attributes."

  :long "<p>Verilog 2005 allows many constructs, (e.g., module instances, wire
declarations, assignments, subexpressions, and so on) to be annotated with
<i>attributes</i>.  Each individual attribute can either be a single key with
no value (e.g., <tt>baz</tt> above), or can have the form <tt>key = value</tt>.
The keys are always identifiers, and the values (if provided) are
expressions.</p>

<p>We represent attributes as alists mapping keys to their values.  We use
ordinary ACL2 strings to represent the keys.  Each value is represented by a
@(see vl-expr-p) object, and keys with no values are bound to <tt>nil</tt>
instead.</p>

<h3>Attributes Used by VL</h3>

<p><b>BOZO</b> this list may not be complete.  Try to keep it up to date.</p>

<dl>

<dt>Modules</dt>

<dd><tt>VL_HANDS_OFF</tt> indicates that the module is special and should be
left alone by transformations.  It is generally intended to be used for
built-in VL modules like <tt>VL_1_BIT_FLOP</tt> and
<tt>VL_1_BIT_LATCH</tt>.</dd>


<dt>Expressions</dt>

<dd><tt>VL_ORIG_EXPR</tt>, with some value, is added to many expressions in the
@(see origexprs) transformation.  It allows us to remember the \"original
version\" of the expression before simplification has taken place.</dd>

<dd><tt>VL_ZERO_EXTENSION</tt> is added when we create certain zero-extension
expressions, mainly to pad operands during @(see ctxsize).</dd>


<dt>Net Declarations</dt>

<dd><tt>VL_IMPLICIT</tt>, with no value, is given to implicitly declared wires
by @(see make-implicit-wires).  This attribute also plays a role in @(see
typo-detection).</dd>

<dd><tt>VL_PORT_IMPLICIT</tt>, with no value, is given to wires that are
declared to be ports (i.e., <tt>input a;</tt>) but which are not also declared
to be wires (i.e., <tt>wire a;</tt>) by @(see make-port-wires)</dd>

<dd><tt>VL_UNUSED</tt> and <tt>VL_MAYBE_UNUSED</tt> may be added by @(see
use-set) when a wire appears to be unused.</dd>

<dd><tt>VL_UNSET</tt> and <tt>VL_MAYBE_UNSET</tt> may be added by @(see
use-set) when a wire appears to be unset.</dd>

<dd><tt>VL_ACTIVE_HIGH</tt> and <tt>VL_ACTIVE_LOW</tt> may be declared by
the user or inferred in the cross-active transformation.</dd>

<dd><tt>VL_CONVERTED_REG</tt> may be attached during latch/flop inference,
when a <tt>reg</tt> is turned into a <tt>wire</tt>.</dd>


<dt>Port Declarations</dt>

<dd><tt>VL_ACTIVE_HIGH</tt> and <tt>VL_ACTIVE_LOW</tt> may be declared by
the user or inferred in the cross-active transformation.</dd>


<dt>Assignments</dt>

<dd><tt>TRUNC_<i>WIDTH</i></tt> attributes are given to assignment statements which
are involve implicit truncations, by @(see trunc).  <b>BOZO</b> probably change
to <tt>VL_TRUNC = width</tt> format.</dd>


<dt>Gate Instances</dt>

<dd><tt>VL_FROM_GATE_ARRAY</tt>, with no value, is given to gate instances that
are the result of splitting an array such as <tt>buf foo [13:0] (o, i);</tt> by
@(see replicate).  This property is also given to module instances as described
below.</dd>

<dd><tt>VL_GATE_REDUX</tt>, with no value, is added when, e.g., <tt>pullup</tt>
and <tt>pulldown</tt> gates are converted into <tt>buf</tt> gates, during @(see
gateredux).  It is also given to certain module instances as described
below.</dd>

<dd><tt>VL_GATESPLIT</tt> is added when certain gates are simplified, e.g.,
when we split <tt>not(o1,o2,...,on, i);</tt> into <tt>not(o1,i);</tt>,
<tt>not(o2,i)</tt>, ..., <tt>not(on, i);</tt> in @(see gatesplit).  <b>BOZO</b>
make this annotation more consistent.</dd>


<dt>Module Instances</dt>

<dd><tt>VL_FROM_GATE_ARRAY</tt>, with no value, is given to module instances that
are the result of splitting an array such as <tt>mymod foo [13:0] (o, i);</tt>
by @(see replicate).  This property is also given to gate instances as described
above.  <b>BOZO</b> probably switch this to VL_FROM_MOD_ARRAY.</dd>

<dd><tt>VL_GATE_REDUX</tt>, with no value, is given to module instances that
are the result of converting gates such as <tt>bufif0</tt>, <tt>notif1</tt>,
<tt>pmos</tt>, etc., into module instances.  It is also given to certain gate
instances as described above.</dd>


<dt>Plain Arguments</dt>

<dd><tt>VL_ACTIVE_HIGH</tt> or <tt>VL_ACTIVE_LOW</tt> may be added during
@(see argresolve), and indicate whether the corresponding formal is considered
active high or low.</dd>

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
    (implies (and (force (vl-atts-p x))
                  (force (vl-atts-p y)))
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
    :hints(("Goal" :induct (hons-assoc-equal key atts))))

  (defthm vl-atts-p-of-vl-remove-keys
    (implies (force (vl-atts-p x))
             (vl-atts-p (vl-remove-keys keys x)))
    :hints(("Goal" :induct (len x)))))





(defsection vl-exprlist-p

  (deflist vl-exprlist-p (x)
    (vl-expr-p x)
    :elementp-of-nil nil
    :verify-guards nil
    :already-definedp t
    :parents (modules))

  ;; These are useful for seeing that arguments exist.
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




(defsection vl-maybe-expr-p
  :parents (modules vl-expr-p)
  :short "Representation for a @(see vl-expr-p) or <tt>nil</tt>."
  :long "<p>This is a basic option type for expressions.</p>"

  (definlined vl-maybe-expr-p (x)
    (declare (xargs :guard t))
    (or (not x)
        (vl-expr-p x)))

  (local (in-theory (enable vl-maybe-expr-p)))

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
  (msb lsb)
  :tag :vl-range
  :legiblep nil
  :require ((vl-expr-p-of-vl-range->msb (vl-expr-p msb))
            (vl-expr-p-of-vl-range->lsb (vl-expr-p lsb)))
  :parents (modules)
  :short "Representation of ranges on wire declarations, instance array
declarations, and so forth."

  :long "<p>Ranges are discussed in Section 7.1.5.</p>

<p>Ranges in declarations and array instances look like <tt>[msb:lsb]</tt>, but
do not confuse them with part-select expressions which have the same
syntax.</p>

<p>The expressions in the <tt>msb</tt> and <tt>lsb</tt> positions are expected
to resolve to constants.  Note that the parser does not try to simplify these
expressions, but some simplification is performed in transformations such as
@(see rangeresolve) and @(see unparameterization).</p>

<p>Even after the expressions have become constants, the Verilog specification
does not require <tt>msb</tt> to be greater than <tt>lsb</tt>, and neither
index is required to be zero.  In fact, even negative indicies seem to be
permitted, which is quite amazing and strange.</p>

<p>While we do not impose any restrictions in <tt>vl-range-p</tt> itself, some
transformations expect the indices to be resolved to integers.  However, we now
try to support the use of both ascending and descending ranges.</p>")



(defsection vl-maybe-range-p
  :parents (modules vl-range-p)
  :short "Representation for a @(see vl-range-p) or <tt>nil</tt>."
  :long "<p>This is a basic option type for ranges.</p>"

  (definlined vl-maybe-range-p (x)
    (declare (xargs :guard t))
    (or (not x)
        (vl-range-p x)))

  (local (in-theory (enable vl-maybe-range-p)))

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
  (name expr loc)
  :tag :vl-port
  :require ((vl-maybe-string-p-of-vl-port->name
             (vl-maybe-string-p name)
             :rule-classes
             ((:type-prescription)
              (:rewrite :corollary
                        ;; BOZO horrible gross stupid hack because type rule isn't forcing
                        (implies (force (vl-port-p x))
                                 (equal (stringp (vl-port->name x))
                                        (if (vl-port->name x)
                                            t
                                          nil))))))
            (vl-maybe-expr-p-of-vl-port->expr
             (vl-maybe-expr-p expr))
            (vl-location-p-of-vl-port->loc
             (vl-location-p loc)))
  :legiblep nil
  :parents (modules)
  :short "Representation of a single Verilog port."

  :long "<h3>Introduction to Ports</h3>

<p>Ports are described in Section 12.3 of the standard.  In simple cases, a
module's ports look like this:</p>

<code>
module mod(a,b,c) ;  &lt;-- ports are a, b, and c
  ...
endmodule
</code>

<p>However, an alternate (and less repetitive) syntax can be used instead:</p>

<code>
module mod(
  input [3:0] a;   &lt; ports are a, b, and c
  input b;
  output c;
) ;
   ...
endmodule
</code>

<p>More complex ports are also possible, e.g., in this example,</p>

<code>
module mod (a, .b(w), c[3:0], .d(c[7:4])) ;
  input a;
  input w;
  input [7:0] c;
  ...
endmodule
</code>

<p>the ports have external names which are distinct from their internal
wiring.</p>


<h3>Representation of Ports</h3>

<p>The <tt>name</tt> of every port is a @(see vl-maybe-string-p).  We think of
this name as the \"externally visible\" name of the port.</p>

<p>The <tt>expr</tt> of every port is a @(see vl-maybe-expr-p) that determines
how the port is wired internally within the module.</p>

<p>The <tt>loc</tt> for each port is a @(see vl-location-p) that says where
the port came from in the Verilog source code.</p>

<p>For instance, in the \"complex\" example above, the names of the ports would
be represented, respectively, as: <tt>\"a\"</tt>, <tt>\"b\"</tt>,
<tt>nil</tt> (i.e., this port has no externally visible name), and
<tt>\"d\"</tt>.  Meanwhile, the first two ports are internally wired to
<tt>a</tt> and <tt>w</tt>, respectively, while the third and fourth ports
collectively specify the bits of <tt>c</tt>.</p>


<h3>Using Ports</h3>

<p>It is generally best to <b>avoid using port names</b> except perhaps for
things like error messages.  Why?  As shown above, some ports might not have
names, and even when a port does have a name, it does not necessarily
correspond to any wires in the module.  But because these cases are relatively
rare, port-name based code is particularly likely to work for test cases and
then fail later when more complex examples are encountered.</p>

<p>Usually you should not need to deal with port names.  The @(see argresolve)
transform converts module instances that use named arguments into their plain
equivalents, and once this has been done there really isn't much reason to have
port names anymore.  Instead, you can work directly with the port's
expression.</p>

<p>Our <tt>vl-port-p</tt> structures do not restrict the kinds of expressions
that may be used as the internal wiring, but we generally expect that each such
expression should satisfy @(see vl-portexpr-p).</p>

<p>A \"blank\" port expression (represented by <tt>nil</tt>) means the port is
not connected to any wires within the module.  Our @(see argresolve) transform
will issue non-fatal @(see warnings) if any non-blank arguments are connected
to blank ports, or if blank arguments are connected to non-blank ports.  It is
usually not hard to support blank ports in other transformations.</p>

<p>The direction of a port can most safely be obtained by @(see
vl-port-direction).  Note that directions are not particularly reliable in
Verilog: one can assign to a input or read from an output, and in simulators
like Cadence this can actually impact values on wires in the supermodule as if
the ports have no buffers.  We call this \"backflow.\" <b>BOZO</b> eventually
implement a comprehensive approach to detecting and dealing with backflow.</p>

<p>The width of a port can be determined after expression sizing has been
performed by examining the width of the port expression.  See @(see selfsize)
and @(see ctxsize) for details.</p>")

(deflist vl-portlist-p (x)
  (vl-port-p x)
  :elementp-of-nil nil
  :parents (modules))

(defprojection vl-portlist->exprs (x)
  (vl-port->expr x)
  :guard (vl-portlist-p x)
  :nil-preservingp t
  :parents (vl-portlist-p))

(defthm vl-exprlist-p-of-vl-portlist->exprs
  (implies (force (vl-portlist-p x))
           (equal (vl-exprlist-p (vl-portlist->exprs x))
                  (not (member nil (vl-portlist->exprs x)))))
  :hints(("Goal" :induct (len x))))

(defthm vl-exprlist-p-of-remove-equal-of-vl-portlist->exprs
  (implies (force (vl-portlist-p x))
           (vl-exprlist-p (remove-equal nil (vl-portlist->exprs x))))
  :hints(("Goal" :induct (len x))))

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
represent these directions with the keyword <tt>:vl-input</tt>,
<tt>:vl-output</tt>, and <tt>:vl-inout</tt>, respectively.</p>

<p>In our @(see argresolve) transformation, directions are also assigned to all
arguments of gate instances and most arguments of module instances.  See our
@(see vl-plainarg-p) structures for more information.</p>")



(defsection vl-maybe-direction-p
  :parents (modules)
  :short "Representation for a @(see vl-direction-p) or <tt>nil</tt>."
  :long "<p>This is a basic option type for directions.</p>"

  (definlined vl-maybe-direction-p (x)
    (declare (xargs :guard t))
    (or (not x)
        (vl-direction-p x)))

  (local (in-theory (enable vl-maybe-direction-p)))

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
  (name dir signedp range loc atts)
  :tag :vl-portdecl
  :legiblep nil
  :require ((stringp-of-vl-portdecl->name
             (stringp name)
             :rule-classes :type-prescription)
            (vl-direction-p-of-vl-portdecl->dir
             (vl-direction-p dir))
            (booleanp-of-vl-portdecl->signedp
             (booleanp signedp)
             :rule-classes :type-prescription)
            (vl-maybe-range-p-of-vl-portdecl->range
             (vl-maybe-range-p range))
            (vl-location-p-vl-portdecl->loc
             (vl-location-p loc))
            (vl-atts-p-of-vl-portdecl->atts
             (vl-atts-p atts)))
  :parents (modules)
  :short "Representation of Verilog port declarations."

  :long "<p>Port declarations ascribe certain properties (direction,
signedness, size, and so on) to the ports of a module.  Here is an example:</p>

<code>
module m(a, b) ;
  input [3:0] a ;  // &lt;--- port declaration
  ...
endmodule
</code>

<p>Although Verilog allows multiple ports to be declared simultaneously, i.e.,
<tt>input a, b ;</tt>, our parser splits these merged declarations to create
separate <tt>vl-portdecl-p</tt> objects for each port.  Because of this, every
<tt>vl-portdecl-p</tt> has only a single name.</p>

<p>Port declarations are described in Section 12.3.3 of the specification.</p>

<p>The <tt>name</tt> of the port is an ordinary string, which should agree
with the name of some port in the module.  (<b>BOZO</b> Is that
the external or internal name?  Oh my God...)</p>

<p>The <tt>direction</tt> of the port is a @(see vl-direction-p) that says
whether this port is an input, output, or bidirectional port.</p>

<p>The <tt>signedp</tt> flag indicates whether the <tt>signed</tt> keyword was
present in the declaration.</p>

<p><b>Warning</b>: Note that per page 175, port declarations and net/reg
declarations must be checked against one another: if either declaration
includes the <tt>signed</tt> keyword, then both are to be considered signed.
The parser DOES NOT do this cross-referencing automatically; instead the @(see
portdecl-sign) transformation needs to be run.</p>

<p>The <tt>range</tt> indicates how whether the input is a vector and, if so,
how large the input is.  Per page 174, if there is also a net declaration then
the range must agree.  This is checked in @(see vl-overlap-compatible-p) as
part of our notion of @(see reasonable) modules.</p>

<p>The <tt>loc</tt> is a @(see vl-location-p) that describes where the port
was declared in the source code.</p>

<p>The <tt>atts</tt> are any attribute (see @(see vl-atts-p)) associated with
this declaration.</p>

<h4>A Note about Port Types</h4>

<p>If you look at the grammar for port declarations, you will see that you
can also do things like:</p>

<code>
input wire a;
input supply0 b;
</code>

<p>And so on.  For some time, our <tt>vl-port-p</tt> structures included a
<tt>type</tt> field.  However, upon a closer reading of the specification,
we have learned that the proper way to handle these is to simultaneously
introduce a @(see vl-netdecl-p) alongside the <tt>vl-portdecl-p</tt> that
we would ordinarily create for a port declaration.  See, e.g., the second
paragraph from the bottom on Page 174.</p>")

(deflist vl-portdecllist-p (x)
  (vl-portdecl-p x)
  :elementp-of-nil nil
  :parents (modules))



(defaggregate vl-gatedelay
  (rise fall high)
  :tag :vl-gatedelay
  :legiblep nil
  :require ((vl-expr-p-of-vl-gatedelay->rise       (vl-expr-p rise))
            (vl-expr-p-of-vl-gatedelay->fall       (vl-expr-p fall))
            (vl-maybe-expr-p-of-vl-gatedelay->high (vl-maybe-expr-p high)))
  :parents (modules)
  :short "Representation of delay expressions."

  :long "<p><b>WARNING</b>.  We have not paid much attention to delays, and our
transformations probably do not handle them properly.</p>

<p>Delays are mainly discussed in 7.14 and 5.3, with some other
discussion in 6.13 and the earlier parts of Section 7.  In short:</p>

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
left as <tt>nil</tt>.  Simulators that care about this will need to carefully
review the rules for correctly computing these delays.</p>")



(defsection vl-maybe-gatedelay-p
  :parents (modules)
  :short "Representation for a @(see vl-gatedelay-p) or <tt>nil</tt>."
  :long "<p>This is a basic option type for gatedelays.</p>"

  (definlined vl-maybe-gatedelay-p (x)
    (declare (xargs :guard t))
    (or (not x)
        (vl-gatedelay-p x)))

  (local (in-theory (enable vl-maybe-gatedelay-p)))

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
  (zero one)
  :tag :vl-gatestrength
  :parents (modules)
  :legiblep nil
  :require ((vl-dstrength-p-of-vl-gatestrength->zero
             (vl-dstrength-p zero))
            (vl-dstrength-p-of-vl-gatestrength->one
             (vl-dstrength-p one)))

  :short "Representation of strengths for a assignment statements, gate
instances, and module instances."

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
  :short "Representation for a @(see vl-gatestrength-p) or <tt>nil</tt>."
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



(defsection vl-maybe-cstrength-p
  :parents (modules)
  :short "Representation for a @(see vl-cstrength-p) or <tt>nil</tt>."
  :long "<p>This is a basic option type for cstrengths.</p>"

  (defund vl-maybe-cstrength-p (x)
    (declare (xargs :guard t))
    (or (not x)
        (vl-cstrength-p x)))

  (local (in-theory (enable vl-maybe-cstrength-p)))

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
  (lvalue expr strength delay loc atts)
  :tag :vl-assign
  :legiblep nil
  :require ((vl-expr-p-of-vl-assign->lvalue
             (vl-expr-p lvalue))
            (vl-expr-p-of-vl-assign->expr
             (vl-expr-p expr))
            (vl-maybe-gatedelay-p-of-vl-assign->delay
             (vl-maybe-gatedelay-p delay))
            (vl-maybe-gatestrength-p-of-vl-assign->strength
             (vl-maybe-gatestrength-p strength))
            (vl-location-p-of-vl-assign->loc
             (vl-location-p loc))
            (vl-atts-p-of-vl-assign->atts
             (vl-atts-p atts)))
  :parents (modules)
  :short "Representation of a continuous assignment statement."

  :long "<p>In the Verilog sources, continuous assignment statements can take
two forms, as illustrated below.</p>

<code>
module m (a, b, c) ;
  wire w1 = a &amp; b ;     // &lt;-- continuous assignment in a declaration
  wire w2;
  assign w2 = w1;       // &lt;-- continuous assignment
endmodule
</code>

<p>Regardless of which form is used, the @(see parser) generates a
<tt>vl-assign-p</tt> object.  Note that the following is also legal
Verilog:</p>

<code>
  assign foo = 1, bar = 2;
</code>

<p>But in such cases, the parser will create two <tt>vl-assign-p</tt> objects,
one to represent the assignment to <tt>foo</tt>, and the other to represent the
assignment to <tt>bar</tt>.  Hence, each <tt>vl-assign-p</tt> represents only a
single assignment.</p>


<h4>Lvalue</h4>

<p>The <tt>lvalue</tt> field must be an expression, and represents the location
being assigned to.  The formal syntax definition for Verilog only permits
lvalues to be:</p>

<ul>
 <li>identifiers,</li>
 <li>bit- or part-selects, and</li>
 <li>concatenations of the above.</li>
</ul>

<p>Furthermore, from Table 6.1, (p. 68), we find that only <tt>net</tt>
declarations are permitted in continuous assignments; <tt>reg</tt>s,
<tt>integer</tt>s, and other variables must be assigned only using procedural
assignments.  We have experimentally verified (see <tt>test-assign.v</tt>) that
Cadence enforces these rules.</p>

<p>Our parser does impose these syntactic restrictions, but in
<tt>vl-assign-p</tt> we are perhaps overly permissive, and we only require that
the <tt>lvalue</tt> is an expression.  Even so, some transforms may cause fatal
warnings if these semantic restrictions are violated, so one must be careful
when generating assignments.</p>

<h4>Expr</h4>

<p>The <tt>expr</tt> is the expression being assigned to this lvalue.  We do
not in any way restrict the expression, nor have we found any restrictions
discussed in the Verilog standard.  Even so, it seems there must be some
limits.  For instance, what does it mean to assign, say, a
minimum/typical/maximum delay expression?  For these sorts of reasons, some
transforms may wish to only permit a subset of all expressions here.</p>


<h4>Delay</h4>

<p>The <tt>delay</tt> for a continuous assignment is discussed in 6.1.3 (page
71), and specifies how long it takes for a change in the value of the
right-hand side to be propagated into the lvalue.  We represent the delay using
a @(see vl-maybe-gatedelay-p); if the <tt>delay</tt> is <tt>nil</tt>,
it means that no delay was specified.</p>

<p>Note (6.1.3) that when delays are provided in the combined declaration and
assignment statement, e.g., </p>

<code>
  wire #10 a = 1, b = 2;
</code>

<p>that the delay is to be associated with each assignment, and NOT with the
net declaration for <tt>a</tt>.  Net delays are different than assignment
delays; see @(see vl-netdecl-p) for additional discussion.</p>

<p><b>Warning:</b> Although the parser is careful to handle the delay
correctly, we are generally uninterested in delays and our transforms may not
properly preserve them.</p>

<p><b>BOZO</b> Presumably the default delay is zero?  Haven't seen that yet,
though.</p>

<h4>Strength</h4>

<p>Strengths on continuous assignments are discussed in 6.1.4.  We represent the
strength using a @(see vl-maybe-gatestrength-p).  If a strength is not provided,
the parser sets this to <tt>nil</tt>.</p>

<p><b>Warning:</b> Although the parser is careful to handle the strength
correctly, we are generally uninterested in strengths and our transforms may not
properly preserve them.</p>

<h4>Loc, Atts</h4>

<p>The <tt>loc</tt> is the location of this continuous assignment in the source
code, and is useful for producing error messages; see @(see vl-location-p).</p>

<p>The <tt>atts</tt> are any Verilog-2005 style attributes associated with this
assignment; see @(see vl-atts-p).  We mostly ignore attributes, but we may
sometimes add them as annotations.</p>")

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



(defsection vl-maybe-netdecltype-p
  :parents (modules)
  :short "Representation for a @(see vl-netdecltype-p) or <tt>nil</tt>."
  :long "<p>This is a basic option type for netdecltypes.</p>"

  (definlined vl-maybe-netdecltype-p (x)
    (declare (xargs :guard t))
    (or (not x)
        (vl-netdecltype-p x)))

  (local (in-theory (enable vl-maybe-netdecltype-p)))

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
  (name type range arrdims atts vectoredp scalaredp signedp delay cstrength loc)
  :tag :vl-netdecl
  :legiblep nil
  :require ((stringp-of-vl-netdecl->name
             (stringp name)
             :rule-classes :type-prescription)
            (vl-netdecltype-p-of-vl-netdecl->type
             (vl-netdecltype-p type))
            (vl-maybe-range-p-of-vl-netdecl->range
             (vl-maybe-range-p range))
            (vl-rangelist-p-of-vl-netdecl->arrdims
             (vl-rangelist-p arrdims))
            (vl-atts-p-of-vl-netdecl->atts
             (vl-atts-p atts))
            (booleanp-of-vl-netdecl->vectoredp
             (booleanp vectoredp)
             :rule-classes :type-prescription)
            (booleanp-of-vl-netdecl->scalaredp
             (booleanp scalaredp)
             :rule-classes :type-prescription)
            (booleanp-of-vl-netdecl->signedp
             (booleanp signedp)
             :rule-classes :type-prescription)
            (vl-maybe-gatedelay-p-of-vl-netdecl->delay
             (vl-maybe-gatedelay-p delay))
            (vl-maybe-cstrength-p-of-vl-netdecl->cstrength
             (vl-maybe-cstrength-p cstrength))
            (vl-location-p-of-vl-netdecl->loc
             (vl-location-p loc)))
  :parents (modules)
  :short "Representation of net (wire) declarations."

  :long "<p>Net declarations introduce new wires with certain properties (type,
signedness, size, and so on).  Here are some examples of basic net
declarations.</p>

<code>
module m (a, b, c) ;
  wire [4:0] w ;       // &lt;-- plain net declaration
  wire ab = a &amp; b ;    // &lt;-- net declaration with assignment
  ...
endmodule
</code>

<p>Net declarations can also arise from using the combined form of port
declarations.</p>

<code>
module m (a, b, c) ;
  input wire a;    // &lt;-- net declaration in a port declaration
  ...
endmodule
</code>

<p>You can also string together net declarations, e.g., by writing <tt>wire w1,
w2;</tt>.</p>

<p>In all of these cases, our parser generates a <tt>vl-netdecl-p</tt> object
for each declared wire.  That is, each <tt>vl-netdecl-p</tt> is a declaration
of a single wire.</p>

<p>Note that when an assignment is also present, the parser creates a
corresponding, separate @(see vl-assign-p) object to contain the assignment.
Similarly, when using the combined net/port declaration format, a separate
@(see vl-portdecl-p) object is generated.  Hence, each <tt>vl-netdecl-p</tt>
really and truly only represents a declaration.</p>


<h4>Basic Fields</h4>

<p>The <tt>name</tt>, <tt>type</tt>, <tt>atts</tt>, and <tt>loc</tt> fields
should be self-explanatory after reading the descriptions of @(see
vl-netdecltype-p), @(see vl-atts-p), and @(see vl-location-p).</p>


<h4>Arrays and Vectors</h4>

<p>The <tt>range</tt> and <tt>arrdims</tt> fields deal with vectors and arrays.
In particular, <tt>range</tt> is a single, optional range that preceeds the
wire name.  For instance, the range of <tt>w</tt> is <tt>[4:0]</tt> in the
following declaration:</p>

<code>
  wire [4:0] w;
</code>

<p>In contrast, the <tt>arrdims</tt> are a list of ranges, also optional, which
follow the wire name.  For instance, the arrdims of <tt>v</tt> below is a
singleton list with the range <tt>[4:0]</tt>.</p>

<code>
  wire v [4:0];
</code>

<p>Be aware that range and arrdims really are <b>different</b> things;
<tt>w</tt> and <tt>v</tt> are <i>not</i> equivalent except for their names.  In
particular, <tt>w</tt> is a single, 5-bit wire, while <tt>v</tt> is an array of
five one-bit wires.</p>

<p>Things are more complicated when a declaration includes both a range and
arrdims.  For instance</p>

<code>
wire [4:0] a [10:0];
</code>

<p>declares <tt>a</tt> to be an 11-element array of five bit wires.  The
<tt>range</tt> for <tt>a</tt> is <tt>[4:0]</tt>, and the arrdims are a list
with one entry, namely the range <tt>[10:0]</tt>.</p>

<p>At present, the translator has almost no support for arrdims.  However, the
parser should handle them just fine.</p>


<h4>Vectorness and Signedness</h4>

<p>The <tt>signedp</tt> flag indicates whether the <tt>signed</tt> keyword was
supplied on this declaration.  <b>Warning</b>: Note that per page 175, port
declarations and net/reg declarations must be checked against one another: if
either declaration includes the <tt>signed</tt> keyword, then both are to be
considered signed.  The parser DOES NOT do this cross-referencing
automatically; instead the @(see portdecl-sign) transformation needs to be
run.</p>

<p>The <tt>vectoredp</tt> and <tt>scalaredp</tt> fields are booleans, which are
set to <tt>t</tt> when, respectively, the Verilog keywords <tt>vectored</tt>
and <tt>scalared</tt> are provided.  In other words, these fields might both be
<tt>nil</tt>.  I do not know what these keywords are supposed to mean; the
Verilog specification says almost nothing about it, and does not even say what
the default is.  According to some random guy on the internet, it's supposed to
be a syntax error to try to bit- or part-select from a vectored net.  Maybe I
can find a more definitive explanation somewhere.  Hey, in 6.1.3 there are some
differences mentioned w.r.t. how delays go to scalared and vectored nets.  4.3.2
has a little bit more.</p>


<h4>Delay</h4>

<p>Net delays are described in 7.14, and indicate the time it takes for any
driver on the net to change its value.  The default delay is zero when no delay
is specified.  Even so, we represent the delay using a @(see
vl-maybe-gatedelay-p), and use <tt>NIL</tt> when no delay is specified.</p>

<p>Note (from 6.1.3) that when delays are provided in the combined declaration
and assignment statement, e.g., </p>

<code>
  wire #10 a = 1, b = 2;
</code>

<p>that the delay is to be associated with each assignment, and NOT with the
net declaration for <tt>a</tt>.  See @(see vl-assign-p) for more information.</p>

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

<p>The <tt>cstrength</tt> field is only applicable to <tt>trireg</tt>-type
nets.  It will be <tt>nil</tt> for all other nets, and will also be
<tt>nil</tt> on <tt>trireg</tt> nets that do not explicitly give a charge
strength.  Note that <tt>vl-netdecl-p</tt> does not enforce the requirement
that only triregs have charge strengths, but the parser does.</p>

<p><b>Warning:</b> we have not really paid attention to charge strengths, and
our transformations may not preserve it correctly.</p>")

(deflist vl-netdecllist-p (x)
  (vl-netdecl-p x)
  :elementp-of-nil nil
  :parents (modules))



(defaggregate vl-plainarg
  (expr atts portname dir)
  :tag :vl-plainarg
  :legiblep nil
  :require
  ((vl-maybe-expr-p-of-vl-plainarg->expr
    (vl-maybe-expr-p expr))
   (vl-atts-p-of-vl-plainarg->atts
    (vl-atts-p atts))
   (vl-maybe-string-p-of-vl-plainarg->portname
    (vl-maybe-string-p portname)
    :rule-classes ((:type-prescription)
                   (:rewrite
                    :corollary (implies (force (vl-plainarg-p x))
                                        (equal (stringp (vl-plainarg->portname x))
                                               (if (vl-plainarg->portname x)
                                                   t
                                                 nil))))))
   (vl-maybe-direction-p-of-vl-plainarg->dir
    (vl-maybe-direction-p dir)))
  :parents (modules vl-arguments-p)
  :short "Representation of a single argument in a plain argument list."

  :long "<p>There are two kinds of argument lists for module instantiations,
which we call <i>plain</i> and <i>named</i> arguments.</p>

<code>
  modname instname ( 1, 2, 3 );             &lt;-- \"plain\" arguments
  modname instname ( .a(1), .b(2), .c(3) ); &lt;-- \"named\" arguments
</code>

<p>A <tt>vl-plainarg-p</tt> represents a single argument in a plain argument
list.</p>

<p>The <tt>expr</tt> is the expression being connected to this port; in
programming languages parlance, the <tt>expr</tt> is an <i>actual</i>.  Note
that <tt>expr</tt> is only a @(see vl-maybe-expr-p), and may be <tt>nil</tt>.
This is because Verilog allows expressions to be \"blank\", in which case they
represent an unconnected wire.  This seems to be used only very rarely, but is
supported.</p>

<p>The <tt>atts</tt> are any attributes (see @(see vl-atts-p)) associated with
this argument.</p>

<p>The <tt>dir</tt> is an @(see vl-maybe-direction-p) object.  This is
<b>not</b> part of the Verilog syntax, but may sometimes be added by the @(see
argresolve) transformation to indicate whether this port for this argument is
an input, output, or inout for the module or gate being instantiated.</p>

<p>Note that after @(see argresolve), all well-formed gate instances will have
their direction information computed.  You may rely upon the <tt>dir</tt> field
for gate instances.</p>

<p>However, for module instances the direction of a port may not be apparent;
see @(see vl-port-direction) for details.  So even after @(see argresolve) some
arguments to module instances may not have a <tt>dir</tt> annotation, and so
the <tt>dir</tt> field should generally not be relied upon for module
instances.</p>

<p>The <tt>portname</tt> is also not part of the Verilog syntax, but may
sometimes be added by the @(see argresolve) transformation as a convenience for
error message generation.  This field should <b>never</b> be used for anything
that is semantically important.  Note that no argument to a gate instance will
ever have a portname.  Also note that since not every @(see vl-port-p) has a
name, some arguments to module instances may also not be given portnames.</p>")

(deflist vl-plainarglist-p (x)
  (vl-plainarg-p x)
  :elementp-of-nil nil
  :parents (modules))

(deflist vl-plainarglistlist-p (x)
  (vl-plainarglist-p x)
  :elementp-of-nil t
  :parents (modules))

(defthm vl-plainarglist-p-of-strip-cars
  (implies (and (vl-plainarglistlist-p x)
                (all-have-len x n)
                (not (zp n)))
           (vl-plainarglist-p (strip-cars x)))
  :hints(("Goal" :induct (len x))))

(defthm vl-plainarglistlist-p-of-strip-cdrs
  (implies (vl-plainarglistlist-p x)
           (vl-plainarglistlist-p (strip-cdrs x)))
  :hints(("Goal" :induct (len x))))

(defprojection vl-plainarglist->exprs (x)
  (vl-plainarg->expr x)
  :guard (vl-plainarglist-p x)
  :nil-preservingp t)

(defthm vl-exprlist-p-of-vl-plainarglist->exprs
  (implies (force (vl-plainarglist-p x))
           (equal (vl-exprlist-p (vl-plainarglist->exprs x))
                  (not (member nil (vl-plainarglist->exprs x)))))
  :hints(("Goal" :induct (len x))))




(defaggregate vl-namedarg
  (name expr atts)
  :tag :vl-namedarg
  :legiblep nil
  :require ((stringp-of-vl-namedarg->name
             (stringp name)
             :rule-classes :type-prescription)
            (vl-maybe-expr-p-of-vl-namedarg->expr
             (vl-maybe-expr-p expr))
            (vl-atts-p-of-vl-namedarg->atts
             (vl-atts-p atts)))
  :parents (modules)
  :short "Representation of a single argument in a named argument list."

  :long "<p>See @(see vl-plainarg-p) for a general discussion of arguments.
Each <tt>vl-namedarg-p</tt> represents a single argument in a named argument
list.  Its fields include:</p>

<ul>

<li><tt>name</tt>, a string, e.g., <tt>foo</tt> in <tt>.foo(3)</tt>,</li>

<li><tt>expr</tt>, a @(see vl-maybe-expr-p) which is the actual for this port,
and may be <tt>nil</tt> for blank ports as described in @(see
vl-plainarg-p), and</li>

<li><tt>atts</tt>, any attributes (see @(see vl-atts-p)) associated with this
argument.</li>

</ul>

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

<code>
  modname instname ( 1, 2, 3 );             &lt;-- \"plain\" arguments
  modname instname ( .a(1), .b(2), .c(3) ); &lt;-- \"named\" arguments
</code>

<p>Similarly, named or plain argument lists can be used in order to give
parameters to a module, e.g.,</p>

<code>
  modname #(.width(6)) instname(o, a, b);
  modname #(6) instname(o, a, b);
</code>

<p>A <tt>vl-arguments-p</tt> structure represents an argument list of either
variety.  Each <tt>vl-arguments-p</tt> structure is an aggregate of two fields:</p>

<ul>
 <li><tt>namedp</tt>, which says whether named or plain arguments are used, and </li>
 <li><tt>args</tt>, the actual list of named or plain arguments.</li>
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
    (cutil::da-patbind-fn 'vl-arguments '(namedp args) args forms rest-expr))

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
  (instname modname range paramargs portargs str delay atts loc)
  :tag :vl-modinst
  :legiblep nil
  :require ((vl-maybe-string-p-of-vl-modinst->instname
             (vl-maybe-string-p instname)
             :rule-classes ((:type-prescription)
                            (:rewrite :corollary
                                      (implies (force (vl-modinst-p x))
                                               (equal (stringp (vl-modinst->instname x))
                                                      (if (vl-modinst->instname x)
                                                          t
                                                        nil))))))
            (stringp-of-vl-modinst->modname
             (stringp modname)
             :rule-classes :type-prescription)
            (vl-maybe-range-p-of-vl-modinst->range
             (vl-maybe-range-p range))
            (vl-arguments-p-of-vl-modinst->paramargs
             (vl-arguments-p paramargs))
            (vl-arguments-p-of-vl-modinst->portargs
             (vl-arguments-p portargs))
            (vl-maybe-gatestrength-p-of-vl-modinst->str
             (vl-maybe-gatestrength-p str))
            (vl-maybe-gatedelay-p-of-vl-modinst->delay
             (vl-maybe-gatedelay-p delay))
            (vl-atts-p-of-vl-modinst->atts
             (vl-atts-p atts))
            (vl-location-p-of-vl-modinst->loc
             (vl-location-p loc)))
  :parents (modules)
  :short "Representation of a single module (or user-defined primitive)
instance."

  :long "<p>We represent module and user-defined primitive instances in a
uniform manner with <tt>vl-modinst-p</tt> structures.  Because of this, certain
fields do not make sense in one context or another.  In particular, a UDP
instance should never have any parameter arguments, its port arguments should
always be an plain argument list, and it may not have a instname.  Meanwhile, a
module instance should never have a drive strength or a delay, and should
always have a instname.</p>

<p>As with variables, nets, etc., we split up combined instantiations such as
<tt>modname inst1 (...), inst2 (...)</tt> into separate, individual structures,
one for <tt>inst1</tt>, and one for <tt>inst2</tt>, so that each
<tt>vl-modinst-p</tt> represents exactly one instance (or instance array).</p>

<p>The <tt>modname</tt> is the name of the module or user-defined primitive
that is being instantiated, and <tt>instname</tt> is either the name of this
instance or <tt>nil</tt> if the instance has no name.</p>

<p>If present, the <tt>range</tt> indicates that this is an array of instances,
instead of a single instance.</p>

<p>The <tt>paramargs</tt> field is a @(see vl-arguments-p) that gives the
values for the module parameters.  (E.g., in an instance of a parameterized
adder module, this list might include the <tt>width</tt> of the adder being
instantiated.)</p>

<p>The <tt>portargs</tt> field is a @(see vl-arguments-p) that gives the values
for the module's ports.  (E.g., in an instance of an adder module, this list
would contain the expressions for the inputs and outputs.)</p>

<p>The <tt>gatestrength</tt> and <tt>gatedelay</tt> should only be used for
user-defined primitives.  <b>Warning:</b> we have generally ignored these
fields and our transforms may not handle them correctly.</p>

<p>The <tt>atts</tt> are any attributes (see @(see vl-atts-p)) associated with
this module instance.</p>

<p>The <tt>loc</tt> is a @(see vl-location-p) that says where in the source
code this module instance was introduced, and is useful for error messages.</p>")

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
  (type name range strength delay args atts loc)
  :tag :vl-gateinst
  :legiblep nil
  :require ((vl-gatetype-p-of-vl-gateinst->type
             (vl-gatetype-p type))
            (vl-maybe-string-p-of-vl-gateinst->name
             (vl-maybe-string-p name)
             :rule-classes ((:type-prescription)
                            (:rewrite :corollary
                                      (implies (force (vl-gateinst-p x))
                                               (equal (stringp (vl-gateinst->name x))
                                                      (if (vl-gateinst->name x)
                                                          t
                                                        nil))))))
            (vl-maybe-range-p-of-vl-gateinst->range
             (vl-maybe-range-p range))
            (vl-maybe-gatestrength-p-of-vl-gateinst->strength
             (vl-maybe-gatestrength-p strength))
            (vl-maybe-gatedelay-p-of-vl-gateinst->delay
             (vl-maybe-gatedelay-p delay))
            (vl-plainarglist-p-of-vl-gateinst->args
             (vl-plainarglist-p args))
            (vl-atts-p-of-vl-gateinst->atts
             (vl-atts-p atts))
            (vl-location-p-of-vl-gateinst->loc
             (vl-location-p loc)))
  :parents (modules)
  :short "Representation of a single gate instantiation."

  :long "<p><tt>vl-gateinst-p</tt> is our representation for any single gate
instance (or instance array).</p>

<p>The grammar for gate instantiations is quite elaborate, but the various
cases are so regular that a unified representation is possible.  Note that the
Verilog grammar restricts the list of expressions in certain cases, e.g., for
an <tt>and</tt> gate, the first expression must be an lvalue.  Although our
parser enforces these restrictions, we do not encode them into the definition
of <tt>vl-gateinst-p</tt>.</p>

<p>The <tt>type</tt> of the gate is an @(see vl-gatetype-p) and says what kind
of gate this is, (e.g., rmos, nand, xor, ...).</p>

<p>The <tt>name</tt> may be a string that names this instance, or may be
<tt>nil</tt> when the instance has no name.</p>

<p>If provided, the <tt>range</tt> indicates that this is an array of
instances instead of a single instance.</p>

<p>The <tt>strength</tt> is represented by a @(see vl-maybe-gatestrength-p).
The parser leaves this as <tt>nil</tt> unless it is explicitly provided.  Note
from Section 7.8 that pullup and pulldown gates are special in that the
strength0 from a pullup source and the strength1 on a pulldown source are
supposed to be ignored.  <b>Warning:</b> in general we have not paid much
attention to strengths, so we may not handle them correctly in our various
transforms.</p>

<p>The <tt>delay</tt> is represented by a @(see vl-maybe-gatedelay-p), and is
also left as <tt>nil</tt> unless it is explicitly provided.  Note that certain
gates (tran, rtran, pullup, and pulldown) never have delays according to the
Verilog grammar, but this is not enforced in our <tt>vl-gateinst-p</tt>
definition, only by the parser.  <b>Warning:</b> as with strengths, we have
not paid much attention to delays, and our transforms may not handle them
correctly.</p>

<p>The <tt>args</tt> are a list of @(see vl-plainarg-p) structures.  Note that
this differs from module instances where @(see vl-arguments-p) structures are
used, because gate arguments are never named.  The grammar restricts how many
arguments certain gates can have, but we do not enforce these restrictions in
the definition of <tt>vl-gateinst-p</tt>.</p>

<p>The <tt>atts</tt> are any attributes (see @(see vl-atts-p)) associated with
this module instance.</p>

<p>The <tt>loc</tt> is a @(see vl-location-p) that says where in the source
code this module instance was introduced, and is useful for error
messages.</p>")

(defthm symbolp-of-vl-gateinst->type
  (implies (force (vl-gateinst-p x))
           (and (symbolp (vl-gateinst->type x))
                (not (equal (vl-gateinst->type x) t))
                (not (equal (vl-gateinst->type x) nil))))
  :hints(("Goal"
          :use ((:instance vl-gatetype-p-of-vl-gateinst->type))
          :in-theory (e/d (vl-gatetype-p)
                          (vl-gatetype-p-of-vl-gateinst->type)))))

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
  (name type arrdims initval atts loc)
  :tag :vl-vardecl
  :legiblep nil
  :require ((stringp-of-vl-vardecl->name
             (stringp name)
             :rule-classes :type-prescription)
            (vl-vardecltype-p-of-vl-vardecl->type
             (vl-vardecltype-p type))
            (vl-rangelist-p-of-vl-vardecl->arrdims
             (vl-rangelist-p arrdims))
            (vl-maybe-expr-p-of-vl-vardecl->initval
             (vl-maybe-expr-p initval))
            (vl-atts-p-of-vl-vardecl->atts
             (vl-atts-p atts))
            (vl-location-p-vl-vardecl->loc
             (vl-location-p loc)))
  :parents (modules)
  :short "Representation of a single variable declaration."
  :long "<p><tt>vl-vardecl-p</tt> is our representation for a single variable
declaration, and is used for <tt>integer</tt>, <tt>real</tt>, <tt>time</tt>,
and <tt>realtime</tt> variable declarations.  As with nets and ports, our
parser splits up combined declarations such as \"integer a, b\" into multiple,
individual declarations, so each <tt>vl-vardecl-p</tt> represents only one
declaration.</p>

<p>The <tt>name</tt> is an ordinary ACL2 string which contains the name of this
variable.</p>

<p>The <tt>type</tt> is a @(see vl-vardecltype-p) that says whether this is an
integer, real, time, or realtime variable.</p>

<p>The <tt>arrdims</tt> are a list of @(see vl-range-p) objects that give the
dimensions for arrays of variables.</p>

<p>The <tt>initval</tt> is used when the declaration inclues an initial value
for the variable, e.g., if one writes <tt>integer i = 3;</tt>, then the
<tt>initval</tt> will be a @(see vl-expr-p) that represents <tt>3</tt>.</p>

<p>The <tt>atts</tt> are any attributes (see @(see vl-atts-p)) associated
with this declaration.</p>

<p>The <tt>loc</tt> is a @(see vl-location-p) that identifies where this
declaration comes from in the source code.</p>")



(defaggregate vl-regdecl
  (name signedp range arrdims initval atts loc)
  :tag :vl-regdecl
  :legiblep nil
  :require ((stringp-of-vl-regdecl->name
             (stringp name)
             :rule-classes :type-prescription)
            (booleanp-of-vl-regdecl->signedp
             (booleanp signedp)
             :rule-classes :type-prescription)
            (vl-maybe-range-p-of-vl-regdecl->range
             (vl-maybe-range-p range))
            (vl-rangelist-p-of-vl-regdecl->arrdims
             (vl-rangelist-p arrdims))

; BOZO eliminate initval and replace with an initial statement.  Update the
; docs for vl-initial-p and also below when this is done.

            (vl-maybe-expr-p-of-vl-regdecl->initval
             (vl-maybe-expr-p initval))
            (vl-atts-p-of-vl-regdecl->atts
             (vl-atts-p atts))
            (vl-location-p-vl-regdecl->loc
             (vl-location-p loc)))
  :parents (modules)
  :short "Representation of a single <tt>reg</tt> declaration."
  :long "<p><tt>vl-regdecl-p</tt> is our representation for a single
<tt>reg</tt> declaration.  Our parser splits up combined declarations such as
\"reg a, b\" into multiple, individual declarations, so each
<tt>vl-regdecl-p</tt> represents only one declaration.</p>

<p>The <tt>name</tt> is the name of this register as an ordinary ACL2
string.</p>

<p>The <tt>signedp</tt> flag indicates whether they keyword <tt>signed</tt> was
used in the declaration of the register.  (By default, registers are
unsigned.)</p>

<p>The <tt>range</tt> and <tt>arrdims</tt> are used for multi-bit regs and
arrays of regs.  More discussion is available in @(see vl-netdecl-p).</p>

<p>The <tt>initval</tt> is an expression that provides an initial value to
this register, if one was provided.</p>

<p>The <tt>atts</tt> are any attributes (see @(see vl-atts-p)) associated
with this declaration.</p>

<p>The <tt>loc</tt> is a @(see vl-location-p) that identifies where this
declaration comes from in the source code.</p>")



(defaggregate vl-eventdecl
  (name arrdims atts loc)
  :tag :vl-eventdecl
  :legiblep nil
  :require ((stringp-of-vl-eventdecl->name
             (stringp name)
             :rule-classes :type-prescription)
            (vl-rangelist-p-of-vl-eventdecl->arrdims
             (vl-rangelist-p arrdims))
            (vl-atts-p-of-vl-eventdecl->atts
             (vl-atts-p atts))
            (vl-location-p-vl-eventdecl->loc
             (vl-location-p loc)))
  :parents (modules)
  :short "Representation of a single event declaration."
  :long "<p>BOZO document this</p>")



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

<code>
parameter_declaration ::=
    'parameter' ['signed'] [range] list_of_param_assignments
  | 'parameter' parameter_type list_of_param_assignments

parameter_type ::=
   'integer' | 'real' | 'realtime' | 'time'
</code>

<p>In other words, every declaration either has:</p>

<ul>

<li>A \"parameter_type\" (<tt>integer</tt>, <tt>real</tt>, <tt>realtime</tt>,
or <tt>time</tt>), in which case we use the symbols <tt>:vl-integer</tt>,
<tt>:vl-real</tt>, <tt>:vl-time</tt>, or <tt>:vl-realtime</tt>; <b>OR</b></li>

<li>A <tt>signed</tt> declaration without any other type, in which case we
use <tt>:vl-signed</tt>, <b>OR</b></li>

<li>(most commonly) No type or sign declaration whatsoever, in which case we
use <tt>:vl-plain</tt>.</li>

</ul>")

(defaggregate vl-paramdecl
  (name expr type localp range atts loc)
  :tag :vl-paramdecl
  :legiblep nil
  :require ((stringp-of-vl-paramdecl->name
             (stringp name)
             :rule-classes :type-prescription)
            (vl-expr-p-of-vl-paramdecl->expr
             (vl-expr-p expr))
            (vl-paramdecltype-p-of-vl-paramdecl->type
             (vl-paramdecltype-p type))
            (booleanp-of-vl-paramdecl->localp
             (booleanp localp)
             :rule-classes :type-prescription)
            (vl-maybe-range-p-of-vl-paramdecl->range
             (vl-maybe-range-p range))
            (vl-atts-p-of-vl-paramdecl->atts
             (vl-atts-p atts))
            (vl-location-p-of-vl-paramdecl->loc
             (vl-location-p loc)))
  :parents (modules)
  :short "Representation of a single <tt>parameter</tt> or <tt>localparam</tt>
declaration."
  :long "<p>Parameters are discussed in 12.2.  Some examples of parameter
declarations include:</p>

<code>
module mymod (a, b, ...) ;
  parameter WIDTH = 3;
  localparam TWICE_WIDTH = 2 * WIDTH;
  ...
endmodule
</code>

<p>The <tt>name</tt> of the parameter is an ordinary ACL2 <tt>stringp</tt>, e.g.,
<tt>WIDTH</tt> or <tt>TWICE_WIDTH</tt> in the examples above.</p>

<p>The <tt>expr</tt> is the default value for this expression.</p>

<p>The <tt>type</tt> is a @(see vl-paramdecltype-p) that might indicate the
parameter is a signed or has a particular type (e.g., integer, realtime).</p>

<p>The <tt>localp</tt> flag is <tt>t</tt> if this delaration was made with
<tt>localparam</tt>, or <tt>nil</tt> if the declaration was made with
<tt>parameter</tt>.  The difference is apparently that <tt>localparam</tt>s
such as <tt>TWICE_WIDTH</tt> cannot be overridden from outside the module,
except insofar as that they depend upon other, non-local parameters.
Apparently the use of <tt>localparam</tt> may be useful for introducing
named constants without polluting the <tt>`define</tt> namespace.</p>

<p>The <tt>range</tt> is some ridiculous thing allowed by the grammar and
who knows what it means.  Some description of it in 12.2.</p>

<p>The <tt>atts</tt> and <tt>loc</tt> should be obvious; see @(see vl-atts-p)
and @(see vl-location-p).</p>")

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



(defsection vl-blockitem-p
  :parents (modules)
  :short "Recognizer for a valid block item."

  :long "<p><tt>vl-blockitem-p</tt> is a sum-of-products style type for
recognizing valid block items.  The valid block item declarations are register
declarations, variable declarations (integer, real, time, and realtime), event
declarations, and parameter declarations (parameter and localparam), which we
represent as @(see vl-regdecl-p), @(see vl-vardecl-p), @(see vl-eventdecl-p),
and @(see vl-paramdecl-p) objects, respectively.</p>"

  (defund vl-blockitem-p (x)
    (declare (xargs :guard t))
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
           (otherwise nil))))

  (local (in-theory (enable vl-blockitem-p)))

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
  :parents (modules))

(defthm vl-blockitemlist-p-when-vl-regdecllist-p
  (implies (vl-regdecllist-p x)
           (vl-blockitemlist-p x))
  :hints(("Goal" :induct (len x))))

(defthm vl-blockitemlist-p-when-vl-vardecllist-p
  (implies (vl-vardecllist-p x)
           (vl-blockitemlist-p x))
  :hints(("Goal" :induct (len x))))

(defthm vl-blockitemlist-p-when-vl-eventdecllist-p
  (implies (vl-eventdecllist-p x)
           (vl-blockitemlist-p x))
  :hints(("Goal" :induct (len x))))

(defthm vl-blockitemlist-p-when-vl-paramdecllist-p
  (implies (vl-paramdecllist-p x)
           (vl-blockitemlist-p x))
  :hints(("Goal" :induct (len x))))




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
  :parents (vl-evatom)
  :short "Type of an item in an event control list."
  :long "<p>Any particular atom in the event control list might have a
<tt>posedge</tt>, <tt>negedge</tt>, or have no edge specifier at all, e.g., for
plain atoms like <tt>a</tt> and <tt>b</tt> in <tt>always @@(a or b)</tt>.</p>")

(defaggregate vl-evatom
  (type expr)
  :tag :vl-evatom
  :legiblep nil
  :require ((vl-evatomtype-p-of-vl-evatom->type
             (vl-evatomtype-p type))
            (vl-expr-p-of-vl-evatom->expr
             (vl-expr-p expr)))
  :parents (modules)
  :short "A single item in an event control list."
  :long "<p>Event expressions and controls are described in Section 9.7.</p>

<p>We represent the expressions for an event control (see @(see
vl-eventcontrol-p)) as a list of <tt>vl-evatom-p</tt> structures.  Each
individual evatom is either a plain Verilog expression, or is <tt>posedge</tt>
or <tt>negedge</tt> applied to a Verilog expression.</p>

<p>The <tt>type</tt> is the type of edge; see @(see vl-evatomtype-p).</p>

<p>The <tt>expr</tt> is the associated expression.</p>")

(deflist vl-evatomlist-p (x)
  (vl-evatom-p x)
  :elementp-of-nil nil
  :parents (modules))



(defaggregate vl-eventcontrol
  (starp atoms)
  :tag :vl-eventcontrol
  :legiblep nil
  :require ((booleanp-of-vl-eventcontrol->star
             (booleanp starp)
             :rule-classes :type-prescription)
            (vl-evatomlist-p-of-vl-eventcontrol->atoms
             (vl-evatomlist-p atoms)))
  :parents (modules)
  :short "Representation of an event controller like <tt>@@(posedge clk)</tt> or
<tt>@@(a or b)</tt>."

  :short "<p>Event controls are described in Section 9.7.  We represent each
event controller as a <tt>vl-eventcontrol-p</tt> aggregates.</p>

<p>If the <tt>starp</tt> flag is <tt>T</tt>, then this event control represents
<tt>@@(*)</tt>.</p>

<p>Otherwise, <tt>atoms</tt> contains a list of @(see vl-evatom-p) structures
that describe the various events.  Verilog allows two kinds of syntax for these
lists, e.g., one can write <tt>@@(a or b)</tt> or <tt>@@(a, b)</tt>.  The meaning
is identical in either case, so we just use a list of atoms.</p>")

(defaggregate vl-delaycontrol
  (value)
  :tag :vl-delaycontrol
  :legiblep nil
  :require ((vl-expr-p-of-vl-delaycontrol->value
             (vl-expr-p value)))
  :parents (modules)
  :short "Representation of a delay controller like <tt>#6</tt>."
  :long "<p>Delay controls are described in Section 9.7.  An example is</p>

<code>
  #10 foo = 1;   &lt;-- The #10 is a delay control
</code>

<p>The <tt>expr</tt> is an expression that represents the delay.</p>")

(defaggregate vl-repeateventcontrol
  (expr ctrl)
  :tag :vl-repeat-eventcontrol
  :legiblep nil
  :require ((vl-expr-p-of-vl-repeateventcontrol->expr
             (vl-expr-p expr))
            (vl-eventcontrol-p-of-vl-repeateventcontrol->ctrl
             (vl-eventcontrol-p ctrl)))
  :parents (modules)
  :short "Representation of <tt>repeat</tt> constructs in intra-assignment
delays."
  :long "<p>See Section 9.7.7.  These are used to represent special
intra-assignment delays, where the assignment should not occur until some
number of occurrences of an event.  For instance:</p>

<code>
   a = repeat(3) @@(posedge clk) b;
</code>

<p>The <tt>expr</tt> indicates how many times to repeat, e.g., <tt>3</tt>
in the above example.  The <tt>ctrl</tt> is an @(see vl-eventcontrol-p)
that says which event is being waited for.</p>

<p><b>BOZO</b> Consider consolidating all of these different kinds of
controls into a single, unified representation.  E.g., you could at
least extend eventcontrol with a maybe-expr that is its count, and get
rid of repeateventcontrol.</p>")



(defsection vl-delayoreventcontrol-p

; BOZO document me

  (defund vl-delayoreventcontrol-p (x)
    (declare (xargs :guard t))
    (mbe :logic
         (or (vl-delaycontrol-p x)
             (vl-eventcontrol-p x)
             (vl-repeateventcontrol-p x))
         :exec
         (case (tag x)
           (:vl-delaycontrol (vl-delaycontrol-p x))
           (:vl-eventcontrol (vl-eventcontrol-p x))
           (:vl-repeat-eventcontrol (vl-repeateventcontrol-p x)))))

  (local (in-theory (enable vl-delayoreventcontrol-p)))

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



(defsection vl-maybe-delayoreventcontrol-p

;; BOZO document me

  (defund vl-maybe-delayoreventcontrol-p (x)
    (declare (xargs :guard t))
    (or (not x)
        (vl-delayoreventcontrol-p x)))

  (local (in-theory (enable vl-maybe-delayoreventcontrol-p)))

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
  :long "<p><tt>:vl-blocking</tt> and <tt>:vl-nonblocking</tt> are for
blocking/nonblocking procedural assignments, e.g., <tt>foo = bar</tt> and
<tt>foo &lt;= bar</tt>, respectively.</p>

<p><tt>:vl-assign</tt> and <tt>:vl-force</tt> are for procedural continuous
assignments, e.g., <tt>assign foo = bar</tt> or <tt>force foo = bar</tt>,
respectivley.</p>")

(defaggregate vl-assignstmt
  (type lvalue expr ctrl atts loc)
  :tag :vl-assignstmt
  :legiblep nil
  :require ((vl-assign-type-p-of-vl-assignstmt->type
             (vl-assign-type-p type))
            (vl-expr-p-of-vl-assignstmt->lvalue
             (vl-expr-p lvalue))
            (vl-expr-p-of-vl-assignstmt->expr
             (vl-expr-p expr))
            (vl-maybe-delayoreventcontrol-p-of-vl-assignstmt->ctrl
             (vl-maybe-delayoreventcontrol-p ctrl))
            (vl-atts-p-of-vl-assignstmt->atts
             (vl-atts-p atts))
            (vl-location-p-of-vl-assignstmt->loc
             (vl-location-p loc)))
  :parents (vl-stmt-p)
  :short "Representation of an assignment statement."
  :long "<p>Assignment statements are covered in Section 9.2.  There are two
major types of assignment statements.</p>

<h4>Procedural Assignments</h4>

<p>Procedural assignment statements may only be used to assign to <tt>reg</tt>,
<tt>integer</tt>, <tt>time</tt>, <tt>realtime</tt>, and memory data types, and
cannot be used to assign to ordinary nets such as <tt>wire</tt>s.  There are
two kinds of procedural assignments: </p>

<code>
   foo = bar ;     // \"blocking\" -- do the assignment now
   foo &lt;= bar ;    // \"nonblocking\" -- schedule the assignment to occur
</code>

<p>The difference between these two statements has to do with Verilog's timing
model and simulation semantics.  In particular, a blocking assignment
\"executes before the statements that follow it,\" whereas a non-blocking
assignment only \"schedules\" an assignment to occur and can be thought of as
executing in parallel with what follows it.</p>

<h4>Continuous Procedural Assignments</h4>

<p>Continuous procedural assignment statements may apparently be used to assign
to either nets or variables.  There are two kinds:</p>

<code>
  assign foo = bar ;  // only for variables
  force foo = bar ;   // for variables or nets
</code>

<p>We represent all of these kinds of assignment statements uniformly as
<tt>vl-assignstmt-p</tt> objects.</p>

<p>The <tt>type</tt> of the object is a @(see vl-assign-type-p) that says what
kind of assignment this is.</p>

<p>The <tt>lvalue</tt> is the location being assigned to.  Note that the
specification places various restrictions on lvalues, e.g., for a procedural
assignment the lvalue may contain only plain variables, and bit-selects,
part-selects, memory words, and nested concatenations of these things.  These
restrictions are not enforced by <tt>vl-assignstmt-p</tt>, where we only
require that the lvalue is an expression.</p>

<p>The <tt>expr</tt> is the right-hand side expression that is being assigned
to this lvalue.</p>

<p>All forms of assignment may have a <tt>ctrl</tt> associated with them.  This
control may be a delay control such as <tt>#(6)</tt> an event control like
<tt>@@(posedge clk)</tt>, which can affect when the assignment is done.  The
rules for this are covered in Section 9.2 and appear to perhaps be different
depending upon the type of assignment.  Further coverage seems to be available
in Section 9.7.7.</p>

<p>The <tt>atts</tt> are any attributes (see @(see vl-atts-p)) associated with
the assignment.</p>

<p>The <tt>loc</tt> is a @(see vl-location-p) describing the origin of this
assignment in the original Verilog sources.</p>")



(defenum vl-deassign-type-p
  (:vl-deassign :vl-release)
  :parents (vl-stmt-p)
  :short "Type of an deassignment statement.")

(defaggregate vl-deassignstmt
  (type lvalue atts)
  :tag :vl-deassignstmt
  :legiblep nil
  :require ((vl-deassign-type-p-of-vl-deassignstmt->type
             (vl-deassign-type-p type))
            (vl-expr-p-of-vl-deassignstmt->lvalue
             (vl-expr-p lvalue))
            (vl-atts-p-of-vl-deassignstmt->atts
             (vl-atts-p atts)))
  :parents (vl-stmt-p)
  :short "Representation of a deassign or release statement."
  :long "<p>Deassign and release statements are described in Section 9.3.1 and
9.3.2.</p>")

(defaggregate vl-enablestmt
  (id args atts)
  :tag :vl-enablestmt
  :legiblep nil
  :require ((vl-expr-p-of-vl-enablestmt->id
             (vl-expr-p id))
            (vl-exprlist-p-of-vl-enablestmt->args
             (vl-exprlist-p args))
            (vl-atts-p-of-vl-enablestmt->atts
             (vl-atts-p atts)))
  :parents (vl-stmt-p)
  :short "Representation of an enable statement."

  :long "<p>Enable statements have an identifier (which should be either a
hierarchial identifier or a system identifier), which we represent as an
expression.  They also have a list of arguments, which are expressions.</p>")

(defaggregate vl-disablestmt
  (id atts)
  :tag :vl-disablestmt
  :legiblep nil
  :require ((vl-expr-p-of-vl-disablestmt->id
             (vl-expr-p id))
            (vl-atts-p-of-vl-disablestmt->atts
             (vl-atts-p atts)))
  :parents (vl-stmt-p)
  :short "Representation of a disable statement."

  :long "<p>Disable statements are simpler and just have a hierarchial
identifier.  Apparently there are no disable statements for system
identifiers.</p>")



(defaggregate vl-eventtriggerstmt
  (id atts)
  :tag :vl-eventtriggerstmt
  :legiblep nil
  :require ((vl-expr-p-of-vl-eventtriggerstmt->id
             (vl-expr-p id))
            (vl-atts-p-of-vl-eventtriggerstmt->atts
             (vl-atts-p atts)))
  :parents (vl-stmt-p)
  :short "Representation of an event trigger."
  :long "<p>Event trigger statements are used to explicitly trigger named
events.  They are discussed in Section 9.7.3 and looks like this:</p>

<code>
 -&gt; foo;
 -&gt; bar[1][2][3];  // I think?
</code>

<p>The <tt>id</tt> for an event trigger are the names such as <tt>foo</tt>
and <tt>bar</tt> above, and may be a hierarchical identifier.  We represent
the <tt>id</tt> as an expression.</p>

<p>The <tt>atts</tt> are any attributes (see @(see vl-atts-p)) associated
with the statement.</p>

<p><b>BOZO</b> are we handling the syntax correctly?  What about the
expressions that can follow the trigger?  Maybe they just become part of the
<tt>id</tt>?</p>")



(defaggregate vl-nullstmt
  (atts)
  :tag :vl-nullstmt
  :legiblep nil
  :require ((vl-atts-p-of-vl-nullstmt->atts
             (vl-atts-p atts)))
  :parents (vl-stmt-p)
  :short "Representation of an empty statement."

  :long "<p>We allow explicit null statements.  This allows us to canonicalize
<tt>if</tt> expressions so that any missing branches are turned into null
statements.</p>")




(defsection vl-atomicstmt-p
  :parents (vl-stmt-p)
  :short "Representation of an atomic statement."

  :long "<p><tt>vl-atomicstmt-p</tt> is a sum-of-products style recognizer.  Every
atomic statement is either a</p>

<ul>
 <li>@(see vl-nullstmt-p), </li>
 <li>@(see vl-assignstmt-p), </li>
 <li>@(see vl-deassignstmt-p), </li>
 <li>@(see vl-enablestmt-p),</li>
 <li>@(see vl-disablestmt-p), or</li>
 <li>@(see vl-eventtriggerstmt-p).</li>
</ul>"

  (defund vl-atomicstmt-p (x)
    (declare (xargs :guard t))
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
                 (otherwise            nil))))

  (local (in-theory (enable vl-atomicstmt-p)))

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
statements.  The <tt>type</tt> of each compound statement is one of the keyword
symbols recognized by <tt>vl-compoundstmttype-p</tt>.</p>

<p>Most of these are obvious, but note that:</p>

<ul>

<li><tt>:vl-casestmt</tt> is used for <tt>case</tt>, <tt>casex</tt>, and
<tt>casez</tt> statements.  See the compound statement's <tt>casetype</tt>
field for the detailed type.</li>

<li><tt>:vl-blockstmt</tt> is used for both sequential (<tt>begin ... end</tt>)
and parallel (<tt>fork ... join</tt>) blocks.  See the compound statement's
<tt>sequentialp</tt> field for the detailed type.</li>

<li>Timing statements are used for things like <tt>@@(posedge clk)
substmt</tt>, <tt>@@(foo or bar) substmt</tt>, and <tt>#6 substmt</tt>.</li>

</ul>")

(defenum vl-casetype-p
  (nil
   :vl-casex
   :vl-casez)
  :parents (vl-stmt-p)
  :short "Recognizes the possible kinds of case statements."
  :long "<ul>
<li><tt>nil</tt> for ordinary <tt>case</tt> statements,</li>
<li><tt>:vl-casex</tt> for <tt>casex</tt> statements, and</li>
<li><tt>:vl-casez</tt> for <tt>casez</tt> statements.</li>
</ul>")

(defsection vl-compoundstmt-basic-checksp
  :parents (vl-compoundstmt-p)
  :short "Additional structural checks for compound statements."

  :long "<p><b>Note:</b> the reader should first see @(see vl-compoundstmt-p)
for a general description of our representation of compound statements.</p>

<p><tt>vl-compoundstmt-basic-checksp</tt> is an additional well-formedness
constraint imposed on <tt>vl-compoundstmt-p</tt> structures.  It is responsible
for ensuring that, e.g., an <tt>if</tt> statement properly has a single
expression (its condition), two sub-statements (its true and false branches),
and no inappropriate fields such as <tt>name</tt>, <tt>decls</tt>, or
<tt>ctrl</tt> which are only appropriate for other kinds of statements.</p>

@(def vl-compoundstmt-basic-checksp)"

  (defund vl-compoundstmt-basic-checksp (type exprs stmts name decls ctrl
                                              sequentialp casetype)
    (declare (xargs :guard (and (vl-compoundstmttype-p type)
                                (vl-exprlist-p exprs)
                                ;; no guard on stmts due to mutual recursion
                                (vl-maybe-string-p name)
                                (vl-blockitemlist-p decls)
                                (vl-maybe-delayoreventcontrol-p ctrl)
                                (booleanp sequentialp)
                                (vl-casetype-p casetype))))
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
              (= num-stmts 1)))))))


(defaggregate vl-compoundstmt
  (type exprs stmts name decls ctrl sequentialp casetype atts)
  :tag :vl-compoundstmt
  :legiblep nil
  :require ((vl-compoundstmttype-p-of-vl-compoundstmt->type
             (vl-compoundstmttype-p type))
            (vl-exprlist-p-of-vl-compoundstmt->exprs
             (vl-exprlist-p exprs))
            ;; no requirements on stmts due to mutual recursion
            (vl-maybe-string-p-of-vl-compoundstmt->name
             (vl-maybe-string-p name)
             :rule-classes ((:type-prescription)
                            (:rewrite :corollary
                                      (implies (force (vl-compoundstmt-p x))
                                               (equal (stringp (vl-compoundstmt->name x))
                                                      (if (vl-compoundstmt->name x)
                                                          t
                                                        nil))))))
            (vl-blockitemlist-p-of-vl-compoundstmt->decls
             (vl-blockitemlist-p decls))
            (vl-maybe-delayoreventcontrol-p-of-vl-compoundstmt->ctrl
             (vl-maybe-delayoreventcontrol-p ctrl)
             :rule-classes ((:rewrite)
                            (:rewrite
                             :corollary
                             (implies (force (vl-compoundstmt-p x))
                                      (iff (vl-delayoreventcontrol-p (vl-compoundstmt->ctrl x))
                                           (vl-compoundstmt->ctrl x))))))
            (booleanp-of-vl-compoundstmt->sequentialp
             (booleanp sequentialp)
             :rule-classes :type-prescription)
            (vl-casetype-p-of-vl-compoundstmt->casetype
             (vl-casetype-p casetype))
            (vl-atts-p-of-vl-compoundstmt->atts
             (vl-atts-p atts))
            (vl-compoundstmt-basic-checksp-of-vl-compoundstmt
             (vl-compoundstmt-basic-checksp type exprs stmts name decls
                                            ctrl sequentialp casetype)))
  :parents (vl-stmt-p)

  :short "Representation of a compound statement."

  :long "<h3>Introduction</h3>

<p>My original approach to statements was essentially in the SDT (\"syntax
definition tree\") style.  I had a separate kind of node for each statement,
e.g., I had a <tt>vl-ifstmt-p</tt>, a <tt>vl-whilestmt-p</tt>, and so on.  This
was extraordinarily unwieldy and difficult to work with.  I ended up needing to
introduce something like an 11-part mutual-recursion to work with any
statement, and this was quite cumbersome.</p>

<p>My new approach is to merge the different kinds of compound statements into
a single <tt>vl-compoundstmt-p</tt> type.  This is a more of an AST (\"abstract
syntax tree\") style, and is basically similar to how <see topic=\"@(url
vl-expr-p)\">expressions</see> are handled.</p>

<p>In the new representation, each compound statement has several components,
some of which may not be applicable depending upon the particular kind of
statement we are dealing with.  The advantage of combining all of these things
together is that we can recur over statements while largely ignoring their
actual types, etc., making the mutually recursive scheme much simpler.</p>

<h3>Field Descriptions</h3>

<p>The <tt>type</tt> is keyword symbol that says what kind of statement this
is, e.g., an <tt>if</tt> or <tt>casez</tt> statement.  The <tt>type</tt> must
be one of the types recognized by @(see vl-compoundstmttype-p).</p>

<p>The <tt>exprs</tt> are a list of expressions associated with the statement.
Some statements (e.g., <tt>begin ... end</tt> blocks) have no expressions, but
other statements, such as <tt>if</tt>, <tt>while</tt>, and <tt>case</tt>
statements, may have one or many.</p>

<p>The <tt>stmts</tt> are any sub-statements that are associated with the
statement.  Every kind of compound statement may have sub-statements, since
otherwise it would be an atomic statement.</p>

<p>The <tt>name</tt> is only valid on block statements (i.e., <tt>begin
... end</tt> and <tt>fork ... join</tt> statements).  If present, it is a
string that names this block.</p>

<p>The <tt>decls</tt> are only valid on block statements, and includes any
declarations for the block; see @(see vl-blockitem-p).</p>

<p>The <tt>sequentialp</tt> flag is only valid on block statements, and is
<tt>t</tt> if this is a <tt>begin/end</tt> block, or <tt>nil</tt> if this is
a <tt>fork/join</tt> block.</p>

<p>The <tt>casetype</tt> is only valid on case statements, and indicates
whether this is a <tt>case</tt>, <tt>casex</tt>, or <tt>casez</tt> statement;
see @(see vl-casetype-p).</p>

<p>The <tt>ctrl</tt> is only valid on procedural timing control statements
such as <tt>@@(posedge clk) substmt</tt> or <tt>#6 substmt</tt>.  If present,
it should be either a @(see vl-eventcontrol-p) that describes what event to
wait for, e.g., \"<tt>posedge clk</tt>\", or a @(see vl-delaycontrol-p) that
says how long to delay, e.g., \"<tt>#6</tt>\".</p>

<p>The <tt>atts</tt> are any <see topic=\"@(url vl-atts-p)\">attributes</see>
associated with the statement.</p>

<h3>Basic Well-Formedness Checks</h3>

<p>A \"problem\" with using a combined representation is that, for instance, an
<tt>if</tt> statement has various fields like <tt>name</tt>, <tt>decls</tt>,
and <tt>ctrl</tt> which it really should not have.  A somewhat similar problem
is that, e.g., <tt>for</tt> statements need a certain number of expressions, so
how do we know it has the right number?</p>

<p>To address these kinds of concerns, in addition to the simple type checks
for each field, we use @(see vl-compoundstmt-basic-checksp) to carry out
additional well-formedness checking on a per-field basis.  This check ensures
that, for instance, an <tt>if</tt> statement has no <tt>name</tt>, and that
a <tt>for</tt> statement has the right number of expressions.</p>")

(defthm acl2-count-of-vl-compoundstmt->stmts
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
  :hints(("Goal" :in-theory (enable vl-atomicstmt-p))))



(defsection vl-stmt-p
  :parents (modules)
  :short "Representation of a statement."

  :long "<p>Verilog includes a number of statements for behavioral modelling.
Some of these (assignments, event triggers, enables and disables) are
<b>atomic</b> in that they do not contain any sub-statements.  We call the
other statements (loops, cases, if statements, etc.) <b>compound</b> since they
contain sub-statements and are mutually-recursive with <tt>vl-stmt-p</tt>.</p>

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

  ;; I'm not exactly sure what to put here, and what to put in mu-stmt-tools.
  ;; I'm going to try to keep most stuff in mu-stmt-tools, and just leave a
  ;; few basics here.

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



(defsection vl-fast-atomicstmt-p
  :parents (vl-atomicstmt-p vl-stmt-p)
  :short "Faster version of @(see vl-atomicstmt-p), given that @(see vl-stmt-p)
is already known."

  :long "<p>We leave this function enabled and reason about <tt>vl-atomicstmt-p</tt>
instead.</p>"

  (definline vl-fast-atomicstmt-p (x)
    (declare (xargs :guard (vl-stmt-p x)))
    (mbe :logic (vl-atomicstmt-p x)
         :exec (not (eq (tag x) :vl-compoundstmt)))))


(defsection vl-fast-compoundstmt-p
  :parents (vl-compoundstmt-p vl-stmt-p)
  :short "Faster version of @(see vl-compoundstmt-p), given that @(see vl-stmt-p)
is already known."

  :long "<p>We leave this function enabled and reason about <tt>vl-compoundstmt-p</tt>
instead.</p>"

  (definline vl-fast-compoundstmt-p (x)
    (declare (xargs :guard (vl-stmt-p x)))
    (mbe :logic (vl-compoundstmt-p x)
         :exec (eq (tag x) :vl-compoundstmt))))


(defsection vl-fast-nullstmt-p
  :parents (vl-nullstmt-p vl-stmt-p)
  :short "Faster version of @(see vl-nullstmt-p), given that @(see vl-stmt-p)
is already known."

  :long "<p>We leave this function nulld and reason about <tt>vl-nullstmt-p</tt>
instead.</p>"

  (definline vl-fast-nullstmt-p (x)
    (declare (xargs :guard (vl-stmt-p x)))
    (mbe :logic (vl-nullstmt-p x)
         :exec (eq (tag x) :vl-nullstmt))))


(defsection vl-fast-assignstmt-p
  :parents (vl-assignstmt-p vl-stmt-p)
  :short "Faster version of @(see vl-assignstmt-p), given that @(see vl-stmt-p)
is already known."

  :long "<p>We leave this function assignd and reason about <tt>vl-assignstmt-p</tt>
instead.</p>"

  (definline vl-fast-assignstmt-p (x)
    (declare (xargs :guard (vl-stmt-p x)))
    (mbe :logic (vl-assignstmt-p x)
         :exec (eq (tag x) :vl-assignstmt))))


(defsection vl-fast-enablestmt-p
  :parents (vl-enablestmt-p vl-stmt-p)
  :short "Faster version of @(see vl-enablestmt-p), given that @(see vl-stmt-p)
is already known."

  :long "<p>We leave this function enabled and reason about <tt>vl-enablestmt-p</tt>
instead.</p>"

  (definline vl-fast-enablestmt-p (x)
    (declare (xargs :guard (vl-stmt-p x)))
    (mbe :logic (vl-enablestmt-p x)
         :exec (eq (tag x) :vl-enablestmt))))





(defsection vl-atomicstmt->atts
  ;; BOZO document me
  (definlined vl-atomicstmt->atts (x)
    (declare (xargs :guard (vl-atomicstmt-p x)))
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

  (local (in-theory (enable vl-atomicstmt->atts)))

  (defthm vl-atts-p-of-vl-atomicstmt->atts
    (implies (force (vl-atomicstmt-p x))
             (vl-atts-p (vl-atomicstmt->atts x)))))

(defsection vl-stmt->atts
  ;; BOZO document me
  (definlined vl-stmt->atts (x)
    (declare (xargs :guard (vl-stmt-p x)))
    (if (vl-fast-atomicstmt-p x)
        (vl-atomicstmt->atts x)
      (vl-compoundstmt->atts x)))

  (local (in-theory (enable vl-stmt->atts)))

  (defthm vl-atts-p-of-vl-stmt->atts
    (implies (force (vl-stmt-p x))
             (vl-atts-p (vl-stmt->atts x)))))





;                       INITIAL AND ALWAYS BLOCKS
;
; Initial and always blocks just have a statement and, perhaps, some
; attributes.

(defaggregate vl-initial
  (stmt atts loc)
  :tag :vl-initial
  :legiblep nil
  :require ((vl-stmt-p-of-vl-initial->stmt
             (vl-stmt-p stmt))
            (vl-atts-p-of-vl-initial->atts
             (vl-atts-p atts))
            (vl-location-p-of-vl-initial->loc
             (vl-location-p loc)))
  :parents (modules)
  :short "Representation of an initial statement."

  :long "<p>Initial statements in Verilog are used to set up initial values for
simulation.  For instance,</p>

<code>
module mymod (a, b, ...) ;
   reg r, s;
   initial r = 0;   &lt;-- initial statement
endmodule
</code>

<ul>

<li>The <tt>stmt</tt> is a @(see vl-stmt-p) that represents the actual
statement, e.g., <tt>r = 0</tt> above.  Such a statement is frequently a
sequential block statement (i.e., <tt>begin ... end</tt>), but as
shown above it can be anything.</li>

<li>The <tt>atts</tt> are any attribute (see @(see vl-atts-p)) associated with
this initial statement.</li>

<li>The <tt>loc</tt> is a @(see vl-location-p) that describes where this
initial statement was read from in the source code.</li>

</ul>

<p><b>BOZO</b> Our plan is to eventually generate <tt>initial</tt> statements
from register and variable declarations with initial values, i.e.,
<tt>reg r = 0;</tt>.</p>")


(defaggregate vl-always
  (stmt atts loc)
  :tag :vl-always
  :legiblep nil
  :require ((vl-stmt-p-of-vl-always->stmt
             (vl-stmt-p stmt))
            (vl-atts-p-of-vl-always->atts
             (vl-atts-p atts))
            (vl-location-p-of-vl-always->loc
             (vl-location-p loc)))
  :parents (modules)
  :short "Representation of an always statement."

  :long "<p>Always statements in Verilog are often used to model latches and
flops, and to set up other simulation events.  A simple example would be:</p>

<code>
module mymod (a, b, ...) ;
  always @@(posedge clk) myreg &lt;= in;
endmodule
</code>

<ul>

<li>The <tt>stmt</tt> is a @(see vl-stmt-p) that represents the actual
statement, e.g., <tt>@@(posedge clk) myreg &lt;= in</tt> above.  Such a
statement need not have a timing control such as <tt>@@(posedge clk)</tt> or
<tt>@@(a or b or c)</tt>, but often does.</li>

<li>The <tt>atts</tt> are any attribute (see @(see vl-atts-p)) associated with
this always statement.</li>

<li>The <tt>loc</tt> is a @(see vl-location-p) that describes where this always
statement was read from in the source code.</li>

</ul>")

(deflist vl-initiallist-p (x)
  (vl-initial-p x)
  :elementp-of-nil nil
  :parents (modules))

(deflist vl-alwayslist-p (x)
  (vl-always-p x)
  :elementp-of-nil nil
  :parents (modules))

(defthm acl2-count-of-vl-initial->stmt
  (and (<= (acl2-count (vl-initial->stmt x))
           (acl2-count x))
       (implies (consp x)
                (< (acl2-count (vl-initial->stmt x))
                   (acl2-count x))))
  :hints(("Goal" :in-theory (enable vl-initial->stmt)))
  :rule-classes ((:rewrite) (:linear)))

(defthm acl2-count-of-vl-always->stmt
  (and (<= (acl2-count (vl-always->stmt x))
           (acl2-count x))
       (implies (consp x)
                (< (acl2-count (vl-always->stmt x))
                   (acl2-count x))))
  :hints(("Goal" :in-theory (enable vl-always->stmt)))
  :rule-classes ((:rewrite) (:linear)))




(defenum vl-funtype-p
  (:vl-unsigned
   :vl-signed
   :vl-integer
   :vl-real
   :vl-realtime
   :vl-time)
  :parents (modules)
  :short "Representation of a function return and argument types."

  :long "<p>These are the various return types that a Verilog function can
have.  For instance, we use <tt>:vl-unsigned</tt> for a function like:</p>

<code> function [7:0] add_one ; ... endfunction </code>

<p>whereas we use <tt>:vl-real</tt> for a function like:</p>

<code> function real get_ratio ; ... endfunction </code>

<p>These same types can be used for the inputs of a function, e.g., you can
have function inputs such as:</p>

<code> input real a; </code>")


(defaggregate vl-funinput
  (name type range atts loc)
  :tag :vl-funinput
  :legiblep nil
  :require ((stringp-of-vl-funinput->name
             (stringp name)
             :rule-classes :type-prescription)
            (vl-funtype-p-of-vl-funinput->type
             (vl-funtype-p type))
            (vl-maybe-range-p-of-vl-funinput->range
             (vl-maybe-range-p range))
            (vl-atts-p-of-vl-funinput->atts
             (vl-atts-p atts))
            (vl-location-p-of-vl-funinput->loc
             (vl-location-p loc)))
  :parents (modules)
  :short "Representation of an input to a function."

  :long "<p>A function in Verilog takes inputs which are similar to the ports
of a module.  We represent them with their own <tt>vl-funinput-p</tt>
structures instead of trying to reuse @(see vl-portdecl-p) because, unlike port
declarations, they can have types such as <tt>integer</tt>, <tt>real</tt>, and
so forth.</p>

<p>The <tt>name</tt> is just a string that is the name of this input.</p>

<p>The <tt>type</tt> is a @(see vl-funtype-p) that gives the type for this
input.</p>

<p>The <tt>range</tt> is a @(see vl-maybe-range-p) that gives the size of this
input.  This only makes sense when the type is <tt>:vl-unsigned</tt> or
<tt>:vl-signed</tt>, and is <tt>nil</tt> when other types are used.</p>

<p>The <tt>atts</tt> are any attributes (see @(see vl-atts-p)) associated with
this input.  Syntactically, the attributes come before the <tt>input</tt>
keyword.</p>

<p>The <tt>loc</tt> is the @(see vl-location-p) where the <tt>name</tt> of the
function was found in the source code.  We use this location, instead of the
location of the input keyword, because a list of inputs can be declared using
the same input keyword.</p>")

(deflist vl-funinputlist-p (x)
  (vl-funinput-p x)
  :guard t
  :elementp-of-nil nil)

(defprojection vl-funinputlist->names (x)
  (vl-funinput->name x)
  :guard (vl-funinputlist-p x)
  :nil-preservingp t
  :result-type string-listp)



(defaggregate vl-fundecl
  (name automaticp rtype rrange inputs decls body atts loc)
  :tag :vl-fundecl
  :legiblep nil
  :require ((stringp-of-vl-fundecl->name
             (stringp name)
             :rule-classes :type-prescription)
            (booleanp-of-vl-fundecl->automaticp
             (booleanp automaticp)
             :rule-classes :type-prescription)
            (vl-funtype-p-of-vl-fundecl->rtype
             (vl-funtype-p rtype))
            (vl-maybe-range-p-of-vl-fundecl->rrange
             (vl-maybe-range-p rrange))
            (vl-funinputlist-p-of-vl-fundecl->inputs
             (vl-funinputlist-p inputs))
            (vl-blockitemlist-p-of-vl-fundecl->decls
             (vl-blockitemlist-p decls))
            (vl-stmt-p-of-vl-fundecl->body
             (vl-stmt-p body))
            (vl-atts-p-of-vl-fundecl->atts
             (vl-atts-p atts))
            (vl-location-p-of-vl-fundecl->loc
             (vl-location-p loc)))
  :parents (modules)
  :short "Representation of a single Verilog function."

  :long "<p>Functions are described in Section 10.4 of the standard.  An
example of a function is:</p>

<code>
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
</code>

<p>Note that functions don't have any inout or output ports.  Instead, you
assign to a function's name to indicate its return value.</p>

<h3>Representation of Functions</h3>

<p>The <tt>name</tt> is a string that names the function, e.g.,
<tt>\"lower_bits\"</tt>.</p>

<p>The <tt>automaticp</tt> flag says whether the <tt>automatic</tt> keyword was
provided.  This keyword indicates that the function should be reentrant and
have its local parameters dynamically allocated for each function call, with
various consequences.</p>

<p>The <tt>rtype</tt> is a @(see vl-funtype-p) that describes the return type
of the function, e.g., a function might return an ordinary unsigned or signed
result of some width, or might return a <tt>real</tt> value, etc.  For
instance, the return type of <tt>lower_bits</tt> is <tt>:vl-unsigned</tt>.</p>

<p>The <tt>rrange</tt> is a @(see vl-maybe-range-p) that describes the width of
the function's result.  This only makes sense when the <tt>rtype</tt> is
<tt>:vl-unsigned</tt> or <tt>:vl-signed</tt>.  For instance, the return range
of <tt>lower_bits</tt> is <tt>[7:0]</tt>.</p>

<p>The <tt>inputs</tt> are the arguments to the function, e.g., <tt>input [7:0]
a</tt> above.  We represent these inputs as an @(see vl-funinputlist-p).  Note
that although functions must have at least one input (and we do check for this
in our parser), we don't syntactically enforce this requirement in the
<tt>vl-fundecl-p</tt> structure.</p>

<p>The <tt>decls</tt> are the local variable declarations for the function,
e.g., the declarations of <tt>lowest_pair</tt> and <tt>next_lowest_pair</tt>
above.  We represent the declarations as an ordinary @(see vl-blockitemlist-p),
and it appears that it may even contain event declarations, parameter
declarations, etc., which seems pretty absurd.</p>

<p>The <tt>body</tt> is a @(see vl-stmt-p) that gives the body of the function.
We represent this as an ordinary statement, but it must follow certain rules as
outlined in 10.4.4, e.g., it cannot have any time controls, cannot enable
tasks, cannot have non-blocking assignments, etc.</p>

<p>The <tt>atts</tt> are any attributes (see @(see vl-atts-p)) associated with
this function.  The attributes come before the <tt>function</tt> keyword.</p>

<p>The <tt>loc</tt> is the @(see vl-location-p) where the <tt>function</tt>
keyword was found in the source code.</p>")

(deflist vl-fundecllist-p (x)
  (vl-fundecl-p x)
  :guard t
  :elementp-of-nil nil)

(defprojection vl-fundecllist->names (x)
  (vl-fundecl->name x)
  :guard (vl-fundecllist-p x)
  :nil-preservingp t
  :result-type string-listp)

(defthm acl2-count-of-vl-fundecl->body
  (and (<= (acl2-count (vl-fundecl->body x))
           (acl2-count x))
       (implies (consp x)
                (< (acl2-count (vl-fundecl->body x))
                   (acl2-count x))))
  :hints(("Goal" :in-theory (enable vl-fundecl->body)))
  :rule-classes ((:rewrite) (:linear)))







(defaggregate vl-module
  (name
   params
   ports
   portdecls
   assigns
   netdecls
   vardecls
   regdecls
   eventdecls
   paramdecls
   fundecls
   modinsts
   gateinsts
   alwayses
   initials
   atts
   minloc
   maxloc
   origname
   warnings
   comments
   esim
   )
  :tag :vl-module
  :legiblep nil
  :require
  ((stringp-of-vl-module->name
    (stringp name)
    :rule-classes :type-prescription)

   ;; BOZO add params?
   (vl-portlist-p-of-vl-module->ports           (vl-portlist-p ports))
   (vl-portdecllist-p-of-vl-module->portdecls   (vl-portdecllist-p portdecls))
   (vl-assignlist-p-of-vl-module->assigns       (vl-assignlist-p assigns))
   (vl-netdecllist-p-of-vl-module->netdecls     (vl-netdecllist-p netdecls))
   (vl-vardecllist-p-of-vl-module->vardecls     (vl-vardecllist-p vardecls))
   (vl-regdecllist-p-of-vl-module->regdecls     (vl-regdecllist-p regdecls))
   (vl-eventdecllist-p-of-vl-module->eventdecls (vl-eventdecllist-p eventdecls))
   (vl-paramdecllist-p-of-vl-module->paramdecls (vl-paramdecllist-p paramdecls))
   (vl-fundecllist-p-of-vl-module->fundecls     (vl-fundecllist-p fundecls))
   (vl-modinstlist-p-of-vl-module->modinsts     (vl-modinstlist-p modinsts))
   (vl-gateinstlist-p-of-vl-module->gateinsts   (vl-gateinstlist-p gateinsts))
   (vl-alwayslist-p-of-vl-module->alwayses      (vl-alwayslist-p alwayses))
   (vl-initiallist-p-of-vl-module->initials     (vl-initiallist-p initials))
   (vl-atts-p-of-vl-module->atts                (vl-atts-p atts))
   (vl-location-p-of-vl-module->minloc          (vl-location-p minloc))
   (vl-location-p-of-vl-module->maxloc          (vl-location-p maxloc))

   (stringp-of-vl-module->origname
    (stringp origname)
    :rule-classes :type-prescription)

   (vl-warninglist-p-of-vl-module->warnings     (vl-warninglist-p warnings))
   (vl-commentmap-p-of-vl-module->comments      (vl-commentmap-p comments))
   )
  :parents (modules)
  :short "Representation of a single module."

  :long "<p>This is our representation for a single module.  There are
many fields.</p>

<h4>Semantically Meaningful Fields</h4>

<p>The <tt>name</tt> is the name of this module as a string.  The name is used
to instantiate this module, so generally we require that modules in our list
have unique names.  A module's name is initially set when it is parsed, but is
not guaranteed to remain fixed throughout simplification.  In particular, it is
currently changed during @(see unparameterization), e.g., a module named
<tt>adder</tt> may be renamed to <tt>adder$size=12</tt>.  We may also wish to
change module names it in other, future transformations.</p>

<h5>Ports and Parameters</h5>

<p>The <tt>ports</tt> are a list of @(see vl-port-p) objects that describe the
module's ports, i.e., <tt>a</tt>, <tt>b</tt>, and <tt>c</tt> in <tt>module
mod(a,b,c);</tt>.</p>

<p>The <tt>portdecls</tt> are a list of @(see vl-portdecl-p) objects that
describe the input, output, and inout declarations for this module, e.g.,
<tt>input [3:0] a;</tt>.</p>

<p>The <tt>paramdecls</tt> are a list of @(see vl-paramdecl-p) objects that
describe all of the parameter declarations for this module, e.g., <tt>parameter
width = 1;</tt>.</p>


<h5>Other Declarations</h5>

<p>The <tt>netdecls</tt> are a list of @(see vl-netdecl-p) objects that
describe all of the wire declarations such as <tt>wire [3:0] w;</tt> and
<tt>tri v;</tt>.  Note that registers and variables (integer, real, ...)  are
kept separately.</p>

<p>The <tt>regdecls</tt> are a list of @(see vl-regdecl-p) objects that
describe all register declarations like <tt>reg [3:0] r;</tt>.</p>

<p>The <tt>vardecls</tt> are a list of @(see vl-vardecl-p) objects that
describe all variable declarations like <tt>integer i;</tt> and <tt>real
foo;</tt>.</p>

<p>The <tt>eventdecls</tt> are a list of @(see vl-eventdecl-p) objects that
describe any events for the module.</p>

<p>The <tt>fundecls</tt> are a list of @(see vl-fundecl-p) objects that
describe any functions for the module.</p>



<h5>Assignments and Instances</h5>

<p>The <tt>assigns</tt> are a list of @(see vl-assign-p) objects that describe
the continuous assignments in this module, e.g., <tt>assign lhs = rhs;</tt>.</p>

<p>The <tt>modinsts</tt> are a list of @(see vl-modinst-p) objects that
describe all submodule (or user-defined primitive) instances in this module,
e.g., <tt>adder my_adder1 (...);</tt>.</p>

<p>The <tt>gateinsts</tt> are a list of @(see vl-gateinst-p) objects that
describe any primitive gate instances in this module, e.g., <tt>and (o, a,
b);</tt>.</p>


<h5>Statements</h5>

<p>The <tt>alwayses</tt> are a list of @(see vl-always-p) objects that describe
any <tt>always</tt> statements found in the module.</p>

<p>The <tt>initials</tt> are a list of @(see vl-initial-p) objects that describe
any <tt>initial</tt> statements found in the module.</p>


<h5>Miscellaneous</h5>

<p>The <tt>params</tt> are any <tt>defparam</tt> statements found in the
module.  BOZO eventually provide better support for this and document the
structure of these defparams.</p>

<p>The <tt>warnings</tt> for a module is an @(see warnings) accumulator that
stores any problems we have with this module.  Warnings are semantically
meaningful only in that any <i>fatal</i> warning indicates the module is
invalid and should not be discarded.  The list of warnings may be extended by
any transformation or well-formedness check.</p>


<h4>Semantically Irrelevant Fields</h4>

<p>The <tt>origname</tt> of a module is its original name in the source code (a
string).  It is set at parse-time, and is expected to remain fixed throughout
all simplifications.  That is, while a module named <tt>adder</tt> might be
renamed to <tt>adder$size=12</tt> during unparameterization, its origname will
always be <tt>adder</tt>.  The <tt>origname</tt> is only intended to be used
for display purposes such as hyperlinking.</p>

<p>The <tt>minloc</tt> and <tt>maxloc</tt> fields are @(see vl-location-p)
objects that describe the locations of the <tt>module</tt> and
<tt>endmodule</tt> keywords that we encountered when parsing this module.
These fields remain fixed throughout the simplification process, and
are mainly useful for displaying the module.</p>

<p>The <tt>atts</tt> are a @(see vl-atts-p) object for any <tt>(*
... *)</tt>-style attributes associated with this module.  This list is
initially set at parse time, and may be consulted or extended by
transformations.</p>

<p>The <tt>comments</tt> field is a @(see vl-commentmap-p) that maps locations
to source-code comments that occurred in this module.  We expect that comments
are never consulted for any semantic content, and this field is mainly intended
for displaying the transformed module with comments preserved.</p>


<h4>Fields for E Translation</h4>

<p>The <tt>esim</tt> field is a temporary/historic artifact used in the
translation to @(see esim).  This is in flux so I'm not going to document it
right now.</p>")

(deflist vl-modulelist-p (x)
  (vl-module-p x)
  :elementp-of-nil nil
  :parents (modules))


(defund vl-module->hands-offp (x)
  (declare (xargs :guard (vl-module-p x)))
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
  :parents (vl-modulelist-p))

(defthm vl-modinstlist-p-of-vl-modulelist->modinsts
  (implies (force (vl-modulelist-p x))
           (vl-modinstlist-p (vl-modulelist->modinsts x)))
  :hints(("Goal" :induct (len x))))


(defprojection vl-modulelist->esims (x)
  (vl-module->esim x)
  :guard (vl-modulelist-p x)
  :nil-preservingp t
  :parents (vl-modulelist-p))





(defsection vl-maybe-module-p
  :parents (vl-expr-p)
  :short "Recognizer for an @(see vl-module-p) or <tt>nil</tt>."

  (definlined vl-maybe-module-p (x)
    (declare (xargs :guard t))
    (or (not x)
        (vl-module-p x)))

  (local (in-theory (enable vl-maybe-module-p)))

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
