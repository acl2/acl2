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
(include-book "expr")
(include-book "util/commentmap")
(include-book "util/warnings")
(include-book "tools/flag" :dir :system)
(local (include-book "util/arithmetic"))

(defxdoc syntax
  :parents (vl)
  :short "Representation of Verilog structures."

  :long "<p>We now describe our representation of Verilog's syntactic
structures.  For each kind of Verilog construct (expressions, statements,
declarations, instances, etc.) we introduce recognizer, constructor, and
accessor functions that enforce certain basic well-formedness criteria.</p>

<p>These structures correspond fairly closely to parse trees in the Verilog
grammar, although we make many simplifcations and generally present a much more
regular view of the source code.</p>")

(local (xdoc::set-default-parents syntax))

(defaggregate vl-range
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

<p>Even after the expressions have become constants, the Verilog-2005 standard
does not require @('msb') to be greater than @('lsb'), and neither index is
required to be zero.  In fact, even negative indicies seem to be permitted,
which is quite amazing and strange.</p>

<p>While we do not impose any restrictions in @('vl-range-p') itself, some
transformations expect the indices to be resolved to integers.  However, we now
try to support the use of both ascending and descending ranges.</p>")

(define vl-maybe-range-p (x)
  :parents (syntax vl-range-p)
  :short "Representation for a @(see vl-range-p) or @('nil')."
  :long "<p>This is a basic option type for ranges.</p>"
  :inline t
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
  :elementp-of-nil t)

(deflist vl-rangelist-p (x)
  (vl-range-p x)
  :elementp-of-nil nil)

(deflist vl-rangelist-list-p (x)
  (vl-rangelist-p x)
  :elementp-of-nil t)


(defaggregate vl-port
  :short "Representation of a single Verilog port."
  :tag :vl-port
  :legiblep nil

  ((name maybe-stringp
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

  :long "<p>Ports are described in Section 12.3 of Verilog-2005.  In simple
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
  :elementp-of-nil nil)

(defprojection vl-portlist->exprs (x)
  :parents (vl-portlist-p)
  :guard (vl-portlist-p x)
  :nil-preservingp t
  (vl-port->expr x)
  ///
  (defthm vl-exprlist-p-of-vl-portlist->exprs
    (implies (force (vl-portlist-p x))
             (equal (vl-exprlist-p (vl-portlist->exprs x))
                    (not (member nil (vl-portlist->exprs x))))))

  (defthm vl-exprlist-p-of-remove-equal-of-vl-portlist->exprs
    (implies (force (vl-portlist-p x))
             (vl-exprlist-p (remove-equal nil (vl-portlist->exprs x))))))

(defprojection vl-portlist->names (x)
  :parents (vl-portlist-p)
  :guard (vl-portlist-p x)
  :nil-preservingp t
  (vl-port->name x))


(defenum vl-direction-p (:vl-input :vl-output :vl-inout)
  :short "Direction for a port declaration (input, output, or inout)."

  :long "<p>Each port declaration (see @(see vl-portdecl-p)) includes a
direction to indicate that the port is either an input, output, or inout.  We
represent these directions with the keyword @(':vl-input'), @(':vl-output'),
and @(':vl-inout'), respectively.</p>

<p>In our @(see argresolve) transformation, directions are also assigned to all
arguments of gate instances and most arguments of module instances.  See our
@(see vl-plainarg-p) structures for more information.</p>")


(define vl-maybe-direction-p (x)
  :short "Representation for a @(see vl-direction-p) or @('nil')."
  :long "<p>This is a basic option type for directions.</p>"
  :inline t
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
              vl-portdecl-and-moduleitem-compatible-p) as part of our notion of
              @(see reasonable) modules.")

   (atts     vl-atts-p
             "Any attributes associated with this declaration.")

   (loc      vl-location-p
             "Where the port was declared in the source code."))

  :long "<p>Port declarations, described in Section 12.3.3 of the Verilog-2005
standard, ascribe certain properties (direction, signedness, size, and so on)
to the ports of a module.  Here is an example:</p>

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
@('type') field.  However, upon a closer reading of the Verilog-2005 standard,
we have learned that the proper way to handle these is to simultaneously
introduce a @(see vl-netdecl-p) alongside the @('vl-portdecl-p') that we would
ordinarily create for a port declaration.  See, e.g., the second paragraph from
the bottom on Page 174.</p>")

(deflist vl-portdecllist-p (x)
  (vl-portdecl-p x)
  :elementp-of-nil nil)


(defaggregate vl-gatedelay
  :short "Representation of delay expressions."
  :tag :vl-gatedelay
  :legiblep nil

  ((rise vl-expr-p "Rising delay.")
   (fall vl-expr-p "Falling delay.")
   (high vl-maybe-expr-p "High-impedence delay or charge decay time." ))

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
  :short "Representation for a @(see vl-gatedelay-p) or @('nil')."
  :long "<p>This is a basic option type for gatedelays.</p>"
  :inline t
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

<p>BOZO add references to the Verilog-2005 standard, description of what these
are.</p>")


(defaggregate vl-gatestrength
  :short "Representation of strengths for a assignment statements, gate
instances, and module instances."
  :tag :vl-gatestrength
  :legiblep nil

  ((zero vl-dstrength-p "Drive strength toward logical zero.")
   (one  vl-dstrength-p "Drive strength toward logical one."))

  :long "<p><b>WARNING</b>.  We have not paid much attention to strengths, and
our transformations probably do not handle them properly.</p>

<p>See sections 7.1.2 and 7.9 of the Verilog-2005 standard for discussion of
strength modelling.  Every regular gate has, associated with it, two drive
strengths; a \"strength0\" which says how strong its output is when it is a
logical zero, and \"strength1\" which says how strong the output is when it is
a logical one.  Strengths also seem to be used on assignments and module
instances.</p>

<p>There seem to be some various rules for default strengths in 7.1.2, and also
in 7.13.  But our parser does not try to implement these defaults, and we only
associate strengths onto module items where they are explicitly
specified.</p>")

(define vl-maybe-gatestrength-p (x)
  :short "Representation for a @(see vl-gatestrength-p) or @('nil')."
  :long "<p>This is a basic option type for gatestrengths.</p>"
  :inline t
  (or (not x)
      (vl-gatestrength-p x))
  ///
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
  :short "Representation of charge strengths."

  :long "<p>We represent Verilog's charge strengths with the keyword symbols
recognized by @(call vl-cstrength-p).</p>

<p>BOZO add references to the Verilog-2005 standard, description of what these
are.</p>")


(define vl-maybe-cstrength-p (x)
  :short "Representation for a @(see vl-cstrength-p) or @('nil')."
  :long "<p>This is a basic option type for cstrengths.</p>"
  :inline t
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
in the Verilog-2005 standard.  Even so, it seems there must be some limits.
For instance, what does it mean to assign, say, a minimum/typical/maximum delay
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
  :elementp-of-nil nil)

(defprojection vl-assignlist->lvalues (x)
  :parents (vl-assignlist-p)
  :guard (vl-assignlist-p x)
  :nil-preservingp t
  :result-type vl-exprlist-p
  (vl-assign->lvalue x))

; BOZO I'm not going to introduce this yet.  I think we should rename the expr
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
  :parents (vl-netdecl-p)
  :short "Representation of wire types."

  :long "<p>Wires in Verilog can be given certain types.  We
represent these types using certain keyword symbols, whose names
correspond to the possible types.</p>")

(define vl-maybe-netdecltype-p (x)
  :parents (vl-netdecl-p)
  :short "Representation for a @(see vl-netdecltype-p) or @('nil')."
  :long "<p>This is a basic option type for netdecltypes.</p>"
  :inline t
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

<p>I do not know what these keywords are supposed to mean; the Verilog-2005
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
  :elementp-of-nil nil)


(defaggregate vl-plainarg
  :parents (syntax vl-arguments-p)
  :short "Representation of a single argument in a plain argument list."
  :tag :vl-plainarg
  :legiblep nil

  ((expr     vl-maybe-expr-p
             "Expression being connected to the port.  In programming languages
              parlance, this is the <i>actual</i>.  Note that this may be
              @('nil') because Verilog allows expressions to be \"blank\", in
              which case they represent an unconnected wire.")

   (portname maybe-stringp
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
  :elementp-of-nil nil)

(deflist vl-plainarglistlist-p (x)
  (vl-plainarglist-p x)
  :elementp-of-nil t
  ///
  (defthm vl-plainarglist-p-of-strip-cars
    (implies (and (vl-plainarglistlist-p x)
                  (all-have-len x n)
                  (not (zp n)))
             (vl-plainarglist-p (strip-cars x))))

  (defthm vl-plainarglistlist-p-of-strip-cdrs
    (implies (vl-plainarglistlist-p x)
             (vl-plainarglistlist-p (strip-cdrs x)))))

(defprojection vl-plainarglist->exprs (x)
  :guard (vl-plainarglist-p x)
  :nil-preservingp t
  (vl-plainarg->expr x)
  ///
  (defthm vl-exprlist-p-of-vl-plainarglist->exprs
    (implies (force (vl-plainarglist-p x))
             (equal (vl-exprlist-p (vl-plainarglist->exprs x))
                    (not (member nil (vl-plainarglist->exprs x))))))

  (defthm vl-exprlist-p-of-remove-nil-of-plainarglist->exprs
    (implies (vl-plainarglist-p x)
             (vl-exprlist-p (remove nil (vl-plainarglist->exprs x))))))


(defaggregate vl-namedarg
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
  :elementp-of-nil nil)


(defsection vl-arguments-p
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
  :elementp-of-nil nil)



(defaggregate vl-modinst
  :short "Representation of a single module (or user-defined primitive)
instance."
  :tag :vl-modinst
  :legiblep nil

  ((instname  maybe-stringp
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
  :elementp-of-nil nil)


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
  :short "Representation of gate types."
  :long "<p>We represent Verilog's gate types with the keyword symbols
recognized by @(call vl-gatetype-p).</p>")

(defaggregate vl-gateinst
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

   (name     maybe-stringp
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
              Note from Section 7.8 of the Verilog-2005 standard that pullup
              and pulldown gates are special in that the strength0 from a
              pullup source and the strength1 on a pulldown source are supposed
              to be ignored.  <b>Warning:</b> in general we have not paid much
              attention to strengths, so we may not handle them correctly in
              our various transforms.")

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
  :elementp-of-nil nil)



(defenum vl-vardecltype-p
  (:vl-integer
   :vl-real
   :vl-time
   :vl-realtime)
  :short "Representation of variable types."
  :long "<p>We represent Verilog's variable types with the keyword symbols
recognized by @(call vl-vardecltype-p).</p>

<p><b>BOZO</b> consider consolidating variable and register declarations into a
single parse tree element by adding an extra reg type to vl-vardecl-p.</p>")

(defaggregate vl-vardecl
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
  :elementp-of-nil nil)

(deflist vl-regdecllist-p (x)
  (vl-regdecl-p x)
  :elementp-of-nil nil)

(deflist vl-eventdecllist-p (x)
  (vl-eventdecl-p x)
  :elementp-of-nil nil)

(deflist vl-paramdecllist-p (x)
  (vl-paramdecl-p x)
  :elementp-of-nil nil)

(deflist vl-paramdecllist-list-p (x)
  (vl-paramdecllist-p x)
  :elementp-of-nil t)



(define vl-blockitem-p (x)
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
  :elementp-of-nil nil)


(defaggregate vl-eventcontrol
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
  :short "Representation of a delay controller like @('#6')."
  :tag :vl-delaycontrol
  :legiblep nil
  ((value vl-expr-p "The expression that governs the delay amount."))

  :long "<p>Delay controls are described in Section 9.7.  An example is</p>

@({
  #10 foo = 1;   <-- The #10 is a delay control
})")

(defaggregate vl-repeateventcontrol
  :short "Representation of @('repeat') constructs in intra-assignment delays."
  :tag :vl-repeat-eventcontrol
  :legiblep nil
  ((expr vl-expr-p
         "The number of times to repeat the control, e.g., @('3') in the below
          example.")

   (ctrl vl-eventcontrol-p
         "Says which event to wait for, e.g., @('@(posedge clk)') in the below
          example."))

  :long "<p>See Section 9.7.7 of the Verilog-2005 standard.  These are used to
represent special intra-assignment delays, where the assignment should not
occur until some number of occurrences of an event.  For instance:</p>

@({
   a = repeat(3) @(posedge clk)   <-- repeat expr ctrl
         b;                       <-- statement to repeat
})

<p><b>BOZO</b> Consider consolidating all of these different kinds of
controls into a single, unified representation.  E.g., you could at
least extend eventcontrol with a maybe-expr that is its count, and get
rid of repeateventcontrol.</p>")

(define vl-delayoreventcontrol-p (x)
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
  :short "BOZO document this."
  :inline t
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
respectively.</p>")

(defaggregate vl-assignstmt
  :parents (vl-stmt-p)
  :short "Representation of an assignment statement."
  :tag :vl-assignstmt
  :legiblep nil

  ((type   vl-assign-type-p
           "Kind of assignment statement, e.g., blocking, nonblocking, etc.")

   (lvalue vl-expr-p
           "Location being assigned to.  Note that the Verilog-2005 standard
            places various restrictions on lvalues, e.g., for a procedural
            assignment the lvalue may contain only plain variables, and
            bit-selects, part-selects, memory words, and nested concatenations
            of these things.  We do not enforce these restrictions in
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
   (name        maybe-stringp)
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

   (name        maybe-stringp
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
                  (force (maybe-stringp name))
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
  :parents (vl-atomicstmt-p vl-stmt-p)
  :short "Faster version of @(see vl-atomicstmt-p), given that @(see vl-stmt-p)
is already known."
  :long "<p>We leave this function enabled and reason about
@('vl-atomicstmt-p') instead.</p>"
  :inline t
  :enabled t
  (mbe :logic (vl-atomicstmt-p x)
       :exec (not (eq (tag x) :vl-compoundstmt))))

(define vl-fast-compoundstmt-p ((x vl-stmt-p))
  :parents (vl-compoundstmt-p vl-stmt-p)
  :short "Faster version of @(see vl-compoundstmt-p), given that @(see
vl-stmt-p) is already known."
  :long "<p>We leave this function enabled and reason about
@('vl-compoundstmt-p') instead.</p>"
  :inline t
  :enabled t
  (mbe :logic (vl-compoundstmt-p x)
       :exec (eq (tag x) :vl-compoundstmt)))

(define vl-fast-nullstmt-p ((x vl-stmt-p))
  :parents (vl-nullstmt-p vl-stmt-p)
  :short "Faster version of @(see vl-nullstmt-p), given that @(see vl-stmt-p)
is already known."
  :long "<p>We leave this function enabled and reason about @('vl-nullstmt-p')
instead.</p>"
  :inline t
  :enabled t
  (mbe :logic (vl-nullstmt-p x)
       :exec (eq (tag x) :vl-nullstmt)))

(define vl-fast-assignstmt-p ((x vl-stmt-p))
  :parents (vl-assignstmt-p vl-stmt-p)
  :short "Faster version of @(see vl-assignstmt-p), given that @(see vl-stmt-p)
is already known."
  :long "<p>We leave this function enabled and reason about
@('vl-assignstmt-p') instead.</p>"
  :inline t
  :enabled t
  (mbe :logic (vl-assignstmt-p x)
       :exec (eq (tag x) :vl-assignstmt)))

(define vl-fast-enablestmt-p ((x vl-stmt-p))
  :parents (vl-enablestmt-p vl-stmt-p)
  :short "Faster version of @(see vl-enablestmt-p), given that @(see vl-stmt-p)
is already known."
  :long "<p>We leave this function enabled and reason about
@('vl-enablestmt-p') instead.</p>"
  :inline t
  :enabled t
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
  :returns (atts vl-atts-p :hyp :fguard)
  :parents (vl-stmt-p)
  :short "Get the attributes from any statement."
  :inline t
  (if (vl-fast-atomicstmt-p x)
      (vl-atomicstmt->atts x)
    (vl-compoundstmt->atts x)))



;                       INITIAL AND ALWAYS BLOCKS
;
; Initial and always blocks just have a statement and, perhaps, some
; attributes.

(defaggregate vl-initial
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
  :elementp-of-nil nil)

(deflist vl-alwayslist-p (x)
  (vl-always-p x)
  :elementp-of-nil nil)



(defenum vl-taskporttype-p
  (:vl-unsigned
   :vl-signed
   :vl-integer
   :vl-real
   :vl-realtime
   :vl-time)
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
  :elementp-of-nil nil)

(defprojection vl-taskportlist->names (x)
  :guard (vl-taskportlist-p x)
  :nil-preservingp t
  :result-type string-listp
  (vl-taskport->name x))


(defaggregate vl-fundecl
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

  :long "<p>Functions are described in Section 10.4 of the Verilog-2005
standard.  An example of a function is:</p>

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
  :elementp-of-nil nil)

(defprojection vl-fundecllist->names (x)
  :guard (vl-fundecllist-p x)
  :nil-preservingp t
  :result-type string-listp
  (vl-fundecl->name x))


(defaggregate vl-taskdecl
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

  :long "<p>Tasks are described in Section 10.2 of the Verilog-2005 standard.
An example of a task is:</p>

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
  :elementp-of-nil nil)

(defprojection vl-taskdecllist->names (x)
  :guard (vl-taskdecllist-p x)
  :nil-preservingp t
  :result-type string-listp
  (vl-taskdecl->name x))


(defaggregate vl-module
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
  :elementp-of-nil nil)

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
  :inline t
  (consp (assoc-equal "VL_HANDS_OFF" (vl-module->atts x))))

(defprojection vl-modulelist->names (x)
  :parents (vl-modulelist-p)
  :guard (vl-modulelist-p x)
  :result-type string-listp
  :nil-preservingp t
  (vl-module->name x))

(defprojection vl-modulelist->paramdecls (x)
  :parents (vl-modulelist-p)
  :guard (vl-modulelist-p x)
  :result-type vl-paramdecllist-list-p
  :nil-preservingp t
  (vl-module->paramdecls x))

(defmapappend vl-modulelist->modinsts (x)
  (vl-module->modinsts x)
  :parents (vl-modulelist-p)
  :guard (vl-modulelist-p x)
  :transform-true-list-p nil
  :rest ((defthm vl-modinstlist-p-of-vl-modulelist->modinsts
           (implies (force (vl-modulelist-p x))
                    (vl-modinstlist-p (vl-modulelist->modinsts x))))))

(defprojection vl-modulelist->esims (x)
  :parents (vl-modulelist-p)
  :guard (vl-modulelist-p x)
  :nil-preservingp t
  (vl-module->esim x))


(define vl-maybe-module-p (x)
  :parents (vl-module-p)
  :short "Recognizer for an @(see vl-module-p) or @('nil')."
  :inline t
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


(defaggregate design
  :short "Top level representation of all modules, interfaces, programs, etc.,
resulting from parsing some Verilog source code."
  :tag :vl-design
  :legiblep nil
  ((mods vl-modulelist-p
         "List of all modules")
   (udps       "List of user defined primtives")
   (interfaces "List of interfaces")
   (programs   "List of all programs")
   (packages   "List of all packages")
   ;; package items?
   ;; bind directives?
   (configs    "List of configurations")))

