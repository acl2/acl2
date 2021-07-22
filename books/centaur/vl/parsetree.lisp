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
(include-book "expr")
(include-book "../sv/svex/svex")
(include-book "util/commentmap")
(include-book "util/warnings")
(include-book "util/defs")
(include-book "tools/flag" :dir :system)
(include-book "tools/templates" :dir :system)
(local (include-book "util/arithmetic"))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable double-containment)))
(local (in-theory (disable vl-atts-p-of-cdr-when-vl-atts-p
                           ;; vl-atts-p-when-subsetp-equal
                           ;; alistp-when-vl-atts-p-rewrite
                           default-car default-cdr
                           acl2::lower-bound-of-car-when-nat-listp
                           stringp-when-true-listp
                           acl2::consp-when-member-equal-of-cons-listp
                           acl2::consp-when-member-equal-of-atom-listp
                           consp-when-member-equal-of-vl-commentmap-p
                           ;; consp-when-member-equal-of-vl-atts-p
                           (tau-system))))


(defxdoc syntax
  :parents (vl)
  :short "Internal representation of the syntax of Verilog and SystemVerilog."

  :long "<h3>Introduction</h3>

<p>A core component of @(see VL) is its internal representation of Verilog's
syntactic structures.  For each kind of Verilog construct (expressions,
statements, declarations, instances, etc.) we introduce corresponding ``types''
with their own recognizer, constructor, and accessor functions.</p>

<p>These structures generally correspond fairly closely to parse trees in the
SystemVerilog grammar, except that:</p>

<ul>

<li>We sometimes make certain <b>simplifications</b> to present a more regular
view of the source code.  For instance, whereas in a normal Verilog module you
might write something like @('wire [3:0] a, b, c;') to simultaneously declare
several wires, our internal representation treats each wire declaration
separately, as if you had instead written @('wire [3:0] a; wire [3:0] b; wire
[3:0] c;').</li>

<li>We generally <b>separate</b> the various kinds of parsed elements (e.g.,
assignments, declarations, etc.) out into distinct lists, whereas in the source
code these elements may be all mixed together.  This is sometimes slightly
tricky; see also the @(see loader) and the @(see annotate) transform.</li>

<li>Many structures also contain various <b>additional fields</b> that are not
purely part of the syntax.  For instance, many structures include @(see
vl-location) annotations to say where they came from, expressions include
annotations about whether they have explicit parentheses, and high-level design
elements like modules have @(see warnings) attached to them.</li>

</ul>

<p>We introduce all of these structures using the @(see fty) library and
following the fixtype discipline.  This generally means that each type has an
associated fixing function, equivalence relation, etc.  If you aren't familiar
with fty, you may want to learn a bit about it before trying to understand
these structures.</p>

<h3>Quick Guide</h3>

<p>SystemVerilog is a huge language (the grammar is about 45 pages!) so it can
be easy to get lost in all of the different kinds of constructs.  Here is a
quick guide to the most major syntactic definitions:</p>

<ul>

<li>@(see vl-design) is our top-level representation of an <b>entire
design</b>, including all of the modules, interfaces, packages, programs, etc.,
typically spread out across many Verilog or SystemVerilog source files.  If you
start here and then drive down into the fields, you'll eventually explore all
of our syntactic constructs.</li>

<li>Many kinds of major <b>design elements</b> can occur in a design, e.g.,
modules, interfaces, packages, programs, configs, user defined primitives, etc.
We represent these with, e.g., @(see vl-module), @(see vl-interface), @(see
vl-package), @(see vl-program), @(see vl-config), @(see vl-udp), etc.</li>

<li><b>Modules</b> are the mainstay of most designs.  Most modules contain
things like assignments, gate and module instances, always blocks, initial
blocks, aliases, and so on.  We represent these module elements using, e.g.,
@(see vl-assign), @(see vl-gateinst), @(see vl-modinst), @(see vl-always),
@(see vl-initial), @(see vl-final), @(see vl-alias), etc.</li>

<li>Other widely used constructs include <b>declarations</b> of many kinds,
e.g., variables, ports, parameters, functions, tasks, types.  See for instance
@(see vl-vardecl), @(see vl-port) and @(see vl-portdecl), @(see vl-paramdecl),
@(see vl-fundecl), @(see vl-taskdecl), and @(see vl-typedef).</li>

<li>Underpinning all of the above are <b><see topic='@(url
expressions-and-datatypes)'>Expressions and Datatypes</see></b>.  These are
mutually recursive since expressions like casts can include types while many
datatypes use expressions for indexes and so forth.</li>

<li>Various constructs like always/initial/final blocks and functions and tasks
also make use of <b>procedural @(see statements)</b> like if/else, case
statements, and for loops.  Some notable statements include @(see
vl-assertstmt) and @(see vl-cassertstmt) for immediate and concurrent
SystemVerilog assertions.  Note that concurrent assertions also involve an
elaborate notion of @(see property-expressions).</li>

</ul>

<p>The above isn't entirely comprehensive; for instance a good deal of stuff is
needed to represent generate statements; see @(see vl-genelement).  There are
also various unfinished areas like support for SystemVerilog assertions.</p>")

(local (xdoc::set-default-parents syntax))


; ----------------------------------------------------------------------------
;
;                            BIG WARNING MESSAGE
;
;     If you modify the any actual parse-tree syntax,
;
;                               then you should update the syntax version!
;
; ----------------------------------------------------------------------------

(defxdoc vl-syntaxversion
  :short "Version of VL @(see syntax) being used."

  :long "<p>Occasionally VL's internal data structures change, e.g., to add new
fields or adjust the way that some field is represented.  As a barbaric
mechanism to make sure that we don't try to mix together translations produced
by incompatible versions of VL, each @(see vl-design) is annotated with a
@('version') field that must match exactly this string.</p>")

(defval *vl-current-syntax-version*
  :parents (vl-syntaxversion)
  :short "Current syntax version: @(`*vl-current-syntax-version*`)."
  "VL Syntax 2016-08-26")

(define vl-syntaxversion-p (x)
  :parents (vl-syntaxversion)
  (equal x *vl-current-syntax-version*))

(define vl-syntaxversion-fix (x)
  :parents (vl-syntaxversion)
  :returns (version vl-syntaxversion-p)
  (if (vl-syntaxversion-p x)
      x
    *vl-current-syntax-version*)
  ///
  (defthm vl-syntaxversion-fix-when-vl-syntaxversion-p
    (implies (vl-syntaxversion-p x)
             (equal (vl-syntaxversion-fix x) x))))

(defsection vl-syntaxversion-equiv
  :parents (vl-syntaxversion)
  (deffixtype vl-syntaxversion
    :pred vl-syntaxversion-p
    :fix vl-syntaxversion-fix
    :equiv vl-syntaxversion-equiv
    :define t
    :forward t))


(defprod vl-eventcontrol
  :short "Representation of an event controller like @('@(posedge clk)') or
@('@(a or b)')."
  :tag :vl-eventcontrol
  :layout :tree

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

(defprod vl-delaycontrol
  :short "Representation of a delay controller like @('#6')."
  :tag :vl-delaycontrol
  :layout :tree
  ((value vl-expr-p "The expression that governs the delay amount."))

  :long "<p>Delay controls are described in Section 9.7.  An example is</p>

@({
  #10 foo = 1;   <-- The #10 is a delay control
})")

(defprod vl-repeateventcontrol
  :short "Representation of @('repeat') constructs in intra-assignment delays."
  :tag :vl-repeat-eventcontrol
  :layout :tree
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

(deftranssum vl-delayoreventcontrol
  :short "BOZO document this."
  (vl-delaycontrol
   vl-eventcontrol
   vl-repeateventcontrol))

(local (defthm vl-delayoreventcontrol-fix-nonnil
         (vl-delayoreventcontrol-fix x)
         :hints(("Goal" :in-theory (enable (tau-system))))
         :rule-classes :type-prescription))

(defoption vl-maybe-delayoreventcontrol vl-delayoreventcontrol-p)



(defenum vl-distweighttype-p
  (:vl-weight-each
   :vl-weight-total)
  :parents (vl-exprdist)
  :short "Representation of the @(':=') or @(':/') weight operators."
  :long "<p>See SystemVerilog-2012 Section 18.5.4, Distribution, and also see
@(see vl-distitem).</p>

<ul>

<li>@(':vl-weight-each') stands for the @(':=') operator, which assigns the
same weight to each item in the range.</li>

<li>@(':vl-weight-total') stands for the @(':/') operator, which assigns a
weight to the range as a whole, i.e., the weight of each value in the range
will become @('weight/n') where @('n') is the number of items in the
range.</li>

</ul>

<p>Both operators have the same meaning when applied to a single expression
instead of a range.</p>")

(defprod vl-distitem
  :parents (vl-exprdist)
  :short "Representation of weighted distribution information."
  :layout :tree
  :tag :vl-distitem

  ((left  vl-expr-p
          "The sole or left expression in a dist item.  For instance, @('left')
           will be @('100') in either @('100 := 1') or @('[100:102] := 1').")

   (right vl-maybe-expr-p
          "The right expression in a dist item that has a value range, or nil
           if this dist item just has a single item.  For instance, @('right')
           would be @('nil') in @('100 := 1'), but would be @('102') in
           @('[100:102] := 1').")

   (type  vl-distweighttype-p
          "The weight type, i.e., @(':vl-weight-each') for @(':=')-style dist items,
           or @(':vl-weight-total') for @(':/')-style dist items.  Note per
           SystemVerilog-2012 Section 18.5.4, if no weight is specified, the
           default weight is @(':= 1'), i.e., the default is
           @(':vl-weight-each').")

   (weight vl-expr-p
           "The weight, e.g., @('1') in @('100 := 1').  Note per
            SystemVerilog-2012 Section 18.5.4, if no weight is specified, the
            default weight is @(':= 1'), so the default weight is @('1')."))

  :long "<p>See SystemVerilog-2012 Section 18.5.4, Distribution.  This is our
representation of a single @('dist_item').  The associated grammar rules
are:</p>

@({
     dist_item ::= value_range [ dist_weight ]

     dist_weight ::= ':=' expression             ;; see vl-distweighttype-p
                   | ':/' expression

     value_range ::= expression
                   | [ expression : expression ]
})")

(fty::deflist vl-distlist
  :parents (vl-exprdist)
  :elt-type vl-distitem
  :elementp-of-nil nil)

(defprod vl-exprdist
  :short "Representation of @('expr dist { ... }') constructs."
  :tag :vl-exprdist
  :layout :tree
  ((expr vl-expr-p
         "The left-hand side expression, which per SystemVerilog-2012 Section
          18.5.4 should involve at least one @('rand') variable.")
   (dist vl-distlist-p
         "The desired ranges of values and probability distribution.  May be
          @('nil') in case of a plain expression without any @('dist')
          part."))

  :long "<p>Very confusingly, the @('dist') operator is mentioned in the
SystemVerilog-2012 precedence table (Table 11-2, Page 221).  This doesn't
make any sense because per the grammar rules it only occurs within</p>

@({
     expression_or_dist ::= expression [ 'dist' { dist_list } ]
})

<p>And these @('expression_or_dist') things definitely do not occur within
other expressions.  After some investigation, I believe this inclusion in
the table is simply misleading and that the right way to treat @('dist') is
as a separate construct rather than as a real operator.  See also the file
@('vl/parser/tests/distprec.sv') for related notes and experiments.</p>")

(fty::deflist vl-exprdistlist
  :parents (vl-exprdist)
  :elt-type vl-exprdist)

(defoption vl-maybe-exprdist vl-exprdist-p
  :parents (vl-exprdist))


(defenum vl-repetitiontype-p
  (:vl-repetition-consecutive
   :vl-repetition-goto
   :vl-repetition-nonconsecutive)
  :parents (vl-proprepeat)
  :short "Representation of SystemVerilog assertion sequence repetition types,
i.e., @('[*...]'), @('[->...]'), or @('[=...]') style repetition."
  :long "<p>See SystemVerilog-2012 Section 16.9.2.</p>

<ul>
<li>@('[* ...]'), @('[*]'), and @('[+]') is called <b>consecutive</b> repetition</li>
<li>@('[-> ...]') is called <b>goto</b> repetition</li>
<li>@('[= ...]') is called <b>nonconsecutive</b> repetition</li>
</ul>")

(defprod vl-repetition
  :parents (vl-proprepeat)
  :short "Representation of a SystemVerilog assertion sequence repetition."
  :tag :vl-repetition
  :layout :tree

  ((type vl-repetitiontype-p
         "Kind of repetition, i.e., consecutive, goto, or nonconsecutive.")

   (left vl-expr-p
         "Sole or left bound on the repetition.  Examples: @('left') is 3 for
          any of @('[* 3]'),
                 @('[* 3:4]'),
                 @('[-> 3]'),
                 @('[-> 3:4]'),
                 @('[= 3]'), or
                 @('[= 3:4]').
          In the special cases of @('[*]') and @('[+]'), @('left') should be
          0 and 1, respectively.")

   (right vl-maybe-expr-p
          "Right bound on the repetition if applicable.  For instance,
           @('right') is
                 @('nil') for any of @('[* 3]'),
                                     @('[-> 3]'), or
                                     @('[= 3]').
           It is @('4') for any of @('[* 3:4]'),
                                   @('[-> 3:4]'), or
                                   @('[= 3:4]').
           It is @('$') for @('[*]') or @('[+]')."))

  :long "<p>See SystemVerilog-2012 Section 16.9.2.</p>

<p>Note from Page 357 that @('[*]') is equivalent to @('[0:$]') and @('[+]') is
equivalent to @('[1:$]'), so we don't bother with separate representations of
these.</p>")


(defenum vl-property-unaryop-p
  (:vl-prop-firstmatch       ;;; first_match a
   :vl-prop-not              ;;; not a
   :vl-prop-strong           ;;; strong a
   :vl-prop-weak             ;;; weak a
   )
  :parents (vl-propunary)
  :short "Very basic unary sequence/property operators.")

(defenum vl-property-binaryop-p
  (:vl-prop-and              ;;; a and b
   :vl-prop-intersect        ;;; a intersect b
   :vl-prop-or               ;;; a or b
   :vl-prop-within           ;;; a within b
   :vl-prop-iff              ;;; a iff b
   :vl-prop-until            ;;; a until b
   :vl-prop-suntil           ;;; a s_until b
   :vl-prop-untilwith        ;;; a until_with b
   :vl-prop-suntilwith       ;;; a s_until_with b
   :vl-prop-word-implies     ;;; a implies b        "plain old implies"
   :vl-prop-thin-implies     ;;; a |-> b            "overlapped implication"
   :vl-prop-fat-implies      ;;; a |=> b            "non-overlapped implication"
   :vl-prop-thin-follows     ;;; a #-# b
   :vl-prop-fat-follows      ;;; a #=# b
   )
  :parents (vl-propbinary)
  :short "Very basic binary sequence/property operators."

  :long "<p>The only confusing thing here is the different kinds of implies and
         follows operators.  Here's the mapping:</p>

         <ul>
         <li>@(':vl-prop-word-implies') is literally the keyword @('implies').</li>
         <li>@(':vl-prop-thin-implies') is the operator @('|->'), i.e., overlapped implication.</li>
         <li>@(':vl-prop-fat-implies') is the operator @('|=>'), i.e., non-overlapped implication.</li>
         <li>@(':vl-prop-thin-follows') is the operator @('#-#').</li>
         <li>@(':vl-prop-fat-follows') is the operator @('#=#').</li>
         </ul>")

(defenum vl-property-acceptop-p
  (:vl-prop-accepton         ;;; accept_on(foo) bar
   :vl-prop-syncaccepton     ;;; sync_accept_on(foo) bar
   :vl-prop-rejecton         ;;; reject_on(foo) bar
   :vl-prop-syncrejecton     ;;; sync_reject_on(foo) bar
   )
  :parents (vl-propaccept)
  :short "The @('accept_on'), @('reject_on'), @('sync_accept_on'), and
          @('sync_reject_on') operators."
  :long "<p>These are a bit unusual and take both a condition and a property as
         their arguments.</p>")


(deftypes property-expressions
  :parents (syntax)
  :short "Representation of SystemVerilog property and sequence expressions."

  (deftagsum vl-propexpr
    :measure (two-nats-measure (acl2-count x) 0)
    :short "Representation of a single property or sequence expression."
    :long "<p>Note that SystemVerilog distinguishes between properties and
           sequences.  However, VL internally represents both property and
           sequence expressions using this same data structure.</p>"

    (:vl-propcore
     :short "Basic, single expression in a sequence or property (perhaps
             with some probability distribution stuff.)"
     :base-name vl-propcore
     ((guts vl-exprdist-p)))

    (:vl-propinst
     :short "Instance of a named sequence or property."
     :base-name vl-propinst
     ((ref  vl-scopeexpr-p      "Name of the sequence/property to instance.")
      (args vl-propactuallist-p "Arguments to give it.")))

    (:vl-propthen
     :short "Sequential sequence composition, i.e., @('foo ##1 bar') and similar."
     :base-name vl-propthen
     ((delay vl-range-p
             "The delay or range part between the two sequences.  Note that
              SystemVerilog gives a rich syntax here which we always boil down
              to a range.  In particular, a single expression like @('##1') is
              represented with the range #('[1:1]').  The SystemVerilog syntax
              @('##[*]') just means @('##[0:$]') and the syntax @('##[+]') just
              means @('##[1:$]').  Dollar signs are supposed to mean the end of
              simulation, or for formal tools are supposed to mean some finite
              but unbounded range.")
      (left  vl-propexpr-p  "Left-hand side sequence to match, e.g., @('foo').")
      (right vl-propexpr-p  "Right-hand side sequence to match, e.g., @('bar')."))
     :long "<p>Note that in SystemVerilog you can write sequences that don't have
            a starting expression, e.g., you can just write @('##1 foo ##1 bar').
            In this case, we set @('left') to the expression @('1'), which always
            evaluates to true and hence has no effect on the sequence.</p>")

    (:vl-proprepeat
     :short "A sequence with repetitions."
     :base-name vl-proprepeat
     ((seq   vl-propexpr-p    "Sequence being repeated, e.g., @('foo') in
                               @('foo[*2]').")
      (reps  vl-repetition-p  "Repetitions of this sequence, e.g., @('[*2]') in
                               @('foo[*2]').")))

    (:vl-propassign
     :short "A sequence with sequence match items (updates to its variables)."
     :base-name vl-propassign
     ((seq   vl-propexpr-p "Base sequence being extended with match items, e.g.,
                            @('foo') in the sequence @('foo, x++').")
      (items vl-exprlist-p "Sequence match items that are being attached to this
                            sequence, e.g., @('x++') in the sequence @('(foo,
                            x++)')."))
     :long "<p>These match items can perhaps influence local sequence
            variables, see SystemVerilog-2012 section 16.10.  In practice these
            should be assignment expressions, increment/decrement expression,
            or function calls.  We just represent them as arbitrary
            expressions.</p>")

    (:vl-propthroughout
     :short "A @('throughout') sequence expression."
     :base-name vl-propthroughout
     ((left  vl-exprdist-p "The left hand side expression.")
      (right vl-propexpr-p "The right hand side sequence expression.")))

    (:vl-propclock
     :short "A sequence or property expression with a clocking event."
     :base-name vl-propclock
     ((trigger vl-evatomlist
               "A @('clocking_event'), e.g., the @('posedge foo') part of a
                sequence expression like @('@(posedge foo) ready ##1
                qvalid').")
      (then    vl-propexpr-p
               "The sequence to match when this clocking event occurs, e.g.,
                the @('ready ##1 qvalid') part of the above sequence.")))

    (:vl-propunary
     :short "A basic unary operator applied to a sequence/property, for
             instance, like @('first_match(a)'), @('not(b)'), etc."
     :base-name vl-propunary
     ((op    vl-property-unaryop-p  "Operator being applied.")
      (arg   vl-propexpr-p          "Argument to the operator.")))

    (:vl-propbinary
     :short "A basic binary operator that joins two sequences/properties, like
             @('a and b'), @('a |-> b'), etc."
     :base-name vl-propbinary
     ((op    vl-property-binaryop-p "Operator that joins these sequences together.")
      (left  vl-propexpr-p          "Left hand side sequence or property operand.")
      (right vl-propexpr-p          "Right hand side sequence or property operand."))
     :long "<p>Note that we use this for @('first_match') sequence operators.
            If you look at the grammar for @('first_match') expressions, there
            is special syntax for embedding match items without nested parens.
            However, that syntax is equivalent to just using the usual @('(foo,
            x++)') style syntax as in a @(see vl-propassign), so in our internal
            representation we only have a sequence expression; the match items,
            if any, will be found within @('arg').</p>")

    (:vl-propalways
     :short "An @('always') or @('s_always') property expression."
     :base-name vl-propalways
     ((strongp booleanp :rule-classes :type-prescription
               "True when this is an @('s_always').")
      (range   vl-maybe-range-p
               "The range applied to this always if applicable.  For instance,
                in @('always [2:3] foo'), the range is @('[2:3]').  A plain
                @('always') may or may not have a range, but an @('s_always')
                should always have one.  We don't enforce this in our data
                structures, but it is enforced by the parser.")
      (prop    vl-propexpr-p
               "The property being tested, e.g., @('foo') in @('always foo').")))

    (:vl-propeventually
     :short "An @('eventually') or @('s_eventually') property expression."
     :base-name vl-propeventually
     ((strongp booleanp :rule-classes :type-prescription
               "True when this is an @('s_eventually').")
      (range   vl-maybe-range-p
               "The range applied to this eventually, if applicable.  For
                instance, in @('eventually [2:3] foo'), the range is @('[2:3]').
                In the grammar, ranges are optional for @('s_eventually') but
                are required for ordinary @('eventually') properties.  We don't
                enforce this in our data structures, but it is enforced by the
                parser.")
      (prop vl-propexpr-p
            "The property being tested, e.g., @('foo') in @('eventually foo').")))

    (:vl-propaccept
     :short "A (possibly synchronous) @('accept_on') or @('reject_on') property
             expression."
     :base-name vl-propaccept
     ((op         vl-property-acceptop-p
                  "The kind of operator, e.g., @('accept_on'), @('reject_on'),
                   etc.")
      (condition  vl-exprdist-p
                  "The abort condition for this operation, e.g., @('foo') in
                   @('accept_on(foo) bar').")
      (prop       vl-propexpr-p
                  "The abort property, e.g., @('bar') in @('accept_on(foo)
                  bar').")))

    (:vl-propnexttime
     :short "A @('nexttime') or @('s_nexttime') property expression."
     :base-name vl-propnexttime
     ((strongp booleanp :rule-classes :type-prescription
               "True for @('s_nexttime') operators, nil for ordinary @('nexttime').")
      (expr    vl-maybe-expr-p
               "For instance, #('3') in case of @('nexttime [3] foo').")
      (prop    vl-propexpr-p
               "The property that must hold next time, e.g., @('foo') in
                @('nexttime [3] foo').")))

    (:vl-propif
     :short "An @('if')-@('else') property expression."
     :base-name vl-propif
     ((condition vl-exprdist-p)
      (then      vl-propexpr-p)
      (else      vl-propexpr-p
                 "In the SystemVerilog grammar the else branch is optional.
                  But an assertion of the form @('if (foo) bar') is equivalent
                  to @('if (foo) bar else 1'), so to keep our internal
                  representation simpler we require that the @('else') branch
                  is present, and if it is missing our parser just fills in
                  an explicit @('1') here.")))

    (:vl-propcase
     :short "A @('case') property expression."
     :base-name vl-propcase
     ((condition vl-exprdist-p)
      (cases     vl-propcaseitemlist-p))))

  (deftagsum vl-propactual
    :measure (two-nats-measure (acl2-count x) 0)
    :short "An actual given as an argument to an instance of a named sequence
            or property.  May be an event expression or a sequence or property
            expression."
    (:blank
     ((name    maybe-stringp :rule-classes :type-prescription
               "An empty property actual; may indicate an explicitly blank
                named argument such as @('.foo()'), or may represent an extra
                commas in the argument list, like @('(foo, , bar)'), in which
                case there will be no name.")))

    (:event
     ((name    maybe-stringp :rule-classes :type-prescription
               "Explicit name for this argument, if provided.  For instance,
                in @('.foo(bar)'), this is the @('foo') part.  Some actuals
                may not have a name..")
      (evatoms vl-evatomlist-p
               "This isn't quite general enough, but event expressions are also
                used in @(see vl-eventcontrol)s, so I'd like this to be
                compatible with that code, reuse its parser, etc.  If we find
                that this isn't good enough, we should extend the eventcontrol
                representation too.")))
    (:prop
     ((name    maybe-stringp :rule-classes :type-prescription
               "Explicit name for this argument, if provided.  For instance,
                in @('.foo(bar)'), this is the @('foo') part.  Some actuals
                may not have a name.")
      (prop    vl-propexpr-p
               "Expression being used as the property or sequence actual
                value."))))

  (fty::deflist vl-propactuallist
    :elt-type vl-propactual
    :measure (two-nats-measure (acl2-count x) 0))

  (defprod vl-propcaseitem
    :short "A single line in a @('case') property expression."
    :measure (two-nats-measure (acl2-count x) 1)
    ((match vl-exprdistlist-p
            "The match expressions before the colon, or @('nil') for the
             default case item.")
     (prop  vl-propexpr-p
            "The property expression for this case.")))

  (fty::deflist vl-propcaseitemlist
    :elt-type vl-propcaseitem
    :measure (two-nats-measure (acl2-count x) 2)))

(defprod vl-propspec
  :parents (property-expressions)
  :short "A single property specification."
  :tag :vl-propspec
  :layout :tree
  ((evatoms vl-evatomlist-p
            "The top-level clocking events for this property specification; this
             can just be @('nil') if there is no clocking event.")
   (disable vl-maybe-exprdist-p
            "Top level disable condition, or @('nil') if this property has no
             @('disable') clause.")
   (prop    vl-propexpr-p
            "Main property expression for this property specification.")
   (loc     vl-location-p)))



(defenum vl-nettypename-p
  (:vl-wire ;; Most common so it goes first.
   :vl-tri
   :vl-supply0
   :vl-supply1
   :vl-triand
   :vl-trior
   :vl-tri0
   :vl-tri1
   :vl-trireg
   :vl-uwire
   :vl-wand
   :vl-wor)
  :short "Representation of wire (net) types, i.e., resolution function."
  :long "<p>Note that Verilog/SystemVerilog <i>net types</i> like @('wire') and
         @('wor') essentially govern how multiple drivers get resolved, and are
         entirely distinct from the normal idea of a <i>data type</i>.  See
         @(see vl-vardecl) for additional discussion.</p>")

(defoption vl-maybe-nettypename vl-nettypename-p)



(defprod vl-interfaceport
  :parents (vl-port)
  :short "Representation of a single interface port."
  :tag :vl-interfaceport
  :layout :tree
  ((name    stringp
            :rule-classes :type-prescription
            "Name (internal and external) of this interface port, e.g.,
             @('foo') for @('simplebus.master foo').")

   (ifname  stringp
            :rule-classes :type-prescription
            "For interface ports like @('simplebus foo') or @('simplebus.master foo'),
             this is the name of the interface, e.g., @('simplebus').  For
             non-interface ports it is just @('nil').")

   (loc     vl-location-p
            "Where this port came from in the Verilog source code.")

   (modport maybe-stringp
            :rule-classes :type-prescription
            "For interface ports with modport components, e.g., @('simplebus.master foo'),
             this is the name of the modport being used, e.g., @('master').
             For plain interfaces like @('simplebus foo') or non-interface
             ports, this is just @('nil').")

   (udims   vl-dimensionlist-p
            "For interface ports only: the unpacked dimensions for this port.")))


(defprod vl-regularport
  :parents (vl-port)
  :short "Representation of a single non-interface port."
  :tag :vl-regularport
  :layout :tree

  ((name maybe-stringp
         :rule-classes :type-prescription
         "The \"externally visible\" name of this port, for use in named module
          instances.  Usually it is best to avoid this; see below.")

   (expr vl-maybe-expr-p
         "How the port is wired internally within the module.  Most of the time,
          this is a simple identifier expression that is just @('name').  But
          it can also be more complex; see below.  The expression should be
          @('nil') for interface ports.")

   (loc  vl-location-p
         "Where this port came from in the Verilog source code."))

  :long "<p>In Verilog-2005, ports are described in Section 12.3 of the
standard.</p>

<p>It is important to understand the difference between ports and port
declarations.  We represent ports as @('vl-port') structures, whereas port
declarations re represented as @(see vl-portdecl) structures.  It is easy to
see the difference between ports and port declarations when modules are
declared using the \"non-ANSI\" syntax.</p>

@({
module mod(a,b,c) ;  <-- ports

  input [3:0] a;     <-- port declarations (not ports)
  input b;
  output c;
endmodule
})

<p>It is less easy to see this difference when the more concise \"ANSI\" syntax
is used:</p>

@({
module mod(
  input [3:0] a;   <-- ports and port declarations, mixed together
  input b;
  output c;
) ;
   ...
endmodule
})

<p>Regardless of which syntax is used, VL internally creates both ports and
portdecls as separate structures.</p>

<p>In most designs, there is a single port corresponding to each port
declaration.  However, in general Verilog permits more complex ports.  Here is
an example of a module where the ports have external names that are distinct
from their internal wiring.</p>

@({
module mod (a, .b(w), c[3:0], .d(c[7:4])) ;
  input a;
  input w;
  input [7:0] c;
  ...
endmodule
})

<p>In this example, the @('name')s of these ports would be, respectively:
@('\"a\"'), @('\"b\"'), @('nil') (because the third port has no externally
visible name), and @('\"d\"').  Meanwhile, the first two ports are internally
wired to @('a') and @('w'), respectively, while the third and fourth ports
collectively specify the bits of @('c').</p>

<p>SystemVerilog-2012 extends ports in several ways, but most of these
extensions (e.g., support for fancy data types) are related to the port
declarations rather than the ports.  One place where the ports themselves
<i>are</i> extended is for interface ports.  See @(see vl-port).</p>")

(deftranssum vl-port
  (vl-regularport
   vl-interfaceport)
  :short "Representation of a single port."
  :long "<p>Most ports are regular ports, see @(see vl-regularport).  However,
SystemVerilog also adds interface ports, see @(see vl-interfaceport).</p>

<p>It is generally best to <b>avoid using port names</b> except perhaps for
things like error messages.  Why?  As shown above, some ports might not have
names, and even when a port does have a name, it does not necessarily
correspond to any wires in the module.  Since these cases are exotic, code that
is based on port names is likely to work for simple test cases, but then fail
later when more complex examples are encountered!</p>

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
performed by examining the width of the port expression.</p>")

(fty::deflist vl-portlist
              :elt-type vl-port-p
              :true-listp nil
              :elementp-of-nil nil)

(fty::deflist vl-interfaceportlist
              :elt-type vl-interfaceport-p
              :true-listp nil
              :elementp-of-nil nil)

(fty::deflist vl-regularportlist
  :elt-type vl-regularport
  :true-listp nil
  :elementp-of-nil nil)



(defthm vl-portlist-p-when-vl-interfaceportlist-p
  (implies (vl-interfaceportlist-p x)
           (vl-portlist-p x))
  :hints(("Goal" :induct (len x))))

(defthm vl-portlist-p-when-vl-regularportlist-p
  (implies (vl-regularportlist-p x)
           (vl-portlist-p x))
  :hints(("Goal" :induct (len x))))

(define vl-port->name ((x vl-port-p))
  :prepwork ((local (in-theory (enable tag-reasoning))))
  :returns (name maybe-stringp :rule-classes :type-prescription)
  (b* ((x (vl-port-fix x)))
    (case (tag x)
      (:vl-regularport   (vl-regularport->name x))
      (:vl-interfaceport (vl-interfaceport->name x))
      (otherwise         (progn$ (impossible) "")))))

(define vl-port->loc ((x vl-port-p))
  :prepwork ((local (in-theory (enable tag-reasoning))))
  :returns (loc vl-location-p)
  (b* ((x (vl-port-fix x)))
    (case (tag x)
      (:vl-regularport   (vl-regularport->loc x))
      (:vl-interfaceport (vl-interfaceport->loc x))
      (otherwise         (progn$ (impossible) *vl-fakeloc*)))))

(defprojection vl-portlist->names ((x vl-portlist-p))
  :parents (vl-portlist-p)
  (vl-port->name x)
  ///
  (defthm string-listp-of-vl-portlist->names
    (equal (string-listp (vl-portlist->names x))
           (not (member nil (vl-portlist->names x)))))

  (defthm string-listp-of-remove-equal-of-vl-portlist->names
    (string-listp (remove-equal nil (vl-portlist->names x)))))

(define vl-collect-interface-ports-exec ((x vl-portlist-p) nrev)
  :parents (vl-collect-interface-ports)
  (b* (((when (atom x))
        (nrev-fix nrev))
       (x1 (vl-port-fix (car x)))
       ((when (eq (tag x1) :vl-interfaceport))
        (b* ((nrev (nrev-push x1 nrev)))
          (vl-collect-interface-ports-exec (cdr x) nrev))))
    (vl-collect-interface-ports-exec (cdr x) nrev)))

(define vl-collect-interface-ports
  :parents (vl-portlist-p)
  :short "Filter a @(see vl-portlist-p) to collect only the interface ports."
  ((x vl-portlist-p))
  :returns (ifports (and (vl-portlist-p ifports)
                         (vl-interfaceportlist-p ifports)))
  :verify-guards nil
  :prepwork ((local (in-theory (enable tag-reasoning))))
  (mbe :logic
       (b* (((when (atom x))
             nil)
            (x1 (vl-port-fix (car x)))
            ((when (eq (tag x1) :vl-interfaceport))
             (cons x1 (vl-collect-interface-ports (cdr x)))))
         (vl-collect-interface-ports (cdr x)))
       :exec
       (if (atom x)
           nil
         (with-local-nrev
           (vl-collect-interface-ports-exec x nrev))))
  ///
  (defthm vl-collect-interface-ports-exec-removal
    (equal (vl-collect-interface-ports-exec x nrev)
           (append nrev (vl-collect-interface-ports x)))
    :hints(("Goal" :in-theory (enable vl-collect-interface-ports-exec))))

  (verify-guards vl-collect-interface-ports)

  (defthm vl-collect-interface-ports-when-atom
    (implies (atom x)
             (equal (vl-collect-interface-ports x)
                    nil)))

  (defthm vl-collect-interface-ports-of-cons
    (equal (vl-collect-interface-ports (cons a x))
           (if (eq (tag (vl-port-fix a)) :vl-interfaceport)
               (cons (vl-port-fix a)
                     (vl-collect-interface-ports x))
             (vl-collect-interface-ports x)))))


(define vl-collect-regular-ports-exec ((x vl-portlist-p) nrev)
  :parents (vl-collect-regular-ports)
  (b* (((when (atom x))
        (nrev-fix nrev))
       (x1 (vl-port-fix (car x)))
       ((when (eq (tag x1) :vl-regularport))
        (b* ((nrev (nrev-push x1 nrev)))
          (vl-collect-regular-ports-exec (cdr x) nrev))))
    (vl-collect-regular-ports-exec (cdr x) nrev)))

(define vl-collect-regular-ports
  :parents (vl-portlist-p)
  :short "Filter a @(see vl-portlist-p) to collect only the regular ports."
  ((x vl-portlist-p))
  :returns (ifports (and (vl-portlist-p ifports)
                         (vl-regularportlist-p ifports)))
  :verify-guards nil
  :prepwork ((local (in-theory (enable tag-reasoning))))
  (mbe :logic
       (b* (((when (atom x))
             nil)
            (x1 (vl-port-fix (car x)))
            ((when (eq (tag x1) :vl-regularport))
             (cons x1 (vl-collect-regular-ports (cdr x)))))
         (vl-collect-regular-ports (cdr x)))
       :exec
       (if (atom x)
           nil
         (with-local-nrev
           (vl-collect-regular-ports-exec x nrev))))
  ///
  (defthm vl-collect-regular-ports-exec-removal
    (equal (vl-collect-regular-ports-exec x nrev)
           (append nrev (vl-collect-regular-ports x)))
    :hints(("Goal" :in-theory (enable vl-collect-regular-ports-exec))))

  (verify-guards vl-collect-regular-ports)

  (defthm vl-collect-regular-ports-when-atom
    (implies (atom x)
             (equal (vl-collect-regular-ports x)
                    nil)))

  (defthm vl-collect-regular-ports-of-cons
    (equal (vl-collect-regular-ports (cons a x))
           (if (eq (tag (vl-port-fix a)) :vl-regularport)
               (cons (vl-port-fix a)
                     (vl-collect-regular-ports x))
             (vl-collect-regular-ports x)))))


(defenum vl-direction-p (:vl-input :vl-output :vl-inout)
  :short "Direction for a port declaration (input, output, or inout)."

  :long "<p>Each port declaration (see @(see vl-portdecl-p)) includes a
direction to indicate that the port is either an input, output, or inout.  We
represent these directions with the keyword @(':vl-input'), @(':vl-output'),
and @(':vl-inout'), respectively.</p>

<p>In our @(see argresolve) transformation, directions are also assigned to all
arguments of gate instances and most arguments of module instances.  See our
@(see vl-plainarg-p) structures for more information.</p>")

(defoption vl-maybe-direction vl-direction-p
  ///
  (defthm type-when-vl-maybe-direction-p
    (implies (vl-direction-p x)
             (and (symbolp x)
                  (not (equal x t))))
    :hints(("Goal" :in-theory (enable vl-maybe-direction-p)))
    :rule-classes :compound-recognizer))

(fty::deflist vl-directionlist
  :elt-type vl-direction-p
  :elementp-of-nil nil
  :parents (vl-direction-p))


(defprod vl-portdecl
  :short "Representation of Verilog port declarations."
  :tag :vl-portdecl
  :layout :tree

  ((name     stringp
             :rule-classes :type-prescription
             "An ordinary string that should agree with some identifier used in
              the \"internal\" wiring expressions from some port(s) in the
              module.")

   (loc      vl-location-p
             "Where the port was declared in the source code.")

   ;; Commonly we have a sequence of ANSI style ports like
   ;;    input logic [3:0] a, b, c, d;
   ;;
   ;; In this case it's likely that we can share dir/type/nettype/atts across
   ;; all of the ports.  So, we put name/loc first and hope that the rest of
   ;; this is usually shared.

   (dir      vl-direction-p
             "Says whether this port is an input, output, or bidirectional
              (inout) port.")

   (type     vl-datatype-p
             "The type and size information for this port.  <b>Warning</b>: per
              Verilog-2005 page 175, port declarations and net/reg declarations
              must be checked against one another: if either declaration
              includes the @('signed') keyword, then both are to be considered
              signed.  The @(see loader) DOES NOT do this cross-referencing
              automatically; instead the @(see portdecl-sign) transformation
              needs to be run.")

   (default  vl-maybe-expr-p
             "Certain kinds of ports (e.g., those in functions and tasks) can
              have default values.")

   (nettype  vl-maybe-nettypename-p)

   (atts     vl-atts-p
             "Any attributes associated with this declaration."))

  :long "<p>See @(see vl-port) for related background.  Port declarations,
described in Section 12.3.3 of the Verilog-2005 standard, ascribe certain
properties (direction, signedness, size, and so on) to the ports of a module.
Here is an example:</p>

@({
module m(a, b) ;
  input [3:0] a ;  // <--- port declaration
  ...
endmodule
})

<p>Although Verilog allows multiple ports to be declared simultaneously, i.e.,
@('input w1, w2;'), our parser splits these merged declarations to create
separate @('vl-portdecl-p') objects for each port.  Because of this, every
@('vl-portdecl-p') has only a single name.</p>

<p>Most of the time, e.g., for @('a') in module @('m') above, the resulting
@(see vl-module) will have:</p>

<ul>
<li>A @(see vl-port) for @('a'),</li>
<li>A corresponding @(see vl-portdecl) that has the direction/type information, and</li>
<li>A corresponding @(see vl-vardecl) that looks like an ordinary variable.</li>
</ul>

<p>The exceptions to this are:</p>

<ul>
<li>Interface ports have no corresponding port/vardecl.</li>
<li>The ports/portdecls do not necessarily line up when complex ports are used,
see @(see vl-port) for details.</li>
</ul>")

(fty::deflist vl-portdecllist
              :elt-type vl-portdecl-p
              :true-listp nil
              :elementp-of-nil nil)


(defprod vl-gatedelay
  :short "Representation of delay expressions."
  :tag :vl-gatedelay
  :layout :tree

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

(defoption vl-maybe-gatedelay vl-gatedelay-p
  ///
  (defthm type-when-vl-maybe-gatedelay-p
    (implies (vl-maybe-gatedelay-p x)
             (or (not x)
                 (consp x)))
    :hints(("Goal" :in-theory (enable vl-maybe-gatedelay-p)))
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

(defprod vl-gatestrength
  :short "Representation of strengths for a assignment statements, gate
instances, and module instances."
  :tag :vl-gatestrength
  :layout :tree

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

(defoption vl-maybe-gatestrength vl-gatestrength-p
  ///
  (defthm type-when-vl-maybe-gatestrength-p
    (implies (vl-maybe-gatestrength-p x)
             (or (not x)
                 (consp x)))
    :hints(("Goal" :in-theory (enable vl-maybe-gatestrength-p)))
    :rule-classes :compound-recognizer))


(defenum vl-cstrength-p (:vl-large :vl-medium :vl-small)
  :short "Representation of charge strengths."

  :long "<p>We represent Verilog's charge strengths with the keyword symbols
recognized by @(call vl-cstrength-p).</p>

<p>BOZO add references to the Verilog-2005 standard, description of what these
are.</p>")

(defoption vl-maybe-cstrength vl-cstrength-p
  ///
  (defthm type-when-vl-maybe-cstrength-p
    (implies (vl-maybe-cstrength-p x)
             (and (symbolp x)
                  (not (equal x t))))
    :hints(("Goal" :in-theory (enable vl-maybe-cstrength-p)))
    :rule-classes :compound-recognizer))


(defprod vl-assign
  :short "Representation of a continuous assignment statement."
  :tag :vl-assign
  :layout :tree

  ((lvalue   vl-expr-p "The location being assigned to.")
   (expr     vl-expr-p "The right-hand side.")
   (loc      vl-location-p
             "Where the assignment was found in the source code.")
   (atts     vl-atts-p
             "Any attributes associated with this assignment.")
   (strength vl-maybe-gatestrength-p)
   (delay    vl-maybe-gatedelay-p))

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
see @(see vl-vardecl) for additional discussion.</p>

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

(fty::deflist vl-assignlist
              :elt-type vl-assign-p
              :true-listp nil
              :elementp-of-nil nil)

(defprojection vl-assignlist->lvalues ((x vl-assignlist-p))
  :returns (lvalues vl-exprlist-p)
  :parents (vl-assignlist-p)
  (vl-assign->lvalue x))



; BOZO I'm not going to introduce this yet.  I think we should rename the expr
; field to rhs first, to prevent confusion between this and allexprs.

;; (defprojection vl-assignlist->exprs (x)
;;   (vl-assign->expr x)
;;   :guard (vl-assignlist-p x)
;;   :nil-preservingp t)


(defprod vl-alias
  :short "Representation of an alias declaration."
  :tag :vl-alias
  :layout :tree

  ((lhs     vl-expr-p "The left-hand side.")
   (rhs     vl-expr-p "The right-hand side.")
   (atts     vl-atts-p
             "Any attributes associated with this alias.")
   (loc      vl-location-p
             "Where the assignment was found in the source code.")))

(fty::deflist vl-aliaslist
  :elt-type vl-alias-p
  :true-listp nil
  :elementp-of-nil nil)

(defenum vl-lifetime-p
  (nil
   :vl-static
   :vl-automatic)
  :short "Representation of the lifetime of a variable, function, task, etc.")

(defprod vl-vardecl
  :short "Representation of a single variable or net (e.g., wire) declaration."
  :tag :vl-vardecl
  :layout :tree

  ((name     stringp
             :rule-classes :type-prescription
             "Name of the variable being declared.")

   (loc      vl-location-p
             "Where the declaration was found in the source code.")

   (type     vl-datatype-p
             "Data type, array dimensions.  See below.")

   (nettype  vl-maybe-nettypename-p
             "Net type (i.e., resolution function, distinct from datatype) or
              @('nil') if this a @('reg') or variable instead of a net.  See
              below.")

   (atts     vl-atts-p
             "Any attributes associated with this declaration.")

   (initval  vl-maybe-rhs-p
             "(Variables only).  When present, indicates the initial value for
              the variable, e.g., for @('integer i = 3;') the @('initval') will
              be the @(see vl-expr-p) for @('3').  Note that when net
              declarations have initial values, the parser turns them into
              separate continuous assignment statements, instead.")

   (constp   booleanp
             :rule-classes :type-prescription
             "(Variables only).  Indicates whether the @('const') keyword was
              provided.")

   (constval sv::maybe-4vec-p
             "If the @('const') keyword was given, we try and resolve the ~
              @('initval') to a constant.  If successful, we store that value ~
              here.")

   (varp     booleanp
             :rule-classes :type-prescription
             "(Variables only).  Indicates whether the @('var') keyword was
              provided.")

   (lifetime vl-lifetime-p
             "(Variables only).  See SystemVerilog-2012 Section 6.21.  There
              are pretty complex rules for variable lifetimes.  BOZO we don't
              really support this yet in any meaningful way, and the
              @('lifetime') field is currently just used to record whether a
              @('static') or @('automatic') keyword was found during parsing.")

   (vectoredp  booleanp
               :rule-classes :type-prescription
               "(Nets only) True if the @('vectored') keyword was explicitly
                provided.  See SystemVerilog-2012 section 6.9.2.  This flag is
                rather obscure and appears to have something to do with whether
                the net will be ``expanded'' for the purposes of the Verilog
                Programming Language Interface (PLI).  Vectored nets should
                apparently not be bit- or part-selected from and should not
                have strengths.  This does not seem particularly relevant to
                anything and VL generally ignores this flag.")

   (scalaredp  booleanp
               :rule-classes :type-prescription
               "(Nets only) True if the @('scalared') keyword was explicitly
                provided.  See SystemVerilog-2012 section 6.9.2.  Again this is
                not well specified and probably irrelevant.  VL generally
                ignores this.")

   (delay      vl-maybe-gatedelay-p
               ;; BOZO consider making this an explicit vl-gatedelay-p and
               ;; having the parser zero it when it's not specified.
               "(Nets only) The delay associated with this wire, if any.
                For instance, @('wire #1 foo') has a delay of 1, and means that
                it takes 1 time unit for the net to change its value in
                response to a change on any driver (Verilog-2005, 7.14).  The
                default delay is zero when no delay is specified, but we
                represent the delay using a @(see vl-maybe-gatedelay-p), and
                use @('NIL') when no delay is specified.  Note per
                Verilog-2005, Section 6.1.3, that when a delays is provided in
                the combined declaration and assignment statement like @('wire
                #10 a = 1, b = 2'), then the delay is associated with each
                assignment and <b>not</b> with the net declaration for @('a');
                see @(see vl-assign-p) for more information.")

   (cstrength  vl-maybe-cstrength-p
               "(Trireg nets only).  The charge strength associated with the
                net, if any.  For instance, @('trireg medium foo') will have a
                @('cstrength') of @('medium'); the @('cstrength') will be
                @('nil') for all non-trireg nets, regs, and variables; it will
                also be @('nil') for @('trireg') nets that do not explicitly
                give a charge strength."))

  :long "<p>Verilog-2005 and SystemVerilog-2012 distinguish between nets and
         variables.  For example:</p>

         @({
              wire signed [4:0] w;     // net
              supply1 vdd;             // net
              wand [3:0] a;            // net

              reg [4:0] r;             // variable
              logic signed [1:0] l;    // variable
              integer i;               // variable
              mybus_t b;               // variable
         })

         <p>In early versions of VL, we also separated nets from variables in
         our internal representation of Verilog @(see syntax).  However, we
         eventually decided that merging together these concepts into a single
         representation would be simpler.  Today, we use the same
         @('vl-vardecl') structures to represent:</p>

         <ul>
         <li>@('net') declarations,</li>
         <li>@('reg') declarations, and</li>
         <li>all other variable declarations (e.g., @('logic'),
         @('mystruct_t'), etc.)</li>
         </ul>

         <p>Any of these declarations introduces a named entity that has
         certain properties.  Some of these properties, like its dimension(s)
         and whether it is regarded as signed, are captured by the notion of a
         SystemVerilog <b>variable type</b> or <b>data type</b>.  We represent
         this information as an ordinary @(see vl-datatype), found in the
         @('type') field of the @('vl-vardecl').</p>

         <p>The main difference between nets and datatypes is that nets can be
         used with multiple drivers.  To support resolving multiple drivers in
         different ways, net declarations can include a <b>net type</b> such as
         @('wire') for plain wires, @('wor') for a wired or, @('supply0') for a
         <i>ground</i> wire, and similar.  Despite its name, the ``net type''
         has nothing to do with the ordinary notion of a data type!  (This
         terminology, unfortunately, comes from the Verilog/SystemVerilog
         standards; see for instance SystemVerilog-2012 section 6.5).</p>

         <p>Here are some examples of basic net declarations.</p>

         @({
             module m (a, b, c) ;
               wire [4:0] w ;       // <-- plain net declaration
               wire ab = a & b ;    // <-- net declaration with assignment
               ...
             endmodule
         })

         <p>Net declarations can also arise from using the combined form of
         port declarations.</p>

         @({
             module m (a, b, c) ;
               input wire a;    // <-- net declaration in a port declaration
               ...
             endmodule
         })

         <p>They can also arise from the more modern ANSI style ports, e.g.,</p>

         @({
             module m (input wire a, ...) ;
         })

         <p>You can also string together net declarations, e.g., by writing
         @('wire w1, w2;').  In all of these cases, our @(see parser) generates
         a separate @('vl-vardecl-p') object for each declared wire.  When an
         assignment is also present, the parser creates a corresponding,
         separate @(see vl-assign-p) object to contain the assignment.  Hence,
         each @('vl-vardecl-p') really and truly only represents a single
         declaration.  Similarly, combined variable declarations such as
         \"integer a, b\" are split apart into multiple, individual
         declarations.</p>")

(fty::deflist vl-vardecllist
              :elt-type vl-vardecl-p
              :true-listp nil
              :elementp-of-nil nil)



(defprod vl-plainarg
  :parents (vl-arguments-p)
  :short "Representation of a single argument in a plain argument list."
  :layout :tree
  ;; No tag, because we found tags on plainargs to be expensive.

  ((expr     vl-maybe-expr-p
             "Expression being connected to the port.  In programming languages
              parlance, this is the <i>actual</i>.  Note that this may be
              @('nil') because Verilog allows expressions to be \"blank\", in
              which case they represent an unconnected wire.")

   (portname maybe-stringp
             :rule-classes
             ((:type-prescription)
              (:rewrite
               :corollary (equal (stringp (vl-plainarg->portname x))
                                 (if (vl-plainarg->portname x)
                                     t
                                   nil))))
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

(fty::deflist vl-plainarglist
  :parents (vl-arguments-p)
  :elt-type vl-plainarg-p
  :true-listp nil)

(fty::deflist vl-plainarglistlist
  :parents (vl-arguments-p)
  :elt-type vl-plainarglist-p
  :true-listp nil
  :elementp-of-nil t
  ///
  (defthm vl-plainarglist-p-of-strip-cars
    (implies (and (vl-plainarglistlist-p x)
                  (all-have-len x n)
                  (not (zp n)))
             (vl-plainarglist-p (strip-cars x)))
    :hints(("Goal" :in-theory (enable strip-cars))))

  (defthm vl-plainarglistlist-p-of-strip-cdrs
    (implies (vl-plainarglistlist-p x)
             (vl-plainarglistlist-p (strip-cdrs x)))
    :hints(("Goal" :in-theory (enable strip-cdrs)))))

(defprojection vl-plainarglist->exprs ((x vl-plainarglist-p))
  (vl-plainarg->expr x)
  ///
  (defthm vl-exprlist-p-of-vl-plainarglist->exprs
    (equal (vl-exprlist-p (vl-plainarglist->exprs x))
           (not (member nil (vl-plainarglist->exprs x)))))

  (defthm vl-exprlist-p-of-remove-nil-of-plainarglist->exprs
    (vl-exprlist-p (remove nil (vl-plainarglist->exprs x)))))


(defprod vl-namedarg
  :short "Representation of a single argument in a named argument list."
  ;; No tag, because we found tags on namedargs to be expensive.

  ((name stringp
         :rule-classes :type-prescription
         "Name of the port being connected to, e.g., @('foo') in
          @('.foo(3)')")

   (expr vl-maybe-expr-p
         "The <i>actual</i> being connected to this port; may be
          @('nil') for blank ports.")

   (nameonly-p booleanp
               "Indicates that this argument is an implicit named port
                connection, i.e., of the form @('.name').  SystemVerilog allows
                ports connections such as @('.foo, .bar, .baz').  This syntax
                is equivalent to @('.foo(foo), .bar(bar), .baz(baz)'), except
                that the names of these wires are required to exist in the
                instantiating module, i.e., no implicit nets are to be created.
                Note: the @('expr') for such a port should just be a simple
                idexpr.")

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

(fty::deflist vl-namedarglist
              :elt-type vl-namedarg-p
              :true-listp nil
              :elementp-of-nil nil)

(deftagsum vl-arguments
  :short "Representation of arguments to a module instance (for ports, not
parameters)."

  :long "<p>There are two kinds of argument lists for the ports of module
instantiations, which we call <i>plain</i> and <i>named</i> arguments.</p>

@({
  modname instname ( 1, 2, 3 );             <-- \"plain\" arguments
  modname instname ( .a(1), .b(2), .c(3) ); <-- \"named\" arguments
})

<p>A @('vl-arguments-p') structure represents an argument list of either
variety.</p>"

  (:vl-arguments-plain
   :base-name vl-arguments-plain
   ((args vl-plainarglist-p
          "The actuals to the instance in order, e.g., @('1, 2, 3').")))

  (:vl-arguments-named
   :base-name vl-arguments-named
   ((args vl-namedarglist-p
          "The actuals to the instance and their names, e.g., @('.a(1), .b(2), .c(3)').")
    (starp booleanp
           "Indicates whether the @('.*') token was present."))))

(define vl-arguments->args ((x vl-arguments-p))
  :inline t
  :enabled t
  (vl-arguments-case x
    :vl-arguments-named x.args
    :vl-arguments-plain x.args))





(define vl-paramargs-empty-p ((x vl-paramargs-p))
  :parents (vl-paramargs)
  (vl-paramargs-case x
    :vl-paramargs-named (atom x.args)
    :vl-paramargs-plain (atom x.args)))


(defprod vl-modinst
  :short "Representation of a single module instance, user-defined primitive
instance, or a direct interface instance (not an interface port)."
  :tag :vl-modinst
  :layout :tree

  ((instname  maybe-stringp
              :rule-classes :type-prescription
              "Either the name of this instance or @('nil') if the instance has
               no name.  See also the @(see addnames) transform.")

   (modname   stringp
              :rule-classes :type-prescription
              "Name of the module, user-defined primitive, or interface that is
               being instantiated.")

   (portargs  vl-arguments-p
              "Connections to use for the submodule's input, output, and inout
               ports.")

   (paramargs vl-paramargs-p
              "Values to use for module parameters.  For instance, this might
               specify the width to use for an adder module, etc.")

   (loc       vl-location-p
              "Where the instance was found in the source code.")

   (range     vl-maybe-range-p
              "When present, indicates that this is an array of instances,
               instead of a single instance.")

   (atts      vl-atts-p
              "Any attributes associated with this instance.")

   (str       vl-maybe-gatestrength-p
              "Strength for user-defined primitive instances.  Does not make
               sense for module instances.  VL mostly ignores this.")

   (delay     vl-maybe-gatedelay-p
              "Delay for user-defined primitive instances.  Does not make sense
               for module instances.  VL mostly ignores this."))

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

(fty::deflist vl-modinstlist
              :elt-type vl-modinst-p
              :true-listp nil
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

(defprod vl-gateinst
  :short "Representation of a single gate instantiation."
  :tag :vl-gateinst
  :layout :tree
  ((type     vl-gatetype-p
             "What kind of gate this is, e.g., @('and'), @('xor'), @('rnmos'),
              etc."
             :rule-classes
             ((:rewrite)
              (:type-prescription
               :corollary
               (and (symbolp (vl-gateinst->type x))
                    (not (equal (vl-gateinst->type x) t))
                    (not (equal (vl-gateinst->type x) nil))))))

   (args     vl-plainarglist-p
             "Arguments to the gate instance.  Note that this differs from
              module instances where @(see vl-arguments-p) structures are used,
              because gate arguments are never named.  The grammar restricts
              how many arguments certain gates can have, but we do not enforce
              these restrictions in the definition of @('vl-gateinst-p').")

   (loc      vl-location-p
             "Where the gate instance was found in the source code.")

   (name     maybe-stringp
             :rule-classes
             ((:type-prescription)
              (:rewrite :corollary
               (equal (stringp (vl-gateinst->name x))
                      (if (vl-gateinst->name x)
                          t
                        nil))))
             "The name of this gate instance, or @('nil') if it has no name;
              see also the @(see addnames) transform.")

   (atts     vl-atts-p
             "Any attributes associated with this gate instance.")

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
              correctly."))

  :long "<p>@('vl-gateinst-p') is our representation for any single gate
instance (or instance array).</p>

<p>The grammar for gate instantiations is quite elaborate, but the various
cases are so regular that a unified representation is possible.  Note that the
Verilog grammar restricts the list of expressions in certain cases, e.g., for
an @('and') gate, the first expression must be an lvalue.  Although our parser
enforces these restrictions, we do not encode them into the definition of
@('vl-gateinst-p').</p>")

(fty::deflist vl-gateinstlist
              :elt-type vl-gateinst-p
              :true-listp nil
              :elementp-of-nil nil)




(deftagsum vl-paramtype
  :parents (vl-paramdecl)
  :short "Representation of the kind and default for a parameter declaration."

  :long "<p>Both Verilog-2005 and SystemVerilog-2012 allow parameters to be
declared without any explicit type information, e.g., one can write:</p>

@({
    parameter size = 5;          <-- no explicit type, signedness, or range
    parameter signed foo = -1;   <-- explicitly signed, no explicit range
    parameter [3:0] bar = 2;     <-- explicitly 4 bits, no explicit signedness
})

<p>The ultimate, post-elaboration type and range of these parameters are
described in Verilog-2005 Section 12.2 and in SystemVerilog-2012 sections
6.20.2 and 23.10.  These rules are exotic.  When no explicit type/range is
given, the final type/range is taken from whatever value is ultimately assigned
to the parameter.  In other cases, i.e., there is only a signedness but no
explicit range, or vice versa, then some aspects of the final type/range are
determined by the value assigned to the parameter, and other aspects are
governed by the parameter declaration itself.</p>

<p>A consequence of these weird rules is that we cannot simply assign some
default type to plain parameter declarations.  Instead, we need to know that
the parameter doesn't have parts of its type specified.  To accommodate this,
we use @(see vl-implicitvalueparam) structures when the type of a parameter is
implicitly specified, or @(see vl-explicitvalueparam) structures for parameters
with explicitly specified types.</p>

<p>All of the above parameters are <b>value parameters</b>.  In Verilog-2005,
all parameters are value parameters.  However, in SystemVerilog-2012, it is
also possible to have type parameters (See Section 6.20.3), e.g.,</p>

@({
    parameter type bus_t = logic [31:0];
})

<p>Type parameters are quite different from value parameters.  We represent
their types as @(see vl-typeparam)s.</p>"

  (:vl-implicitvalueparam
   :layout :tree
   :base-name vl-implicitvalueparam
   :short "Representation for implicitly specified value parameter types."
   ((range   vl-maybe-range-p    "The range for this parameter, if provided.")
    (sign    vl-maybe-exprsign-p "The signedness for this parameter, if provided.")
    (default vl-maybe-expr-p     "The default value for this parameter, if provided."))
   :long "<p>Note that there are no unpacked dimensions here, even though it is
   legal to write things like @('parameter [3:0] foo [4:0]'), because we have
   not seen a case where the above sort of parameter declaration differs from a
   fully explicitly typed parameter such as @('parameter logic [3:0] foo
   [4:0]').  It's not entirely clear that this is the right behavior, but at
   present the parser will create @(see vl-explicitvalueparam)s for any
   parameters that have unpacked dimensions, as if they had been specified
   with a @('logic') type.</p>")

  (:vl-explicitvalueparam
   :layout :tree
   :base-name vl-explicitvalueparam
   :short "Representation for explicitly specified value parameter types."
   ((type    vl-datatype          "Type of this parameter.")
    (default vl-maybe-expr-p      "The default value for this parameter, if provided.")
    (final-value sv::maybe-4vec-p "The final, resolved value for this parameter, if available" )))

  (:vl-typeparam
   :layout :tree
   :short "Representation for type parameter types."
   :base-name vl-typeparam
   ((default vl-maybe-datatype-p "The default type for this parameter, if provided."))))


(defprod vl-paramdecl
  :short "Representation of a single @('parameter') or @('localparam')
declaration."
  :tag :vl-paramdecl
  :layout :tree

  ((name   stringp
           :rule-classes :type-prescription
           "Name of the parameter being declared.")

   (type   vl-paramtype-p
           "Indicates the type and default value of the parameter, and also
            distinguishes between implicit/explicit value parameters and type
            parameters.")

   (loc    vl-location-p
           "Where the declaration was found in the source code.")

   (localp booleanp
           :rule-classes :type-prescription
           "True for @('localparam') declarations, @('nil') for @('parameter')
            declarations.  The difference is apparently that @('localparam')s
            such as @('TWICE_WIDTH') below cannot be overridden from outside
            the module, except insofar as that they depend upon non-local
            parameters.  (These @('localparam') declarations are a way to
            introduce named constants without polluting the @('`define')
            namespace.)")

   (overriddenp booleanp
                :rule-classes :type-prescription
                "For non-local module parameters, this may get set to T during
                 unparameterization, signifying that the parameter was overridden
                 in a module instantiation.  The \"default\" values recorded in
                 the paramtype are then actually the overridden values.  We sometimes
                 need to know whether it was overridden or not to know which scope
                 (that of the instance or of the instantiated module) names are
                 relative to.")

   (atts   vl-atts-p
           "Any attributes associated with this declaration."))

  :long "<p>Some examples of parameter declarations include:</p>

@({
module mymod (a, b, ...) ;
  parameter WIDTH = 3;
  localparam TWICE_WIDTH = 2 * WIDTH;
  ...
endmodule
})")

(fty::deflist vl-paramdecllist
              :elt-type vl-paramdecl-p
              :true-listp nil
              :elementp-of-nil nil)

(fty::deflist vl-paramdecllist-list
              :elt-type vl-paramdecllist-p
              :true-listp nil
              :elementp-of-nil t)



(define vl-importpart-p (x)
  (or (eq x :vl-import*)
      (stringp x))
  ///
  (defthm vl-importpart-p-when-stringp
    (implies (stringp x)
             (vl-importpart-p x)))

  (defthm vl-importpart-p-compound-recognizer
    (implies (vl-importpart-p x)
             (or (and (symbolp x)
                      (not (equal x nil))
                      (not (equal x t)))
                 (stringp x)))
    :rule-classes :compound-recognizer))

(define vl-importpart-fix ((x vl-importpart-p))
  :returns (part vl-importpart-p)
  (if (vl-importpart-p x)
      x
    :vl-import*)
  ///
  (defthm vl-importpart-fix-when-vl-importpart-p
    (implies (vl-importpart-p x)
             (equal (vl-importpart-fix x)
                    x))))

(fty::deffixtype vl-importpart
  :pred vl-importpart-p
  :fix vl-importpart-fix
  :equiv vl-importpart-equiv
  :define t
  :forward t)


(defprod vl-import
  :tag :vl-import
  :layout :tree
  :short "Representation of a single import item, i.e., @('import foo::bar;')."

  ((pkg  stringp :rule-classes :type-prescription
         "Package to import everything from, e.g., @('\"foo\"').")

   (part vl-importpart-p
         "Either: a single name to import, e.g., @('\"bar\"') above, or else
          the symbol @(':vl-import*'), which means import everything, as in
          @('import foo::*;').")

   (loc  vl-location-p)
   (atts vl-atts-p)))

(fty::deflist vl-importlist
  :elt-type vl-import-p
  :elementp-of-nil nil)



(defprod vl-typedef
  :tag :vl-typedef
  :short "Representation of a basic type declaration like @('typedef struct ... foo_t;')."
  ((name     stringp
             "Name of the type being defined, e.g., @('foo_t').")
   (type     vl-datatype-p
             "Type this name is being defined as, e.g., @('struct { ... }').")
   (minloc   vl-location-p)
   (maxloc   vl-location-p)
   (atts     vl-atts-p)
   (warnings vl-warninglist-p)
   (comments vl-commentmap-p)))

(defmacro vl-typedef->loc (x)
  `(vl-typedef->minloc ,x))

(fty::deflist vl-typedeflist
  :elt-type vl-typedef-p
  :elementp-of-nil nil)

(defprojection vl-typedeflist->names ((x vl-typedeflist-p))
  :parents (vl-typedeflist-p)
  :returns (names string-listp)
  (vl-typedef->name x))



(deftranssum vl-blockitem
  :short "Recognizer for a valid block item."
  :long "<p>@('vl-blockitem-p') is a sum-of-products style type for recognizing
valid block items.  These can occur within @('begin/end') and @('fork/join')
block statements, function declarations, and task declarations.</p>"
  (vl-vardecl
   vl-paramdecl
   vl-import
   vl-typedef))

;; This is automatic now, see TAG-OF-VL-BLOCKITEM-FIX-FORWARD
;; (defthmd vl-blockitem-fix-possible-tags
;;   (or (equal (tag (vl-blockitem-fix x)) :vl-vardecl)
;;       (equal (tag (vl-blockitem-fix x)) :vl-paramdecl)
;;       (equal (tag (vl-blockitem-fix x)) :vl-import)
;;       (equal (tag (vl-blockitem-fix x)) :vl-typedef))
;;   :rule-classes ((:forward-chaining :trigger-terms ((tag (vl-blockitem-fix x)))))
;;   :hints (("goal"
;;            :in-theory (enable tag-reasoning)
;;            :cases ((vl-blockitem-p (vl-blockitem-fix x))))))
;;
;; (add-to-ruleset tag-reasoning '(vl-blockitem-fix-possible-tags))

;; I don't think this should be necessary; it's part of the type prescription.
;; (defthm vl-blockitem-fix-type
;;   (consp (vl-blockitem-fix x))
;;   :rule-classes :type-prescription
;;   :hints(("Goal" :expand ((:with vl-blockitem-fix (vl-blockitem-fix x))))))

(fty::deflist vl-blockitemlist
  :elt-type vl-blockitem-p
  :true-listp nil
  :elementp-of-nil nil
  ///
  (defthm vl-blockitemlist-p-when-vl-vardecllist-p
    (implies (vl-vardecllist-p x)
             (vl-blockitemlist-p x))
    :hints(("Goal" :induct (len x))))

  (defthm vl-blockitemlist-p-when-vl-paramdecllist-p
    (implies (vl-paramdecllist-p x)
             (vl-blockitemlist-p x))
    :hints(("Goal" :induct (len x))))

  (defthm vl-blockitemlist-p-when-vl-importlist-p
    (implies (vl-importlist-p x)
             (vl-blockitemlist-p x))
    :hints(("Goal" :induct (len x))))

  (defthm vl-blockitemlist-p-when-vl-typedeflist-p
    (implies (vl-typedeflist-p x)
             (vl-blockitemlist-p x))
    :hints(("Goal" :induct (len x)))))


(define vl-sort-blockitems-aux ((x vl-blockitemlist-p)
                                ;; accumulators
                                (vardecls-acc   vl-vardecllist-p)
                                (paramdecls-acc vl-paramdecllist-p)
                                (imports-acc    vl-importlist-p)
                                (typedefs-acc   vl-typedeflist-p))
  :prepwork ((local (in-theory (enable tag-reasoning))))
  :returns (mv (vardecls   vl-vardecllist-p)
               (paramdecls vl-paramdecllist-p)
               (imports    vl-importlist-p)
               (typedefs   vl-typedeflist-p))
  (b* (((when (atom x))
        (mv (rev (vl-vardecllist-fix   vardecls-acc))
            (rev (vl-paramdecllist-fix paramdecls-acc))
            (rev (vl-importlist-fix    imports-acc))
            (rev (vl-typedeflist-fix   typedefs-acc))))
       (x1 (vl-blockitem-fix (car x)))
       ((mv vardecls-acc paramdecls-acc imports-acc typedefs-acc)
        (case (tag x1)
          (:vl-vardecl   (mv (cons x1 vardecls-acc) paramdecls-acc imports-acc typedefs-acc))
          (:vl-paramdecl (mv vardecls-acc (cons x1 paramdecls-acc) imports-acc typedefs-acc))
          (:vl-import    (mv vardecls-acc paramdecls-acc (cons x1 imports-acc) typedefs-acc))
          (otherwise     (mv vardecls-acc paramdecls-acc imports-acc (cons x1 typedefs-acc))))))
    (vl-sort-blockitems-aux (cdr x) vardecls-acc paramdecls-acc imports-acc typedefs-acc)))

(define vl-sort-blockitems ((x vl-blockitemlist-p))
  :returns (mv (vardecls   vl-vardecllist-p)
               (paramdecls vl-paramdecllist-p)
               (imports    vl-importlist-p)
               (typedefs   vl-typedeflist-p))
  (vl-sort-blockitems-aux x nil nil nil nil))


(defenum vl-assign-type-p
  (:vl-blocking
   :vl-nonblocking
   :vl-assign
   :vl-force)
  :parents (vl-assignstmt)
  :short "Type of an assignment statement."
  :long "<p>@(':vl-blocking') and @(':vl-nonblocking') are for
blocking/nonblocking procedural assignments, e.g., @('foo = bar') and @('foo <=
bar'), respectively.</p>

<p>@(':vl-assign') and @(':vl-force') are for procedural continuous
assignments, e.g., @('assign foo = bar') or @('force foo = bar'),
respectively.</p>")

(defenum vl-deassign-type-p
  (:vl-deassign :vl-release)
  :parents (vl-deassignstmt)
  :short "Type of an deassignment statement.")

(defenum vl-casetype-p
  (nil
   :vl-casex
   :vl-casez)
  :parents (vl-casestmt)
  :short "Recognizes the possible kinds of case statements."
  :long "<ul>

<li>@('nil') for ordinary @('case') statements,</li>
<li>@(':vl-casex') for @('casex') statements, and</li>
<li>@(':vl-casez') for @('casez') statements.</li>

</ul>")

(defenum vl-casecheck-p
  (nil
   :vl-unique
   :vl-unique0
   :vl-priority)
  :parents (vl-casestmt)
  :short "Case statement violation checking mode."
  :long "<p>For ordinary @('case') statements this will be @('nil').  The other
values are for SystemVerilog's @('unique'), @('unique0'), and @('priority')
case statements.</p>")

(defenum vl-asserttype-p
  (:vl-assert
   :vl-assume
   :vl-cover
   :vl-expect
   :vl-restrict)
  :parents (vl-assertstmt)
  :short "Type of assertion, e.g., @('assert'), @('assume'), @('cover'), etc.")

(defenum vl-assertdeferral-p
  (nil
   :vl-defer-0
   :vl-defer-final)
  :parents (vl-assertstmt)
  :short "Indicates whether this assertion is deferred."
  :long "<ul>
         <li>@('nil') &mdash; this is not a deferred assertion.</li>
         <li>@(':vl-defer-0') &mdash; this is a @('#0') deferred assertion.</li>
         <li>@(':vl-defer-final') &mdash; this is a @('final') deferred assertion.</li>
         </ul>")

(defenum vl-blocktype-p
  (:vl-beginend
   :vl-forkjoin
   :vl-forkjoinany
   :vl-forkjoinnone)
  :parents (vl-blockstmt)
  :short "Indicates whether this is a @('begin/end'), @('fork/join'),
          @('fork/join_any'), or @('fork/join_none') statement.")

(defenum vl-casekey-p
  (:inside
   :matches
   nil))

(deftypes statements
  :short "Representation of a statement."

  :long "<p>Verilog includes a number of statements for behavioral modelling.
Some of these (assignments, event triggers, enables and disables) are
<b>atomic</b> in that they do not contain any sub-statements.  We call the
other statements (loops, cases, if statements, etc.) <b>compound</b> since they
contain sub-statements and are mutually-recursive with @('vl-stmt-p').</p>"

  :prepwork
  ((local (in-theory (disable VL-EXPR-P-OF-CAR-WHEN-VL-EXPRLIST-P
                              VL-MAYBE-EXPR-P-OF-CDAR-WHEN-VL-ATTS-P
                              VL-ATTS-P-OF-CDR-WHEN-VL-ATTS-P
                              ACL2::CONSP-OF-CAR-WHEN-ALISTP
                              acl2::car-when-all-equalp
                              ;; VL-EXPRLIST-P-OF-CAR-WHEN-VL-EXPRLISTLIST-P
                              VL-EXPRLIST-P-OF-CDR-WHEN-VL-EXPRLIST-P
                              VL-EXPR-P-WHEN-VL-MAYBE-EXPR-P
                              ;; VL-EXPRLISTLIST-P-OF-CDR-WHEN-VL-EXPRLISTLIST-P
                              ))))

  (fty::deflist vl-stmtlist
    :measure (two-nats-measure (acl2-count x) 2)
    :elt-type vl-stmt-p
    :true-listp t
    :elementp-of-nil nil)

  (fty::defalist vl-caselist
    :measure (two-nats-measure (acl2-count x) 2)
    :key-type vl-exprlist ;; The match expressions in a case item
    :val-type vl-stmt     ;; The associated statement
    :true-listp t)

  (deftagsum vl-stmt
    :measure (two-nats-measure (acl2-count x) 0)
    (:vl-nullstmt
     :short "Representation of an empty statement."
     :base-name vl-nullstmt
     :layout :tree
     ((atts vl-atts-p
            "Any <tt>(* foo, bar = 1*)</tt> style attributes associated with
             this statement."))
     :long "<p>We allow explicit null statements.  This allows us to
            canonicalize @('if') expressions so that any missing branches are
            turned into null statements.</p>")

    (:vl-assignstmt
     :layout :tree
     :base-name vl-assignstmt
     :short "Representation of an assignment statement."
     ((type   vl-assign-type-p
              "Kind of assignment statement, e.g., blocking, nonblocking, etc.")
      (lvalue vl-expr-p
              "Location being assigned to.  Note that the Verilog-2005 standard
               places various restrictions on lvalues, e.g., for a procedural
               assignment the lvalue may contain only plain variables, and
               bit-selects, part-selects, memory words, and nested
               concatenations of these things.  We do not enforce these
               restrictions in @('vl-assignstmt-p'), but only require that the
               lvalue is an expression.")
      (rhs    vl-rhs-p
              "The right-hand side expression that should be assigned to the
               lvalue.")
      (loc    vl-location-p
              "Where the statement was found in the source code.")
      (ctrl   vl-maybe-delayoreventcontrol-p
              "Control that affects when the assignment is done, if any.  These
               controls can be a delay like @('#(6)') or an event control like
               @('@(posedge clk)').  The rules for this are covered in Section
               9.2 and appear to perhaps be different depending upon the type
               of assignment.  Further coverage seems to be available in
               Section 9.7.7.")
      (atts   vl-atts-p
              "Any <tt>(* foo, bar = 1*)</tt> style attributes associated with this statement."))

     :long "<p>Assignment statements are covered in Section 9.2.  There are two
            major types of assignment statements.</p>

            <h4>Procedural Assignments</h4>

            <p>Procedural assignment statements may only be used to assign to
            @('reg'), @('integer'), @('time'), @('realtime'), and memory data
            types, and cannot be used to assign to ordinary nets such as
            @('wire')s.  There are two kinds of procedural assignments: </p>

            @({
               foo = bar ;     // \"blocking\" -- do the assignment now
               foo <= bar ;    // \"nonblocking\" -- schedule the assignment to occur
            })

            <p>The difference between these two statements has to do with
            Verilog's timing model and simulation semantics.  In particular, a
            blocking assignment \"executes before the statements that follow
            it,\" whereas a non-blocking assignment only \"schedules\" an
            assignment to occur and can be thought of as executing in parallel
            with what follows it.</p>

            <h4>Continuous Procedural Assignments</h4>

            <p>Continuous procedural assignment statements may apparently be
            used to assign to either nets or variables.  There are two
            kinds:</p>

            @({
              assign foo = bar ;  // only for variables
              force foo = bar ;   // for variables or nets
            })

            <p>We represent all of these kinds of assignment statements
            uniformly as @('vl-assignstmt-p') objects.</p>

            <h4>SystemVerilog Extensions</h4>

            <p>SystemVerilog-2012 implements special additional assignment
            operators such as @('a += b').  Per Section 11.4 of
            SystemVerilog-2012, these operators are semantically equivalent to
            blocking assignment statements except that in the case of index
            expressions such as @('a[i] += b'), the index @('i') is only
            evaluated once.  VL's parser converts assignments such as @('a +=
            b') into blocking assignments such as @('a = a + b').  To note that
            this was a @('+=') style assignment, the parser adds a
            @('VL_FANCY_ASSIGNMENT_OPERATOR') attribute to the assignstmt.</p>

            <p>SystemVerilog also adds increment and decrement operators, i.e.,
            @('a++') and @('a--').  These operators, per Section 11.4.2 of
            SystemVerilog-2012, also \"behave as blocking assignments.\"</p>")

    (:vl-deassignstmt
     :short "Representation of a deassign or release statement."
     :base-name vl-deassignstmt
     :layout :tree
     ((type   vl-deassign-type-p)
      (lvalue vl-expr-p)
      (atts   vl-atts-p
              "Any <tt>(* foo, bar = 1*)</tt> style attributes associated with
               this statement."))
     :long "<p>Deassign and release statements are described in Section 9.3.1
            and 9.3.2.</p>")

    (:vl-callstmt
     :short "Representation of a Verilog-2005 task enable statement, or a
             SystemVerilog-2012 subroutine call statement."
     :base-name vl-callstmt
     :layout :tree
     ((id      vl-scopeexpr-p "The function being called.")
      (args    vl-maybe-exprlist-p
               "The (non-datatype) arguments to the function, in order.  We use
                NIL here to represent any 'blank' arguments.")
      (loc     vl-location-p
               "Location of this statement in the source code.")
      (atts    vl-atts-p
               "Any <tt>(* foo, bar = 1*)</tt> style attributes associated with
                this statement.")
      (typearg vl-maybe-datatype-p
               "Most function calls just take expressions as arguments, in
                which case @('typearg') will be @('nil').  However, certain
                system functions can take a datatype argument.  For instance,
                you can write @('$bits(struct { ...})').  In such cases, we put
                that datatype here.")
      (systemp booleanp
               "Indicates that this is a system task like @('$display')
                instead of a user-defined function like @('myclear').")
      (voidp   booleanp
               "Indicates that this call was wrapped in @('void '(...)')."))
     :long "<p>This is similar to a @(see vl-call) expression.</p>")

    (:vl-disablestmt
     :short "Representation of a disable statement."
     :base-name vl-disablestmt
     :layout :tree
     ((id    vl-scopeexpr-p)
      (atts  vl-atts-p
             "Any <tt>(* foo, bar = 1*)</tt> style attributes associated with
              this statement."))
     :long "<p>Disable statements are simpler and just have a hierarchial
            identifier.  Apparently there are no disable statements for system
            identifiers.</p>")

    (:vl-eventtriggerstmt
     :short "Representation of an event trigger."
     :base-name vl-eventtriggerstmt
     :layout :tree
     ((id    vl-expr-p
             "Typically a name like @('foo') and @('bar'), but may instead be a
              hierarchical identifier.")
      (atts  vl-atts-p
             "Any <tt>(* foo, bar = 1*)</tt> style attributes associated with
              this statement."))
     :long "<p>Event trigger statements are used to explicitly trigger named
            events.  They are discussed in Section 9.7.3 and looks like
            this:</p>

            @({
                 -> foo;
                 -> bar[1][2][3];  // Weirdly permitted in Verilog-2005 but
                                   // not in SystemVerilog-2012.
            })

            <p>We put any indexing operations into the @('id') expression.</p>")

    (:vl-casestmt
     :base-name vl-casestmt
     :layout :tree
     :short "Representation of case, casez, and casex statements."
     ((test      vl-expr-p
                 "The expression being tested.")
      (caselist  vl-caselist-p
        "The match expressions and associated statements.")
      (default   vl-stmt-p
        "The default statement, if provided.  This is optional in the
                  Verilog and SystemVerilog syntax.  If it is omitted, our
                  parser will put a null statement here.")
      (loc vl-location-p)
      (casetype  vl-casetype-p
        "Basic case statement type: @('case'), @('casez'), or
                  @('casex').")
      (check     vl-casecheck-p
                 "SystemVerilog violation checking specification: @('unique'),
                  @('unique0'), @('priority'), or none.")
      (atts      vl-atts-p
                 "Any <tt>(* foo, bar = 1*)</tt> style attributes associated
                  with this statement.")
      (casekey   vl-casekey-p
        "Extra keyword: :inside, :matches, or none"))
     :long "<p>Case statements are discussed in the Verilog-2005 standard,
            Section 9.5 (page 127), and in the SystemVerilog-2012 standard in
            Section 12.5 (page 270).</p>

            <p>We do not yet support some SystemVerilog extensions, in
            particular:</p>

            <ul>
            <li>@('case ... matches ...')</li>
            <li>@('case ... inside ...')</li>
            </ul>")

    (:vl-ifstmt
     :base-name vl-ifstmt
     :layout :tree
     :short "Representation of an if/then/else statement."
     ((condition   vl-expr-p)
      (truebranch  vl-stmt-p)
      (falsebranch vl-stmt-p)
      (atts        vl-atts-p
                   "Any <tt>(* foo, bar = 1*)</tt> style attributes associated
                    with this statement."))
     :long "<h4>General Form:</h4>

            @({
                 if (<condition>)
                    <truebranch>
                 else
                    <falsebranch>
            })")

    (:vl-foreverstmt
     :base-name vl-foreverstmt
     :layout :tree
     :short "Representation of @('forever') statements."
     ((body  vl-stmt-p)
      (atts  vl-atts-p
             "Any <tt>(* foo, bar = 1*)</tt> style attributes associated
              with this statement."))
     :long "<p>General syntax of a forever statement:</p>

            @({
                 forever <body>;
            })

            <p>See Section 9.6 (page 130).  The forever statement continuously
            executes <i>body</i>.</p>")

    (:vl-waitstmt
     :base-name vl-waitstmt
     :layout :tree
     :short "Representation of @('wait') statements."
     ((condition vl-expr-p)
      (body      vl-stmt-p)
      (atts      vl-atts-p
                 "Any <tt>(* foo, bar = 1*)</tt> style attributes associated
                  with this statement."))
     :long "<h4>General Form:</h4>

            @({
                 wait (<condition>)
                   <body>
            })

            <p>See Section 9.7.6 (page 136).  The wait statement first
            evaluates <i>condition</i>.  If the result is true, <i>body</i> is
            executed.  Otherwise, this flow of execution blocks until
            <i>condition</i> becomes 1, at which point it resumes and
            <i>body</i> is executed.  There is no discussion of what happens
            when the <i>condition</i> is X or Z.  I would guess it is treated
            as 0 like in if statements, but who knows.</p>")

    (:vl-repeatstmt
     :base-name vl-repeatstmt
     :layout :tree
     :short "Representation of @('repeat') statements."
     ((condition vl-expr-p)
      (body      vl-stmt-p)
      (atts      vl-atts-p
                 "Any <tt>(* foo, bar = 1*)</tt> style attributes associated
                  with this statement."))
     :long "<h4>General Form:</h4>

            @({
                repeat (<condition>)
                  <body>
            })

            <p>See Section 9.6 (page 130).  The <i>condition</i> is presumably
            evaluated to a natural number, and then <i>body</i> is executed
            that many times.  If the expression evaluates to @('X') or @('Z'),
            it is supposed to be treated as zero and the statement is not
            executed at all.  (What a crock!)</p>")

    (:vl-whilestmt
     :base-name vl-whilestmt
     :layout :tree
     :short "Representation of @('while') statements."
     ((condition vl-expr-p)
      (body      vl-stmt-p)
      (atts      vl-atts-p
                 "Any <tt>(* foo, bar = 1*)</tt> style attributes associated
                  with this statement."))
     :long "<h4>General Form:</h4>

            @({
                while (<condition>)
                  <body>
            })

            <p>See Section 9.6 (page 130).  The semantics are like those of
            while loops in C; <i>body</i> is executed until <i>condition</i>
            becomes false.  If <i>condition</i> is false to begin with, then
            <i>body</i> is not executed at all.</p>")

    (:vl-dostmt
     :base-name vl-dostmt
     :layout :tree
     :short "Representation of @('do-while') loops."
     ((body      vl-stmt-p)
      (condition vl-expr-p)
      (atts      vl-atts-p
                 "Any <tt>(* foo, bar = 1*)</tt> style attributes associated
                  with this statement."))
     :long "<h4>General Form:</h4>

            @({
                do <body> while (<condition>);
            })

            <p>See SystemVerilog Section 12.7.5.  The semantics are similar
            to those of @('do-while') loops in C.</p>")

    (:vl-forstmt
     :base-name vl-forstmt
     :layout :tree
     :short "Representation of @('for') statements."
     ((test        vl-expr-p)
      (stepforms   vl-stmtlist-p)
      (body        vl-stmt-p)
      (initdecls   vl-vardecllist-p)
      (initassigns vl-stmtlist-p)
      (atts        vl-atts-p
                   "Any <tt>(* foo, bar = 1*)</tt> style attributes associated
                    with this statement."))
     :long "<h4>General Form:</h4>

            @({
                 for( <for_initialization> ; <test> ; <for_step> )
                   <body>
            })

            <p>A @('for_initialization') can either be a comma-separated list
            of variable declarations with initial values, or a comma-separated
            list of assignments (of previously declared variables).  A
            @('for_step') is a comma-separated list of variable assignments,
            increments, or decrements.</p>

            <p>See SystemVerilog Section 12.7.1.  The for statement acts like a
            for-loop in C.  First, outside the loop, it executes the
            @('for_initialization') assignments.  Then it evalutes <i>test</i>.
            If <i>test</i> evaluates to zero (or to X or Z) then the loop
            exists.  Otherwise, <i>body</i> is executed, the @('for_step') is
            performed, and we loop back to evaluating <i>test</i>.</p>

            <p>The syntax for @('for_initialization') is a little tricky since
            it can either have declarations or assignments to pre-existing
            variables, but not both.  Our representation contains a @(see
            vl-vardecllist-p) with initial values to cover the declaration case
            and a @(see vl-stmtlist-p) to cover the assignment case; one or the
            other of these will be empty.</p>")

    (:vl-foreachstmt
     :base-name vl-foreachstmt
     :layout :tree
     :short "Representation of @('foreach') statements."
     ((array    vl-scopeexpr-p)
      (loopvars vl-maybe-string-list-p)
      (vardecls vl-vardecllist-p)
      (body     vl-stmt-p)
      (atts     vl-atts-p))
     :long "<h4>General form</h4>
            @({
                 foreach( <array> [ <var1>, ..., <varN> ] ) statement
            })

            <p>See SystemVerilog-2012 section 12.7.3.  The @('<array>') should
            be a (possibly hierarchical) reference to an array variable, which
            we just represent with an expression.</p>

            <p>The variable list allows us to introduce name variables
            corresponding to certain dimensions of the array.  It should not
            mention more variables than the dimensions of the array.  Variable
            names may also be omitted to indicate that we don't want to iterate
            through that particular dimension of the array.  We represent these
            with a @(see vl-maybe-exprlist) so that you can tell when a
            variable has been omitted.</p>

            <p>We infer a @(see vl-vardecl) from each loop variable.  These
            will be @('integer') variables.  This arguably contradicts the
            standard, which suggests (12.7.3) that each loop variable is
            ``implicitly declared to be consistent with the type of array
            index.''  In other words, the standard seems to suggest that code
            like:</p>

            @({
                 logic [3:0][7:0][15:0] arr;
                 foreach (arr [i,j,k]) begin
                   $display(\"Size of i is %d\", $bits(i));
                   $display(\"Size of j is %d\", $bits(j));
                   $display(\"Size of k is %d\", $bits(k));
                 end
            })

            <p>should report sizes such as 2, 3, and 4.  But commercial tools
            seem to report a size of 32 bits for all of these variables, so we
            think that in practice these are interpreted as
            @('integer')s.</p>")

    (:vl-breakstmt
     :base-name vl-breakstmt
     :layout :tree
     :short "Representation of a @('break') statement."
     ((atts vl-atts-p
            "Any <tt>(* foo, bar = 1*)</tt> style attributes associated
             with this statement."))
     :long "<p>It doesn't get much simpler than a @('break') statement.</p>")

    (:vl-continuestmt
     :base-name vl-continuestmt
     :layout :tree
     :short "Representation of a @('continue') statement."
     ((atts vl-atts-p
            "Any <tt>(* foo, bar = 1*)</tt> style attributes associated
             with this statement."))
     :long "<p>It doesn't get much simpler than a @('continue') statement.</p>")

    (:vl-blockstmt
     :base-name vl-blockstmt
     :layout :tree
     :short "Representation of begin/end and fork/join blocks."
     ((blocktype   vl-blocktype-p
                   "Kind of block statement&mdash;@('begin/end'),
                    @('fork/join'), etc.")
      (stmts       vl-stmtlist-p)
      (name        maybe-stringp :rule-classes :type-prescription
                   "E.g., @('foo') in @('foo : begin ... end') or in
                    @('begin : foo ... end'), if applicable.")
      (atts        vl-atts-p
                   "Any <tt>(* foo, bar = 1*)</tt> style attributes associated
                    with this statement.")
      (vardecls    vl-vardecllist-p)
      (paramdecls  vl-paramdecllist-p)
      (typedefs    vl-typedeflist-p)
      (imports     vl-importlist-p)
      (loaditems   vl-blockitemlist-p
                   "Block items for this block in parse order, before splitting
                    out into typed lists.  Should not be used except in
                    shadowcheck."))
     :long "<h4>General Form (from Verilog-2005)</h4>

            @({
                 begin [ : <name> <declarations> ]
                   <statements>
                 end

                 fork [ : <name> <declarations> ]
                   <statements>
                 join
            })

            <p>See Section 9.8.  The difference between the two kinds of blocks
            is that in a @('begin/end') block, statements are to be executed in
            order, whereas in a @('fork/join') block, statements are executed
            simultaneously.</p>

            <p>A further remark is that \"Block names give a means of uniquely
            identifying all variables at any simulation time.\" This seems to
            suggest that one might try to flatten all of the declarations in a
            module by, e.g., prepending the block name to each variable
            name.</p>

            <p>With regards to declarations: \"All variables shall be static;
            that is, a unique location exists for all variables, and leaving or
            entering blocks shall not affect the values stored in them.\"</p>

            <h4>SystemVerilog-2012 Extensions</h4>

            <p>In Verilog-2005 only blocks that are named can have local
            declarations.  SystemVerilog drops this restriction and allows
            declarations even in unnamed blocks.</p>

            <p>SystemVerilog also allows the label to occur before the
            @('begin') or @('fork') keyword, and, more generally, allows labels
            to be added to other kinds of statements.  For instance, you can
            write:</p>

            @({
                 update_foo: foo = foo + bar;
            })

            <p>We turn labels like this into named begin/end blocks that
            surround their statement.</p>

            <p>Note that it's not legal to label a block both before and after
            the begin keyword.  See SystemVerilog-2012 Section 9.3.5, Statement
            Labels, on page 178.</p>

            <p>SystemVerilog also adds different kinds of @('join') keywords,
            which we now represent as part of the block's type.</p>")

    (:vl-timingstmt
     :base-name vl-timingstmt
     :layout :tree
     :short "Representation of timing statements."
     ((ctrl  vl-delayoreventcontrol-p)
      (body  vl-stmt-p)
      (atts  vl-atts-p
             "Any <tt>(* foo, bar = 1*)</tt> style attributes associated with
              this statement."))
     :long "<h4>General Form:</h4>

            @({
                <ctrl> <body>
            })

            <h4>Examples:</h4>

            @({
                #3 foo = bar;
                @@(posedge clk) foo = bar;
                @@(bar or baz) foo = bar | baz;
            })")

    (:vl-returnstmt
     :base-name vl-returnstmt
     :layout :tree
     :short "Representation of return statements."
     ((val   vl-maybe-expr-p
             "The value to return, if any.")
      (atts  vl-atts-p
             "Any <tt>(* foo, bar = 1*)</tt> style attributes associated with
              this statement.")
      (loc   vl-location-p
             "Location of this statement in the source code.")))

    (:vl-assertstmt
     :base-name vl-assertstmt
     :layout :tree
     :short "Representation of an immediate assertion statement."
     ((assertion vl-assertion-p
                 "All of the data for the assertion.  We split this out from
                  the main @(see vl-stmt) structure so that module-level and
                  statement-level assertions can easily share the same core
                  representation.")
      (atts       vl-atts-p
                  "Any <tt>(* foo, bar = 1*)</tt> style attributes associated
                   with this statement.")))

    (:vl-cassertstmt
     :base-name vl-cassertstmt
     :layout :tree
     :short "Representation of a concurrent assertion statement."
     ((cassertion vl-cassertion-p
                  "All of the data for the assertion.  We split this out from
                   the main @(see vl-stmt) structure so that module-level and
                   statement-level assertions can easily share the same core
                   representation.)")
      (atts       vl-atts-p
                  "Any <tt>(* foo, bar = 1*)</tt> style attributes associated
                   with this statement."))))

  (defprod vl-assertion
    :short "Representation of an immediate assertion."
    :layout :tree
    :tag :vl-assertion
    :measure (two-nats-measure (acl2-count x) 1)
    ((name       maybe-stringp :rule-classes :type-prescription
                 "The label for this assertion, if provided.  Note that in a
                  statement context, labels like @('foo : assert ...')  mainly
                  get turned into named @('begin/end') blocks, but we do take
                  care to also put the name into the assertion object.")
     (type       vl-asserttype-p
                 "The type of this assertion, e.g., @('assert'), @('assume'),
                  etc.")
     (deferral   vl-assertdeferral-p
                 "Indicates whether this assertion is a regular, non-deferred
                  assertion, or a #('#0') or @('final') deferred assertion.")
     (condition  vl-expr-p
                 "The condition to assert.  Note that since this is an
                  immediate assertion, the condition is a simple expression,
                  not a fancy sequence or property.")
     (success    vl-stmt-p
                 "For most assertions, this is the success statement for the
                  associated action block, or a @(see vl-nullstmt) if there is
                  no success statement.  Note that @('cover') assertions are
                  special and don't have an action block, so for a @('cover')
                  assertion this is just the associated statement, if any.")
     (failure    vl-stmt-p
                 "This is the @('else') statement from the action block, or a
                  @(see vl-nullstmt) if there is no @('else') statement.  For
                  @('cover') assertions this is always just a @(see
                  vl-nullstmt) since there is no @('else') action.")
     (loc        vl-location-p
                 "Location of this statement in the source code.")))

  (defprod vl-cassertion
    :short "Representation of a concurrent assertion."
    :layout :tree
    :tag :vl-cassertion
    :measure (two-nats-measure (acl2-count x) 1)
    ((name        maybe-stringp :rule-classes :type-prescription
                  "The label for this assertion, if provided.  Note that in a
                   statement context, labels like @('foo : assert ...')  mainly
                   get turned into named @('begin/end') blocks, but we do take
                   care to also put the name into the assertion object.")
     (type        vl-asserttype-p
                  "The type of this assertion, e.g., @('assert'), @('assume'),
                   etc.")
     (sequencep   booleanp :rule-classes :type-prescription
                  "This should be @('nil') except for @('cover sequence')
                   statements, where it is @('t').  Cover statements are
                   special; most concurrent assertions are just things like
                   @('assert property ...') or @('assume property ...')  and
                   don't even have a @('sequence') form.")
     (condition   vl-propspec-p
                  "The property specification being asserted.")
     (success     vl-stmt-p
                  "For most assertions, this is the success statement for the
                   associated action block, or a @(see vl-nullstmt) if there
                   is no success statement.  Note that @('cover') assertions
                   are special and don't have an action block, so for a
                   @('cover') assertion this is just the associated
                   statement, if any.")
     (failure     vl-stmt-p
                  "This is the @('else') statement from the action block, or
                   a @(see vl-nullstmt) if there is no @('else') statement.
                   For @('cover') assertions this is always just a @(see
                   vl-nullstmt) since there is no @('else') action.")
     (loc         vl-location-p
                  "Location of this statement in the source code."))))

;; NOTE: Other statement subtypes are declared in stmt-tools.  This is here
;; because scopestack needs it.
(define vl-blockstmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  (vl-stmt-case x :vl-blockstmt))

(local (in-theory (disable vl-stmtlist-p-of-cdr-when-vl-stmtlist-p
                           consp-when-member-equal-of-vl-caselist-p
                           vl-stmt-p-when-member-equal-of-vl-stmtlist-p)))


(fty::deflist vl-assertionlist
  :elt-type vl-assertion)

(fty::deflist vl-cassertionlist
  :elt-type vl-cassertion)


;                       INITIAL, FINAL, AND ALWAYS BLOCKS
;
; Initial and always blocks just have a statement and, perhaps, some
; attributes.

(defprod vl-initial
  :short "Representation of an @('initial') statement."
  :tag :vl-initial
  :layout :tree
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


(defprod vl-final
  :short "Representation of a @('final') statement."
  :tag :vl-final
  :layout :tree
  ((stmt vl-stmt-p
         "Represents the actual statement, e.g., @('$display(\"Goodbye\");')
          below.")
   (atts vl-atts-p
         "Any attributes associated with this @('final') statement.")
   (loc  vl-location-p
         "Where the final statemetn was found in the source code."))

  :long "<p>SystemVerilog's @('final') statements are run at the end of
simulation.  For instance,</p>

@({
    module mymod (a, b, ...) ;
      final $display(\"Goodbye\");   <-- final statement
    endmodule
})")


(defenum vl-alwaystype-p
  (:vl-always
   :vl-always-comb
   :vl-always-latch
   :vl-always-ff)
  :short "Indicates the kind of an always statement."
  :long "<p>In Verilog-2005 there are only @('always') statements.
SystemVerilog-2012 adds @('always_comb'), @('always_latch'), and
@('always_ff').</p>")

(defprod vl-always
  :short "Representation of an always statement."
  :tag :vl-always
  :layout :tree
  ((type vl-alwaystype-p
         "What kind of @('always') block this is, e.g., @('always'), @('always_comb'),
          @('always_latch'), or @('always_ff').")
   (stmt vl-stmt-p
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

(fty::deflist vl-initiallist
  :elt-type vl-initial-p
  :elementp-of-nil nil)

(fty::deflist vl-finallist
  :elt-type vl-final-p
  :elementp-of-nil nil)

(fty::deflist vl-alwayslist
  :elt-type vl-always-p
  :elementp-of-nil nil)



(defprod vl-propport
  :short "Representation of a single @('property') or @('sequence') port."
  :tag :vl-propport
  ((name   stringp :rule-classes :type-prescription
           "Name of this port.")
   (localp booleanp :rule-classes :type-prescription
           "True if the @('local') keyword was provided.")
   (dir    vl-direction-p
           "The direction for this port.  Note that the ports for a sequence
            can be either @('input'), @('output'), or @('inout') ports.  The
            ports for a property are always @('input') ports.")
   (type   vl-datatype-p
           "The type declared for this port, if any.  Note that the special
            keywords @('property'), @('sequence'), and @('untyped') can also be
            used here; we represent them as ordinary @(see vl-datatype)s, see
            @(see vl-coretypename-p).  This type includes any array dimensions
            associated with the port.")
   (arg    vl-propactual-p
           "The default property or sequence actual assigned to this port.  If
            there is no such assignment, this will just be a blank @(see
            vl-propactual).")
   (atts   vl-atts-p
           "Any <tt>(* foo = bar, baz *)</tt> style attributes.")
   (loc    vl-location-p)))

(fty::deflist vl-propportlist
  :elt-type vl-propport
  :elementp-of-nil nil)

(defprod vl-property
  :measure (two-nats-measure (acl2-count x) 1)
  :tag :vl-property
  :short "Represents a single @('property')...@('endproperty') declaration."
  ((name   stringp :rule-classes :type-prescription
           "E.g., this is @('foo') for @('property foo ... endproperty').")
   (ports  vl-propportlist-p
           "The ports for this property declaration.")
   (decls  vl-vardecllist-p
           "Variable declarations for this property.")
   (spec   vl-propspec-p
           "The main content of the property declaration.  The property spec
            contains its clocking information, disable condition, and the
            core property expression.")
   (loc    vl-location-p)))

(defprod vl-sequence
  :measure (two-nats-measure (acl2-count x) 1)
  :tag :vl-sequence
  :short "Represents a single @('sequence')...@('endsequence') declaration."
  ((name   stringp :rule-classes :type-prescription
           "E.g., this is @('foo') for @('sequence foo ... endsequence').")
   (ports  vl-propportlist-p
           "The ports for this sequence declaration.")
   (decls  vl-vardecllist-p
           "Variable declarations for this sequence.")
   (expr   vl-propexpr-p
           "The main content of the sequence declaration.  The expression
            should be a valid sequence expression.  We represent it as a
            @(see vl-propexpr), which is overly permissive but sufficient
            to capture any sequence expression.")
   (loc    vl-location-p)))

(fty::deflist vl-propertylist
  :elt-type vl-property
  :elementp-of-nil nil)

(fty::deflist vl-sequencelist
  :elt-type vl-sequence
  :elementp-of-nil nil)


(defprod vl-clkskew
  :short "Representation of a clock skew (clocking blocks)."
  :tag :vl-clkskew
  :layout :tree
  ((delay vl-maybe-expr-p "Cycle delay amount, e.g., @('#3'), if applicable.")
   (edge  vl-evatomtype-p "Edge indicator, or @(':vl-noedge') for edgeless skews."))
  :long "<p>Clock skews are described in SystemVerilog-2012 Section 14.4.  They
         indicate when a signal is to be sampled relative to a clocking event.
         Some examples:</p>

         @({
              clocking @(posedge clk);
                 input #3 foo;          // <-- skew is '#3'
                 input negedge bar;     // <-- skew is 'negedge'
                 input negedge #3 baz;  // <-- skew is both 'negedge #3'
              endclocking
         })

         <p>Per 14.3 (page 304) input skews are implicitly ``negative'' in that
         they say how far before the clock the signal should be sampled; output
         skews are ``positive'' and refer to some time after the clock.</p>

         <p>Instead of numbers, skews can also be @('posedge'), @('negedge'),
         or @('edge'), which indicate that, e.g., that @('bar') above should be
         sampled at the @('negedge') of @('clk').  I'm not sure what @('edge')
         means or how these combine with delays, but Section 14.4 may be a good
         starting place.</p>")

(defoption vl-maybe-clkskew vl-clkskew)


(defprod vl-clkassign
  :short "Representation of a single clocking assignment (clocking blocks)."
  :tag :vl-clkassign
  :layout :tree
  ((name   stringp :rule-classes :type-prescription
           "Name of the wire being sampled or expression being named.")
   (loc    vl-location-p
           "Location of this clocking assignment.")
   (inputp booleanp :rule-classes :type-prescription
           "Indicates whether this is an @('input') or @('output') clocking
            variable.  See below for notes on inouts.")
   (rhs    vl-maybe-expr-p
           "Expression to sample, or @('nil') if there is no such expression.
            When provided, this might typically be a hierarchical reference to
            some signal, but it could also be something more complex like a
            concatenation.")
   (skew   vl-maybe-clkskew-p
           "Clock skew for when to sample this variable, if specified."))
  :long "<p>Some examples:</p>
         @({
              clocking @(posedge clk);
                 input #3 foo;                 // <-- clkassign with delay and no rhs
                 output bar = top.sub.mybar;   // <-- clkassign with an rhs
                 inout baz;                    // <-- two clkassigns, one input, one output
              endclocking
         })

         <p>The SystemVerilog-2012 grammar allows @('inout')s here, but note
         from Section 14.1 (page 303) that ``a clockvar whose
         clocking_direction is inout shall behave as if it were two clockvars,
         one input and one output, having the same name and same
         clocking_signal.''  We take this approach in VL: when the parser
         encounters an inout, we explicitly split it up into separate
         input/output clkassigns.</p>")

(fty::deflist vl-clkassignlist
  :elt-type vl-clkassign)


(defprod vl-clkdecl
  :short "Representation of a (non-global) clocking block declaration."
  :tag :vl-clkdecl
  :layout :tree
  ((defaultp booleanp :rule-classes :type-prescription
             "Was the @('default') keyword provided?")
   (name     maybe-stringp :rule-classes :type-prescription
             "Name of the clocking block, if provided.  Per SystemVerilog-2012
              14.3, only default clocking blocks can be unnamed.")
   (event    vl-evatomlist-p
             "The clocking event expression for this block.  Should always be
              non-empty and is typically a single edge expression like
              @('@(posedge clk)').")
   ;; Things that come from clocking_items ---
   (iskew      vl-maybe-clkskew-p
               "Default input clocking skew, if applicable.")
   (oskew      vl-maybe-clkskew-p
               "Default output clocking skew, if applicable.")
   (clkassigns vl-clkassignlist-p
               "Clocking assignments like @('input #3 foo').")
   (properties vl-propertylist-p
               "Any properties declared in this block.")
   (sequences  vl-sequencelist-p
               "Any sequences declared in this block.")
   ;; BOZO can also have let statements but we don't support those yet.
   (loc        vl-location-p)
   (atts       vl-atts-p)))

(fty::deflist vl-clkdecllist
  :elt-type vl-clkdecl)

(defprod vl-gclkdecl
  :short "Representation of a global clocking declaration."
  :tag :vl-gclkdecl
  :layout :tree
  ((name maybe-stringp :rule-classes :type-prescription
         "Name of the declaration, if one is provided.")
   (event vl-evatomlist-p "The clocking event expression.")
   (loc vl-location-p)
   (atts vl-atts-p)))

(fty::deflist vl-gclkdecllist
  :elt-type vl-gclkdecl)

(defprod vl-defaultdisable
  :short "Representation of a @('default disable iff') construct."
  :tag :vl-defaultdisable
  :layout :tree
  ((exprdist vl-exprdist-p
             "The argument, e.g., @('reset') in @('default disable iff reset')")
   (loc  vl-location-p)
   (atts vl-atts-p)))

(fty::deflist vl-defaultdisablelist
  :elt-type vl-defaultdisable)


;; (defenum vl-taskporttype-p
;;   (:vl-unsigned
;;    :vl-signed
;;    :vl-integer
;;    :vl-real
;;    :vl-realtime
;;    :vl-time)
;;   :short "Representation for the type of task ports, function return types, and
;; function inputs."

;;   :long "<p>These are the various return types that can be used with a Verilog
;; task's input, output, or inout declarations.  For instance, a task can have
;; ports such as:</p>

;; @({
;;   task mytask;
;;     input integer count;  // type :vl-integer
;;     output signed value;  // type :vl-signed
;;     inout x;              // type :vl-unsigned
;;     ...
;;   endtask
;; })

;; <p>There isn't an explicit @('unsigned') type that you can write; so note that
;; @(':vl-unsigned') is really the type for \"plain\" ports that don't have an
;; explicit type label.</p>

;; <p>These same types are used for the return values of Verilog functions.  For
;; instance, we use @(':vl-unsigned') for a function like:</p>

;; @({ function [7:0] add_one ; ... endfunction })

;; <p>whereas we use @(':vl-real') for a function like:</p>

;; @({ function real get_ratio ; ... endfunction })

;; <p>Likewise, the inputs to Verilog functions use these same kinds of
;; types.</p>")

;; (defprod vl-taskport
;;   :short "Representation of a task port or a function input."
;;   :tag :vl-taskport
;;   :layout :Tree

;;   ((name  stringp
;;           :rule-classes :type-prescription
;;           "The name of this task port.")

;;    (dir   vl-direction-p
;;           :rule-classes
;;           ((:rewrite)
;;            (:type-prescription
;;             :corollary
;;             (implies (force (vl-taskport-p x))
;;                      (and (symbolp (vl-taskport->dir x))
;;                           (not (equal (vl-taskport->dir x) t))
;;                           (not (equal (vl-taskport->dir x) nil))))))
;;           "Says whether this is an input, output, or inout port.  Note that
;;            tasks can have all three kinds of ports, but functions only have
;;            inputs.")

;;    (type  vl-taskporttype-p
;;           :rule-classes
;;           ((:rewrite)
;;            (:type-prescription
;;             :corollary
;;             (implies (force (vl-taskport-p x))
;;                      (and (symbolp (vl-taskport->type x))
;;                           (not (equal (vl-taskport->type x) t))
;;                           (not (equal (vl-taskport->type x) nil))))))
;;           "Says what kind of port this is, i.e., @('integer'), @('real'),
;;           etc.")

;;    (range vl-maybe-range-p
;;           "The size of this input.  A range only makes sense when the type is
;;            @(':vl-unsigned') or @(':vl-signed').  It should be @('nil') when
;;            other types are used.")

;;    (atts  vl-atts-p
;;           "Any attributes associated with this input.")

;;    (loc   vl-location-p
;;           "Where this input was found in the source code."))

;;   :long "<p>Verilog tasks have ports that are similar to the ports of a module.
;; We represent these ports with their own @('vl-taskport-p') structures, rather
;; than reusing @(see vl-portdecl-p), because unlike module port declarations,
;; task ports can have types like @('integer') or @('real').</p>

;; <p>While Verilog functions don't have @('output') or @('inout') ports, they do
;; have input ports that are very similar to task ports.  So, we reuse
;; @('vl-taskport-p') structures for function inputs.</p>")

;; (fty::deflist vl-taskportlist :elt-type vl-taskport-p
;;   :elementp-of-nil nil)

;; (defprojection vl-taskportlist->names ((x vl-taskportlist-p))
;;   :returns (names string-listp)
;;   (vl-taskport->name x))

(deftranssum vl-portdecl-or-blockitem
  (vl-portdecl-p
   vl-blockitem-p)
  :parents (shadowcheck)
  :short "Goofy structure for representing the loaditems of functions/tasks.")

(fty::deflist vl-portdecl-or-blockitem-list
  :elt-type vl-portdecl-or-blockitem
  :parents (shadowcheck)
  ///
  (local (in-theory (enable vl-portdecl-or-blockitem-p)))

  (defthm vl-portdecl-or-blockitem-list-p-when-vl-portdecllist-p
    (implies (vl-portdecllist-p x)
             (vl-portdecl-or-blockitem-list-p x))
    :hints(("Goal"
            :induct (len x)
            :in-theory (enable tag-reasoning))))

  (defthm vl-portdecl-or-blockitem-list-p-when-vl-blockitemlist-p
    (implies (vl-blockitemlist-p x)
             (vl-portdecl-or-blockitem-list-p x))
    :hints(("Goal" :induct (len x)))))


(defprod vl-fundecl
  :short "Representation of a single Verilog function."
  :tag :vl-fundecl
  :layout :tree

  ((name       stringp
               :rule-classes :type-prescription
               "Name of this function, e.g., @('lower_bits') below.")

   (rettype    vl-datatype-p
               "Return type of the function, e.g., a function might return an
                ordinary unsigned or signed result of some width, or might
                return a @('real') value, etc.  For instance, the return type
                of @('lower_bits') below is @(':vl-unsigned').")
   
   (body       vl-stmt-p
               "The body of the function.  We represent this as an ordinary statement,
                but it must follow certain rules as outlined in 10.4.4, e.g.,
                it cannot have any time controls, cannot enable tasks, cannot
                have non-blocking assignments, etc.")

   (loc        vl-location-p
               "Where this declaration was found in the source code.")

   (portdecls  vl-portdecllist-p
               "The arguments to the function, e.g., @('input [7:0] a') below.
                Functions must have at least one input.  We check this in our
                parser, but we don't syntactically enforce this requirement in
                the @('vl-fundecl-p') structure.  In Verilog-2005, functions
                may only have inputs (i.e., they can't have outputs or inouts),
                but our @(see vl-portdecl-p) structures have a direction, so in
                the context of a function declaration this direction should
                always be @(':vl-input').  In SystemVerilog functions can have
                other kinds of ports, but functions with output/inout ports
                have restrictions and can't be used in expressions like normal
                functions.")

   (function   sv::maybe-svex-p
               "The svex expression for the value of the function, if it has been
                computed, which happens during elaboration")

   (constraints sv::constraintlist-p
                "Constraints that must hold of the function inputs, or the result
                 may be undefined; computed during elaboration")

   (lifetime   vl-lifetime-p
               "Indicates whether an explicit @('automatic') or @('static')
                lifetime was provided.  An automatic function is supposed to be
                reentrant and have its local parameters dynamically allocated
                for each function call, with various consequences.")

   (vardecls    vl-vardecllist-p
                "Local variable declarations, including ones for the ports and
                 return value (see below).")

   (paramdecls  vl-paramdecllist-p
                "Local parameter declarations")

   (typedefs    vl-typedeflist-p
                "Local type declarations.")

   (imports     vl-importlist-p
                "Local package imports")

   (atts       vl-atts-p
               "Any attributes associated with this function declaration.")

   (loaditems   vl-portdecl-or-blockitem-list-p
                "Owned by @(see shadowcheck); do not use elsewhere.
                 Declarations within the function, in parse order, before
                 sorting out into imports, vardecls, paramdecls, and
                 typedefs."))

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
assign to a function's name to indicate its return value.</p>

<p>To simplify scoping issues, we put \"hidden\" variables declarations for the
ports and return value of the function into its @('decls').  These ports are
marked with the @('VL_HIDDEN_DECL_FOR_TASKPORT') attribute.  The pretty printer
and other code rely on this attribute to produce the correct output.  These
extra declarations are created automatically by the loader.</p>")

(fty::deflist vl-fundecllist
  :elt-type vl-fundecl-p
  :elementp-of-nil nil)

(defprojection vl-fundecllist->names ((x vl-fundecllist-p))
  :returns (names string-listp)
  (vl-fundecl->name x))


(defprod vl-taskdecl
  :short "Representation of a single Verilog task."
  :tag :vl-taskdecl
  :layout :tree

  ((name       stringp
               :rule-classes :type-prescription
               "The name of this task.")

   (body       vl-stmt-p
               "The statement that gives the actions for this task, i.e., the
                entire @('begin/end') statement in the below task.")

   (loc        vl-location-p
               "Where this task was found in the source code.")

   (portdecls  vl-portdecllist-p
               "The input, output, and inout ports for the task.")

   (vardecls    vl-vardecllist-p
                "Local variable declarations, including ones for the ports and
                 return value (see below); these are marked with
                 @('VL_HIDDEN_DECL_FOR_TASKPORT').")

   (paramdecls  vl-paramdecllist-p
                "Local parameter declarations")

   (typedefs    vl-typedeflist-p
                "Local type declarations.")

   (imports     vl-importlist-p
                "Local package imports")

   (atts       vl-atts-p
               "Any attributes associated with this task declaration.")

   (lifetime   vl-lifetime-p
               "Indicates whether an explicit @('automatic') or @('static')
                lifetime was provided.  Each invocation of an automatic task
                has its own copy of its variables.  For instance, the task
                below had probably better be automatic if it there are going to
                be concurrent instances of it running, since otherwise
                @('temp') could be corrupted by the other task.")

   (loaditems   vl-portdecl-or-blockitem-list-p
                "Owned by @(see shadowcheck); do not use elsewhere.
                 Declarations within the task, in parse order, before sorting
                 out into imports, vardecls, paramdecls, and typedefs."))

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

(fty::deflist vl-taskdecllist
  :elt-type vl-taskdecl-p
  :elementp-of-nil nil)

(defprojection vl-taskdecllist->names ((x vl-taskdecllist-p))
  :returns (names string-listp)
  (vl-taskdecl->name x))




(defprod vl-modport-port
  :parents (vl-interface)
  :short "A single port from a modport declaration."
  :long  "<p>The syntax for this is:</p>
@({
 modport_simple_ports_declaration ::=
 port_direction modport_simple_port { , modport_simple_port }

 modport_simple_port ::=
 port_identifier
 | . port_identifier ( [ expression ] )
 })

<p>As with regular ports, if the expression is not provided then the port
identifier is turned into an expression.  The variables used in the expression
must be declared in the interface, but it is permissible for the expression to
be non-sliceable, at least if it's an input.</p>"

  ((name stringp         "Name of the port; often the same as the expr")
   (dir  vl-direction-p  "Port direction")
   (loc  vl-location-p :default *vl-fakeloc*)
   (expr vl-maybe-expr-p "Expression in terms of the declared variables of the interface.")
   (atts vl-atts-p       "attributes"))
  :prepwork ())

(fty::deflist vl-modport-portlist
  :elt-type vl-modport-port
  :elementp-of-nil nil
  :true-listp nil)

(defprod vl-modport
  :parents (vl-interface)
  :short "A modport declaration within an interface"
  :long "<p>Missing task/function import/exports and clocking blocks.</p>"
  ((name      stringp                "the name of the modport declaration; often master or slave")
   (loc       vl-location-p :default *vl-fakeloc*)
   (ports     vl-modport-portlist-p  "the ports; names must be declared in the interface")
   (atts      vl-atts-p              "attributes"))
  :tag :vl-modport)

(fty::deflist vl-modportlist
  :elt-type vl-modport
  :elementp-of-nil nil
  :true-listp nil)


(defenum vl-fwdtypedefkind-p
  (:vl-enum
   :vl-struct
   :vl-union
   :vl-class
   :vl-interfaceclass)
  :parents (vl-fwdtypedef-p)
  :short "Kinds of forward type declarations.")

(defprod vl-fwdtypedef
  :tag :vl-fwdtypedef
  :short "Representation of a forward typedef like @('typedef struct foo_t;')."
  ((atts vl-atts-p)
   (kind vl-fwdtypedefkind-p)
   (name stringp)
   (loc  vl-location-p)))

(fty::deflist vl-fwdtypedeflist
  :elt-type vl-fwdtypedef-p
  :elementp-of-nil nil)




(defenum vl-dpispec-p
  (:vl-dpi
   :vl-dpi-c)
  :parents (vl-dpiimport vl-dpiexport)
  :short "Representation of the @('\"DPI\"') or @('\"DPI-C\"') specification
          used in DPI import/exports."
  :long "<p>This governs low level arcana like how packed array arguments are
         passed to C.</p>")

(defenum vl-dpiprop-p
  (nil
   :vl-dpi-pure
   :vl-dpi-context)
  :parents (vl-dpiimport)
  :short "Representation of @('pure') or @('context') properties."
  :long "<p>See SystemVerilog-2012 Sections 35.5.2 and 35.5.3.  A DPI imported
         function (not task) can be declared as @('pure'), which is supposed to
         be a promise that the C function's result only depends only on its
         inputs, doesn't do any file IO, doesn't access any global variables,
         etc.</p>

         <p>Alternately, an imported function or task can be declared as
         @('context'), which means that it is intended to call exported
         subroutines that access SystemVerilog data objects besides its
         arguments.  The simulator may have to take special measures and avoid
         various optimizations when calling these functions.</p>")

(defprod vl-dpiimport
  :short "Represents a single import of a C function into SystemVerilog via the
          Direct Programming Interface."
  :tag :vl-dpiimport
  :layout :tree
  ((name      stringp
              :rule-classes :type-prescription
              "The SystemVerilog version of the name (may differ from the C
               function's name.)")
   (c-name    stringp
              :rule-classes :type-prescription
              "The name of the C function being imported.")
   (spec      vl-dpispec-p
              "Indicates whether this function uses the deprecated @('\"DPI\"')
               or the replacement @('\"DPI-C\"') interface.")
   (prop      vl-dpiprop-p
              "Indicates whether the @('pure') or @('context') keywords were
               provided.")
   (rettype   vl-maybe-datatype-p
              "For an imported function, this is the return type.  For a task,
               it is @('nil'), which lets you distinguish whether this import
               is for a function or a task.")
   (portdecls vl-portdecllist-p
              "The arguments from the function/task prototype.")
   (atts      vl-atts-p
              "Any attributes associated with this DPI import.")
   (loc       vl-location-p
              "Where this DPI import was found in the source code."))

  :long "<p>SystemVerilog's Direct Programming Interface (DPI) allows for
         SystemVerilog code to invoke functions that are written in C, and for
         C programs to invoke SystemVerilog functions/tasks.  (In theory the
         DPI can also be used to connect to other languages besides C, but
         we'll just say C here.)</p>

         <p>A DPI @('import') statement is for making C functions available to
         the SystemVerilog design.  A DPI @('export') goes the other way and we
         treat them separately; see @(see vl-dpiexport).</p>

         <p>We cannot imagine any way for VL to really comprehend or make any
         real use of imported C code.  However, we do try to at least parse and
         represent the actual DPI import statements so that they don't lead to
         parse errors.  We also regard import statements as real, legitimate
         scope items that can be looked up in a @(see scopestack), which allows
         applications like @(see vl-lint) to recognize that calls of these
         functions/tasks are not undefined.</p>")

(fty::deflist vl-dpiimportlist
  :elt-type vl-dpiimport
  :elementp-of-nil nil)

(defenum vl-dpifntask-p
  (:vl-dpi-function
   :vl-dpi-task)
  :parents (vl-dpiexport)
  :short "Indicates whether we are exporting a @('function') or @('task').")

(defprod vl-dpiexport
  :short "Represents a single export of a SystemVerilog function/task for use
          in C programs via the Direct Programming Interface."
  :tag :vl-dpiexport
  :layout :tree
  ((name      stringp
              :rule-classes :type-prescription
              "The SystemVerilog version of the name (may differ from the C
               function's name.)")
   (c-name    stringp
              :rule-classes :type-prescription
              "The name of the new C function to create which will correspond
               to this SystemVerilog function/task.")
   (spec      vl-dpispec-p
              "Indicates whether this function uses the deprecated @('\"DPI\"')
               or the replacement @('\"DPI-C\"') interface.")
   (fntask    vl-dpifntask-p
              "Are we exporting a function or a task?")
   (atts      vl-atts-p
              "Any attributes associated with this DPI export.")
   (loc       vl-location-p
              "Where this DPI export was found in the source code."))

  :long "<p>SystemVerilog's Direct Programming Interface (DPI) allows for
         SystemVerilog code to invoke functions that are written in C, and for
         C programs to invoke SystemVerilog functions/tasks.  (In theory the
         DPI can also be used to connect to other languages besides C, but
         we'll just say C here.)</p>

         <p>A DPI @('export') statement is for making SystemVerilog tasks and
         functions available to C programs.  A DPI @('import') goes the other
         way and we treat them separately; see @(see vl-dpiimport).</p>

         <p>We cannot imagine any way for VL to really comprehend or make any
         real use of imported C code.  However, we do try to at least parse and
         represent the actual DPI export statements so that they don't lead to
         parse errors.</p>

         <p>Aside from parsing, we largely don't care about DPI exports.
         Unlike DPI imports, we don't treat exports as scope items because if
         you look up a function @('foo'), you want to find its definition, not
         the fact that it was exported.</p>")

(fty::deflist vl-dpiexportlist
  :elt-type vl-dpiexport
  :elementp-of-nil nil)


(defprod vl-genvar
  :tag :vl-genvar
  :short "Representation of a genvar declaration."
  ((name stringp)
   (atts vl-atts-p)
   (loc  vl-location-p)))

(fty::deflist vl-genvarlist :elt-type vl-genvar :elementp-of-nil nil)


(defprod vl-bind
  :layout :tree
  :tag :vl-bind
  :short "Representation of a bind directive."
  ((scope maybe-stringp :rule-classes :type-prescription
          "When non-NIL, this indicates the name of the module or interface to
           insert the modinsts into.  Otherwise this is a simple bind directive
           without a @('bind_target_scope') and should just refer to an
           explicit instance.")
   (addto vl-exprlist-p
          "Possibly empty, in which case @('scope') should be provided and in
           which case the modinst is to be inserted into all instances of the
           indicated scope.  Alternately: a list of the particular instances
           where modinst is to be added to.")
   (modinsts vl-modinstlist-p
             "The modinst(s) to be added to the target.")
   (loc     vl-location-p)
   (atts    vl-atts-p))
  :long "<p>There are scoped and scopeless versions of bind directives.  From
         SystemVerilog-2012:</p>

         @({
               bind_directive ::=
                  'bind' bind_target_scope [ ':' bind_target_instance_list ] bind_instantiation ';'
                | 'bind' bind_target_instance bind_instantiation ';'
         })

         <p>Note: our parser allows arbitrary expressions for the
         @('bind_target_instance')s, which is perhaps too permissive, but the
         SystemVerilog-2012 grammar appears to be incorrect: it says the rule
         is:</p>

         @({
              bind_target_instance ::= hierarchical_identifier constant_bit_select
         })

         <p>But the examples in Section 23.11 clearly show targets that do not
         have such selects.</p>")

(fty::deflist vl-bindlist :elt-type vl-bind :elementp-of-nil nil)


(defprod vl-class
  :short "Representation of a single @('class')."
  :tag :vl-class
  :layout :tree
  ;; We define classes here and make them modelements because they can occur
  ;; within (?).  Fortunately it looks like you can't use generates inside of
  ;; classes, so we should not need to make these mutually recursive with
  ;; genelements or anything like that.
  ((name stringp
         :rule-classes :type-prescription
         "The name of this class as a string.")
   (warnings vl-warninglist-p)
   (minloc   vl-location-p)
   (maxloc   vl-location-p)
   (atts     vl-atts-p)
   (comments vl-commentmap-p)
   (virtualp booleanp :rule-classes :type-prescription)
   (lifetime vl-lifetime-p))
  :long "BOZO incomplete stub -- we don't really support classes yet."
  :extra-binder-names (loc))

(define vl-class->loc ((x vl-class-p))
  ;; We want these to be like an ordinary modelement, so dumbly make it so
  ;; so dumbly make loc an alias for minloc.
  :parents (vl-class)
  :enabled t
  (vl-class->minloc x))

(fty::deflist vl-classlist :elt-type vl-class-p
  :elementp-of-nil nil)

(defprojection vl-classlist->names ((x vl-classlist-p))
  :parents (vl-classlist-p)
  :returns (names string-listp)
  (vl-class->name x))


(defprod vl-covergroup
  :short "Representation of a single @('covergroup')."
  :tag :vl-covergroup
  :layout :tree
  ((name stringp
         :rule-classes :type-prescription
         "The name of this covergroup as a string.")
   (loc  vl-location-p)
   (atts     vl-atts-p))
  :long "BOZO incomplete stub -- we don't really support covergroupes yet.")

(fty::deflist vl-covergrouplist :elt-type vl-covergroup-p
  :elementp-of-nil nil)

(defprojection vl-covergrouplist->names ((x vl-covergrouplist-p))
  :parents (vl-covergrouplist-p)
  :returns (names string-listp)
  (vl-covergroup->name x))

(defprod vl-elabtask
  :short "Representation of a SystemVerilog @('elaboration_system_task')."
  :tag :vl-elabtask
  :layout :tree
  ((stmt vl-stmt-p
         "In practice this should always be a @(see vl-callstmt), and should be
          a call of @('$fatal'), @('$error'), @('$warning'), or @('$info').")
   ;; Potentially we could add other fields here, but the callstmt has its
   ;; own location, atts, etc., so it's probably best to just use that.
   )
  :extra-binder-names (loc))

(define vl-elabtask->loc ((x vl-elabtask-p))
  :returns (loc vl-location-p)
  (b* (((vl-elabtask x)))
    (vl-stmt-case x.stmt
      (:vl-callstmt x.stmt.loc)
      (:otherwise   (progn$
                     (raise "Elabtask is not a call stmt?")
                     *vl-fakeloc*)))))

(fty::deflist vl-elabtasklist :elt-type vl-elabtask
  :elementp-of-nil nil)

(defsection modelements
  :parents nil

  (defconst *vl-modelement-typenames*
    '(portdecl
      assign
      alias
      vardecl
      paramdecl
      fundecl
      taskdecl
      modinst
      gateinst
      always
      initial
      final
      typedef
      import
      fwdtypedef
      modport
      genvar
      assertion
      cassertion
      property
      sequence
      clkdecl
      gclkdecl
      defaultdisable
      dpiimport
      dpiexport
      bind
      class
      covergroup
      elabtask
      ))

  (local (defun typenames-to-tags (x)
           (declare (xargs :mode :program))
           (if (atom x)
               nil
             (cons (intern$ (cat "VL-" (symbol-name (car x))) "KEYWORD")
                   (typenames-to-tags (cdr x))))))

  (make-event
   `(defconst *vl-modelement-tagnames*
      ',(typenames-to-tags *vl-modelement-typenames*)))

  (defun vl-typenames-to-tmplsubsts (types)
    (declare (xargs :mode :program))
    (if (atom types)
        nil
      (let ((name (symbol-name (car types))))
        (cons (make-tmplsubst
               :strs `(("__TYPE__" ,name . vl-package)
                       ("__ELTS__" ,(cond ((member (char name (1- (length name))) '(#\S #\s))
                                           (str::cat name "ES"))
                                          ((member (char name (1- (length name))) '(#\Y #\y))
                                           (str::cat (subseq name 0 (1- (length name))) "IES"))
                                          (t
                                           (str::cat name "S"))) . vl-package)))
              (vl-typenames-to-tmplsubsts (cdr types))))))

  (defconst *vl-modelement-tmplsubsts*
    (vl-typenames-to-tmplsubsts *vl-modelement-typenames*))

  (defun project-over-modelement-types (template)
    (declare (xargs :mode :program))
    (template-proj template *vl-modelement-tmplsubsts*))

  (defun append-over-modelement-types (template)
    (declare (xargs :mode :program))
    (template-append template *vl-modelement-tmplsubsts*))


  (make-event
   `(progn
      (deftranssum vl-modelement
        :short "Recognizer for an arbitrary module element."

        :long "<p>It is sometimes useful to be able to deal with module elements of
arbitrary types.  For instance, we often use this in error messages, along with
@(see vl-context-p), to describe where expressions occur.  We also use it in
our @(see parser), where before module formation, the module elements are
initially kept in a big, mixed list.</p>"
        ,(project-over-modelement-types 'vl-__type__))

      (fty::deflist vl-modelementlist
        :elt-type vl-modelement-p
        :elementp-of-nil nil
        ///
        (local (in-theory (enable vl-modelementlist-p)))
        . ,(project-over-modelement-types
            '(defthm vl-modelementlist-p-when-vl-__type__list-p
               (implies (vl-__type__list-p x)
                        (vl-modelementlist-p x)))))

      (define vl-modelement->loc ((x vl-modelement-p))
        :prepwork ((local (in-theory (enable tag-reasoning))))
        :returns (loc vl-location-p :hints(("Goal" :in-theory (enable vl-modelement-fix
                                                                      vl-modelement-p
                                                                      tag-reasoning
                                                                      (tau-system)))))
        (let ((x (vl-modelement-fix x)))
          (case (tag x)
            . ,(project-over-modelement-types
                '(:vl-__type__ (vl-__type__->loc x)))))))))



(defxdoc vl-scopeid
  :parents (vl-scopestack)
  :short "Type of the name of a scope level -- either a string, in the common cases
          of modules, interfaces, packages, single generate constructs, etc., or
          an integer, for the special case of a generate block produced by a for
          loop.")

(define vl-scopeid-p (x)
  :parents (vl-scopeid)
  :short "Recognizer for scope names."
  :returns bool
  (or (stringp x)
      (integerp x))
  ///

  (defthm vl-scopeid-compound-recognizer
    (equal (vl-scopeid-p x)
           (or (stringp x) (integerp x)))
    :rule-classes :compound-recognizer))

(define vl-scopeid-fix ((x vl-scopeid-p))
  :parents (vl-scopeid)
  :short "Fixing function for @(see vl-scopeid)s."
  :returns (name vl-scopeid-p)
  :inline t
  (mbe :logic (if (vl-scopeid-p x)
                  x
                "")
       :exec x)
  ///
  (defthm vl-scopeid-fix-when-vl-scopeid-p
    (implies (vl-scopeid-p x)
             (equal (vl-scopeid-fix x) x))))

(defsection vl-scopeid-equiv
  :parents (vl-scopeid)
  :short "Equivalence relation for @(see vl-scopeid)s."
  (deffixtype vl-scopeid
    :pred vl-scopeid-p
    :fix vl-scopeid-fix
    :equiv vl-scopeid-equiv
    :define t
    :forward t))

(defoption vl-maybe-scopeid vl-scopeid
  ///
  (defthm vl-maybe-scopeid-compound-recognizer
    (equal (vl-maybe-scopeid-p x)
           (or (not x) (stringp x) (integerp x)))
    :hints(("Goal" :in-theory (enable vl-maybe-scopeid-p
                                      vl-scopeid-p)))
    :rule-classes :compound-recognizer))



(defsection generates
  :parents nil

  (local (in-theory (disable acl2::o<-of-two-nats-measure o< o<-when-natps nfix)))
  (deftypes vl-genelement

    ;; NOTE: According to the SystemVerilog spec, generate/endgenerate just
    ;; defines a textual region, which makes "no semantic difference" in the
    ;; module.

    (deftagsum vl-genelement
      :short "Representation of an arbitrary module element or generate construct."
      :measure (two-nats-measure (acl2-count x) 1)

      (:vl-genbase
       :base-name vl-genbase
       :layout :tree
       :short "Wrapper for promoting basic module items into genelements."
       ((item vl-modelement))
       :long "<p>This is a trivial wrapper that allows any kind of module
              element (variables, assignments, module instances, etc.) to be
              used within a @('generate') construct.</p>")

      (:vl-genbegin
       :base-name vl-genbegin
       :short "Wrapper for promoting begin/end generate blocks into genelements."
       ((block vl-genblock-p))
       :long "<p>This is a trivial wrapper for converting a @(see vl-genblock),
              which represents a @('begin/end') generate construct, into a
              standalone @('vl-genelement').</p>

              <p>Having this kind of wrapper is a bit ugly.  It might be nicer
              looking to just have the name, location, and genelements for the
              block right here, instead of relegating them to a @(see
              vl-genblock).</p>

              <p>But having a wrapper gives us a really nice property: it
              allows the ``implicit'' begin/end blocks for every kind of
              generate construct to be treated in a completely uniform way.
              That is: go look at @(see vl-gencase), @(see vl-genif), etc.
              You'll see that all of our branches are represented as explicit
              @(see vl-genblock)s.  This is really handy when it comes to
              scoping.  We can ensure that all of these blocks have a name, and
              we can deal with begin/end blocks and if/case blocks in a uniform
              way in @(see scopestack)s.  (We still have to handle generate
              arrays separately, but there's no getting around that.)</p>

              <p>We wouldn't be able to have this kind of uniformity if a
              begin/end block just had its elements right here, because we
              can't easily require that, e.g., a @(see vl-genif)'s @('then')
              branch is @(see vl-genelement) of subtype
              @(':vl-genbegin').</p>")

      (:vl-genif
       :base-name vl-genif
       :layout :tree
       :short "An @('if') or @('if/else') generate construct."
       ((test vl-expr-p    "Expression to test.")
        (then vl-genblock-p "The begin/end block for when @('test') is true.")
        (else vl-genblock-p "The begin/end block for when @('test') is false.
                             May be an empty block if there is no @('else') part.")
        (loc  vl-location-p "Where this @('if') came from in the Verilog source code."))
       :long "<p>These are mostly straightforward; note that each branch gets
              its own scope but that there are tricky scoping rules for nested
              if/else branches; see SystemVerilog-2012 Section 27.5 for
              details.</p>")

      (:vl-gencase
       :base-name vl-gencase
       :layout :tree
       :short "A case generate construct."
       ((test      vl-expr-p      "The expression to test against the cases, e.g.,
                                   @('mode') in @('case (mode) ...').")
        (cases     vl-gencaselist "The match expressions and corresponding blocks.")
        (default   vl-genblock-p  "The default block. May be an empty @(see vl-genblock).")
        (loc       vl-location-p  "Where this @('case') came from in the Verilog source code.")))

      (:vl-genloop
       :base-name vl-genloop
       :layout :tree
       :short "A loop generate construct, before elaboration."
       ((var        stringp       "Iterator variable for this generate loop.")
        (genvarp    booleanp      "Is the variable declared using the genvar keyword, locally")
        (initval    vl-expr-p     "Initial value of the variable.")
        (continue   vl-expr-p     "Continue the loop until this expression is false.")
        (nextval    vl-expr-p     "Next value expression for the variable.")
        (body       vl-genblock-p "Body of the loop.")
        (loc        vl-location-p "Where this loop came from in the Verilog source code."))
       :long "<p>This structure captures something like the ``just parsed''
              form of a generate loop.  Elaboration should convert these into
              the more regular @(see vl-genarray) form.</p>")

      (:vl-genarray
       :base-name vl-genarray
       :layout :tree
       :short "A loop generate construct, after elaboration."
       ((name      maybe-stringp     "Name of the block array, if named.")
        (var       stringp           "Iterator variable name.")
        (genvarp   booleanp          "Was the variable declared using the genvar keyword, locally")
        (blocks    vl-genblocklist-p "Blocks produced by the loop")
        (loc       vl-location-p     "Where the loop came from in the Verilog source code."))
       :long "<p>This is a post-elaboration representation of a generate for
              loop, where the loop itself is gone and we instead have something
              like a list of begin/end blocks for each value that @('var') took
              on during the loop's execution.</p>

              <p>This representation may seem weird but notice that things like
              the sizes of wires can change from iteration to iteration if they
              depend on the loop variable, and similarly other things within
              the loop like @('if/else') generate blocks may depend on the loop
              variable and so may need to differ from iteration to iteration.
              To support these kinds of things, we really do want a
              representation where each block can be separated from the others
              and processed independently.</p>"))

    (defprod vl-genblock
      :layout :tree
      :short "Representation of an explicit or implicit @('begin/end') generate block."
      ((name        vl-maybe-scopeid-p  "The name of the block, if named.")
       (elems       vl-genelementlist-p "Elements within the block.")
       (condnestp   booleanp            "Reflects special case where the block
                                         doesn't create a scope, in case of nested
                                         conditionals.  See SystemVerilog-2012
                                         27.5: a block within a conditional construct
                                         that has only one element, and is not
                                         surrounded by begin/end keywords, is not
                                         treated as a separate scope.")
       (loc       vl-location         "Location of the block in the Verilog source code."))
      :measure (two-nats-measure (acl2-count x) 3)
      :long "<p>See the documentation for @(see vl-genbegin).  A
             @('vl-genblock') may represent an explicit @('begin/end')
             construct, or might instead be something like the @('true') or
             @('false') branch of an @('if/else') generate construct,
             etc.</p>")

    (fty::deflist vl-genelementlist
      :elt-type vl-genelement
      :true-listp t
      :elementp-of-nil nil
      :measure (two-nats-measure (acl2-count x) 1))

    (fty::defalist vl-gencaselist
      :key-type vl-exprlist
      :val-type vl-genblock
      :true-listp t
      :measure (two-nats-measure (acl2-count x) 10))

    (fty::deflist vl-genblocklist
      :elt-type vl-genblock
      :true-listp t
      :elementp-of-nil nil
      :measure (two-nats-measure (acl2-count x) 1))

    :enable-rules (acl2::o-p-of-two-nats-measure
                   acl2::o<-of-two-nats-measure
                   acl2-count-of-car
                   acl2-count-of-cdr
                   acl2-count-of-cdr-same-fc
                   cons-equal
                   ;; default-car  default-cdr
                   nfix
                   ))

  (defthm vl-genelement-fix-type
    (consp (vl-genelement-fix x))
    :rule-classes :type-prescription
    :hints(("Goal" :expand ((:with vl-genelement-fix (vl-genelement-fix x))))))

  (define vl-genelement->loc ((x vl-genelement-p))
    :returns (loc vl-location-p)
    (vl-genelement-case x
      (:vl-genbase  (vl-modelement->loc x.item))
      (:vl-genbegin (vl-genblock->loc x.block))
      (:vl-genloop  x.loc)
      (:vl-genif    x.loc)
      (:vl-gencase  x.loc)
      (:vl-genarray x.loc))))


(define vl-modelementlist->genelements ((x vl-modelementlist-p))
  :returns (xx vl-genelementlist-p)
  (if (atom x)
      nil
    (cons (make-vl-genbase :item (car x))
          (vl-modelementlist->genelements (cdr x)))))

(defsection ctxelements
  :parents nil

  (deftranssum vl-ctxelement
    ;; Add any tagged product that can be written with ~a and has a loc field.
    (vl-portdecl
     vl-assign
     vl-alias
     vl-vardecl
     vl-paramdecl
     vl-fundecl
     vl-taskdecl
     vl-modinst
     vl-gateinst
     vl-always
     vl-initial
     vl-final
     vl-typedef
     vl-import
     vl-fwdtypedef
     vl-modport
     vl-interfaceport
     vl-regularport
     vl-genelement
     vl-assertion
     vl-cassertion
     vl-property
     vl-sequence
     vl-dpiimport
     vl-dpiexport
     vl-bind
     vl-class
     vl-covergroup
     vl-elabtask))

  (local (defthm vl-genelement-kind-by-tag-when-vl-ctxelement-p
           (implies (and (vl-ctxelement-p x)
                         (vl-genelement-p x))
                    (equal (vl-genelement-kind x)
                           (tag x)))
           :hints(("Goal" :in-theory (enable vl-ctxelement-p
                                             vl-genelement-p
                                             vl-genelement-kind
                                             tag)))))

  (defthmd tag-when-vl-ctxelement-p
    (implies (vl-ctxelement-p x)
             (or (equal (tag x) :vl-regularport)
                 (equal (tag x) :vl-interfaceport)
                 (equal (tag x) :vl-portdecl)
                 (equal (tag x) :vl-assign)
                 (equal (tag x) :vl-alias)
                 (equal (tag x) :vl-vardecl)
                 (equal (tag x) :vl-paramdecl)
                 (equal (tag x) :vl-fundecl)
                 (equal (tag x) :vl-taskdecl)
                 (equal (tag x) :vl-modinst)
                 (equal (tag x) :vl-gateinst)
                 (equal (tag x) :vl-always)
                 (equal (tag x) :vl-initial)
                 (equal (tag x) :vl-final)
                 (equal (tag x) :vl-typedef)
                 (equal (tag x) :vl-fwdtypedef)
                 (equal (tag x) :vl-assertion)
                 (equal (tag x) :vl-cassertion)
                 (equal (tag x) :vl-property)
                 (equal (tag x) :vl-sequence)
                 (equal (tag x) :vl-import)
                 (equal (tag x) :vl-genbegin)
                 (equal (tag x) :vl-genarray)
                 (equal (tag x) :vl-genbase)
                 (equal (tag x) :vl-genif)
                 (equal (tag x) :vl-gencase)
                 (equal (tag x) :vl-genloop)
                 (equal (tag x) :vl-modport)
                 (equal (tag x) :vl-dpiimport)
                 (equal (tag x) :vl-dpiexport)
                 (equal (tag x) :vl-bind)
                 (equal (tag x) :vl-class)
                 (equal (tag x) :vl-covergroup)
                 (equal (tag x) :vl-elabtask)
                 ))
    :rule-classes (:forward-chaining)
    :hints(("Goal" :in-theory (enable tag-reasoning vl-ctxelement-p))))

  (add-to-ruleset tag-reasoning '(tag-when-vl-ctxelement-p))

  (define vl-ctxelement->loc ((x vl-ctxelement-p))
    :returns (loc vl-location-p)
    :prepwork ((local (in-theory (enable tag-reasoning
                                         ;; bozo probably don't need this if we add thms about
                                         ;; tag of vl-ctxelement-fix.  or maybe we want to just
                                         ;; have it known that a fixing function produces a
                                         ;; well-typed object, as a forward chaining rule?
                                         vl-ctxelement-fix))))
    (let ((x (vl-ctxelement-fix X)))
      (case (tag x)
        (:vl-portdecl (vl-portdecl->loc x))
        (:vl-assign (vl-assign->loc x))
        (:vl-alias (vl-alias->loc x))
        (:vl-vardecl (vl-vardecl->loc x))
        (:vl-paramdecl (vl-paramdecl->loc x))
        (:vl-fundecl (vl-fundecl->loc x))
        (:vl-taskdecl (vl-taskdecl->loc x))
        (:vl-modinst (vl-modinst->loc x))
        (:vl-gateinst (vl-gateinst->loc x))
        (:vl-always (vl-always->loc x))
        (:vl-initial (vl-initial->loc x))
        (:vl-final (vl-final->loc x))
        (:vl-typedef (vl-typedef->loc x))
        (:vl-import (vl-import->loc x))
        (:vl-fwdtypedef (vl-fwdtypedef->loc x))
        (:vl-modport (vl-modport->loc x))
        (:vl-interfaceport (vl-interfaceport->loc x))
        (:vl-regularport (vl-regularport->loc x))
        (:vl-genbase (vl-modelement->loc (vl-genbase->item x)))
        (:vl-genloop (vl-genloop->loc x))
        (:vl-genif   (vl-genif->loc x))
        (:vl-gencase (vl-gencase->loc x))
        (:vl-genbegin (vl-genblock->loc (vl-genbegin->block x)))
        (:vl-genarray (vl-genarray->loc x))
        (:vl-assertion (vl-assertion->loc x))
        (:vl-cassertion (vl-cassertion->loc x))
        (:vl-property (vl-property->loc x))
        (:vl-sequence (vl-sequence->loc x))
        (:vl-dpiimport (vl-dpiimport->loc x))
        (:vl-dpiexport (vl-dpiexport->loc x))
        (:vl-bind (vl-bind->loc x))
        (:vl-class (vl-class->loc x))
        (:vl-covergroup (vl-covergroup->loc x))
        (:vl-elabtask (vl-elabtask->loc x))))))

(defprod vl-context1
  :short "Description of where an expression occurs."
  :tag :vl-context
  :layout :tree
  ((mod  stringp :rule-classes :type-prescription
         "The module where this module element was taken from.")
   (elem vl-ctxelement-p
         "Some element from the module.")))

(defxdoc vl-context
  :short "A context for @(see warnings)."

  :long "<p>Contexts are usually @(see vl-context1)s.  However, for more
generality, you can use any arbitrary object as a context.  The proper way to
do this is to wrap it using @('(vl-context x)').</p>

@(def vl-context)
@(def make-vl-context)")

(define vl-context-p ((x))
  :parents (vl-context)
  :prepwork ((set-tau-auto-mode nil))
  (declare (ignorable x))
  t
  ///
  (defthm vl-context-p-type
    (booleanp (vl-context-p x))
    :rule-classes :type-prescription)
  (in-theory (disable (:t vl-context-p)))

  (defthm vl-context-p-when-vl-ctxelement-p
    (implies (vl-ctxelement-p x)
             (vl-context-p x)))

  (defthm vl-context-p-when-vl-context1-p
    (implies (vl-context1-p x)
             (vl-context-p x))))

(define vl-context-fix ((x))
  :prepwork ((set-tau-auto-mode nil))
  :parents (vl-context)
  x
  ///
  (local (in-theory (enable vl-context-p)))
  (defthm vl-context-p-of-vl-context-fix
    (vl-context-p (vl-context-fix x)))
  (defthm vl-context-fix-when-vl-context-p
    (implies (vl-context-p x)
             (equal (vl-context-fix x) x)))

  (fty::deffixtype vl-context
    :pred vl-context-p
    :fix vl-context-fix
    :equiv vl-context-equiv
    :define t))

(defmacro make-vl-context (&rest args)
  `(vl-context (make-vl-context1 . ,args)))

(defmacro vl-context (x)
  `(vl-context-fix ,x))


(defprod vl-ansi-portdecl
  :short "Temporary representation for port declarations."
  :long "<p>Some constraints on the presence/absence of some of these fields:</p>
<ul>
<li>typename should imply no type, signedness, or pdims</li>
<li>type should imply no signedness or pdims.</li>
<li>modport should imply typename and not varp, dir, or nettype</li>
</ul>

<p>The reason we have these: Parsing ports is fairly ambiguous and there's a
lot that needs to be fleshed out after we have a fuller picture of the design.
The worst ambiguity is that there's no syntactic difference in an ANSI portlist
between an interfaceport of interface foo, and a regular port of type foo (if
it doesn't have an explicit direction, nettype, or @('var') keyword).  The only
way to resolve these is to determine whether the interface/type name actually
refers to an interface or a type.</p>

<p>Another issue, with non-ANSI ports, is that a port declaration may have a
corresponding net/variable declaration that contains different information
about its type and nettype.  We resolve this later as well, cross-propagating
the type information between the variable and port declarations.</p>"
  :tag :vl-ansi-portdecl
  ((name       stringp
               "Name of the port")
   (loc        vl-location-p)
   (dir vl-maybe-direction-p
        "Direction, if an explicit keyword was present.")
   (typename maybe-stringp
             "The name of the type, if it was just a simple ID, or the name of
              the interface, to be determined.")
   (type    vl-maybe-datatype-p
            "The datatype, if it was explicit")
   (pdims      vl-dimensionlist-p
               "Dimensions, if given and no explicit datatype")
   (udims      vl-dimensionlist-p
               "Dimensions from after the name")
   (nettype vl-maybe-nettypename-p
            "Nettype, if present")
   (varp    booleanp
            "Indicates whether the var keyword was present.")
   (modport maybe-stringp
            "Modport of the interface, if specified")
   (signedness vl-maybe-exprsign-p
               "The signedness, if given, and if there is no explicit datatype)")
   (atts vl-atts-p)))

(fty::deflist vl-ansi-portdecllist :elt-type vl-ansi-portdecl)


(defprod vl-parse-temps
  :short "Temporary stuff recorded by parsing that's used to generate real module
          items by the first annotate transforms, and should be ignored after
          that."
  ((ansi-p booleanp
           "Says whether we parsed this module in the ANSI or non-ANSI style.")
   (ansi-ports vl-ansi-portdecllist-p
               "Temporary form of the ports from parsing for ANSI modules. These
                immediately get processed into the real ports by the port-resolve
                transform and should be ignored thereafter.")
   (paramports vl-paramdecllist-p
               "List of parameter declarations that occur in the parameter port
                list, rather than in the body of the module.  These must be kept
                separate in the ANSI case because the ports may refer to parameters,
                and we therefore need to preserve the textual order so that shadowcheck
                doesn't fail.")
   (loaditems vl-genelementlist-p
              "See @(see make-implicit-wires).  This is a temporary container to
               hold the module elements, in program order, until the rest of the
               design has been loaded.  This field is \"owned\" by the @('make-implicit-wires')
               transform.  You should never access it or modify it in any other
               code.")))

(defoption vl-maybe-parse-temps vl-parse-temps)


(defprod vl-timeliteral
  :short "Representation of a single @('time_literal') token."
  :tag :vl-timeliteral
  :layout :fulltree
  ((quantity stringp :rule-classes :type-prescription
             "An ACL2 string with the amount.  In practice, the amount should
              match either @('unsigned_number') or @('fixed_point_number'),
              e.g., @('\"3\"') or @('\"45.617\"').  We don't try to process
              this further because (1) we don't expect it to matter for much,
              and (2) ACL2 doesn't really support fixed point numbers.")
   (units    vl-timeunit-p
             "The kind of time unit this is, e.g., seconds, milliseconds,
              microseconds, ..."))
  :long "<p>This is used in @(see vl-timeunitdecl)s and @(see
         vl-timeprecisiondecl)s.</p>")

(defoption vl-maybe-timeliteral vl-timeliteral)

(defprod vl-timeunitdecl
  :short "Representation of a 'timeunit' declaration."
  :tag :vl-timeunitdecl
  :layout :fulltree
  ((numerator   vl-timeliteral-p)
   (denominator vl-maybe-timeliteral-p)
   (loc         vl-location-p)))

(defoption vl-maybe-timeunitdecl vl-timeunitdecl)

(defprod vl-timeprecisiondecl
  :short "Representation of a 'timeprecision' declaration."
  :tag :vl-timeprecisiondecl
  :layout :fulltree
  ((precision vl-timeliteral-p)
   (loc       vl-location-p)))

(defoption vl-maybe-timeprecisiondecl vl-timeprecisiondecl)

(defprod vl-module
  :short "Representation of a single module."
  :tag :vl-module
  ;; BOZO it would be nice to use :tree, but we'll need to patch up modname-sets.
  :layout :fulltree

  ((name       stringp
               :rule-classes :type-prescription
               "The name of this module as a string.  The name is used to
                instantiate this module, so generally we require that modules
                in our list have unique names.  A module's name is initially
                set when it is parsed, but it may not remain fixed throughout
                simplification.  For instance, during @(see unparameterization)
                a module named @('adder') might become @('adder$size=12').")

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

   (ports      vl-portlist-p
               "The module's ports list, i.e., @('a'), @('b'), and @('c') in
                @('module mod(a,b,c);').")

   (portdecls  vl-portdecllist-p
               "The input, output, and inout declarations for this module,
                e.g., @('input [3:0] a;').")

   (vardecls   vl-vardecllist-p
               "Wire and variable declarations like @('wire [3:0] w'), @('tri v'),
                @('reg [3:0] r;'), @('integer i;'), @('real foo;'), and so forth.")

   (modinsts   vl-modinstlist-p
               "Instances of modules and user-defined primitives, e.g.,
                @('adder my_adder1 (...);').")

   (assigns    vl-assignlist-p
               "Top-level continuous assignments like @('assign lhs = rhs;').")

   (gateinsts  vl-gateinstlist-p
               "Instances of primitive gates, e.g., @('and (o, a, b);').")

   (paramdecls vl-paramdecllist-p
               "The parameter declarations for this module, e.g., @('parameter
                width = 1;').")

   (imports    vl-importlist-p
               "Package import statements for this module, like @('import
                foo::*').")


   (atts       vl-atts-p
               "Any attributes associated with this top-level module.")

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

   ;; BOZO possibly add lifetime declarations, but the spec seems pretty vague
   ;; about what they mean.  The only thing I see about them is that they are
   ;; the "default lifetime (static or automatic) of subroutines defined within
   ;; the module."  Which doesn't seem like a very good idea anyway...

   (timeunit   vl-maybe-timeunitdecl-p
               "The @('timeunits') for this module, if specified.")

   (timeprecision vl-maybe-timeprecisiondecl-p
                  "The @('timeprecision') for this module, if specified.")

   (alwayses   vl-alwayslist-p
               "Always blocks like @('always @(posedge clk) ...').")

   (genvars    vl-genvarlist-p
               "Genvar declarations.")

   (generates  vl-genelementlist-p
               "Generate blocks including generate regions and for/if/case blocks.")

   (fundecls   vl-fundecllist-p
               "Function declarations like @('function f ...').")

   (taskdecls  vl-taskdecllist-p
               "Task declarations, e.g., @('task foo ...').")

   (typedefs   vl-typedeflist-p
               "Type declarations such as @('typedef logic [3:0] nibble;').")

   (initials   vl-initiallist-p
               "Initial blocks like @('initial begin ...').")

   (finals     vl-finallist-p
               "Final statements like @('final begin ...').")

   (aliases    vl-aliaslist-p
               "Wire aliases, @('alias lhs = rhs;')")

   (assertions  vl-assertionlist-p
                "Immediate (including deferred immediate) assertions.")

   (cassertions vl-cassertionlist-p
                "Concurrent assertions for the module.")

   (properties  vl-propertylist-p
                "Property declarations for the module.")

   (sequences   vl-sequencelist-p
                "Sequence declarations for the module.")

   (clkdecls    vl-clkdecllist-p
                "(Non-global) clocking blocks for the module.")

   (gclkdecls   vl-gclkdecllist-p
                "Global clocking for this module, if any.  Note that
                 SystemVerilog only allows a single global clocking, but we
                 allow a list here because it makes things work much more
                 smoothly with modelements.")

   (defaultdisables vl-defaultdisablelist-p
                    "Any @('default disable ...') constructs for the module.")

   (dpiimports  vl-dpiimportlist-p
                "DPI imports for this module.")

   (dpiexports  vl-dpiexportlist-p
                "DPI exports for this module.")

   (binds       vl-bindlist-p
                "Bind directives in this module.")

   (classes     vl-classlist-p
                "Classes declared within this module.")

   (covergroups vl-covergrouplist-p
                "Covergroups declared within this module.")

   (elabtasks   vl-elabtasklist-p
                "Elaboration system tasks like @('$fatal').")

   (parse-temps  vl-maybe-parse-temps-p
                 "Temporary stuff recorded by the parser, used to generate real
                  module contents.")

   (params     "Any @('defparam') statements for this module.  BOZO these are
                bad form anyway, but eventually we should provide better
                support for them and proper structures."))
  :extra-binder-names (hands-offp
                       ifports
                       modnamespace))

(fty::deflist vl-modulelist
  :elt-type vl-module-p
  :elementp-of-nil nil)

(define vl-module->hands-offp ((x vl-module-p))
  :returns hands-offp
  :parents (vl-module-p)
  :short "Attribute that says a module should not be transformed."

  :long "<p>We use the ordinary <see topic='@(url vl-atts-p)'>attribute</see>
@('VL_HANDS_OFF') to say that a module should not be changed by @(see
transforms).</p>

<p>This is probably mostly outdated.  It was originally intended for use in
@(see vl2014::primitives).  The Verilog definitions of these modules sometimes
make use of fancy Verilog constructs.  Normally our transforms would try to
remove these constructs, replacing them with instances of primitives.  This can
lead to funny sorts of problems if we try to transform the primitives
themselves.</p>

<p>For instance, consider the @(see vl2014::*vl-1-bit-delay-1*) module.  This
module has a delayed assignment, @('assign #1 out = in').  If we hit this
module with the @(see vl2014::delayredux) transform, we'll try to replace the
delay with an explicit instance of @('VL_1_BIT_DELAY_1').  But that's crazy:
now the module is trying to instantiate itself!</p>

<p>Similar issues can arise from trying to replace the @('always') statements
in a primitive flop/latch with instances of flop/latch primitives, etc.  So as
a general rule, we mark the primitives with @('VL_HANDS_OFF') and code our
transforms to not modules with this attribute.</p>"
  ;; :prepwork ((local (defthm alistp-when-atts-p
  ;;                     (implies (vl-atts-p x)
  ;;                              (alistp x))
  ;;                     :hints(("Goal" :in-theory (enable alistp))))))
  :inline t
  (consp (hons-assoc-equal "VL_HANDS_OFF" (vl-module->atts x))))

(define vl-module->ifports
  :short "Collect just the interface ports for a module."
  ((x vl-module-p))
  :returns (ports (vl-interfaceportlist-p ports))
  (vl-collect-interface-ports (vl-module->ports x))
  ///
  (local (defthm vl-regularportlist-p-when-no-interface-ports
           (implies (and (not (vl-collect-interface-ports x))
                         (vl-portlist-p x))
                    (vl-regularportlist-p x))
           :hints(("Goal"
                   :induct (len x)
                   :in-theory (enable tag-reasoning)))))

  (defthm vl-regularportlist-p-when-no-module->ifports
    (implies (not (vl-module->ifports x))
             (vl-regularportlist-p (vl-module->ports x)))
    :hints(("Goal" :in-theory (enable vl-module->ifports)))))



(defprojection vl-modulelist->names ((x vl-modulelist-p))
  :returns (names string-listp)
  :parents (vl-modulelist-p)
  (vl-module->name x))

(defprojection vl-modulelist->paramdecls ((x vl-modulelist-p))
  :returns (paramdecl-lists vl-paramdecllist-list-p)
  :parents (vl-modulelist-p)
  (vl-module->paramdecls x))

(defmapappend vl-modulelist->modinsts (x)
  (vl-module->modinsts x)
  :parents (vl-modulelist-p)
  :guard (vl-modulelist-p x)
  :transform-true-list-p nil
  :rest ((defthm vl-modinstlist-p-of-vl-modulelist->modinsts
           (vl-modinstlist-p (vl-modulelist->modinsts x)))
         (deffixequiv vl-modulelist->modinsts :args ((x vl-modulelist-p)))))

(defoption vl-maybe-module vl-module-p
  :short "Recognizer for an @(see vl-module-p) or @('nil')."
  ///
  (defthm type-when-vl-maybe-module-p
    (implies (vl-maybe-module-p x)
             (or (not x)
                 (consp x)))
    :hints(("Goal" :in-theory (enable vl-maybe-module-p)))
    :rule-classes :compound-recognizer))


(defenum vl-udpsymbol-p
  (:vl-udp-0
   :vl-udp-1
   :vl-udp-x
   :vl-udp-?
   :vl-udp-b
   :vl-udp--
   :vl-udp-*
   :vl-udp-r
   :vl-udp-f
   :vl-udp-p
   :vl-udp-n)
  :short "Symbols that can occur in a UDP table"
  :long "<p>These are basically taken from Verilog-2005 Table 8-1.</p>

<ul>

<li>@(':vl-udp-0') &mdash; logic 0.</li>

<li>@(':vl-udp-1') &mdash; logic 1.</li>

<li>@(':vl-udp-x') &mdash; unknown.  Permitted in input/outputs of all UDPs and
current state of sequential UDPs.</li>

<li>@(':vl-udp-?') &mdash; iteration of 0, 1, and X.  Not permitted in outputs.</li>

<li>@(':vl-udp-b') &mdash; iteration of 0 and 1.  Permitted in inputs of all
udps and current state of sequential udps, not in outputs.</li>

<li>@(':vl-udp--') &mdash; no change.  Permitted only in the output field of a
sequential UDP.</li>

<li>@(':vl-udp-*') &mdash; any value change on input, same as @('(??)').</li>

<li>@(':vl-udp-r') &mdash; rising edge on input, same as @('(01)').</li>

<li>@(':vl-udp-f') &mdash; falling edge on input, same as @('(10)').</li>

<li>@(':vl-udp-p') &mdash; any potential positive edge on the input, iteration of
                           @('(01)'), @('(0x)'), @('(x1)').</li>

<li>@(':vl-udp-n') &mdash; any potential negative edge on the input, iteration of
                           @('(10)'), @('(1x)'), @('(x0)').</li>

</ul>")

(defoption vl-maybe-udpsymbol-p
  vl-udpsymbol-p)

(defprod vl-udpedge
  :tag :vl-udplevel
  :layout :tree
  :short "Representation of an explicit edge that can occur in a UDP table,
e.g., @('(01)') or @('(1?)')."
  ((prev vl-udpsymbol-p)
   (next vl-udpsymbol-p)))

(define vl-udpentry-p (x)
  :short "Representation of any entry in a UDP table."
  :returns bool
  (mbe :logic
       (or (vl-udpsymbol-p x)
           (vl-udpedge-p x))
       :exec
       (if (consp x)
           (vl-udpedge-p x)
         (vl-udpsymbol-p x)))
  ///
  (defthm vl-udpentry-p-when-vl-udpsymbol-p
    (implies (vl-udpsymbol-p x)
             (vl-udpentry-p x)))
  (defthm vl-udpentry-p-when-vl-udpedge-p
    (implies (vl-udpedge-p x)
             (vl-udpentry-p x))))

(define vl-udpentry-fix (x)
  :parents (vl-udpentry-p)
  :returns (entry vl-udpentry-p)
  :inline t
  (if (vl-udpentry-p x)
      x
    :vl-udp-0)
  ///
  (defthm vl-udpentry-fix-when-vl-udpentry-p
    (implies (vl-udpentry-p x)
             (equal (vl-udpentry-fix x)
                    x))))

(deffixtype vl-udpentry
  :pred vl-udpentry-p
  :fix vl-udpentry-fix
  :equiv vl-udpentry-equiv
  :define t
  :forward t)

(fty::deflist vl-udpentrylist
  :elt-type vl-udpentry-p
  :elementp-of-nil nil)

(defprod vl-udpline
  :short "Representation of one line of a UDP table."
  :tag    :vl-udpline
  :layout :tree
  ((inputs  vl-udpentrylist-p
            "The input entries, i.e., whatever occurs before the first colon.")
   (output  vl-udpsymbol-p
            "The output value.")
   (current vl-maybe-udpsymbol-p
            "For sequential UDPs only: the current state.")))

(fty::deflist vl-udptable
  :elt-type vl-udpline-p
  :elementp-of-nil nil)

(defprod vl-udp
  :short "Representation of a user defined @('primitive')."
  :tag :vl-udp
  :layout :tree

  ((name        stringp :rule-classes :type-prescription
                "The name of this udp as a string.")

   (output      vl-portdecl-p
                "Declaration of the output port, which always comes first.")

   (inputs      vl-portdecllist-p
                "Port declarations for the input ports, in order.")

   (sequentialp booleanp
                "True when this is a sequential (instead of combinational) UDP.")

   (table       vl-udptable-p
                "The UDP state table.")

   (initval     vl-maybe-expr-p
                "For sequential UDPs, the initial value for the register, if specified.")

   (warnings    vl-warninglist-p)
   (minloc      vl-location-p)
   (maxloc      vl-location-p)
   (atts        vl-atts-p)
   (comments    vl-commentmap-p)))

(fty::deflist vl-udplist
  :elt-type vl-udp-p
  :elementp-of-nil nil)

(defprojection vl-udplist->names ((x vl-udplist-p))
  :parents (vl-udplist-p)
  :returns (names string-listp)
  (vl-udp->name x))


(defprod vl-config
  :short "Representation of a single @('config')."
  :tag :vl-config
  :layout :tree
  ((name stringp
         :rule-classes :type-prescription
         "The name of this config as a string.")
   ;; ...
   (warnings vl-warninglist-p)
   (minloc   vl-location-p)
   (maxloc   vl-location-p)
   (atts     vl-atts-p)
   (comments vl-commentmap-p))
  :long "BOZO incomplete stub -- we don't really support configs yet.")

(fty::deflist vl-configlist :elt-type vl-config-p
  :elementp-of-nil nil)

(defprojection vl-configlist->names ((x vl-configlist-p))
  :parents (vl-configlist-p)
  :returns (names string-listp)
  (vl-config->name x))


(defprod vl-package
  :short "Representation of a single @('package')."
  :tag :vl-package
  :layout :tree
  ((name stringp
         :rule-classes :type-prescription
         "The name of this package as a string.")
   (minloc     vl-location-p)
   (maxloc     vl-location-p)
   (paramdecls vl-paramdecllist-p)
   (typedefs   vl-typedeflist-p)
   (comments   vl-commentmap-p)
   (warnings   vl-warninglist-p)
   (imports    vl-importlist-p)
   (fundecls   vl-fundecllist-p)
   (taskdecls  vl-taskdecllist-p)
   (vardecls   vl-vardecllist-p)
   (lifetime   vl-lifetime-p)
   (dpiimports vl-dpiimportlist-p)
   (dpiexports vl-dpiexportlist-p)
   (classes    vl-classlist-p)
   (atts       vl-atts-p))
  :long "<p>BOZO we haven't finished out all the things that can go inside of
packages.  Eventually there will be new fields here.</p>")

(fty::deflist vl-packagelist
  :elt-type vl-package-p
  :elementp-of-nil nil)

(defprojection vl-packagelist->names ((x vl-packagelist-p))
  :parents (vl-packagelist-p)
  :returns (names string-listp)
  (vl-package->name x))


(defprod vl-interface
  :short "Representation of a single @('interface')."
  :tag :vl-interface
  :layout :tree
  ((name stringp
         :rule-classes :type-prescription
         "The name of this interface as a string.")

   ;; Still various missing things, e.g., program_instantiation,
   ;; bind_directive, let statements, elaboration system tasks, timeunit stuff,
   ;; clocking stuff, default disable stuff...

   (imports     vl-importlist-p)
   (ports       vl-portlist-p)       ;; allowed via interface_*_header
   (portdecls   vl-portdecllist-p)   ;; allowed via headers or directly via interface_item

   (modports    vl-modportlist-p)    ;; allowed via interface_or_generate_item -> modport_declaration
   ;; interface_or_generate_item ::= module_common_item
   ;;                                ::= module_or_generate_item_declaration
   ;;                                    ::= package_or_generate_item_declaration

   (vardecls    vl-vardecllist-p)    ;; allowed via package_or_generate_item
   (paramdecls  vl-paramdecllist-p)  ;; allowed via package_or_generate_item
   (fundecls    vl-fundecllist-p)    ;; allowed via package_or_generate_item
   (taskdecls   vl-taskdecllist-p)   ;; allowed via package_or_generate_item
   (typedefs    vl-typedeflist-p)    ;; allowed via package_or_generate_item (data_declaration)
   (dpiimports  vl-dpiimportlist-p)  ;; allowed via package_or_generate_item
   (dpiexports  vl-dpiexportlist-p)  ;; allowed via package_or_generate_item
   (properties  vl-propertylist-p)   ;; allowed via package_or_generate_item (assertion_item_declaration)
   (sequences   vl-sequencelist-p)   ;; allowed via package_or_generate_item (assertion_item_declaration)
   (clkdecls    vl-clkdecllist-p)
   (gclkdecls   vl-gclkdecllist-p)
   (defaultdisables vl-defaultdisablelist-p)
   (binds       vl-bindlist-p)
   (classes     vl-classlist-p)
   ;; can interfaces have covergroups?? (covergroups vl-covergrouplist-p)
   (elabtasks   vl-elabtasklist-p)

   ;; interface_or_generate_item ::= module_common_item
   (modinsts    vl-modinstlist-p     ;; allowed via module_common_item (interface_instantiation)
                "Note: interfaces are not allowed to have submodule instances
                 (SystemVerilog-2012 section 25.3, page 713).  However, they
                 are allowed to have interface instances.  We check in @(see
                 basicsanity) that modinsts within each interface do indeed
                 refer to interfaces.")

   (assigns     vl-assignlist-p)     ;; allowed via module_common_item (continuous_assign)
   (aliases     vl-aliaslist-p)      ;; allowed via module_common_item (net_alias)
   (assertions  vl-assertionlist-p)  ;; allowed via module_common_item (assertion_item)
   (cassertions vl-cassertionlist-p) ;; allowed via module_common_item (assertion_item)
   (alwayses    vl-alwayslist-p)     ;; allowed via module_common_item (always_construct)
   (initials    vl-initiallist-p)    ;; allowed via module_common_item (ijnitial_construct)
   (finals      vl-finallist-p)      ;; allowed via module_common_item (final_construct)
   (generates   vl-genelementlist-p) ;; allowed via module_common_item (loop_generate, conditional_generate, ...)
   (genvars     vl-genvarlist-p)     ;; allowed via module_or_generate_item_declaration (genvar_declaration)

   (warnings    vl-warninglist-p)
   (minloc      vl-location-p)
   (maxloc      vl-location-p)
   (atts        vl-atts-p)
   (origname    stringp :rule-classes :type-prescription)
   (comments    vl-commentmap-p)

   (parse-temps  vl-maybe-parse-temps-p
                 "Temporary stuff recorded by the parser, used to generate real
                  interface contents."))

  :extra-binder-names (ifports))

(define vl-interface->ifports
  :short "Collect just the interface ports for a interface."
  ((x vl-interface-p))
  :returns (ports (vl-interfaceportlist-p ports))
  (vl-collect-interface-ports (vl-interface->ports x))
  ///
  (local (defthm vl-regularportlist-p-when-no-interface-ports
           (implies (and (not (vl-collect-interface-ports x))
                         (vl-portlist-p x))
                    (vl-regularportlist-p x))
           :hints(("Goal"
                   :induct (len x)
                   :in-theory (enable tag-reasoning)))))

  (defthm vl-regularportlist-p-when-no-interface->ifports
    (implies (not (vl-interface->ifports x))
             (vl-regularportlist-p (vl-interface->ports x)))
    :hints(("Goal" :in-theory (enable vl-interface->ifports)))))

(fty::deflist vl-interfacelist
  :elt-type vl-interface-p
  :elementp-of-nil nil)

(defprojection vl-interfacelist->names ((x vl-interfacelist-p))
  :parents (vl-interfacelist-p)
  :returns (names string-listp)
  (vl-interface->name x))



(defprod vl-program
  :short "Representation of a single @('program')."
  :tag :vl-program
  :layout :tree
  ((name stringp
         :rule-classes :type-prescription
         "The name of this program as a string.")
   ;; ...
   (warnings vl-warninglist-p)
   (minloc   vl-location-p)
   (maxloc   vl-location-p)
   (atts     vl-atts-p)
   (comments vl-commentmap-p))
  :long "BOZO incomplete stub -- we don't really support programs yet.")

(fty::deflist vl-programlist :elt-type vl-program-p
  :elementp-of-nil nil)

(defprojection vl-programlist->names ((x vl-programlist-p))
  :parents (vl-programlist-p)
  :returns (names string-listp)
  (vl-program->name x))


(defprod vl-design
  :short "Top level representation of all modules, interfaces, programs, etc.,
resulting from parsing some Verilog source code."
  :tag :vl-design
  :layout :tree
  ((version    vl-syntaxversion-p  "Version of VL syntax being used." :default *vl-current-syntax-version*)
   (mods       vl-modulelist-p     "List of all modules.")
   (udps       vl-udplist-p        "List of user defined primtives.")
   (interfaces vl-interfacelist-p  "List of interfaces.")
   (programs   vl-programlist-p    "List of all programs.")
   (classes    vl-classlist-p      "List of all classes.")
   (packages   vl-packagelist-p    "List of all packages.")
   (configs    vl-configlist-p     "List of configurations.")
   (vardecls   vl-vardecllist-p    "Top-level variable declarations.")
   (taskdecls  vl-taskdecllist-p   "Top-level task declarations.")
   (fundecls   vl-fundecllist-p    "Top-level function declarations.")
   (paramdecls vl-paramdecllist-p  "Top-level (local and non-local) parameter declarations.")
   (imports    vl-importlist-p     "Top-level package import statements.")
   (dpiimports vl-dpiimportlist-p  "Top-level DPI imports.")
   (dpiexports vl-dpiexportlist-p  "Top-level DPI exports.")
   (fwdtypes   vl-fwdtypedeflist-p "Forward (incomplete) typedefs.")
   (typedefs   vl-typedeflist-p    "Regular (non-forward, complete) typedefs.")
   (binds      vl-bindlist-p       "Top-level bind directives.")
   (properties vl-propertylist-p   "Top-level property declarations.")
   (sequences  vl-sequencelist-p   "Top-level sequence declarations.")
   ;; BOZO lots of things still missing
   (warnings   vl-warninglist-p    "So-called \"floating\" warnings.")
   (comments   vl-commentmap-p     "So-called \"floating\" comments.")
   (plusargs   string-listp        "List of plusargs (without + characters).")
   ))

(defoption vl-maybe-design vl-design-p)



