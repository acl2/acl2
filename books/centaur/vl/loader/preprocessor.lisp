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

; Amusingly, even though we preprocess before lexing, we need the lexer defined
; before we write the preprocessor.  This is because, e.g., when we process
; defines, we need to be able to identify string boundaries, escaped
; identifiers, etc.
(include-book "../util/cwtime")
(include-book "read-file")
(include-book "find-file")
(include-book "lexer")
(include-book "defines")
(local (include-book "../util/arithmetic"))


;; stupid speed hacking

(local (in-theory (disable vl-echarlist-p-when-subsetp-equal
                           nthcdr-of-increment
                           double-containment
                           default-car
                           default-cdr
                           acl2::subsetp-append1
                           vl-echar-p-when-member-equal-of-vl-echarlist-p)))


(local (defthm append-nil
         (equal (append nil y) y)))

(local (defthm true-listp-append-rw
         (equal (true-listp (append x y))
                (true-listp y))))

(local (in-theory (disable acl2-count-positive-when-consp
                           append-when-not-consp
                           append-of-cons
                           acl2::true-listp-append
                           (:type-prescription true-listp)
                           )))

(local (in-theory (disable ;ACL2-COUNT-OF-VL-READ-UNTIL-END-OF-DEFINE-WEAK
                           hons-assoc-equal
                           CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP
                           STRINGP-WHEN-MEMBER-EQUAL-IN-STRING-LISTP
                           STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP
                           STRING-LISTP-WHEN-MEMBER-EQUAL-OF-STRING-LIST-LISTP
                           SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP
                           TRUE-LISTP-WHEN-MEMBER-EQUAL-OF-TRUE-LIST-LISTP)))

(local (in-theory (disable VL-MATCHES-STRING-P-WHEN-ACL2-COUNT-ZERO)))


(defxdoc preprocessor
  :parents (loader)
  :short "Limited preprocessor for Verilog."

  :long "<p>First, a warning.  In general, the Verilog specification does not
cover how preprocessing is to be done in a very complete way.  We are left with
many subtle questions about how the preprocessor should behave, and to resolve
these questions we have sometimes just given test cases to Verilog-XL.  This is
not a very satisfying state of affairs.</p>

<h4>Supported Directives</h4>

<p>Our preprocessor has pretty good support for the @('define')- and
@('ifdef')-related directives:</p>

<ul>
 <li>define</li>
 <li>ifdef</li>
 <li>ifndef</li>
 <li>elsif</li>
 <li>else</li>
 <li>undef</li>
</ul>

<p>However, we do not currently accept definitions with arguments, e.g.,
@('`max(a,b)'), and we place some (reasonable) restrictions on the above
macros.  For instance, we do not allow definitions to include most compiler
directives---we allow the body of @('`foo') to include @('`bar'), but not
@('`endif').  These restrictions are intended to ensure that we do not
\"mispreprocess\" anything.  See @(see preprocessor-define-minutia) for some
details and additional discussion.</p>

<p>We also have pretty good support for @('include') directives.  This is quite
underspecified, and we have basically tried to mimic the behavior of Verilog-XL
and NCVerilog.  See also @(see preprocessor-include-minutia).</p>


<h4>Ignored Directives</h4>

<p>We also \"support\" certain directives by <b>ignoring</b> them.</p>

<ul>
 <li>celldefine</li>
 <li>endcelldefine</li>
 <li>resetall</li>
 <li>timescale</li>
</ul>

<p>When we say we ignore these directives, we mean that the preprocessor
literally removes them from the source code that the lexer sees.  No record of
these directives is ever kept.  A consequence of this is, upon having loaded
some VL modules, there is not really any way to know whether these directives
were included anywhere in the source code.</p>

<p>In the case of @('celldefine') and @('endcelldefine'), this seems pretty
reasonable.  It seems that these directives only mark modules as \"cells\" for
certain PLI directives or other tools.  None of the tools we are developing
care about this, so for now we just ignore this directive.</p>

<p>The @('resetall') directive is tool dependent and it seems valid to ignore
it entirely.  We do not try to enforce the restriction that @('resetall') must
not occur within a module definition.</p>

<p>We also ignore @('timescale') directives.  This is not ideal, but is pretty
reasonable for things like ESIM where timing is irrelevant.  It is also fairly
reasonable even for something like a transistor analyzer that cares about unit
delays, as long as differnet timescales are not being mixed together.  (Mixing
timescales within a single design seems insane, and after all what is the
\"default\" timescale supposed to be?  BOZO maybe add a warning if more than
one kind of timescale is seen.</p>

<p>As future work, there might be some benefit to somehow preserving these
directives so that they can be printed out again in the simplified Verilog we
produce.  That is, maybe it would make the simplified Verilog easier to use as
a \"drop-in replacement\" for the unsimplified Verilog.</p>


<h4>Unsupported Directives</h4>

<p>We currently make no attempt to support:</p>

<ul>
 <li>`begin_keywords</li>
 <li>`default_nettype</li>
 <li>`end_keywords</li>
 <li>`line</li>
 <li>`pragma</li>
 <li>`nounconnected_drive</li>
 <li>`unconnected_drive</li>
</ul>

<p>It might be good to ignore @('begin_keywords \"1364-2005\"') and just cause
an error if a different set of keywords is requested.  We could also ignore
@('end_keywords').  But trying to add anything more sophisticated than this
seems very tricky and messy.</p>

<p>It would be good to add proper support for @('`line').  Failing that, it
would be quite easy to just ignore it, like the other ignored directives.  We
should probably also ignore @('`pragma') directives, and this should be easy to
do.</p>

<p>It would be somewhat difficult to support @('default_nettype') and
@('unconnected_drive').  Probably the thing to do would be build a table of
when the declarations are made, and then use some trick like comment injection
to mark modules appropriately.  We would then have to change the @(see
make-implicit-wires) transform to consider the @('default_nettype') for the
module, and probably use a separate transform to handle @('unconnected_drive')
stuff.</p>")



(defenum vl-is-compiler-directive-p

  (;; Verilog-2005 Compiler Directives
   "begin_keywords"
   "celldefine"
   "default_nettype"
   "define"
   "else"
   "elsif"
   "end_keywords"
   "endcelldefine"
   "endif"
   "ifdef"
   "ifndef"
   "include"
   "line"
   "nounconnected_drive"
   "pragma"
   "resetall"
   "timescale"
   "unconnected_drive"
   "undef"

   ;; Extended VL Compiler Directives
   "centaur_define"
   )

  :parents (preprocessor)
  :short "List of Verilog-2005 compiler directives."
  :long "<p>This list is taken directly from Section 19.  We do not support some of
these, but we need to recognize all of them so that we can complain when we
run into ones we don't support, etc.</p>

<p><b>Centaur Extension</b>.  We also add @('centaur_define'), which we treat
exactly as @('define').</p>")



(defxdoc preprocessor-ifdef-minutia
  :parents (preprocessor)
  :short "Subtle notes about or @('`define') and @('`ifdef') handling."

  :long "<p>There are many subtleties related to @('`define') and @('`ifdef')
that make my head hurt.</p>

<p><b>BOZO</b> most of my testing was done on Verilog-XL before I really knew
much about NCVerilog.  It would be good to double-check all of these things on
NCVerilog and make sure it behaves the same.</p>


<h5>Define is Lazy</h5>

<p>An important thing to realize is that the text which follows \"@('`define
foo')\" is not preprocessed once when it is read.  Instead, it is separately
preprocessed each time `foo is encountered.  Hence, upon running</p>

@({
`define foo 3
`define bar `foo
`undef foo
`define foo 4
})

<p>the value of `bar will be 4.</p>


<h5>Includes are not followed if they are @('ifdef')ed away.</h5>

<p>On both Verilog-XL and NCVerilog, it appears that an @('`include')
directives within @('ifdef')-ed away blocks are NOT expanded.  An easy way to
test this is by writing a file called @('endif.v') which simply contains:</p>

@({
`endif
})

<p>Then we can do things like this:</p>

@({
`define foo
`ifdef foo
  `include \"endif.v\"
// the `ifdef has now ended
})

<p>And this:</p>

@({
// suppose bar is undefined
`ifdef bar
  `include \"endif.v\"
  // the `ifdef has not ended yet, so the include is not expanded
`endif
})

<p>We think this is pretty reasonable so we mimic this behavior.</p>


<h5>We Prohibit Certain Directives In Defines</h5>

<p>In Verilog-XL, @('`define') can interact with the @('`ifdef') tree in subtle
ways.  For instance, Verilog-XL accepts the following input:</p>

@({
`define condition 1
`define myendif `endif
`ifdef condition
   assign w1 = 1 ;
`myendif
})

<p>Yet when @('`foo') is used inside of an ifdef'd-away section, it is not
expanded.  And so, the above example becomes a parse error if you merely remove
the @('`define condition 1') line.</p>

<p>Another subtlety.  As expected, defines found within ifdefed-away parts of
the code have no effect.  For example, if not_defined is not defined, then upon
running</p>

@({
`define foo 3
`ifdef not_defined
   `define foo 4
`endif
})

<p>the value of @('`foo') will correctly be 3.  Similarly, writing @('`undef
foo') in the not_defined block does not actually undefine foo.  But the
preprocessor is not mindlessly skipping text until an `else or `elseif is
encountered.  For example, the following is well-formed and does not result in
a too-many-endifs warning.</p>

@({
`ifdef not_defined
   `define myendif `endif
`endif
})

<p>This is insane, so we prohibit things like @('`define myendif `endif') by
disallowing the use of built-in directives in macro text.  Note that we still
permit the use of @('`define foo `bar'), with the same lazy semantics that
Verilog-XL uses.</p>


<h5>We Prohibit Defining or Testing Built-in Directive Names</h5>

<p>We do not allow compiler directive names to be @('`define')d, or to be used
within @('ifdef'), @('ifndef'), or @('elsif') directives.  Why is this?</p>

<p>Note that macro names can be simple or escaped identifiers.  In Section
3.7.1, we are told that the leading backslash character and trailing whitespace
are not considered part of an escaped identifier, and that the escaped
identifier @('\\cpu3') is to be treated the same as @('cpu3').  Indeed, in
Verilog-XL we find that the following works as expected:</p>

@({
`define foo 3
`define \\bar 4

assign w1 = `foo ;
assign w2 = `\\foo ;
assign w3 = `bar ;
assign w4 = '\\bar ;
})

<p>In Section 19.3.1, we are told that all compiler directives shall be
considered predefined macro names, and it shall be illegal to redefine a
compiler directive as a macro name.  And Verilog-XL seems to rightfully complain
about things like:</p>

@({
`define define 5
`define ifdef 6
})

<p>And yet, Verilog-XL permits the following:</p>

@({
`define \\define 5
`define \\ifdef 6

assign w1 = `\\define ;
assign w2 = `\\ifdef ;
})

<p>While the following will be errors:</p>

@({
assign w3 = `define ;
assign w4 = `ifdef ;
})

<p>Should @('\\define') be treated differently from @('define')?  Maybe.  After
all, the point of escaped identifiers is probably to not clash with regular
keywords.  But on the other hand, if the predefined names are to be considered
predefined, then shouldn't things like this</p>

@({
`ifdef define
})

<p>always evaluate to true?  But in Verilog-XL this is false unless you have
done a @('`define \\define') like above.  Verilog-XL also does not complain
about @('`undef') define, which seems strange.</p>

<p>At any rate, to entirely avoid the question of what the right behavior is
here, we simply prohibit the use of compiler directives, whether escaped or
not, as names anywhere in @('defines'), @('undefs'), @('ifdefs'), @('ifndefs'),
and @('elsifs').  In practice this only prevents people from writing things
like @('`define define') and @('`ifdef undef'), anyway, so this should not be
too controversial.</p>


<h5>We make certain restrictions to disambiguate line continuations and
comments.</h5>

<p>From 19.3.1, the macro text for a define is:</p>

<ul>
 <li>any arbitrary text specified on the same line as the macro name,</li>

 <li>except that the sequence @('\\<newline>') may be used to extend the macro
     text across multiple lines,</li>

 <li>and single-line comments are not to become part of the substituted
     text.</li>
</ul>

<p>On the surface, this is straightforward enough.  But it is difficult to know
exactly how comments and these line continuations are supposed to interact.
And Verilog-XL, in particular, has some very strange and seemingly inconsistent
rules:</p>

@({
`define foo 5 \// comment             (accepted)
         'h4

`define foo 5 // comment \\           (rejected)
         'h4

`define foo 5 \\/* comment */         (rejected)
         'h4

`define foo 5 /* comment \\           (accepted)
      */ 'h4

`define foo 5 /* comment              (rejected)
      */ 'h4
})

<p>To prevent any amiguity, we prohibit any combination of comments and
continuations that seems difficult to understand.  In particular, we impose the
following \"cowardly\" restrictions on macro text:</p>

<ol>

<li>Single-line comments are not allowed to end with @('\\')</li>

<li>Block comments are not allowed to contain newlines</li>

<li>The sequences @('\\//') and @('\\/*') are not allowed except within
comments, string literals, and escaped identifiers</li>

</ol>

<p>These constriants make reading until the end of the macro text fairly
complicated since we cannot stupidly read the text without interpreting it;
rather we have to look for string literals, comments, escaped identifiers, etc.
The goal is for everything we support will be interpreted in the same way by
Verilog-XL and other tools.</p>")



(defaggregate vl-iframe
  (initially-activep
   some-thing-satisfiedp
   already-saw-elsep)
  :tag :vl-iframe
  :require ((booleanp-of-vl-iframe->initially-activep (booleanp initially-activep))
            (booleanp-of-vl-iframe->some-thing-satisfiedp (booleanp some-thing-satisfiedp))
            (booleanp-of-vl-iframe->already-saw-elsep (booleanp already-saw-elsep)))
  :parents (preprocessor)
  :short "@('`ifdef') stack frame objects."

  :long "<p>Iframes (\"ifdef frames\") are essential in our approach to
handling @('`ifdef') directives.  Our main preprocessing function, @(see
vl-preprocess-loop), takes three arguments that have to do with handling
ifdefs:</p>

<ul>

<li>@('defines') is the current @(see vl-defines-p) alist.  For now, just
assume that we are able to appropriately keep this list updated as we encounter
defines and undefs.</li>

<li>@('activep') is a boolean which is true whenever the characters are are now
reading from the file ought to be given to the lexer -- the idea is that when
we encounter an @('`ifdef') whose condition isn't satisfied, we turn off
@('activep') until the closing @('`endif') is encountered.</li>

<li>@('istack') is a stack of @('vl-iframe-p') objects which explain how to
manage @('activep') as we descend through a nest of @('`ifdef'), @('`ifndef'),
@('`elsif'), @('`else'), and @('`endif') directives.</li>

</ul>

<p>Let us temporarily ignore nested directives.  Then, our task would be to
decide when activep should be turned on during sequences like this:</p>

@({
    `if[n]def THING
      stuff1
    `elsif THING2
      stuff2
    `elsif THING3
      stuff3
    `else
      stuff4
    `endif
})

<p>The semantics of this (Section 19.4) are essentially: figure out the first
<i>THING</i> that is satisfied, include its stuff, and ignore the rest.  So for
instance, if <i>THING2</i> and <i>THING3</i> are both satisfied, we still only
want to include <i>stuff2</i> since it comes first.</p>

<p>To implement this, the basic idea is that when we encounter an @('`ifdef')
or @('`ifndef') directive, we construct an iframe that helps us set
@('activep') correctly.  The first two fields of the iframe are:</p>

<dl>

<dt>@('some-thing-satisfiedp')</dt>

<dd>which indicates if any of the <i>THING</i>s we have seen so far was
satisfied, and</dd>

<dt>@('already-saw-elsep')</dt>

<dd>which indicates whether we have seen an @('`else') and is used only as a
sanity check to prevent multiple @('`else') clauses.</dd>

</dl>

<p>And as we descend through the above sequences, we update the iframe and
ensure that @('activep') is set exactly when the current <i>THING</i> is
satisfied and no previous <i>THING</i> was satisfied.</p>

<p>But the story is not quite complete yet, because we also have to handle
nested ifdefs.  For example, imagine we have:</p>

@({
   `ifdef OUTER
     ...
     `ifdef INNER_THING1
       stuff1
     `elsif INNER2_THING2
       stuff2
     `else
       stuff3
     `endif
     ...
   `endif
})

<p>This is almost the same, except that now we only want to turn on
@('activep') when <i>OUTER</i> is also satisfied.  To keep track of this, we
add another field to our iframe objects:</p>

<dl>

<dt>@('initially-activep')</dt>

<dd>which indicates whether @('activep') was set when we encountered the
@('`ifdef') or @('ifndef') for this iframe.</dd>

</dl>

<p>Now, @('activep') should be enabled exactly when:</p>

<ul>

<li>(inner criteria): the current <i>THING</i> is satisfied and no previous
<i>THING</i> was sastified, and</li>

<li>(outer-criteria): @('initially-activep') was also set, i.e., this chunk of
code is not being blocked by some <i>THING</i> in an outer @('ifdef')
tree.</li>

</ul>")

(deflist vl-istack-p (x)
  (vl-iframe-p x)
  :elementp-of-nil nil)



(defsection vl-process-ifdef
  :parents (preprocessor)
  :short "Handler for @('ifdef'), @('ifndef'), and @('elsif') directives."

  :long "<p><b>Signature:</b> @(call vl-process-ifdef) returns @('(mv successp
new-istack new-activep remainder)')</p>

<p>See the discussion in @(see vl-iframe-p) for details.</p>

<p>Here, @('directive') is either @('ifdef'), @('ifndef'), or @('elsif'); we
assume that we have just read @('`directive') from @('echars').  We need to
read the identifier that should follow this directive, look it up in the
defines table, and make the appropriate changes to the @('istack') and
@('activep').</p>"

  (defund vl-process-ifdef (loc directive echars defines istack activep)
    "Returns (MV SUCCESSP NEW-ISTACK NEW-ACTIVEP REMAINDER)"
    (declare (xargs :guard (and (vl-location-p loc)
                                (member-equal directive '("ifdef" "ifndef" "elsif"))
                                (vl-echarlist-p echars)
                                (true-listp echars)
                                (vl-defines-p defines)
                                (vl-istack-p istack)
                                (booleanp activep))))

    (b* (((mv & remainder)      (vl-read-while-whitespace echars))
         ((mv name & remainder) (vl-read-identifier remainder)))
        (cond ((not name)
               (mv (cw "Preprocessor error (~s0): found an `~s1 without an identifier.~%"
                       (vl-location-string loc) directive)
                   istack activep echars))

              ((vl-is-compiler-directive-p name)
               ;; Special prohibition of compiler directive names in ifdefs,
               ;; ifndefs, etc.  See :xdoc preprocessor-ifdef-minutia for why.
               (mv (cw "Preprocessor error (~s0): cowardly refusing to permit `s1 ~s2.~%"
                       (vl-location-string loc) directive name)
                   istack activep echars))

              ((equal directive "ifdef")
               (let* ((this-satisfiedp (consp (vl-lookup-in-defines name defines)))
                      (new-iframe      (vl-iframe activep this-satisfiedp nil))
                      (new-istack      (cons new-iframe istack))
                      (new-activep     (and activep this-satisfiedp)))
                 (mv t new-istack new-activep remainder)))

              ((equal directive "ifndef")
               (let* ((this-satisfiedp (not (vl-lookup-in-defines name defines)))
                      (new-iframe      (vl-iframe activep this-satisfiedp nil))
                      (new-istack      (cons new-iframe istack))
                      (new-activep     (and activep this-satisfiedp)))
                 (mv t new-istack new-activep remainder)))

              ((not (consp istack))
               (mv (cw "Preprocessor error (~s0): found an `elsif, but no ~
                        ifdef or ifndef is open.~%"
                       (vl-location-string loc))
                   istack activep echars))

              ((vl-iframe->already-saw-elsep (car istack))
               (mv (cw "Preprocessor error (~s0): found an `elsif, but we ~
                        have already seen `else.~%"
                       (vl-location-string loc))
                   istack activep echars))

              (t
               (let* ((this-satisfiedp   (consp (vl-lookup-in-defines name defines)))
                      (iframe            (car istack))
                      (prev-satisfiedp   (vl-iframe->some-thing-satisfiedp iframe))
                      (initially-activep (vl-iframe->initially-activep iframe))
                      (new-activep       (and this-satisfiedp
                                              (not prev-satisfiedp)
                                              initially-activep))
                      (new-iframe        (vl-iframe initially-activep
                                                    (or this-satisfiedp prev-satisfiedp)
                                                    nil))
                      (new-istack        (cons new-iframe (cdr istack))))
                 (mv t new-istack new-activep remainder))))))

  (local (in-theory (enable vl-process-ifdef)))

  (defthm vl-istack-p-of-vl-process-ifdef
    (implies (and (force (vl-istack-p istack))
                  (force (booleanp activep)))
             (vl-istack-p (mv-nth 1 (vl-process-ifdef loc directive echars
                                                      defines istack activep)))))

  (defthm booleanp-of-vl-process-ifdef
    (implies (and (force (booleanp activep))
                  (force (vl-istack-p istack)))
             (booleanp (mv-nth 2 (vl-process-ifdef loc directive echars
                                                   defines istack activep)))))

  (defthm vl-echarlist-p-of-vl-process-ifdef
    (implies (force (vl-echarlist-p echars))
             (vl-echarlist-p (mv-nth 3 (vl-process-ifdef loc directive echars
                                                         defines istack activep)))))

  (defthm true-listp-of-vl-process-ifdef
    (equal (true-listp (mv-nth 3 (vl-process-ifdef loc directive echars
                                                   defines istack activep)))
           (true-listp echars))
    :rule-classes ((:rewrite)
                   (:type-prescription :corollary
                    (implies (true-listp echars)
                             (true-listp
                              (mv-nth 3 (vl-process-ifdef loc directive echars
                                                          defines istack activep)))))))

  (defthm acl2-count-of-vl-process-ifdef-weak
    (<= (acl2-count (mv-nth 3 (vl-process-ifdef loc directive echars
                                                defines istack activep)))
        (acl2-count echars))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm acl2-count-of-vl-process-ifdef-strong
    (implies (mv-nth 0 (vl-process-ifdef loc directive echars
                                         defines istack activep))
             (< (acl2-count (mv-nth 3 (vl-process-ifdef loc directive echars
                                                        defines istack activep)))
                (acl2-count echars)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force))))))



(defsection vl-process-else
  :parents (preprocessor)
  :short "Handler for @('else') directives."

  :long "<p><b>Signature:</b> @(call vl-process-else) returns @('(mv successp
new-istack new-activep)').</p>

<p>See the discussion in @(see vl-iframe-p) for details.</p>"

  (defund vl-process-else (loc istack activep)
    "Returns (MV SUCCESSP NEW-ISTACK NEW-ACTIVEP)"
    (declare (xargs :guard (and (vl-location-p loc)
                                (vl-istack-p istack)
                                (booleanp activep))))
    (cond ((not (consp istack))
           (mv (cw "Preprocessor error (~s0): found an `else, but no ~
                    ifdef/ifndef is open.~%"
                   (vl-location-string loc))
               istack activep))

          ((vl-iframe->already-saw-elsep (car istack))
           (mv (cw "Preprocessor error (~s0): found an `else, but we have ~
                    already seen an `else.~%"
                   (vl-location-string loc))
               istack activep))

          (t
           (let* ((iframe            (car istack))
                  (prev-satisfiedp   (vl-iframe->some-thing-satisfiedp iframe))
                  (initially-activep (vl-iframe->initially-activep iframe))
                  (new-activep       (and initially-activep
                                          (not prev-satisfiedp)))
                  (new-iframe        (vl-iframe initially-activep t t))
                  (new-istack        (cons new-iframe (cdr istack))))
             (mv t new-istack new-activep)))))

  (local (in-theory (enable vl-process-else)))

  (defthm vl-istack-p-of-vl-process-else
    (implies (and (force (vl-istack-p istack))
                  (force (booleanp activep)))
             (vl-istack-p (mv-nth 1 (vl-process-else loc istack activep)))))

  (defthm booleanp-of-vl-process-else
    (implies (and (force (vl-istack-p istack))
                  (force (booleanp activep)))
             (booleanp (mv-nth 2 (vl-process-else loc istack activep))))))



(defsection vl-process-endif
  :parents (preprocessor)
  :short "Handler for @('endif') directives."

  :long "<p><b>Signature:</b> @(call vl-process-endif) returns @('(mv successp
new-istack new-activep)').</p>

<p>See the discussion in @(see vl-iframe-p) for details.</p>"

  (defund vl-process-endif (loc istack activep)
    "Returns (MV SUCCESSP NEW-ISTACK NEW-ACTIVEP)"
    (declare (xargs :guard (and (vl-location-p loc)
                                (vl-istack-p istack)
                                (booleanp activep))))
    (if (not (consp istack))
        (mv (cw "Preprocessor error (~s0): found an `endif, but no ifdef/ifndef ~
                 is open.~%"
                (vl-location-string loc))
            istack activep)
      (let ((new-istack (cdr istack))
            (new-activep (vl-iframe->initially-activep (car istack))))
        (mv t new-istack new-activep))))

  (local (in-theory (enable vl-process-endif)))

  (defthm vl-istack-p-of-vl-process-endif
    (implies (and (force (vl-istack-p istack))
                  (force (booleanp activep)))
             (vl-istack-p (mv-nth 1 (vl-process-endif loc istack activep)))))

  (defthm booleanp-of-vl-process-endif
    (implies (and (force (vl-istack-p istack))
                  (force (booleanp activep)))
             (booleanp (mv-nth 2 (vl-process-endif loc istack activep))))))




(defsection vl-read-until-end-of-define
  :parents (preprocessor)
  :short "Read from @('`define') until the end of the line."

  :long "<p><b>Signature:</b> @(call vl-read-until-end-of-define) returns
@('(mv successp prefix remainder)').</p>

<p>This is really tricky!  See @(see preprocessor-ifdef-minutia) for an
overview of some of the problems we face.</p>"

  (defund vl-read-until-end-of-define (echars)
    "Returns (MV SUCCESSP TEXT REMAINDER)"
    (declare (xargs :guard (and (vl-echarlist-p echars)
                                (true-listp echars))))
    (if (not (consp echars))
        ;; We allow macros to be defined on the last line of the file;
        ;; "implicitly inserting a newline" for them.
        (mv t nil echars)

      (case (vl-echar->char (first echars))

        (#\Newline
         ;; Successful end of macro text.
         (mv t nil echars))

        (#\`
         ;; We allow user-defines like `foo and `bar, but not built-ins
         ;; like `define and `endif.
         (mv-let (name prefix remainder)
                 (vl-read-identifier (cdr echars))
                 (cond ((not name)
                        (mv (cw "Preprocessor error (~s0): no name following ~
                                 back-quote/grave character (`).~%"
                                (vl-location-string (vl-echar->loc (car echars))))
                            nil echars))
                       ((vl-is-compiler-directive-p name)
                        (mv (cw "Preprocessor error (~s0): we cowardly do not ~
                                 allow `~s1 in defines.~%"
                                (vl-location-string (vl-echar->loc (car echars)))
                                name)
                            nil echars))
                       (t
                        (mv-let (successp text remainder)
                                (vl-read-until-end-of-define remainder)
                                (if (not successp)
                                    (mv nil nil echars)
                                  (mv t
                                      (cons (car echars) (append prefix text))
                                      remainder)))))))

        (#\"
         ;; Skip over string literals so we aren't confused by graves, etc.
         (mv-let (string prefix remainder)
                 (vl-read-string echars)
                 (if (not string)
                     (mv nil nil echars)
                   (mv-let (successp text remainder)
                           (vl-read-until-end-of-define remainder)
                           (if (not successp)
                               (mv nil nil echars)
                             (mv t (append prefix text) remainder))))))

        (#\\
         (cond ((vl-matches-string-p "//" (cdr echars))
                (mv (cw "Preprocessor error (~s0): we cowardly do not allow ~
                         '\//' in defines.~%"
                        (vl-location-string (vl-echar->loc (car echars))))
                    nil echars))
               ((vl-matches-string-p "/*" (cdr echars))
                (mv (cw "Preprocessor error (~s0): we cowardly do not allow ~
                         '\/*' in defines.~%"
                        (vl-location-string (vl-echar->loc (car echars))))
                    nil echars))
               ((vl-matches-string-p *nls* (cdr echars))

; Line continuations.
;
; Ugh.  I found a stupid bug here on 2011-04-26 because I was recurring on (cdr
; echars) instead of (cddr echars).
;
; Then I did some more tests.  This is really horrible.  I apparently used to
; think that the sequence \<newline> should just expand into a newline
; character.  But that doesn't seem right: both Verilog-XL and NCVerilog say
; that `goo is 3 in the following:
;
;   |`define foo 1 \<newline>
;   |  + 2
;   |`define `goo `foo
;
; So it seems that \<newline> must expand into something other than a newline,
; since otherwise the expansion of `foo would yield:
;
;   |`define `goo 1
;   |  + 2
;
; And `goo would then be defined as 1.  So what should \<newline> expand to?  I
; think plausible answers would be nothing, or a single space.  As another
; experiment, I tried:
;
;  |`define `test module\<newline>
;  |test
;  |
;  |`test () ;
;  |endmodule
;
; NCVerilog was happy with this, which suggests that \<newline> expands to at
; least a space.  Verilog-XL said this was a syntax error, even when I added a
; space before the module's name, e.g.,
;
;  |`define `test module\<newline>
;  | test
;
; But it was happy when I put a space before the \<newline>.  So, it doesn't
; seem like Verilog-XL tolerates \ continuations without a space before them,
; meaning that whether it expands to a space or nothing is irrelevant.
;
; Well, I think expanding into a space seems pretty reasonable, so that's what
; I'm going to do for now.

                (mv-let (successp text remainder)
                        (vl-read-until-end-of-define (cddr echars))
                        (if (not successp)
                            (mv nil nil echars)
                          (mv t
                              (cons (change-vl-echar (second echars) :char #\Space) text)
                              remainder))))
               (t
                ;; Skip over escaped identifiers so we aren't confused by graves,
                ;; etc.
                (mv-let (name prefix remainder)
                        (vl-read-escaped-identifier echars)
                        (if (not name)
                            (mv (cw "Preprocessor error (~s0): stray backslash?~%"
                                    (vl-location-string (vl-echar->loc (car echars))))
                                nil echars)
                          (mv-let (successp text remainder)
                                  (vl-read-until-end-of-define remainder)
                                  (if (not successp)
                                      (mv nil nil echars)
                                    (mv t (append prefix text) remainder))))))))

        (#\/
         (cond
          ((vl-matches-string-p "//" echars)
           ;; start of a single-line comment; read until end of line.
           (b* (((mv successp prefix remainder)
                 (vl-read-until-literal *nls* echars)))
               (cond ((not successp)
                      ;; This actually just means the file ends with something
                      ;; like "`define foo ... // blah blah" and there is no
                      ;; newline.  That's fine.  The comment is to be excluded
                      ;; from the expansion.
                      (mv t nil remainder))
                     ((and (consp prefix)
                           (eql (vl-echar->char (car (last prefix))) #\\))
                      (mv (cw "Preprocessor error (~s0): we cowardly do not ~
                               allow single-line comments inside defines to ~
                               end with \.~%"
                              (vl-location-string (vl-echar->loc (car echars))))
                          nil echars))
                     (t
                      ;; Single-line comments are to be excluded; nothing more is
                      ;; to be read.
                      (mv t nil remainder)))))

          ((vl-matches-string-p "/*" echars)
           (b* (((mv successp prefix remainder)
                 (vl-read-through-literal "*/" (cddr echars))))
               (cond ((not successp)
                      (mv (cw "Preprocessor error (~s0): block comment is ~
                               never closed.~%"
                              (vl-location-string (vl-echar->loc (car echars))))
                          nil echars))
                     ((member #\Newline (vl-echarlist->chars prefix))
                      (mv (cw "Preprocessor error (~s0): block comment inside ~
                               a define is not closed before end of line.~%"
                              (vl-location-string (vl-echar->loc (car echars))))
                          nil echars))
                     (t
                      (mv-let (successp text remainder)
                              (vl-read-until-end-of-define remainder)
                              (if (not successp)
                                  (mv nil nil echars)
                                (mv t (append (list* (first echars)
                                                     (second echars)
                                                     prefix)
                                              text)
                                    remainder)))))))

          (t
           ;; Regular division operator -- treat it as a regular character
           (mv-let (successp text remainder)
                   (vl-read-until-end-of-define (cdr echars))
                   (if (not successp)
                       (mv nil nil echars)
                     (mv t (cons (car echars) text) remainder))))))

        (otherwise
         ;; A regular character
         (mv-let (successp text remainder)
                 (vl-read-until-end-of-define (cdr echars))
                 (if (not successp)
                     (mv nil nil echars)
                   (mv t (cons (car echars) text) remainder)))))))

  (local (in-theory (enable vl-read-until-end-of-define)))

  (defthm booleanp-of-vl-read-until-end-of-define-successp
    (booleanp (mv-nth 0 (vl-read-until-end-of-define echars)))
    :rule-classes :type-prescription)

  (defthm vl-echarlist-p-of-vl-read-until-end-of-define-prefix
    (implies (and (force (vl-echarlist-p echars))
                  (force (true-listp echars)))
             (vl-echarlist-p (mv-nth 1 (vl-read-until-end-of-define echars)))))

  (defthm true-listp-of-vl-read-until-end-of-define-prefix
    (true-listp (mv-nth 1 (vl-read-until-end-of-define echars)))
    :rule-classes :type-prescription)

  (defthm vl-echarlist-p-of-vl-read-until-end-of-define-remainder
    (implies (force (vl-echarlist-p echars))
             (vl-echarlist-p (mv-nth 2 (vl-read-until-end-of-define echars)))))

  (defthm true-listp-of-vl-read-until-end-of-define-remainder
    (equal (true-listp (mv-nth 2 (vl-read-until-end-of-define echars)))
           (true-listp echars))
    :rule-classes ((:rewrite)
                   (:type-prescription
                    :corollary
                    (implies (true-listp echars)
                             (true-listp (mv-nth 2 (vl-read-until-end-of-define echars)))))))

  (defthm acl2-count-of-vl-read-until-end-of-define-weak
    (<= (acl2-count (mv-nth 2 (vl-read-until-end-of-define echars)))
        (acl2-count echars))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm acl2-count-of-vl-read-until-end-of-define-strong
    (implies (mv-nth 1 (vl-read-until-end-of-define echars))
             (< (acl2-count (mv-nth 2 (vl-read-until-end-of-define echars)))
                (acl2-count echars)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force))))))



(defsection vl-process-define
  :parents (preprocessor)
  :short "Handler for @('define') directives."

  :long "<p><b>Signature:</b> @(call vl-process-define) returns @('(mv successp
new-defines remainder)').</p>

<p>We assume that @('`define') has just been read and @('echars') is the text
which comes right after the @('`define') directive.  We read the name and text
for this new macro definition, and update the defines table appropriately if
@('activep') is set.</p>"

  (defund vl-process-define (loc echars defines activep)
    "Returns (MV SUCCESSP NEW-DEFINES REMAINDER)"
    (declare (xargs :guard (and (vl-location-p loc)
                                (vl-echarlist-p echars)
                                (true-listp echars)
                                (vl-defines-p defines)
                                (booleanp activep))
                    :guard-debug t))

    (b* (((mv & remainder)      (vl-read-while-whitespace echars))
         ((mv name & remainder) (vl-read-identifier remainder))

         ((when (not name))
          (mv (cw "Preprocessor error (~s0): found a `define without a name.~%"
                  (vl-location-string loc))
              defines echars))

         ((when (vl-is-compiler-directive-p name))
          (mv (cw "Preprocessor error (~s0): refusing to permit `define ~s1.~%"
                  (vl-location-string loc) name)
              defines echars))

         ((mv successp text remainder)
          (vl-read-until-end-of-define remainder))

         ((when (not successp))
          ;; Error message was already printed, so we just need to return
          ;; failure.
          (mv nil defines echars))

         ((when (not activep))
          ;; This define happens in an ifdef'd out context anyway, so we just
          ;; wanted to skip over it.  It looks like we're doing nothing here,
          ;; but it's important that we got called and went to the trouble of
          ;; parsing the define line, since this ensures there is no nested
          ;; `endif, etc. in the definition.
          (mv t defines remainder))

         (lookup
          (vl-lookup-in-defines name defines))

         (- (if (and lookup
                     (not (equal (str::trim (vl-echarlist->string (cdr lookup)))
                                 (str::trim (vl-echarlist->string text)))))
                (cw "Preprocessor warning (~s0): redefining ~s1 from ~s2 to ~s3.~%"
                    (vl-location-string loc)
                    name
                    (vl-echarlist->string (cdr lookup))
                    (vl-echarlist->string text))
              nil)))
        (mv t
            (acons name text defines)
            remainder)))

  (local (in-theory (enable vl-process-define)))

  (defthm vl-defines-p-of-vl-process-define
    (implies (and (force (vl-location-p loc))
                  (force (vl-echarlist-p echars))
                  (force (true-listp echars))
                  (force (vl-defines-p defines)))
             (vl-defines-p (mv-nth 1 (vl-process-define loc echars defines activep)))))

  (defthm vl-echarlist-p-of-vl-process-define-remainder
    (implies (force (vl-echarlist-p echars))
             (vl-echarlist-p (mv-nth 2 (vl-process-define loc echars defines activep)))))

  (defthm true-listp-of-vl-process-define-remainder
    (equal (true-listp (mv-nth 2 (vl-process-define loc echars defines activep)))
           (true-listp echars))
    :rule-classes ((:rewrite)
                   (:type-prescription
                    :corollary
                    (implies (true-listp echars)
                             (true-listp
                              (mv-nth 2 (vl-process-define loc echars defines activep)))))))

  (defthm acl2-count-of-vl-process-define
    (<= (acl2-count (mv-nth 2 (vl-process-define loc echars defines activep)))
        (acl2-count echars))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm acl2-count-of-vl-process-define-strong
    (implies (mv-nth 0 (vl-process-define loc echars defines activep))
             (< (acl2-count (mv-nth 2 (vl-process-define loc echars defines activep)))
                (acl2-count echars)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force))))))



(defsection vl-process-undef
  :parents (preprocessor)
  :short "Handler for @('undef') directives."

  :long "<p><b>Signature:</b> @(call vl-process-undef) returns @('(mv successp
new-defines remainder)').</p>

<p>We assume that an @('`undef') has just been read and @('echars') is the text
which follows it.  We try to read the name we are to undefine, then update the
defines table appropriately.</p>"

  (defund vl-process-undef (loc echars defines activep)
    "Returns (MV SUCCESSP NEW-DEFINES REMAINDER)"
    (declare (xargs :guard (and (vl-location-p loc)
                                (vl-echarlist-p echars)
                                (vl-defines-p defines)
                                (booleanp activep))))

    (b* (((mv & remainder)      (vl-read-while-whitespace echars))
         ((mv name & remainder) (vl-read-identifier remainder))

         ((when (not name))
          (mv (cw "Preprocessor error (~s0): found an `undef without a name.~%"
                  (vl-location-string loc))
              defines echars))

         ((when (vl-is-compiler-directive-p name))
          (mv (cw "Preprocessor error (~s0): refusing to permit `undef ~s1.~%"
                  (vl-location-string loc) name)
              defines echars))

         ((when (not activep))
          ;; Not an active section, so don't actually do anything.
          (mv t defines remainder))

         (lookup
          (vl-lookup-in-defines name defines))

         (- (if (not lookup)
                (cw "Preprocessor warning (~s0): found `undef ~s1, but ~s1 is ~
                     not defined.~%"
                    (vl-location-string loc)
                    name)
              (cw "Undefining ~s0.~%" name))))

        (mv t (remove-from-alist name defines) remainder)))

  (local (in-theory (enable vl-process-undef)))

  (defthm vl-defines-p-of-vl-process-undef
    (implies (and (force (vl-echarlist-p echars))
                  (force (vl-defines-p defines)))
             (vl-defines-p (mv-nth 1 (vl-process-undef loc echars defines activep)))))

  (defthm vl-echarlist-p-of-vl-process-undef-remainder
    (implies (force (vl-echarlist-p echars))
             (vl-echarlist-p (mv-nth 2 (vl-process-undef loc echars defines activep)))))

  (defthm true-listp-of-vl-process-undef-remainder
    (equal (true-listp (mv-nth 2 (vl-process-undef loc echars defines activep)))
           (true-listp echars))
    :rule-classes ((:rewrite)
                   (:type-prescription
                    :corollary
                    (implies (true-listp echars)
                             (true-listp (mv-nth 2 (vl-process-undef loc echars defines activep)))))))

  (defthm acl2-count-of-vl-process-undef
    (<= (acl2-count (mv-nth 2 (vl-process-undef loc echars defines activep)))
        (acl2-count echars))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm acl2-count-of-vl-process-undef-strong
    (implies (mv-nth 0 (vl-process-undef loc echars defines activep))
             (< (acl2-count (mv-nth 2 (vl-process-undef loc echars defines activep)))
                (acl2-count echars)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force))))))



(defsection vl-read-timescale

  (defund vl-read-timescale (echars)
    "Returns (MV PREFIX REMAINDER)"
    (declare (xargs :guard (and (vl-echarlist-p echars)
                                (true-listp echars))))

; timescale_compiler_directive ::= `timescale time_unit / time_precision
;
; The time_unit seems to be 1, 10, or 100.
; and time_precision seems to be s, ms, us, ns, ps, or fs.

    (b* (((mv ws1 remainder)     (vl-read-while-whitespace echars))
         ((mv tu-val remainder)  (vl-read-some-literal (list "100" "10" "1") remainder))
         ((mv ws2 remainder)     (vl-read-while-whitespace remainder))
         ((mv tu-type remainder) (vl-read-some-literal (list "fs" "ps" "ns" "us" "ms" "s") remainder))
         ((mv ws3 remainder)     (vl-read-while-whitespace remainder))
         ((mv div remainder)     (vl-read-literal "/" remainder))
         ((mv ws4 remainder)     (vl-read-while-whitespace remainder))
         ((mv tp-val remainder)  (vl-read-some-literal (list "100" "10" "1") remainder))
         ((mv ws5 remainder)     (vl-read-while-whitespace remainder))
         ((mv tp-type remainder) (vl-read-some-literal (list "fs" "ps" "ns" "us" "ms" "s") remainder)))
        (if (and tu-val tu-type div tp-val tp-type)
            (mv (append ws1 tu-val ws2 tu-type ws3 div ws4 tp-val ws5 tp-type)
                remainder)
          (mv (cw "Preprocessor error (~s0): invalid `timescale directive.~%"
                  (if (consp echars)
                      (vl-location-string (vl-echar->loc (car echars)))
                    "at end of file"))
              echars))))

  (def-prefix/remainder-thms vl-read-timescale))




(defxdoc preprocessor-include-minutia
  :parents (preprocessor)
  :short "Subtle notes about @('`include') handling."

  :long "<p>The Verilog spec is very vague about how @('include') directives
are to be processed.</p>

<p>It does nicely explain that we are to simply replace the @('`include
\"foo.v\"') directive with the entire contents of @('foo.b'), and explains some
things related to the syntax of the directive.  It also says that the included
file can itself contain @('include') directives, which of course seems
perfectly reasonable.</p>

<p>The spec explicitly says the filename can be an absolute or relative
pathname.  In the case of an absolute pathname, the intention seems pretty
clear.</p>

<p>Unfortunately, the spec does <b>not</b> explain anything about what a
relative path is relative to.  Upon reading the spec, I thought, \"well,
<i>obviously</i> it means relative to whatever file is currently being
processed.\" But it turns out that this is not at all how Verilog-XL and
NCVerilog handle things.</p>

<p>Instead, both of these tools include a notion of <i>include directories</i>.
These directories are similar to, but distinct from, the <i>library
directories</i> which are used to load \"missing\" modules.  These directories
are configured with command-line options like:</p>

@({
 +incdir+/home/jared/dir1 +incdir+/home/jared/dir2 ...
})

<p>When these tools see @('`include \"foo.v\"'), they seem to search for
@('foo.v') in these include directories, and include the first file that is
found.</p>

<p>Because of this, it does <i>not</i> work to just try to write includes
relative to whatever file is being loaded, you just always write them relative
to whatever the include path is going to be.</p>")



(defsection vl-read-include
  :parents (preprocessor)
  :short "Read an @('`include') directive."

  :long "<p><b>Signature:</b> @(call vl-read-include) returns @('(mv successp
filename remainder)').</p>

<p>@('echars') are the characters we are reading; we assume that an
@('`include') was just read and removed from @('echars').  We try to read the
filename part and return it (without the quotes).  Per Section 19.5 of the
Verilog spec, the syntax is:</p>

@({
 `include \"filename\"
})

<p>We are told that filename here can be a relative or absolute path, but there
is not any discussion of the actual syntax of the filename (e.g., as it relates
to escaping).  I believe it should be read as an ordinary string literal.  As
evidence for this belief:</p>

<ul>

<li>In Section 19.7 where @('`line') directives are covered, we are told that
the filename for @('`line') directives is a string constant, so if there is any
justice in the world the filenames for @('`includes') should be the same.</li>

<li>I tried using Verilog-XL and NCVerilog to @('`include
\"test\\055latch.v\"'), where 055 is the octal character code for the dash
character, and both systems were happy with this.  So, it seems like these
tools are treating it as an ordinary string constant.</li>

</ul>

<p>NOTE: We are told in Section 19.5 that only whitespace or a comment can
appear on the same line as an @('`include') directive.  We don't currently try
to enforce this restriction since it is somewhat awkward to do so.</p>"

  (defund vl-read-include (echars)
    "Returns (MV FILENAME PREFIX REMAINDER)"
    (declare (xargs :guard (and (vl-echarlist-p echars)
                                (true-listp echars))))
    (b* (((mv ws1 remainder)
          (vl-read-while-whitespace echars))

         ((mv filename prefix remainder)
          (if (and (consp remainder)
                   (equal (vl-echar->char (car remainder)) #\"))
              (vl-read-string remainder)
            (mv nil nil remainder)))

         ((unless filename)
          (mv (cw "Preprocessor error (~s0): invalid `include directive.~%"
                  (if (consp echars)
                      (vl-location-string (vl-echar->loc (car echars)))
                    "at end of file"))
              nil echars)))
      (mv filename (append ws1 prefix) remainder)))

  (def-prefix/remainder-thms vl-read-include
    :prefix-n 1
    :remainder-n 2)

  (defthm stringp-of-vl-read-include
    (equal (stringp (mv-nth 0 (vl-read-include echars)))
           (if (mv-nth 0 (vl-read-include echars))
               t
             nil))
    :hints(("Goal" :in-theory (enable vl-read-include)))))




(defsection vl-preprocess-loop

  (defund vl-preprocess-loop (echars defines istack activep include-dirs acc n state)
    "Returns (MV SUCCESSP DEFINES-PRIME ACC REMAINDER STATE)"
    (declare (xargs :guard (and (vl-echarlist-p echars)
                                (true-listp echars)
                                (vl-defines-p defines)
                                (vl-istack-p istack)
                                (booleanp activep)
                                (string-listp include-dirs)
                                (vl-echarlist-p acc)
                                (natp n))
                    :stobjs state
                    :measure (two-nats-measure n (acl2-count echars))
                    :hints(("Goal" :in-theory (disable (force))))))

; This is the main loop for the preprocessor.  It accumulates the transformed
; characters that are to be given to the lexer into acc, in reverse order.

    (b* (((when (atom echars))
          (mv t defines acc echars state))

         (echar1 (car echars))
         (char1  (vl-echar->char echar1))
         (loc    (vl-echar->loc echar1))

         ((when (mbe :logic (zp n)
                     :exec (= n 0)))
          (mv (cw "Preprocessor error (~s0): ran out of steps. Macro ~
                   expansion or file inclusion loop?")
              defines acc echars state))

; Preliminaries.  We need to be sure to treat strings, escaped identifiers, and
; comments atomically.  For instance, we don't want to look at a string like
; "looks like an `endif to me" and think that we have just read an `endif.

         ((when (eql char1 #\"))
          ;; Start of a string literal
          (b* (((mv string prefix remainder) (vl-read-string echars)))
            (if (not string)
                ;; it already printed a warning, so we don't use cw.
                (mv nil defines acc echars state)
              (vl-preprocess-loop remainder defines istack activep include-dirs
                                  (if activep (revappend prefix acc) acc)
                                  n state))))

         ((when (eql char1 #\\))
          ;; Start of an escaped identifier
          (b* (((mv name prefix remainder) (vl-read-escaped-identifier echars)))
            (if (not name)
                (mv (cw "Preprocessor error (~s0): stray backslash?~%"
                        (vl-location-string (vl-echar->loc (car echars))))
                    defines acc echars state)
              (vl-preprocess-loop remainder defines istack activep include-dirs
                                  (if activep (revappend prefix acc) acc)
                                  n state))))

         ((when (and (eql char1 #\/)
                     (consp (cdr echars))
                     (eql (vl-echar->char (second echars)) #\/)))
          ;; Start of a one-line comment

; SPECIAL VL EXTENSION.
;
; We decided we wanted a way to have code that only VL sees and that other
; tools see as comments.  So, if we see a comment of the form
;
;   //+VL...\newline
;
; Then in the preprocessor we remove the //+VL part and just leave "..." in the
; character stream.
;
; We wanted a shorthand for //+VL (* FOO *).  So, we say that //@VL FOO is
; equivalent to this.  We then decided that it should be permitted to put
; comments after the attributes, so as a special convenience we recognize:
;
;    //@VL FOO // comment goes here    , and
;    //@VL FOO /* comment starts here...
;
; And only read up to the start of the comment.  In other words, the above
; expand into
;
;    (* FOO *) // comment goes here    , and
;    (* FOO *) /* comment start here...
;
; respectively.

          (if (vl-matches-string-p "@VL" (cddr echars))
              (b* (((mv atts-text remainder)
                    ;; Figure out how much text we want to read for the attributes...
                    (b* (((mv & prefix remainder) (vl-read-until-literal *nls* (nthcdr 5 echars)))
                         ((mv comment1p pre-comment1 post-comment1)
                          (vl-read-until-literal "//" prefix))
                         ((mv comment2p pre-comment2 post-comment2)
                          (vl-read-until-literal "/*" prefix)))
                      (cond ((and comment1p comment2p)
                             (if (< (len pre-comment1) (len pre-comment2))
                                 (mv pre-comment1 (append post-comment1 remainder))
                               (mv pre-comment2 (append post-comment2 remainder))))
                            (comment1p
                             (mv pre-comment1 (append post-comment1 remainder)))
                            (comment2p
                             (mv pre-comment2 (append post-comment2 remainder)))
                            (t
                             (mv prefix remainder)))))
                   (atts (append (vl-echarlist-from-str "(*")
                                 atts-text
                                 (vl-echarlist-from-str "*)"))))
                ;; We leave the atts in the preprocessor's input stream so
                ;; that, e.g., defines can still get expanded in them.
                (vl-preprocess-loop (append atts remainder)
                                    defines istack activep include-dirs
                                    acc (- n 1) state))

            ;; Else, not a //@VL comment
            (b* (((mv & prefix remainder) (vl-read-until-literal *nls* (cddr echars)))
                 ((when (vl-matches-string-p "+VL" prefix))
                  ;; The // part is already gone, strip off the +VL part and
                  ;; leave it in the preprocessor's input stream, as above.
                  (vl-preprocess-loop (append (nthcdr 3 prefix) remainder)
                                      defines istack activep include-dirs
                                      acc (- n 1) state))
                 ;; Else, regular comment instead of //+VL or //@VL comment, so
                 ;; put the slashes back and don't try to preprocess it any more.
                 (prefix (list* (first echars) (second echars) prefix)))
              (vl-preprocess-loop remainder defines istack activep include-dirs
                                  (if activep (revappend prefix acc) acc)
                                  n state))))

         ((when (and (eql char1 #\/)
                     (consp (cdr echars))
                     (eql (vl-echar->char (second echars)) #\*)))
          ;; Start of a block comment.

; SPECIAL VL EXTENSION.  We do the same thing for /*+VL...*/, converting it into
; "..." here during preprocessing, and for /*@VL...*/, converting it into (*...*)
; We don't do anything special to support comments within the /*@VL ... */ form,
; since this is mainly intended for inline things

          (b* (((mv successp prefix remainder) (vl-read-through-literal "*/" (cddr echars)))
               ((unless successp)
                (mv (cw "Preprocessor error (~s0): block comment is never closed.~%"
                        (vl-location-string loc))
                    defines acc echars state))

               ((when (vl-matches-string-p "+VL" prefix))
                ;; The /* part is already gone.  Strip off "+VL" and "*/", and put the
                ;; comment's body into the input stream, as for //+VL above.
                (b* ((body (butlast (nthcdr 3 prefix) 2)))
                  (vl-preprocess-loop (append body remainder)
                                      defines istack activep include-dirs
                                      acc (- n 1) state)))

               ((when (vl-matches-string-p "@VL" prefix))
                ;; The /* part is gone.  Strip off "@VL" and "*/"; add "(*" and "*)",
                ;; and put the body into the input stream, as for //@VL above.
                (b* ((body (append (vl-echarlist-from-str "(*")
                                   (butlast (nthcdr 3 prefix) 2)
                                   (vl-echarlist-from-str "*)"))))
                  (vl-preprocess-loop (append body remainder)
                                      defines istack activep include-dirs
                                      acc (- n 1) state)))

               ;; Else, not a +VL or @VL comment, so put the /* back, and put
               ;; the prefix into the acc becuase we're done preprocessing this
               ;; comment.
               (prefix (list* (first echars) (second echars) prefix)))
            (vl-preprocess-loop remainder defines istack activep include-dirs
                                (if activep (revappend prefix acc) acc)
                                n state)))


         ((when (not (eql char1 #\`)))
          ;; Any regular character.  Accumulate or discard, per activep.
          (vl-preprocess-loop (cdr echars) defines istack activep include-dirs
                              (if activep (cons (car echars) acc) acc)
                              n state))

; Otherwise we just found a legitimate grave character which isn't inside a
; string literal or comment or anything.  We need to handle some compiler
; directive.

         ((mv & remainder)
          (vl-read-while-whitespace (cdr echars)))

         ((mv directive prefix remainder)
          (vl-read-identifier remainder))

         ((when (not directive))
          (mv (cw "Preprocessor error (~s0): stray ` character.~%"
                  (vl-location-string loc))
              defines acc echars state))

         ((when (not (vl-is-compiler-directive-p directive)))

; A macro usage like `foo.  The defines table stores the macro text in order,
; so we can essentially revappend it into the accumulator.

          (if (not activep)
              ;; Subtle.  Never try to expand macros in inactive sections,
              ;; because it is legitimate for them to be undefined.
              (vl-preprocess-loop remainder defines istack activep include-dirs
                                  acc n state)

            (let ((lookup (vl-lookup-in-defines directive defines)))
              (if (not lookup)
                  (mv (cw "Preprocessor error (~s0): `~s1 is not defined.~%"
                          (vl-location-string loc) directive)
                      defines acc echars state)
                (let* ((text (cdr lookup))
                       ;; Subtle.  If we just inserted the echars stored in the
                       ;; defines table, then locations on these characters would
                       ;; refer to their original position in the file.  This
                       ;; might lead to confusing error messages, telling you
                       ;; that something is wrong and showing you line numbers
                       ;; for a `define that looks just fine.  So instead, we
                       ;; change all of the locations for the inserted text to
                       ;; point at the grave character for the macro usage.  That
                       ;; is, if `foo occurs on line 37 from characters 5 through
                       ;; 8, then every character of foo's expansion is said to
                       ;; be located at 37:5.
                       (insert (vl-change-echarlist-locations text loc)))

                  ;; Subtle.  Variables in `define are lazy, e.g., if I first
                  ;; `define foo to be 3, then `define bar to be `foo, then
                  ;; redefine `foo to be 4, then the value of `bar should also be
                  ;; 4.  To accomplish this, we need to make sure that the
                  ;; expansion, "insert", is added not to the accumulator but
                  ;; instead to the list of echars we are processing, namely
                  ;; remainder.  This does not always terminate!
                  (vl-preprocess-loop (append insert remainder)
                                      defines istack activep include-dirs
                                      acc
                                      (- (lnfix n) 1)
                                      state))))))

         ((when (eql (vl-echar->char (car prefix)) #\\))
          ;; We explicitly disallow `\define, `\ifdef, etc.
          (mv (cw "Preprocessor error (~s0): we do not allow the use of \~s1.~%"
                  (vl-location-string loc) directive)
              defines acc echars state))

         ((when (or (equal directive "define")
                    (equal directive "centaur_define")))
          ;; CENTAUR EXTENSION: we also support centaur_define
          (b* (((mv successp new-defines remainder)
                (vl-process-define loc remainder defines activep))
               ((unless successp)
                (mv nil defines acc echars state)))
            (vl-preprocess-loop remainder new-defines istack activep include-dirs
                                acc n state)))

         ((when (equal directive "undef"))
          (b* (((mv successp new-defines remainder)
                (vl-process-undef loc remainder defines activep))
               ((unless successp)
                (mv nil defines acc echars state)))
            (vl-preprocess-loop remainder new-defines istack activep include-dirs
                                acc n state)))

         ((when (or (equal directive "ifdef")
                    (equal directive "ifndef")
                    (equal directive "elsif")))
          (b* (((mv successp new-istack new-activep remainder)
                (vl-process-ifdef loc directive remainder defines istack activep))
               ((unless successp)
                (mv nil defines acc echars state)))
            (vl-preprocess-loop remainder defines new-istack new-activep include-dirs
                                acc n state)))

         ((when (equal directive "else"))
          (b* (((mv successp new-istack new-activep)
                (vl-process-else loc istack activep))
               ((unless successp)
                (mv nil defines acc echars state)))
            (vl-preprocess-loop remainder defines new-istack new-activep include-dirs
                                acc n state)))

         ((when (equal directive "endif"))
          (b* (((mv successp new-istack new-activep)
                (vl-process-endif loc istack activep))
               ((unless successp)
                (mv nil defines acc echars state)))
            (vl-preprocess-loop remainder defines new-istack new-activep include-dirs
                                acc n state)))

         ((when (equal directive "include"))
          (b* (((unless activep)
                ;; Don't even do anything, we'll read the string literal next
                ;; and ignore it since we're not in an active section.  This
                ;; seems to be the right behavior: both NCVerilog and
                ;; Verilog-XL allow things like
                ;;
                ;;   `ifdef not_defined
                ;;     `include 5
                ;;   `endif
                ;;
                ;; but they complain if you do something like
                ;;
                ;;   `ifdef not_defined
                ;;     `include "foo
                ;;   `endif
                ;;
                ;; where the string literal isn't closed.  So, the behavior
                ;; seems to just be, ignore the include token and continue
                ;; ignoring whatever comes after it.
                (vl-preprocess-loop remainder defines istack activep include-dirs
                                    acc n state))

               ;; Else, we're in an active section, so read the filename try to
               ;; carry out the inclusion.
               ((mv filename ?prefix remainder) (vl-read-include remainder))

               ((unless filename)
                ;; Already warned.
                (mv nil defines acc echars state))

               ((mv realfile state) (vl-find-file filename include-dirs state))
               ((unless realfile)
                (mv (cw "Preprocessor error (~s0): unable to find ~s1.  The ~
                         include directories are ~&2."
                        (vl-location-string loc) filename include-dirs)
                    defines acc echars state))

               ((mv contents state)
                (cwtime (vl-read-file (string-fix realfile) state)
                        :mintime 1/2))
               ((when (stringp contents))
                (mv (cw "Preprocessor error (~s0): unable to read ~s1."
                        (vl-location-string loc) realfile)
                    defines acc echars state)))

            (vl-preprocess-loop
             ;; We could perhaps avoid this append with two recursive calls,
             ;; but we'll have to modify vl-preprocess-loop to additionally
             ;; return the updated istack and activep.
             (append contents remainder) defines istack activep include-dirs
             acc (- n 1) state)))

         ((when (equal directive "timescale"))
          (b* (((mv prefix remainder) (vl-read-timescale remainder))
               ((unless prefix)
                (mv nil defines acc echars state)))
            ;; BOZO maybe add a note that we are ignoring timescale?
            (vl-preprocess-loop remainder defines istack activep include-dirs
                                acc n state)))

         ((when (or (equal directive "celldefine")
                    (equal directive "endcelldefine")
                    (equal directive "resetall")))
          ;; BOZO maybe add a note that we are ignoring these directives?
          (vl-preprocess-loop remainder defines istack activep include-dirs
                              acc n state)))

      (mv (cw "Preprocessor error (~s0): we do not support ~s1.~%"
              (vl-location-string loc) directive)
          defines acc echars state)))

  (local (in-theory (enable vl-preprocess-loop)))

  ;; Speed hint
  (local (in-theory (disable ACL2::OPEN-SMALL-NTHCDR
                             CONSP-UNDER-IFF-WHEN-TRUE-LISTP
                             ACL2::NTHCDR-WITH-LARGE-INDEX
                             VL-MATCHES-STRING-P-WHEN-ACL2-COUNT-ZERO
                             acl2::nthcdr-append
                             acl2::consp-butlast
                             acl2::len-when-prefixp
                             string-fix
                             stringp-when-true-listp
                             CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP
                             hons-assoc-equal
                             (:TYPE-PRESCRIPTION REMAINDER-OF-VL-READ-UNTIL-LITERAL)
                             acl2::revappend-removal
                             revappend
                             )))

  (local (set-default-hints
          ;; I think we might be hitting ACL2's heuristics on not opening up
          ;; functions when it would introduce too many ifs, so we need this to
          ;; tell it to really go ahead and open up the function.
          '('(:expand ((:free (activep) (vl-preprocess-loop echars defines istack activep include-dirs acc n state)))))))

  (defthm booleanp-of-vl-preprocess-loop-success
    (booleanp (mv-nth 0 (vl-preprocess-loop echars defines istack activep include-dirs
                                            acc n state)))
    :rule-classes :type-prescription)

  (defthm state-p1-of-vl-preprocess-loop
    (let ((ret (vl-preprocess-loop echars defines istack activep include-dirs acc n state)))
      (implies (force (state-p1 state))
               (state-p1 (mv-nth 4 ret)))))

  (defthm true-listp-of-vl-preprocess-loop-result
    (let ((ret (vl-preprocess-loop echars defines istack activep include-dirs acc n state)))
      (equal (true-listp (mv-nth 2 ret))
             (true-listp acc))))

  (defthm true-listp-of-vl-preprocess-loop-remainder
    (let ((ret (vl-preprocess-loop echars defines istack activep include-dirs acc n state)))
      (equal (true-listp (mv-nth 3 ret))
             (true-listp echars))))

  (defthmd no-remainder-of-vl-preprocess-loop-on-success
    (let ((ret (vl-preprocess-loop echars defines istack activep include-dirs acc n state)))
      (implies (and (mv-nth 0 ret)
                    (force (true-listp echars)))
               (not (mv-nth 3 ret)))))

  (defthm vl-preprocess-loop-basics
    (let ((ret (vl-preprocess-loop echars defines istack activep include-dirs acc n state)))
      (implies (and (force (vl-echarlist-p echars))
                    (force (true-listp echars))
                    (force (vl-defines-p defines))
                    (force (vl-istack-p istack))
                    (force (booleanp activep))
                    (force (string-listp include-dirs))
                    (force (vl-echarlist-p acc))
                    (force (state-p1 state)))
               (and (vl-defines-p (mv-nth 1 ret))
                    (vl-echarlist-p (mv-nth 2 ret))
                    (vl-echarlist-p (mv-nth 3 ret)))))))




(defsection vl-preprocess

  (defconst *vl-preprocess-clock*
    ;; This is a really big number and is a fixnum on OpenMCL.  If there is no
    ;; loop, it is hard to imagine ever hitting this; each expansion of a
    ;; legitimate macro will require some consing, so we will almost certainly
    ;; run out of memory before running out of clock.
    (expt 2 59))

  (defund vl-safe-previous-n (n acc)
    ;; Used only for error reporting
    (declare (xargs :guard (and (natp n)
                                (true-listp acc))))
    (reverse (take (min (nfix n) (len acc)) acc)))

  (defund vl-safe-next-n (n x)
    ;; Used only for error reporting
    (declare (xargs :guard (and (natp n)
                                (true-listp x))))
    (take (min (nfix n) (len x)) x))

  (defthm vl-echarlist-p-of-vl-safe-previous-n
    (implies (vl-echarlist-p acc)
             (vl-echarlist-p (vl-safe-previous-n n acc)))
    :hints(("Goal" :in-theory (enable vl-safe-previous-n))))

  (defthm vl-echarlist-p-of-vl-safe-next-n
    (implies (vl-echarlist-p acc)
             (vl-echarlist-p (vl-safe-next-n n acc)))
    :hints(("Goal" :in-theory (enable vl-safe-next-n))))

  (defund vl-preprocess (echars defines include-dirs state)
    "Returns (MV SUCCESSP DEFINES NEW-ECHARS STATE)"
    (declare (xargs :guard (and (vl-echarlist-p echars)
                                (true-listp echars)
                                (vl-defines-p defines)
                                (string-listp include-dirs))
                    :stobjs state))
    ;; Note: keep in sync with optimized version, below.
    (b* (((mv successp defines acc remainder state)
          (vl-preprocess-loop echars defines
                              nil                   ;; istack
                              t                     ;; activep
                              include-dirs          ;; include-dirs
                              nil                   ;; acc
                              *vl-preprocess-clock* ;; n
                              state))
         ((when successp)
          (mv successp defines (reverse acc) state)))
      (mv (cw "[[ Previous  ]]: ~s0~%~
               [[ Remaining ]]: ~s1~%"
              (vl-echarlist->string (vl-safe-previous-n 50 acc))
              (vl-echarlist->string (vl-safe-next-n 50 remainder)))
          defines
          nil
          state)))

  (local (in-theory (enable vl-preprocess)))

  (defmvtypes vl-preprocess (booleanp nil true-listp nil))

  (defthm state-p1-of-vl-preprocess
    (let ((ret (vl-preprocess echars defines include-dirs state)))
      (implies (force (state-p1 state))
               (state-p1 (mv-nth 3 ret)))))

  (defthm vl-preprocess-basics
    (let ((ret (vl-preprocess echars defines include-dirs state)))
      (implies (and (force (vl-echarlist-p echars))
                    (force (true-listp echars))
                    (force (vl-defines-p defines))
                    (force (string-listp include-dirs))
                    (force (state-p1 state)))
               (and (vl-defines-p   (mv-nth 1 ret))
                    (vl-echarlist-p (mv-nth 2 ret))))))

  (defttag vl-optimize)
  (progn!
   ;; Nreverse optimization for success case.
   (set-raw-mode t)
   (setf (gethash 'vl-preprocess-loop ACL2::*never-profile-ht*) t)
   (defun vl-preprocess (echars defines include-dirs state)
     (b* (((mv successp defines acc remainder state)
           (vl-preprocess-loop echars defines
                               nil                   ;; istack
                               t                     ;; activep
                               include-dirs          ;; include-dirs
                               nil                   ;; acc
                               *vl-preprocess-clock* ;; n
                               state))
          ((when successp)
           (mv successp defines (reverse acc) state)))
       (mv (cw "[[ Previous  ]]: ~s0~%~
                [[ Remaining ]]: ~s1~%"
               (vl-echarlist->string (vl-safe-previous-n 50 acc))
               (vl-echarlist->string (vl-safe-next-n 50 remainder)))
           defines
           nil
           state))))
  (defttag nil))

