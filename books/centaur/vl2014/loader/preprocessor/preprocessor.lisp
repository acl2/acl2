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
(include-book "defines")
(include-book "print-defines")
(include-book "../filemap")
(include-book "../../util/cwtime")
(include-book "../read-file")
(include-book "../find-file")
(include-book "../lexer/lexer") ;; to identify string boundaries, escaped ids, etc.
(local (include-book "../../util/arithmetic"))

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
                           acl2::append-when-not-consp
                           acl2::append-of-cons
                           acl2::true-listp-append
                           (:type-prescription true-listp)
                           )))

(local (in-theory (disable ;ACL2-COUNT-OF-VL-READ-UNTIL-END-OF-DEFINE-WEAK
                           hons-assoc-equal
                           acl2::CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP
                           acl2::STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP
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
these questions we have sometimes just given test cases to simulators such as
Verilog-XL, NCVerilog, and VCS.  This is not a very satisfying state of
affairs.</p>

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

<p>We place some (reasonable) restrictions on the above macros.  For instance,
we do not allow definitions to include most compiler directives&mdash;we allow
the body of @('`foo') to include @('`bar'), but not @('`endif').  These
restrictions are intended to ensure that we do not \"mispreprocess\" anything.
See @(see preprocessor-ifdef-minutia) for some details and additional
discussion.</p>

<p>We also have pretty good support for @('`include') directives.  This is
quite underspecified, and we have basically tried to mimic the behavior of
Verilog-XL and NCVerilog.  See also @(see preprocessor-include-minutia).</p>


<h4>Ignored Directives</h4>

<p>We also \"support\" certain directives by <b>ignoring</b> them.</p>

<ul>
 <li>@('`celldefine')</li>
 <li>@('`endcelldefine')</li>
 <li>@('`resetall')</li>
 <li>@('`timescale')</li>
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
 <li>@('`begin_keywords')</li>
 <li>@('`default_nettype')</li>
 <li>@('`end_keywords')</li>
 <li>@('`line')</li>
 <li>@('`pragma')</li>
 <li>@('`nounconnected_drive')</li>
 <li>@('`unconnected_drive')</li>
</ul>

<p>It might be good to ignore @('`begin_keywords \"1364-2005\"') and just cause
an error if a different set of keywords is requested.  We could also ignore
@('`end_keywords').  But trying to add anything more sophisticated than this
seems very tricky and messy.</p>

<p>It would be good to add proper support for @('`line').  Failing that, it
would be quite easy to just ignore it, like the other ignored directives.  We
should probably also ignore @('`pragma') directives, and this should be easy to
do.</p>

<p>It would be somewhat difficult to support @('`default_nettype') and
@('`unconnected_drive').  Probably the thing to do would be build a table of
when the declarations are made, and then use some trick like comment injection
to mark modules appropriately.  We would then have to change the @(see
make-implicit-wires) transform to consider the @('`default_nettype') for the
module, and probably use a separate transform to handle @('`unconnected_drive')
stuff.</p>")

(local (xdoc::set-default-parents preprocessor))

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

  :short "List of Verilog-2005 compiler directives."
  :long "<p>This list is taken directly from Section 19.  We do not support some of
these, but we need to recognize all of them so that we can complain when we
run into ones we don't support, etc.</p>

<p><b>Centaur Extension</b>.  We also add @('`centaur_define'), which we treat
exactly as @('`define').</p>")


(defxdoc preprocessor-ifdef-minutia
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
  :short "@('`ifdef') stack frame objects."
  :tag :vl-iframe

  ((initially-activep     booleanp :rule-classes :type-prescription)
   (some-thing-satisfiedp booleanp :rule-classes :type-prescription)
   (already-saw-elsep     booleanp :rule-classes :type-prescription))

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



(define vl-process-ifdef
  :short "Handler for @('ifdef'), @('ifndef'), and @('elsif') directives."
  ((loc       vl-location-p)
   (directive (member-equal directive '("ifdef" "ifndef" "elsif")))
   (echars    vl-echarlist-p)
   (defines   vl-defines-p)
   (istack    vl-istack-p)
   (activep   booleanp))
  :returns
  (mv (successp)
      (new-istack vl-istack-p :hyp (and (force (vl-istack-p istack))
                                        (force (booleanp activep))))
      (new-activep booleanp :hyp (and (force (booleanp activep))
                                      (force (vl-istack-p istack))))
      (remainder vl-echarlist-p :hyp (force (vl-echarlist-p echars))))

  :long "<p>We assume that we have just read @('`directive') from @('echars').
We need to read the identifier that should follow this directive, look it up in
the defines table, and make the appropriate changes to the @('istack') and
@('activep').</p>"

  (b* (((mv & remainder)      (vl-read-while-whitespace echars))
       ((mv name & remainder) (vl-read-identifier remainder))

       ((unless name)
        (mv (cw "Preprocessor error (~s0): found an `~s1 without an identifier.~%"
                (vl-location-string loc) directive)
            istack activep echars))

       ((when (vl-is-compiler-directive-p name))
        ;; Special prohibition of compiler directive names in ifdefs, ifndefs,
        ;; etc.  See :xdoc preprocessor-ifdef-minutia for why.
        (mv (cw "Preprocessor error (~s0): cowardly refusing to permit `s1 ~s2.~%"
                (vl-location-string loc) directive name)
            istack activep echars))

       ((when (equal directive "ifdef"))
        (let* ((this-satisfiedp (consp (vl-find-define name defines)))
               (new-iframe      (vl-iframe activep this-satisfiedp nil))
               (new-istack      (cons new-iframe istack))
               (new-activep     (and activep this-satisfiedp)))
          (mv t new-istack new-activep remainder)))

       ((when (equal directive "ifndef"))
        (let* ((this-satisfiedp (not (vl-find-define name defines)))
               (new-iframe      (vl-iframe activep this-satisfiedp nil))
               (new-istack      (cons new-iframe istack))
               (new-activep     (and activep this-satisfiedp)))
          (mv t new-istack new-activep remainder)))

       ((when (atom istack))
        (mv (cw "Preprocessor error (~s0): found an `elsif, but no ifdef or ~
                 ifndef is open.~%"
                (vl-location-string loc))
            istack activep echars))

       ((when (vl-iframe->already-saw-elsep (car istack)))
        (mv (cw "Preprocessor error (~s0): found an `elsif, but we have ~
                 already seen `else.~%"
                (vl-location-string loc))
            istack activep echars))

       (this-satisfiedp   (consp (vl-find-define name defines)))
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
    (mv t new-istack new-activep remainder))
  ///
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


(define vl-process-else
  :short "Handler for @('else') directives."
  ((loc     vl-location-p)
   (istack  vl-istack-p)
   (activep booleanp))
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (new-istack vl-istack-p :hyp (force (vl-istack-p istack)))
      (new-activep booleanp :rule-classes :type-prescription
                   :hyp (booleanp activep)))
  (b* (((when (atom istack))
        (mv (cw "Preprocessor error (~s0): found an `else, but no ~
                  ifdef/ifndef is open.~%"
                (vl-location-string loc))
            istack activep))
       ((when (vl-iframe->already-saw-elsep (car istack)))
        (mv (cw "Preprocessor error (~s0): found an `else, but we have ~
                 already seen an `else.~%"
                (vl-location-string loc))
            istack activep))
       (iframe            (car istack))
       (prev-satisfiedp   (vl-iframe->some-thing-satisfiedp iframe))
       (initially-activep (vl-iframe->initially-activep iframe))
       (new-activep       (and initially-activep (not prev-satisfiedp)))
       (new-iframe        (make-vl-iframe
                           :initially-activep     initially-activep
                           :some-thing-satisfiedp t
                           :already-saw-elsep     t))
       (new-istack        (cons new-iframe (cdr istack))))
    (mv t new-istack new-activep)))


(define vl-process-endif
  :short "Handler for @('endif') directives."
  ((loc     vl-location-p)
   (istack  vl-istack-p)
   (activep booleanp))
  :returns
  (mv (successp   booleanp :rule-classes :type-prescription)
      (new-istack vl-istack-p
                  :hyp (force (vl-istack-p istack)))
      (new-activep booleanp :rule-classes :type-prescription
                   :hyp (booleanp activep)))
  (b* (((when (atom istack))
        (mv (cw "Preprocessor error (~s0): found an `endif, but no ifdef/ifndef ~
                 is open.~%"
                (vl-location-string loc))
            istack activep))
       (new-istack (cdr istack))
       (new-activep (vl-iframe->initially-activep (car istack))))
    (mv t new-istack (and new-activep t))))

(define vl-read-until-end-of-define
  :short "Read from @('`define') until the end of the line."
  ((echars vl-echarlist-p)
   (config vl-loadconfig-p))
  :returns
  (mv (successp  booleanp       :rule-classes :type-prescription)
      (prefix    vl-echarlist-p :hyp (force (vl-echarlist-p echars)))
      (remainder vl-echarlist-p :hyp (force (vl-echarlist-p echars))))
  :long "<p>This is really tricky!  See @(see preprocessor-ifdef-minutia).</p>

<p>The initial @('echars') are everything past the macro name, e.g., for:</p>

@({ `define foo blah... })

<p>the initial @('echars') will be @('[space]blah...'), and for</p>

@({ `define max(a,b) blah... })

<p>the initial @('echars') will be @('(a,b) blah...').  NCVerilog allows
newlines within the macro arguments, e.g., it allows you to write things
like</p>

@({
     `define sum(a,
                    b) a+b
})

<p>But VCS rejects this.  I think it's reasonable to reject this, too, so we
basically just read the whole line, then split it up into any arguments versus
non-arguments pieces.</p>"

  (b* (((when (atom echars))
        ;; We allow macros to be defined on the last line of the file;
        ;; "implicitly inserting a newline" for them.
        (mv t nil echars))
       (char1 (vl-echar->char (first echars)))

       ((when (eql char1 #\Newline))
        ;; Successful end of macro text.
        (mv t nil echars))

       ((when (eql char1 #\`))
        ;; We allow user-defines like `foo and `bar, but not built-ins like
        ;; `define and `endif.
        (b* (((mv name prefix remainder) (vl-read-identifier (cdr echars)))
             ((unless name)
              (mv (cw "Preprocessor error (~s0): no name following ~
                       back-quote/grave character (`).~%"
                      (vl-location-string (vl-echar->loc (car echars))))
                  nil echars))
             ((when (vl-is-compiler-directive-p name))
              (mv (cw "Preprocessor error (~s0): we cowardly do not allow ~
                       `~s1 in defines.~%"
                      (vl-location-string (vl-echar->loc (car echars)))
                      name)
                  nil echars))
             ((mv successp text remainder)
              (vl-read-until-end-of-define remainder config))
             ((unless successp)
              (mv nil nil echars)))
          (mv t
              (cons (car echars) (append prefix text))
              remainder)))

       ((when (eql char1 #\"))
        ;; Skip over string literals so we aren't confused by graves, etc.
        (b* (((mv string prefix remainder)
              (vl-read-string echars (vl-lexstate-init config)))
             ((unless string)
              (mv nil nil echars))
             ((mv successp text remainder)
              (vl-read-until-end-of-define remainder config))
             ((unless successp)
              (mv nil nil echars)))
          (mv t (append prefix text) remainder)))

       ((when (eql char1 #\\))
        (b* (((when (vl-matches-string-p "//" (cdr echars)))
              (mv (cw "Preprocessor error (~s0): we cowardly do not allow ~
                       '\//' in defines.~%"
                      (vl-location-string (vl-echar->loc (car echars))))
                  nil echars))
             ((when (vl-matches-string-p "/*" (cdr echars)))
              (mv (cw "Preprocessor error (~s0): we cowardly do not allow ~
                       '\/*' in defines.~%"
                      (vl-location-string (vl-echar->loc (car echars))))
                  nil echars))
             ((when (vl-matches-string-p *nls* (cdr echars)))

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

              (b* (((mv successp text remainder)
                    (vl-read-until-end-of-define (cddr echars) config))
                   ((unless successp)
                    (mv nil nil echars)))
                (mv t
                    (cons (change-vl-echar (second echars) :char #\Space) text)
                    remainder)))

             ;; Skip over escaped identifiers so we aren't confused by graves,
             ;; etc.
             ((mv name prefix remainder)
              (vl-read-escaped-identifier echars))
             ((unless name)
              (mv (cw "Preprocessor error (~s0): stray backslash?~%"
                      (vl-location-string (vl-echar->loc (car echars))))
                  nil echars))
             ((mv successp text remainder)
              (vl-read-until-end-of-define remainder config))
             ((unless successp)
              (mv nil nil echars)))
          (mv t (append prefix text) remainder)))

       ((when (eql char1 #\/))
        (cond
         ((vl-matches-string-p "//" echars)
          ;; start of a single-line comment; read until end of line.
          (b* (((mv successp prefix remainder)
                (vl-read-until-literal *nls* echars))
               ((unless successp)
                ;; This actually just means the file ends with something like
                ;; "`define foo ... // blah blah" and there is no newline.
                ;; That's fine.  The comment is to be excluded from the
                ;; expansion.
                (mv t nil remainder))
               ((when (and (consp prefix)
                           (eql (vl-echar->char (car (last prefix))) #\\)))
                (mv (cw "Preprocessor error (~s0): we cowardly do not allow ~
                         single-line comments inside defines to end with \.~%"
                        (vl-location-string (vl-echar->loc (car echars))))
                    nil echars)))
            ;; Single-line comments are to be excluded; nothing more is to be
            ;; read.
            (mv t nil remainder)))

         ((vl-matches-string-p "/*" echars)
          (b* (((mv successp prefix remainder)
                (vl-read-through-literal "*/" (cddr echars)))
               ((unless successp)
                (mv (cw "Preprocessor error (~s0): block comment is never ~
                         closed.~%"
                        (vl-location-string (vl-echar->loc (car echars))))
                    nil echars))
               ((when (member #\Newline (vl-echarlist->chars prefix)))
                (mv (cw "Preprocessor error (~s0): block comment inside a ~
                         define is not closed before end of line.~%"
                        (vl-location-string (vl-echar->loc (car echars))))
                    nil echars))
               ((mv successp text remainder)
                (vl-read-until-end-of-define remainder config))
               ((unless successp)
                (mv nil nil echars)))
            (mv t (append (list* (first echars) (second echars) prefix)
                          text)
                remainder)))

         (t
          ;; Regular division operator -- treat it as a regular character
          (b* (((mv successp text remainder)
                (vl-read-until-end-of-define (cdr echars) config))
               ((unless successp)
                (mv nil nil echars)))
            (mv t (cons (car echars) text) remainder)))))

       ;; Else, some regular character
       ((mv successp text remainder)
        (vl-read-until-end-of-define (cdr echars) config))
       ((unless successp)
        (mv nil nil echars)))
    (mv t (cons (car echars) text) remainder))
  ///
  (defthm true-listp-of-vl-read-until-end-of-define-prefix
    (true-listp (mv-nth 1 (vl-read-until-end-of-define echars config)))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-read-until-end-of-define-remainder
    (equal (true-listp (mv-nth 2 (vl-read-until-end-of-define echars config)))
           (true-listp echars))
    :rule-classes ((:rewrite)))

  (defthm acl2-count-of-vl-read-until-end-of-define-weak
    (<= (acl2-count (mv-nth 2 (vl-read-until-end-of-define echars config)))
        (acl2-count echars))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm acl2-count-of-vl-read-until-end-of-define-strong
    (implies (mv-nth 1 (vl-read-until-end-of-define echars config))
             (< (acl2-count (mv-nth 2 (vl-read-until-end-of-define echars config)))
                (acl2-count echars)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force))))))




(define vl-parse-define-formal-arguments
  ;; Match list_of_formal_arguments, also eating the close paren and returning
  ;; the remaining text after the close paren.
  :parents (vl-split-define-text)
  ((text         vl-echarlist-p "Text after the opening paren, or after some comma.")
   (config       vl-loadconfig-p)
   (starting-loc vl-location-p  "Context for error messages."))
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (formals  vl-define-formallist-p)
      (body     vl-echarlist-p "Remaining characters after the closing paren."
                :hyp (force (vl-echarlist-p text))))
  (b* (((when (atom text))
        (mv (cw "Preprocessor error (~s0): `define arguments are not closed.~%"
                (vl-location-string starting-loc))
            nil nil))
       ;; This is a mess -- without a lexer we're always having to eat whitespace.
       ((mv ?ws rest) (vl-read-while-whitespace text))
       ((mv id rest)  (vl-read-simple-identifier rest))
       ((unless id)
        (mv (cw "Preprocessor error (~s0): invalid `define argument name~%"
                (vl-location-string (vl-echar->loc (car text))))
            nil nil))

       (name1 (vl-echarlist->string id))
       ;; Prohibit using keywords as arguments.  Of course, the valid keywords
       ;; are governed by the Verilog edition... blaaah...
       ((when (vl-keyword-lookup name1 (vl-lexstate->kwdtable (vl-lexstate-init config))))
        (mv (cw "Preprocessor error (~s0): keyword ~s1 not permitted as `define argument~%"
                (vl-location-string (vl-echar->loc (car text)))
                name1)
            nil nil))

       ((mv ?ws rest) (vl-read-while-whitespace rest))
       ;; BOZO implement support for equal signs, default values... but that is
       ;; going to be nasty, complex rules about what's allowed.  For now just
       ;; skip it.
       (formal1 (make-vl-define-formal :name name1 :default ""))

       ((when (and (consp rest)
                   (eql (vl-echar->char (car rest)) #\))))
        ;; End of arguments, woohoo.  Eat final closing paren and we're done.
        (mv t (list formal1) (cdr rest)))

       ((unless (and (consp rest)
                     (eql (vl-echar->char (car rest)) #\,)))
        (mv (cw "Preprocessor error (~s0): expected next `define argument or end of arguments.~%"
                (vl-location-string (if (consp rest)
                                        (vl-echar->loc (car rest))
                                      ;; Blah, not quite right, probably close enough to be useful
                                      (vl-echar->loc (car text)))))
            nil nil))

       ;; Else, found a comma: eat it, recur, etc.
       (starting-loc (vl-echar->loc (car rest)))
       (rest         (cdr rest))
       ((mv rest-okp rest-formals body)
        (vl-parse-define-formal-arguments rest config starting-loc))
       ((unless rest-okp)
        ;; Already printed an error message.
        (mv nil nil nil))
       (formals (cons formal1 rest-formals)))
    (mv t formals body)))

(define vl-split-define-text
  :short "Split up the rest of a define line into macro arguments and macro text."
  ((text vl-echarlist-p "The text that occurs after @('`define foo'), perhaps
                         including any macro arguments such as @('(a,b)') in
                         the case of macros such as @('`define max(a,b) ...').")
   (config vl-loadconfig-p))
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (formals  vl-define-formallist-p)
      (body     vl-echarlist-p "Remaining characters after any macro arguments."
                :hyp (force (vl-echarlist-p text))))
  (b* (((unless (and (consp text)
                     (eql (vl-echar->char (car text)) #\()))
        ;; SystemVerilog-2012: Page 640: "If formal arguments are used [...]
        ;; the left parenthesis shall follow the text macro name immediately,
        ;; with no space in between."  Since we have no opening paren, this
        ;; macro does NOT have arguments, and all text belongs to the macro
        ;; itself.
        (mv t nil (vl-echarlist-fix text))))
    ;; Else, eat the opening paren and go do the actual parsing.
    (vl-parse-define-formal-arguments (cdr text) config (vl-echar->loc (car text)))))

(define vl-process-define
  :short "Handler for @('define') directives."

  ((loc     vl-location-p)
   (echars  vl-echarlist-p)
   (defines vl-defines-p)
   (activep booleanp)
   (config  vl-loadconfig-p))
  :returns
  (mv (successp)
      (new-defines vl-defines-p)
      (remainder   vl-echarlist-p :hyp (force (vl-echarlist-p echars))))

  :long "<p>We assume that @('`define') has just been read and @('echars') is
the text which comes right after the @('`define') directive.  We read the name
and text for this new macro definition, and update the defines table
appropriately if @('activep') is set.</p>"

  (b* ((defines (vl-defines-fix defines))
       ((mv & remainder)      (vl-read-while-whitespace echars))
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
        (vl-read-until-end-of-define remainder config))

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

       ((mv okp formals body) (vl-split-define-text text config))
       ((unless okp)
        ;; Error message was already printed, so we just need to return
        ;; failure.
        (mv nil defines remainder))

       (formal-names (vl-define-formallist->names formals))
       ((unless (uniquep formal-names))
        (mv (cw "Preprocessor error (~s0): `define ~s1 has repeats arguments ~&2."
                (vl-location-string loc) name (duplicated-members formal-names))
            defines echars))

       (new-def  (make-vl-define :name    name
                                 :formals formals
                                 :body    (vl-echarlist->string body)
                                 :loc     loc))

       (prev-def (vl-find-define name defines))
       (- (or (not prev-def)
              (b* ((new-str (str::trim (vl-define->body new-def)))
                   (old-str (str::trim (vl-define->body prev-def)))
                   ((when (equal new-str old-str))
                    ;; Don't warn, redefining it in exactly the same way, modulo
                    ;; whitespace.
                    t))
              (cw "Preprocessor warning: redefining ~s0:~% ~
                    - Was ~s1     // from ~s2~% ~
                    - Now ~s3     // from ~s4~%"
                  name
                  old-str
                  (vl-location-string (vl-define->loc prev-def))
                  new-str
                  (vl-location-string loc)))))

       (defines  (if prev-def
                     (vl-delete-define name defines)
                   defines))
       (defines  (vl-add-define new-def defines)))

    (mv t defines remainder))

  ///
  (defthm true-listp-of-vl-process-define-remainder
    (equal (true-listp (mv-nth 2 (vl-process-define loc echars defines activep config)))
           (true-listp echars)))

  (defthm acl2-count-of-vl-process-define
    (<= (acl2-count (mv-nth 2 (vl-process-define loc echars defines activep config)))
        (acl2-count echars))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm acl2-count-of-vl-process-define-strong
    (implies (mv-nth 0 (vl-process-define loc echars defines activep config))
             (< (acl2-count (mv-nth 2 (vl-process-define loc echars defines activep config)))
                (acl2-count echars)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force))))))


(define vl-parse-define-actual
  :parents (vl-expand-define)
  :short "Collect a single argument to a text macro, like @('`max(a+b, c)')."
  :long "<p>SystemVerilog-2012 gives the following grammar (Page 641, Syntax
22-3):</p>

@({
     text_macro_usage ::= text_macro_identifier [ '(' list_of_actual_arguments ')' ]

     list_of_actual_arguments ::= actual_argument { ',' actual_argument }

     actual_argument ::= expression
})

<p>But this last part is clearly total bullshit.  For instance on page 643 we
are told:</p>

<blockquote>\"However, one can define an empty text macro, say @('`EMPTY'), and
use that as an actual argument.  This will be substituted in place of the
formal argument and will be replaced by empty text after expansion of the empty
text macro.\"</blockquote>

<p>It seems very clear that the empty string is not an expression.  Moreover,
all of this discussion of the preprocessor seems quite deeply rooted in a
notion of textual substitution.  Accordingly, the idea that
@('actual_argument ::= expression') seems to be very much confusing different
levels of representation (e.g., expressions versus text) and just cannot be
correct at all.</p>

<p>That's a bummer because we need to allow <i>something</i> to occur in these
actuals, and that something could be some rather complicated piece of text.
Interestingly, both NCVerilog and VCS permit uses of macros such as:</p>

@({
   `define identity(a) a
   module foo;
     `identity(reg foo;)
   endmodule
})

<p>However they complain about too many macro arguments on examples such as:</p>

@({
    `identity(reg bar, baz;)
})

<p>Meanwhile they happily accept syntax such as:</p>

@({
    `identity(2 + {1'b0, 1'b1})
})

<p>On Page 641 of the spec, we find some hints about what might be permitted
here:</p>

<blockquote>\"Actual arguments and defaults shall not contain comma or right
parenthesis characters outside matched pairs of left and right parentheses
@('()'), square brackets @('[]'), braces @('{}'), double quotes @('\"'), or an
escaped identifier.\"</blockquote>

<p>This paragraph seems to suggest a kind of algorithm for deciding where the
actual text ends, roughly: keep track of matched pairs of these special
characters, be smart enough to recognize strings and escaped identifiers, and
stop when you see a comma or right parenthesis.</p>

<p>I implement such an algorithm here, but of course there is a great deal of
room for ambiguity and confusion here, so this may well not be at all correct.
The system tests (centaur/vl2014/systest) do try to test some tricky cases,
but there may well be mismatches left.</p>"
  ((name   stringp          "Name of macro being expanded, e.g., @('max'), for error messages.")
   (echars vl-echarlist-p   "Text we're parsing, initially follows an open paren or comma.")
   (config vl-loadconfig-p)
   (loc    vl-location-p    "Location information in case of error messages.")
   (stk    character-listp  "Stack of open paren/bracket/brace characters.")
   (acc    vl-echarlist-p   "Text we've matched so far."))
  :returns
  (mv (successp  booleanp :rule-classes :type-prescription "Was there any error?")
      (morep     booleanp :rule-classes :type-prescription "Is this the last actual?")
      (actual    stringp  :rule-classes :type-prescription "Contents of the actual as a string.")
      (remainder vl-echarlist-p "Remaining characters past the comma/closing paren."
                 :hyp (force (vl-echarlist-p echars))))
  (b* (((when (atom echars))
        ;; Error because we expect to eventually find a closing paren.
        (mv (cw "Preprocessor error (~s0): unexpected end of input while processing ~
                 arguments to `~s1." (vl-location-string loc) name)
            nil "" echars))

       (char1 (vl-echar->char (car echars)))
       (loc1  (vl-echar->loc  (car echars)))

       ((when (eql char1 #\"))
        ;; BOZO this isn't quite right -- it assumes Verilog-2012 string
        ;; literal syntax even if we're trying to parse Verilog-2005 code.  Fix
        ;; it if we ever care.
        (b* (((mv str prefix remainder) (vl-read-string echars (vl-lexstate-init config)))
             ((unless str)
              (mv (cw "Preprocessor error (~s0): bad string literal while processing ~
                       arguments to `~s1." (vl-location-string loc1) name)
                  nil "" echars))
             (acc (revappend prefix acc)))
          (vl-parse-define-actual name remainder config loc stk acc)))

       ((when (eql char1 #\\))
        (b* (((mv name prefix remainder) (vl-read-escaped-identifier echars))
             ((unless name)
              (mv (cw "Preprocessor error (~s0): stray backslash while processing ~
                       arguments to `~s1." (vl-location-string loc1) name)
                  nil "" echars))
             (acc (revappend prefix acc)))
          (vl-parse-define-actual name remainder config loc stk acc)))

       ((when (eql char1 #\/))
        ;; NCVerilog and VCS seem to skip over comments here, so we'll do the same...
        (b* (((when (vl-matches-string-p "//" echars))
              ;; start of a single-line comment; read until end of line.
              (b* (((mv successp ?prefix remainder)
                    (vl-read-until-literal *nls* (cddr echars)))
                   ((unless successp)
                    (mv (cw "Preprocessor error (~s0): unexpected EOF while reading ~
                             macro arguments to ~s1.~%" (vl-location-string loc1) name)
                        nil "" echars)))
                ;; It might be nice to preserve the comment.  On the other
                ;; hand, that would possibly replicate the comment in many
                ;; places.  I think it seems reasonable to just drop it.
                (vl-parse-define-actual name remainder config loc stk acc)))

             ((when (vl-matches-string-p "/*" echars))
              (b* (((mv successp ?prefix remainder)
                    (vl-read-through-literal "*/" (cddr echars)))
                   ((unless successp)
                    (mv (cw "Preprocessor error (~s0): block comment is never closed.~%"
                            (vl-location-string (vl-echar->loc (car echars))))
                        nil "" echars)))
                ;; As with single-line comments, we'll just drop the comment.
                (vl-parse-define-actual name remainder config loc stk acc))))

          ;; Otherwise, just an ordinary division operation, accumulate it as
          ;; usual, no effect on the stk.
          (vl-parse-define-actual name (cdr echars) config loc stk (cons (car echars) acc))))

       ((when (member char1 '(#\( #\[ #\{)))
        ;; Open bracket -- Fine, push it on the stack so we can balance it.
        (b* ((stk (cons char1 stk))
             (acc (cons (car echars) acc)))
          (vl-parse-define-actual name (cdr echars) config loc stk acc)))

       ((when (member char1 '(#\) #\] #\})))
        ;; Close bracket or paren...
        (b* (((when (and (eql char1 #\))
                         (atom stk)))
              ;; Closing right paren with no other brackets open means that we
              ;; have reached the end of the arguments.
              (mv t
                  nil ;; Closing paren means no more arguments!
                  (reverse (vl-echarlist->string acc))
                  (cdr echars)))
             ;; Otherwise, a closing bracket/paren/brace is only okay if a
             ;; matching opening bracket/paren/brace is already open.
             (matching-char (case char1 (#\) #\() (#\] #\[) (#\} #\{)))  ;; escape all the things
             ((unless (and (consp stk)
                           (eql (car stk) matching-char)))
              (mv (cw "Preprocessor error (~s0): unbalanced ~s1 vs. ~s2 in arguments to `~s3."
                      (vl-location-string loc1)
                      (implode (list matching-char))
                      (implode (list char1))
                      name)
                  nil "" echars))
             ;; Else, fine, it was balanced
             (stk (cdr stk))
             (acc (cons (car echars) acc)))
          (vl-parse-define-actual name (cdr echars) config loc stk acc)))

       ((when (and (atom stk)
                   (eql char1 #\,)))
        ;; Comma encountered with no open braces/parents/brackets means that we
        ;; have reached the end of this argument
        (mv t
            t ;; comma means there are more arguments
            (reverse (vl-echarlist->string acc))
            (cdr echars))))

    ;; If we get here, then it wasn't any special character or it was a comma
    ;; that happened to be in a bracket/paren/brace region, so we want to just
    ;; accumulate it anyway.  Keep reading this actual.
    (vl-parse-define-actual name (cdr echars) config loc stk (cons (car echars) acc)))
  ///
  (defthm acl2-count-of-vl-parse-define-actual
    (b* (((mv successp ?morep ?actual remainder)
          (vl-parse-define-actual name echars config loc stk acc)))
      (implies successp
               (< (acl2-count remainder)
                  (acl2-count echars))))
    :rule-classes ((:rewrite) (:linear))))


(define vl-parse-define-actuals
  :parents (vl-expand-define)
  :short "Collect the arguments to a macro, like @('`max(a+b, c)')."
  ((name   stringp          "Name of macro being expanded, e.g., @('max'), for error messages.")
   (echars vl-echarlist-p   "Text that follows the initial open paren, or that follows a comma.")
   (config vl-loadconfig-p)
   (loc    vl-location-p    "Location information in case of error messages."))
  :returns
  (mv (successp  booleanp :rule-classes :type-prescription)
      (actuals   string-listp)
      (remainder vl-echarlist-p
                 "Remainder of the input stream after eating all the actuals and also
                  the closing paren."
                 :hyp (force (vl-echarlist-p echars))))
  (b* (((mv successp morep actual1 echars)
        (vl-parse-define-actual name echars config loc nil nil))
       ((unless successp)
        ;; Already printed an error message.
        (mv nil nil echars))
       ((unless morep)
        ;; That was the last formal.  We already ate the closing paren.
        (mv t (list actual1) echars))
       ((mv successp rest-actuals echars)
        (vl-parse-define-actuals name echars config loc))
       ((unless successp)
        (mv nil nil echars)))
    (mv t (cons actual1 rest-actuals) echars)))

(define vl-check-remaining-formals-all-have-defaults
  ((x    vl-define-formallist-p)
   (name stringp       "Name of macro being expanded, context for error messages.")
   (loc  vl-location-p "Location of macro being expanded, context for error messages."))
  (b* (((when (atom x))
        t)
       ((vl-define-formal x1) (car x))
       (has-default-p (not (equal "" (str::trim x1.default))))
       ((unless has-default-p)
        (cw "Preprocessor error (~s0): too few arguments to ~s1 (no ~
             default value for ~s2)."
            (vl-location-string loc) name x1.name)))
    (vl-check-remaining-formals-all-have-defaults (cdr x) name loc)))

(define vl-line-up-define-formals-and-actuals
  ((formals vl-define-formallist-p)
   (actuals string-listp)
   (name stringp       "Name of macro being expanded, context for error messages.")
   (loc  vl-location-p "Location of macro being expanded, context for error messages."))
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (subst    (and (alistp subst)
                     (string-listp (alist-keys subst))
                     (string-listp (alist-vals subst)))))
  (b* (((when (atom formals))
        (if (atom actuals)
            ;; Ran out of formals and actuals at the same time.  That's fine,
            ;; no more substitution to create.
            (mv t nil)
          ;; Ran out of formals but still have actuals?  No sir, that's not ok.
          (mv (cw "Preprocessor error (~s0): too many arguments given to ~s1."
                  (vl-location-string loc) name)
              nil)))

       ((when (atom actuals))
        ;; SystemVerilog-2012, page 641.  "If fewer actual arguments are
        ;; specified than the number of formal arguments, then the defaults are
        ;; substituted for the additional formal arguments.  It shall be an
        ;; error if any of the remaining formal arguments does not have a
        ;; default specified."
        (if (vl-check-remaining-formals-all-have-defaults formals name loc)
            ;; Fine, pair them up.
            (mv t (pairlis$ (vl-define-formallist->names formals)
                            (vl-define-formallist->defaults formals)))
          ;; Already printed an error, this is just an error.
          (mv nil nil)))

       ((mv okp rest-subst)
        (vl-line-up-define-formals-and-actuals (cdr formals) (cdr actuals) name loc))
       ((unless okp)
        (mv nil nil))

       ;; SystemVerilog-2012 Page 641: "An actual argument may be empty or
       ;; white space only, in which case the formal argument is substituted by
       ;; the argument default if one is specified, or by nothing if no default
       ;; is specified.
       ((vl-define-formal formal1) (car formals))
       (actual1 (str::trim (car actuals)))
       (value1  (if (equal actual1 "")
                    (str::trim formal1.default)
                  actual1)))
    (mv t (cons (cons formal1.name value1) rest-subst))))

(define vl-substitute-into-macro-text
  ((body   vl-echarlist-p
           "Characters in the macro's body, which we recur through.")
   (subst  (and (alistp subst)
                (string-listp (alist-keys subst))
                (string-listp (alist-vals subst)))
           "The substitution being made, an alist binding formals to actuals.")
   (name   stringp
           "Name of the text macro being expanded, for error messages.")
   (loc    vl-location-p
           "Location of the text macro being expanded, for error messages and
            also becomes the new location for each character being created.")
   (config vl-loadconfig-p)
   (acc    vl-echarlist-p
           "Accumulated extended characters to be inserted into the file."))
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (acc      vl-echarlist-p
                "Accumulated characters, still in reverse order."
                :hyp (and (force (vl-echarlist-p body))
                          (force (vl-echarlist-p acc)))))

  :long "<p>This is very underspecified.  We need to minimally skip over things
like string literals.  We can at least assume that the @('body') was accepted
by @(see vl-read-until-end-of-define).  We try to do something reasonably
sensible.</p>"

  ;; Styled after vl-read-until-end-of-define.
  (b* (((when (atom body))
        (mv t acc))
       (char1 (vl-echar->char (first body)))

       ((when (eql char1 #\`))
        (b* (((mv name prefix remainder) (vl-read-identifier (cdr body)))
             ((unless name)
              ;; Should be ruled out by vl-read-until-end-of-define
              (mv (cw "Preprocessor error (~s0): bad grave character in macro ~
                       text for ~s1.~%"
                      (vl-location-string loc) name)
                  acc))
             (acc (revappend prefix (cons (car body) acc))))
          (vl-substitute-into-macro-text remainder subst name loc config acc)))

       ((when (eql char1 #\"))
        (b* (((mv string prefix remainder)
              (vl-read-string body (vl-lexstate-init config)))
             ((unless string)
              ;; Should be ruled out by vl-read-until-end-of-define
              (mv (cw "Preprocessor error (~s0): bad string literal in macro ~
                       text for ~s1.~%"
                      (vl-location-string loc) name)
                  acc))
             (acc (revappend prefix acc)))
          (vl-substitute-into-macro-text remainder subst name loc config acc)))

       ((when (eql char1 #\\))
        ;; See vl-read-until-end-of-define.  Line continuations should already
        ;; have been eaten and replaced by spaces here.  The only reason we
        ;; should see a backslash, then, is for escaped identifiers.
        (b* (((mv name prefix remainder)
              (vl-read-escaped-identifier body))
             ((unless name)
              ;; Should be ruled out by vl-read-until-end-of-define.
              (mv (cw "Preprocessor error (~s0): stray backslash in macro ~
                       text for ~s1.~%"
                      (vl-location-string loc) name)
                  acc))
             (acc (revappend prefix acc)))
          (vl-substitute-into-macro-text remainder subst name loc config acc)))

       ((when (eql char1 #\/))
        (b* (((when (vl-matches-string-p "//" body))
              ;; Single-line comments are eaten by vl-read-until-end-of-define,
              ;; so we shouldn't need to deal with them here.
              (mv (cw "Preprocessor error (~s0): //-style comment in macro ~
                       text for ~s1? Jared thinks this shouldn't happen.~%"
                      (vl-location-string loc) name)
                  acc))

             ((when (vl-matches-string-p "/*" body))
              (b* (((mv successp prefix remainder)
                    (vl-read-through-literal "*/" (cddr body)))
                   ((unless successp)
                    ;; Should be ruled out by vl-read-until-end-of-define.
                    (mv (cw "Preprocessor error (~s0): unterminated /* ... */ ~
                             style comment in macro text for ~s1?  Jared ~
                             thinks this shouldn't happen."
                            (vl-location-string loc) name)
                        acc))
                   (acc (revappend (list* (first body) (second body) prefix) acc)))
                (vl-substitute-into-macro-text remainder subst name loc config acc))))

          ;; Else: regular division character, treat it as a regular character.
          (vl-substitute-into-macro-text (cdr body) subst name loc config (cons (car body) acc))))

       ;; Else, not a special character.
       ;; We know that macro arguments are simple identifiers.
       ((unless (vl-simple-id-head-p char1))
        (vl-substitute-into-macro-text (cdr body) subst name loc config (cons (car body) acc)))

       ;; We don't bother to check for keywords here, because we shouldn't
       ;; allow keywords as formals in the first place, so they just shouldn't
       ;; be in our substitution to begin with
       ((mv prefix remainder) (vl-read-simple-identifier body))
       (str  (vl-echarlist->string prefix))
       (look (assoc-equal str subst))
       ((unless look)
        ;; Found an identifier but it's not related to the formals.  Just
        ;; accumulate its characters.
        (vl-substitute-into-macro-text remainder subst name loc config (revappend prefix acc)))

       ;; Conversion of replacement text into echars is subtle.  See the
       ;; comments in vl-expand-define to understand why we do this.
       (replacement-str    (cdr look))
       (replacement-echars (vl-echarlist-from-str replacement-str))
       (replacement-fixed  (vl-change-echarlist-locations replacement-echars loc))
       (acc                (revappend replacement-fixed acc)))
    (vl-substitute-into-macro-text remainder subst name loc config acc))

  :prepwork
  ((local (defthm lemma
            (implies (and (alistp subst)
                          (string-listp (alist-vals subst))
                          (assoc-equal key subst))
                     (stringp (cdr (assoc-equal key subst))))
            :hints(("Goal" :in-theory (enable hons-assoc-equal alist-keys)))))

   (local (in-theory (disable assoc-equal-elim)))))


(define vl-expand-define
  :short "Expand uses of defines like @('`foo') and @('`max(a,b)')."
  ((name    stringp         "Name of the directive we've just read, like @('\"foo\"') for @('`foo').")
   (defines vl-defines-p    "All definitions we currently have.")
   (echars  vl-echarlist-p  "Remaining text after the name.  For simple macros like @('`foo') we
                             will just need to append the definition's body onto these characters.
                             For macros with arguments we will need to extract the actuals from
                             these characters.")
   (config  vl-loadconfig-p)
   (loc     vl-location-p   "Location for error messages and for the resulting expansion text."))
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (new-echars vl-echarlist-p
                  "On success, the updated characters with the macro invocation replaced by
                   its expansion."
                  :hyp (force (vl-echarlist-p echars))))

  :long "<p>Note that variables in `define are lazy, e.g., if you do:</p>

@({
      `define foo 3
      `define bar `foo
      `define foo 4
})

<p>Then from here on @('`bar') should also expand to 4.  To accomplish this,
we're going to modify the @('echars') that are remaining in the input.  That
is, the <b>output</b> of @('vl-expand-define') is going to get preprocessed.
This does not always terminate! (Hence the termination counter on @(see
vl-preprocess-loop).</p>

<p><b>Subtle.</b> If we simply inserted the echars stored in the defines table,
then locations on these characters would refer to their original position in
the file.  This might lead to confusing error messages, telling you that
something is wrong and showing you line numbers for a @('`define') that looks
just fine.  So instead, we change all of the locations for the inserted text to
point at the grave character for the macro usage.  That is, if @('`foo') occurs
on line 37 from characters 5 through 8, then we'll make every character of
foo's expansion occur at 37:5.</p>"

  (b* ((lookup (vl-find-define name defines))
       ((unless lookup)
        (mv (cw "Preprocessor error (~s0): `~s1 is not defined.~%"
                (vl-location-string loc) name)
            echars))

       ((vl-define lookup))


       ((when (atom lookup.formals))
        ;; No arguments to process, just insert the body of the macro.
        (b* ((body-str    lookup.body)
             (body-echars (vl-echarlist-from-str body-str))
             (body-fixed  (vl-change-echarlist-locations body-echars loc)))
          (mv t (append body-fixed echars))))

       ;; The macro has arguments.
       ;;
       ;;  - Parentheses are required.  (See for instance SystemVerilog-2012,
       ;;    page 641: "To use a macro defined with arguments, the name of the
       ;;    text macro shall be followed by a list of actual arguments in
       ;;    parentheses...".  See also examples such as, on page 642:
       ;;       "`MACRO3  // ILLEGAL: parentheses required.")
       ;;
       ;;  - Whitespace is allowed before the parens.  (SystemVerilog-2012,
       ;;    page 641: "White space shall be allowed between the text macro
       ;;    name and the left parentheses in the macro usage.")

       ((mv ?ws echars) (vl-read-while-whitespace echars))
       ((unless (and (consp echars)
                     (eql (vl-echar->char (car echars)) #\()))
        (mv (cw "Preprocessor error (~s0): `~s1 requires arguments.~%"
                (vl-location-string loc) name)
            echars))
       (echars (cdr echars)) ;; Eat leading '(' character
       ((mv successp actuals echars) (vl-parse-define-actuals name echars config loc))
       ((unless successp) (mv nil echars)) ;; Already printed error

       ;; Note: at this point, we've already eaten the final ')' character so
       ;; the echars now contain all of the input stream except that we need to
       ;; inject the expansion of this macro.  All that's left to do is to line
       ;; up the actuals and formals, and substitute into the macro body.
       ((mv successp subst)
        (vl-line-up-define-formals-and-actuals lookup.formals actuals name loc))
       ((unless successp) (mv nil echars)) ;; Already printed error

       ((mv okp rev-replacement-body)
        (vl-substitute-into-macro-text (vl-echarlist-from-str lookup.body)
                                       subst name loc config nil))
       ((unless okp) (mv nil echars)) ;; Already printed error

       (replacement-body (rev rev-replacement-body))
       (echars (append replacement-body echars)))
    (mv t echars)))

(define vl-process-undef
  :short "Handler for @('undef') directives."

  ((loc     vl-location-p)
   (echars  vl-echarlist-p)
   (defines vl-defines-p)
   (activep booleanp))

  :returns
  (mv (successp)
      (new-defines vl-defines-p)
      (remainder   vl-echarlist-p :hyp (force (vl-echarlist-p echars))))

  :long "<p>We assume that an @('`undef') has just been read and @('echars') is
the text which follows it.  We try to read the name we are to undefine, then
update the defines table appropriately.</p>"

  (b* ((defines (vl-defines-fix defines))
       ((mv & remainder)      (vl-read-while-whitespace echars))
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

       (lookup (vl-find-define name defines))

       (- (if (not lookup)
              (cw "Preprocessor warning (~s0): found `undef ~s1, but ~s1 is ~
                   not defined.~%"
                  (vl-location-string loc)
                  name)
            (cw "Undefining ~s0.~%" name)))

       (defines (vl-delete-define name defines)))

    (mv t defines remainder))

  ///
  (defthm true-listp-of-vl-process-undef-remainder
    (equal (true-listp (mv-nth 2 (vl-process-undef loc echars defines activep)))
           (true-listp echars)))

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



(define vl-read-timescale
  ((echars vl-echarlist-p))
  :returns (mv prefix remainder)

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
          echars)))
  ///
  (def-prefix/remainder-thms vl-read-timescale))




(defxdoc preprocessor-include-minutia
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



(define vl-read-include
  :short "Read an @('`include') directive."
  ((echars vl-echarlist-p "Characters we're preprocessing.  We assume that
                           @('`include') was just read and removed from
                           @('echars').")
   (config vl-loadconfig-p))
  :returns (mv (filename (or (stringp filename)
                             (not filename))
                         :rule-classes :type-prescription)
               (prefix)
               (remainder))

  :long "<p>We try to read the filename part and return it (without the
quotes).  Per Section 19.5 of the Verilog spec, the syntax is:</p>

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

  (b* (((mv ws1 remainder)
        (vl-read-while-whitespace echars))

       ((mv filename prefix remainder)
        (if (and (consp remainder)
                 (equal (vl-echar->char (car remainder)) #\"))
            (vl-read-string remainder (vl-lexstate-init config))
          (mv nil nil remainder)))

       ((unless filename)
        (mv (cw "Preprocessor error (~s0): invalid `include directive.~%"
                (if (consp echars)
                    (vl-location-string (vl-echar->loc (car echars)))
                  "at end of file"))
            nil echars)))
    (mv filename (append ws1 prefix) remainder))
  ///
  (def-prefix/remainder-thms vl-read-include
    :formals (echars config)
    :prefix-n 1
    :remainder-n 2))

(define vl-preprocess-loop
  :short "Main loop for the preprocessor."
  :long "<p>We accumulate the transformed characters that are to be given to
  the lexer into acc, in reverse order.</p>"
  ((echars  vl-echarlist-p)
   (defines vl-defines-p)
   (filemap vl-filemap-p)
   (istack  vl-istack-p)
   (activep booleanp)
   (acc)
   (n natp)
   (config vl-loadconfig-p)
   (state))
  :returns (mv (successp)
               (defines)
               (filemap)
               (acc)
               (remainder)
               (state))
  :measure (two-nats-measure n (acl2-count echars))
  :hints(("Goal" :in-theory (disable (force))))

  (b* (((when (atom echars))
        (mv t defines filemap acc echars state))

       (echar1 (car echars))
       (char1  (vl-echar->char echar1))
       ((when (zp n))
        (mv (cw "Preprocessor error (~s0): ran out of steps. Macro expansion ~
                 or file inclusion loop?")
            defines filemap acc echars state))

; Preliminaries.  We need to be sure to treat strings, escaped identifiers, and
; comments atomically.  For instance, we don't want to look at a string like
; "looks like an `endif to me" and think that we have just read an `endif.

       ((when (eql char1 #\"))
        ;; Start of a string literal
        (b* (((mv string prefix remainder)
              (vl-read-string echars (vl-lexstate-init config)))
             ((unless string)
              ;; it already printed a warning, so we don't use cw.
              (mv nil defines filemap acc echars state)))
          (vl-preprocess-loop remainder defines filemap istack activep
                              (if activep (revappend prefix acc) acc)
                              n config state)))

       ((when (eql char1 #\\))
        ;; Start of an escaped identifier
        (b* (((mv name prefix remainder) (vl-read-escaped-identifier echars))
             ((unless name)
              (mv (cw "Preprocessor error (~s0): stray backslash?~%"
                      (vl-location-string (vl-echar->loc echar1)))
                  defines filemap acc echars state)))
          (vl-preprocess-loop remainder defines filemap istack activep
                              (if activep (revappend prefix acc) acc)
                              n config state)))

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
                  (b* (((mv & prefix remainder)
                        (vl-read-until-literal *nls* (rest-n 5 echars)))
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
                                  defines filemap istack activep
                                  acc (- n 1) config state))

          ;; Else, not a //@VL comment
          (b* (((mv & prefix remainder) (vl-read-until-literal *nls* (cddr echars)))
               ((when (vl-matches-string-p "+VL" prefix))
                ;; The // part is already gone, strip off the +VL part and
                ;; leave it in the preprocessor's input stream, as above.
                (vl-preprocess-loop (append (rest-n 3 prefix) remainder)
                                    defines filemap istack activep
                                    acc (- n 1) config state))
               ;; Else, regular comment instead of //+VL or //@VL comment, so
               ;; put the slashes back and don't try to preprocess it any more.
               (prefix (list* (first echars) (second echars) prefix)))
            (vl-preprocess-loop remainder defines filemap istack activep
                                (if activep (revappend prefix acc) acc)
                                n config state))))

       ((when (and (eql char1 #\/)
                   (consp (cdr echars))
                   (eql (vl-echar->char (second echars)) #\*)))
        ;; Start of a block comment.

; SPECIAL VL EXTENSION.  We do the same thing for /*+VL...*/, converting it into
; "..." here during preprocessing, and for /*@VL...*/, converting it into (*...*)
; We don't do anything special to support comments within the /*@VL ... */ form,
; since this is mainly intended for inline things

        (b* (((mv successp prefix remainder)
              (vl-read-through-literal "*/" (cddr echars)))
             ((unless successp)
              (mv (cw "Preprocessor error (~s0): block comment is never closed.~%"
                      (vl-location-string (vl-echar->loc echar1)))
                  defines filemap acc echars state))

             ((when (vl-matches-string-p "+VL" prefix))
              ;; The /* part is already gone.  Strip off "+VL" and "*/", and put the
              ;; comment's body into the input stream, as for //+VL above.
              (b* ((body (butlast (rest-n 3 prefix) 2)))
                (vl-preprocess-loop (append body remainder)
                                    defines filemap istack activep
                                    acc (- n 1) config state)))

             ((when (vl-matches-string-p "@VL" prefix))
              ;; The /* part is gone.  Strip off "@VL" and "*/"; add "(*" and "*)",
              ;; and put the body into the input stream, as for //@VL above.
              (b* ((body (append (vl-echarlist-from-str "(*")
                                 (butlast (rest-n 3 prefix) 2)
                                 (vl-echarlist-from-str "*)"))))
                (vl-preprocess-loop (append body remainder)
                                    defines filemap istack activep
                                    acc (- n 1) config state)))

             ;; Else, not a +VL or @VL comment, so put the /* back, and put
             ;; the prefix into the acc becuase we're done preprocessing this
             ;; comment.
             (prefix (list* (first echars) (second echars) prefix)))
          (vl-preprocess-loop remainder defines filemap istack activep
                              (if activep (revappend prefix acc) acc)
                              n config state)))


       ((when (not (eql char1 #\`)))
        ;; Any regular character.  Accumulate or discard, per activep.
        (vl-preprocess-loop (cdr echars) defines filemap istack activep
                            (if activep (cons (car echars) acc) acc)
                            n config state))

; Otherwise we just found a legitimate grave character which isn't inside a
; string literal or comment or anything.  We need to handle some compiler
; directive.

       ((mv & remainder)
        (vl-read-while-whitespace (cdr echars)))

       ((mv directive prefix remainder)
        (vl-read-identifier remainder))

       ((when (not directive))
        (mv (cw "Preprocessor error (~s0): stray ` character.~%"
                (vl-location-string (vl-echar->loc echar1)))
            defines filemap acc echars state))

       ((when (not (vl-is-compiler-directive-p directive)))

; A macro usage like `foo.  The defines table stores the macro text in order,
; so we can essentially revappend it into the accumulator.

        (b* (((unless activep)
              ;; Subtle.  Never try to expand macros in inactive sections,
              ;; because it is legitimate for them to be undefined.
              (vl-preprocess-loop remainder defines filemap istack activep
                                  acc n config state))
             ((mv successp expansion)
              (vl-expand-define directive defines remainder config (vl-echar->loc echar1)))
             ((unless successp)
              ;; Already printed an error message.
              (mv nil defines filemap acc expansion state)))

          (vl-preprocess-loop expansion
                              defines filemap istack activep
                              acc
                              (- (lnfix n) 1)
                              config state)))

       ((when (eql (vl-echar->char (car prefix)) #\\))
        ;; We explicitly disallow `\define, `\ifdef, etc.
        (mv (cw "Preprocessor error (~s0): we do not allow the use of \~s1.~%"
                (vl-location-string (vl-echar->loc echar1)) directive)
            defines filemap acc echars state))

       ((when (or (equal directive "define")
                  (equal directive "centaur_define")))
        ;; CENTAUR EXTENSION: we also support centaur_define
        (b* (((mv successp new-defines remainder)
              (vl-process-define (vl-echar->loc echar1) remainder defines activep config))
             ((unless successp)
              (mv nil defines filemap acc echars state)))
          (vl-preprocess-loop remainder new-defines filemap istack activep
                              acc n config state)))

       ((when (equal directive "undef"))
        (b* (((mv successp new-defines remainder)
              (vl-process-undef (vl-echar->loc echar1) remainder defines activep))
             ((unless successp)
              (mv nil defines filemap acc echars state)))
          (vl-preprocess-loop remainder new-defines filemap istack activep
                              acc n config state)))

       ((when (or (equal directive "ifdef")
                  (equal directive "ifndef")
                  (equal directive "elsif")))
        (b* (((mv successp new-istack new-activep remainder)
              (vl-process-ifdef (vl-echar->loc echar1) directive remainder defines istack activep))
             ((unless successp)
              (mv nil defines filemap acc echars state)))
          (vl-preprocess-loop remainder defines filemap new-istack new-activep
                              acc n config state)))

       ((when (equal directive "else"))
        (b* (((mv successp new-istack new-activep)
              (vl-process-else (vl-echar->loc echar1) istack activep))
             ((unless successp)
              (mv nil defines filemap acc echars state)))
          (vl-preprocess-loop remainder defines filemap new-istack new-activep
                              acc n config state)))

       ((when (equal directive "endif"))
        (b* (((mv successp new-istack new-activep)
              (vl-process-endif (vl-echar->loc echar1) istack activep))
             ((unless successp)
              (mv nil defines filemap acc echars state)))
          (vl-preprocess-loop remainder defines filemap new-istack new-activep
                              acc n config state)))

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
              (vl-preprocess-loop remainder defines filemap istack activep
                                  acc n config state))

             ;; Else, we're in an active section, so read the filename try to
             ;; carry out the inclusion.
             ((mv filename ?prefix remainder) (vl-read-include remainder config))

             ((unless filename)
              ;; Already warned.
              (mv nil defines filemap acc echars state))

             ((mv realfile state)
              (vl-find-file filename (vl-loadconfig->include-dirs config) state))
             ((unless realfile)
              (mv (cw "Preprocessor error (~s0): unable to find ~s1.  The ~
                       include directories are ~&2."
                      (vl-location-string (vl-echar->loc echar1))
                      filename
                      (vl-loadconfig->include-dirs config))
                  defines filemap acc echars state))

             ((mv okp contents state)
              (cwtime (vl-read-file (string-fix realfile))
                      :mintime 1/2))
             ((unless okp)
              (mv (cw "Preprocessor error (~s0): unable to read ~s1."
                      (vl-location-string (vl-echar->loc echar1)) realfile)
                  defines filemap acc echars state))

             (filemap (if (vl-loadconfig->filemapp config)
                          (cons (cons realfile (vl-echarlist->string contents))
                                filemap)
                        filemap)))

          (vl-preprocess-loop
           ;; We could perhaps avoid this append with two recursive calls,
           ;; but we'll have to modify vl-preprocess-loop to additionally
           ;; return the updated istack and activep.
           (append contents remainder) defines filemap istack activep
           acc (- n 1) config state)))

       ((when (equal directive "timescale"))
        (b* (((mv prefix remainder) (vl-read-timescale remainder))
             ((unless prefix)
              (mv nil defines filemap acc echars state)))
          ;; BOZO maybe add a note that we are ignoring timescale?
          (vl-preprocess-loop remainder defines filemap istack activep
                              acc n config state)))

       ((when (or (equal directive "celldefine")
                  (equal directive "endcelldefine")
                  (equal directive "resetall")))
        ;; BOZO maybe add a note that we are ignoring these directives?
        (vl-preprocess-loop remainder defines filemap istack activep
                            acc n config state)))

    (mv (cw "Preprocessor error (~s0): we do not support ~s1.~%"
            (vl-location-string (vl-echar->loc echar1)) directive)
        defines filemap acc echars state))

  ///
  (never-memoize vl-preprocess-loop)

  ;; Speed hint
  (local (in-theory (disable ACL2::OPEN-SMALL-NTHCDR
                             acl2::CONSP-UNDER-IFF-WHEN-TRUE-LISTP
                             ACL2::NTHCDR-WITH-LARGE-INDEX
                             VL-MATCHES-STRING-P-WHEN-ACL2-COUNT-ZERO
                             acl2::nthcdr-append
                             acl2::consp-butlast
                             acl2::len-when-prefixp
                             string-fix
                             stringp-when-true-listp
                             hons-assoc-equal
                             (:TYPE-PRESCRIPTION REMAINDER-OF-VL-READ-UNTIL-LITERAL)
                             acl2::revappend-removal
                             revappend
                             )))

  (local (set-default-hints
          ;; I think we might be hitting ACL2's heuristics on not opening up
          ;; functions when it would introduce too many ifs, so we need this to
          ;; tell it to really go ahead and open up the function.
          '('(:expand ((:free (activep) (vl-preprocess-loop echars defines filemap istack activep acc n config state)))))))

  (defthm booleanp-of-vl-preprocess-loop-success
    (b* (((mv ?successp ?defines ?filemap ?acc ?remainder ?state)
          (vl-preprocess-loop echars defines filemap istack activep acc n config state)))
      (booleanp successp))
    :rule-classes :type-prescription)

  (defthm state-p1-of-vl-preprocess-loop
    (implies (force (state-p1 state))
             (b* (((mv ?successp ?defines ?filemap ?acc ?remainder ?state)
                   (vl-preprocess-loop echars defines filemap istack activep acc n config state)))
               (state-p1 state))))

  ;; (defthm true-listp-of-vl-preprocess-loop-result
  ;;   (b* (((mv ?successp ?defines ?filemap new-acc ?remainder ?state)
  ;;         (vl-preprocess-loop echars defines filemap istack activep acc n config state)))
  ;;     (equal (true-listp new-acc)
  ;;            (true-listp acc))))

  ;; (defthm true-listp-of-vl-preprocess-loop-remainder
  ;;   (b* (((mv ?successp ?defines ?filemap ?acc ?remainder ?state)
  ;;         (vl-preprocess-loop echars defines filemap istack activep acc n config state)))
  ;;     (equal (true-listp remainder)
  ;;            (true-listp echars))))

  ;; (defthmd no-remainder-of-vl-preprocess-loop-on-success
  ;;   (b* (((mv ?successp ?defines ?filemap ?acc ?remainder ?state)
  ;;         (vl-preprocess-loop echars defines filemap istack activep acc n config state)))
  ;;     (implies (and successp
  ;;                   (true-listp echars))
  ;;              (not (consp remainder)))))

  (defthm vl-preprocess-loop-basics
    (implies (and (force (vl-echarlist-p echars))
                  (force (vl-defines-p defines))
                  (force (vl-filemap-p filemap))
                  (force (vl-istack-p istack))
                  (force (booleanp activep))
                  (force (vl-echarlist-p acc))
                  (force (state-p1 state)))
             (b* (((mv ?successp ?defines ?filemap ?acc ?remainder ?state)
                   (vl-preprocess-loop echars defines filemap istack activep acc n config state)))
               (and (vl-defines-p defines)
                    (vl-filemap-p filemap)
                    (vl-echarlist-p acc)
                    (vl-echarlist-p remainder))))))


(defval *vl-preprocess-clock*
  :short "Artificial bound on preprocessor loops, for termination."
  :long "<p>This is a really big number and is a fixnum on CCL.  If there is no
loop, it is hard to imagine ever hitting this; each expansion of a
legitimate macro will require some consing, so we will almost certainly run
out of memory before running out of clock.</p>"
  (expt 2 59))

(define vl-safe-previous-n ((n natp) acc)
  :short "Used to get a context for error messages."
  :returns (prev-n vl-echarlist-p :hyp (vl-echarlist-p acc))
  (reverse (first-n (min (nfix n) (len acc)) acc)))

(define vl-safe-next-n ((n natp) remainder)
  :short "Used to get a context for error messages."
  :returns (next-n vl-echarlist-p :hyp (vl-echarlist-p remainder))
  (first-n (min (nfix n) (len remainder)) remainder))

(define vl-preprocess
  :short "Top-level interface to the preprocessor."
  ((echars "Characters to preprocess, in order."
           vl-echarlist-p)
   &key
   (defines "Initial definitions to use." vl-defines-p)
   (filemap "Initial file map to extend (for `includes)." vl-filemap-p)
   (config  "Controls the Verilog edition, include paths, etc." vl-loadconfig-p)
   ((state   "ACL2's @(see state), for file i/o.") 'state))
  :returns
  (mv (successp   "Was preprocessing successful?"
                  booleanp :rule-classes :type-prescription)
      (defines    "Updated defines after preprocessing the files."
                  vl-defines-p :hyp :fguard)
      (filemap    "Possibly extended filemap."
                  vl-filemap-p :hyp :fguard)
      (new-echars "Updated extended characters, after preprocessing."
                  vl-echarlist-p :hyp :fguard)
      (state state-p1 :hyp (force (state-p1 state))))

  ;; Note: keep in sync with optimized version, below.
  (b* (((mv successp defines filemap acc remainder state)
        (vl-preprocess-loop echars defines filemap
                            nil                   ;; istack
                            t                     ;; activep
                            nil                   ;; acc
                            *vl-preprocess-clock* ;; n
                            config
                            state))
       ((when successp)
        ;; BOZO it would be really nice to use nreverse here.
        (mv successp defines filemap (rev acc) state)))
    (mv (cw "[[ Previous  ]]: ~s0~%~
             [[ Remaining ]]: ~s1~%"
            (vl-echarlist->string (vl-safe-previous-n 50 acc))
            (vl-echarlist->string (vl-safe-next-n 50 remainder)))
        defines
        filemap
        nil
        state)))


