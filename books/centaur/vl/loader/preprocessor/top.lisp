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
(include-book "defines")
(include-book "print-defines")
(include-book "../filemap")
(include-book "../read-file")
(include-book "../find-file")
(include-book "../lexer/top") ;; to identify string boundaries, escaped ids, etc.
(include-book "../../util/cwtime")
(include-book "../../mlib/print-warnings")
(local (include-book "../../util/arithmetic"))

;; stupid speed hacking

(local (defthm append-nil
         (equal (append nil y) y)))

(local (defthm true-listp-append-rw
         (equal (true-listp (append x y))
                (true-listp y))))

(local (in-theory (disable vl-echarlist-p-when-subsetp-equal
                           nthcdr-of-increment
                           double-containment
                           default-car
                           default-cdr
                           acl2::subsetp-append1
                           vl-echar-p-when-member-equal-of-vl-echarlist-p
                           acl2-count-positive-when-consp
                           acl2::append-when-not-consp
                           acl2::append-of-cons
                           acl2::true-listp-append
                           acl2::rev-when-not-consp
                           (:type-prescription true-listp)
                           hons-assoc-equal
                           acl2::CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP
                           acl2::STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP
                           STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP
                           STRING-LISTP-WHEN-MEMBER-EQUAL-OF-STRING-LIST-LISTP
                           SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP
                           TRUE-LISTP-WHEN-MEMBER-EQUAL-OF-TRUE-LIST-LISTP
                           VL-MATCHES-STRING-P-WHEN-ACL2-COUNT-ZERO
                           acl2::nth-with-large-index
                           nth-when-too-big
                           (tau-system))))


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

<p>See @(see preprocessor-ifdef-minutia) for some details and additional
discussion.</p>

<p>We also have pretty good support for @('`include') directives.  This is
quite underspecified, and we have basically tried to mimic the behavior of
Verilog-XL and NCVerilog.  See also @(see preprocessor-include-minutia).</p>

<p>We also support @('`__FILE__') and @('`__LINE__') directives.</p>

<h4>Ignored Directives</h4>

<p>We also \"support\" certain directives by <b>ignoring</b> them.</p>

<ul>
 <li>@('`celldefine')</li>
 <li>@('`endcelldefine')</li>
 <li>@('`resetall')</li>
 <li>@('`timescale')</li>
 <li>@('`protect')</li>
 <li>@('`endprotect')</li>
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

<p>We also ignore @('`protect') and @('`endprotect'), which seem to be old
Verilog-XL directives for marking code that you want a tool to encrypt.  VL
doesn't implement any support for decrypting protected code, but it can at
least ignore these indications that you want to encrypt something.  Note that
these directives are not documented in the SystemVerilog-2012 standard and are
probably subsumed by the @('pragma') syntax described in Section 34, protected
envelopes.</p>

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

   ;; SystemVerilog-2012 Compiler Directives
   "__FILE__"
   "__LINE__"
   "undefineall"

   ;; Legacy Verilog-XL nonsense
   "protect"
   "endprotect"

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


(fty::defprod vl-iskipinfo
  :parents (vl-includeskips)
  :short "Information about the multiple-include status of an individual file."
  :tag :vl-iskipinfo
  :layout :tree
  ((controller maybe-stringp :rule-classes :type-prescription
               "NIL if this file does not have a proper include guard,
                or the name of the controlling define otherwise.")
   (misses vl-locationlist-p
           "For evaluating multiple-include optimization effectiveness.  This
            is a list of places where this file is @('`include')d and is
            actually being loaded from disk.  For files that follow proper
            include-guard discipline, this should end up being a singleton list
            with only the initial @('`include') of the file.  For files that
            don't follow the include-guard discipline but are included multiple
            times, it may be a longer list.")
   (hits vl-locationlist-p
         "For evaluating multiple-include optimization effectiveness.  This is
          a list of places where this file is being @('`include')d from but
          where we don't bother reloading it thanks to MI optimization.")
   (len natp :rule-classes :type-prescription
        "Length of this file in characters.  Possibly of interest for
         evaluating multiple-include effectiveness.")))

(fty::defalist vl-includeskips
  :key-type stringp
  :val-type vl-iskipinfo-p
  :short "A record of which files we have already included that have ``proper''
include guards and may not need to be included again."

  :long "<p>Header files often have the form</p>

@({
     `ifndef included_foo
     `define included_foo
        ...
     `endif
})

<p>Or equivalently (and possibly common in legacy code since historically
@('ifndef') wasn't supported by some tools):</p>

@({
     `ifdef included_foo
     `else
        `define included_foo
        ...
     `endif
})

<p>In the typical case where @('included_foo') never gets undefined, it is good
for performance to completely skip subsequent includes of such files.</p>

<p>To accomplish this, we maintain an @('includeskips') alist, which is
a (fast) alist binding pathnames of files that we have @('`include')d so far to
@(see vl-iskipinfo)s that contain the names of their controlling define, e.g.,
@('included_foo') (and some additional information).</p>

<p>These controlling defines should only be added to the @('includeskips') when
we determine that they have the proper form.  Later, when we encounter a new
@('`include'), we can check whether the file is in the @('includeskips') and,
if so, whether its controlling define is still @('`define')d.  If so, we can
avoid the pointless work of re-opening the file, re-reading its characters, and
re-preprocessing them, because we know that after expanding the @('ifdefs'),
the file will make no contribution to the post-preprocessed text we are
building.</p>

<p>To identify files that match the proper form, when we open a file due to an
@('`include'), we check whether the file begins with one of the above,
``proper'' include-guard formats; see @(see vl-multiple-include-begin).  This
identification is pretty efficient: we only have to scan initial comments,
whitespace, and a few tokens.  If we find a proper include-guard start, we push
a special @(see vl-iframe), corresponding to the @('ifndef included_foo').
This iframe is marked as <b>multiple-include candidate</b> whose controller is
@('included_foo').  We then skip until just before the @('`define') and resume
preprocessing.</p>

<p>We have to be careful, as we process the body of the included file, to be
sure to remove this marking if we ever encounter an @('`else') or @('`elseif')
that's part of the special top-level @('`ifndef').  This is done in @(see
vl-process-ifdef) and @(see vl-process-else).</p>

<p>When we finally get to the @('`endif'), we notice in @(see vl-process-endif)
that we have a special frame.  If so, we know that (1) the start of the file
begins with a suitable @('ifndef/define') pair and (2) there have been no
@('`else') or @('`elseif') directives attached with this pair along the way.
So, the only thing left to check is that the remainder of the file consists of
nothing but whitespace and comments, which is easy and efficient.  If so, we're
set: the file has the desired form, so we add it to the @('includeskips')
alist.</p>")

(defprod vl-iframe
  :short "@('`ifdef') stack frame objects."
  :layout :tree

  ((initially-activep     booleanp      :rule-classes :type-prescription)
   (some-thing-satisfiedp booleanp      :rule-classes :type-prescription)
   (already-saw-elsep     booleanp      :rule-classes :type-prescription)
   (mi-controller         maybe-stringp :rule-classes :type-prescription
                          "When set, this iframe is possibly an include guard
                           and this is the name of the controlling define.
                           See @(see vl-includeskips).")
   (mi-filename           maybe-stringp :rule-classes :type-prescription
                          "Corresponds to mi-controller; the filename that is
                           being included."))

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

(fty::deflist vl-istack
  :elt-type vl-iframe)

;; (local (defthm true-listp-of-vl-echarlist-fix
;;          (true-listp (vl-echarlist-fix x))
;;          :hints(("Goal" :in-theory (enable vl-echarlist-fix)))))

(defsection ppst
  :short "Preprocessor state object."
  :long "<p>Our preprocessor deals with a lot of state, and needs to mutate it
a lot, so we stick its fields together in a stobj.</p> @(def ppst)"
  :autodoc nil

  (make-event
   `(defstobj ppst
      ;; Characters we are emitting (post-preprocessed text), reverse order
      (vl-ppst-acc      :type (satisfies vl-echarlist-p) :initially nil)
      ;; Stack of `ifdef frames
      (vl-ppst-istack   :type (satisfies vl-istack-p) :initially nil)
      ;; Are we currently active (not `ifdefed out)
      (vl-ppst-activep  :type (satisfies booleanp) :initially nil)
      ;; Current `defines
      (vl-ppst-defines  :type (satisfies vl-defines-p) :initially nil)
      ;; Filemap (for optionally recording contents of included files)
      (vl-ppst-filemap  :type (satisfies vl-filemap-p) :initially nil)
      ;; Load configuration (include dirs, verilog edition, other settings)
      (vl-ppst-config   :type (satisfies vl-loadconfig-p) :initially ,*vl-default-loadconfig*)
      ;; Data for skipping multiply included files
      (vl-ppst-iskips   :type (satisfies vl-includeskips-p) :initially nil)
      ;; Accumulator for preprocessor warnings
      (vl-ppst-warnings :type (satisfies vl-warninglist-p) :initially nil)
      ;; Stack of files we are currently `include'ing
      (vl-ppst-includes :type (satisfies string-listp) :initially nil)
      ;; Total bytes we have read so far
      (vl-ppst-bytes :type unsigned-byte :initially 0)
      ;; Include directory cache
      (vl-ppst-idcache :type (satisfies vl-dirlist-cache-p) :initially nil)
      ;; Ifdef use map
      (vl-ppst-ifdefmap :type (satisfies vl-ifdef-use-map-p) :initially nil)
      ;; Define (non-ifdef) use map
      (vl-ppst-defmap :type (satisfies vl-def-use-map-p) :initially nil)
      :inline t
      :non-memoizable t
      :renaming ((ppstp                     vl-ppst-p)
                 (vl-ppst-acc               vl-ppst->acc-raw)
                 (update-vl-ppst-acc        vl-ppst-update-acc-raw)
                 (vl-ppst-istack            vl-ppst->istack-raw)
                 (update-vl-ppst-istack     vl-ppst-update-istack-raw)
                 (vl-ppst-activep           vl-ppst->activep-raw)
                 (update-vl-ppst-activep    vl-ppst-update-activep-raw)
                 (vl-ppst-defines           vl-ppst->defines-raw)
                 (update-vl-ppst-defines    vl-ppst-update-defines-raw)
                 (vl-ppst-filemap           vl-ppst->filemap-raw)
                 (update-vl-ppst-filemap    vl-ppst-update-filemap-raw)
                 (vl-ppst-config            vl-ppst->config-raw)
                 (update-vl-ppst-config     vl-ppst-update-config-raw)
                 (vl-ppst-iskips            vl-ppst->iskips-raw)
                 (update-vl-ppst-iskips     vl-ppst-update-iskips-raw)
                 (vl-ppst-warnings          vl-ppst->warnings-raw)
                 (update-vl-ppst-warnings   vl-ppst-update-warnings-raw)
                 (vl-ppst-includes          vl-ppst->includes-raw)
                 (update-vl-ppst-includes   vl-ppst-update-includes-raw)
                 (vl-ppst-bytes             vl-ppst->bytes-raw)
                 (update-vl-ppst-bytes      vl-ppst-update-bytes-raw)
                 (vl-ppst-idcache           vl-ppst->idcache-raw)
                 (update-vl-ppst-idcache    vl-ppst-update-idcache-raw)
                 (vl-ppst-ifdefmap          vl-ppst->ifdefmap-raw)
                 (update-vl-ppst-ifdefmap   vl-ppst-update-ifdefmap-raw)
                 (vl-ppst-defmap            vl-ppst->defmap-raw)
                 (update-vl-ppst-defmap     vl-ppst-update-defmap-raw)
                 ))))

(defsection ppst-accessors
  :parents (ppst)
  :short "Replacement accessors for @(see ppst) with unconditional types and
          automatic @('ppst')."

  (define vl-ppst->acc (&key (ppst 'ppst))
    :returns (acc vl-echarlist-p)
    :inline t
    (mbe :logic (vl-echarlist-fix (vl-ppst->acc-raw ppst))
         :exec (vl-ppst->acc-raw ppst)))

  (define vl-ppst->istack (&key (ppst 'ppst))
    :returns (istack vl-istack-p)
    :inline t
    (mbe :logic (vl-istack-fix (vl-ppst->istack-raw ppst))
         :exec (vl-ppst->istack-raw ppst)))

  (define vl-ppst->activep (&key (ppst 'ppst))
    :returns (activep booleanp :rule-classes :type-prescription)
    :inline t
    (mbe :logic (acl2::bool-fix (vl-ppst->activep-raw ppst))
         :exec (vl-ppst->activep-raw ppst)))

  (define vl-ppst->defines (&key (ppst 'ppst))
    :returns (defines vl-defines-p)
    :inline t
    (mbe :logic (vl-defines-fix (vl-ppst->defines-raw ppst))
         :exec (vl-ppst->defines-raw ppst)))

  (define vl-ppst->filemap (&key (ppst 'ppst))
    :returns (filemap vl-filemap-p)
    :inline t
    (mbe :logic (vl-filemap-fix (vl-ppst->filemap-raw ppst))
         :exec (vl-ppst->filemap-raw ppst)))

  (define vl-ppst->config (&key (ppst 'ppst))
    :returns (config vl-loadconfig-p)
    :inline t
    (mbe :logic (vl-loadconfig-fix (vl-ppst->config-raw ppst))
         :exec (vl-ppst->config-raw ppst)))

  (define vl-ppst->iskips (&key (ppst 'ppst))
    :returns (iskips vl-includeskips-p)
    :inline t
    (mbe :logic (vl-includeskips-fix (vl-ppst->iskips-raw ppst))
         :exec (vl-ppst->iskips-raw ppst)))

  (define vl-ppst->warnings (&key (ppst 'ppst))
    :returns (warnings vl-warninglist-p)
    :inline t
    (mbe :logic (vl-warninglist-fix (vl-ppst->warnings-raw ppst))
         :exec (vl-ppst->warnings-raw ppst)))

  (define vl-ppst->includes (&key (ppst 'ppst))
    :returns (includes string-listp)
    :inline t
    (mbe :logic (string-list-fix (vl-ppst->includes-raw ppst))
         :exec (vl-ppst->includes-raw ppst)))

  (define vl-ppst->bytes (&key (ppst 'ppst))
    :returns (bytes natp)
    :inline t
    (mbe :logic (lnfix (vl-ppst->bytes-raw ppst))
         :exec (vl-ppst->bytes-raw ppst)))

  (define vl-ppst->idcache (&key (ppst 'ppst))
    :returns (idcache vl-dirlist-cache-p)
    :inline t
    (mbe :logic (vl-dirlist-cache-fix (vl-ppst->idcache-raw ppst))
         :exec (vl-ppst->idcache-raw ppst)))

  (define vl-ppst->ifdefmap (&key (ppst 'ppst))
    :returns (map vl-ifdef-use-map-p)
    :inline t
    (mbe :logic (vl-ifdef-use-map-fix (vl-ppst->ifdefmap-raw ppst))
         :exec (vl-ppst->ifdefmap-raw ppst)))

  (define vl-ppst->defmap (&key (ppst 'ppst))
    :returns (map vl-def-use-map-p)
    :inline t
    (mbe :logic (vl-def-use-map-fix (vl-ppst->defmap-raw ppst))
         :exec (vl-ppst->defmap-raw ppst)))

  )


(defsection ppst-mutators
  :parents (ppst)
  :short "Replacement mutators for @(see ppst) with automatic @('ppst')."

  (define vl-ppst-update-acc ((acc vl-echarlist-p) &key (ppst 'ppst))
    :returns ppst
    :inline t
    (vl-ppst-update-acc-raw acc ppst))

  (define vl-ppst-update-istack ((istack vl-istack-p) &key (ppst 'ppst))
    :returns ppst
    :inline t
    (vl-ppst-update-istack-raw istack ppst))

  (define vl-ppst-update-activep ((activep booleanp) &key (ppst 'ppst))
    :returns ppst
    :inline t
    (vl-ppst-update-activep-raw activep ppst))

  (define vl-ppst-update-defines ((defines vl-defines-p) &key (ppst 'ppst))
    :returns ppst
    :inline t
    (vl-ppst-update-defines-raw defines ppst))

  (define vl-ppst-update-filemap ((filemap vl-filemap-p) &key (ppst 'ppst))
    :returns ppst
    :inline t
    (vl-ppst-update-filemap-raw filemap ppst))

  (define vl-ppst-update-config ((config vl-loadconfig-p) &key (ppst 'ppst))
    :returns ppst
    :inline t
    (vl-ppst-update-config-raw config ppst))

  (define vl-ppst-update-iskips ((iskips vl-includeskips-p) &key (ppst 'ppst))
    :returns ppst
    :inline t
    (vl-ppst-update-iskips-raw iskips ppst))

  (define vl-ppst-update-warnings ((warnings vl-warninglist-p) &key (ppst 'ppst))
    :returns ppst
    :inline t
    (vl-ppst-update-warnings-raw warnings ppst))

  (define vl-ppst-update-includes ((includes string-listp) &key (ppst 'ppst))
    :returns ppst
    :inline t
    (vl-ppst-update-includes-raw includes ppst))

  (define vl-ppst-update-bytes ((bytes natp) &key (ppst 'ppst))
    :returns ppst
    :inline t
    (vl-ppst-update-bytes-raw bytes ppst))

  (define vl-ppst-update-idcache ((idcache vl-dirlist-cache-p) &key (ppst 'ppst))
    :returns ppst
    :inline t
    (vl-ppst-update-idcache-raw idcache ppst))

  (define vl-ppst-update-ifdefmap ((ifdefmap vl-ifdef-use-map-p) &key (ppst 'ppst))
    :returns ppst
    :inline t
    (vl-ppst-update-ifdefmap-raw ifdefmap ppst))

  (define vl-ppst-update-defmap ((defmap vl-def-use-map-p) &key (ppst 'ppst))
    :returns ppst
    :inline t
    (vl-ppst-update-defmap-raw defmap ppst))

  )


(defprod vl-saved-ppst
  :parents (ppst)
  :short "A saved @(see ppst), useful for backtracking in case of bad includes."
  :layout :tree
  :tag :vl-saved-ppst
  ((acc vl-echarlist-p)
   (istack vl-istack-p)
   (activep booleanp)
   (defines vl-defines-p)
   (filemap vl-filemap-p)
   (config vl-loadconfig-p)
   (iskips vl-includeskips-p)
   (warnings vl-warninglist-p)
   (includes string-listp)
   (bytes natp)
   (idcache vl-dirlist-cache-p)
   (ifdefmap vl-ifdef-use-map-p)
   (defmap vl-def-use-map-p)
   ))

(define vl-save-ppst (&key (ppst 'ppst))
  :returns (saved vl-saved-ppst-p)
  :parents (ppst)
  :short "Save the contents of a @(see ppst) into a @(see vl-saved-ppst)."
  (make-vl-saved-ppst :acc (vl-ppst->acc)
                      :istack (vl-ppst->istack)
                      :activep (vl-ppst->activep)
                      :defines (vl-ppst->defines)
                      :filemap (vl-ppst->filemap)
                      :config (vl-ppst->config)
                      :iskips (vl-ppst->iskips)
                      :warnings (vl-ppst->warnings)
                      :includes (vl-ppst->includes)
                      :bytes (vl-ppst->bytes)
                      :idcache (vl-ppst->idcache)
                      :ifdefmap (vl-ppst->ifdefmap)
                      :defmap (vl-ppst->defmap)))

(define vl-restore-ppst ((saved vl-saved-ppst-p)
                         &key (ppst 'ppst))
  :parents (ppst)
  :short "Restore a saved @(see vl-saved-ppst) into the @(see ppst) stobj."
  (b* (((vl-saved-ppst saved))
       (ppst (vl-ppst-update-acc saved.acc))
       (ppst (vl-ppst-update-istack saved.istack))
       (ppst (vl-ppst-update-activep saved.activep))
       (ppst (vl-ppst-update-defines saved.defines))
       (ppst (vl-ppst-update-filemap saved.filemap))
       (ppst (vl-ppst-update-config saved.config))
       (ppst (vl-ppst-update-iskips saved.iskips))
       (ppst (vl-ppst-update-warnings saved.warnings))
       (ppst (vl-ppst-update-includes saved.includes))
       (ppst (vl-ppst-update-bytes saved.bytes))
       (ppst (vl-ppst-update-idcache saved.idcache))
       (ppst (vl-ppst-update-ifdefmap saved.ifdefmap))
       (ppst (vl-ppst-update-defmap saved.defmap)))
    ppst)
  ///
  (local (defthm xx
           (implies (and (< 0 (len x))
                         (true-listp x))
                    (equal (equal (cons (first x) rest) x)
                           (equal rest (cdr x))))))

  (local (defthm xx1
           (implies (syntaxp (quotep n))
                    (equal (nth n x)
                           (cond ((atom x) nil)
                                 ((zp n) (car x))
                                 (t (nth (- n 1) (cdr x))))))))

  (defthm vl-save-and-restore-ppst-correct
    ;; This is a good sanity check to have, because if you add fields to ppst
    ;; you need to also remember to add them to the save/restore mechanism.  I
    ;; forgot to do that when adding iskips, and it was pretty hard to debug!
    (implies (vl-ppst-p ppst)
             (equal (vl-restore-ppst (vl-save-ppst)
                                     :ppst (create-ppst))
                    ppst))
    :hints(("Goal" :in-theory (e/d (vl-restore-ppst
                                    vl-save-ppst
                                    vl-ppst-update-acc
                                    vl-ppst-update-istack
                                    vl-ppst-update-activep
                                    vl-ppst-update-defines
                                    vl-ppst-update-filemap
                                    vl-ppst-update-config
                                    vl-ppst-update-iskips
                                    vl-ppst-update-warnings
                                    vl-ppst-update-includes
                                    vl-ppst-update-bytes
                                    vl-ppst-update-idcache
                                    vl-ppst-update-ifdefmap
                                    vl-ppst-update-defmap
                                    vl-ppst->acc
                                    vl-ppst->istack
                                    vl-ppst->activep
                                    vl-ppst->defines
                                    vl-ppst->filemap
                                    vl-ppst->config
                                    vl-ppst->iskips
                                    vl-ppst->warnings
                                    vl-ppst->includes
                                    vl-ppst->bytes
                                    vl-ppst->idcache
                                    vl-ppst->ifdefmap
                                    vl-ppst->defmap
                                    ))))))

(define vl-ppst-warn (&key (type symbolp)
                           (msg stringp)
                           (args true-listp)
                           ((fn symbolp) '__function__)
                           (ppst 'ppst))
  :parents (ppst)
  :short "Add a non-fatal warning to the @(see ppst)."
  :long "<p>We don't print anything since it's just a warning.</p>"
  (b* ((warnings (vl-ppst->warnings))
       (warnings (warn :type type
                       :msg msg
                       :args args
                       :fn fn)))
    (vl-ppst-update-warnings warnings)))

(define vl-maybe-ppst-warn (&key (when)
                                 (type symbolp)
                                 (msg stringp)
                                 (args true-listp)
                                 ((fn symbolp) '__function__)
                                 (ppst 'ppst))
  :parents (ppst)
  :short "Add a non-fatal warning to the @(see ppst)."
  :long "<p>We don't print anything since it's just a warning.</p>"
  (b* ((warnings (vl-ppst->warnings))
       ((unless when) ppst)
       (warnings (warn :type type
                       :msg msg
                       :args args
                       :fn fn)))
    (vl-ppst-update-warnings warnings)))


(define vl-nice-bytes ((bytes natp))
  :returns (str stringp :rule-classes :type-prescription)
  :short "Human-friendly summary of some number of bytes."
  :prepwork ((local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
             (local (in-theory (disable truncate rem))))
  (b* (((when (< bytes 1000))
        (cat (natstr bytes) "B"))
       (kbytes (truncate bytes 1000))
       ((when (< kbytes 1000))
        (cat (natstr kbytes)
             "."
             (natstr (truncate (rem bytes 1000) 100))
             "K"))
       (mbytes (truncate kbytes 1000))
       ((when (< mbytes 1000))
        (cat (natstr mbytes)
             "."
             (natstr (truncate (rem kbytes 1000) 100))
             "M"))
       (gbytes (truncate mbytes 1000)))
    (cat (natstr gbytes)
         "."
         (natstr (truncate (rem mbytes 1000) 100))
         "G"))
  ///
  ;; Some examples
  (assert! (equal (vl-nice-bytes 0) "0B"))
  (assert! (equal (vl-nice-bytes 123) "123B"))
  (assert! (equal (vl-nice-bytes 1234) "1.2K"))
  (assert! (equal (vl-nice-bytes 12345) "12.3K"))
  (assert! (equal (vl-nice-bytes 123456) "123.4K"))
  (assert! (equal (vl-nice-bytes 1234567) "1.2M"))
  (assert! (equal (vl-nice-bytes 12345678) "12.3M"))
  (assert! (equal (vl-nice-bytes 123456789) "123.4M"))
  (assert! (equal (vl-nice-bytes 1234567890) "1.2G"))
  (assert! (equal (vl-nice-bytes 12345678901) "12.3G")))

(define vl-ppst-pad (&key (ppst 'ppst))
  :returns (pad stringp :rule-classes :type-prescription)
  :short "Prefix for lines produced by the preprocessor."
  ;; To give the user some feeling of progress, we report how many bytes we
  ;; have read so far.  But we summarize that in a way that is friendly for
  ;; humans to read with vl-nice-bytes.  Unless we're reading some absurd
  ;; amount of data, that summary should look like, at most, 123.4B or similar,
  ;; i.e., it should fit into 6 characters.  So we'll tag our lines with [size]
  ;; and pad the size to 6 characters to keep things consistent.
  (cat "[" (str::lpadstr (vl-nice-bytes (vl-ppst->bytes)) 6) "] "
       ;; Beyond the size pad, we'll indent to the current include depth, which
       ;; gives an intuitive sense of how deep we are getting and maybe what
       ;; files are taking a long time.
       (implode (make-list (len (vl-ppst->includes)) :initial-element #\Space))))

(define vl-ppst-fatal (&key ((type symbolp) ':vl-preprocessor-error)
                            (msg stringp)
                            (args true-listp)
                            ((fn symbolp) '__function__)
                            (ppst 'ppst))
  :parents (ppst)
  :short "Add a fatal warning to the @(see ppst)."
  :long "<p>We also print the warning since this is a fatal error, and the user
  may be interested in seeing it sooner rather than later.</p>"
  (b* ((w (make-vl-warning :type type
                           :fatalp t
                           :msg msg
                           :args args
                           :fn fn))
       (warnings (vl-ppst->warnings))
       (ppst (vl-ppst-update-warnings (cons w warnings)))
       ;; Some embellishments -- we print the warning as per usual, but then
       ;; indent it out to the current number of includes.
       (wstr    (with-local-ps (vl-print-warning w)))
       (padded  (str::prefix-lines wstr (cat (vl-ppst-pad) " *** "))))
    (cw-unformatted padded)
    ppst))

(define vl-ppst-write ((etext vl-echarlist-p) &key (ppst 'ppst))
  :parents (ppst)
  :short "Unconditionally add some preprocessor output."
  :inline t
  (vl-ppst-update-acc (revappend-without-guard etext (vl-ppst->acc))))

(define vl-ppst-maybe-write ((etext vl-echarlist-p) &key (ppst 'ppst))
  :parents (ppst)
  :short "Add some preprocessor output unless we're currently @('ifdef')'d out."
  :inline t
  (if (vl-ppst->activep)
      (vl-ppst-update-acc (revappend-without-guard etext (vl-ppst->acc)))
    ppst))

(define vl-ppst-maybe-write1 ((echar vl-echar-p) &key (ppst 'ppst))
  :parents (ppst)
  :short "Add some preprocessor output unless we're currently @('ifdef')'d out."
  :inline t
  (if (vl-ppst->activep)
      (vl-ppst-update-acc (cons echar (vl-ppst->acc)))
    ppst))


(define vl-includeskips-controller-lookup ((realfile stringp)
                                           (iskips vl-includeskips-p))
  :returns (controller maybe-stringp :rule-classes :type-prescription)
  :short "Look up the controlling define for this file, if one is known."
  (b* ((iskipinfo (cdr (hons-get realfile iskips))))
    (and iskipinfo
         (vl-iskipinfo->controller iskipinfo))))

(define vl-includeskips-install-controller ((realfile stringp)
                                            (controller stringp)
                                            (iskips vl-includeskips-p))
  :returns (new-iskips vl-includeskips-p)
  :parents (vl-includeskips)
  :short "Install the controlling define into the @(see vl-includeskips).
          This should be done when the final @('`endif') is encountered
          and determined to be ok."
  (b* ((realfile (string-fix realfile))
       (iskips   (vl-includeskips-fix iskips))
       (entry (cdr (hons-get realfile iskips)))
       ((unless entry)
        (raise "Programming error: missing initial entry in includeskips ~
                for ~f0.  Expected entries to be created upon initial load, ~
                so this should never happen." realfile)
        iskips)
       (entry (change-vl-iskipinfo entry :controller controller)))
    (hons-acons realfile entry iskips)))

(define vl-includeskips-record-hit ((realfile stringp "File being included.")
                                    (loc      vl-location-p "Location of the @('`include').")
                                    (iskips   vl-includeskips-p))
  :returns (new-iskips vl-includeskips-p)
  :parents (vl-includeskips)
  :short "Record that a file is being successfully skipped due to multiple include optimization."
  (b* ((realfile (string-fix realfile))
       (loc      (vl-location-fix loc))
       (iskips   (vl-includeskips-fix iskips))
       (entry (cdr (hons-get realfile iskips)))
       ((unless entry)
        (raise "Programming error: skipping include without entry for ~f0???" realfile)
        iskips)
       (entry (change-vl-iskipinfo entry :hits (cons loc (vl-iskipinfo->hits entry)))))
    (hons-acons realfile entry iskips)))

(define vl-includeskips-record-miss ((realfile stringp       "File being included.")
                                     (loc      vl-location-p "Location of the @('`include').")
                                     (len      natp          "Length of the file.")
                                     (iskips   vl-includeskips-p))
  :returns (new-iskips vl-includeskips-p)
  :parents (vl-includeskips)
  :short "Record that a file is not being skipped due to multiple include optimization."
  (b* ((realfile (string-fix realfile))
       (loc      (vl-location-fix loc))
       (iskips   (vl-includeskips-fix iskips))
       (entry    (or (cdr (hons-get realfile iskips))
                     (make-vl-iskipinfo :controller nil
                                        :misses nil
                                        :hits nil
                                        :len len)))
       (entry    (change-vl-iskipinfo entry :misses (cons loc (vl-iskipinfo->misses entry)))))
    (hons-acons realfile entry iskips)))


(define vl-skip-whitespace/comments ((x vl-echarlist-p))
  :returns (remainder vl-echarlist-p :hyp :guard)
  :parents (vl-includeskips)
  :short "For use in @(see vl-includeskips), just skip past any whitespace and
          comments."
  (b* (((when (atom x))
        x)
       (char1 (vl-echar->char (first x)))
       ((when (vl-whitespace-p char1))
        (vl-skip-whitespace/comments (cdr x)))
       ((unless (and (eql char1 #\/)
                     (consp (cdr x))))
        x)
       (char2 (vl-echar->char (second x)))
       (rest  (cddr x))
       ((when (and (eql char2 #\/)
                   (not (vl-matches-string-p "@VL" rest))
                   (not (vl-matches-string-p "+VL" rest))))
        ;; Found // comment that isn't a special //+VL or //@VL comment, so
        ;; skip it and keep going.
        (b* (((mv ?okp ?prefix remainder)
              (vl-read-through-literal *nls* rest)))
          (vl-skip-whitespace/comments remainder)))
       ((when (and (eql char2 #\*)
                   (not (vl-matches-string-p "@VL" rest))
                   (not (vl-matches-string-p "+VL" rest))))
        ;; Found /* comment that isn't a special /*+VL ...*/ or /*@VL ...*/
        ;; comment, so skip it and keep going.
        (b* (((mv ?okp ?prefix remainder)
              (vl-read-through-literal "*/" rest)))
          (vl-skip-whitespace/comments remainder))))
    x))

(local (defthm maybe-stringp-of-vl-read-identifier
         (implies (vl-echarlist-p echars)
                  (maybe-stringp (mv-nth 0 (vl-read-identifier echars))))
         :hints(("Goal" :in-theory (e/d (maybe-stringp))))))

(define vl-match-proper-header-file-start-1 ((x vl-echarlist-p))
  :parents (vl-includeskips)
  :short "Match the start of a ``proper'' @('ifndef')-controlled header file."
  :returns
  (mv (controller maybe-stringp :rule-classes :type-prescription
                  "On success, the name of the controlling define.")
      (loc        vl-location-p
                  "Location of the controlling define")
      (resume-point vl-echarlist-p
                    "On success, the remainder of the file immediately
                    after the @('ifndef included_foo') part."
                   :hyp :guard))

  :long "<p>Here @('x') is a file we've just read due to an @('include').  We
want to see if @('x') looks like it might be a proper header, i.e., does it
have the form:</p>

@({
     `ifndef included_foo
     `define included_foo
       ...
     `endif
})

<p>except that we're a bit more permissive than this because we allow for
whitespace and comments before the leading `ifndef and so forth.</p>

<p>Here we only examine the start of the file and, if we match the above
template through @('define included_foo'), we return @('included_foo') as
the name of the ``controlling define'' for this file.  If the file isn't
of an acceptable form we just return NIL.</p>"

  (b* (;; Any leading comments/whitespace are OK.
       (x (vl-echarlist-fix x))
       (x (vl-skip-whitespace/comments x))

       (loc (if (consp x)
                (vl-echar->loc (car x))
              *vl-fakeloc*))

       ;; Match `ifndef
       ((mv prefix x) (vl-read-literal "`ifndef" x))
       ((unless prefix) (mv nil loc nil))

       ;; Match included_foo
       ((mv ws x) (vl-read-while-whitespace x))
       ((unless ws) (mv nil loc nil))
       ((mv ifndef-name & x) (vl-read-identifier x))
       ((unless ifndef-name) (mv nil loc nil))

       ;; Any subsequent comments/whitespace are OK.
       (x (vl-skip-whitespace/comments x))

       (resume-point x)

       ;; Match `define
       ((mv prefix x) (vl-read-literal "`define" x))
       ((unless prefix) (mv nil loc nil))

       ;; Match included_foo
       ((mv ws x) (vl-read-while-whitespace x))
       ((unless ws) (mv nil loc nil))
       ((mv define-name ?prefix ?remainder) (vl-read-identifier x))
       ((unless define-name) (mv nil loc nil))

       ;; Make sure the ifndef/define both are for the same name
       ((unless (equal ifndef-name define-name)) (mv nil loc nil)))

    ;; Looks like a proper ifndef header.
    (mv (string-fix ifndef-name)
        loc
        resume-point)))

(define vl-match-proper-header-file-start-2 ((x vl-echarlist-p))
  :parents (vl-includeskips)
  :short "Match the start of a ``proper'' @('ifdef')-controlled header file."
  :returns
  (mv (controller maybe-stringp :rule-classes :type-prescription
                  "On success, the name of the controlling define.")
      (loc        vl-location-p
                  "Location of the controlling define")
      (resume-point vl-echarlist-p
                    "On success, the remainder of the file immediately after
                     the @('else') part."
                    :hyp :guard))

  :long "<p>Here @('x') is a file we've just read due to an @('include').  We
want to see if @('x') looks like it might be a proper header, i.e., does it
have the form:</p>

@({
     `ifdef included_foo
     `else
       `define included_foo
       ...
     `endif
})

<p>except that we're a bit more permissive than this because we allow for
whitespace and comments before the leading `ifdef and so forth.</p>

<p>Here we only examine the start of the file and, if we match the above
template through @('define included_foo'), we return @('included_foo') as the
name of the ``controlling define'' for this file.  If the file isn't of an
acceptable form we just return NIL.</p>"

  (b* (;; Match `ifdef
       (x (vl-skip-whitespace/comments x))
       (loc (if (consp x)
                (vl-echar->loc (car x))
              *vl-fakeloc*))
       ((mv prefix x) (vl-read-literal "`ifdef" x))
       ((unless prefix) (mv nil loc nil))

       ;; Match included_foo
       ((mv ws x) (vl-read-while-whitespace x))
       ((unless ws) (mv nil loc nil))
       ((mv ifdef-name & x) (vl-read-identifier x))
       ((unless ifdef-name) (mv nil loc nil))

       ;; Match `else
       (x (vl-skip-whitespace/comments x))
       ((mv prefix x) (vl-read-literal "`else" x))
       ((unless prefix) (mv nil loc nil))

       (resume-point x)

       ;; Match `define
       (x (vl-skip-whitespace/comments x))
       ((mv prefix x) (vl-read-literal "`define" x))
       ((unless prefix) (mv nil loc nil))

       ;; Match included_foo
       ((mv ws x) (vl-read-while-whitespace x))
       ((unless ws) (mv nil loc nil))
       ((mv define-name ?prefix ?remainder) (vl-read-identifier x))
       ((unless define-name) (mv nil loc nil))

       ;; Make sure the ifdef/define both are for the same name
       ((unless (equal ifdef-name define-name)) (mv nil loc nil)))

    ;; Looks like a proper ifdef header.
    (mv (string-fix ifdef-name)
        loc
        resume-point)))

(define vl-ppst-record-ifdef-use ((name stringp)
                                  (ctx vl-ifdef-context-p)
                                  &key (ppst 'ppst))
  :returns ppst
  (b* ((ifdef-map (vl-ppst->ifdefmap))
       (ifdef-map (vl-extend-ifdef-map name ctx ifdef-map)))
    (vl-ppst-update-ifdefmap ifdef-map)))

(define vl-ppst-record-def-use ((name stringp)
                                (ctx vl-def-context-p)
                                &key (ppst 'ppst))
  :returns ppst
  (b* ((def-map (vl-ppst->defmap))
       (def-map (vl-extend-def-map name ctx def-map)))
    (vl-ppst-update-defmap def-map)))

(define vl-multiple-include-begin ((realfile stringp        "File name being loaded.")
                                   (contents vl-echarlist-p "Contents of that file.")
                                   ppst)
  :parents (vl-includeskips)
  :short "Check a file for a proper include-guard header; if so, install a
          special iframe and skip past the initial @('ifndef') part, otherwise
          leave the file alone."
  :returns (mv (new-contents vl-echarlist-p
                             "On failure, the unmodified @('contents').  On success,
                              the remainder of the file just past the include guard.")
               (ppst "Possibly updated with a special iframe for the include guard."))

  (b* ((contents (vl-echarlist-fix contents))
       ((mv controller1 controller1-loc post-ifndef)
        (vl-match-proper-header-file-start-1 contents))
       ((mv controller2 controller2-loc post-else)
        (if controller1
            (mv nil nil nil)
          (vl-match-proper-header-file-start-2 contents)))

       (controller (or controller1 controller2))
       (resume-point (if controller1 post-ifndef post-else))
       (controller-loc (if controller1 controller1-loc controller2-loc))
       ((unless controller)
        (let ((ppst (vl-ppst-warn
                     :type :vl-warn-include-guard
                     :msg "~s0: included file has no include-guard.  (This is ~
                           fine but may reduce performance if the file is ~
                           included multiple times.)"
                     :args (list realfile))))
          (mv contents ppst)))

       (prev-def (vl-find-define controller (vl-ppst->defines)))
       ((when prev-def)
        ;; When I originally coded this, I worried that if there was a previous
        ;; definition of the include guard, then it wouldn't be safe to do
        ;; multiple-include optimization.
        ;;
        ;; In particular, if we have
        ;;
        ;;    `define included_foo
        ;;    `include "foo.v"
        ;;
        ;; where foo.v has a legitimate included_foo guard, then (1) that's kind
        ;; of weird, and (2) are we sure that our multiple include-guard
        ;; handling will work the right way?
        ;;
        ;; After thinking about it more, I thought the answer might be yes.  In
        ;; particular, even if we're preprocessing foo.v with the whole thing
        ;; inactive because of a previous define, we still have to process the
        ;; whole ifdef tree and therefore will still notice if there are any
        ;; problematic `endif or `elses.  Right?
        ;;
        ;; On further reflection I don't think so.  The problem is intervening
        ;; defines.  In particular consider something like:
        ;;
        ;;    // foo.v
        ;;    `ifndef included_foo
        ;;    `define included_foo
        ;;
        ;;     `define blah `endif
        ;;     `blah
        ;;
        ;;    wire extra_wire
        ;;    `endif
        ;;
        ;; In this case, if we try to preprocess this file without some external
        ;; definition of included_foo, the `blah token will expand to an `endif
        ;; and we'll see that the file is not suitable for multiple include
        ;; optimization.  However, if we skip the body of foo.v due to the prior
        ;; definition, the `blah will occur in an inactive section and not get
        ;; expanded and therefore we will not see the problematic `endif.
        ;;
        ;; So that's too bad, but I think we're obliged to avoid multiple
        ;; include optimization here.
        (let ((ppst (vl-ppst-warn
                     :type :vl-warn-include-guard
                     :msg "~s0: potential include guard controller, ~s1, is ~
                           already defined when reading the file; previous ~
                           definition from ~a2.  This is unusual and will ~
                           defeat multiple-include optimization for this file."
                     :args (list realfile controller (vl-define->loc prev-def)))))
          (mv contents ppst)))

       (- (cw-unformatted (cat (vl-ppst-pad) " (multi-include candidate)" *nls*)))

       ;; Make the special multiple-include iframe for `ifndef foo
       (iframe (make-vl-iframe
                ;; It's initially active because it's the first thing in the
                ;; file and we wouldn't even be expanding a `include unless
                ;; we were active to begin with.
                :initially-activep t
                ;; It *is* satisfied because it's an `ifndef foo and we
                ;; explicitly checked that foo isn't defined.
                :some-thing-satisfiedp t
                ;; In the ifndef form (controller1) we don't have an else,
                ;; but in the second form (controller2) we do.
                :already-saw-elsep (not controller1)
                :mi-controller controller
                :mi-filename realfile))

       (ppst (vl-ppst-record-ifdef-use controller
                                       (make-vl-ifdef-context :loc controller-loc)))

       (istack (vl-ppst->istack))
       (ppst   (vl-ppst-update-istack (cons iframe istack))))
    ;; Finally, since we're forging the iframe ourselves, sneak just past the
    ;; ifndef and only preprocess the rest of the file, starting right from
    ;; the controlling `define.
    (mv resume-point ppst)))

(define vl-process-ifdef
  :short "Handler for @('ifdef'), @('ifndef'), and @('elsif') directives."
  ((loc       vl-location-p)
   (directive (member-equal directive '("ifdef" "ifndef" "elsif")))
   (echars    vl-echarlist-p)
   ppst)
  :returns
  (mv (successp)
      (remainder vl-echarlist-p)
      ppst)

  :long "<p>We assume that we have just read @('`directive') from @('echars').
We need to read the identifier that should follow this directive, look it up in
the defines table, and make the appropriate changes to the @('istack') and
@('activep').</p>"

  (b* ((echars                (vl-echarlist-fix echars))
       ((mv & remainder)      (vl-read-while-whitespace echars))
       ((mv name & remainder) (vl-read-identifier remainder))

       ((unless name)
        (let ((ppst (vl-ppst-fatal
                     :msg "~a0: found an `~s1 without an identifier."
                     :args (list loc directive))))
          (mv nil echars ppst)))

       ((when (vl-is-compiler-directive-p name))
        ;; Special prohibition of compiler directive names in ifdefs, ifndefs,
        ;; etc.  See :xdoc preprocessor-ifdef-minutia for why.
        (let ((ppst (vl-ppst-fatal
                     :msg "~a0: cowardly refusing to permit `s1 ~s2."
                     :args (list loc directive name))))
          (mv nil echars ppst)))

       (activep (vl-ppst->activep))
       (defines (vl-ppst->defines))
       (istack  (vl-ppst->istack))

       ((when (equal directive "ifdef"))
        (let* ((this-satisfiedp (consp (vl-find-define name defines)))
               (new-iframe      (make-vl-iframe :initially-activep     activep
                                                :some-thing-satisfiedp this-satisfiedp
                                                :already-saw-elsep     nil
                                                ;; Ordinary ifdef, nothing to do with includes
                                                :mi-controller         nil
                                                :mi-filename           nil))
               (new-istack      (cons new-iframe istack))
               (new-activep     (and activep this-satisfiedp))
               (new-ctx         (make-vl-ifdef-context :loc loc))
               (ppst            (vl-ppst-update-istack new-istack))
               (ppst            (vl-ppst-record-ifdef-use name new-ctx))
               (ppst            (vl-ppst-update-activep new-activep)))
          (mv t remainder ppst)))

       ((when (equal directive "ifndef"))
        (let* ((this-satisfiedp (not (vl-find-define name defines)))
               (new-iframe      (make-vl-iframe :initially-activep     activep
                                                :some-thing-satisfiedp this-satisfiedp
                                                :already-saw-elsep     nil
                                                ;; Ordinary ifndef, nothing to do with includes
                                                :mi-controller         nil
                                                :mi-filename           nil))
               (new-istack      (cons new-iframe istack))
               (new-activep     (and activep this-satisfiedp))
               (new-ctx         (make-vl-ifdef-context :loc loc))
               (ppst            (vl-ppst-update-istack new-istack))
               (ppst            (vl-ppst-record-ifdef-use name new-ctx))
               (ppst            (vl-ppst-update-activep new-activep)))
          (mv t remainder ppst)))

       ;; Otherwise we're dealing with an elsif.

       ((when (atom istack))
        (let ((ppst (vl-ppst-fatal
                     :msg "~a0: found `elsif, but no `ifdef is open."
                     :args (list loc))))
          (mv nil echars ppst)))

       ((vl-iframe iframe) (car istack))

       ((when iframe.already-saw-elsep)
        (let ((ppst (vl-ppst-fatal
                     :msg "~a0: found `elsif, but we have already seen `else."
                     :args (list loc))))
          (mv nil echars ppst)))

       (ppst (vl-maybe-ppst-warn :when iframe.mi-controller
                                 :type :vl-warn-include-guard
                                 :msg "~a0: suppressing multiple-include optimization due to ~
                      `elsif."
                                 :args (list loc)))

       (this-satisfiedp (consp (vl-find-define name defines)))
       (new-activep     (and this-satisfiedp
                             (not iframe.some-thing-satisfiedp)
                             iframe.initially-activep))
       (new-iframe      (change-vl-iframe
                         iframe
                         :some-thing-satisfiedp (or this-satisfiedp
                                                    iframe.some-thing-satisfiedp)
                         ;; Unmark any potential multiple-include optimization
                         ;; because we don't want to think about `elsif trees here.
                         :mi-controller nil
                         :mi-filename nil))
       (new-ctx         (make-vl-ifdef-context :loc loc))
       (new-istack      (cons new-iframe (cdr istack)))
       (ppst            (vl-ppst-update-activep new-activep))
       (ppst            (vl-ppst-record-ifdef-use name new-ctx))
       (ppst            (vl-ppst-update-istack new-istack)))
    (mv t remainder ppst))
  ///
  (defthm true-listp-of-vl-process-ifdef
    (true-listp (mv-nth 1 (vl-process-ifdef loc directive echars ppst)))
    :rule-classes :type-prescription)

  (defthm acl2-count-of-vl-process-ifdef-weak
    (<= (acl2-count (mv-nth 1 (vl-process-ifdef loc directive echars ppst)))
        (acl2-count (vl-echarlist-fix echars)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm acl2-count-of-vl-process-ifdef-strong
    (implies (mv-nth 0 (vl-process-ifdef loc directive echars ppst))
             (< (acl2-count (mv-nth 1 (vl-process-ifdef loc directive echars ppst)))
                (acl2-count (vl-echarlist-fix echars))))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force))))))


(define vl-process-else
  :short "Handler for @('else') directives."
  ((loc     vl-location-p)
   ppst)
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      ppst)
  (b* ((istack (vl-ppst->istack))
       ((when (atom istack))
        (let ((ppst (vl-ppst-fatal
                     :msg "~a0: found `else, but no `ifdef is open."
                     :args (list loc))))
          (mv nil ppst)))

       ((vl-iframe iframe) (car istack))
       ((when iframe.already-saw-elsep)
        (let ((ppst (vl-ppst-fatal
                     :msg "~a0: found `else, but we already saw an `else."
                     :args (list loc))))
          (mv nil ppst)))

       (ppst (vl-maybe-ppst-warn :when iframe.mi-controller
                                 :type :vl-warn-include-guard
                                 :msg "~a0: suppressing multiple-include optimization due to `else."
                                 :args (list loc)))

       (new-activep       (and iframe.initially-activep
                               (not iframe.some-thing-satisfiedp)))
       (new-iframe        (make-vl-iframe
                           :initially-activep     iframe.initially-activep
                           :some-thing-satisfiedp t
                           :already-saw-elsep     t
                           ;; Unmark any potential multiple-include optimization
                           ;; because we don't want to think about `else trees here.
                           :mi-controller nil
                           :mi-filename nil))
       (new-istack        (cons new-iframe (cdr istack)))

       (ppst (vl-ppst-update-activep new-activep))
       (ppst (vl-ppst-update-istack new-istack)))
    (mv t ppst)))

(define vl-process-endif
  :short "Handler for @('endif') directives."
  ((loc     vl-location-p)
   (echars  vl-echarlist-p
            "Characters that come after the @('`endif'), which are used only
             for multiple-include optimization.")
   ppst)
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      ppst)
  (b* ((istack (vl-ppst->istack))
       ((when (atom istack))
        (let ((ppst (vl-ppst-fatal
                     :msg "~a0: found `endif, but no `ifdef is open."
                     :args (list loc))))
          (mv nil ppst)))

       ;; Ordinary stuff for handling an `endif: pop the current frame and
       ;; adjust activep accordingly.
       ((vl-iframe iframe) (car istack))
       (new-istack  (cdr istack))
       (new-activep iframe.initially-activep)
       (ppst (vl-ppst-update-istack new-istack))
       (ppst (vl-ppst-update-activep new-activep))

       ((unless iframe.mi-controller)
        ;; Not a multiple include candidate; we've already adjusted the istack
        ;; and there's nothing left to do.
        (mv t ppst))
       ((unless iframe.mi-filename)
        ;; This should never happen if we're updating iframes correctly.
        (raise "Programming error: iframe has mi controller but no filename? ~x0"
               iframe)
        (mv t ppst))

       ;; Else, see vl-includeskips: this is a multiple include candidate so
       ;; the start of the file begins with:
       ;;
       ;;   `ifndef {mi.controller}
       ;;   `define {mi-controller}
       ;;
       ;; and there are no intervening, associated `elsif or `else directives
       ;; between that starting point and this `endif that we're now looking
       ;; at.  There are still some things to check.

       ;; (1) We'd better still be in the same file.
       ((unless (equal iframe.mi-filename (vl-location->filename loc)))
        (let ((ppst (vl-ppst-warn
                     :type :vl-warn-include-guard
                     :msg "~a0: disabling multiple-include optimization ~
                           because the corresponding include guard was found ~
                           in a different file, ~s1.  If this isn't expected, ~
                           there may be a problem with your `ifdef tree."
                     :args (list loc iframe.mi-filename))))
          ;; Even though the optimization can't kick in, we are still
          ;; successfully processing this else.
          (mv t ppst)))

       ;; (2) There'd better be nothing else in the file, except perhaps
       ;; some trailing comments and whitespace.
       (post-ws (vl-skip-whitespace/comments echars))
       ((unless (atom post-ws))
        (let ((ppst (vl-ppst-warn
                     :type :vl-warn-include-guard
                     :msg "~a0: disabling multiple-include optimization ~
                           because there's content after the `else for ~
                           ~s1."
                     :args (list loc iframe.mi-controller))))
          ;; Even though the optimization can't kick in, we are still
          ;; successfully processing this else.
          (mv t ppst)))

       ;; Looks good so extend the includeskips
       (- (cw-unformatted (cat (vl-ppst-pad) " (multi-include confirmed)" *nls*)))
       (iskips (vl-includeskips-install-controller iframe.mi-filename
                                                   iframe.mi-controller
                                                   (vl-ppst->iskips)))
       (ppst (vl-ppst-update-iskips iskips)))

    (mv t ppst)))

(local
 (defrule remainder-when-successful-vl-read-until-literal
   (b* (((mv successp ?prefix remainder)
         (vl-read-until-literal string echars)))
     (implies successp
              remainder))
   :hints (("goal" :use consp-of-remainder-when-successful-vl-read-until-literal
            :in-theory (disable consp-of-remainder-when-successful-vl-read-until-literal)))))

(define vl-read-until-end-of-define
  :short "Read from @('`define') until the end of the line."
  ((echars vl-echarlist-p)
   ppst)
  :returns
  (mv (successp  booleanp       :rule-classes :type-prescription)
      (prefix    vl-echarlist-p)
      (remainder vl-echarlist-p)
      ppst)

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

  :measure (acl2-count (vl-echarlist-fix echars))
  :prepwork ((local (in-theory (disable (tau-system)))))

  (b* ((echars (vl-echarlist-fix echars))
       ((when (atom echars))
        ;; We allow macros to be defined on the last line of the file;
        ;; "implicitly inserting a newline" for them.
        (mv t nil echars ppst))
       (char1 (vl-echar->char (first echars)))

       ((when (eql char1 #\Newline))
        ;; Successful end of macro text.
        (mv t nil echars ppst))

       ((when (eql char1 #\`))
        (b* ( ;; Check for new SystemVerilog sequences `" and ``.
             ((when (and (consp (cdr echars))
                         (member (vl-echar->char (second echars)) '(#\" #\`))))
              (b* (((mv successp text remainder ppst)
                    (vl-read-until-end-of-define (cddr echars) ppst))
                   ((unless successp)
                    (mv nil nil echars ppst))
                   (prefix (list* (first echars) (second echars) text)))
                (mv t prefix remainder ppst)))

             ;; Check for new SystemVerilog sequence `\`".  (Seriously)
             ((when (and (consp (cdr echars))
                         (consp (cddr echars))
                         (consp (cdddr echars))
                         (eql (vl-echar->char (second echars)) #\\)
                         (eql (vl-echar->char (third echars))  #\`)
                         (eql (vl-echar->char (fourth echars)) #\")))
              (b* (((mv successp text remainder ppst)
                    (vl-read-until-end-of-define (cddddr echars) ppst))
                   ((unless successp)
                    (mv nil nil echars ppst))
                   (prefix (list* (first echars)
                                  (second echars)
                                  (third echars)
                                  (fourth echars)
                                  text)))
                (mv t prefix remainder ppst)))

             ;; Otherwise it should be an identifier like `foo.  We allow
             ;; user-defines like `foo and `bar, but not built-ins like `define
             ;; and `endif.
             ((mv name prefix remainder) (vl-read-identifier (cdr echars)))
             ((unless name)
              (let ((ppst (vl-ppst-fatal
                           :msg "~a0: no name following back-quote/grave character (`)."
                           :args (list (vl-echar->loc (car echars))))))
                (mv nil nil echars ppst)))

             ;; [Jared] We historically prohibited the use of any compiler
             ;; directives here.  But the really scary things are the ifdef
             ;; related things; it seems pretty reasonable for a compiler macro
             ;; to include other things like `celldefine, `timescale, and so
             ;; on.  It would be nice to prohibit the ifdef stuff, but I found
             ;; that to support certain code I needed it.  So, for now just
             ;; emit warnings about them.
             ;;
             ;; [Jared] Hrmn, on further reflection I think we probably
             ;; shouldn't be loudly warning about this.  If we ever rejigger
             ;; the preprocessor to create proper warnings, we could add these
             ;; warnings back in.  But for now they seem potentially too chatty
             ;; and there's no nice way to turn them off.  Probably best to
             ;; just be quiet for now.
             ;;
             ;; (- (and (vl-is-compiler-directive-p name)
             ;;         (member-equal (string-fix name)
             ;;                       '("ifdef" "ifndef" "else"
             ;;                         "elsif" "endif"))
             ;;         (cw "Preprocessor warning (~f0): using `~s1 in a `define ~
             ;;              seems scary.~%~%"
             ;;             (vl-location-string (vl-echar->loc (car echars)))
             ;;             name)))

             ((mv successp text remainder ppst)
              (vl-read-until-end-of-define remainder ppst))
             ((unless successp)
              (mv nil nil echars ppst)))
          (mv t
              (cons (car echars) (append prefix text))
              remainder
              ppst)))

       ((when (eql char1 #\"))
        ;; Skip over string literals so we aren't confused by graves, etc.
        (b* (((mv string prefix remainder)
              (vl-read-string echars (vl-lexstate-init (vl-ppst->config))))
             ((unless string)
              (mv nil nil echars ppst))
             ((mv successp text remainder ppst)
              (vl-read-until-end-of-define remainder ppst))
             ((unless successp)
              (mv nil nil echars ppst)))
          (mv t (append prefix text) remainder ppst)))

       ((when (eql char1 #\\))
        (b* (((when (vl-matches-string-p "//" (cdr echars)))
              (let ((ppst (vl-ppst-fatal
                           :msg "~a0: we cowardly do not allow '\//' in ~
                                 defines."
                           :args (list (vl-echar->loc (car echars))))))
                (mv nil nil echars ppst)))

             ((when (vl-matches-string-p "/*" (cdr echars)))
              (let ((ppst (vl-ppst-fatal
                           :msg "~a0: we cowardly do not allow '\/*' in ~
                                 defines."
                           :args (list (vl-echar->loc (car echars))))))
                (mv nil nil echars ppst)))

             ((when (vl-matches-string-p *nls* (cdr echars)))

; A line continuation.
;
; Ugh.  I found a stupid bug here on 2011-04-26 because I was recurring on (cdr
; echars) instead of (cddr echars).
;
; Then I did some more tests.  This is really horrible.  In particular, what
; should \<newline> expand to?  Some plausible answers would include at least:
; nothing, a newline, or a single space.
;
; Theory 1 (my first theory): the sequence \<newline> should just expand into a
; newline character.
;
; Experiment to try to disprove Theory 2 (cosims/pp3): Verilog-XL, NCV, and VCS
; say that `goo is 3 in the following:
;
;   |`define foo 1 \<newline>
;   |  + 2
;   |`define goo `foo
;
; After seeing this, I originally thought that it disproved Theory 1, because
; if \<newline> expanded to just a <newline>, then wouldn't that mean that
; after expanding `foo the above would be equivalent to:
;
;   |`define goo 1
;   |  + 2
;
; And wouldn't this mean that `goo would be defined as 1?  But I no longer
; think this is the case.  Instead, I think all we're seeing here is that
; `define expansion is lazy: `goo just expands to `foo, which then expands to 1
; [whatever \<newline> expands to] + 2.  So the experiment is just not very
; useful.  For further verification that `define is lazy, see cosims/pp5.
;
; New experiment (cosims/pp4) to try to rule out \<newline> expanding into
; nothing at all.  Notice the left column here.
;
;  |`define test module\<newline>
;  |mytest
;  |
;  |`test () ;
;  |endmodule
;
; NCVerilog and VCS both accept this, which suggests that \<newline> expands to
; at least a space or newline or some other kind of whitespace.  Verilog-XL
; said this was a syntax error, even when I added a space before the module's
; name, e.g.,
;
;  |`define `test module\<newline>
;  | test
;
; But it was happy when I put a space before the \<newline>.  So, it doesn't
; seem like Verilog-XL tolerates \ continuations without a space before them,
; meaning that whether it expands to a space or nothing is irrelevant.
;
; For many years, I had \<newline> expand into a space character and I thought
; that was the right story.  But later, when I relaxed VL's restrictions that
; `defines must not contain directives like `ifdef, `define, etc., I found that
; this did not seem to be correct.  In particular, consider:
;
; Experiment 3 (cosims/pp2):
;
;    |`define HORRIBLE \<newline>
;    |  `define FOO \<newline>
;    |  1'b1<newline>
;
; If \<newline> expands to a space, then this should be equivalent to:
;
;    |`define HORRIBLE `define FOO 1'b1
;
; But both NCV and VCS seem to interpret this differently.  In particular,
; constructs such as
;
;   generate
;     if (`HORRIBLE) ...
;   endgenerate
;
; Are tolerated, and afterward `FOO seems to be `define'd to be 1.  I think
; the most plausible explanation is that \<newline> expands to a newline
; character.

              (b* (((mv successp text remainder ppst)
                    (vl-read-until-end-of-define (cddr echars) ppst))
                   ((unless successp)
                    (mv nil nil echars ppst)))
                (mv t
                    (cons (second echars) text)
                    remainder
                    ppst)))

             ;; Skip over escaped identifiers so we aren't confused by graves,
             ;; etc.
             ((mv name prefix remainder)
              (vl-read-escaped-identifier echars))
             ((unless name)
              (let ((ppst (vl-ppst-fatal
                           :msg "~a0: stray backslash?"
                           :args (list (vl-echar->loc (car echars))))))
                (mv nil nil echars ppst)))
             ((mv successp text remainder ppst)
              (vl-read-until-end-of-define remainder ppst))
             ((unless successp)
              (mv nil nil echars ppst)))
          (mv t (append prefix text) remainder ppst)))

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
                (mv t nil remainder ppst))

               ((when (and (consp prefix)
                           (eql (vl-echar->char (car (last prefix))) #\\)))
                ;; Horrible case: something like
                ;;
                ;;    `define foo begin // fancy macro \
                ;;        x = y; \
                ;;     end
                ;;
                ;; It's not clear whether the backslash is a line continuation
                ;; or just part of the comment.  We originally tried to just
                ;; complain about these and not support it, but it appears that
                ;; some commercial tools are actually allowing this and
                ;; treating it as a line continuation.  So, now we'll just
                ;; print a warning and do the same.
                (b* ((ppst (vl-ppst-warn
                            :type :vl-warn-line-continuation
                            :msg "~a0: within a `define, a single-line ~
                                  comment ends with a backslash.  Treating ~
                                  this as a line continuation."
                            :args (list (vl-echar->loc (car echars)))))
                     ;; See the above case for handling line continuations.  I
                     ;; think we need to go ahead and just eat the comment and
                     ;; then turn it into a space.  Note that the remainder
                     ;; currently starts with the newline character, so we'll
                     ;; turn that newline into a space and then process the
                     ;; rest of the remainder.
                     (new-space (change-vl-echar (car remainder) :char #\Space))
                     ((mv successp text remainder ppst)
                      (vl-read-until-end-of-define (cdr remainder) ppst))
                     ((unless successp)
                      (mv nil nil echars ppst)))
                  (mv t (cons new-space text) remainder ppst))))

            ;; Single-line comments are to be excluded; nothing more is to be
            ;; read.
            (mv t nil remainder ppst)))

         ((vl-matches-string-p "/*" echars)
          (b* (((mv successp prefix remainder)
                (vl-read-through-literal "*/" (cddr echars)))
               ((unless successp)
                (let ((ppst (vl-ppst-fatal
                             :msg "~a0: block comment is never closed."
                             :args (list (vl-echar->loc (car echars))))))
                  (mv nil nil echars ppst)))
               ((when (member #\Newline (vl-echarlist->chars prefix)))
                (let ((ppst (vl-ppst-fatal
                             :msg "~a0: block comment inside a define is not ~
                                   closed before end of line."
                             :args (list (vl-echar->loc (car echars))))))
                  (mv nil nil echars ppst)))
               ((mv successp text remainder ppst)
                (vl-read-until-end-of-define remainder ppst))
               ((unless successp)
                (mv nil nil echars ppst)))
            (mv t
                (append (list* (first echars) (second echars) prefix)
                        text)
                remainder
                ppst)))

         (t
          ;; Regular division operator -- treat it as a regular character
          (b* (((mv successp text remainder ppst)
                (vl-read-until-end-of-define (cdr echars) ppst))
               ((unless successp)
                (mv nil nil echars ppst)))
            (mv t (cons (car echars) text) remainder ppst)))))

       ;; Else, some regular character
       ((mv successp text remainder ppst)
        (vl-read-until-end-of-define (cdr echars) ppst))
       ((unless successp)
        (mv nil nil echars ppst)))
    (mv t (cons (car echars) text) remainder ppst))
  ///
  (local (in-theory (disable (:d vl-read-until-end-of-define))))
  (local (defthm cdr-of-vl-echarlist-fix
           (equal (cdr (vl-echarlist-fix x))
                  (vl-echarlist-fix (cdr x)))
           :hints(("Goal" :in-theory (enable vl-echarlist-fix)))))
  (local (defthm true-listp-cdr-when-consp
           (implies (consp x)
                    (equal (true-listp (cdr x))
                           (True-listp x)))))

  (local (set-default-hints
          '((acl2::just-induct-and-expand
             (vl-read-until-end-of-define echars config)))))

  (local (in-theory (disable acl2::append-under-iff
                             acl2::member-of-cons)))
  
  (defthm true-listp-of-vl-read-until-end-of-define-prefix
    (true-listp (mv-nth 1 (vl-read-until-end-of-define echars config)))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-read-until-end-of-define-remainder
    (true-listp (mv-nth 2 (vl-read-until-end-of-define echars config)))
    :rule-classes :type-prescription)

  (defthm acl2-count-of-vl-read-until-end-of-define-weak
    (<= (acl2-count (mv-nth 2 (vl-read-until-end-of-define echars config)))
        (acl2-count (vl-echarlist-fix echars)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force) (:d vl-read-until-end-of-define))
            :induct (vl-read-until-end-of-define echars config)
            :expand ((vl-read-until-end-of-define echars config)))))

  (defthm acl2-count-of-vl-read-until-end-of-define-strong
    (implies (mv-nth 1 (vl-read-until-end-of-define echars config))
             (< (acl2-count (mv-nth 2 (vl-read-until-end-of-define echars config)))
                (acl2-count (vl-echarlist-fix echars))))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force) (:d vl-read-until-end-of-define))
            :induct (vl-read-until-end-of-define echars config)
            :expand ((vl-read-until-end-of-define echars config))))))



(define vl-read-define-default-text
; Matt K. mod: Deleted non-existent parent, letting set-default-parents take
; charge here.  (Jared thought this made sense, too.)
; :parents (vl-read-default-text)
  ((echars       vl-echarlist-p "Text starting just after the equal sign.")
   (starting-loc vl-location-p "Context for error messages.")
   (ppst))
  :returns
  (mv (successp  booleanp :rule-classes :type-prescription)
      (prefix    vl-echarlist-p)
      (remainder vl-echarlist-p
                 "On success this should start with a comma or endparen.")
      (ppst))
  :measure (acl2-count (vl-echarlist-fix echars))

  ;; SystemVerilog-2012 page 640 says that "The default text may be explicitly
  ;; specified to be empty by adding an = token after a formal argument name,
  ;; followed by a comma (or a right parenthesis if it is the last argument in
  ;; the argument list.)"  So, things like `define foo(a, b=) should be OK and
  ;; we don't have to check for non-emptiness.

  ;; BOZO SystemVerilog-2012 page 641, says that "Actual arguments and defaults
  ;; shall not contain commas or right parenthesis characters outside matched
  ;; pairs of left and right parentheses (), square brackets [], braces {},
  ;; double quotes "", or an escaped identifier.
  ;;
  ;; We probably aren't handling all of this correctly yet and for that matter
  ;; we should do a lot of testing to see what other Verilog tools handle and
  ;; add suitable failtests/cosims that explore the corner cases.
  ;;
  ;; But for now, the following should at least be better than what we used to
  ;; do (namely: die when we encountered an equal sign.)
  (b* ((echars (vl-echarlist-fix echars))
       ((when (atom echars))
        (let ((ppst (vl-ppst-fatal
                     :msg "~a0: EOF while reading `define default text."
                     :args (list starting-loc))))
          (mv nil nil echars ppst)))

       (char1 (vl-echar->char (car echars)))

       ((when (or (eql char1 #\,)
                  (eql char1 #\))))
        ;; Ran into a bare comma or ) character, so this seems like the end of
        ;; this default-text, assuming we're smart enough to ignore string
        ;; literals, etc.
        (mv t nil echars ppst))

       ((when (eql char1 #\\))
        ;; Maybe the start of an escaped identifier.
        (b* (((mv name prefix1 remainder)
              (vl-read-escaped-identifier echars))
             ((unless name)
              (let ((ppst (vl-ppst-fatal
                           :msg "~a0: stray backslash in define default argument?"
                           :args (list (vl-echar->loc (car echars))))))
                (mv nil nil echars ppst)))
             ((mv okp prefix2 remainder ppst)
              (vl-read-define-default-text remainder starting-loc ppst))
             ((unless okp)
              ;; already warned
              (mv nil nil echars ppst)))
          (mv t (append prefix1 prefix2) remainder ppst)))

       ((when (eql char1 #\"))
        ;; Maybe the start of a string literal?
        (b* (((mv string prefix1 remainder)
              (vl-read-string echars (vl-lexstate-init (vl-ppst->config))))
             ((unless string)
              (let ((ppst (vl-ppst-fatal
                           :msg "~a0: unterminated string literal in `define default argument?"
                           :args (list (vl-echar->loc (car echars))))))
                (mv nil nil echars ppst)))
             ((mv okp prefix2 remainder ppst)
              (vl-read-define-default-text remainder starting-loc ppst))
             ((unless okp)
              ;; already warned
              (mv nil nil echars ppst)))
          (mv t (append prefix1 prefix2) remainder ppst)))

       ;; Otherwise plausibly this is just an ordinary character that should
       ;; become part of the text?
       ((mv okp rest remainder ppst)
        (vl-read-define-default-text (cdr echars) starting-loc ppst))
       ((unless okp)
        (mv nil nil echars ppst)))
    (mv t (cons (car echars) rest) remainder ppst))
  ///
  (defthm true-listp-of-vl-read-define-default-text-prefix
    (true-listp (mv-nth 1 (vl-read-define-default-text echars starting-loc ppst)))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-read-define-default-text-remainder
    (true-listp (mv-nth 2 (vl-read-define-default-text echars starting-loc ppst)))
    :rule-classes :type-prescription)

  (defthm acl2-count-of-vl-read-define-default-text-weak
    (<= (acl2-count (mv-nth 2 (vl-read-define-default-text echars config starting-loc)))
        (acl2-count (vl-echarlist-fix echars)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm acl2-count-of-vl-read-define-default-text-strong
    (implies (mv-nth 1 (vl-read-define-default-text echars config starting-loc))
             (< (acl2-count (mv-nth 2 (vl-read-define-default-text echars config starting-loc)))
                (acl2-count (vl-echarlist-fix echars))))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force))))))


(define vl-parse-define-formal-arguments
  ;; Match list_of_formal_arguments, also eating the close paren and returning
  ;; the remaining text after the close paren.
  :parents (vl-split-define-text)
  ((text         vl-echarlist-p "Text after the opening paren, or after some comma.")
   (starting-loc vl-location-p  "Context for error messages.")
   (ppst))
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (formals  vl-define-formallist-p)
      (body     vl-echarlist-p "Remaining characters after the closing paren.")
      (ppst))
  :measure (acl2-count (vl-echarlist-fix text))
  (b* ((text (vl-echarlist-fix text))
       ((when (atom text))
        (let ((ppst (vl-ppst-fatal
                     :msg "~a0: `define arguments are not closed."
                     :args (list starting-loc))))
          (mv nil nil nil ppst)))

       ;; This is a mess -- without a lexer we're always having to eat whitespace.
       ((mv ?ws rest) (vl-read-while-whitespace text))
       ((mv id rest)  (vl-read-simple-identifier rest))
       ((unless id)
        (let ((ppst (vl-ppst-fatal
                     :msg "~a0: invalid `define argument name."
                     :args (list (vl-echar->loc (car text))))))
          (mv nil nil nil ppst)))

       (name1 (vl-echarlist->string id))
       ;; ;; Prohibit using keywords as arguments.  Of course, the valid keywords
       ;; ;; are governed by the Verilog edition... blaaah...
       ;; ((when (vl-keyword-lookup name1 (vl-lexstate->kwdtable (vl-lexstate-init config))))
       ;;  (mv (cw "Preprocessor error (~f0): keyword ~s1 not permitted as `define argument~%~%"
       ;;          (vl-location-string (vl-echar->loc (car text)))
       ;;          name1)
       ;;      nil nil))

       ((mv ?ws rest) (vl-read-while-whitespace rest))

       ((mv okp default rest ppst)
        (b* (((unless (and (consp rest)
                           (eql (vl-echar->char (car rest)) #\=)))
              ;; No equal sign --> no default value
              (mv t nil rest ppst))
             (rest (cdr rest)) ;; Eat the equal sign
             ((mv okp prefix rest ppst)
              (vl-read-define-default-text rest starting-loc ppst)))
          (mv okp (vl-echarlist->string prefix) rest ppst)))

       ((unless okp)
        ;; Already warned.
        (mv nil nil nil ppst))

       ((mv ?ws rest) (vl-read-while-whitespace rest))

       (formal1 (make-vl-define-formal :name name1 :default default))
       ((when (and (consp rest)
                   (eql (vl-echar->char (car rest)) #\))))
        ;; End of arguments, woohoo.  Eat final closing paren and we're done.
        (mv t (list formal1) (cdr rest) ppst))

       ((unless (and (consp rest)
                     (eql (vl-echar->char (car rest)) #\,)))
        (let ((ppst (vl-ppst-fatal
                     :msg "~a0: expected next `define argument or end of arguments."
                     :args (list (if (consp rest)
                                     (vl-echar->loc (car rest))
                                   ;; Blah, not quite right, probably close enough to be useful
                                   (vl-echar->loc (car text)))))))
          (mv nil nil nil ppst)))

       ;; Else, found a comma: eat it, recur, etc.
       (starting-loc (vl-echar->loc (car rest)))
       (rest         (cdr rest))
       ((mv rest-okp rest-formals body ppst)
        (vl-parse-define-formal-arguments rest starting-loc ppst))
       ((unless rest-okp)
        ;; Already printed an error message.
        (mv nil nil nil ppst))
       (formals (cons formal1 rest-formals)))
    (mv t formals body ppst)))

(define vl-split-define-text
  :short "Split up the rest of a define line into macro arguments and macro text."
  ((text vl-echarlist-p "The text that occurs after @('`define foo'), perhaps
                         including any macro arguments such as @('(a,b)') in
                         the case of macros such as @('`define max(a,b) ...').")
   (ppst))
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (formals  vl-define-formallist-p)
      (body     vl-echarlist-p "Remaining characters after any macro arguments.")
      (ppst))
  (b* ((text (vl-echarlist-fix text))
       ((unless (and (consp text)
                     (eql (vl-echar->char (car text)) #\()))
        ;; SystemVerilog-2012: Page 640: "If formal arguments are used [...]
        ;; the left parenthesis shall follow the text macro name immediately,
        ;; with no space in between."  Since we have no opening paren, this
        ;; macro does NOT have arguments, and all text belongs to the macro
        ;; itself.
        (mv t nil (vl-echarlist-fix text) ppst)))
    ;; Else, eat the opening paren and go do the actual parsing.
    (vl-parse-define-formal-arguments (cdr text) (vl-echar->loc (car text)) ppst)))

(define vl-process-define
  :short "Handler for @('define') directives."
  ((loc     vl-location-p)
   (echars  vl-echarlist-p)
   (ppst))
  :returns
  (mv (successp)
      (remainder   vl-echarlist-p)
      (ppst))

  :long "<p>We assume that @('`define') has just been read and @('echars') is
the text which comes right after the @('`define') directive.  We read the name
and text for this new macro definition, and update the defines table
appropriately if @('activep') is set.</p>"

  (b* ((echars (vl-echarlist-fix echars))
       ((mv & remainder)      (vl-read-while-whitespace echars))
       ((mv name & remainder) (vl-read-identifier remainder))
       ((unless name)
        (let ((ppst (vl-ppst-fatal
                     :msg "~a0: found a `define without a name."
                     :args (list loc))))
          (mv nil echars ppst)))
       ((when (vl-is-compiler-directive-p name))
        (let ((ppst (vl-ppst-fatal
                     :msg "~a0: refusing to permit `define ~s1."
                     :args (list loc name))))
          (mv nil echars ppst)))

       ((mv successp text remainder ppst)
        (vl-read-until-end-of-define remainder ppst))

       ((unless successp)
        ;; Error message was already printed, so we just need to return
        ;; failure.
        (mv nil echars ppst))

       ((unless (vl-ppst->activep))
        ;; This define happens in an ifdef'd out context anyway, so we just
        ;; wanted to skip over it.  It looks like we're doing nothing here,
        ;; but it's important that we got called and went to the trouble of
        ;; parsing the define line, since this ensures there is no nested
        ;; `endif, etc. in the definition.
        (mv t remainder ppst))

       ((mv okp formals body ppst) (vl-split-define-text text ppst))
       ((unless okp)
        ;; Error message was already printed, so we just need to return
        ;; failure.
        (mv nil remainder ppst))

       (formal-names (vl-define-formallist->names formals))
       ((unless (uniquep formal-names))
        (let ((ppst (vl-ppst-fatal
                     :msg "~a0: `define ~s1 has repeated arguments ~&2."
                     :args (list loc name (duplicated-members formal-names)))))
          (mv nil echars ppst)))

       (new-def (make-vl-define :name    name
                                :formals formals
                                :body    (vl-echarlist->string body)
                                :loc     loc
                                :stickyp nil))

       ;; Warn if we're redefining something.
       (defines (vl-ppst->defines))
       (prev-def (vl-find-define name defines))
       (ppst (b* (((unless prev-def)
                   ppst)
                  (new-str (str::trim (vl-define->body new-def)))
                  (old-str (str::trim (vl-define->body prev-def)))
                  ((when (equal new-str old-str))
                   ;; Don't warn, redefining it in exactly the same way, modulo
                   ;; whitespace.
                   ppst))
               (vl-ppst-warn
                :type (if (vl-define->stickyp prev-def)
                          :vl-warn-define-ignored
                        :vl-warn-define-smashed)
                :msg  (if (vl-define->stickyp prev-def)
                          "Preprocessor warning: ignoring redefinition of ~s0:~% ~
                           - Keeping  ~s1     // from ~a2~% ~
                           - Ignoring ~s3     // from ~a4~%"
                        "Preprocessor warning: redefining ~s0:~% ~
                         - Was ~s1     // from ~a2~% ~
                         - Now ~s3     // from ~a4~%")
                :args (list name
                            old-str
                            (vl-define->loc prev-def)
                            new-str
                            loc))))

       (defines (cond ((and prev-def
                            (vl-define->stickyp prev-def))
                       ;; Ignore the new definition, keep the old.
                       defines)
                      (prev-def
                       ;; Not sticky so delete the old definition and add the new.
                       (vl-add-define new-def (vl-delete-define name defines)))
                      (t
                       ;; No old definition, add the new one.
                       (vl-add-define new-def defines))))
       (ppst (vl-ppst-update-defines defines)))

    (mv t remainder ppst))

  ///
  (defthm true-listp-of-vl-process-define-remainder
    (true-listp (mv-nth 1 (vl-process-define loc echars ppst)))
    :rule-classes :type-prescription)

  (defthm acl2-count-of-vl-process-define
    (<= (acl2-count (mv-nth 1 (vl-process-define loc echars ppst)))
        (acl2-count (vl-echarlist-fix echars)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm acl2-count-of-vl-process-define-strong
    (implies (mv-nth 0 (vl-process-define loc echars ppst))
             (< (acl2-count (mv-nth 1 (vl-process-define loc echars ppst)))
                (acl2-count (vl-echarlist-fix echars))))
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
The system tests (centaur/vl/systest) do try to test some tricky cases, but
there may well be mismatches left.</p>"
  ((name   stringp          "Name of macro being expanded, e.g., @('max'), for error messages.")
   (echars vl-echarlist-p   "Text we're parsing, initially follows an open paren or comma.")
   (loc    vl-location-p    "Location information in case of error messages.")
   (stk    character-listp  "Stack of open paren/bracket/brace characters.")
   (acc    vl-echarlist-p   "Text we've matched so far.")
   (ppst))
  :returns
  (mv (successp  booleanp :rule-classes :type-prescription "Was there any error?")
      (morep     booleanp :rule-classes :type-prescription "Is this the last actual?")
      (actual    stringp  :rule-classes :type-prescription "Contents of the actual as a string.")
      (remainder vl-echarlist-p "Remaining characters past the comma/closing paren.")
      (ppst))
  :measure (acl2-count (vl-echarlist-fix echars))
  (b* ((echars (vl-echarlist-fix echars))
       ((when (atom echars))
        ;; Error because we expect to eventually find a closing paren.
        (let ((ppst (vl-ppst-fatal
                     :msg "~a0: unexpected end of input while processing ~
                           arguments to `~s1."
                     :args (list loc name))))
          (mv nil nil "" echars ppst)))

       (char1 (vl-echar->char (car echars)))
       (loc1  (vl-echar->loc  (car echars)))

       ((when (eql char1 #\"))
        ;; BOZO this isn't quite right -- it assumes Verilog-2012 string
        ;; literal syntax even if we're trying to parse Verilog-2005 code.  Fix
        ;; it if we ever care.
        (b* (((mv str prefix remainder)
              (vl-read-string echars (vl-lexstate-init (vl-ppst->config))))
             ((unless str)
              (let ((ppst (vl-ppst-fatal
                           :msg "~a0: bad string literal while processing ~
                                 arguments to `~s1."
                           :args (list loc1 name))))
                (mv nil nil "" echars ppst)))
             (acc (revappend prefix acc)))
          (vl-parse-define-actual name remainder loc stk acc ppst)))

       ((when (and (eql char1 #\`)
                   (consp (cdr echars))
                   (eql (vl-echar->char (second echars)) #\")))
        ;; Very weirdly, and from nowhere in the standard that I am aware of,
        ;; other tools seem to permit things like the following:
        ;;
        ;;    `define foo(x) x
        ;;    `foo(`"bar`")
        ;;
        ;; I don't see why in the world we could use `" during the macro text, but
        ;; it seems like they permit it.  Other findings:
        ;;
        ;;    `foo("bar`")     -- works on other tools, resulting string is bar`
        ;;    `foo(`"\101bc`") -- works on other tools, resulting string is Abc
        ;;    `foo(`"bar")     -- parse error on other tools
        ;;    `foo(`"bar)      -- parse error on other tools
        ;;
        ;; It also seems to be a parse error in other tools to try to split the
        ;; actual by doing some trick like this:
        ;;
        ;;     `define foo(x) x`"
        ;;     `foo(`"bar)
        ;;
        ;; Curiously some tools (but not others) also seem to tolerate uses of
        ;; `" that do not even occur in macro text, such as:
        ;;
        ;;    logic [31:0] msg = `"foo`";
        ;;
        ;; At any rate, if we see a `" here, I'll try to parse a string and
        ;; then chop off the extra ` that we read.  This should handle octal
        ;; escapes like \101.  No idea how this is supposed to compare with
        ;; things like {}/()/[] matching and so on.
        (b* (((mv str prefix remainder)
              (vl-read-string (cdr echars) (vl-lexstate-init (vl-ppst->config))))
             ((unless str)
              (let ((ppst (vl-ppst-fatal
                           :msg "~a0: bad string literal while processing ~
                                 arguments to `~s1."
                           :args (list loc1 name))))
                (mv nil nil "" echars ppst)))
             (len (length str))
             ((unless (and (< 0 len)
                           (equal (char str (- len 1)) #\`)))
              (let ((ppst (vl-ppst-fatal
                           :msg "~a0: found string literal with backtick-escaped ~
                                 open quote but regular closing quote, i.e., ~
                                 `\"...\", while processing arguments to ~s1."
                           :args (list loc1 name))))
                (mv nil nil "" echars ppst)))
             ;; At this point we know we have found:
             ;;   `" ... `"
             ;; And prefix omits the leading `, so we really have in prefix: "...`"
             ;; We want to eat the `.  So to clean that up:
             (rprefix (rev prefix))
             (rprefix-fixed (cons (first rprefix) (cddr rprefix)))
             ;; Now rprefix-fixed is the reverse string without the grave characters
             ;; but with the quotes, as desired.  Since we've already reversed it,
             ;; we can just append it onto the acc.
             (acc (append rprefix-fixed acc)))
          (vl-parse-define-actual name remainder loc stk acc ppst)))

       ((when (eql char1 #\\))
        (b* (((mv name prefix remainder) (vl-read-escaped-identifier echars))
             ((unless name)
              (let ((ppst (vl-ppst-fatal
                           :msg "~a0:  stray backslash while processing ~
                                 arguments to `~s1."
                           :args (list loc1 name))))
                (mv nil nil "" echars ppst)))
             (acc (revappend prefix acc)))
          (vl-parse-define-actual name remainder loc stk acc ppst)))

       ((when (eql char1 #\/))
        ;; NCVerilog and VCS seem to skip over comments here, so we'll do the same...
        (b* (((when (vl-matches-string-p "//" echars))
              ;; start of a single-line comment; read until end of line.
              (b* (((mv successp ?prefix remainder)
                    (vl-read-until-literal *nls* (cddr echars)))
                   ((unless successp)
                    (let ((ppst (vl-ppst-fatal
                                 :msg "~a0: unexpected EOF while reading ~
                                       macro arguments to ~s1."
                                 :args (list loc1 name))))
                      (mv nil nil "" echars ppst))))
                ;; It might be nice to preserve the comment.  On the other
                ;; hand, that would possibly replicate the comment in many
                ;; places.  I think it seems reasonable to just drop it.
                (vl-parse-define-actual name remainder loc stk acc ppst)))

             ((when (vl-matches-string-p "/*" echars))
              (b* (((mv successp ?prefix remainder)
                    (vl-read-through-literal "*/" (cddr echars)))
                   ((unless successp)
                    (let ((ppst (vl-ppst-fatal
                                 :msg "~a0: block comment is never closed."
                                 :args (list (vl-echar->loc (car echars))))))
                      (mv nil nil "" echars ppst))))
                ;; As with single-line comments, we'll just drop the comment.
                (vl-parse-define-actual name remainder loc stk acc ppst))))

          ;; Otherwise, just an ordinary division operation, accumulate it as
          ;; usual, no effect on the stk.
          (vl-parse-define-actual name (cdr echars) loc stk (cons (car echars) acc) ppst)))

       ((when (member char1 '(#\( #\[ #\{)))
        ;; Open bracket -- Fine, push it on the stack so we can balance it.
        (b* ((stk (cons char1 stk))
             (acc (cons (car echars) acc)))
          (vl-parse-define-actual name (cdr echars) loc stk acc ppst)))

       ((when (member char1 '(#\) #\] #\})))
        ;; Close bracket or paren...
        (b* (((when (and (eql char1 #\))
                         (atom stk)))
              ;; Closing right paren with no other brackets open means that we
              ;; have reached the end of the arguments.
              (mv t
                  nil ;; Closing paren means no more arguments!
                  (reverse (vl-echarlist->string acc))
                  (cdr echars)
                  ppst))
             ;; Otherwise, a closing bracket/paren/brace is only okay if a
             ;; matching opening bracket/paren/brace is already open.
             (matching-char (case char1 (#\) #\() (#\] #\[) (#\} #\{)))  ;; escape all the things
             ((unless (and (consp stk)
                           (eql (car stk) matching-char)))
              (let ((ppst (vl-ppst-fatal
                           :msg "~a0: unbalanced ~s1 vs. ~s2 in arguments to `~s3."
                           :args (list loc1
                                       (implode (list matching-char))
                                       (implode (list char1))
                                       name))))
                (mv nil nil "" echars ppst)))
             ;; Else, fine, it was balanced
             (stk (cdr stk))
             (acc (cons (car echars) acc)))
          (vl-parse-define-actual name (cdr echars) loc stk acc ppst)))

       ((when (and (atom stk)
                   (eql char1 #\,)))
        ;; Comma encountered with no open braces/parents/brackets means that we
        ;; have reached the end of this argument
        (mv t
            t ;; comma means there are more arguments
            (reverse (vl-echarlist->string acc))
            (cdr echars)
            ppst)))

    ;; If we get here, then it wasn't any special character or it was a comma
    ;; that happened to be in a bracket/paren/brace region, so we want to just
    ;; accumulate it anyway.  Keep reading this actual.
    (vl-parse-define-actual name (cdr echars) loc stk (cons (car echars) acc) ppst))
  ///
  (local (in-theory (disable (:d vl-parse-define-actual))))
  (defthm acl2-count-of-vl-parse-define-actual
    (b* (((mv successp ?morep ?actual remainder ?ppst)
          (vl-parse-define-actual name echars loc stk acc ppst)))
      (implies successp
               (< (acl2-count remainder)
                  (acl2-count (vl-echarlist-fix echars)))))
    :hints ((acl2::just-induct-and-expand
             (vl-parse-define-actual name echars loc stk acc ppst)))
    :rule-classes ((:rewrite) (:linear))))


(define vl-parse-define-actuals
  :parents (vl-expand-define)
  :short "Collect the arguments to a macro, like @('`max(a+b, c)')."
  ((name   stringp          "Name of macro being expanded, e.g., @('max'), for error messages.")
   (echars vl-echarlist-p   "Text that follows the initial open paren, or that follows a comma.")
   (loc    vl-location-p    "Location information in case of error messages.")
   (ppst))
  :returns
  (mv (successp  booleanp :rule-classes :type-prescription)
      (actuals   string-listp)
      (remainder vl-echarlist-p
                 "Remainder of the input stream after eating all the actuals and also
                  the closing paren.")
      (ppst))
  :measure (acl2-count (vl-echarlist-fix echars))
  (b* (((mv successp morep actual1 echars ppst)
        (vl-parse-define-actual name echars loc nil nil ppst))
       ((unless successp)
        ;; Already printed an error message.
        (mv nil nil echars ppst))
       ((unless morep)
        ;; That was the last formal.  We already ate the closing paren.
        (mv t (list actual1) echars ppst))
       ((mv successp rest-actuals echars ppst)
        (vl-parse-define-actuals name echars loc ppst))
       ((unless successp)
        (mv nil nil echars ppst)))
    (mv t (cons actual1 rest-actuals) echars ppst)))

(define vl-check-remaining-formals-all-have-defaults
  ((x    vl-define-formallist-p)
   (name stringp       "Name of macro being expanded, context for error messages.")
   (loc  vl-location-p "Location of macro being expanded, context for error messages.")
   (ppst))
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (ppst))
  (b* (((when (atom x))
        (mv t ppst))
       ((vl-define-formal x1) (car x))
       ;; [Jared] Merge BOZO.  Sol was checking whether (str::trim x1.default)
       ;; was empty.  Is that what we want?  I think we want a nil check
       ;; instead?  Write a directed failtest for this to be sure.
       ((unless x1.default)
        (let ((ppst (vl-ppst-fatal
                     :msg "~a0: too few arguments to ~s1 (no default value ~
                           for ~s2)."
                     :args (list loc name x1.name))))
          (mv nil ppst))))
    (vl-check-remaining-formals-all-have-defaults (cdr x) name loc ppst)))

(defprojection vl-define-formallist->defaults ((x vl-define-formallist-p))
  (vl-define-formal->default x))

(local (defthm string-listp-of-vl-define-formallist->defaults
         (implies (mv-nth 0 (vl-check-remaining-formals-all-have-defaults formals name loc ppst))
                  (string-listp (vl-define-formallist->defaults formals)))
         :hints(("Goal"
                 :in-theory (enable vl-check-remaining-formals-all-have-defaults)))))

(define vl-line-up-define-formals-and-actuals
  ((formals vl-define-formallist-p)
   (actuals string-listp)
   (name    stringp       "Name of macro being expanded, context for error messages.")
   (loc     vl-location-p "Location of macro being expanded, context for error messages.")
   (ppst))
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (subst    (and (alistp subst)
                     (string-listp (alist-keys subst))
                     (string-listp (alist-vals subst))))
      (ppst))
  (b* (((when (atom formals))
        (if (atom actuals)
            ;; Ran out of formals and actuals at the same time.  That's fine,
            ;; no more substitution to create.
            (mv t nil ppst)
          ;; Ran out of formals but still have actuals?  No sir, that's not ok.
          (let ((ppst (vl-ppst-fatal
                       :msg "~a0: too many arguments given to ~s1."
                       :args (list loc name))))
            (mv nil nil ppst))))

       ((when (atom actuals))
        ;; SystemVerilog-2012, page 641.  "If fewer actual arguments are
        ;; specified than the number of formal arguments, then the defaults are
        ;; substituted for the additional formal arguments.  It shall be an
        ;; error if any of the remaining formal arguments does not have a
        ;; default specified."
        (b* (((mv okp ppst)
              (vl-check-remaining-formals-all-have-defaults formals name loc ppst))
             ((when okp)
              ;; Fine, pair them up.
              (mv t
                  (pairlis$ (vl-define-formallist->names formals)
                            (vl-define-formallist->defaults formals))
                  ppst)))
          ;; Already printed an error, this is just an error.
          (mv nil nil ppst)))

       ((mv okp rest-subst ppst)
        (vl-line-up-define-formals-and-actuals (cdr formals) (cdr actuals) name loc ppst))
       ((unless okp)
        (mv nil nil ppst))

       ;; SystemVerilog-2012 Page 641: "An actual argument may be empty or
       ;; white space only, in which case the formal argument is substituted by
       ;; the argument default if one is specified, or by nothing if no default
       ;; is specified.
       ((vl-define-formal formal1) (car formals))
       (actual1 (str::trim (car actuals)))
       (value1  (if (and (equal actual1 "")
                         formal1.default)
                    (str::trim formal1.default)
                  actual1)))
    (mv t
        (cons (cons formal1.name value1) rest-subst)
        ppst)))


#||
(trace$ (vl-substitute-into-macro-text
         :entry
         (list 'vl-substitute-into-macro-text
               :body (vl-echarlist->string body)
               :subst subst
               :name name
               :reversed-acc (reverse (vl-echarlist->string acc)))
         :exit
         (list 'vl-substitute-into-macro-text
               :successp     (car acl2::values)
               :reversed-acc (reverse (vl-echarlist->string (second acl2::values))))))
||#

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
   (acc    vl-echarlist-p
           "Accumulated extended characters to be inserted into the file.")
   (ppst))
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (acc      vl-echarlist-p
                "Accumulated characters, still in reverse order.")
      (ppst))

  :long "<p>This is very underspecified.  We need to minimally skip over things
like string literals.  We can at least assume that the @('body') was accepted
by @(see vl-read-until-end-of-define).  We try to do something reasonably
sensible.</p>"

  :measure (acl2-count (vl-echarlist-fix body))
  ;; Styled after vl-read-until-end-of-define.
  (b* ((body (vl-echarlist-fix body))
       (acc (vl-echarlist-fix acc))
       ((when (atom body))
        (mv t acc ppst))
       (char1 (vl-echar->char (first body)))

       ((when (eql char1 #\`))
        (b* (((when (and (consp (cdr body))
                         (member (vl-echar->char (second body)) '(#\" #\`))))
              (case (vl-echar->char (second body))
                (#\"
                 ;; See SystemVerilog-2012 page 644.  I think `" is just
                 ;; supposed to expand into a literal quote mark.
                 (b* ((acc (cons (second body) acc)))
                   (vl-substitute-into-macro-text (cddr body) subst name loc acc ppst)))
                (#\`
                 ;; See SystemVerilog-2012 page 644.  I think `` is just
                 ;; supposed to disappear -- it is used to separate tokens
                 ;; in the macro body without introducing any whitespace.
                 (vl-substitute-into-macro-text (cddr body) subst name loc acc ppst))
                (otherwise
                 (mv (impossible) acc ppst))))

             ((when (and (consp (cdr body))
                         (consp (cddr body))
                         (consp (cdddr body))
                         (eql (vl-echar->char (second body)) #\\)
                         (eql (vl-echar->char (third body))  #\`)
                         (eql (vl-echar->char (fourth body)) #\")))
              ;; See SystemVerilog-2012 page 644.  I think `\`" is supposed
              ;; to turn into literally the sequence \".
              (b* ((acc (list* (fourth body)   ;; ", because reverse order
                               (second body)   ;; \, because reverse order
                               acc)))
                (vl-substitute-into-macro-text (cddddr body) subst name loc acc ppst)))

             ;; We previously read an identifier here and then just stuck it
             ;; into the accumulator.  However, it appears that NCVerilog and
             ;; VCS both support things like the following:
             ;;
             ;;    `define blah mywire
             ;;    `define mac(arg) wire `arg = 1;
             ;;    `mac(blah)                         // results in wire mywire = 1;
             ;;
             ;; Which means that it is NOT correct to just put `arg into the
             ;; accumulator.  Instead, we need to do things like argument
             ;; substitution here.  So, now don't try to read anything and just
             ;; keep going past the grave.

             ;; Old code was:
             ;;
             ;;    ((mv name prefix remainder) (vl-read-identifier (cdr body)))
             ;;    ((unless name)
             ;;     ;; Should be ruled out by vl-read-until-end-of-define
             ;;     (mv (cw "Preprocessor error (~f0): bad grave character in macro ~
             ;;              text for ~s1.~%~%"
             ;;             (vl-location-string loc) name)
             ;;         acc))
             ;;    (acc (revappend prefix (cons (car body) acc))))
             ;; (vl-substitute-into-macro-text remainder subst name loc config acc)))

             )
          (vl-substitute-into-macro-text (cdr body) subst name loc (cons (car body) acc) ppst)))

       ((when (eql char1 #\"))
        (b* (((mv string prefix remainder)
              (vl-read-string body (vl-lexstate-init (vl-ppst->config))))
             ((unless string)
              ;; Should be ruled out by vl-read-until-end-of-define
              (let ((ppst (vl-ppst-fatal
                           :msg "~a0: bad string literal in macro text for ~s1."
                           :args (list loc name))))
                (mv nil acc ppst)))
             (acc (revappend prefix acc)))
          (vl-substitute-into-macro-text remainder subst name loc acc ppst)))

       ((when (eql char1 #\\))
        ;; See vl-read-until-end-of-define.  Line continuations should already
        ;; have been eaten and replaced by spaces here.  The only reason we
        ;; should see a backslash, then, is for escaped identifiers.

        ;; We used to do a lot here to try to properly parse escaped
        ;; identifiers, and it appears that in some cases (see for instance
        ;; tests.lisp, corner8 and corner9).  NCVerilog is doing something
        ;; different than we are for escaped identifiers.  However, this very
        ;; simple behavior seems to agree with VCS so far, so I think it is
        ;; perhaps an improvement...
        (vl-substitute-into-macro-text (cdr body) subst name loc
                                       (cons (car body) acc)
                                       ppst))

       ;; Old code for \...
       ;;
       ;; (b* (((mv name prefix remainder)
       ;;       (vl-read-escaped-identifier body))
       ;;      ((unless name)
       ;;       ;; Should be ruled out by vl-read-until-end-of-define.
       ;;       (mv (cw "Preprocessor error (~f0): stray backslash in macro ~
       ;;                text for ~s1.~%~%"
       ;;               (vl-location-string loc) name)
       ;;           acc))
       ;;
       ;;      ;; No---Gods, why?  There are horrible corner cases here.
       ;;      ;; Consider something like this:
       ;;      ;;
       ;;      ;;    `define mac(name) wire \mac_``name ;
       ;;      ;;
       ;;      ;; VCS and NCVerilog agree that `mac(foo) should result in a wire
       ;;      ;; named \mac_foo being defined.  But that is horrible.  It means
       ;;      ;; that the ` is no longer part of the escaped identifier but is
       ;;      ;; instead some special thing.
       ;;      ;;
       ;;      ;;
       ;;      ;; In contrast, a macro like this:
       ;;      ;;
       ;;      ;;    `define mac(name) wire \``name``_mac ;
       ;;      ;;
       ;;      ;; Seems to mean that `mac(foo) produces:
       ;;      ;;
       ;;      ;;    On VCS: a wire named \foo_foo
       ;;      ;;    On NCV: a wire named \``foo_mac
       ;;      ;;
       ;;      ;; I am sure there is plenty of other esoterica.  As a horrible
       ;;      ;; hack that is hopefully sufficient, I will treat grave
       ;;      ;; characters in a special way and just try to stop reading once
       ;;      ;; any grave character is encountered.
       ;;      ((unless (str::substrp "`" name))
       ;;       (b* ((acc (revappend prefix acc)))
       ;;         (vl-substitute-into-macro-text remainder subst name loc config acc)))
       ;;
       ;;      ;; Found grave, so do some awful thing...
       ;;      (acc (cons (car body) acc))
       ;;      ((mv okp prefix remainder) (vl-read-until-literal "`" (cdr body)))
       ;;      ((unless okp)
       ;;       (mv (raise "Impossibly failed to find grave character after already ~
       ;;                   finding it earlier.  Jared thinks this is impossible.")
       ;;           acc))
       ;;      (acc (revappend prefix acc)))
       ;;   (vl-substitute-into-macro-text remainder subst name loc config acc)))

       ((when (eql char1 #\/))
        (b* (((when (vl-matches-string-p "//" body))
              ;; Single-line comments are eaten by vl-read-until-end-of-define,
              ;; so we shouldn't need to deal with them here.
              (let ((ppst (vl-ppst-fatal
                           :msg "~a0: //-style comment in macro text for ~s1? ~
                                 Jared thinks this shouldn't happen."
                           :args (list loc name))))
                (mv nil acc ppst)))

             ((when (vl-matches-string-p "/*" body))
              (b* (((mv successp prefix remainder)
                    (vl-read-through-literal "*/" (cddr body)))
                   ((unless successp)
                    ;; Should be ruled out by vl-read-until-end-of-define.
                    (let ((ppst (vl-ppst-fatal
                                 :msg "~a0: unterminated /* ... */ style ~
                                       comment in macro text for ~s1?  Jared ~
                                       thinks this shouldn't happen."
                                 :args (list loc name))))
                      (mv nil acc ppst)))
                   (acc (revappend (list* (first body) (second body) prefix) acc)))
                (vl-substitute-into-macro-text remainder subst name loc acc ppst))))

          ;; Else: regular division character, treat it as a regular character.
          (vl-substitute-into-macro-text (cdr body) subst name loc (cons (car body) acc) ppst)))

       ;; Else, not a special character.
       ;; We know that macro arguments are simple identifiers.
       ((unless (vl-simple-id-head-p char1))
        (vl-substitute-into-macro-text (cdr body) subst name loc (cons (car body) acc) ppst))

       ;; We don't bother to check for keywords here, because we shouldn't
       ;; allow keywords as formals in the first place, so they just shouldn't
       ;; be in our substitution to begin with
       ((mv prefix remainder) (vl-read-simple-identifier body))
       (str  (vl-echarlist->string prefix))
       (look (assoc-equal str subst))
       ((unless look)
        ;; Found an identifier but it's not related to the formals.  Just
        ;; accumulate its characters.
        (vl-substitute-into-macro-text remainder subst name loc (revappend prefix acc) ppst))

       ;; Conversion of replacement text into echars is subtle.  See the
       ;; comments in vl-expand-define to understand why we do this.
       (replacement-str    (cdr look))
       (replacement-echars (vl-echarlist-from-str replacement-str))
       (replacement-fixed  (vl-change-echarlist-locations replacement-echars loc))
       (acc                (revappend replacement-fixed acc)))
    (vl-substitute-into-macro-text remainder subst name loc acc ppst))

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
   (echars  vl-echarlist-p  "Remaining text after the name.  For simple macros like @('`foo') we
                             will just need to append the definition's body onto these characters.
                             For macros with arguments we will need to extract the actuals from
                             these characters.")
   (loc     vl-location-p   "Location for error messages and for the resulting expansion text.")
   (ppst))
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (new-echars vl-echarlist-p
                  "On success, the updated characters with the macro invocation replaced by
                   its expansion.")
      (ppst))

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

  (b* ((echars (vl-echarlist-fix echars))
       (lookup (vl-find-define name (vl-ppst->defines)))
       ((unless lookup)
        (let ((ppst (vl-ppst-fatal
                     :msg "~a0: `~s1 is not defined."
                     :args (list loc name))))
          (mv nil echars ppst)))

       ((vl-define lookup))
       ((when (atom lookup.formals))
        ;; No arguments to process, just insert the body of the macro.
        ;;
        ;; Historically we just got the body and dumped it into the file after
        ;; changing its locations, like this:
        ;;
        ;; (b* ((body-str    lookup.body)
        ;;      (body-echars (vl-echarlist-from-str body-str))
        ;;      (body-fixed  (vl-change-echarlist-locations body-echars loc)))
        ;;   (mv t (append body-fixed echars))))
        ;;
        ;; That turns out to be not quite correct in the case of goofy macros
        ;; such as:  `define FOO `"foo`", because we end up just dumping the
        ;; `" directly into the body instead of expanding it.  So even though
        ;; there are no arguments, we now call substitute-into-macro-text.
        (b* (((mv okp rev-replacement-body ppst)
              (vl-substitute-into-macro-text (vl-change-echarlist-locations
                                              (vl-echarlist-from-str lookup.body)
                                              loc)
                                             nil ;; no formals->actual substitution
                                             name loc nil ppst))
             ((unless okp) (mv nil echars ppst)) ;; Already printed error
             (replacement-body (rev rev-replacement-body))
             (echars (append replacement-body echars)))
          (mv t echars ppst)))

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
        (let ((ppst (vl-ppst-fatal
                     :msg "~a0: `~s1 requires arguments."
                     :args (list loc name))))
          (mv nil echars ppst)))

       (echars (cdr echars)) ;; Eat leading '(' character
       ((mv successp actuals echars ppst) (vl-parse-define-actuals name echars loc ppst))
       ((unless successp) (mv nil echars ppst)) ;; Already printed error

       ;; Note: at this point, we've already eaten the final ')' character so
       ;; the echars now contain all of the input stream except that we need to
       ;; inject the expansion of this macro.  All that's left to do is to line
       ;; up the actuals and formals, and substitute into the macro body.
       ((mv successp subst ppst)
        (vl-line-up-define-formals-and-actuals lookup.formals actuals name loc ppst))
       ((unless successp) (mv nil echars ppst)) ;; Already printed error

       ((mv okp rev-replacement-body ppst)
        (vl-substitute-into-macro-text (vl-change-echarlist-locations
                                        (vl-echarlist-from-str lookup.body)
                                        loc)
                                       subst name loc nil ppst))
       ((unless okp) (mv nil echars ppst)) ;; Already printed error

       (replacement-body (rev rev-replacement-body))
       (echars (append replacement-body echars)))
    (mv t echars ppst)))


(define vl-process-undef
  :short "Handler for @('undef') directives."
  ((loc     vl-location-p)
   (echars  vl-echarlist-p)
   (ppst))
  :returns
  (mv (successp)
      (remainder   vl-echarlist-p)
      (ppst))

  :long "<p>We assume that an @('`undef') has just been read and @('echars') is
the text which follows it.  We try to read the name we are to undefine, then
update the defines table appropriately.</p>"

  (b* ((echars (vl-echarlist-fix echars))
       ((mv & remainder)      (vl-read-while-whitespace echars))
       ((mv name & remainder) (vl-read-identifier remainder))
       ((unless name)
        (let ((ppst (vl-ppst-fatal
                     :msg "~a0: found an `undef without a name."
                     :args (list loc))))
          (mv nil echars ppst)))
       ((when (vl-is-compiler-directive-p name))
        (let ((ppst (vl-ppst-fatal
                     :msg "~a0: refusing to permit `undef ~s1."
                     :args (list loc name))))
          (mv nil echars ppst)))
       ((unless (vl-ppst->activep))
        ;; Not an active section, so don't actually do anything.
        (mv t remainder ppst))
       (defines (vl-ppst->defines))
       (lookup  (vl-find-define name defines))
       (ppst (if (not lookup)
                 (vl-ppst-warn
                  :type :vl-warn-undef
                  :msg "~a0: found `undef ~s1, but ~s1 is not defined."
                  :args (list loc name))
               (progn$ (cw-unformatted (cat (vl-ppst-pad) " Undefining " name *nls*))
                       ppst)))
       (defines (vl-delete-define name defines))
       (ppst (vl-ppst-update-defines defines)))
    (mv t remainder ppst))
  ///
  (defthm true-listp-of-vl-process-undef-remainder
    (true-listp (mv-nth 1 (vl-process-undef loc echars ppst)))
    :rule-classes :type-prescription)

  (defthm acl2-count-of-vl-process-undef
    (<= (acl2-count (mv-nth 1 (vl-process-undef loc echars ppst)))
        (acl2-count (vl-echarlist-fix echars)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm acl2-count-of-vl-process-undef-strong
    (implies (mv-nth 0 (vl-process-undef loc echars ppst))
             (< (acl2-count (mv-nth 1 (vl-process-undef loc echars ppst)))
                (acl2-count (vl-echarlist-fix echars))))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force))))))


(define vl-read-include
  :short "Read an @('`include') directive."
  ((echars vl-echarlist-p "Characters we're preprocessing.  We assume that
                           @('`include') was just read and removed from
                           @('echars').")
   (ppst))
  :returns (mv (filename (or (stringp filename)
                             (not filename))
                         :rule-classes :type-prescription)
               (prefix)
               (remainder)
               (ppst))

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
            (vl-read-string remainder (vl-lexstate-init (vl-ppst->config)))
          (mv nil nil remainder)))
       ((unless filename)
        (let ((ppst (vl-ppst-fatal
                     :msg "~a0: invalid `include directive."
                     :args (list (if (consp echars)
                                     (vl-echar->loc (car echars))
                                   "at end of file")))))
          (mv nil nil echars ppst))))
    (mv filename (append ws1 prefix) remainder ppst))
  ///
  (def-prefix/remainder-thms vl-read-include
    :formals (echars ppst)
    :prefix-n 1
    :remainder-n 2))

(define vl-filename-to-string-literal ((filename stringp))
  :returns (string stringp :rule-classes :type-prescription)
  (implode (append (vl-maybe-escape-string
                    filename 0 (length filename)
                    (list #\"))
                   (list #\"))))


(define vl-maybe-update-filemap ((realfile stringp)
                                 (contents vl-echarlist-p)
                                 ppst)
  :prepwork ((local (defthm alistp-when-vl-filemap-p-rw
                      (implies (vl-filemap-p x)
                               (alistp x))
                      :hints(("Goal" :in-theory (enable (tau-system)))))))
  (b* (((vl-loadconfig config) (vl-ppst->config))
       ((unless config.filemapp)
        ppst)
       (filemap (vl-ppst->filemap))
       ((when (assoc-equal realfile filemap))
        ;; Already have it in the filemap, so no need to add it again.  When
        ;; this wins, we avoid the expensive call of vl-echarlist->string and
        ;; may also save a good bit of memory.
        ppst)
       ;; Don't already have it, so add it.
       (filemap (cons (cons realfile (vl-echarlist->string contents))
                      filemap)))
    (vl-ppst-update-filemap filemap)))


(define vl-atvl-atts-text ((echars vl-echarlist-p))
  :returns (mv (atts-text vl-echarlist-p)
               (remainder vl-echarlist-p))
  (b* ((echars (vl-echarlist-fix echars))
       ((mv & prefix remainder)
        (vl-read-until-literal *nls* (rest-n 5 echars)))
       ((mv comment1p pre-comment1 post-comment1)
        (vl-read-until-literal "//" prefix))
       ((mv comment2p pre-comment2 post-comment2)
        (vl-read-until-literal "/*" prefix)))
    (cond ((acl2::and** comment1p comment2p)
           (if (< (len pre-comment1) (len pre-comment2))
               (mv pre-comment1 (append post-comment1 remainder))
             (mv pre-comment2 (append post-comment2 remainder))))
          (comment1p
           (mv pre-comment1 (append post-comment1 remainder)))
          (comment2p
           (mv pre-comment2 (append post-comment2 remainder)))
          (t
           (mv prefix remainder))))
  ///
  (defret true-listp-atts-text-of-<fn>
    (true-listp atts-text)
    :rule-classes :type-prescription)
  ;; ///
  ;; (defret acl2-count-of-<fn>
  ;;   (< (acl2-count remainder) (acl2-count (vl-echarlist-fix echars)))
  ;;   :rule-classes :linear)
  )

(with-output
  :off :all
  :on (error summary)

(define vl-preprocess-loop
  :short "Main loop for the preprocessor."
  :long "<p>We accumulate the transformed characters that are to be given to
  the lexer into acc, in reverse order.</p>"
  ((echars  vl-echarlist-p)
   (n       natp)
   (ppst)
   (state))
  :returns (mv (successp  booleanp :rule-classes :type-prescription)
               (remainder vl-echarlist-p)
               (ppst)
               (state))
  :measure (two-nats-measure n (acl2-count (vl-echarlist-fix echars)))
  :verify-guards nil
  :hints(("Goal" :in-theory (disable (force))))
  :prepwork (

             ;; Speed hint
             (local (in-theory (disable (:e tau-system)
                                        acl2::nthcdr-append
                                        acl2::lower-bound-of-len-when-sublistp
                                        ACL2::NTHCDR-WITH-LARGE-INDEX
                                        ACL2::CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP
                                        ACL2::LEN-WHEN-PREFIXP
                                        acl2::open-small-nthcdr
                                        acl2::nthcdr-of-cdr
                                        acl2::butlast-redefinition
                                        butlast-under-iff
                                        acl2::len-when-atom
                                        (:t prefix-of-vl-read-through-literal)
                                        acl2::len-of-nthcdr
                                        natp-when-posp
                                        acl2::nthcdr-when-atom
                                        (:t acl2::binary-and*)
                                        (:t acl2::binary-or*)
                                        no-change-loser-of-vl-read-while-whitespace
                                        not
                                        ))))
  (b* ((echars (vl-echarlist-fix echars))

       ((when (atom echars))
        (mv t echars ppst state))

       (echar1 (car echars))
       (char1  (vl-echar->char echar1))
       ((when (zp n))
        (let ((ppst (vl-ppst-fatal
                     :msg "~a0: ran out of steps. Macro expansion or file ~
                           inclusion loop?"
                     :args (list (vl-echar->loc echar1)))))
          (mv nil echars ppst state)))

       ;; Preliminaries.  We need to be sure to treat strings, escaped
       ;; identifiers, and comments atomically.  For instance, we don't want to
       ;; look at a string like "looks like an `endif to me" and think that we
       ;; have just read an `endif.

       ((when (eql char1 #\"))
        ;; Start of a string literal
        (b* (((mv string prefix remainder)
              (vl-read-string echars (vl-lexstate-init (vl-ppst->config))))
             ((unless string)
              ;; it already printed a warning, so we don't use cw.
              (mv nil echars ppst state))
             (ppst (vl-ppst-maybe-write prefix)))
          (vl-preprocess-loop remainder n ppst state)))

       ((when (eql char1 #\\))
        ;; Start of an escaped identifier
        (b* (((mv name prefix remainder) (vl-read-escaped-identifier echars))
             ((unless name)
              (let ((ppst (vl-ppst-fatal
                           :msg "~a0: stray backslash?"
                           :args (list (vl-echar->loc echar1)))))
                (mv nil echars ppst state)))
             (ppst (vl-ppst-maybe-write prefix)))
          (vl-preprocess-loop remainder n ppst state)))

       ((when (acl2::and** (eql char1 #\/)
                           (consp (cdr echars))
                           (eql (vl-echar->char (second echars)) #\/)))
        ;; Start of a one-line comment

        ;; SPECIAL VL EXTENSION.
        ;;
        ;; We decided we wanted a way to have code that only VL sees and that
        ;; other tools see as comments.  So, if we see a comment of the form
        ;;
        ;;   //+VL...\newline
        ;;
        ;; Then in the preprocessor we remove the //+VL part and just leave
        ;; "..." in the character stream.
        ;;
        ;; We wanted a shorthand for //+VL (* FOO *).  So, we say that //@VL
        ;; FOO is equivalent to this.  We then decided that it should be
        ;; permitted to put comments after the attributes, so as a special
        ;; convenience we recognize:
        ;;
        ;;    //@VL FOO // comment goes here    , and
        ;;    //@VL FOO /* comment starts here...
        ;;
        ;; And only read up to the start of the comment.  In other words, the
        ;; above expand into
        ;;
        ;;    (* FOO *) // comment goes here    , and
        ;;    (* FOO *) /* comment start here...
        ;;
        ;; respectively.
        (if (vl-matches-string-p "@VL" (cddr echars))
            (b* (((mv atts-text remainder)
                  ;; Figure out how much text we want to read for the attributes...
                  (vl-atvl-atts-text echars))
                 (atts (append (vl-echarlist-from-str "(*")
                               atts-text
                               (vl-echarlist-from-str "*)"))))
              ;; We leave the atts in the preprocessor's input stream so
              ;; that, e.g., defines can still get expanded in them.
              (vl-preprocess-loop (append atts remainder)
                                  (- n 1)
                                  ppst state))

          ;; Else, not a //@VL comment
          (b* (((mv & prefix remainder) (vl-read-until-literal *nls* (cddr echars)))
               ((when (vl-matches-string-p "+VL" prefix))
                ;; The // part is already gone, strip off the +VL part and
                ;; leave it in the preprocessor's input stream, as above.
                (vl-preprocess-loop (append (rest-n 3 prefix) remainder)
                                    (- n 1)
                                    ppst state))
               ;; Else, regular comment instead of //+VL or //@VL comment, so
               ;; put the slashes back and don't try to preprocess it any more.
               (prefix (list* (first echars) (second echars) prefix))
               (ppst   (vl-ppst-maybe-write prefix)))
            (vl-preprocess-loop remainder n ppst state))))

       ((when (acl2::and** (eql char1 #\/)
                           (consp (cdr echars))
                           (eql (vl-echar->char (second echars)) #\*)))
        ;; Start of a block comment.
        ;;
        ;; SPECIAL VL EXTENSION.  We do the same thing for /*+VL...*/,
        ;; converting it into "..." here during preprocessing, and for
        ;; /*@VL...*/, converting it into (*...*) We don't do anything special
        ;; to support comments within the /*@VL ... */ form, since this is
        ;; mainly intended for inline things
        (b* (((mv successp prefix remainder)
              (vl-read-through-literal "*/" (cddr echars)))
             ((unless successp)
              (let ((ppst (vl-ppst-fatal
                           :msg "~a0: block comment is never closed."
                           :args (list (vl-echar->loc echar1)))))
                (mv nil echars ppst state)))

             ((when (vl-matches-string-p "+VL" prefix))
              ;; The /* part is already gone.  Strip off "+VL" and "*/", and put the
              ;; comment's body into the input stream, as for //+VL above.
              (b* ((body (butlast (rest-n 3 prefix) 2)))
                (vl-preprocess-loop (append body remainder)
                                    (- n 1)
                                    ppst state)))

             ((when (vl-matches-string-p "@VL" prefix))
              ;; The /* part is gone.  Strip off "@VL" and "*/"; add "(*" and "*)",
              ;; and put the body into the input stream, as for //@VL above.
              (b* ((body (append (vl-echarlist-from-str "(*")
                                 (butlast (rest-n 3 prefix) 2)
                                 (vl-echarlist-from-str "*)"))))
                (vl-preprocess-loop (append body remainder)
                                    (- n 1)
                                    ppst state)))

             ;; Else, not a +VL or @VL comment, so put the /* back, and put
             ;; the prefix into the acc becuase we're done preprocessing this
             ;; comment.
             (prefix (list* (first echars) (second echars) prefix))
             (ppst (vl-ppst-maybe-write prefix)))
          (vl-preprocess-loop remainder n ppst state)))


       ((unless (eql char1 #\`))
        ;; Any regular character.  Accumulate or discard, per activep.
        (b* ((ppst (vl-ppst-maybe-write1 (car echars))))
          (vl-preprocess-loop (cdr echars) n ppst state)))

       ;; Otherwise we just found a legitimate grave character which isn't
       ;; inside a string literal or comment or anything.  We need to handle
       ;; some compiler directive.

       ((mv & remainder) (vl-read-while-whitespace (cdr echars)))
       ((mv directive prefix remainder) (vl-read-identifier remainder))
       ((unless directive)
        (let ((ppst (vl-ppst-fatal
                     :msg "~a0: stray ` character."
                     :args (list (vl-echar->loc echar1)))))
          (mv nil echars ppst state)))

       ((unless (vl-is-compiler-directive-p directive))
        ;; A macro usage like `foo.  The defines table stores the macro text in
        ;; order, so we can essentially revappend it into the accumulator.
        (b* ((activep (vl-ppst->activep))
             (ppst
              ;; Record that we have seen a use of this macro.  We do this
              ;; regardless of whether we are in an ifdef-ed out part of the
              ;; file.  But we record whether the macro would actually be
              ;; expanded or not as part of the context we save.
              (vl-ppst-record-def-use directive
                                      (make-vl-def-context :activep activep
                                                           :loc (vl-echar->loc echar1))))
             ((unless (vl-ppst->activep))
              ;; Subtle.  Never try to expand macros in inactive sections,
              ;; because it is legitimate for them to be undefined.
              (vl-preprocess-loop remainder n ppst state))
             ((mv successp expansion ppst)
              (vl-expand-define directive remainder (vl-echar->loc echar1) ppst))
             ((unless successp)
              ;; Already printed an error message.
              (mv nil expansion ppst state)))
          (vl-preprocess-loop expansion (- n 1) ppst state)))

       ((when (eql (vl-echar->char (car prefix)) #\\))
        ;; We explicitly disallow `\define, `\ifdef, etc.
        (let ((ppst (vl-ppst-fatal
                     :msg "~a0: we do not allow the use of \\~s1."
                     :args (list (vl-echar->loc echar1) directive))))
          (mv nil echars ppst state)))

       ((when (acl2::or** (equal directive "define")
                          (equal directive "centaur_define")))
        ;; CENTAUR EXTENSION: we also support centaur_define
        (b* (((mv successp remainder ppst)
              (vl-process-define (vl-echar->loc echar1) remainder ppst))
             ((unless successp)
              (mv nil echars ppst state)))
          (vl-preprocess-loop remainder n ppst state)))

       ((when (equal directive "undef"))
        (b* (((mv successp remainder ppst)
              (vl-process-undef (vl-echar->loc echar1) remainder ppst))
             ((unless successp)
              (mv nil echars ppst state)))
          (vl-preprocess-loop remainder n ppst state)))

       ((when (acl2::or** (equal directive "ifdef")
                          (equal directive "ifndef")
                          (equal directive "elsif")))
        (b* (((mv successp remainder ppst)
              (vl-process-ifdef (vl-echar->loc echar1) directive remainder ppst))
             ((unless successp)
              (mv nil echars ppst state)))
          (vl-preprocess-loop remainder n ppst state)))

       ((when (equal directive "else"))
        (b* (((mv successp ppst)
              (vl-process-else (vl-echar->loc echar1) ppst))
             ((unless successp)
              (mv nil echars ppst state)))
          (vl-preprocess-loop remainder n ppst state)))

       ((when (equal directive "endif"))
        (b* (((mv successp ppst)
              (vl-process-endif (vl-echar->loc echar1) remainder ppst))
             ((unless successp)
              (mv nil echars ppst state)))
          (vl-preprocess-loop remainder n ppst state)))

       ((when (equal directive "include"))
        (b* (((unless (vl-ppst->activep))
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
              (vl-preprocess-loop remainder n ppst state))

             ;; Else, we're in an active section, so (roughly): read the
             ;; filename try to carry out the inclusion.
             ;;
             ;; But this is very subtle.  Ostensibly, per SystemVerilog-2012,
             ;; the syntax is just
             ;;
             ;;     `include "filename"`
             ;;  or `include <filename>`
             ;;
             ;; Except that the syntax permits only whitespace or "a comment"
             ;; to occur on the same line as the include directive.  But this
             ;; description doesn't at all describe how includes are supposed
             ;; to interact with the rest of preprocessing.  For instance:
             ;; should the following be legal?
             ;;
             ;;    `include `ifdef foo "foo.v" `else "bar.v" `endif
             ;;
             ;; NCVerilog allows it but VCS does not.  As another example:
             ;; should the following be legal?
             ;;
             ;;    `define mymacro(filename) `"/some/path/to/filename.sv`"
             ;;    `include `mymacro(foo)
             ;;
             ;; Both NCVerilog and VCS permit this.  To support this sort of
             ;; thing, we will try to:
             ;;
             ;;   (1) read until the end of the line
             ;;   (2) preprocess whatever we find
             ;;   (3) read the post-preprocessing output to try to discover
             ;;       a string literal which should be the file to include.
             ;;
             ;; This could possibly be wrong if the line with the include
             ;; contains junk afterwards, e.g., consider
             ;;
             ;;    `include "foo.sv" `foo
             ;;
             ;; If `foo is defined within "foo.sv", then it isn't correct to
             ;; try to preprocess it in the current context before we've loaded
             ;; in foo.sv.
             ;;
             ;; We think this is sufficiently unlikely that we are not going to
             ;; try to defend against it, for now.  If we need to add some
             ;; defense against this, it could probably be added to
             ;; vl-read-include itself.

             ;; 1. Read the rest of the `include `mymacro(foo) line
             ((mv & include-line rest-of-file) (vl-read-until-literal *nls* remainder))

             ;; 2. Preprocess the include-line itself.  This is complicated
             ;; because we're juggling the stobj around, but basically: save
             ;; the current state, preprocess the include-line in a new state
             ;; that has a fresh accumulator, extract the resulting expansion,
             ;; then restore the state we saved and go on with life.
             (saved (vl-save-ppst))
             (ppst (vl-ppst-update-acc nil)) ;; Empty accumulator to begin with
             ((mv okp ?include-line-remainder ppst state)
              (vl-preprocess-loop include-line (- n 1) ;; makes termination easy
                                  ppst state))
             ((vl-saved-ppst post) (vl-save-ppst))
             (ppst (vl-restore-ppst saved))
             ;; BOZO think harder about whether we actually want to do this.
             ;; This is what we did before introducing PPST, but it may not
             ;; have been entirely sensible...
             (ppst (vl-ppst-update-defines post.defines))
             (ppst (vl-ppst-update-filemap post.filemap))
             (ppst (vl-ppst-update-iskips post.iskips))
             ((unless okp)
              (let ((ppst (vl-ppst-fatal
                           :msg "~a0: failed to preprocess rest of `include line: ~s1."
                           :args (list (vl-echar->loc echar1)
                                       include-line))))
                (mv nil echars ppst state)))

             ;; 3. Now try to read the filename to be included out of the
             ;; post-preprocessed include line.
             ((vl-loadconfig config) (vl-ppst->config))
             ((mv filename & rest-of-line ppst) (vl-read-include (rev post.acc) ppst))
             ((unless filename)
              ;; Already warned.
              (mv nil echars ppst state))

             ;; Hooray -- at this point we actually know what file name we
             ;; are supposed to try to include.  It might live in any number
             ;; of include directories, so go off and search for it.
             ((mv realfile state)
              (time$ (vl-find-file filename (vl-ppst->idcache) state)
                     :msg "~s0: (find ~s1: ~st sec, ~sa bytes)~%"
                     :args (list (vl-ppst-pad) filename)
                     :mintime config.mintime))
             ((unless realfile)
              (let ((ppst (vl-ppst-fatal
                           :msg "~a0: unable to find ~s1.  The include ~
                                 directories are ~&2."
                           :args (list (vl-echar->loc echar1)
                                       filename
                                       config.include-dirs))))
                (mv nil echars ppst state)))

             ;; We now have the real filename to load.  Maybe we've already
             ;; loaded it before and don't need to load it again?
             (controller (vl-includeskips-controller-lookup realfile (vl-ppst->iskips)))
             ((when (acl2::and** controller
                                 (consp (vl-find-define controller (vl-ppst->defines)))))
              ;; Multiple include optimization HIT: we can skip this include
              ;; and just go on reading the rest of the file.
              (b* ((iskips (vl-includeskips-record-hit realfile
                                                       (vl-echar->loc echar1)
                                                       (vl-ppst->iskips)))
                   (ppst (vl-ppst-update-iskips iskips)))
                (cw-unformatted (cat (vl-ppst-pad) " (skip " realfile ")" *nls*))
                (vl-preprocess-loop rest-of-file (- n 1) ppst state)))

             (ppst (vl-maybe-ppst-warn
                    :when controller
                    :type :vl-warn-include-guard
                    :msg "~a0: multiple include optimization failure: the ~
                              controlling define ~s1 is not currently ~
                              defined, so we will have to re-include ~s2."
                    :args (list (vl-echar->loc echar1) controller
                                realfile)))

             (current-includes (vl-ppst->includes))
             (ppst (vl-ppst-update-includes (cons realfile current-includes)))
             (pad (vl-ppst-pad))
             (- (cw-unformatted (cat pad realfile *nls*)))

             ;; We need to read the file and preprocess it.
             ((mv okp contents len state)
              (time$ (vl-read-file (string-fix realfile))
                     :msg "~s0 (read: ~st sec, ~sa bytes)~%"
                     :args (list pad)
                     :mintime config.mintime))
             ((unless okp)
              (let ((ppst (vl-ppst-fatal
                           :msg "~a0: unable to read ~s1."
                           :args (list (vl-echar->loc echar1)
                                       realfile))))
                (mv nil echars ppst state)))

             (ppst (vl-ppst-update-bytes (+ (vl-ppst->bytes) len)))
             (ppst (vl-maybe-update-filemap realfile contents ppst))
             (ppst (b* ((iskips (vl-includeskips-record-miss realfile
                                                             (vl-echar->loc echar1)
                                                             len
                                                             (vl-ppst->iskips))))
                     (vl-ppst-update-iskips iskips)))

             ;; Check for a proper include-guard and handle that accordingly.
             ((mv contents ppst)
              (vl-multiple-include-begin realfile contents ppst))

             ;; Preprocess the contents of the file we just included.
             ((mv okp remainder ppst state)
              (vl-preprocess-loop contents (- n 1) ppst state))
             ((unless okp)
              (mv okp remainder ppst state))

             ;; All done preprocessing that include, so pop it.
             (ppst (vl-ppst-update-includes current-includes))

             (ppst
              ;; Add the rest of the line (whatever comes after the name of the
              ;; file to be included, but before the rest of the current file,
              ;; e.g., if the include line is `include "myfile.v" `endif, this
              ;; will be the `endif part.  Per the comments in vl-read-include
              ;; this isn't allowed by the spec, but the user might write it
              ;; and other Verilog tools support it.
              (vl-ppst-update-acc (revappend rest-of-line (vl-ppst->acc)))))

          ;; All done with the `include, so preprocess the remaining contents
          ;; of the file that did the including.
          (vl-preprocess-loop rest-of-file (- n 1) ppst state)))

       ((when (equal directive "timescale"))
        ;; [Jared] historically, our preprocessor recognized constructs such as
        ;; `timescale 1ns/1ps and just threw them away.  But I later found that
        ;; designers were using constructs such as `timescale `foo, which meant
        ;; that I needed to somehow expand the `foo before trying to process
        ;; the timescale part.  After considering how to handle this, I think
        ;; the nicest approach is to move the job of ignoring `timescale from
        ;; the preprocessor to the lexer.  The preprocessor can just leave the
        ;; `timescale directives in, and the lexer can remove them after any
        ;; other `define stuff within them has been expanded.
        (b* ((ppst (vl-ppst-maybe-write (cons echar1 prefix))))
          (vl-preprocess-loop remainder n ppst state)))

       ((when (equal directive "__FILE__"))
        (b* (((unless (vl-ppst->activep))
              (vl-preprocess-loop remainder n ppst state))
             ((vl-location loc) (vl-echar->loc echar1))
             (quoted-escaped-filename-str
              (vl-filename-to-string-literal loc.filename))
             (quoted-escaped-filename-echars
              (vl-change-echarlist-locations
               (vl-echarlist-from-str quoted-escaped-filename-str)
               loc))
             (ppst (vl-ppst-write quoted-escaped-filename-echars)))
          (vl-preprocess-loop remainder n ppst state)))

       ((when (equal directive "__LINE__"))
        (b* (((unless (vl-ppst->activep))
              (vl-preprocess-loop remainder n ppst state))
             ((vl-location loc) (vl-echar->loc echar1))
             (line-str (natstr loc.line))
             (line-echars (vl-change-echarlist-locations
                           (vl-echarlist-from-str line-str)
                           loc))
             (ppst (vl-ppst-write line-echars)))
          (vl-preprocess-loop remainder n ppst state)))

       ((when (acl2::or** (equal directive "celldefine")
                          (equal directive "endcelldefine")
                          (equal directive "resetall")
                          (equal directive "protect")
                          (equal directive "endprotect")))
        ;; BOZO maybe add a note that we are ignoring these directives?
        (vl-preprocess-loop remainder n ppst state))

       ((when (and (equal directive "default_nettype")
                   (not (vl-ppst->activep))))
        (b* (((mv & ?prefix remainder) (vl-read-until-literal *nls*
                                                              remainder)))
          (vl-preprocess-loop remainder n ppst state)))
             
       
       (ppst (vl-ppst-fatal
              :msg "~a0: we do not support `~s1."
              :args (list (vl-echar->loc echar1)
                          directive))))
    (mv nil echars ppst state))
  ///
  (never-memoize vl-preprocess-loop)

  (local (defthm consp-of-vl-read-identifier-under-iff
           (iff (consp (mv-nth 1 (vl-read-identifier echars)))
                (mv-nth 0 (vl-read-identifier echars)))))

  ;; (local (set-default-hints
  ;;         ;; I think we might be hitting ACL2's heuristics on not opening up
  ;;         ;; functions when it would introduce too many ifs, so we need this to
  ;;         ;; tell it to really go ahead and open up the function.
  ;;         '('(:expand ((:free (activep) (vl-preprocess-loop echars n ppst state)))))))

  (local (in-theory (disable (:d vl-preprocess-loop))))

  (defthm state-p1-of-vl-preprocess-loop
    (implies (force (state-p1 state))
             (b* (((mv ?successp ?echars ?ppst state)
                   (vl-preprocess-loop echars n ppst state)))
               (state-p1 state)))
    :hints((acl2::just-induct-and-expand (vl-preprocess-loop echars n ppst state))))

  (verify-guards vl-preprocess-loop
    :hints(("Goal"
            :do-not '(generalize fertilize)))))

) ; with-output


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

(define vl-ppst-unsound-nreverse-acc (ppst)
  ;; Should only be used by vl-preprocess.  In principle we shouldn't use
  ;; nreverse here because we haven't ensured that the acc is a true-listp.  In
  ;; practice it will be fine.
  :returns ppst
  (progn$ (raise "Under the hood definition not installed?")
          (b* ((acc (vl-ppst->acc)))
            (vl-ppst-update-acc (rev acc)))))

(defttag :vl-optimize)
(progn!
; Start Matt K. mod: push the about-to-be-smashed function onto the appropriate
; list, so that (comp t) doesn't undo the smashing.
 :state-global-bindings
 ((acl2::temp-touchable-vars t acl2::set-temp-touchable-vars))
 (f-put-global 'acl2::logic-fns-with-raw-code
               (cons 'vl-ppst-unsound-nreverse-acc
                     (@ acl2::logic-fns-with-raw-code))
               state)
; End Matt K. mod.
 (set-raw-mode t)
 (defun vl-ppst-unsound-nreverse-acc (ppst)
   (let ((acc (vl-ppst->acc)))
     (vl-ppst-update-acc (nreverse acc)))
   ppst))
(defttag nil)

;; Just a sanity check to make sure it's working...
(local (define test-nreverse ((str stringp))
         (b* (((local-stobjs ppst)
               (mv ans ppst))
              (echars (vl-echarlist-from-str str))
              (ppst (vl-ppst-update-acc echars))
              (ppst (vl-ppst-unsound-nreverse-acc ppst))
              (ans  (vl-echarlist->string (vl-ppst->acc))))
           (mv ans ppst))))

(local (assert! (equal (test-nreverse "foo") "oof")))

(define vl-preprocess
  :short "Top-level interface to the preprocessor."
  ((echars "Characters to preprocess, in order."
           vl-echarlist-p)
   &key
   (defines  "Initial definitions to use." vl-defines-p)
   (filemap  "Initial file map to extend (for `includes)." vl-filemap-p)
   (config   "Controls the Verilog edition, include paths, etc." vl-loadconfig-p)
   (iskips   "Multi-include optimization." vl-includeskips-p)
   (bytes    "Bytes read so far." natp)
   (idcache  "Include-directory cache." vl-dirlist-cache-p)
   (ifdefmap "Ifdef use map to extend." vl-ifdef-use-map-p)
   (defmap   "Define use map to extend." vl-def-use-map-p)
   (warnings "Warnings accumulator to extend." vl-warninglist-p)
   ((state   "ACL2's @(see state), for file i/o.") 'state))
  :returns
  (mv (successp   booleanp :rule-classes :type-prescription
                  "Was preprocessing successful?")
      (defines    vl-defines-p "Updated defines after preprocessing the files.")
      (filemap    vl-filemap-p "Possibly extended filemap.")
      (iskips     vl-includeskips-p "Possibly updated iskips.")
      (ifdefmap   vl-ifdef-use-map-p "Possibly extended ifdef use map.")
      (defmap     vl-def-use-map-p "Possibly extended define use map.")
      (bytes      natp :rule-classes :type-prescription "Updated total bytes.")
      (warnings   vl-warninglist-p "Possibly updated warnings.")
      (new-echars vl-echarlist-p "Updated extended characters, after preprocessing.")
      (state      state-p1 :hyp (force (state-p1 state))))

  (b* (((local-stobjs ppst)
        (mv successp defines filemap iskips ifdefmap defmap bytes warnings new-echars ppst state))
       ;; istack defaults to nil
       ;; acc defaults to nil
       (ppst (vl-ppst-update-defines defines))
       (ppst (vl-ppst-update-filemap filemap))
       (ppst (vl-ppst-update-config config))
       (ppst (vl-ppst-update-activep t))
       (ppst (vl-ppst-update-iskips iskips))
       (ppst (vl-ppst-update-warnings warnings))
       (ppst (vl-ppst-update-idcache idcache))
       (ppst (vl-ppst-update-ifdefmap ifdefmap))
       (ppst (vl-ppst-update-defmap defmap))
       ;; just a quick sanity check
       (- (or (equal (vl-loadconfig->include-dirs config)
                     (alist-keys (vl-ppst->idcache)))
              (raise "idcache is screwed up: ~x0 versus ~x1"
                     (vl-loadconfig->include-dirs config)
                     (alist-keys (vl-ppst->idcache)))))
       (ppst (vl-ppst-update-bytes bytes))
       ((mv successp remainder ppst state)
        (vl-preprocess-loop echars *vl-preprocess-clock* ppst state))
       (defines  (vl-ppst->defines))
       (filemap  (vl-ppst->filemap))
       (iskips   (vl-ppst->iskips))
       ;; Don't clean/free the ifdefmap/defmap here, loader will do it.
       (ifdefmap (vl-ppst->ifdefmap))
       (defmap   (vl-ppst->defmap))
       (bytes    (vl-ppst->bytes))
       (warnings (vl-ppst->warnings))
       ((when successp)
        ;; Using nreverse here saves a copy of a potentially hugely long list.
        (let ((ppst (vl-ppst-unsound-nreverse-acc ppst)))
          (mv successp defines filemap iskips ifdefmap defmap bytes warnings (vl-ppst->acc) ppst state))))
    (mv (cw "[[ Previous  ]]: ~s0~%~
             [[ Remaining ]]: ~s1~%"
            (vl-echarlist->string (vl-safe-previous-n 50 (vl-ppst->acc)))
            (vl-echarlist->string (vl-safe-next-n 50 remainder)))
        defines filemap iskips ifdefmap defmap bytes warnings nil ppst state)))



