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
(include-book "lexer")
(include-book "defines")
(local (include-book "../util/arithmetic"))


(defxdoc preprocessor
  :parents (loader)
  :short "Limited preprocessor for Verilog."

  :long "<p>First, a warning.  In general, the Verilog specification does not
cover how preprocessing is to be done in a very complete way.  We are left with
many subtle questions about how the preprocessor should behave, and to resolve
these questions we have sometimes just given test cases to Cadence.  This is
not a very satisfying state of affairs.</p>

<p>We implement a limited preprocessor for Verilog.  We mainly provide support
for the directives:</p>

<ul>
<li>define</li>
<li>ifdef</li>
<li>ifndef</li>
<li>elsif</li>
<li>else</li>
<li>undef</li>
</ul>

<p>We also \"support\" <tt>timescale</tt> by throwing it away.  This oddity is
just intended to support our work at Centaur.  It's probably not the right
thing to do, but our synthesis to E ignores times and delays anyway.</p>

<p>Even the directives we do support are subject to limitations.  For instance,
we do not accept definitions with arguments, e.g., <tt>`max(a,b)</tt>, and we
do not allow definitions to include most compiler directives, e.g., the body of
<tt>`foo</tt> may not include <tt>`endif</tt>, but may include <tt>`bar</tt>.
These restrictions are intended to ensure that we do not \"mispreprocess\"
anything.</p>

<h3>Implementation Notes and Considerations</h3>


<p>There are many subtleties that make my head hurt.</p>

<h5>Define is Lazy</h5>

<p>An important thing to realize is that the text which follows \"<tt>`define
foo</tt>\" is not preprocessed once when it is read.  Instead, it is separately
preprocessed each time `foo is encountered.  Hence, upon running</p>

<code>
`define foo 3
`define bar `foo
`undef foo
`define foo 4
</code>

<p>the value of `bar will be 4.</p>



<h5>We Prohibit Certain Directives In Defines</h5>

<p>In Cadence, <tt>`define</tt> can interact with the <tt>`ifdef</tt> tree in
subtle ways.  For instance, Cadence accepts the following input:</p>

<code>
`define condition 1
`define myendif `endif
`ifdef condition
   assign w1 = 1 ;
`myendif
</code>

<p>Yet when <tt>`foo</tt> is used inside of an ifdef'd-away section, it is not
 expanded.  And so, the above example becomes a parse error if you merely remove
 the <tt>`define condition 1</tt> line.</p>

<p>Another subtlety.  As expected, defines found within ifdefed-away parts of
 the code have no effect.  For example, if not_defined is not defined, then
 upon running</p>

<code>
`define foo 3
`ifdef not_defined
   `define foo 4
`endif
</code>

<p>the value of <tt>`foo</tt> will correctly be 3.  Similarly, writing
<tt>`undef foo</tt> in the not_defined block does not actually undefine foo.
But the preprocessor is not mindlessly skipping text until an `else or `elseif
is encountered.  For example, the following is well-formed and does not
result in a too-many-endifs warning.</p>

<code>
`ifdef not_defined
   `define myendif `endif
`endif
</code>

<p>This is insane, so we prohibit things like <tt>`define myendif `endif</tt>
by disallowing the use of built-in directives in macro text.  Note that we
still permit the use of <tt>`define foo `bar</tt>, with the same lazy semantics
that Cadence uses.</p>


<h5>We Prohibit Defining or Testing Built-in Directive Names</h5>

<p>We do not allow compiler directive names to be <tt>`define</tt>d, or to be
used within <tt>ifdef</tt>, <tt>ifndef</tt>, or <tt>elsif</tt> directives.
Why is this?</p>

<p>Note that macro names can be simple or escaped identifiers.  In Section
3.7.1, we are told that the leading backslash character and trailing whitespace
are not considered part of an escaped identifier, and that the escaped
identifier <tt>\\cpu3</tt> is to be treated the same as <tt>cpu3</tt>.  Indeed,
in Cadence we find that the following works as expected:</p>

<code>
`define foo 3
`define \\bar 4

assign w1 = `foo ;
assign w2 = `\\foo ;
assign w3 = `bar ;
assign w4 = '\\bar ;
</code>

<p>In Section 19.3.1, we are told that all compiler directives shall be
considered predefined macro names, and it shall be illegal to redefine a
compiler directive as a macro name.  And Cadence seems to rightfully complain
about things like:</p>

<code>
`define define 5
`define ifdef 6
</code>

<p>And yet, Cadence permits the following:</p>

<code>
`define \\define 5
`define \\ifdef 6

assign w1 = `\\define ;
assign w2 = `\\ifdef ;
</code>

<p>While the following will be errors:</p>

<code>
assign w3 = `define ;
assign w4 = `ifdef ;
</code>

<p>Should <tt>\\define</tt> be treated differently from <tt>define</tt>?
Maybe.  After all, the point of escaped identifiers is probably to not clash
with regular keywords.  But on the other hand, if the predefined names are to
be considered predefined, then shouldn't things like this</p>

<code>
`ifdef define
</code>

<p>always evaluate to true?  But in Cadence this is false unless you have done
a <tt>`define \\define</tt> like above.  Cadence also does not complain about
<tt>`undef</tt> define, which seems strange.</p>

<p>At any rate, to entirely avoid the question of what the right behavior is
here, we simply prohibit the use of compiler directives, whether escaped or
not, as names anywhere in <tt>defines</tt>, <tt>undefs</tt>, <tt>ifdefs</tt>,
<tt>ifndefs</tt>, and <tt>elsifs</tt>.  In practice this only prevents people
from writing things like <tt>`define define</tt> and <tt>`ifdef undef</tt>,
anyway, so this should not be too controversial.</p>


<h5>We make certain restrictions to disambiguate line continuations and
comments.</h5>

<p>From 19.3.1, the macro text for a define is:</p>

<ul>
 <li>any arbitrary text specified on the same line as the macro name,</li>

 <li>except that the sequence <tt>\\&lt;newline&gt;</tt> may be used to extend
     the macro text across multiple lines,</li>

 <li>and single-line comments are not to become part of the substituted
     text.</li>
</ul>

<p>On the surface, this is straightforward enough.  But it is difficult to know
exactly how comments and these line continuations are supposed to interact.
And Cadence, in particular, has some very strange and seemingly inconsistent
rules:</p>

<code>
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
</code>

<p>To prevent any amiguity, we prohibit any combination of comments and
continuations that seems difficult to understand.  In particular, we impose the
following \"cowardly\" restrictions on macro text:</p>

<ol>
<li>Single-line comments are not allowed to end with <tt>\\</tt></li>
<li>Block comments are not allowed to contain newlines</li>
<li>The sequences <tt>\\//</tt> and <tt>\\/*</tt> are not allowed
except within comments, string literals, and escaped identifiers</li>
</ol>

<p>These constriants make reading until the end of the macro text fairly
complicated since we cannot stupidly read the text without interpreting it;
rather we have to look for string literals, comments, escaped identifiers, etc.
The goal is for everything we support will be interpreted in the same way by
Cadence and other tools.</p>")


(defconst *vl-list-of-compiler-directives*

; This is taken directly from Section 19.  We do not actually support most of
; these, but we need to recognize them so we can complain when we run into ones
; we don't support, etc.

  (list "begin_keywords"
        "celldefine"
        "default_nettype"

; CENTAUR EXTENSION.  We also add centaur_define, which we treat exactly as
; define.

        "centaur_define"

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
        "undef"))

(defund vl-is-compiler-directive-p (x)
  (declare (xargs :guard (stringp x)))
  (if (member-equal x *vl-list-of-compiler-directives*)
      t
    nil))



(defaggregate vl-iframe
  (initially-activep
   some-thing-satisfiedp
   already-saw-elsep)
  :tag :vl-iframe
  :require ((booleanp-of-vl-iframe->initially-activep (booleanp initially-activep))
            (booleanp-of-vl-iframe->some-thing-satisfiedp (booleanp some-thing-satisfiedp))
            (booleanp-of-vl-iframe->already-saw-elsep (booleanp already-saw-elsep)))
  :parents (preprocessor)
  :short "<tt>`ifdef</tt> stack frame objects."

  :long "<p>Iframes (\"ifdef frames\") are essential in our approach to
handling <tt>`ifdef</tt> directives.  Our main preprocessing function, @(see
vl-preprocess-loop), takes three arguments that have to do with handling
ifdefs:</p>

<ul>

<li><tt>defines</tt> is the current @(see vl-defines-p) alist.  For now, just
assume that we are able to appropriately keep this list updated as we encounter
defines and undefs.</li>

<li><tt>activep</tt> is a boolean which is true whenever the characters are are
now reading from the file ought to be given to the lexer -- the idea is that
when we encounter an <tt>`ifdef</tt> whose condition isn't satisfied, we turn
off <tt>activep</tt> until the closing <tt>`endif</tt> is encountered.</li>

<li><tt>istack</tt> is a stack of <tt>vl-iframe-p</tt> objects which explain
how to manage <tt>activep</tt> as we descend through a nest of <tt>`ifdef</tt>,
<tt>`ifndef</tt>, <tt>`elsif</tt>, <tt>`else</tt>, and <tt>`endif</tt>
directives.</li>

</ul>

<p>Let us temporarily ignore nested directives.  Then, our task would be to
decide when activep should be turned on during sequences like this:</p>

<code>
    `if[n]def THING
      stuff1
    `elsif THING2
      stuff2
    `elsif THING3
      stuff3
    `else
      stuff4
    `endif
</code>

<p>The semantics of this (Section 19.4) are essentially: figure out the first
<i>THING</i> that is satisfied, include its stuff, and ignore the rest.  So for
instance, if <i>THING2</i> and <i>THING3</i> are both satisfied, we still only
want to include <i>stuff2</i> since it comes first.</p>

<p>To implement this, the basic idea is that when we encounter an
<tt>`ifdef</tt> or <tt>`ifndef</tt> directive, we construct an iframe that
helps us set <tt>activep</tt> correctly.  The first two fields of the iframe
are:</p>

<dl>

<dt><tt>some-thing-satisfiedp</tt></dt>
<dd>which indicates if any of the <i>THING</i>s we have seen so far
 was satisfied, and</dd>

<dt><tt>already-saw-elsep</tt></dt>
<dd>which indicates whether we have seen an <tt>`else</tt> and is
used only as a sanity check to prevent multiple <tt>`else</tt>
clauses.</dd>

</dl>

<p>And as we descend through the above sequences, we update the iframe and
ensure that <tt>activep</tt> is set exactly when the current <i>THING</i> is
satisfied and no previous <i>THING</i> was satisfied.</p>

<p>But the story is not quite complete yet, because we also have to handle
 nested ifdefs.  For example, imagine we have:</p>

<code>
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
</code>

<p>This is almost the same, except that now we only want to turn on
<tt>activep</tt> when <i>OUTER</i> is also satisfied.  To keep track of this,
we add another field to our iframe objects:</p>

<dl>
<dt><tt>initially-activep</tt></dt>
<dd>which indicates whether <tt>activep</tt> was set when we encountered
the <tt>`ifdef</tt> or <tt>ifndef</tt> for this iframe.</dd>
</dl>

<p>Now, <tt>activep</tt> should be enabled exactly when:</p>

<ul>

<li>(inner criteria): the current <i>THING</i> is satisfied and no previous
   <i>THING</i> was sastified, and</li>

<li>(outer-criteria): <tt>initially-activep</tt> was also set, i.e., this chunk
   of code is not being blocked by some <i>THING</i> in an outer <tt>ifdef</tt>
   tree.</li>

</ul>")

(deflist vl-istack-p (x)
  (vl-iframe-p x)
  :elementp-of-nil nil)




(defsection vl-process-ifdef
  :parents (preprocessor)

  :short "Handler for <tt>ifdef</tt>, <tt>ifndef</tt>, and <tt>elsif</tt>
directives."

  :long "<p><b>Signature:</b> @(call vl-process-ifdef) returns <tt>(mv successp
new-istack new-activep remainder)</tt></p>

<p><tt>loc</tt> is a location for error reporting.  <tt>directive</tt> is one
of the strings \"ifdef\", \"ifndef\", or \"elsif\".  We assume that we have
just read <tt>`&lt;directive&gt;</tt> and that <tt>echars</tt> are the
characters which come right afterwards.  We read a name from the
<tt>echars</tt>, look it up in the defines table, and make the appropriate
changes to the <tt>istack</tt> and <tt>activep</tt>.</p>"

  (defund vl-process-ifdef (loc directive echars defines istack activep)
    "Returns (MV SUCCESSP NEW-ISTACK NEW-ACTIVEP REMAINDER)"
    (declare (xargs :guard (and (vl-location-p loc)
                                (member-equal directive '("ifdef" "ifndef" "elsif"))
                                (vl-echarlist-p echars)
                                (true-listp echars)
                                (vl-defines-p defines)
                                (vl-istack-p istack)
                                (booleanp activep))
                    :guard-debug t))


    (b* (((mv & remainder)      (vl-read-while-whitespace echars))
         ((mv name & remainder) (vl-read-identifier remainder)))
        (cond ((not name)
               (mv (cw "Preprocessor error (~s0): found an `~s1 without an identifier.~%"
                       (vl-location-string loc) directive)
                   istack activep echars))

              ((vl-is-compiler-directive-p name)
               ;; Special prohibition of compiler directive names in ifdefs,
               ;; ifndefs, etc.  See "Supporting Defines" below for details.
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
               (mv (cw "Preprocessor error (~s0): found an `elsif, but no ifdef ~
                        or ifndef is open.~%"
                       (vl-location-string loc))
                   istack activep echars))

              ((vl-iframe->already-saw-elsep (car istack))
               (mv (cw "Preprocessor error (~s0): found an `elsif, but we have ~
                        already seen `else.~%"
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

  :short "Handler for <tt>else</tt> directives."

  :long "<p><b>Signature:</b> @(call vl-process-else) returns <tt>(mv successp
new-istack new-activep)</tt>.</p>

<p>See the discussion in @(see vl-iframe-p) for details.</p>"

  (defund vl-process-else (loc istack activep)
    "Returns (MV SUCCESSP NEW-ISTACK NEW-ACTIVEP)"
    (declare (xargs :guard (and (vl-location-p loc)
                                (vl-istack-p istack)
                                (booleanp activep))))
    (cond ((not (consp istack))
           (mv (cw "Preprocessor error (~s0): found an `else, but no ifdef/ifndef ~
                 is open.~%"
                   (vl-location-string loc))
               istack activep))

          ((vl-iframe->already-saw-elsep (car istack))
           (mv (cw "Preprocessor error (~s0): found an `else, but we have already ~
                 seen an `else.~%"
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

  :short "Handler for <tt>endif</tt> directives."

  :long "<p><b>Signature:</b> @(call vl-process-endif) returns <tt>(mv successp
new-istack new-activep)</tt>.</p>

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
  :short "Read from <tt>`define</tt> until the end of the line."

  :long "<p><b>Signature:</b> @(call vl-read-until-end-of-define) returns
<tt>(mv successp prefix remainder)</tt>.</p>

<p>This is really tricky!  See the discussion in @(see preprocessor) for an
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
                (mv (cw "Preprocessor error (~s0): we cowardly do not allow '\//' ~
                       in defines.~%"
                        (vl-location-string (vl-echar->loc (car echars))))
                    nil echars))
               ((vl-matches-string-p "/*" (cdr echars))
                (mv (cw "Preprocessor error (~s0): we cowardly do not allow '\/*' ~
                       in defines.~%"
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
                      (mv (cw "Preprocessor error (~s0): we cowardly do not allow ~
                             single-line comments inside defines to end with \.~%"
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
                      (mv (cw "Preprocessor error (~s0): block comment is never ~
                             closed.~%"
                              (vl-location-string (vl-echar->loc (car echars))))
                          nil echars))
                     ((member #\Newline (vl-echarlist->chars prefix))
                      (mv (cw "Preprocessor error (~s0): block comment inside a ~
                             define is not closed before end of line.~%"
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
  :short "Handler for <tt>define</tt> directives."

  :long "<p><b>Signature:</b> @(call vl-process-define) returns <tt>(mv
successp new-defines remainder)</tt>.</p>

<p>We assume that <tt>`define</tt> has just been read and <tt>echars</tt>
is the text which comes right after the <tt>`define</tt> directive.  We
read the name and text for this new macro definition, and update the
defines table appropriately if <tt>activep</tt> is set.</p>"

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
                     (not (equal (string-trim (vl-echarlist->string (cdr lookup)))
                                 (string-trim (vl-echarlist->string text)))))
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

  (defund vl-process-undef (loc echars defines activep)
    "Returns (MV SUCCESSP NEW-DEFINES REMAINDER)"
    (declare (xargs :guard (and (vl-location-p loc)
                                (vl-echarlist-p echars)
                                (vl-defines-p defines)
                                (booleanp activep))))

; We assume that an `undef has just been read and echars is the text which
; comes right after the `undef directive.  We try to read the name we are to
; undefine and then update the defines table appropriately.

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
                (cw "Preprocessor warning (~s0): found `undef ~s1, but ~
                     ~s1 is not defined.~%"
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
                                (true-listp echars))
                    :guard-debug t))

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


(defsection vl-preprocess-loop

  (defund vl-preprocess-loop (echars defines istack activep acc n)
    "Returns (MV SUCCESSP DEFINES-PRIME ACC REMAINDER)"
    (declare (xargs :guard (and (vl-echarlist-p echars)
                                (true-listp echars)
                                (vl-defines-p defines)
                                (vl-istack-p istack)
                                (booleanp activep)
                                (vl-echarlist-p acc)
                                (natp n))
                    :measure (two-nats-measure n (acl2-count echars))
                    :hints(("Goal" :in-theory (disable (force))))))

; This is the main loop for the preprocessor.  It accumulates the transformed
; characters that are to be given to the lexer into acc, in reverse order.

    (b* (((when (atom echars))
          (mv t defines acc echars))

         (echar1 (car echars))
         (char1  (vl-echar->char echar1))
         (loc    (vl-echar->loc echar1))

         ((when (mbe :logic (zp n)
                     :exec (= n 0)))
          (mv (cw "Preprocessor error (~s0): ran out of steps. ~
                 Macro expansion loop?")
              defines acc echars))

; Preliminaries.  We need to be sure to treat strings, escaped identifiers, and
; comments atomically.  For instance, we don't want to look at a string like
; "looks like an `endif to me" and think that we have just read an `endif.

         ((when (eql char1 #\"))
          ;; Start of a string literal
          (b* (((mv string prefix remainder) (vl-read-string echars)))
              (if (not string)
                  ;; it already printed a warning, so we don't use cw.
                  (mv nil defines acc echars)
                (vl-preprocess-loop remainder defines istack activep
                                    (if activep (revappend prefix acc) acc)
                                    n))))

         ((when (eql char1 #\\))
          ;; Start of an escaped identifier
          (b* (((mv name prefix remainder) (vl-read-escaped-identifier echars)))
              (if (not name)
                  (mv (cw "Preprocessor error (~s0): stray backslash?~%"
                          (vl-location-string (vl-echar->loc (car echars))))
                      defines acc echars)
                (vl-preprocess-loop remainder defines istack activep
                                    (if activep (revappend prefix acc) acc)
                                    n))))

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
                (vl-preprocess-loop remainder defines istack activep
                                    (if activep (revappend atts acc) acc)
                                    (- n 1)))

            ;; Else, not a //@VL comment
            (b* (((mv & prefix remainder) (vl-read-until-literal *nls* (cddr echars)))
                 (prefix (if (vl-matches-string-p "+VL" prefix)
                             ;; The // is already gone, strip off the "+VL" part
                             (nthcdr 3 prefix)
                           ;; Else, not a +VL or @VL comment, so put the slashes back.
                           (list* (first echars) (second echars) prefix))))
              (vl-preprocess-loop remainder defines istack activep
                                  (if activep (revappend prefix acc) acc)
                                  n))))

         ((when (and (eql char1 #\/)
                     (consp (cdr echars))
                     (eql (vl-echar->char (second echars)) #\*)))
          ;; Start of a block comment.

; SPECIAL VL EXTENSION.  We do the same thing for /*+VL...*/, converting it into
; "..." here during preprocessing, and for /*@VL...*/, converting it into (*...*)
; We don't do anything special to support comments within the /*@VL ... */ form,
; since this is mainly intended for inline things

          (b* (((mv successp prefix remainder) (vl-read-through-literal "*/" (cddr echars)))
               (prefix
                (cond ((vl-matches-string-p "+VL" prefix)
                       ;; The /* part is already gone.  Strip off "+VL" and "*/"
                       (butlast (nthcdr 3 prefix) 2))

                      ((vl-matches-string-p "@VL" prefix)
                       ;; The /* part is gone.  Strip off "@VL" and "*/"; add "(*" and "*)"
                       (append (vl-echarlist-from-str "(*")
                               (butlast (nthcdr 3 prefix) 2)
                               (vl-echarlist-from-str "*)")))

                      (t
                       ;; Else, not a +VL or @VL comment, so put the /* back.
                       (list* (first echars) (second echars) prefix)))))

              (if (not successp)
                  (mv (cw "Preprocessor error (~s0): block comment is never closed.~%"
                          (vl-location-string loc))
                      defines acc echars)
                (vl-preprocess-loop remainder defines istack activep
                                    (if activep (revappend prefix acc) acc)
                                    n))))

         ((when (not (eql char1 #\`)))
          ;; Any regular character.  Accumulate or discard, per activep.
          (vl-preprocess-loop (cdr echars) defines istack activep
                              (if activep (cons (car echars) acc) acc)
                              n))

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
              defines acc echars))

         ((when (not (vl-is-compiler-directive-p directive)))

; A macro usage like `foo.  The defines table stores the macro text in order,
; so we can essentially revappend it into the accumulator.

          (if (not activep)
              ;; Subtle.  Never try to expand macros in inactive sections,
              ;; because it is legitimate for them to be undefined.
              (vl-preprocess-loop remainder defines istack activep acc n)

            (let ((lookup (vl-lookup-in-defines directive defines)))
              (if (not lookup)
                  (mv (cw "Preprocessor error (~s0): `~s1 is not defined.~%"
                          (vl-location-string loc) directive)
                      defines acc echars)
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
                                      defines istack activep acc
                                      (- (mbe :logic (nfix n) :exec n) 1)))))))

         ((when (eql (vl-echar->char (car prefix)) #\\))
          ;; We explicitly disallow `\define, `\ifdef, etc.
          (mv (cw "Preprocessor error (~s0): we do not allow the use of \~s1.~%"
                  (vl-location-string loc) directive)
              defines acc echars))

         ((when (or (equal directive "define")
                    (equal directive "centaur_define")))
          ;; CENTAUR EXTENSION: we also support centaur_define
          (b* (((mv successp new-defines remainder)
                (vl-process-define loc remainder defines activep)))
              (if (not successp)
                  (mv nil defines acc echars)
                (vl-preprocess-loop remainder new-defines istack activep acc n))))

         ((when (equal directive "undef"))
          (b* (((mv successp new-defines remainder)
                (vl-process-undef loc remainder defines activep)))
              (if (not successp)
                  (mv nil defines acc echars)
                (vl-preprocess-loop remainder new-defines istack activep acc n))))

         ((when (or (equal directive "ifdef")
                    (equal directive "ifndef")
                    (equal directive "elsif")))
          (b* (((mv successp new-istack new-activep remainder)
                (vl-process-ifdef loc directive remainder defines istack activep)))
              (if (not successp)
                  (mv nil defines acc echars)
                (vl-preprocess-loop remainder defines new-istack new-activep acc n))))

         ((when (equal directive "else"))
          (b* (((mv successp new-istack new-activep)
                (vl-process-else loc istack activep)))
              (if (not successp)
                  (mv nil defines acc echars)
                (vl-preprocess-loop remainder defines new-istack new-activep acc n))))

         ((when (equal directive "endif"))
          (b* (((mv successp new-istack new-activep)
                (vl-process-endif loc istack activep)))
              (if (not successp)
                  (mv nil defines acc echars)
                (vl-preprocess-loop remainder defines new-istack new-activep acc n))))

         ((when (equal directive "timescale"))
          (b* (((mv prefix remainder) (vl-read-timescale remainder)))
              (if (not prefix)
                  (mv nil defines acc echars)
                (vl-preprocess-loop remainder defines istack activep acc n)))))

        (mv (cw "Preprocessor error (~s0): we do not support ~s1.~%"
                (vl-location-string loc) directive)
            defines acc echars)))

  (local (in-theory (enable vl-preprocess-loop)))

  (defthm booleanp-of-vl-preprocess-loop-success
    (booleanp (mv-nth 0 (vl-preprocess-loop echars defines istack activep acc n)))
    :rule-classes :type-prescription)

  (defthm vl-defines-p-of-vl-preprocess-loop-defines
    (implies (and (force (vl-echarlist-p echars))
                  (force (true-listp echars))
                  (force (vl-defines-p defines))
                  (force (vl-istack-p istack))
                  (force (booleanp activep))
                  (force (vl-echarlist-p acc)))
             (vl-defines-p (mv-nth 1 (vl-preprocess-loop echars defines istack activep acc n)))))

  (defthm true-listp-of-vl-preprocess-loop-result
    (equal (true-listp (mv-nth 2 (vl-preprocess-loop echars defines istack activep acc n)))
           (true-listp acc)))

  (defthm vl-echarlist-p-of-vl-preprocess-loop-result
    (implies (and (force (vl-echarlist-p echars))
                  (force (true-listp echars))
                  (force (vl-defines-p defines))
                  (force (vl-istack-p istack))
                  (force (booleanp activep))
                  (force (vl-echarlist-p acc)))
             (vl-echarlist-p (mv-nth 2 (vl-preprocess-loop echars defines istack activep acc n)))))

  (defthm no-remainder-of-vl-preprocess-loop-on-success
    (implies (and (mv-nth 0 (vl-preprocess-loop echars defines istack activep acc n))
                  (force (true-listp echars)))
             (not (mv-nth 3 (vl-preprocess-loop echars defines istack activep acc n)))))

  (defthm vl-echarlist-p-of-vl-preprocess-loop-remainder
    (implies (and (force (vl-echarlist-p echars))
                  (force (true-listp echars))
                  (force (vl-defines-p defines))
                  (force (vl-istack-p istack))
                  (force (booleanp activep))
                  (force (vl-echarlist-p acc)))
             (vl-echarlist-p (mv-nth 3 (vl-preprocess-loop echars defines istack activep acc n)))))

  (defthm true-listp-of-vl-preprocess-loop-remainder
    (equal (true-listp (mv-nth 3 (vl-preprocess-loop echars defines istack activep acc n)))
           (true-listp echars))))




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

  (defund vl-preprocess (echars defines)
    "Returns (MV SUCCESSP NEW-ECHARS)"
    (declare (xargs :guard (and (vl-echarlist-p echars)
                                (true-listp echars)
                                (vl-defines-p defines))))
    ;; Note: keep in sync with optimized version, below.
    (mv-let (successp defines acc remainder)
            (vl-preprocess-loop echars defines nil t nil *vl-preprocess-clock*)
            (if successp
                (mv successp defines (reverse acc))
              (mv (cw "[[ Previous  ]]: ~s0~%~
                       [[ Remaining ]]: ~s1~%"
                      (vl-echarlist->string (vl-safe-previous-n 50 acc))
                      (vl-echarlist->string (vl-safe-next-n 50 remainder)))
                  defines
                  nil))))

  (local (in-theory (enable vl-preprocess)))

  (defthm booleanp-of-vl-preprocess-success
    (booleanp (mv-nth 0 (vl-preprocess echars defines)))
    :rule-classes :type-prescription)

  (defthm vl-defines-p-of-vl-preprocess-defines
  (implies (and (force (vl-echarlist-p echars))
                (force (true-listp echars))
                (force (vl-defines-p defines)))
           (vl-defines-p (mv-nth 1 (vl-preprocess echars defines)))))

  (defthm true-listp-of-vl-preprocess
    (true-listp (mv-nth 2 (vl-preprocess echars defines)))
    :rule-classes :type-prescription)

  (defthm vl-echarlist-p-of-vl-preprocess
    (implies (and (force (vl-echarlist-p echars))
                  (force (true-listp echars))
                  (force (vl-defines-p defines)))
             (vl-echarlist-p (mv-nth 2 (vl-preprocess echars defines))))))

(defttag vl-optimize)
(progn!
 ;; Nreverse optimization for success case.
 (set-raw-mode t)
 (setf (gethash 'vl-preprocess-loop ACL2::*never-profile-ht*) t)
 (defun vl-preprocess (echars defines)
   (mv-let (successp defines acc remainder)
           (vl-preprocess-loop echars defines nil t nil *vl-preprocess-clock*)
           (if successp
               (mv successp defines (nreverse acc))
             (mv (cw "[[ Previous  ]]: ~s0~%~
                      [[ Remaining ]]: ~s1~%"
                     (vl-echarlist->string (vl-safe-previous-n 50 acc))
                     (vl-echarlist->string (vl-safe-next-n 50 remainder)))
                 defines
                 nil)))))
(defttag nil)

