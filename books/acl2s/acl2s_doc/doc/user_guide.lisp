(defxdoc ACL2s User Guide
  :parents (acl2::acl2-sedan acl2::macro-libraries acl2s::defunc)
  :short "ACL2 Sedan User Guide"
  :long
  "
          <p>
            This guide showcases the important parts of the ACL2 Sedan
            user experience. We assume you already have a running
            ACL2s session; if not go
            to <a href="index.html#tutorial">Get Started</a>. The ACL2
            <a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____ACL2-TUTORIAL">tutorial</a>
            is a fine place to learn about the ACL2 language, logic
            and theorem proving system. For in-depth documentation
            about the ACL2 itself refer to the
            <a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/">
            manual</a>.
          </p>
        </div>

        <div class="left-center" data-target="cheat_sheet">
          <h2>Cheat Sheet</h2>
          A cheat sheet is available with a summary of key bindings and command types:
          <a href="http://acl2s.ccs.neu.edu/acl2s/doc/sheet.html">HTML</a> or <a href="sheet.pdf">PDF</a>.
        </div>

<div class="left-center" data-target="guide_customization">
<h2>Customization</h2>
<h4>Workspace Layout</h4>
<p>
Getting your workspace laid out in a convenient way is important to using
ACL2s efficiently.  Here are some pointers:
</p>
<ul>
<li><b>Editor split</b>:  At this time, source code and sessions are in
editors--different editors.  To see both at one time, you need to split up
your editor area.  (Each workbench window has one rectangular "editor area"
in which all the open editors are tabbed and/or tiled.)  Click the title
area of an editor you would like to split away from the others and drag it
to any side of the others.  As you drag, a gray outline of the proposed
layout is shown.  Observe that you can also drag titles back together, and
you can relocate views around the editor area analogously.
<li><b>Open, close, many, one</b>:  Through the "Window" menu, you can open
more than one workbench window, each of which has one rectangular editor area
and can have only one of any view open.  Also through the "Window" menu, you
can open another editor to the same file; all editors for the same file
keep their content in sync with each other.  Also through the "Window" menu,
you can reopen any views that may have accidentally been closed.
<li><b>Fast views</b>:  If you don't want to dedicate long-term real estate
to views such as the Project Explorer, Outline, Proof Tree, and Console, you can
minimize them to make them available quickly.  If you click the icon for
the minimized view--rather than the restore icon--it pops up as a "fast
view" which is minimized again after you click outside it.
</ul>
<h4>Preferences</h4>
<p>
Some ACL2s options are available for setup under <b>Window</b> |
<b>Preferences...</b> | <b>ACL2s</b>, but these are easy to find and
should be self-documenting.  Here I'll point out ACL2s settings burried
(necessarily) elsewhere and other Eclipse-wide settings that affect ACL2s:
</p>
<ul>
<li><b>Editor font</b>: Open the preferences dialog and go to
<b>General</b> | <b>Appearance</b> | <b>Colors and Fonts</b>.  Under "Basic,"
the "Text Font" is that used by the ACL2s editors.  Click "Change..." to
change it.
<li><b>Editor colors</b>: To make the editor text darker in general,
go in the preferences dialog to <b>General</b> | <b>Appearance</b>
and select the "Current theme" "High Contrast (ACL2s)".  This is good for
use on a projector, for example.  To manipulate the colors in detail,
go to <b>Colors and Fonts</b> and open the ACL2s group.  <i>Note:
You will have to close and re-open editors for these color changes to
take effect.</i>
</ul>
<h4>Session</h4>
<p>
If you want to add some configuration input to be loaded with each interactive
session, use an
<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____ACL2-CUSTOMIZATION">acl2-customization file</a>.
This can include your own configuration to be done after the session mode is
loaded and configured.  This should not include events, which should be
specified or explicitly loaded in the source code.  In fact, we do not load
the acl2-customization for certification.  Also note that ACL2s does not
respect the environment variable for acl2-customization.  Also note that
acl2-customization is only loaded in some modes (see below), unless
overridden in the preferences.
</p>
</div>

<div class="left-center" data-target="guide_modes">
<h2>Session Modes for ACL2 development</h2>
<p>
Lisp files developed in our tool are configured to be in one of several
modes, choosable from the menu <b>ACL2</b> | <b>Set ACL2 session
mode</b>.  Modes cannot be changed while ACL2 is running, so selection must
be made while no associated session is running.
</p><p>
The current mode is displayed in the <i>content description line</i> of the
lisp editor, just below the file name tab.  The mode is also displayed as
part of the startup output of a session, as below:
</p>
<pre><code>
========================================================================
Executing /home/peterd/acl2s.exe
Starting ACL2 in mode "Recursion and Induction"
</code></pre>

<h4>Introductory modes</h4>
<p>
These modes are intended for those learning ACL2.  They all modify ACL2
to print results in a way that is itself "evalable":
</p>

<pre><code>
ACL2 &gt;VALUE <i>(cons 'a (cons 'b nil))</i>
(LIST 'A 'B)
ACL2 &gt;VALUE <i>(cons 1 (cons 2 3))</i>
(CONS 1 (CONS 2 3))
ACL2 &gt; 
</code></pre>


<p>
Here are the introductory modes:
</p>

<table>
<thead>
  <tr>
    <th>Mode</th>
    <th>Description</th>
  </tr>
</thead>
<tbody>
<tr><td><b>Bare Bones</b><br><em>(introductory)</em></td><td>
<p>
Bare Bones is a mode that is used to teach
the semantics of ACL2 using a minimal subset of built-in functions.
The mode introduces ACL2 as a
programming language with contracts (a "typed" ACL2) to the
students, using a "minimal" subset of primitive functions.
For example, in the case of the Booleans, all that is built-in
are the constants t and nil and the functions if and equal.

Everything else is built on top of that.
</p><p>
</td></tr>
<tr><td><b>Programming</b><br><em>(introductory)</em></td><td>
<p>
This mode is designed around exploring ACL2 as a programming language of
untyped, total functions.  The only caveat is that definitions in
"Programming" mode are not checked for termination.  Consequently, logically
invalid, non-terminating definitions are possible, but this freedom should
be familiar to programmers.  "Programming" mode also removes some
restrictions and warnings about "silly" definitions, and any attempts at
proof fail.
</p><p>
<em>A note for experienced ACL2 users:</em>
Primarily, this mode uses 
<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____PROGRAM">program</a> mode and
<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____SET-GUARD-CHECKING">guard-checking :none</a>.
</p>
</td></tr>
<tr><td valign=top><b>Recursion &amp; Induction</b><br><em>(introductory)</em></td><td>
<p>
This mode is intended to be the next step for students comfortable with
ACL2 programming and writing proofs by hand.  The primary feature of this
mode is that it only performs induction with explicit hints.  Its
non-standard <code><b>theorem</b></code> event also disables any generated
rules by default (like
<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____DEFTHMD"><code>defthmd</code></a>).
Induction and theory extension are disabled *not* to discourage use, but to
force the user to give some guidance to ACL2, with
<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____HINTS">hints</a>.
Automatic generalization and irrelevance elimination are also disabled for
proofs in this mode--to encourage writing appropriate lemmas.
</p><p>
Here's an example script for Recursion &amp; Induction mode:
@({
(defun app (x y)
  (if (consp x)
    (cons (car x) (app (cdr x) y))
    y))

(defun rev (x)
  (if (consp x)
    (app (rev (cdr x)) (cons (car x) nil))
    nil))

(theorem rev-app-single 
  (equal (rev (app l (list v)))
         (cons v (rev l)))
  :hints (("Goal" :induct (rev l))))

(theorem rev-rev
  (implies (true-listp x)
    (equal (rev (rev x)) x))
  :hints (("Goal" :induct (rev x)
                  :in-theory (enable rev-app-single))))
})
</p><p>
Here's the general form of <code>theorem</code>:
@({
(theorem &lt;name&gt;
  &lt;formula&gt;
  [:hints (("Goal" [:induct &lt;term&gt;]
                   [:in-theory (enable &lt;name1&gt;
		                       ...
				       &lt;nameK&gt;)]))])
})
where things in [ ] are optional, etc. etc.
</p><p> R&amp;I mode also includes CCG termination analysis and, for
cases in which that fails, is configured to use lexicographic ordering
for termination proofs.  It also supports specifying Data Definitions
(<code>:doc defdata</code>) and automated Counterexample Generation
(<code>:doc cgen</code>).
</td></tr>

<!-- harshrc -- Intermediate mode not supported (doesnt work) -->
<!-- <tr><td valign=top><b>Intermediate</b><br><em>(introductory)</em></td><td> -->
<!-- <p> -->
<!-- This mode is like the R&amp;I mode (above) except that the prover is allowed -->
<!-- to perform one level of induction automatically.  <code>DEFTHM</code> or -->
<!-- <code>THEOREM</code> may be used.  This mode is like "ACL2s" mode (below) -->
<!-- except for prover restrictions on induction, generalization, and irrelevance. -->
<!-- </p> -->
<!-- </td></tr> -->
</tbody>
</table>

<h4>Standard/Industrial modes</h4>
<p>
In addition to removing prover restrictions present in introductory modes,
these modes are more friendly to customization.  By default, ACL2s will only
load <a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____ACL2-CUSTOMIZATION">acl2-customization
files</a> in non-introductory modes.  (There is a preference controlling this.)
</p>

<table>
<thead>
  <tr>
    <th>Mode</th>
    <th>Description</th>
  </tr>
</thead>
<tbody>
<tr><td><b>ACL2s</b></td><td>
<p>
This mode is full-featured. It is like the Recursion&amp; Induction
  mode, but with no restrictions on the theorem prover.
</p><p>
This is the recommended mode for a standard ACL2s user.
</p>
</td></tr>
<tr><td><b>Compatible</b></td><td>
<p>
In this mode, ACL2 is almost indistinguishable from what you would get
from executing it directly.  This mode is recommended for those
developing definitions and theorems to be used by ACL2 outside of ACL2s.
</p><p>
Admissibility in this mode, however, does not *guarantee* admissibility
in ACL2 proper (and vice-versa).  For more details, see
<a href="http://acl2s.ccs.neu.edu/acl2s/doc/impl.html#impl_hooks">How/what ACL2 functionality is modified for ACLs</a>.
Also see <a href="user_guide.html#guide_book">book development</a> for certification
with ACL2 proper inside of ACL2s/Eclipse.
</p>
</td></tr>
</tbody>
</table>

<p><em>Additional advanced note:</em>
Another feature of all these modes except "Compatible" is doing destructor
elimination before laying down a checkpoint.  Thus, the checkpoint summary
will show the formula after destructor elimination.  The downside is that the
variable names may appear cryptic and unfamiliar, but the upside is that
you get some generalization for free, usually resulting in smaller formulas.
</p><p>
Notes about how these modes are implemented are described in
<a href="http://acl2s.ccs.neu.edu/acl2s/doc/impl.html#impl_modes"><em>How modes are implemented</em></a>.
</p>
</div>

<div class="left-center" data-target="guide_classifications">
<h2>Input Command Classifications</h2>
<p>
Each input form submitted to ACL2 from the plugin is placed into
one of the following categories based on its purpose and potential
effect.  Basically, if you use RAW or ACTION input, we cannot guarantee
that the plugin will behave in a consistent way with respect to UNDOing,
etc., but the rest should behave as expected.  We present them in decreasing
order of commonness or importance to the user:
</p>

<table>
<thead>
  <tr>
    <th>Class</th>
    <th>Description</th>
  </tr>
</thead>
<tbody>
<tr><td><b>EVENT</b></td><td>
These correspond to ACL2
<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____EMBEDDED-EVENT-FORM">embedded event forms</a>,
which are those forms that can appear in <a href="user_guide.html#guide_book">books</a>.
Calls to <tt>defun</tt>, <tt>defmacro</tt>, and <tt>defthm</tt> are examples
of embedded event forms and <b>EVENT</b>s.
</td></tr>
<tr><td valign=top><b>VALUE</b></td><td>
<p>Such forms are simple computations which return a value when (and if)
they terminate.
No <b>VALUE</b> form can alter ACL2's state and, therefore, never
affects undoing or redoing.
</p><p>
A precise definition is that if ACL2 permits <tt>(cons </tt>
<em>&lt;form&gt;</em> <tt>nil)</tt>, then <em>&lt;form&gt;</em> is a <b>VALUE</b>.
</p><p>
<em>Advanced Note</em>: some <b>VALUE</b> forms
have transient side effects, but they have no logical consequence (e.g.
<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____CW">CW</a>
and
<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____WORMHOLE">WORMHOLE</a>).
</p>
</td></tr>
<tr><td valign=top><b>QUERY</b></td><td>
These are calls to some built-in ACL2 functions that report information about
the current state but are known not to modify state.  Examples include
<tt>(<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____PE">pe</a> 'append)</tt>
and
<tt>(<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____PBT">pbt</a> 0)</tt>.
</td></tr>
<tr><td valign=top><b>UNDO</b><br>(internal initiation only)</td><td>
Various UI actions which have to do with "undoing" or "moving the line up"
can initiate the execution of an <b>UNDO</b> in the session.  An ordinary
user need not concern him/herself with how this works
(<a href="http://acl2s.ccs.neu.edu/acl2s/doc/impl.html#impl_undo_redo"><em>How undo and redo are implemented<em></a>),
but should keep in mind that <b>UNDO</b>ing an <b>ACTION</b> or <b>RAW</b>
form may not have the desired effect.
</td></tr>
<tr><td valign=top><b>REDO</b><br>(internal initiation only)</td><td>
<p>This is the counterpart of <b>UNDO</b>.  It is used when resubmitting
something with the same abstract syntax and in the same environment as
something that was previously undone.
</p><p>
<b>REDO</b> enables one to (for example) edit comments above the line, by
retreating the line far enough to edit what one wants to change, and then
moving the "todo" line back to where it was.  If only comments were
changed, the session will accept the forms as <b>REDO</b>s, which happen
almost instantaneously.</b>
</p>
</td></tr>
<tr><td valign=top><b>BAD</b></td><td>
<p>If the input is a parseable ACL2 object but is an ill-formed expression
according to the current history, we call it "BAD" input.  Examples of
violations that would cause input to be staticly ill-formed are:
<ul>
<li>wrong number of parameters to a function/macro
<li>use of an undefined function/macro
<li>first element of an invocation list is not a symbol or lambda expression
<li>mismatch between expected and actual
"<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____MV">mv</a>
shape"
</ul>
</p>
</td></tr>
<tr><td valign=top><b>COMMAND</b></td><td>
There are many forms that are illegal in books but we are able to undo the
effect of.  If we recognize a form as such, we call it a <b>COMMAND</b>--
except for special cases <b>IN-PACKAGE</b> and <b>BEGIN-BOOK</b>.  The
best example of a command is "<tt>:set-guard-checking :none</tt>".
</td></tr>
<tr><td valign=top><b>ACTION</b><br>
<font color="red">(potentially dangerous!)</font></td><td>
This is the "catch-all" categorization for forms that may have effects
that we don't know how to properly undo or might even break or hang the
ACL2 session.  Users who use
<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____STOBJ">STOBJs</a>
or other
<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____STATE">STATE</a>
beyond the logical
<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____WORLD">WORLD</a>
will need to use <b>ACTION</b>s heavily, but these are advanced uses of ACL2.
</td></tr>
<tr><td valign=top><b>IN-PACKAGE</b></td><td>
This <b>COMMAND</b> gets its own category because of its role in
<a href="user_guide.html#guide_book">book development</a>.  See also
<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____IN-PACKAGE">:DOC
in-package</a>.
</td></tr>
<tr><td valign=top><b>BEGIN-BOOK</b></td><td>
This <b>COMMAND</b> gets its own category because of its role in
<a href="user_guide.html#guide_book">book development</a> with our plugin.  This form
is not part of ACL2 proper (yet!).
</td></tr>
<tr><td valign=top><b>EVENT/VALUE</b></td><td>
These are a special type of
<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____EMBEDDED-EVENT-FORM">embedded event form</a>
(<tt>value-triple</tt>s) that have no logical consequence--except that they
could halt progress by generating a hard lisp error.
</td></tr>
<tr><td valign=top><b>RAW</b><br>
<font color="red">(potentially very dangerous!)</font></td><td>
Most users of ACL2 are familiar with breaking into "raw lisp" by typing
":q" at the top-level prompt.  This is not supported in our plugin, but
<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____SET-RAW-MODE">
"raw mode"</a> is supported.  Most forms submitted under this mode are
classified as <b>RAW</b> because they have no well-defined meaning from the
ACL2 view of things.  With raw mode, the user can easily break many things,
and it's only supported for the benefit of <em>experts</em>.
</td></tr>
</tbody>
</table>
</div>

<div class="left-center" data-target="guide_desc">
<h2>Descriptions of UI Actions with key bindings</h2>
<p>
The keyboard bindings for these actions
are user modifiable through Eclipse's preferences, which is under the
<b>Window</b> menu or the <b>Eclipse</b> menu depending on platform.
The settings are under
<b>General</b> &gt; <b>Keys</b>, and show up beside their location in the
application menus (under <b>ACL2</b> or <b>Navigate</b>).
</p>
<p>
<b>Mac OS X Note:</b>
The keybindings below are for PC users.  The Mac equivalents (if available)
are the same except that Ctrl+Shift is replaced by
<img src="mac-command.gif" width="14" height="13" alt="Command">+Shift.  For
example, <em>Interrupt</em> is still Ctrl+Break (if you have a Break key), but
switching editors is
<img src="mac-command.gif" width="14" height="13" alt="Command">+Shift+o.
</p>

<table>
  <thead>
    <tr>
      <th>UI Action</th>
      <th>Icon</th>
      <th>Description</th></tr>
  </thead>

  <tbody>
<tr><td><b class="warning label">Navigation</b></td><td></td><td>(appear under "Navigate" menu)</td></tr>
<tr><td>
"Go To" | "Corresponding ..."
</td><td>
</td><td>
This switches which editor has keyboard focus.  If you are in a .lisp file,
it switches to the corresponding .a2s editor, opening it if necessary.
Vice-versa if starting from an .a2s editor.  The keyboard shortcut is
Ctrl+Shift+o (since it is related to emacs' C-x o).
</td></tr>
<tr><td>
"Go To" | "Matching Character"
</td><td>
</td><td>
If the character behind the caret (cursor) is matched to another (such as
<u><font color="red">(</font></u> and <u><font color="red">)</font></u>,
or <u><font color="red">"</font></u> and <u><font color="red">"</font></u>),
then this action moves the cursor just beyond the match.  Invoking this action
twice in a row should have no net effect <em>except</em> in the case of
going from a <u><font color="red">,</font></u> to its matching
<u><font color="red">`</font></u>, which could potentially have many commas
matching to it.  The keyboard shortcut is
Ctrl+Shift+P (as in Eclipse's Java Development Environment).
</td></tr>
<tr><td>
"Down/Up to Next/Previous Session Input" (.a2s only)
</td><td>
</td><td>
These allow the user to navigate through the session history by moving to the
beginning of the next/previous command in the history.  If, for example, one
is at the bottom of a failed proof attempt, one can navigate to the beginning
of the command that initiated it with Ctrl+Shift+Up.  "Next" is bound to
Ctrl+Shift+Down.  One can go to the end of any buffer with Ctrl+End (Eclipse
binding).
</td></tr>
<tr><td>
"Down/Up to Next/Previous Checkpoint/Input" (.a2s only)
</td><td>
</td><td>
<p>
These grant the user finer-grained navigation through the session history
than the above by also visiting checkpoints in proof attempts.  For a
description of checkpoints, see
<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____THE-METHOD">:DOC
THE-METHOD</a>.
</p><p>
"Next" is bound to Ctrl+Shift+Right and "Previous" is bound to Ctrl+Shift+Left.
Thus, to go to the first checkpoint of the previous form's output, type
Ctrl+Shift+Up, Ctrl+Shift+Right.
</p>
</td></tr>
<tr><td>
"Next/Previous/Last Command in History" (.a2s only)
</td><td>
</td><td>
The .a2s editor keeps a history of acl2 forms that have been submitted as
"immediates" (typed in the .a2s editor).  One can navigate through this
history in much the same way one can navigate through a shell history, or a
history of ACL2 commands (assuming <em>readline</em> support).  Previous:
Ctrl+Shift+, (comma);  Next: Ctrl+Shift+. (period);  Last/Current: Ctrl+Shift+/
(slash).
<p>
Actually, two orthogonal histories are maintained.  One for immediates
submitted as command forms and one for miscellaneous input, such as input to
the proof checker.  The command history for each is available only when the
session has prompted for that type of input.
</td></tr>
<tr><td><b class="warning label">Session-related</b></td><td></td></td></tr>
<tr><td>
Submit Immediate
</td><td>
</td><td>
When ACL2 is running and waiting for input, one can type input forms directly
into the .a2s buffer.  We call these "immediates."  Whenever <em>Enter</em>
(sometimes called <em>Return</em>) is typed at the end of the .a2s buffer,
we check to see
if some prefix of the typed input is a valid, complete input form.  If so,
the <em>Enter</em> is interpreted as submitting the form.  If not, the
<em>Enter</em> is inserted, as in a traditional editor.  <em>Ctrl+Enter</em>
ignores the location of the caret and will submit the first complete, valid
input form if there is one.
<p>
If the form submitted is relevant to the logical history, (i.e. not a
QUERY or VALUE), the user will be queried on whether to insert it at the
"completed" line point in the corresponding .lisp file or to immediately
undo it.  This is to maintain the invariant that the forms
above the "completed" line in the .lisp file comprise the logical history of
the session.
</td></tr>
<tr><td>
"Clean Session"
</td><td>
<img src="../icons/acl2_clean.gif" width="16" height="16">
</td><td>
Opens a dialog box with options to clear the session history, the typed
command history, and others.  Clearing the session history will stop the
associated ACL2 session (if running) and move the "completed" line in the
corresponding Lisp file to the top.  Forgetting REDO information is useful
for including updated versions of the same book.
Note that some of these actions are not readily reversible, if at all,
so use them cautiously.  Shortcut: Alt+Delete.
</td></tr>
<tr><td>
"(Re)start Session"
</td><td>
<img src="../icons/acl2_restart.gif" width="16" height="16">
</td><td>
<p>
Starts a fresh, new ACL2 session, with its output going to the current or
corresponding .a2s editor.  If an ACL2 session was already running in that
editor, it is stopped/killed.  Depending on user preferences, the dump of
previous sessions may or may not be cleared. Shortcut: Alt+Home.
</p><p>
In the corresponding Lisp file, the "completed" line is moved to the top.
The "todo" line is left where it is, meaning forms that were done or still
left "todo" in a previous session will start being read and loaded
automatically.  To avoid this, use "Stop session" (optional, but takes ACL2
interaction out of the operation) and "Undo/cancel all forms" before
"(Re)start Session".
</p>
</td></tr>
<tr><td>
"Stop Session"
</td><td>
<img src="../icons/acl2_stop.gif" width="16" height="16">
</td><td>
<p>
If ACL2 is running in this (or the corresponding) .a2s editor, stop it cleanly
or kill it.  Regardless of the state it was in before, ACL2 is *not* running
in this editor after "Stop Session" is pressed.  Shortcut: Alt+End
</p><p>
In the corresponding Lisp file, the completed line is reset and the todo line
is left where it is.
</p>
</td></tr>
<tr><td>
"Interrupt Session"
</td><td>
<img src="../icons/acl2_interrupt.gif" width="16" height="16">
</td><td>
<p>
If ACL2 is processing a command form, this will break it back out to the
top-level prompt.  This is most commonly used to interrupt the execution of
some evaluation that will take too long, or to abort what seems to be a
divergent proof attempt.  As a nod to times passed, we bind this to Ctrl+Break.
</p><p>
"Interrupt Session" often has the same effect as "Cancel all
'todo' forms," because if the form being processed by ACL2 is the next
"todo" form, either action will both interrupt ACL2 and (because an
interrupted form is not successful) move the "todo" line back to the "done"
line.
</p>
</td></tr>
<tr><td> <b class="warning label">Line-related</b></td><td></td><td></td></tr>
<tr><td>
"Undo/cancel all forms"
</td><td>
<img src="../icons/clean.gif" width="16" height="16">
</td><td>
<p>
This moves both the "completed" line and the "todo" line to the top of the
.lisp file.  ACL2 need not be running, but if it is, this will cause
anything currently executing to be interrupted, and all completed forms
to be undone in LIFO (last-in, first-out) order.  (No default shortcut)
</p><p>
The large double arrows in the icon are intended to portray moving the line
all the way to the top.
</p>
</td></tr>
<tr><td>
"Undo/cancel last form"
</td><td>
<img src="../icons/retreat.gif" width="16" height="16">
</td><td>
<p>
If there are any "todo" forms, the last will be cancelled.  If it was
currently being executed by ACL2, it will be interrupted.
If there were no "todo" forms, both lines will be moved up one form, and if
that form was relevant to the logical history, it will be undone in the
ACL2 session.  ACL2 need not be running to use this action.
Shortcut: Ctrl+Shift+M <font color="red">This has changed from 0.9.6
    to accomodate for GNOME users. To restore this binding to
    Ctrl+Shift+U, go to Window->Preferences->General->Keys and change
    the "Retreat Line" action's binding.</font>
</p><p>
The small arrow in the icon is intended to indicate the undoing of a
single form.
</p>
</td></tr>
<tr><td>
"Cancel all "todo" forms"
</td><td>
<img src="../icons/cancel.gif" width="16" height="16">
</td><td>
<p>
The "todo" line is moved to be even with the "completed" line.  If the next
"todo" form was being processed by ACL2, it is interrupted.
(No default shortcut)
</p><p>
The large arrow next to green text in the icon is intended to indicate the
undoing of all "todo" forms.
</p>
</td></tr>
<tr><td>
"Advance todo line"
</td><td>
<img src="../icons/advance.gif" width="16" height="16">
</td><td>
<p>
The "todo" line is advanced by one command form.  This will often cause ACL2 to
start processing "todo" forms.  Many forms are completed by ACL2 so quickly,
that there is but a flicker before the "completed" line is moved as well.
ACL2 need not be running to use this action, but it won't trigger ACL2 to
start.  Shortcut: Ctrl+Shift+I
</p><p>
The small down arrow in the icon is intended to indicate the advancement of
the line by a single form.
</p>
</td></tr>
<tr><td>
"Move todo up/down past cursor" (.lisp only)
</td><td>
<img src="../icons/move.gif" width="16" height="16">
</td><td>
<p>
If the "todo" line is above the cursor, it is advanced until it reaches
(or passes) the cursor.  If the "todo" line is below the cursor, it is
retreated until it passes the cursor.  Note that invoking this action
repeatedly in the same spot will have a sort of "toggle" action on the
form under or immediately after the cursor. Shortcut: Ctrl+Shift+Enter
</p><p>
The up and down arrows in the icon are intended to indicate moving the line
in either direction to get to the current spot.
</p><p>
<b>This is the only line action valid in "No Line" mode</b>, in which it has
a special (but obvious) meaning:  it submits the command form under or
following the cursor to the associated session (if exists, running, and ready)
and advances the cursor past the submitted form.
</td></tr>

<tr><td> <b class="warning label">Misc.</b></td><td></td><td></td></tr>
<!-- <tr><td> -->
<!-- Auto-complete (content-assist) -->
<!-- </td><td></td><td> -->
<!-- <p> -->
<!-- DISABLED TEMPORARILY -->
<!-- In the .lisp editor, you may press Ctrl+Space to auto-complete your -->
<!-- function/macro names, parameter names, let bindings or -->
<!-- defconsts. The functions and constants defined in ground -->
<!-- theory ACL2 are also auto-completed. If a session is open, then any -->
<!-- defined function, macro or defconst in the world will also be auto-completed. -->
<!-- </p> -->
<!-- </td></tr> -->

<tr><td>
Indent code
</td><td></td><td>
<p>
In either the .lisp editor or the immediate area of the .a2s editor, the
Tab key indents lines spanned by the current selection (or just the line
containing the caret) according to some built-in rules.  Not all lines
will have their indention changed by this operation, such as lines whose
first non-whitespace characters are ";;;".
</p>
</td></tr>

<tr><td>
Select s-exp
</td><td></td><td>
<p>
In either the .lisp editor or the immediate area of the .a2s editor,
Ctrl+Shift+Space selects (highlights) s-expressions, to help with cutting
and pasting mostly.  If nothing is highlighted, the smallest s-exp "under"
(and to the right) of the cursor is selected.  Sometimes a single token that
is not itself an s-exp (such as ')') is highlighted.  Hitting Ctrl+Shift+Space
with something already selected selects the next larger s-exp
that contains the selected region.  Thus, hitting this sequence repeatedly
selects larger and larger s-expressions until an entire top-level form is
selected.
</p><p>
Using this sequence to select a symbol causes all lines with occurrences of
that same symbol to be marked.  Selecting a non-symbol clears the markings.
This is helpful for finding definitions and uses of functions and variables.
</p>
</td></tr>

<tr><td>
Certify as book
</td><td>
<img src="../icons/acl2_book.gif" width="16" height="16">
</td><td>
<p>
See <a href="user_guide.html#guide_book">book development</a>.  Alt+C
</p>
</td></tr>

<tr><td>
Recertify ACL2s system books
</td><td></td><td>
<p>
This should only be needed if an ACL2 session fails to start up and
asks you to do this.  This could happen, for example, if you change the
version of ACL2 you are using with ACL2s.
</p>
</td></tr>
</tbody>
</table>
</div>

<div class="left-center" data-target="guide_ccg">
<h2>CCG termination analysis</h2>
<h4>Background</h4>
<p>
The "ACL2s," "Intermediate," and "Recursion &amp; Induction" session modes
include
improved termination analysis for ACL2 based on research by Pete Manolios
and Daron Vroon.  The analysis is based on "context calling graphs," so
we refer to it as CCG termination analysis for short.
</p>
<p>

Beginners can think of CCG termination analysis of as a black-box
analysis.  We say "black-box" because beginning users need not
concern themselves with the details of how CCG analysis works.
Of course, any termination analysis is necessarily incomplete and
eventually users may come across terminating functions that CCG
analysis cannot prove terminating.  When that happens, CCG
analysis will construct a function that is as simple as possible,
includes a subset of the looping behavior of the submitted
function, and which CCG analysis cannot prove terminating. This
function, along with several suggestions of how to help CCG
analysis prove termination, will be presented to the user. 
<h4>Settings</h4>
<p>
CCG is configured by calling
<b><tt>set-termination-method</tt></b> with a single parameter,
which must be one of these:
</p>
<ul>
<li><b><tt>:ccg</tt></b> - CCG analysis only (no measure-based proof
attempt)
<li><b><tt>:measure</tt></b> - no CCG analysis (measure-based proofs
only)
</ul>
<p>
Regardless of this or other settings, ACL2's built-in
method will be used if an explicit measure is specified.
</p><p>
For advanced debugging purposes, <tt>:set-ccg-verbose t</tt> causes the
analysis to show what it is doing.  This generates <em>lots</em> of
output, however.
</p><p>
Finally, "Compatible" mode does not include CCG, and "Programming" mode
does not need CCG.  CCG is independent of the rest of ACL2s in the sense
that it is implemented as an ACL2 book in the acl2s-modes plugin.
</p>

<h4>More Documentation</h4>
<p>
Our CCG termination analysis is highly customizable and includes
many features not mentioned here. For  detailed documentation
please refer to <tt>:doc ccg</tt> from inside a session. 
</p>
</div>

<div class="left-center" data-target="guide_datadef">
<h2>Data Definitions</h2>
<h4>Background</h4>
<p>
Data definitions are an essential part of crafting programs and
modeling systems. Whereas most programming languages provide rich
mechanisms for defining datatypes, ACL2 only really provides a
limited collection of built-in types and <code>cons</code>. 

<p>
This state of affairs presented us with a challenge when we started
teaching undergraduates how to model, specify and reason about
computation, because even freshmen students have a type-centric view
of the world.
</p>

<p>
We introduced the <b class="embolden">defdata</b> framework in ACL2s
in order to provide a convenient, intuitive way to specify data
definitions.  A version of <code>defdata</code> has appeared in ACL2s
since at least August 2009 (in version 0.9.7), and we have been
extending and improving it since then.
</p>


<h4>Documentation</h4>
<p>
A readable and example-oriented description of
the <code>defdata</code> framework appears in the ACL2 2014 Workshop
paper <a href="http://arxiv.org/abs/1406.1557">Data Definitions in
ACL2 Sedan</a>.  Furthur documentation is also available by
submitting <code>:doc defdata</code> inside an ACL2s session.
</p>
</div>

<div class="left-center" data-target="guide_RT">
<h2>Counterexample Generation</h2>
<h4>Background</h4>
<p>
Counterexample generation framework seamlessly integrates (random)
testing and the full power of the theorem prover (ACL2) to provide an
automatic bug-finding capability that often finds counterexamples to
false conjectures.  This feature is especially effective when used in
conjunction with the data definition framework.  The counterexamples
allow users to quickly fix specification errors and to learn the
valuable skill of designing correct specifications. This feature is
enabled by default and requires no special syntax so that users get
the benefit of automated testing without any effort on their part.
The data definition framework supports the counterexample generation
framework in an important way . For example, we guarantee
that random testing will automatically generate examples that
satisfy any hypotheses restricting the (defdata) type of a variable.
</p>
<p>
The ACL2 2011 workshop paper
<a href="http://arxiv.org/pdf/1105.4394v2.pdf">Integrating Testing and Interactive Theorem Proving</a>
goes into the details of this feature, but is a very easy read. The reader is encouraged to go through it.
</p>
<p>
All modes except "Compatible" and "Programming" have testing enabled
by default.  This feature is independent of the rest of ACL2s in the
sense that it is implemented as an ACL2 book in the acl2s-modes
plugin.
</p>

<h4>Documentation</h4>
<p>
For documentation on usage and settings please refer to <code>:doc
cgen</code> from inside a session.  See in particular <code>:doc
test?</code>.
</p>

<!-- <p> -->
<!-- The counterexample generation and data definition framework was -->
<!-- implemented by Harsh Raju Chamarthi, Peter Dillinger, Matt Kaufmann  -->
<!-- and Pete Manolios. -->
<!-- </p> -->
</div>

<div class="left-center" data-target="guide_book">
  <a name="guide_book"></a>
<h2>ACL2 Book Development</h2>
<h4>Introduction</h4>
<p>
An ACL2/ACL2s <a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____BOOKS">book</a>
is a reusable collection of definitions and other
<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____EVENTS">events</a>
(<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____EMBEDDED-EVENT-FORM">embedded event forms</a>,
actually).  A valid book can be certified to demonstrate its validity and/or
to prepare it for
<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____INCLUDE-BOOK">inclusion</a> elsewhere.
</p><p>
To develop a .lisp file as a book in ACL2s, either create the file using
the ACL2s/Lisp file wizard selecting "Create with book code", or put this at the
top/beginning:
<pre>
<code class="lisp">
  (begin-book t :ttags :all)
  (in-package "ACL2")
</code>
</pre>

Usually the only things that would go before the <code>begin-book</code> form
are package definitions (<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____EVENTS">defpkg</a>),
but these aren't worth learning about until you know you need them.
</p><p>
After the <code>begin-book</code> and <code>in-package</code> come the
definitions and other events for your book.  As one is developing a book,
it is very helpful to use the line action discussed above for interactive
development.  One difference is that everything starting from the
<code>begin-book</code> form that is in the "completed" region will be
highlighted blue as long as it is valid for use in a book (see 
<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____EMBEDDED-EVENT-FORM">EMBEDDED-EVENT-FORM</a>).
Any <em>tangent</em> from book-valid forms will begin gray highlight.  Such
tangents should eventually be undone and removed before certification.
</p><p>
To ensure your book is valid/certifiable, save your changes and choose
"Certify as book" from the menu or toolbar (<img src="../icons/acl2_book.gif"
width=16 height=16>).  An Eclipse console will dump the output of the
certification process and indicate success or failure when finished.
</p>

<h4>More detail</h4>
<p>
In ACL2s, a <code>(begin-book ...)</code> form in a .lisp file has
special significance, indicating the .lisp file is intended to define
a book.  Our approach might seem strange at first, but it really works
pretty well with the seemingly obscure requirements ACL2 has for books.
This and the next subsection get into the details and the justification.
</p><p><img src="book_dev.png" width="424" height="400" align="right">
The <em>preamble</em> is everything that comes before the
<code>begin-book</code>.  This defines what ACL2 authors call the
<em>certification world</em> for the book, which become the book's
<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____PORTCULLIS"><em>portcullis</em></a>.  The
simplest explanation for the preamble/portcullis is that it is where
any <a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____EVENTS"><code>defpkg</code></a> events
should go, because
these are not allowed inside books (because Common Lisps vary in their
ability to compile files that define packages).
</p><p>
The <code>begin-book</code> form itself takes the syntax of ACL2's
<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____CERTIFY-BOOK"><code>certify-book</code></a> except
<code>begin-book</code> doesn't take the "book-name" or "k" parameters.  In
fact, here are the parameter and guard specifications for ACL2s's
<code>begin-book</code>:</p>
@({
  (defmacro begin-book (&amp;optional (compile-flg 't)
                      &amp;key (defaxioms-okp 'nil)
                           (skip-proofs-okp 'nil)
                           (ttags 'nil)
                           (save-expansion 'nil))
  (declare (xargs :guard (and (booleanp compile-flg)
                              (booleanp defaxioms-okp)
                              (booleanp skip-proofs-okp)
                              (member-eq save-expansion '(t nil :save)))))
  ...)
  })
<p>
So the parameters to <code>begin-book</code> indicate the parameters that
should be given to <code>certify-book</code> for certification of the
containing .lisp file as a book.  One can look up the meaning of the
<code>compile-flg</code>, <code>defaxioms-okp</code>,
<code>skip-proofs-okp</code>, and <code>save-expansion</code> arguments
from <a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____CERTIFY-BOOK">ACL2's documentation for
<code>certify-book</code></a>.  But the <code>ttags</code> argument is
important in ACL2s:
</p><p>
ACL2s session modes other than "Compatible" mode utilize ACL2 extensions that
ACL2 cannot verify are sound or even safe.  These modes include books
for ACL2s that define <em>trust tags</em> or <em>ttags</em> in order to tweak
ACL2 in non-standard ways.  In order to certify a book that depends on
the use of trust tags, including books defined in a mode other than
"Compatible", an appropriate <code>:ttags</code> argument must
be given to <code>begin-book</code>.  We recommend the all-encompassing
<code>:all</code> argument to <code>:ttags</code>, which roughly says,
"I recognize this book could depend on some non-standard stuff, and
I don't want to bother specifying the details.  Just go ahead."
See the docs for <a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____TTAGS-SEEN">ttags-seen</a>
and <a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____CERTIFY-BOOK">certify-book</a> for more
information on how to be more specific.
</p><p>
The <em>contents</em> or <em>body</em> of a book is everything after the
<code>begin-book</code> form as long as it conforms to
<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____BOOK-CONTENTS">ACL2's requirements for
book contents</a>.  Basically, the first form must be
<code>(in-package "</code><em>blah</em><code>")</code> where <em>blah</em> names
a built-in package (such as ACL2 or ACL2-USER) or a package defined in the
preamble.  (The wizard for "New ACL2s/Lisp file" can generate appropriate
"book code" that defines a package in the standard way, begins the book, and
enters the defined package.)  After the
<code>(in-package "</code><em>blah</em><code>")</code> form are
<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____EMBEDDED-EVENT-FORM">embedded event
forms</a> using <em>blah</em> as the default package.  In ACL2s, embedded
event forms have the <a href="user_guide.html#guide_classifications">input
classification</a> EVENT or EVENT/VALUE.
</p><p>
Book code in the completed region is formatted specially.  The preamble
looks like any other non-book .lisp file, and so uses gray highlighting.
The <code>begin-book</code> form begins the part that distinguishes this
.lisp file as a book, and so begins blue highlighting.  The blue
highlighting continues either until the end of the current "completed"
region, or until the end of the last form that was valid as the contents
of a book.  This visually tells the user whether and where the book
contents have became polluted with code disallowed in books.
</p><p>
We call anything after a valid book body a <em>tangent</em>, which is given
gray highlight in the completed region.  A tangent might be intentional;
the user might want to try things in ACL2 without the restrictions imposed
by book development and later undo his work and clean it up for use as
book code.  Any .lisp file with a tangent (that hasn't been commented out)
will not certify, and we cannot forsee any case in which ACL2s would
falsely report a form as tangential.
</p>
<a name="guide_book_impl"></a>
<h4>Implementation and compatibility with ACL2</h4>
<p>
One of the goals of ACL2s is to maintain a high degree of compatibility
with existing ACL2 development patterns/infrastructure while hiding some
of the nasty details from ACL2s-only users.  Compatibility of ACL2s
book development with existing patterns/infrastructure utilizes the fact
that the text in the ACL2s .lisp editor is not exactly what is saved on
disk.  In particular, when book code is present, the preamble and the
begin-book form are saved in a specially-formatted comment.  Thus, when
ACL2 reads the .lisp file, the first (uncommented) thing it sees is
the in-package.
</p><p>
Our "preamble" roughly corresponds to what ACL2 users would put in
a .acl2 file.  We have a java subroutine/program that can extract the
specially-formatted preamble+begin-book from a .lisp file and put it
into a .acl2 file with the begin-book call translated to a corresponding
certify-book call.  This subroutine is used to generate a .acl2 file when
the ACL2s users asks to "Certify as book" but the functionality can also
be accessed as a stand-alone program.  The class is
acl2s.lib.certify.MaybeExtractPreamble in acl2s-lib (acl2s-lib.jar in the
plugin directory).  This program plays nice with old codebases in that it
will not overwrite an existing .acl2 file unless there is an ACL2s preamble
in the corresponding .lisp file.
</p><p>
Right now, however, there's no automatic way to import an existing book AND
its "preamble" into an ACL2s-ready .lisp file.  You can, however, open the
.lisp file with ACL2s, which from the ACL2s perspective has no book code
yet, insert the preamble and <code>begin-book</code> form at the top, and
save it.
</p>
</div>

<div class="left-center" data-target="guide_trace">
<h2>Tracing function execution</h2>
<p>
ACL2s offers a "beautified" version of ACL2's tracing capability, which is
inspired by Common Lisp tracing capabilities.  Perhaps the capability is
most easily demonstrated with an example:
</p>
<h4>Tracing Example</h4>
@({
(defun app (x y)
  (if (endp x)
    y
    (cons (car x)
          (app (cdr x) y))))

(defun rev (x)
  (if (endp x)
    nil
    (app (rev (cdr x))
         (cons (car x) nil))))

(trace* app)

(rev '(1 2))
})
<p>
The last input produces the following output:
</p>
<code>
<span style="color:#0000b0">ACL2 &gt;</span><span style="color:#808080">VALUE</span>
<span>(rev '(1 2))</span><br></code>
<table style="border:solid yellow" cellpadding=0 cellspacing=0><tr><td>
<code><span style="color:#008000">
<pre style="margin: 0cm 0cm 0cm 0cm">1&gt; (APP NIL '(2))
&lt;1 (APP NIL '(2))
 = '(2)
1&gt; (APP '(2) '(1))
  2&gt; (APP NIL '(1))
  &lt;2 (APP NIL '(1))
   = '(1)
&lt;1 (APP '(2) '(1))
 = '(2 1)</pre</span></code>
</td></tr></table>

<code>
<span style="color:#008000;border:solid purple">(2 1)</span<br>
<span style="color:#0000b0">ACL2 &gt;</span><br>
</code>

<p>
The output outlined in yellow is the tracing output.  This indicates that
during the execution of <code>(rev '(1 2))</code>, <code>app</code> was
first called with parameters <code>nil</code> and the list <code>(2)</code>.
Note that arguments are quoted as needed so that one could copy and paste
the call that is displayed, as in <code>(APP NIL '(2))</code>.  The second
and third line of tracing output indicate that the same call returned the list
<code>(2)</code>.  Like parameters, the return value
is quoted, so that what is displayed is a theorem, in this case that
<code>(APP NIL '(2))</code> equals <code>'(2)</code>.
</p><p>
The next time <code>app</code> is called in the execution of
<code>(rev '(1 2))</code> is, as the output indicates, as
<code>(APP '(2) '(1))</code>.  The next line,
"<code>2&gt; (APP NIL '(1))</code>" indicates that <code>app</code> was
called recursively.  The "2" means the recursive depth is two.  We then
see that that call (level 2) returns <code>(1)</code> and the outer call
of <code>app</code> (level 1) returns <code>(2 1)</code>.
</p><p>
The final <code>(2 1)</code> outlined with purple is the usual printed
output of evaluating <code>(rev '(1 2))</code>.  This comes from the
"PRINT" part of "READ-EVAL-PRINT (LOOP)".
</p>

<h4>More Tracing Details</h4>
<p>
One can trace multiple functions simultaneously with
<code>(trace* fn1 fn2)</code> or with multiple calls
to <code>trace*</code>.
</p><p>
The tracing is active as long as the <code>trace*</code> form is in the
completed region of your source code.  It is true that tracing has no
impact on ACL2's logical world, but tracing does depend on ACL2's logical
world.  So at least for now, we consider <code>trace*</code> to be
"relevant".  Calls to <code>trace*</code> are
<a href="user_guide.html#guide_classifications">classified</a> as COMMAND, which means they
are not allows in <a href="user_guide.html#guide_book">books</a>.
</p><p>
It is ill-advised to trace functions built into ACL2.  Such functions
are likely to be used by ACL2 itself, so you are likely to get mounds of
output that originates from the operation of ACL2 itself before you get
the output you are looking for.  One can effectively trace one's own uses
of a built-in function by writing a simple proxy function that directly
calls the desired function, replacing your uses of the built-in function,
and tracing the proxy.  For example: 
</p>
@({
(defun my-butlast (lst n)
  (butlast lst n))

(trace* my-butlast)
})

<p>
If one attempts to use tracing in "Compatible" mode,
you might get this output:
</p>
<pre><code class="lisp">1&gt; !! Warning: guard-checking is not :none, so trace    !!
   !!   output could be misleading or appear incorrect. !!
   !!   (see :DOC set-guard-checking)                   !!
   (REV '(1 2))
  2&gt; (APP NIL '(2))
  &lt;2 (APP NIL '(2))
   = '(2)
  2&gt; (APP '(2) '(1))
  &lt;2 (APP '(2) '(1))
   = '(2 1)
&lt;1 (REV '(1 2))
 = '(2 1)
</code></pre>
which means exactly what it says.
</div>

<!-- <a name="guide_graphics"> -->
<!-- <h2>Graphics Development</h2> -->
<!-- <p> -->
<!-- ACL2s supports development of simple graphical applications, inspired by -->
<!-- some teachpacks in <a href="http://www.drscheme.org">DrScheme</a> -->
<!-- and <a href="http://www.ccs.neu.edu/home/cce/acl2/">DrACuLa</a>.  We intend -->
<!-- this to be a motivational pedagogical tool, so that students can prove -->
<!-- theorems about something they can literally see in action and play with. -->
<!-- </p> -->
<!-- <p> -->
<!-- A basic API is available by including a book from the ACL2s system -->
<!-- books, -->
<!-- </p> -->
<!-- <blockquote> -->
<!-- <tt>(include-book "graphics" :dir :acl2s :ttags :all)</tt> -->
<!-- </blockquote> -->
<!-- <blockquote> -->
<!-- <em>Advanced note:</em> Although this is an ACL2 book, the graphical capabilities -->
<!-- are provided by the ACL2s plugin to Eclipse, so you won't be able to use -->
<!-- graphical applications outside of ACL2s, but you can certainly reason -->
<!-- about them in ACL2 without ACL2s.  In fact, if an astute ACL2 user -->
<!-- decomposes this book, he/she will find logical underpinnings that enable -->
<!-- reasoning not only about pieces of a graphical system, but about the -->
<!-- reactive behavior of the overall system.  But this "public" book is -->
<!-- designed only for reasoning about the pieces in isolation. -->
<!-- </blockquote> -->
<!-- <p> -->
<!-- In the following API, a "configuration" is an abstraction of the -->
<!-- current state of the graphical world, and this abstraction is whatever -->
<!-- the user of the API wants it to be.   The user can register a -->
<!-- function to construct a "presentation" from this "configuration", which -->
<!-- will be used to re-present the graphical world after each event/update. -->
<!-- </p><p> -->
<!-- At present, the graphics are limited to a single window with a square -->
<!-- canvas and a textual status line at the bottom.  Events are limited to -->
<!-- timer events, mouse clicks, and key presses that correspond to printable -->
<!-- characters.  (Sorry, arrow keys.) -->
<!-- </p><p> -->
<!-- The API includes some EVENTs for registering event handler routines -->
<!-- &amp; data: -->
<!-- </p> -->

<!-- <table cellspacing=3 cellpadding=3 border=3> -->
<!-- <tr><td valign=top> -->
<!-- <nobr> -->
<!-- <tt>(set-initial-configuration</tt> <em>v</em><tt>)</tt> -->
<!-- </nobr> -->
<!-- </td><td> -->
<!-- This registers the value of <em>v</em> as the initial "configuration". -->
<!-- How this corresponds to what is shown on screen is determined by -->
<!-- the next setting. -->
<!-- </td></tr> -->

<!-- <tr><td valign=top> -->
<!-- <nobr> -->
<!-- <tt>(set-configuration-presenter</tt> <em>f</em><tt>)</tt> -->
<!-- </nobr> -->
<!-- </td><td> -->
<!-- This registers the named function <em>f</em> as the translation from -->
<!-- "configurations" to "presentations".  After each update to the -->
<!-- graphics "configuration", this function will be called with -->
<!-- [first argument] that configuration and [second argument] an -->
<!-- empty presentation.  The return value is treated as the graphics -->
<!-- presentation to show.  This is built using API presentation -->
<!-- modification routines described in the next list. -->
<!-- <br><br> -->
<!-- This event overwrites any previous setting for the configuration -->
<!-- presenter.  Initially, this is the identity function, which means -->
<!-- the graphics "configuration" is treated as the "presentation". -->
<!-- </td></tr> -->

<!-- <tr><td valign=top> -->
<!-- <nobr> -->
<!-- <tt>(add-timer-handler</tt> <em>delay-ms</em> <em>f</em><tt>)</tt> -->
<!-- </nobr> -->
<!-- </td><td> -->
<!-- This registers the named function <em>f</em> as a "timer handler". -->
<!-- Once started, our system invokes this function every <em>delay-ms</em> -->
<!-- milliseconds with the current "configuration" and uses the return value -->
<!-- as the updated "configuration".  As the name implies, you can register -->
<!-- multiple timers with their own (or the same) handler. -->
<!-- </td></tr> -->

<!-- <tr><td valign=top> -->
<!-- <tt>(add-key-handler</tt> <em>f</em><tt>)</tt> -->
<!-- </td><td> -->
<!-- This registers the named function <em>f</em> as a "key handler". -->
<!-- When a character is typed into the graphics window, we invoke each -->
<!-- registered key handler with [first argument] the ACL2/Lisp character -->
<!-- that was typed and [second argument] -->
<!-- the current "configuration".  We use the return value -->
<!-- as the updated "configuration".  Note that keys that do not correspond -->
<!-- to Lisp characters, such as arrow keys, are not currently supported. -->
<!-- </td></tr> -->

<!-- <tr><td valign=top> -->
<!-- <tt>(add-click-handler</tt> <em>f</em><tt>)</tt> -->
<!-- </td><td> -->
<!-- This registers the named function <em>f</em> as a "click handler". -->
<!-- When the user clicks in the graphics window, we invoke each -->
<!-- registered key handler with -->
<!-- [first argument] the number of the button clicked (1=left 2=middle 3=right), -->
<!-- [second argument] the X position of the click -->
<!-- (a rational proportion, 0=left-most 1=right-most), -->
<!-- [third argument] the Y position of the click -->
<!-- (a rational proportion, 0=top-most 1=bottom-most), -->
<!-- and [fourth argument] the current "configuration". -->
<!-- The return value is used as the updated "configuration". -->
<!-- </td></tr> -->
<!-- </table> -->
<!-- <p> -->
<!-- The API also includes some functions for constructing/modifying -->
<!-- "presentations". -->
<!-- </p><p> -->
<!-- Unlike what one might expect, X and Y coordinates (and widths and -->
<!-- heights) are given as ratios (rationals from 0 to 1) of the entire -->
<!-- canvas.  This allows one to specify what the presentation -->
<!-- should look like supposing it is <em>not</em> composed of discrete pixels. -->
<!-- Working directly with pixels would allow one to make the displayed -->
<!-- result as "pretty" as one wants, but this library is intended to -->
<!-- discourage such tweaking in favor of focusing on the "concept" of the -->
<!-- presentation. -->
<!-- </p><p> -->
<!-- Colors are specified in several ways, including all of -->
<!-- the ways to specify a color as a string in HTML.  Some examples include -->
<!-- <tt>"#A080FF"</tt>, <tt>"blue"</tt>, <tt>:gray</tt>, <tt>'violet</tt> -->
<!-- and <tt>'(255 0 127)</tt>. -->
<!-- </p><p> -->
<!-- Image paths are strings and interpreted by Java in the expected, -->
<!-- OS-dependent way, except that forward slashes are always permitted as -->
<!-- a directory separator character (for portability). -->
<!-- Paths can be absolute or relative to the directory -->
<!-- containing the .lisp file, such as <tt>"abc.png"</tt>, -->
<!-- <tt>"../images/foo.jpg"</tt>, or <tt>"/home/me/pics/me.jpg"</tt> (unix/mac -->
<!-- specific); relative is preferred for easy packaging of images with your -->
<!-- source code.  The image files themselves can be PNG -->
<!-- (recommended for drawings/text), JPG (recommended for photos/scenes), and -->
<!-- possibly others.  PNG transparency is supported. -->
<!-- </p><p> -->
<!-- Here are the functions: -->
<!-- </p> -->
<!-- <table cellspacing=3 cellpadding=3 border=3> -->
<!-- <tr><td valign=top> -->
<!-- <nobr> -->
<!-- <tt>(set-status-bar</tt> <em>str</em> <em>presentation</em><tt>)</tt> -->
<!-- </nobr> -->
<!-- </td><td> -->
<!-- This returns a modified version of <em>presentation</em> in which -->
<!-- the status bar text is set to the string <em>str</em>. -->
<!-- </td></tr> -->

<!-- <tr><td valign=top> -->
<!-- <table border=0 cellpadding=0 cellspacing=0><tr><td valign=top> -->
<!-- <tt>(draw-line</tt>&nbsp; -->
<!-- </td><td> -->
<!-- <em>x1</em> <em>y1</em> <em>x2</em> <em>y2</em> -->
<!-- <em>color</em> <em>presentation</em><tt>)</tt> -->
<!-- </td></tr></table> -->
<!-- </td><td> -->
<!-- This returns a modified version of <em>presentation</em> in which -->
<!-- a line has been drawn from (<em>x1</em>,<em>y1</em>) to -->
<!-- (<em>x2</em>,<em>y2</em>) in the given <em>color</em>. -->
<!-- </td></tr> -->

<!-- <tr><td valign=top> -->
<!-- <table border=0 cellpadding=0 cellspacing=0><tr><td valign=top> -->
<!-- <tt>(outline-oval</tt>&nbsp; -->
<!-- </td><td> -->
<!-- <em>x</em> <em>y</em> <em>w</em> <em>h</em> -->
<!-- <em>color</em> <em>presentation</em><tt>)</tt> -->
<!-- </td></tr></table> -->
<!-- </td><td> -->
<!-- This returns a modified version of <em>presentation</em> in which -->
<!-- the outline of an oval extending right from <em>x</em> with width -->
<!-- <em>w</em> and down from <em>y</em> with height <em>h</em> is drawn -->
<!-- in the given <em>color</em>. -->
<!-- </td></tr> -->

<!-- <tr><td valign=top> -->
<!-- <table border=0 cellpadding=0 cellspacing=0><tr><td valign=top> -->
<!-- <tt>(outline-oval-centered</tt>&nbsp; -->
<!-- </td><td> -->
<!-- <em>x</em> <em>y</em> <em>w</em> <em>h</em> -->
<!-- <em>color</em> <em>presentation</em><tt>)</tt> -->
<!-- </td></tr></table> -->
<!-- </td><td> -->
<!-- This returns a modified version of <em>presentation</em> in which -->
<!-- the outline of an oval centered at (<em>x</em>, <em>y</em>) -->
<!-- with width <em>w</em> and height <em>h</em> is drawn -->
<!-- in the given <em>color</em>. -->
<!-- </td></tr> -->

<!-- <tr><td valign=top> -->
<!-- <table border=0 cellpadding=0 cellspacing=0><tr><td valign=top> -->
<!-- <tt>(fill-oval</tt>&nbsp; -->
<!-- </td><td> -->
<!-- <em>x</em> <em>y</em> <em>w</em> <em>h</em> -->
<!-- <em>color</em> <em>presentation</em><tt>)</tt> -->
<!-- </td></tr></table> -->
<!-- </td><td> -->
<!-- This returns a modified version of <em>presentation</em> in which -->
<!-- the oval extending right from <em>x</em> with width -->
<!-- <em>w</em> and down from <em>y</em> with height <em>h</em> is filled -->
<!-- with the given <em>color</em>. -->
<!-- </td></tr> -->

<!-- <tr><td valign=top> -->
<!-- <table border=0 cellpadding=0 cellspacing=0><tr><td valign=top> -->
<!-- <tt>(fill-oval-centered</tt>&nbsp; -->
<!-- </td><td> -->
<!-- <em>x</em> <em>y</em> <em>w</em> <em>h</em> -->
<!-- <em>color</em> <em>presentation</em><tt>)</tt> -->
<!-- </td></tr></table> -->
<!-- </td><td> -->
<!-- This returns a modified version of <em>presentation</em> in which -->
<!-- the oval centered at (<em>x</em>, <em>y</em>) -->
<!-- with width <em>w</em> and height <em>h</em> is filled -->
<!-- with the given <em>color</em>. -->
<!-- </td></tr> -->

<!-- <tr><td valign=top> -->
<!-- <table border=0 cellpadding=0 cellspacing=0><tr><td valign=top> -->
<!-- <tt>(outline-rect</tt>&nbsp; -->
<!-- </td><td> -->
<!-- <em>x</em> <em>y</em> <em>w</em> <em>h</em> -->
<!-- <em>color</em> <em>presentation</em><tt>)</tt> -->
<!-- </td></tr></table> -->
<!-- </td><td> -->
<!-- This returns a modified version of <em>presentation</em> in which -->
<!-- the outline of a rectangle extending right from <em>x</em> with width -->
<!-- <em>w</em> and down from <em>y</em> with height <em>h</em> is drawn -->
<!-- in the given <em>color</em>. -->
<!-- </td></tr> -->

<!-- <tr><td valign=top> -->
<!-- <table border=0 cellpadding=0 cellspacing=0><tr><td valign=top> -->
<!-- <tt>(fill-rect</tt>&nbsp; -->
<!-- </td><td> -->
<!-- <em>x</em> <em>y</em> <em>w</em> <em>h</em> -->
<!-- <em>color</em> <em>presentation</em><tt>)</tt> -->
<!-- </td></tr></table> -->
<!-- </td><td> -->
<!-- This returns a modified version of <em>presentation</em> in which -->
<!-- the rectangle extending right from <em>x</em> with width -->
<!-- <em>w</em> and down from <em>y</em> with height <em>h</em> is filled -->
<!-- with the given <em>color</em>. -->
<!-- </td></tr> -->

<!-- <tr><td valign=top> -->
<!-- <table border=0 cellpadding=0 cellspacing=0><tr><td valign=top> -->
<!-- <tt>(put-image</tt>&nbsp; -->
<!-- </td><td> -->
<!-- <em>x</em> <em>y</em> <em>w</em> <em>h</em> -->
<!-- <em>path</em> <em>presentation</em><tt>)</tt> -->
<!-- </td></tr></table> -->
<!-- </td><td> -->
<!-- This returns a modified version of <em>presentation</em> in which -->
<!-- the image file given by the string <em>path</em> has been placed -->
<!-- with its top-left corner at position (<em>x</em>, <em>y</em>) and -->
<!-- scaled to extend by width <em>w</em> and height <em>h</em>. -->
<!-- </td></tr> -->

<!-- <tr><td valign=top> -->
<!-- <table border=0 cellpadding=0 cellspacing=0><tr><td valign=top> -->
<!-- <tt>(center-image</tt>&nbsp; -->
<!-- </td><td> -->
<!-- <em>x</em> <em>y</em> -->
<!-- <em>path</em> <em>presentation</em><tt>)</tt> -->
<!-- </td></tr></table> -->
<!-- </td><td> -->
<!-- This returns a modified version of <em>presentation</em> in which -->
<!-- the image file given by the string <em>path</em> has been centered at -->
<!-- position <em>x</em>, <em>y</em>.  Conceptually, you should think of -->
<!-- this function as placing an image of negligible/unimportant size at -->
<!-- a point in space.  Unlike <tt>put-image</tt>, this will -->
<!-- draw the image at its native size, but to stay "conceptual", we -->
<!-- recommend "put-image" if resulting image size is large or important. -->
<!-- </td></tr> -->

<!-- <tr><td valign=top> -->
<!-- <table border=0 cellpadding=0 cellspacing=0><tr><td valign=top> -->
<!-- <tt>(center-text</tt>&nbsp; -->
<!-- </td><td> -->
<!-- <em>x</em> <em>y</em> <em>text</em> <em>h</em> -->
<!-- <em>color</em> <em>presentation</em><tt>)</tt> -->
<!-- </td></tr></table> -->
<!-- </td><td> -->
<!-- This returns a modified version of <em>presentation</em> in which -->
<!-- the text of the string <em>text</em> has been drawn with height <em>h</em> -->
<!-- in color <em>color</em>, centered at position <em>x</em>, <em>y</em>. -->
<!-- If <em>h</em> is zero, a default readable size is used.   -->
<!-- </td></tr> -->

<!-- <tr><td valign=top> -->
<!-- <table border=0 cellpadding=0 cellspacing=0><tr><td valign=top> -->
<!-- <tt>(put-text</tt>&nbsp; -->
<!-- </td><td> -->
<!-- <em>x</em> <em>y</em> <em>text</em> <em>h</em> -->
<!-- <em>color</em> <em>presentation</em><tt>)</tt> -->
<!-- </td></tr></table> -->
<!-- </td><td> -->
<!-- This returns a modified version of <em>presentation</em> in which -->
<!-- the text of the string <em>text</em> has been drawn with height <em>h</em> -->
<!-- in color <em>color</em> with its top-left corener at position -->
<!-- <em>x</em>, <em>y</em>.  If <em>h</em> is zero, a default readable size is used.   -->
<!-- </td></tr> -->

<!-- </table> -->
<!-- <p> -->
<!-- Finally, to run your graphics program, execute <tt>(big-bang)</tt>, -->
<!-- which should open a new window, etc. -->
<!-- </p><p> -->
<!-- <a href="reversi.lisp">Here is an example .lisp file</a> that has the -->
<!-- graphical skeleton of an Othello/Reversi game.  It shows the board -->
<!-- and you can switch a spot between white, black, and empty by clicking -->
<!-- it.  The logic of the game (what's legal, whose turn it is, what should -->
<!-- happen in response to certain actions, etc.) is not included. -->
<!-- </p> -->

</section>
</div>
</div>



<!-- <hr align=center> -->

<!-- <a name="impl"></a> -->
<!-- <div class="row"> -->
<!-- <h2>Notes for ACL2s Hackers</h2> -->
<!-- <ul class="disc"> -->
<!-- <li> ACL2s Design <a href=design.html>Notes</a> by Peter Dillinger. -->
<!-- <li> Implementation <a href=impl.html>Notes</a> by Peter Dillinger. -->
<!-- </ul> -->
<!-- </div> -->


<script src="http://ajax.googleapis.com/ajax/libs/jquery/1.9.1/jquery.min.js"></script>
<script>
//<![CDATA[
window.jQuery || document.write('<script src=/jquery-1.9.1.min.js><\/script>')
//]]>
")
