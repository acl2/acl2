(in-package "ACL2S")

(include-book "xdoc/top" :dir :system)

(defxdoc acl2s-tutorial
  :parents (acl2::acl2-sedan)
  :short "A short ACL2s tutorial"
  :long "
<h3>Get Started</h3>

<p>
Before starting this guide, follow the @(see acl2s-installation) guide to install ACL2s on your system.
</p>

<p>
We will now guide you through the process of creating a new ACL2s/Lisp
file, typing definitions into that file, opening up an associated ACL2
session, sending definitions to the session, querying the session,
etc.
</p>


<h3>Get Set...</h3>
<p> The first time you run Eclipse, it will prompt you for a
\"workspace\" location. This is where Eclipse will save your
configuration and layout and is the default location for your ACL2s
projects and their associated files. Please <b>choose a fresh
workspace</b> (e.g. /Users/yourname/acl2s-workspace) that is different
from the workspace you use for Java or other eclipse projects.
</p>

<p>
If you get a welcome window, you can either click on \"Hide\" at the
top-right corner of the screen or click on the \"X\" button to the right
of the \"Welcome\" tab at the top of the screen.
</p>

<p>To familiarize yourself with some Eclipse vocabulary and navigating
the workbench, we recommend going through
the <a href=\"http://help.eclipse.org/2022-09/topic/org.eclipse.platform.doc.user/gettingStarted/qs-02a.htm\">Basic
Tutorial</a> section of the Workbench User Guide.
</p>

<p>
<b>Create a project</b>: Select <b>File</b> | <b>New</b>
| <b>Project...</b>  and select <b>Project</b> from the
group <b>General</b>.  Give a name to the project that will contain
your ACL2 developments and click <b>Finish</b>.
</p><p>
<b>Open the \"ACL2 Development\" perspective</b>:  Select
<b>Window</b> | <b>Perspective</b> | <b>Open Perspective</b> | <b>Other...</b> and then select <b>ACL2 Development</b> and then <b>Open</b> in the window that appears.
You could have instead clicked on the
<icon src=\"res/acl2s/new_persp.gif\" width=\"16\" height=\"16\"/> icon in the top-right corner.
The new perspective will change the layout of your workbench.
</p>

<p>
Note that, on macOS, depending on where the workspace and project
directories are located, you may get a popup asking you to give Eclipse
access to one of your folders (typically Documents or Desktop). You should
respond \"Yes\" if you're comfortable letting Eclipse access these folders
(so it can access your workspace and project folders), or respond \"No\" and
move your workspace somewhere that macOS does not require permission to
access (see <a href=\"https://support.apple.com/guide/mac-help/control-access-to-files-and-folders-on-mac-mchld5a35146/mac\">this Apple help page</a> for more information).
</p>

<p>
<b>Create a new Lisp file</b> for getting the feel of Eclipse and our
plugin.  Select <b>File</b> | <b>New</b> | <b>ACL2s/Lisp file</b>.
The \"Directory\" should already indicate the project you just created.
If not, browse to the project you just created.  Pick a file name like
\"test.lisp\" or leave the default.  Use \"ACL2s\" for the session mode
and click <b>Finish</b>.
</p>

<p>
You can now type some ACL2 code in the editor.  Type in this
definition to get the feel of the auto-indenting, paren-matching, and
syntax-based coloring:

@({
; Computes the nth fibonacci number (maybe?)
(definec fib (n :nat) :nat
  (match n
    ((:or 0 1) (+ (fib (1- n)) (fib (- n 2))))
    (& 1)))
})
</p>

<p>
Upon creating the new file, an <b>editor</b> has now opened in the
<b>editor area</b> of the <b>workbench</b>.
Around the editor area are <b>views</b>,
such as the <b>Project Explorer</b> view to the left and <b>Outline</b> view
to the right.  From their title areas, these can be dragged around, tiled,
minimized, etc.  You probably also noticed that <tt>(definec fib (n :nat) :nat</tt> showed up in
the Outline view, which you can use to navigate the top-level forms of your
file.
</p>

<p>
In the Project Explorer view, which is a tree view of projects and
files, expand your project to reveal a few files:
</p>
<ul>
<li><tt>.project</tt> - a file used by Eclipse to store project-specific
settings.</li>
<li><tt>test.lisp</tt> or whatever you called it.  This will contain ACL2
code your write.</li>
<li><tt>test.lisp.a2s</tt> - a file created automatically when you opened
<tt>test.lisp</tt>.  This file will store the history of ACL2 sessions
you open to develop <tt>test.lisp</tt>.</li>
</ul>

<p>
<b>Open <tt>test.lisp.a2s</tt></b> by double-clicking it in the
Project Explorer.  Alternatively, hit Ctrl+Shift+o
(Mac: <icon src=\"res/acl2s/mac-command.gif\" width=\"14\" height=\"13\"
alt=\"Command\"/>+Shift+o) in the editor for <tt>test.lisp</tt>.  This is
the key sequence for switching between corresponding .lisp and
.lisp.a2s editors, opening the other if necessary.  You should now be
in an editor that has a little message \"No session running\" at the top
and won't let you type anything.  This editor is read-only when no
session is running.
</p>

<h3>Go...</h3>
<p>
<b>Start a session</b> for testing our code in <tt>test.lisp</tt> by
clicking the
<icon src=\"res/acl2s/icons/acl2_restart.gif\" width=\"16\" height=\"16\" alt=\"restart session\"/>
icon in the toolbar.
</p>

<p>
ACL2 should start up, resulting in a .a2s file opening up and the \"<tt>ACL2S &gt;</tt>\" prompt
appearing after a few seconds.
</p>


<p>
<b>Type an \"immediate command\" for ACL2</b>, such as
@({(* 21 2)}) in the session editor (.a2s editor).  Notice
that the editor is read-only except for the part after the last prompt.
Hitting <b>Enter</b> (<b>Return</b>) at the end of this editor will submit
the typed
form to ACL2.  Actually, it will only submit <b>syntactically valid</b>
commands to ACL2, so if one tries to trick it by hitting <b>Enter</b>
after just @({(* 21}), the editor just goes to the next
line.
</p>

<p>
<b>Try submitting other types of input</b> to ACL2.
@({(* 21 2)}) was classified by the plugin as \"VALUE\"
input, because it's just computation that returns a value.  Another
example is a \"QUERY\" such as @({:pe strip-cars}), which
prints out information about the current history or \"world\", in this
case the definition of the function \"strip-cars\".
@({(definec successor (x :int) :int (1+ x))}) is an \"EVENT\" because it
(potentially) changes the history.
See @(see acl2s-command-classifications) for more detail.
For \"EVENT\" inputs, ACL2s pops up a
dialog asking what to do about the fact that we did something logically
relevant from the command line rather than from our source code.  Read
the dialog and for now choose \"Insert\".
</p>

<p>
<b>Try submitting something with an error</b> such as
@({(successor 1 2)}) This has an error because the arity of the <tt>successor</tt>
function we just defined is 1.  The red (maroon, I guess) output indicates
the command was not successful.  ACL2 is back in the state it was in before
you submitted the form that caused the error.
</p>

<h3>Line action</h3>

<p>
<b>Switch back to the .lisp editor</b> where you will discover the
@({(definec successor (x :int) :int (1+ x))}) form we submitted in the
session editor has been \"inserted\" above what we had typed previously!
Also, that form is \"above the line\" and read-only.  This is
part of the intrinsic linkage between <tt>somename.lisp</tt> and
<tt>somename.lisp.a2s</tt>: the forms \"above the line\" in the .lisp
editor are those used to get the ACL2 session in the .lisp.a2s editor
in its current state.  To maintain this invariant, we have to do one of
two things in the case of executing something history-relevant in the
session editor: insert it at the line in the lisp editor or undo it.
These are the options the \"Relevant input at command line\" dialog gave us.
Note that \"QUERY\"s and \"VALUE\"s do not modify the
history, so we don't need to insert those above the line.
</p>

<p>
<b>Try moving the line</b> past the definition we gave
for <tt>fib</tt> by pressing the \"advance todo\" button on the toolbar
(<icon src=\"res/acl2s/icons/advance.gif\" width=\"16\" height=\"16\"/> or
Ctrl+Shift+I on PC or
<icon src=\"res/acl2s/mac-command.gif\" width=\"14\" height=\"13\" alt=\"Command\"/>+Shift+I
on Mac).
Watch carefully and you will see the definition for <tt>fib</tt> flash green.
Because it did not turn from green to gray, our definition of <tt>fib</tt> was
rejected by ACL2.  Also, if the \"Proof Tree\" view is open (probably
left), it might show some information about a failed termination
proof that caused ACL2 to reject the definition.
</p>

<box>
<h4>More Details: Meaning of green and gray highlighting?</h4>

    <p> The plugin models two \"lines\" in a .lisp file: the \"completed
      line\" and the \"todo line\".  These \"lines\" are only visible as the
      boundary between regions with different highlighting.  The
      \"completed line\" is at the last point of gray (or blue)
      highlighting.  The \"todo line\" is at the last point of <b>any</b>
      highlighting: gray, blue or green.
    </p>

    <p> Above the \"completed line\" is the (potentially empty) \"completed
      region,\" which has forms that ACL2 has--get this--completed.
      Between the two lines are forms that we want ACL2 to work on
      completing (hence \"todo\").  This (potentially empty) region, the
      \"todo region\", has green highlighting.  We can call the rest of
      the buffer the \"working region\", which is the freely editable
      part.
    </p>
</box>


<p>So what was the meaning of the flash of green highlighting?
Clicking \"advance todo\" moved the \"todo line\" from between
<code>(definec successor ...)</code> and <code>(definec fib
...)</code>  to after <code>(definec fib ...)</code>.  With
at least one form in the \"todo region\", the session started processing
the first (and only) one.  If you look at the session output, you see
that the attempt to admit our @('fib') function failed.  The
attempt to prove termination failed.  If the next \"todo\" form fails,
the plugin moves the todo line back to the point of the completed
line, \"cancelling\" the todo operations and prompting the user to fix
the rejected form.
</p>

<p>
<b>Fix our @('fib') definition</b>: the previous one had
the bodies of the two match cases swapped.  ACL2 admits
this definition:
@({
; Computes the nth fibonacci number
(definec fib (n :nat) :nat
  (match n
    ((:or 0 1) 1)
    (& (+ (fib (1- n)) (fib (- n 2))))))
})

Now clicking \"advance todo\" should result in the definition flashing
green while it is in the todo region and turning gray after being
accepted.
</p>
")

(defxdoc acl2s-intro
  :parents (acl2::acl2-sedan)
  :short "A longer introduction to ACL2s"
  :long
  "
<p>
  The ACL2 Sedan theorem prover (<b>ACL2s</b>) is an Eclipse plug-in
  that provides a modern integrated development environment, supports
  several modes of interaction, provides a powerful termination
  analysis engine, includes a rich support for \"types\" and
  seamlessly integrates semi-automated bug-finding methods with
  interactive theorem proving.
</p>

  <h2>Introduction</h2>
  <p><see topic=\"@(url acl2::acl2)\">ACL2</see> is a powerful system for integrated
modeling, simulation, and inductive reasoning.  Under expert control,
it has been used to verify some of the most complex theorems to have
undergone mechanical verification.  In addition to its maturity and
stability, these qualifications make it a good platform for learning
about industrial-strength theorem proving.  Unfortunately, ACL2 has a
steep learning curve and with its traditional tool support is
analogous to a racecar: it is powerful, but it take expertise to
operate properly. </p>

<p> We want to make tool support for the ACL2 platform that is more
analogous to a family sedan; hence, the \"ACL2s\" or \"ACL2 Sedan\" name.
With just a little training, a new user should be able to drive slowly
on paved streets without worrying about oversteer, tire temperature,
or even engine RPMs.
</p>

<p>
Pushing aside the analogies, ACL2s includes powerful features that
provide users with more automation and support for specifying
conjectures and proving theorems. This includes <see topic=\"@(url acl2::ccg)\">
CCG termination analysis</see> and automated <see topic=\"@(url acl2::cgen)\">
Counterexample generation</see>. In addition, ACL2s is \"safer\" by constructing and
enforcing abstractions based on what is meaningful interaction with
ACL2. For example, unlike the traditional ACL2 development environment
(the command-line theorem prover and Emacs), pressing Return at the
command prompt in ACL2s does not send any input to ACL2 until a
single, well-formed input expression is completed.  Unlike Emacs,
ACL2s stops automatically sending input to ACL2 if something fails.
Undoing in ACL2s is simple and natural; in other ACL2 environments,
however, one has to figure out for oneself the command to undo to a
particular point, while watching for critical commands that evade the
traditional undo mechanism.
</p>

<p>
We have implemented our tool as a plugin for the Eclipse development
environment (see <i>What is Eclipse?</i> in the @(see acl2s-faq)).
In addition, the plugin requires some extra functionality from ACL2
that is not included in the main distribution.  This functionality is
largely hidden from the user and shouldn't alter ACL2's behavior for
all practical purposes.  To be sure, though, users can certify their
work in a clean ACL2 session.
</p>

<p>
ACL2s is not completely mature in its capabilities, but industrial and
academic users alike should find it stable enough, intuitive enough,
and capable enough to meet their needs.  Ideally, the tool will become
even more intuitive, self-teaching, etc.  in the future.
</p>

")


(defxdoc ACL2s-FAQ
  :parents (acl2::acl2-sedan)
  :short "Frequently Asked Questions"
  :long
  "
<div class=\"left-center\">
<h3>Eclipse-related</h3>

<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><b>What is Eclipse?</b></td> </tr>
<tr> <td>A:</td>
     <td>Eclipse is a highly modularized, extensible, free
development environment for a variety of programming languages.  See <a
href=\"http://www.eclipse.org\">www.eclipse.org</a>.  Eclipse is written
in Java and has an especially well developed development environment
for Java.</td></tr>
</table><br/>


<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><b>Where do I learn about all this Eclipse lingo?</b></td> </tr>
<tr> <td>A:</td>
     <td>See the <a href=\"http://help.eclipse.org/2022-06/topic/org.eclipse.platform.doc.user/gettingStarted/qs-02a.htm\">Basic
Tutorial section of the <b>Workbench User Guide</b></a>.
</td></tr>
</table><br/>



<table class=\"rounded striped\">
<tr> <td >Q:</td>
     <td><b>How do I tell what Java version Eclipse is running under, and if its 64bit?</b></td> </tr>
<tr> <td>A:</td>
     <td>Inside Eclipse, go to <b>Help</b> | <b>About Eclipse SDK</b> and
click \"Installation Details\".  Under \"Configuration\" tab are the \"eclipse.commands\"
property and the \"java.runtime.*\" properties, you will find the relevant information. 
You can also find out under \"-arch\" your machine architecture, for
example, \"X86_64\" will indicate that you are running a 64bit Eclipse. 
\"java.vm.name\" will tell you if the Java being used is a 64bit JVM.
</td></tr>
</table><br/>


<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><b>Where is Eclipse documentation?</b></td> </tr>
<tr> <td>A:</td>
     <td><a href=\"http://www.eclipse.org/documentation/main.html\">http://www.eclipse.org/documentation/main.html</a>
</td></tr>
</table><br/>


<table class=\"rounded striped\">
<tr> <td >Q:</td>
     <td><b> Can I do a multi-user install of Eclipse?</b></td> </tr>
<tr> <td >A:</td>
     <td><p>It is tricky to support a multi-user install of Eclipse.  The key
seems to be not running Eclipse at all in a way that would allow modification
of the files in that eclipse installation.  Once it has written some
configuration stuff to the installation directory, it bombs if you can't
write to that directory anymore.
</p><p>
This is why I discourage this unless you're truly in an environment that's
going to have many Eclipse users.  As awkward as it sounds, just install
Eclipse such that the user who will be running it can modify all of its
files, and life will be easier.
</p>
</td></tr>
</table>
</div>

<div class=\"left-center\">
  <h3>ACL2-related</h3>

<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><b>What is ACL2?</b></td> </tr>
<tr> <td>A:</td>
     <td>ACL2 is a programming language, logic, and theorem
prover/checker based on Common Lisp.  See <a
href=\"http://www.cs.utexas.edu/~moore/acl2/\">the ACL2 home page</a> for more
information.</td></tr>
</table>

<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><b>What is CAR?</b></td> </tr>
<tr> <td>A:</td>
     <td><u>CAR</u> is an abbreviation we sometimes use to refer to this
(print) book:
<blockquote>
<b>Computer-Aided Reasoning: An Approach</b>.<br/>
Matt Kaufmann, Panagiotis Manolios, and J Strother Moore.<br/>
Kluwer Academic Publishers, June, 2000. (ISBN 0-7923-7744-3)
</blockquote>
See <a href=\"http://www.cs.utexas.edu/users/moore/publications/acl2-books/car/index.html\">J
Moore's page about the book</a> for description and <b>affordable</b>
ordering information.
</td>
</tr>
</table>

<table class=\"rounded striped\">
<tr> <td >Q:</td>
     <td><b>What is an ACL2 book?</b></td> </tr>
<tr> <td >A:</td>
     <td>Basically, an ACL2 book is a bunch of ACL2 definitions (functions,
theorems, proof rules, etc.) that can be easily imported into other ACL2
work.  See @(see acl2::books) for more information.</td></tr>
</table><br/>

<table class=\"rounded striped\">
<tr> <td>Q:</td>
<td><b>Can I use my own version of ACL2? i.e. Finding ACL2 on user's system:</b></td>
</tr>
<tr> <td>A:</td>
<td>
<p>
This used to be a pain, but it's much simpler now.  First, we have a
preference in the Eclipse preferences (under <b>ACL2s</b> &gt; <b>ACL2</b>)
that allows one to specify the directory that contains your ACL2 image,
whether it's \"saved_acl2\", \"run_acl2\", or \"bin/acl2.exe\" under that
directory.
</p>
<p>

If you don't specify that preference, we check to
see if an \"ACL2 Image\" is installed in Eclipse, in which case we attempt
to use that.
</p>
<p>
Next we check the environment variable ACL2_HOME for the directory.
Next the java property acl2.home.  Then if none of those is fruitful,
we just try executing \"acl2\" and see what happens.
</p>
</td></tr>
</table>
</div>

<div class=\"left-center\">
<h3>Java-related</h3>

<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><b>Do I already have Java?  What version?</b></td> </tr>
<tr> <td>A:</td>
     <td>The simple answer is to type @({java -version}) at
your operating system's command prompt/terminal/shell.  You might
still have Java if the command is rejected.
</td></tr>
</table>


<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><b>Do I need the Java SDK or is the JRE fine?</b></td> </tr>
<tr> <td>A:</td>
     <td>The SDK is only needed if you plan on ever doing any Java
development. The (smaller) JRE should be opted if there is a
choice. It is recommended to have separate eclipse installations
(directories) for Java development and ACL2 development.
</td></tr>
</table><br/>


<table class=\"rounded striped\">
<tr> <td >Q:</td>
     <td><b>Can I use another version of Java?</b></td> </tr>
<tr> <td >A:</td>
     <td>The ACL2s Eclipse plugin uses Java constructs from Java 11.
You are likely to encounter problems if you use a Java runtime that is
older than Java 11.  We recommend the use of JRE 17 or 18.
</td></tr>
</table><br/>
</div>

<h3>ACL2s-related</h3>

<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><b>Why won't ACL2s let me do &lt;blah&gt; in a session?</b></td> </tr>
<tr> <td>A:</td>
     <td><p>In order for the plugin to follow what's going on in ACL2, we
must impose some small limitations.  One, for example, is that it will not let
you break into raw Lisp.  For those interested in this dangerous,
low-level form of interaction, however,
<see topic=\"@(url acl2::set-raw-mode)\">raw
mode</see> is supported (because it uses ACL2's reader).
</p><p>
Another subtle limitation is that--aside from
<see topic=\"@(url acl2::wormhole)\">wormholes</see>--@(see ld)
will only let you read from
<see topic=\"@(url acl2::standard-oi)\">*standard-oi*</see> at ld level 1.  The reason has to do with undoing and also @(see ld-error-action).  Another example is that
<tt>good-bye</tt> and other exit commands are disabled to the user,
to encourage use of the user interface operation \"Stop session\" instead.
</p><p>
For more details, see <b>How/what ACL2 functionality is
modified for ACL2s</b> in the @(see acl2s-implementation-notes).
</p>
</td></tr>
</table><br/>

<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><b>Can I use ACL2s extensions to ACL2 in an Emacs development environment?</b></td> </tr>
<tr> <td>A:</td>
     <td>

<p>Yes! One can reproduce inside Emacs, the theorem proving
     environment ACL2 Sedan provides (sans GUI) in the various session
     modes. To use just the CCG analysis and Counterexample generation
     features individually, see the next question. 
</p>
<p>
  You first need to identify where your ACL2 systems book directory is.
  You can do this by running @({(assoc :system (project-dir-alist (w state)))}) inside of an Eclipse ACL2s-mode session.
  The output of that command will start with @('(:system . ')) and will be followed by a path inside of a string.
  That path is your ACL2 system books directory, and we'll refer to it below as @('[books]').
</p>
    <ol>
    <li>Open a shell in emacs, start the ACL2 session: @({[books]../saved_acl2})</li>
    <li>In the ACL2 session, submit the following commands:
 @({
   (ld \"acl2s/acl2s-mode.lsp\" :dir :system)
   (reset-prehistory t)
   })
</li>
</ol>
<p>
If you want finer control on what gets loaded, you can selectively copy and paste the forms in @('[books]/acl2s/acl2s-mode.lsp') that
you need, in the emacs session. For example, say you want a session without trust tags, then except
for the @('(include-book \"ccg\" ...)') form, submit the rest of the events in <tt>acl2s-mode.lsp</tt>.
</p>
</td></tr>
</table>
<br/>


<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><b>Can I use CCG termination analysis and Counterexample
     generation in Emacs (ACL2 session)?</b></td> </tr>
<tr> <td>A:</td>
<td>
<p>To enable CCG termination analysis, submit the following two commands
  in your emacs ACL2 session.
@({
 (include-book \"acl2s/ccg/ccg\" :ttags ((:ccg)) :dir :system :load-compiled-file nil)
 (ld \"acl2s/ccg/ccg-settings.lsp\" :dir :system)
})
</p>
<p>To enable automated counterexample generation, submit the
  following two commands in your emacs ACL2 session.
@({
 (include-book \"acl2s/cgen/top\" :dir :system :ttags :all)
 (acl2s-defaults :set testing-enabled T)
})
</p>
</td></tr>
</table><br/>


<h3>Installation Issues</h3>
See @(see acl2s-installation-faq) as well as the corresponding @(see acl2s-installation) page for your operating system for more information.
")
 
(defxdoc acl2s-user-guide
  :parents (acl2::acl2-sedan)
  :short "ACL2 Sedan User Guide"
  :long
  "
<p>
This guide showcases the important parts of the ACL2 Sedan user
experience. We assume you already have a running ACL2s session; if not
check out the @(see acl2s-tutorial).  The ACL2 tutorial (@(see
acl2::acl2-tutorial)) is a fine place to learn about the ACL2
language, logic and theorem proving system. For in-depth documentation
about ACL2 itself refer to @(see acl2::acl2).
</p>

<div class=\"left-center\">
  <h2>Cheat Sheet</h2>
  A cheat sheet is available with a summary of key bindings and
  command types <a href=\"res/acl2s/sheet.pdf\">here</a>.
</div>

<div class=\"left-center\">
<h2>Customization</h2>
<h4>Workspace Layout</h4>
<p>
Getting your workspace laid out in a convenient way is important to using
ACL2s efficiently.  Here are some pointers:
</p>
<ul>
<li><b>Editor split</b>:  At this time, source code and sessions are in
editors--different editors.  To see both at one time, you need to split up
your editor area.  (Each workbench window has one rectangular \"editor area\"
in which all the open editors are tabbed and/or tiled.)  Click the title
area of an editor you would like to split away from the others and drag it
to any side of the others.  As you drag, a gray outline of the proposed
layout is shown.  Observe that you can also drag titles back together, and
you can relocate views around the editor area analogously.</li>
<li><b>Open, close, many, one</b>:  Through the \"Window\" menu, you can open
more than one workbench window, each of which has one rectangular editor area
and can have only one of any view open.  Also through the \"Window\" menu, you
can open another editor to the same file; all editors for the same file
keep their content in sync with each other.  Also through the \"Window\" menu,
you can reopen any views that may have accidentally been closed.</li>
<li><b>Fast views</b>:  If you don't want to dedicate long-term real estate
to views such as the Project Explorer, Outline, Proof Tree, and Console, you can
minimize them to make them available quickly.  If you click the icon for
the minimized view--rather than the restore icon--it pops up as a \"fast
view\" which is minimized again after you click outside it.
</li>
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
<b>General</b> | <b>Appearance</b> | <b>Colors and Fonts</b>.  Under \"Basic,\"
the \"Text Font\" is that used by the ACL2s editors.  Click \"Change...\" to
change it.</li>
<li><b>Editor colors</b>: To make the editor text darker in general,
go in the preferences dialog to <b>General</b> | <b>Appearance</b>
and select the \"Current theme\" \"High Contrast (ACL2s)\".  This is good for
use on a projector, for example.  To manipulate the colors in detail,
go to <b>Colors and Fonts</b> and open the ACL2s group.  <i>Note:
You will have to close and re-open editors for these color changes to
take effect.</i></li>
</ul>
<h4>Session</h4>
<p>
If you want to add some configuration input to be loaded with each interactive
session, use an
<see topic=\"@(url acl2::acl2-customization)\">acl2-customization file</see>.
This can include your own configuration to be done after the session mode is
loaded and configured.  This should not include events, which should be
specified or explicitly loaded in the source code.  In fact, we do not load
the acl2-customization for certification.  Also note that ACL2s does not
respect the environment variable for acl2-customization.  Also note that
acl2-customization is only loaded in some modes (see below), unless
overridden in the preferences.
</p>
</div>

<div class=\"left-center\" data-target=\"guide_modes\">
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
@({
========================================================================
Executing /home/peterd/acl2s.exe
Starting ACL2 in mode \"ACL2s\"
})

<h4>Standard modes</h4>
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
This mode is full-featured and places no restrictions on the theorem prover.
</p><p>
This is the recommended mode for a standard ACL2s user.
</p>
</td></tr>
<tr><td><b>Compatible</b></td><td>
<p>
In this mode, ACL2 is almost indistinguishable from what you would get
from executing it directly.  This mode is recommended for those
developing definitions and theorems to be used by ACL2 outside of ACL2s.
</p>
<p>
Admissibility in this mode, however, does not *guarantee* admissibility
in ACL2 proper (and vice-versa).  For more details, see
the <b>How/what ACL2 functionality is modified for ACLs</b> section of the @(see acl2s-implementation-notes).
</p>
</td></tr>
</tbody>
</table>

<p><b>Additional advanced note:</b>
Another feature of all these modes except \"Compatible\" is doing destructor
elimination before laying down a checkpoint.  Thus, the checkpoint summary
will show the formula after destructor elimination.  The downside is that the
variable names may appear cryptic and unfamiliar, but the upside is that
you get some generalization for free, usually resulting in smaller formulas.
</p><p>
Notes about how these modes are implemented are described in the <b>How modes are implemented</b> section of the @(see acl2s-implementation-notes).
</p>
</div>

<div class=\"left-center\">
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
<icon src=\"res/acl2s/mac-command.gif\" width=\"14\" height=\"13\" alt=\"Command\"/>+Shift.  For
example, <b>Interrupt</b> is still Ctrl+Break (if you have a Break key), but
switching editors is
<icon src=\"res/acl2s/mac-command.gif\" width=\"14\" height=\"13\" alt=\"Command\"/>+Shift+o.
</p>

<table>
  <thead>
    <tr>
      <th>UI Action</th>
      <th>Icon</th>
      <th>Description</th></tr>
  </thead>

  <tbody>
<tr><td><b class=\"warning label\">Navigation</b></td><td></td><td>(appear under \"Navigate\" menu)</td></tr>
<tr><td>
\"Go To\" | \"Corresponding ...\"
</td><td>
</td><td>
This switches which editor has keyboard focus.  If you are in a .lisp file,
it switches to the corresponding .a2s editor, opening it if necessary.
Vice-versa if starting from an .a2s editor.  The keyboard shortcut is
Ctrl+Shift+o (since it is related to emacs' C-x o).
</td></tr>
<tr><td>
\"Go To\" | \"Matching Character\"
</td><td>
</td><td>
If the character behind the caret (cursor) is matched to another (such as
<u><color rgb=\"red\">(</color></u> and <u><color rgb=\"red\">)</color></u>,
or <u><color rgb=\"red\">\"</color></u> and <u><color rgb=\"red\">\"</color></u>),
then this action moves the cursor just beyond the match.  Invoking this action
twice in a row should have no net effect <b>except</b> in the case of
going from a <u><color rgb=\"red\">,</color></u> to its matching
<u><color rgb=\"red\">`</color></u>, which could potentially have many commas
matching to it.  The keyboard shortcut is
Ctrl+Shift+P (as in Eclipse's Java Development Environment).
</td></tr>
<tr><td>
\"Down/Up to Next/Previous Session Input\" (.a2s only)
</td><td>
</td><td>
These allow the user to navigate through the session history by moving to the
beginning of the next/previous command in the history.  If, for example, one
is at the bottom of a failed proof attempt, one can navigate to the beginning
of the command that initiated it with Ctrl+Shift+Up.  \"Next\" is bound to
Ctrl+Shift+Down.  One can go to the end of any buffer with Ctrl+End (Eclipse
binding).
</td></tr>
<tr><td>
\"Down/Up to Next/Previous Checkpoint/Input\" (.a2s only)
</td><td>
</td><td>
<p>
These grant the user finer-grained navigation through the session history
than the above by also visiting checkpoints in proof attempts.  For a
description of checkpoints, see @(see acl2::the-method).
</p><p>
\"Next\" is bound to Ctrl+Shift+Right and \"Previous\" is bound to Ctrl+Shift+Left.
Thus, to go to the first checkpoint of the previous form's output, type
Ctrl+Shift+Up, Ctrl+Shift+Right.
</p>
</td></tr>
<tr><td>
\"Next/Previous/Last Command in History\" (.a2s only)
</td><td>
</td><td>
The .a2s editor keeps a history of acl2 forms that have been submitted as
\"immediates\" (typed in the .a2s editor).  One can navigate through this
history in much the same way one can navigate through a shell history, or a
history of ACL2 commands (assuming <b>readline</b> support).  Previous:
Ctrl+Shift+, (comma);  Next: Ctrl+Shift+. (period);  Last/Current: Ctrl+Shift+/
(slash).
<p>
Actually, two orthogonal histories are maintained.  One for immediates
submitted as command forms and one for miscellaneous input, such as input to
the proof checker.  The command history for each is available only when the
session has prompted for that type of input.
</p>
</td></tr>
<tr><td><b class=\"warning label\">Session-related</b></td><td></td></tr>
<tr><td>
Submit Immediate
</td><td>
</td><td>
When ACL2 is running and waiting for input, one can type input forms directly
into the .a2s buffer.  We call these \"immediates.\"  Whenever <b>Enter</b>
(sometimes called <b>Return</b>) is typed at the end of the .a2s buffer,
we check to see
if some prefix of the typed input is a valid, complete input form.  If so,
the <b>Enter</b> is interpreted as submitting the form.  If not, the
<b>Enter</b> is inserted, as in a traditional editor.  <b>Ctrl+Enter</b>
ignores the location of the caret and will submit the first complete, valid
input form if there is one.
<p>
If the form submitted is relevant to the logical history, (i.e. not a
QUERY or VALUE), the user will be queried on whether to insert it at the
\"completed\" line point in the corresponding .lisp file or to immediately
undo it.  This is to maintain the invariant that the forms
above the \"completed\" line in the .lisp file comprise the logical history of
the session.
</p>
</td></tr>
<tr><td>
\"Clean Session\"
</td><td>
<icon src=\"res/acl2s/icons/acl2_clean.gif\" width=\"16\" height=\"16\"/>
</td><td>
Opens a dialog box with options to clear the session history, the typed
command history, and others.  Clearing the session history will stop the
associated ACL2 session (if running) and move the \"completed\" line in the
corresponding Lisp file to the top.  Forgetting REDO information is useful
for including updated versions of the same book.
Note that some of these actions are not readily reversible, if at all,
so use them cautiously.  Shortcut: Alt+Delete.
</td></tr>
<tr><td>
\"(Re)start Session\"
</td><td>
<icon src=\"res/acl2s/icons/acl2_restart.gif\" width=\"16\" height=\"16\"/>
</td><td>
<p>
Starts a fresh, new ACL2 session, with its output going to the current or
corresponding .a2s editor.  If an ACL2 session was already running in that
editor, it is stopped/killed.  Depending on user preferences, the dump of
previous sessions may or may not be cleared. Shortcut: Alt+Home.
</p><p>
In the corresponding Lisp file, the \"completed\" line is moved to the top.
The \"todo\" line is left where it is, meaning forms that were done or still
left \"todo\" in a previous session will start being read and loaded
automatically.  To avoid this, use \"Stop session\" (optional, but takes ACL2
interaction out of the operation) and \"Undo/cancel all forms\" before
\"(Re)start Session\".
</p>
</td></tr>
<tr><td>
\"Stop Session\"
</td><td>
<icon src=\"res/acl2s/icons/acl2_stop.gif\" width=\"16\" height=\"16\"/>
</td><td>
<p>
If ACL2 is running in this (or the corresponding) .a2s editor, stop it cleanly
or kill it.  Regardless of the state it was in before, ACL2 is *not* running
in this editor after \"Stop Session\" is pressed.  Shortcut: Alt+End
</p><p>
In the corresponding Lisp file, the completed line is reset and the todo line
is left where it is.
</p>
</td></tr>
<tr><td>
\"Interrupt Session\"
</td><td>
<icon src=\"res/acl2s/icons/acl2_interrupt.gif\" width=\"16\" height=\"16\"/>
</td><td>
<p>
If ACL2 is processing a command form, this will break it back out to the
top-level prompt.  This is most commonly used to interrupt the execution of
some evaluation that will take too long, or to abort what seems to be a
divergent proof attempt.  As a nod to times passed, we bind this to Ctrl+Break.
</p><p>
\"Interrupt Session\" often has the same effect as \"Cancel all
'todo' forms,\" because if the form being processed by ACL2 is the next
\"todo\" form, either action will both interrupt ACL2 and (because an
interrupted form is not successful) move the \"todo\" line back to the \"done\"
line.
</p>
</td></tr>
<tr><td> <b class=\"warning label\">Line-related</b></td><td></td><td></td></tr>
<tr><td>
\"Undo/cancel all forms\"
</td><td>
<icon src=\"res/acl2s/icons/clean.gif\" width=\"16\" height=\"16\"/>
</td><td>
<p>
This moves both the \"completed\" line and the \"todo\" line to the top of the
.lisp file.  ACL2 need not be running, but if it is, this will cause
anything currently executing to be interrupted, and all completed forms
to be undone in LIFO (last-in, first-out) order.  (No default shortcut)
</p><p>
The large double arrows in the icon are intended to portray moving the line
all the way to the top.
</p>
</td></tr>
<tr><td>
\"Undo/cancel last form\"
</td><td>
<icon src=\"res/acl2s/icons/retreat.gif\" width=\"16\" height=\"16\"/>
</td><td>
<p>
If there are any \"todo\" forms, the last will be cancelled.  If it was
currently being executed by ACL2, it will be interrupted.
If there were no \"todo\" forms, both lines will be moved up one form, and if
that form was relevant to the logical history, it will be undone in the
ACL2 session.  ACL2 need not be running to use this action.
Shortcut: Ctrl+Shift+M
</p><p>
The small arrow in the icon is intended to indicate the undoing of a
single form.
</p>
</td></tr>
<tr><td>
\"Cancel all \"todo\" forms\"
</td><td>
<icon src=\"res/acl2s/icons/cancel.gif\" width=\"16\" height=\"16\"/>
</td><td>
<p>
The \"todo\" line is moved to be even with the \"completed\" line.  If the next
\"todo\" form was being processed by ACL2, it is interrupted.
(No default shortcut)
</p><p>
The large arrow next to green text in the icon is intended to indicate the
undoing of all \"todo\" forms.
</p>
</td></tr>
<tr><td>
\"Advance todo line\"
</td><td>
<icon src=\"res/acl2s/icons/advance.gif\" width=\"16\" height=\"16\"/>
</td><td>
<p>
The \"todo\" line is advanced by one command form.  This will often cause ACL2 to
start processing \"todo\" forms.  Many forms are completed by ACL2 so quickly,
that there is but a flicker before the \"completed\" line is moved as well.
ACL2 need not be running to use this action, but it won't trigger ACL2 to
start.  Shortcut: Ctrl+Shift+I
</p><p>
The small down arrow in the icon is intended to indicate the advancement of
the line by a single form.
</p>
</td></tr>
<tr><td>
\"Move todo up/down past cursor\" (.lisp only)
</td><td>
<icon src=\"res/acl2s/icons/move.gif\" width=\"16\" height=\"16\"/>
</td><td>
<p>
If the \"todo\" line is above the cursor, it is advanced until it reaches
(or passes) the cursor.  If the \"todo\" line is below the cursor, it is
retreated until it passes the cursor.  Note that invoking this action
repeatedly in the same spot will have a sort of \"toggle\" action on the
form under or immediately after the cursor. Shortcut: Ctrl+Shift+Enter
</p><p>
The up and down arrows in the icon are intended to indicate moving the line
in either direction to get to the current spot.
</p><p>
<b>This is the only line action valid in \"No Line\" mode</b>, in which it has
a special (but obvious) meaning:  it submits the command form under or
following the cursor to the associated session (if exists, running, and ready)
and advances the cursor past the submitted form.
</p>
</td></tr>

<tr><td> <b class=\"warning label\">Misc.</b></td><td></td><td></td></tr>

<tr><td>
Indent code
</td><td></td><td>
<p>
In either the .lisp editor or the immediate area of the .a2s editor, the
Tab key indents lines spanned by the current selection (or just the line
containing the caret) according to some built-in rules.  Not all lines
will have their indention changed by this operation, such as lines whose
first non-whitespace characters are \";;;\".
</p>
</td></tr>

<tr><td>
Select s-exp
</td><td></td><td>
<p>
In either the .lisp editor or the immediate area of the .a2s editor,
Ctrl+Shift+Space selects (highlights) s-expressions, to help with cutting
and pasting mostly.  If nothing is highlighted, the smallest s-exp \"under\"
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
<icon src=\"res/acl2s/icons/acl2_book.gif\" width=\"16\" height=\"16\"/>
</td><td>
<p>
This will use <see topic=\"@(url build::cert.pl)\">cert.pl</see> to <i>certify</i> the current book so that it can be quickly <see topic=\"@(url acl2::include-book)\">included</see> from another file. See @(see acl2::certificate) for more information. Shortcut: Alt+C
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

<div class=\"left-center\" data-target=\"guide_ccg\">
<h2>CCG termination analysis</h2>
<h4>Background</h4>
<p>
The \"ACL2s,\" session mode
includes
improved termination analysis for ACL2 based on research by Pete Manolios
and Daron Vroon.  The analysis is based on \"context calling graphs,\" so
we refer to it as CCG termination analysis for short.
</p>
<p>

Beginners can think of CCG termination analysis of as a black-box
analysis.  We say \"black-box\" because beginning users need not
concern themselves with the details of how CCG analysis works.
Of course, any termination analysis is necessarily incomplete and
eventually users may come across terminating functions that CCG
analysis cannot prove terminating.  When that happens, CCG
analysis will construct a function that is as simple as possible,
includes a subset of the looping behavior of the submitted
function, and which CCG analysis cannot prove terminating. This
function, along with several suggestions of how to help CCG
analysis prove termination, will be presented to the user.
</p>
<h4>Settings</h4>
<p>
CCG is configured by calling
<b><tt>set-termination-method</tt></b> with a single parameter,
which must be one of these:
</p>
<ul>
<li><b><tt>:ccg</tt></b> - CCG analysis only (no measure-based proof
attempt)</li>
<li><b><tt>:measure</tt></b> - no CCG analysis (measure-based proofs
only)</li>
</ul>
<p>
Regardless of this or other settings, ACL2's built-in
method will be used if an explicit measure is specified.
</p><p>
For advanced debugging purposes, <tt>:set-ccg-verbose t</tt> causes the
analysis to show what it is doing.  This generates <b>lots</b> of
output, however.
</p><p>
Finally, \"Compatible\" mode does not include CCG, and \"Programming\" mode
does not need CCG.  CCG is independent of the rest of ACL2s in the sense
that it is implemented as an ACL2 book in the acl2s-modes plugin.
</p>

<h4>More Documentation</h4>
<p>
Our CCG termination analysis is highly customizable and includes
many features not mentioned here. For detailed documentation
please refer to @(see acl2::ccg).
</p>
</div>

<div class=\"left-center\" data-target=\"guide_datadef\">
<h2>Data Definitions</h2>
<h4>Background</h4>
<p>
Data definitions are an essential part of crafting programs and
modeling systems. Whereas most programming languages provide rich
mechanisms for defining datatypes, ACL2 only really provides a
limited collection of built-in types and @('cons').
</p>

<p>
This state of affairs presented us with a challenge when we started
teaching undergraduates how to model, specify and reason about
computation, because even freshmen students have a type-centric view
of the world.
</p>

<p>
We introduced the <b>defdata</b> framework in ACL2s
in order to provide a convenient, intuitive way to specify data
definitions.  A version of @('defdata') has appeared in ACL2s
since at least August 2009 (in version 0.9.7), and we have been
extending and improving it since then.
</p>


<h4>Documentation</h4>
<p>
See @(see acl2::defdata) for defdata's documentation. In particular,
a readable and example-oriented description of defdata framework appears
in the ACL2 2014 Workshop paper linked at the bottom of that topic.
</p>
</div>

<div class=\"left-center\" data-target=\"guide_RT\">
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
<a href=\"http://arxiv.org/pdf/1105.4394v2.pdf\">Integrating Testing and Interactive Theorem Proving</a>
goes into the details of this feature, but is a very easy read. The reader is encouraged to go through it.
</p>
<p>
All modes except \"Compatible\" have testing enabled by default.
</p>

<h4>Documentation</h4>
<p>
See @(see acl2::test?) and @(see acl2::cgen) for more documentation.
</p>

</div>
")

(defxdoc acl2s-command-classifications
  :parents (acl2s-user-guide)
  :short "Description of classifications for commands in ACL2s"
  :long
  "
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
These correspond to ACL2 <see topic=\"@(url acl2::embedded-event-form)\">embedded event forms</see>,
which are those forms that can appear in <see topic=\"@(url acl2::books)\">ACL2 books</see>.
Calls to <tt>defun</tt>, <tt>defmacro</tt>, and <tt>defthm</tt> are examples
of embedded event forms and <b>EVENT</b>s.
</td></tr>
<tr><td valign=\"top\"><b>VALUE</b></td><td>
Such forms are simple computations which return a value when (and if)
they terminate.
No <b>VALUE</b> form can alter ACL2's state and, therefore, never
affects undoing or redoing.
<br/><br/>
A precise definition is that if ACL2 permits <tt>(cons </tt>
<b>&lt;form&gt;</b> <tt>nil)</tt>, then <b>&lt;form&gt;</b> is a <b>VALUE</b>.
<br/><br/>
<b>Advanced Note</b>: some <b>VALUE</b> forms
have transient side effects, but they have no logical consequence (e.g.
<see topic=\"@(url acl2::cw)\">CW</see>
and
<see topic=\"@(url acl2::wormhole)\">WORMHOLE</see>).
</td></tr>
<tr><td valign=\"top\"><b>QUERY</b></td><td>
These are calls to some built-in ACL2 functions that report information about
the current state but are known not to modify state.  Examples include
@('(pe 'append)')
and
@('(pbt 0)').
</td></tr>
<tr><td valign=\"top\"><b>UNDO</b><br/>(internal initiation only)</td><td>
Various UI actions which have to do with \"undoing\" or \"moving the line up\"
can initiate the execution of an <b>UNDO</b> in the session.  An ordinary
user need not concern him/herself with how this works
(See <b>How undo and redo are implemented</b> in the <see topic=\"@(url acl2s-implementation-notes)\">ACL2s implementation notes</see>),
but should keep in mind that <b>UNDO</b>ing an <b>ACTION</b> or <b>RAW</b>
form may not have the desired effect.
</td></tr>
<tr><td valign=\"top\"><b>REDO</b><br/>(internal initiation only)</td><td>
This is the counterpart of <b>UNDO</b>.  It is used when resubmitting
something with the same abstract syntax and in the same environment as
something that was previously undone.
<br/><br/>
<b>REDO</b> enables one to (for example) edit comments above the line, by
retreating the line far enough to edit what one wants to change, and then
moving the \"todo\" line back to where it was.  If only comments were
changed, the session will accept the forms as <b>REDO</b>s, which happen
almost instantaneously.
</td></tr>
<tr><td valign=\"top\"><b>BAD</b></td><td>
If the input is a parseable ACL2 object but is an ill-formed expression
according to the current history, we call it \"BAD\" input.  Examples of
violations that would cause input to be statically ill-formed are:
<ul>
<li>wrong number of parameters to a function/macro</li>
<li>use of an undefined function/macro</li>
<li>first element of an invocation list is not a symbol or lambda expression</li>
<li>mismatch between expected and actual @('mv') shape</li>
</ul>
</td></tr>
<tr><td valign=\"top\"><b>COMMAND</b></td><td>
There are many forms that are illegal in books but we are able to undo the
effect of.  If we recognize a form as such, we call it a <b>COMMAND</b>--
except for special case <b>IN-PACKAGE</b>.  The
best example of a command is \"<tt>:set-guard-checking :none</tt>\".
</td></tr>
<tr><td valign=\"top\"><b>ACTION</b><br/>
<color rgb=\"red\">(potentially dangerous!)</color></td><td>
This is the \"catch-all\" categorization for forms that may have effects
that we don't know how to properly undo or might even break or hang the
ACL2 session.  Users who use
<see topic=\"@(url acl2::stobj)\">STOBJs</see>
or other
<see topic=\"@(url acl2::state)\">STATE</see>
beyond the logical
<see topic=\"@(url acl2::acl2)\">WORLD</see>
will need to use <b>ACTION</b>s heavily, but these are advanced uses of ACL2.
</td></tr>
<tr><td valign=\"top\"><b>EVENT/VALUE</b></td><td>
These are a special type of
<see topic=\"@(url acl2::embedded-event-form)\">embedded event form</see>
(<tt>value-triple</tt>s) that have no logical consequence--except that they
could halt progress by generating a hard lisp error.
</td></tr>
<tr><td valign=\"top\"><b>RAW</b><br/>
<color rgb=\"red\">(potentially very dangerous!)</color></td><td>
Most users of ACL2 are familiar with breaking into \"raw lisp\" by typing
\":q\" at the top-level prompt.  This is not supported in our plugin, but
<see topic=\"@(url acl2::set-raw-mode)\">
\"raw mode\"</see> is supported.  Most forms submitted under this mode are
classified as <b>RAW</b> because they have no well-defined meaning from the
ACL2 view of things.  With raw mode, the user can easily break many things,
and it's only supported for the benefit of <b>experts</b>.
</td></tr>
</tbody>
</table>
")

(defxdoc acl2s-implementation-notes
  :parents (acl2::acl2-sedan)
  :short "Some details regarding how ACL2s is implemented"
  :long
  "
<h2>WARNING</h2>
<color rgb=\"red\">
Note that much of the information here is not up-to-date with the current implementation of ACL2s.
</color>
We're in the process of going through this documentation and updating it, but we haven't finished updating
this file yet.
<h2>Wrapping the ACL2 process</h2>
<p>
  To support interruption of the ACL2 process, we need more
  information/functionality than Java provides through its
  @('java.lang.Process') API.  Roughly, we execute ACL2 in a wrapper
  that outputs as its first line of text an ID number that can be used
  to interrupt the process.  All output after that is that of ACL2.
  The plugin captures that ID number and uses it when needed.
</p>
<p>
  <b>On Unix variants</b> (Linux, Mac OS X), the wrapper for an invocation of
  @('acl2') would look like this (4 arguments, each underlined):
</p>
<blockquote>
  <code><u>sh</u> <u>-c</u> <u>echo \"$$\"; exec \"$0\" \"$@\"</u> <u>acl2</u></code>
</blockquote>
<p>
  Basically, this uses the standard Bourne shell to echo its process
  id and then execs (keeping the same pid) acl2--or any other command
  used there.  To interrupt or terminate acl2 (respectively), we
  execute one of these:
</p>
<blockquote>
  <code><u>kill</u> <u>-INT</u> <u><i>pid</i></u></code>
  <code><u>kill</u> <u>-TERM</u> <u><i>pid</i></u></code>
</blockquote>
<p>
  <b>On Windows machines</b>, things are not this easy.  We use a
  wrapper called <tt>hiddencon</tt>(<tt>.exe</tt>) that opens a new
  console, immediately hides it (flicker; sorry), outputs an id
  number, and executes a program \"attached\" to that console.  Then
  we can invoke <tt>sendctrlc</tt>(<tt>.exe</tt>) with that id to
  asynchronously deliver a \"Ctrl+C\" equivalent to that console,
  interrupting the program.  <tt>sendbreak</tt>(<tt>.exe</tt>)
  likewise sends a \"Ctrl+Break\" equivalent, which causes the program
  to terminate.
</p>
<p>
  These auxillary programs (hiddencon, sendctrlc, sendbreak) are included
  with the ACL2s plugin, so there's nothing extra to install.  It's a bit of
  a mess, but it seems to work reliably these days.
</p>
<p>
  Some wacky details of hiddencon.exe:<br/> The stdin and stdout of
  the program are inherited from the wrapper--not connected to the
  console, so one might wonder what the console is for.  The answer:
  Windows has no \"interrupt\" signal.  When one types \"Ctrl+C\" in a
  console, the console takes care of notifying the process in some
  weird way.  Windows has a mechanism for programmatically initiating
  a \"Ctrl+C\" equivalent, but its really only practical from a
  process that is \"attached\" to that console.  With this in mind,
  the job of the wrapper is to enable any other process to initiate an
  \"interrupt\" on the console it created.  The wrapper has a thread
  that reads and processes events from its Windows event queue, and
  one type of event, which could be initiated by anyone who knows the
  thread id of that wrapper thread, causes the wrapper to send an
  \"interruption\" to the hidden console.
</p>

<h2>Hooks: How/what ACL2 functionality is modified for ACL2s</h2>
<blockquote>
  <i>Here I discuss the stuff that is common to all modes, including
  \"Compatible\" mode.  See the @(see acl2s-user-guide) section on modes
  and \"How modes are implemented\" below.</i>
</blockquote>
<p>
  To support the kind of interaction ACL2s provides requires lots of
  cooperation and metadata from ACL2.  Thus when we run ACL2 for an
  interactive session, we install some changes that disallow some
  things (see <b>Why won't ACL2s let me do &lt;blah&gt; in a
  session?</b> in the @(see acl2s-faq)), spit out metadata for some
  things, and provide some system-level extensions in functionality.
  All of these ACL2 modifications are implemented via books
  distributed with ACL2 (@('[books]/acl2s/distribution/acl2s-hooks')).
</p>
<ul>
  <li><b>preinit.lsp</b> - disables raw Lisp debugger, which must be
  disabled because we can't tell for sure when/what kind of input it
  is expecting.  This file often includes other version-specific
  tweaks and fixes.  (This file is loaded by raw Lisp.)</li>
  <li><b>acl2s.lisp</b> - the main \"hooks\" book, which includes the
  \"hacking\" books now distributed with ACL2 and the rest of the
  books listed below.</li>
  <li><b>canonical-print.lisp</b> - functions for printing
  things... in a canonical way! (for reading by the acl2s plugin)</li>
  <li><b>categorize-input.lisp</b> - functions for (you guessed it...)
  categorizing inputs to ACL2.  Note that categorizing inputs is an
  example of the plugin executing commands in ACL2 that are unseen to
  the user.</li>
  <li><b>super-history.lisp</b> - implements the \"super-history\"
  mechanism of UNDOing and REDOing.  See \"How undo and redo are
  implemented\" below.</li>
  <li><b>protection-hooks.lisp</b> - implements a protection mechanism
  by which only those with knowledge of a secret number (the plugin)
  can invoke certain actions, such as UNDOing, REDOing, quitting, or
  breaking into raw Lisp.  Only a hash of the secret number is stored
  in the ACL2 runtime.  You could defeat the protection with your own
  trust tag, but I challenge you defeat it without using trust
  tags!</li>
  <li><b>interaction-hooks.lisp</b> - this redefines internal ACL2
  functions to provide metadata output that is sucked up (hidden) by
  the plugin and used to inform it about interaction.  Most
  importantly, extra environment information is sent with the prompt,
  a special marker is sent in the case of a form being successful, and
  a special marker is sent whenever ACL2 is about to read another
  object from *standard-oi*.  The plugin is now also given all of the
  package definitions so that they can be used in determining whether
  abstract syntax is the same in checking whether REDO is
  allowed.</li>
  <li><b>markup-hooks.lisp</b> - the markups in this book are not
  critical to intelligent interaction with ACL2, but add some extra
  helpful info, such as the position of checkpoints in the output.
  Along these lines, somewhere in startup stuff we remove destructor
  elimination as a checkpoint-causing processor, since destructor
  elimination cannot reduce theorems to non-theorems (confirmed by
  Matt Kaufmann).</li>
</ul>
<p>
  After these are included at startup, @(see acl2::reset-prehistory)
  is used to suggest to newbies that ACL2 is starting fresh, but
  @('(strip-cars (global-val 'known-package-alist (w state)))') should
  reveal the \"ACL2S\" package is defined, and @(':ttags-seen')
  accurately suggests how severely spoiled your session is.
</p>
<p>
  A consequence of including the standard hacking books for this code
  is that if you want to include them in your code in ACL2s, it will
  appear redundant during interactive development but is needed for
  certification as a book, for which none of the above are
  required/included.
</p>
<p>
  If you run into a case in which you really need to do something
  differently between interactive development and certification (like
  when I'm doing interactive development on the hooks books--my head
  hurts!), you can use the feature-based reader macros
  <tt>#+acl2s</tt> and <tt>#-acl2s</tt>.  <tt>:acl2s</tt> is added to
  *features* for interactive development only.  Please don't abuse. ;)
</p>

<h2>How undo and redo are implemented</h2>
<p>
  The <b>super-history</b> book of the acl2s_hooks plugin implements a
  stack of old \"states\".  Actually there are two stacks: an undo
  stack and a redo stack.  An undo pops the undo stack, pushes that
  \"state\" onto the redo stack, and then installs the \"state\" on
  the top of the undo stack.  A redo pops the redo stack, pushes that
  \"state\" onto the undo stack, and installs it as current.  Any
  other \"state\"-changing form empties the redo stack, and the
  resulting \"state\" is pushed onto the undo stack.
</p>
<p>
  Now I've put \"state\" in quotes and not called it \"the world\"
  because this notion of state is not that same as ACL2's <see
  topic=\"@(url acl2::state)\">state stobj</see> and is more than just
  ACL2's <see topic=\"@(url acl2::acl2)\">WORLD</see>.  Our
  super-history states are the world and a bunch of state-global
  variables that store things like the current package, guard-checking
  setting, and other things that affect whether things might pass or
  fail, and what they mean.  The complete list is
  @('ACL2S::*SETTINGS-GLOBALS*') in the <b>categorize-input</b> book
  of the acl2s_hooks.  This is similar to--but not exactly--what is
  saved and restored by <see topic=\"@(url acl2::make-event)\">make-event
  </see> (Our undo/redo mechanism predates the release of make-event.)
</p>

<h2>How modes are implemented</h2>
<p>
  Since version 0.9.0, ACL2s' session modes other than \"Compatible\"
  come from an independent plugin, acl2s_modes.  (Note that all three
  plugins \"acl2s,\" \"acl2s_hooks,\" and \"acl2s_modes\" are
  installed with the <i>feature</i> \"acl2s.\") Thus, third party
  Eclipse plugins can also add their own session modes to ACL2s.  To
  do so, they must extend the \"acl2s.modedir\" extension point, like
  in the plugin.xml for <a href=\"bobs_mode.jar\">an example \"Bob's
  mode\"</a>:
</p>
<blockquote>
@({
<?xml version=\"1.0\" encoding=\"UTF-8\"?>
<?eclipse version=\"3.2\"?>
<plugin>
   <extension point=\"acl2s.modedir\">
      <include-book-dir-entry keyword=\":bobs-mode\"/>
      <dependency keyword=\":acl2s-modes\"/>
      <mode
            name=\"Bob&apos;s Mode\"
            short_desc=\"Favorite mode of some hypothetical person named Bob\"
            long_desc=\"this is an optional long description\"
            book_dev=\"true\"
            extra_imports=\"(defun-bob defmacro-bob)\"
            init_file=\"bobs-mode.lsp\"
            precedence=\"50\"
            ttags=\"((:ccg))\">
      </mode>
      <certify-order-element book=\"defun-bob\"/>
      <certify-order-element book=\"defmacro-bob\"/>
   </extension>
</plugin>
})
</blockquote>
<p>
  The plugin is a JAR file with such a plugin.xml file, a proper
  manifest file, and any books and supporting files needed for the
  mode.
</p>
<p>
  All of the components shown above are optional, and all but the
  <tt>include-book-dir-entry</tt> can have multiple instances.  ACL2
  will be given the root install directory of the plugin with
  add-include-book-dir and the keyword in
  <tt>include-book-dir-entry</tt>.  In fact, ACL2s will create a
  \"dir.lsp\" file with that form whenever the plugin is used.
  Specifying an <tt>include-book-dir-entry</tt> is required if the
  initialization of any modes need to refer to that directory for
  including books.  (The current directory will <i>not</i> be set to
  the plugin directory.)
</p>
<p>
  Each include-book keyword directory used in your mode initialization
  (other than yourself and <tt>:system</tt>) should be listed as a
  <tt>dependency</tt>.  Bob's mode uses \"ccg\" from
  <tt>:acl2s-modes</tt>.
</p>
<p>
  Technically, only the name and short_desc are required for a mode.
  The non-obvious parts:
</p>
<ul>
  <li><tt>book_dev</tt> - whether book development/certification
  should be allowed in this mode (default true)</li>
  <li><tt>extra_imports</tt> - any extra symbols that are suggested to
  be imported into packages defined under this mode, aside from the
  ACL2 standard set</li>
  <li><tt>init_file</tt> - the file with the forms to execute at
  startup to initialize the mode.  These should not refer to the
  current directory (instead use :dir :whatever).  If
  <tt>book_dev</tt> is true, the forms should follow the guidelines
  for a .acl2 file, or commands that are okay prior to @(see
  acl2::certify-book).  We recommend the <i>whatever</i>-mode.lsp
  naming convention.</li>
</ul>
<p>
  Each <tt>certify-order-element</tt> names a book to be certified
  with the ACL2s system books, in the order given.  You should name
  all the books in this mode directory your modes depend on.  Note
  that here, like in include-book and certify-book, \".lisp\" is not
  included in the name.
</p>
")
