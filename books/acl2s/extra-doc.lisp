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
<b>Window</b> | <b>Open Perspective</b> | <b>ACL2 Development</b>.
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
Upon creating the new file, an <em>editor</em> has now opened in the
<em>editor area</em> of the <em>workbench</em>.
Around the editor area are <em>views</em>,
such as the <em>Project Explorer</em> view to the left and <em>Outline</em> view
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

<box>
<h4>Note: First-time ACL2s initialization...</h4>

<p>
<em>The first time you start a session,</em> there is some
bookkeeping that ACL2s must take care of.  This will happen
automatically (except for a couple confirmation dialogs), but the
process could take several minutes (5-10).
</p>

<p>
First, the ACL2 Image for Eclipse will need to fix .cert files for the
absolute path of Eclipse on your computer.  If you move Eclipse, this
step will automatically be repeated. Be patient and let it finish this
one-time bookkeeping task, it might take around 5 minutes.
</p>
      
<p>
Second, the ACL2s <em>system books</em>, our visible and invisible
extensions to ACL2, need to be certified and compiled by ACL2.  This
step could be required again if you change your ACL2 version or when
you update ACL2s to a new version.
</p>

</box>

<p>
After this bookkeeping, you should be able to click the \"restart
session\" icon on the toolbar and have ACL2 start up, resulting in the
\"<tt>ACL2 &gt;</tt>\" prompt.
</p>


<p>
<b>Type an \"immediate command\" for ACL2</b>, such as
<code>(* 21 2)</code> in the session editor (.a2s editor).  Notice
that the editor is read-only except for the part after the last prompt.
Hitting <em>Enter</em> (<em>Return</em>) at the end of this editor will submit
the typed
form to ACL2.  Actually, it will only submit <em>syntactically valid</em>
commands to ACL2, so if one tries to trick it by hitting <em>Enter</em>
after just <code>(* 21</code>, the editor just goes to the next
line.
</p>

<p>
<b>Try submitting other types of input</b> to ACL2.
<code>(* 21 2)</code> was classified by the plugin as \"VALUE\"
input, because it's just computation that returns a value.  Another
example is a \"QUERY\" such as <code>:pe strip-cars</code>, which
prints out information about the current history or \"world\", in this
case the definition of the function \"strip-cars\".
<code>(definec successor (x :int) :int (1+ x))</code> is an \"EVENT\" because it
(potentially) changes the history.
See <a href=\"index.html#guide_classifications\">Command Classifications</a> in
the guide for more detail.
For \"EVENT\" inputs, ACL2s pops up a
dialog asking what to do about the fact that we did something logically
relevant from the command line rather than from our source code.  Read
the dialog and for now choose \"Insert\".
</p>

<p>
<b>Try submitting something with an error</b> such as
<code>(successor 1 2)</code>--an error because the arity of the <tt>successor</tt>
function we just defined is 1.  The red (maroon, I guess) output indicates
the command was not successful.  ACL2 is back in the state it was in before
you submitted the form that caused the error.
</p>

<h3>Line action</h3>

<p>
<b>Switch back to the .lisp editor</b> where you will discover the
<code>(definec successor (x :int) :int (1+ x))</code> form we submitted in the
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
 
  <div class=\"row\">
    <div class=\"eight columns centered\" style=\"margin-bottom: 10pt; font-size: 120%; text-align:justify;\">
      The ACL2 Sedan theorem prover (<strong>ACL2s</strong>) is an
      Eclipse plug-in that provides a modern integrated development
      environment, supports several modes of interaction, provides a
      powerful termination analysis engine, includes a rich support
      for \"types\" and seamlessly integrates semi-automated bug-finding
      methods with interactive theorem proving.
    </div>
  </div>



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
environment (see <a href=\"index.html#faq_eclipse\"><i>What is Eclipse?</i></a>).
In addition, the plugin requires some extra functionality from ACL2
that is not included in the main distribution.  This functionality is
largely hidden from the user and shouldn't alter ACL2's behavior for
all practical purposes.  To be sure, though, users can certify their
work in a clean ACL2 session (see <a href=\"index.html#guide_book\">Book
development</a>).
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
<h3>General</h3>

<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><strong>Is my OS 32 bit or 64 bit?</strong></td> </tr>
<tr> <td valign=\"top\">A:</td>
     <td>For Linux and MacOS, if you see \"x86_64\" or \"amd64\" in the
output of shell command <code>uname -a</code> in your terminal, you have a
64bit OS, otherwise a 32 bit one.  For other operating systems, please
visit their respective FAQ
pages: <a href=\"http://support.microsoft.com/kb/827218\">Windows</a>.
</td></tr>
</table>

<div class=\"left-center\" data-target=\"faq_section_eclipse\">
<h3>Eclipse-related</h3>

<a name=\"faq_eclipse\"></a>
<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><strong>What is Eclipse?</strong></td> </tr>
<tr> <td>A:</td>
     <td>Eclipse is a highly modularized, extensible, free
development environment for a variety of programming languages.  See <a
href=\"http://www.eclipse.org\">www.eclipse.org</a>.  Eclipse is written
in Java and has an especially well developed development environment
for Java.</td></tr>
</table><br/>


<a name=\"faq_eclipse_lingo\"></a>
<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><strong>Where do I learn about all this Eclipse lingo?</strong></td> </tr>
<tr> <td>A:</td>
     <td>See the <a href=\"http://help.eclipse.org/2022-06/topic/org.eclipse.platform.doc.user/gettingStarted/qs-02a.htm\">Basic
Tutorial section of the <em>Workbench User Guide</em></a>.
</td></tr>
</table><br/>


<a name=\"faq_eclipse_running\"></a>
<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><strong>How do I run Eclipse--with the right options?</strong></td> </tr>
<tr> <td>A:</td>
     <td>See the \"Running Eclipse\" section of the 3.5 Release Notes.
To view details about how a currently-running Eclipse was invoked, go to
<b>Help</b> | <b>About Eclipse SDK</b> and click \"Configuration Details\".
</td></tr>
</table><br/>


<a name=\"faq_eclipse_java_version\"></a>
<table class=\"rounded striped\">
<tr> <td >Q:</td>
     <td><strong>How do I tell what Java version Eclipse is running under, and if its 64bit?</strong></td> </tr>
<tr> <td>A:</td>
     <td>Inside Eclipse, go to <b>Help</b> | <b>About Eclipse SDK</b> and
click \"Installation Details\".  Under \"Configuration\" tab are the \"eclipse.commands\"
property and the \"java.runtime.*\" properties, you will find the relevant information. 
You can also find out under \"-arch\" your machine architecture, for
example, \"X86_64\" will indicate that you are running a 64bit Eclipse. 
\"java.vm.name\" will tell you if the Java being used is a 64bit JVM.
</td></tr>
</table><br/>


<a name=\"faq_eclipse_docs\"></a>
<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><strong>Where is Eclipse documentation?</strong></td> </tr>
<tr> <td>A:</td>
     <td><a href=\"http://www.eclipse.org/documentation/main.html\">http://www.eclipse.org/documentation/main.html</a>
</td></tr>
</table><br/>


<a name=\"faq_eclipse_multiuser\"></a>
<table class=\"rounded striped\">
<tr> <td >Q:</td>
     <td><strong> Can I do a multi-user install of Eclipse?</strong></td> </tr>
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

<div class=\"left-center\" data-target=\"faq_section_acl2\">
  <h3>ACL2-related</h3>

  <a name=\"faq_acl2\"></a>
<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><strong>What is ACL2?</strong></td> </tr>
<tr> <td>A:</td>
     <td>ACL2 is a programming language, logic, and theorem
prover/checker based on Common Lisp.  See <a
href=\"http://www.cs.utexas.edu/~moore/acl2/\">the ACL2 home page</a> for more
information.</td></tr>
</table>

<a name=\"faq_car\"></a>
<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><strong>What is CAR?</strong></td> </tr>
<tr> <td>A:</td>
     <td><u>CAR</u> is an abbreviation we sometimes use to refer to this
(print) book:
<blockquote>
<strong>Computer-Aided Reasoning: An Approach</strong>.<br/>
Matt Kaufmann, Panagiotis Manolios, and J Strother Moore.<br/>
Kluwer Academic Publishers, June, 2000. (ISBN 0-7923-7744-3)
</blockquote>
See <a href=\"http://www.cs.utexas.edu/users/moore/publications/acl2-books/car/index.html\">J
Moore's page about the book</a> for description and <b>affordable</b>
ordering information.
</td>
</tr>
</table>

<a name=\"faq_acl2_book\"></a>
<table class=\"rounded striped\">
<tr> <td >Q:</td>
     <td><strong>What is an ACL2 book?</strong></td> </tr>
<tr> <td >A:</td>
     <td>Basically, an ACL2 book is a bunch of ACL2 definitions (functions,
theorems, proof rules, etc.) that can be easily imported into other ACL2
work.  See <a
href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____BOOKS\">:DOC books</a> and
<a href=\"user_guide.html#guide_book\">our guide to book development in ACL2s</a>
for more information.</td></tr>
</table><br/>

<a name=\"faq_acl2_image_outside\"></a>
<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><strong>Can I use the ACL2 image downloaded by Eclipse outside of Eclipse?</strong></td> </tr>
<tr> <td>A:</td>
     <td>Absolutely!  From the ACL2 perspective, it has everything you would
have building ACL2 yourself. Use the following executable script
<code>myeclipse/plugins/acl2_image.<em>something</em>/run_acl2</code>
instead of the usual <code>saved_acl2</code>
</td></tr>
</table>

<a name=\"impl_acl2_path\"></a>
<table class=\"rounded striped\">
<tr> <td>Q:</td>
<td><strong>Can I use my own version of ACL2? i.e. Finding ACL2 on user's system:</strong></td>
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

<div class=\"left-center\" data-target=\"faq_section_java\">
<h3>Java-related</h3>

<a name=\"faq_already_java\"></a>
<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><strong>Do I already have Java?  What version?</strong></td> </tr>
<tr> <td>A:</td>
     <td>The simple answer is to type <code>java -version</code> at
your operating system's command prompt/terminal/shell.  You might
still have Java if the command is rejected.
See also <a href=\"faq.html#faq_eclipse_running\">How do I run Eclipse--with the
right options?</a> and <a href=\"faq.html#faq_5.0\">Is there a difference
between Java SDK 1.5.0 and 5.0?</a> for more info.
</td></tr>
</table>


<a name=\"faq_sdk\"></a>
<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><strong>Do I need the Java SDK or is the JRE fine?</strong></td> </tr>
<tr> <td>A:</td>
     <td>The SDK is only needed if you plan on ever doing any Java
development. The (smaller) JRE should be opted if there is a
choice. It is recommended to have separate eclipse installations
(directories) for Java development and ACL2 development.
</td></tr>
</table><br/>


<a name=\"faq_5.0\"></a>
<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><strong>Is there a difference between Java SDK 1.5.0 and 5.0?</strong></td> </tr>
<tr> <td>A:</td>
     <td>No.  \"5.0\" is the version number adjusted for marketing-hype.  See
<a href=\"http://java.sun.com/j2se/1.5.0/docs/relnotes/version-5.0.html\">
\"Version 1.5.0 or 5.0?\"</a> on Sun's site. Similarily, there is no
difference between Java version \"6.0\" and JDK/JRE 1.6.0 etc etc.
</td></tr>
</table><br/>


<a name=\"faq_netbeans\"></a>
<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><strong>What is Netbeans?</strong></td> </tr>
<tr> <td>A:</td>
     <td>Netbeans is a Java development environment that feels much like
Eclipse but is more Java-specific.  You do not need it.
</td></tr>
</table><br/>


<a name=\"faq_oldjava\"></a>
<table class=\"rounded striped\">
<tr> <td >Q:</td>
     <td><strong>Can I use a version 1.* of Java?</strong></td> </tr>
<tr> <td >A:</td>
     <td>ACL2s Eclipse plugin uses 1.5
<a href=\"http://java.sun.com/j2se/1.5.0/docs/relnotes/features.html#lang\">language constructs</a> and
<a href=\"http://java.sun.com/j2se/1.5.0/docs/relnotes/features.html#base_libs\">APIs</a>.
You are likely to encounter problems if you use a Java runtime that is
older than \"5.0\". Moreover due to
a <a href=\"http://java-performance.info/changes-to-string-java-1-7-0_06/\">bug</a>
in JRE 1.7, ACL2s will not work with it. We recommend the use of JRE
1.6 or 1.8.
</td></tr>
</table><br/>
</div>

<div class=\"left-center\" data-target=\"faq_section_acl2s\">
<h3>ACL2s-related</h3>

<a name=\"faq_restrictions\"></a>
<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><strong>Why won't ACL2s let me do &lt;blah&gt; in a session?</strong></td> </tr>
<tr> <td>A:</td>
     <td><p>In order for the plugin to follow what's going on in ACL2, we
must impose some small limitations.  One, for example, is that it will not let
you break into raw Lisp.  For those interested in this dangerous,
low-level form of interaction, however,
<a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____SET-RAW-MODE\">raw
mode</a> is supported (because it uses ACL2's reader).  
</p><p>
Another subtle limitation is that--aside from
<a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2_____WORMHOLE\">wormholes</a>--<a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____LD\">ld</a>
will only let you read from
<a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2_____star_STANDARD-OI_star_\">*standard-oi*</a> at ld level 1.  The reason has to do with undoing and
also <a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____LD-ERROR-ACTION\">ld-error-action</a>.  Another example is that
<tt>good-bye</tt> and other exit commands are disabled to the user,
to encourage use of the user interface operation \"Stop session\" instead.
</p><p>
For more details, see <a href=\"http://acl2s.ccs.neu.edu/acl2s/doc/impl.html#impl_hooks\">How/what ACL2 functionality is
modified for ACL2s</a>.
</p>
</td></tr>
</table><br/>

<a name=\"faq_acl2s_emacs\"></a>
<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><strong>Can I use ACL2s extensions to ACL2 in an Emacs development environment?</strong></td> </tr>
<tr> <td>A:</td>
     <td>

<p>Yes! One can reproduce inside Emacs, the theorem proving
     environment ACL2 Sedan provides (sans GUI) in the various session
     modes. To use just the CCG analysis and Counterexample generation
     features individually, see the next question. 
</p>
<p>
  Assuming you have ACL2s installed as an eclipse plugin
     in <tt>/Users/sarah/tools/eclipse</tt>, here are instructions on
     how to run an <em>ACL2s mode</em> session in Emacs. Name the above
     directory <em>my_eclipse</em>.
</p>
    <ol>
    <li>Open a shell in emacs, start the ACL2 session: <code><em>my_eclipse</em>/plugins/acl2_image.<em>something</em>/run_acl2</code></li>
    <li>In the ACL2 session, submit the following 3 commands:
 @({
   (add-include-book-dir :acl2s-modes \"my_eclipse/plugins/acl2s_modes_<em>something</em>/\") 
   (ld \"acl2s-mode.lsp\" :dir :acl2s-modes)
   (reset-prehistory t)
   })
</li>
</ol>
<p>
If you want more finer control on what gets loaded, you can selectively copy paste the forms in the <tt>acl2s-mode.lsp</tt> that
you need, in the emacs session. For example, say you want a session without trust tags, then except
for the <code>(include-book \"ccg\" ...)</code> form, submit the rest of the events in <tt>acl2s-mode.lsp</tt>.
</p>
<p>
To reproduce other sessions modes, follow the above, but replace acl2s-mode.lsp by the corresponding session mode file, e.g. acl2s-beginner.lsp
</p>
</td></tr>
</table><br/>


<a name=\"faq_ccg_emacs\"></a>
<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><strong>Can I use CCG termination analysis and Counterexample
     generation in Emacs (ACL2 session)?</strong></td> </tr>
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

</div>

<div class=\"left-center\" data-target=\"faq_section_installation\">
  <a name=\"faq_section_installation\"></a>
<h3>Installation Issues</h3>
<a name=\"faq_installation_problems\"></a>
<table class=\"rounded striped\">
<tr> <td>Q:</td>
     <td><strong>I am having trouble installing/running ACL2s, what should I do?</strong></td> </tr>
<tr> <td>A:</td>
     <td>
<h5>Case: Standard prepackaged installation</h5>
<ul class=\"disc\"> 

<li><b><sf>ACL2 appears to be stuck on starting (Anti-virus software is getting in the way):</sf></b> Do whatever is necessary to give eclipse/plugins/acl2_image*/run_acl2.exe appropriate privileges. In particular, if on Avast Anti-virus, go to settings and uncheck the DeepScreen feature.
</li>

<li><b>Old Linux distros</b> On linux machines whose glibc version is older
than 2.15 the current prepackaged tarball does not work. Please contact
the ACL2s maintainer to provide you with a custom ACL2s build.
</li>

</ul>
<br/>
<h5> Case: Non-standard Installation:</h5>
<ul class=\"disc\">

<li><strong><sf>MacOSX/Linux Permissions:</sf></strong> If you
installed eclipse on your Mac/Linux machine using a package manager
that comes with the OS, then you will have trouble installing and
starting ACL2s due to different permissions. Instead follow the
eclipse download instructions as described above in the website,
mainly: Download the Eclipse tar.gz and extract (without using sudo)
the archive in your home directory
(e.g. <tt>/home/johnd/tools/eclipse</tt>).</li>

<li><b><sf>Cannot Start ACL2:</sf></b> If ACL2s was installed
correctly, but when you start an ACL2 session, you get an error, then
there can be other causes like: 
<br/><font size=\"2\">
1. You only installed ACl2s plugin and not the ACL2 image and you forgot to specify the build path in <em>Windows&rarr;Preferences&rarr;ACL2s&rarr;ACL2</em>.
</font>
<br/><font size=\"2\">
2. You are using an older ACL2 version, again check the build path in <em>Windows&rarr;Preferences&rarr;ACL2s&rarr;ACL2</em> and modify it to point to a newer version.
</font>
<br/><font size=\"2\">
3. You are using a workspace on network share path. Switch to a workspace on local path.
</font>
<br/><font size=\"2\">
4. Certain exectuable scripts e.g. run_acl2, dx86cl64, wx86cl64.exe etc in your acl2_image* plugin do not have executable permissions.
</font>

</li>

<li><strong><sf>Java issues:</sf></strong> We recommend JRE version 1.8 (also known as Java 8.0).
Either Java is not
installed (not in PATH) or you are using a version of JRE 1.7 that
has a
<a href=\"http://java-performance.info/changes-to-string-java-1-7-0_06/\">bug</a>
in its string library.</li>

</ul>
</td></tr>
</table><br/>
</div>
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


        <div class=\"left-center\" data-target=\"cheat_sheet\">
          <h2>Cheat Sheet</h2>
          A cheat sheet is available with a summary of key bindings and command types:
          <a href=\"http://acl2s.ccs.neu.edu/acl2s/doc/sheet.html\">HTML</a> or <a href=\"res/acl2s/sheet.pdf\">PDF</a>.
        </div>

<div class=\"left-center\" data-target=\"guide_customization\">
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
<a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____ACL2-CUSTOMIZATION\">acl2-customization file</a>.
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
<a href=\"http://acl2s.ccs.neu.edu/acl2s/doc/impl.html#impl_hooks\">How/what ACL2 functionality is modified for ACLs</a>.
Also see <a href=\"user_guide.html#guide_book\">book development</a> for certification
with ACL2 proper inside of ACL2s/Eclipse.
</p>
</td></tr>
</tbody>
</table>

<p><em>Additional advanced note:</em>
Another feature of all these modes except \"Compatible\" is doing destructor
elimination before laying down a checkpoint.  Thus, the checkpoint summary
will show the formula after destructor elimination.  The downside is that the
variable names may appear cryptic and unfamiliar, but the upside is that
you get some generalization for free, usually resulting in smaller formulas.
</p><p>
Notes about how these modes are implemented are described in
<a href=\"http://acl2s.ccs.neu.edu/acl2s/doc/impl.html#impl_modes\"><em>How modes are implemented</em></a>.
</p>
</div>

<div class=\"left-center\" data-target=\"guide_classifications\">
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
<a href=\"@(url acl2::embedded-event-form)\">embedded event forms</a>,
which are those forms that can appear in <a href=\"user_guide.html#guide_book\">books</a>.
Calls to <tt>defun</tt>, <tt>defmacro</tt>, and <tt>defthm</tt> are examples
of embedded event forms and <b>EVENT</b>s.
</td></tr>
<tr><td valign=\"top\"><b>VALUE</b></td><td>
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
<a href=\"@(url acl2::cw)\">CW</a>
and
<a href=\"@(url acl2::wormhole)\">WORMHOLE</a>).
</p>
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
(<a href=\"http://acl2s.ccs.neu.edu/acl2s/doc/impl.html#impl_undo_redo\"><em>How undo and redo are implemented</em></a>),
but should keep in mind that <b>UNDO</b>ing an <b>ACTION</b> or <b>RAW</b>
form may not have the desired effect.
</td></tr>
<tr><td valign=\"top\"><b>REDO</b><br/>(internal initiation only)</td><td>
<p>This is the counterpart of <b>UNDO</b>.  It is used when resubmitting
something with the same abstract syntax and in the same environment as
something that was previously undone.
</p><p>
<b>REDO</b> enables one to (for example) edit comments above the line, by
retreating the line far enough to edit what one wants to change, and then
moving the \"todo\" line back to where it was.  If only comments were
changed, the session will accept the forms as <b>REDO</b>s, which happen
almost instantaneously.
</p>
</td></tr>
<tr><td valign=\"top\"><b>BAD</b></td><td>
<p>If the input is a parseable ACL2 object but is an ill-formed expression
according to the current history, we call it \"BAD\" input.  Examples of
violations that would cause input to be staticly ill-formed are:
<ul>
<li>wrong number of parameters to a function/macro</li>
<li>use of an undefined function/macro</li>
<li>first element of an invocation list is not a symbol or lambda expression</li>
<li>mismatch between expected and actual @('mv') shape</li>
</ul>
</p>
</td></tr>
<tr><td valign=\"top\"><b>COMMAND</b></td><td>
There are many forms that are illegal in books but we are able to undo the
effect of.  If we recognize a form as such, we call it a <b>COMMAND</b>--
except for special cases <b>IN-PACKAGE</b> and <b>BEGIN-BOOK</b>.  The
best example of a command is \"<tt>:set-guard-checking :none</tt>\".
</td></tr>
<tr><td valign=\"top\"><b>ACTION</b><br/>
<font color=\"red\">(potentially dangerous!)</font></td><td>
This is the \"catch-all\" categorization for forms that may have effects
that we don't know how to properly undo or might even break or hang the
ACL2 session.  Users who use
<a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____STOBJ\">STOBJs</a>
or other
<a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____STATE\">STATE</a>
beyond the logical
<a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____WORLD\">WORLD</a>
will need to use <b>ACTION</b>s heavily, but these are advanced uses of ACL2.
</td></tr>
<tr><td valign=\"top\"><b>IN-PACKAGE</b></td><td>
This <b>COMMAND</b> gets its own category because of its role in
<a href=\"user_guide.html#guide_book\">book development</a>.  See also
<a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____IN-PACKAGE\">:DOC
in-package</a>.
</td></tr>
<tr><td valign=\"top\"><b>BEGIN-BOOK</b></td><td>
This <b>COMMAND</b> gets its own category because of its role in
<a href=\"user_guide.html#guide_book\">book development</a> with our plugin.  This form
is not part of ACL2 proper (yet!).
</td></tr>
<tr><td valign=\"top\"><b>EVENT/VALUE</b></td><td>
These are a special type of
<a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____EMBEDDED-EVENT-FORM\">embedded event form</a>
(<tt>value-triple</tt>s) that have no logical consequence--except that they
could halt progress by generating a hard lisp error.
</td></tr>
<tr><td valign=\"top\"><b>RAW</b><br/>
<font color=\"red\">(potentially very dangerous!)</font></td><td>
Most users of ACL2 are familiar with breaking into \"raw lisp\" by typing
\":q\" at the top-level prompt.  This is not supported in our plugin, but
<a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____SET-RAW-MODE\">
\"raw mode\"</a> is supported.  Most forms submitted under this mode are
classified as <b>RAW</b> because they have no well-defined meaning from the
ACL2 view of things.  With raw mode, the user can easily break many things,
and it's only supported for the benefit of <em>experts</em>.
</td></tr>
</tbody>
</table>
</div>

<div class=\"left-center\" data-target=\"guide_desc\">
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
example, <em>Interrupt</em> is still Ctrl+Break (if you have a Break key), but
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
<u><font color=\"red\">(</font></u> and <u><font color=\"red\">)</font></u>,
or <u><font color=\"red\">\"</font></u> and <u><font color=\"red\">\"</font></u>),
then this action moves the cursor just beyond the match.  Invoking this action
twice in a row should have no net effect <em>except</em> in the case of
going from a <u><font color=\"red\">,</font></u> to its matching
<u><font color=\"red\">`</font></u>, which could potentially have many commas
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
description of checkpoints, see
<a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____THE-METHOD\">:DOC
THE-METHOD</a>.
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
history of ACL2 commands (assuming <em>readline</em> support).  Previous:
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
into the .a2s buffer.  We call these \"immediates.\"  Whenever <em>Enter</em>
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
Shortcut: Ctrl+Shift+M <font color=\"red\">This has changed from 0.9.6
    to accomodate for GNOME users. To restore this binding to
    Ctrl+Shift+U, go to Window&rarr;Preferences&rarr;General&rarr;Keys and change
    the \"Retreat Line\" action's binding.</font>
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
See <a href=\"user_guide.html#guide_book\">book development</a>.  Alt+C
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
The \"ACL2s,\" \"Intermediate,\" and \"Recursion &amp; Induction\" session modes
include
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
analysis to show what it is doing.  This generates <em>lots</em> of
output, however.
</p><p>
Finally, \"Compatible\" mode does not include CCG, and \"Programming\" mode
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

<div class=\"left-center\" data-target=\"guide_datadef\">
<h2>Data Definitions</h2>
<h4>Background</h4>
<p>
Data definitions are an essential part of crafting programs and
modeling systems. Whereas most programming languages provide rich
mechanisms for defining datatypes, ACL2 only really provides a
limited collection of built-in types and <code>cons</code>. 
</p>

<p>
This state of affairs presented us with a challenge when we started
teaching undergraduates how to model, specify and reason about
computation, because even freshmen students have a type-centric view
of the world.
</p>

<p>
We introduced the <b class=\"embolden\">defdata</b> framework in ACL2s
in order to provide a convenient, intuitive way to specify data
definitions.  A version of <code>defdata</code> has appeared in ACL2s
since at least August 2009 (in version 0.9.7), and we have been
extending and improving it since then.
</p>


<h4>Documentation</h4>
<p>
See @(see defdata::defdata) for defdata's documentation. In particular,
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
All modes except \"Compatible\" and \"Programming\" have testing enabled
by default.  This feature is independent of the rest of ACL2s in the
sense that it is implemented as an ACL2 book in the acl2s-modes
plugin.
</p>

<h4>Documentation</h4>
<p>
See @(see test?) and @(see cgen) for more documentation.
</p>

</div>

<div class=\"left-center\" data-target=\"guide_book\">
  <a name=\"guide_book\"></a>
<h2>ACL2 Book Development</h2>
<h4>Introduction</h4>
<p>
An ACL2/ACL2s <a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____BOOKS\">book</a>
is a reusable collection of definitions and other
<a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____EVENTS\">events</a>
(<a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____EMBEDDED-EVENT-FORM\">embedded event forms</a>,
actually).  A valid book can be certified to demonstrate its validity and/or
to prepare it for inclusion using @(see include-book) elsewhere.
</p><p>
To develop a .lisp file as a book in ACL2s, either create the file using
the ACL2s/Lisp file wizard selecting \"Create with book code\", or put this at the
top/beginning:
<pre>
<code class=\"lisp\">
  (begin-book t :ttags :all)
  (in-package \"ACL2\")
</code>
</pre>

Usually the only things that would go before the <code>begin-book</code> form
are package definitions (<a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____EVENTS\">defpkg</a>),
but these aren't worth learning about until you know you need them.
</p><p>
After the <code>begin-book</code> and <code>in-package</code> come the
definitions and other events for your book.  As one is developing a book,
it is very helpful to use the line action discussed above for interactive
development.  One difference is that everything starting from the
<code>begin-book</code> form that is in the \"completed\" region will be
highlighted blue as long as it is valid for use in a book (see 
<a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____EMBEDDED-EVENT-FORM\">EMBEDDED-EVENT-FORM</a>).
Any <em>tangent</em> from book-valid forms will begin gray highlight.  Such
tangents should eventually be undone and removed before certification.
</p><p>
To ensure your book is valid/certifiable, save your changes and choose
\"Certify as book\" from the menu or toolbar (<icon src=\"res/acl2s/icons/acl2_book.gif\"
width=\"16\" height=\"16\"/>).  An Eclipse console will dump the output of the
certification process and indicate success or failure when finished.
</p>

<h4>More detail</h4>
<p>
In ACL2s, a <code>(begin-book ...)</code> form in a .lisp file has
special significance, indicating the .lisp file is intended to define
a book.  Our approach might seem strange at first, but it really works
pretty well with the seemingly obscure requirements ACL2 has for books.
This and the next subsection get into the details and the justification.
</p><p><icon src=\"res/acl2s/book_dev.png\" width=\"424\" height=\"400\" align=\"right\"/>
The <em>preamble</em> is everything that comes before the
<code>begin-book</code>.  This defines what ACL2 authors call the
<em>certification world</em> for the book, which become the book's
<a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____PORTCULLIS\"><em>portcullis</em></a>.  The
simplest explanation for the preamble/portcullis is that it is where
any <a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____EVENTS\"><code>defpkg</code></a> events
should go, because
these are not allowed inside books (because Common Lisps vary in their
ability to compile files that define packages).
</p><p>
The <code>begin-book</code> form itself takes the syntax of ACL2's
<a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____CERTIFY-BOOK\"><code>certify-book</code></a> except
<code>begin-book</code> doesn't take the \"book-name\" or \"k\" parameters.  In
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
from <a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____CERTIFY-BOOK\">ACL2's documentation for
<code>certify-book</code></a>.  But the <code>ttags</code> argument is
important in ACL2s:
</p><p>
ACL2s session modes other than \"Compatible\" mode utilize ACL2 extensions that
ACL2 cannot verify are sound or even safe.  These modes include books
for ACL2s that define <em>trust tags</em> or <em>ttags</em> in order to tweak
ACL2 in non-standard ways.  In order to certify a book that depends on
the use of trust tags, including books defined in a mode other than
\"Compatible\", an appropriate <code>:ttags</code> argument must
be given to <code>begin-book</code>.  We recommend the all-encompassing
<code>:all</code> argument to <code>:ttags</code>, which roughly says,
\"I recognize this book could depend on some non-standard stuff, and
I don't want to bother specifying the details.  Just go ahead.\"
See the docs for <a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____TTAGS-SEEN\">ttags-seen</a>
and <a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____CERTIFY-BOOK\">certify-book</a> for more
information on how to be more specific.
</p><p>
The <em>contents</em> or <em>body</em> of a book is everything after the
<code>begin-book</code> form as long as it conforms to
<a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____BOOK-CONTENTS\">ACL2's requirements for
book contents</a>.  Basically, the first form must be
<code>(in-package \"</code><em>blah</em><code>\")</code> where <em>blah</em> names
a built-in package (such as ACL2 or ACL2-USER) or a package defined in the
preamble.  (The wizard for \"New ACL2s/Lisp file\" can generate appropriate
\"book code\" that defines a package in the standard way, begins the book, and
enters the defined package.)  After the
<code>(in-package \"</code><em>blah</em><code>\")</code> form are
<a href=\"http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____EMBEDDED-EVENT-FORM\">embedded event
forms</a> using <em>blah</em> as the default package.  In ACL2s, embedded
event forms have the <a href=\"user_guide.html#guide_classifications\">input
classification</a> EVENT or EVENT/VALUE.
</p><p>
Book code in the completed region is formatted specially.  The preamble
looks like any other non-book .lisp file, and so uses gray highlighting.
The <code>begin-book</code> form begins the part that distinguishes this
.lisp file as a book, and so begins blue highlighting.  The blue
highlighting continues either until the end of the current \"completed\"
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
<a name=\"guide_book_impl\"></a>
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
Our \"preamble\" roughly corresponds to what ACL2 users would put in
a .acl2 file.  We have a java subroutine/program that can extract the
specially-formatted preamble+begin-book from a .lisp file and put it
into a .acl2 file with the begin-book call translated to a corresponding
certify-book call.  This subroutine is used to generate a .acl2 file when
the ACL2s users asks to \"Certify as book\" but the functionality can also
be accessed as a stand-alone program.  The class is
acl2s.lib.certify.MaybeExtractPreamble in acl2s-lib (acl2s-lib.jar in the
plugin directory).  This program plays nice with old codebases in that it
will not overwrite an existing .acl2 file unless there is an ACL2s preamble
in the corresponding .lisp file.
</p><p>
Right now, however, there's no automatic way to import an existing book AND
its \"preamble\" into an ACL2s-ready .lisp file.  You can, however, open the
.lisp file with ACL2s, which from the ACL2s perspective has no book code
yet, insert the preamble and <code>begin-book</code> form at the top, and
save it.
</p>
</div>

<div class=\"left-center\" data-target=\"guide_trace\">
<h2>Tracing function execution</h2>
<p>
ACL2s offers a \"beautified\" version of ACL2's tracing capability, which is
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
<span style=\"color:#0000b0\">ACL2 &gt;</span><span style=\"color:#808080\">VALUE</span>
<span>(rev '(1 2))</span><br/></code>
<table style=\"border:solid yellow\" cellpadding=\"0\" cellspacing=\"0\"><tr><td>
<code><span style=\"color:#008000\">
<pre style=\"margin: 0cm 0cm 0cm 0cm\">1&gt; (APP NIL '(2))
&lt;1 (APP NIL '(2))
 = '(2)
1&gt; (APP '(2) '(1))
  2&gt; (APP NIL '(1))
  &lt;2 (APP NIL '(1))
   = '(1)
&lt;1 (APP '(2) '(1))
 = '(2 1)</pre></span></code>
</td></tr></table>

<code>
<span style=\"color:#008000;border:solid purple\">(2 1)</span><br/>
<span style=\"color:#0000b0\">ACL2 &gt;</span><br/>
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
\"<code>2&gt; (APP NIL '(1))</code>\" indicates that <code>app</code> was
called recursively.  The \"2\" means the recursive depth is two.  We then
see that that call (level 2) returns <code>(1)</code> and the outer call
of <code>app</code> (level 1) returns <code>(2 1)</code>.
</p><p>
The final <code>(2 1)</code> outlined with purple is the usual printed
output of evaluating <code>(rev '(1 2))</code>.  This comes from the
\"PRINT\" part of \"READ-EVAL-PRINT (LOOP)\".
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
\"relevant\".  Calls to <code>trace*</code> are
<a href=\"user_guide.html#guide_classifications\">classified</a> as COMMAND, which means they
are not allows in <a href=\"user_guide.html#guide_book\">books</a>.
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
If one attempts to use tracing in \"Compatible\" mode,
you might get this output:
</p>
<pre><code class=\"lisp\">1&gt; !! Warning: guard-checking is not :none, so trace    !!
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
")
