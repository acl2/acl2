
(defxdoc ACL2s Home page/Documentation
  :parents (acl2::acl2-sedan acl2::macro-libraries acl2s::defunc)
  :short "1.2.0.1 (compatible with ACL2 8.0.0)"
  :long
  "<div style="height: 90px;"></div>
  

  <div class="row">
    <div class="eight columns centered" style="margin-bottom: 10pt; font-size: 120%; text-align:justify;">
      The ACL2 Sedan theorem prover (<strong>ACL2s</strong>) is an
      Eclipse plug-in that provides a modern integrated development
      environment, supports several modes of interaction, provides a
      powerful termination analysis engine, includes a rich support
      for "types" and seamlessly integrates semi-automated bug-finding
      methods with interactive theorem proving.
    </div>
  </div>


<a name="intro"><a/>
<div style="height: 20px;"></div>
<div class="row" data-target="intro">
  <h2>Introduction</h2>
  <p><a href="faq.html#faq_acl2"><strong>ACL2</strong></a> is a powerful system for integrated
modeling, simulation, and inductive reasoning.  Under expert control,
it has been used to verify some of the most complex theorems to have
undergone mechanical verification.  In addition to its maturity and
stability, these qualifications make it a good platform for learning
about industrial-strength theorem proving.  Unfortunately, ACL2 has a
steep learning curve and with its traditional tool support is
analogous to a racecar: it is powerful, but it take expertise to
operate properly. </p>

<p> We want to make tool support for the ACL2 platform that is more
analogous to a family sedan; hence, the "ACL2s" or "ACL2 Sedan" name.
With just a little training, a new user should be able to drive slowly
on paved streets without worrying about oversteer, tire temperature,
or even engine RPMs.
</p>

<p>
Pushing aside the analogies, ACL2s includes powerful features that
provide users with more automation and support for specifying
conjectures and proving theorems. This includes <a href="index.html#guide_ccg"
>CCG termination analysis</a> and automated <a href="index.html#guide_RT" >
Counterexample generation</a>. In addition, ACL2s is "safer" by constructing and
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
environment (see <a href="index.html#faq_eclipse"><i>What is Eclipse?</i></a>).
In addition, the plugin requires some extra functionality from ACL2
that is not included in the main distribution.  This functionality is
largely hidden from the user and shouldn't alter ACL2's behavior for
all practical purposes.  To be sure, though, users can certify their
work in a clean ACL2 session (see <a href="index.html#guide_book">Book
development</a>).
</p>

<p>
ACL2s is not completely mature in its capabilities, but industrial and
academic users alike should find it stable enough, intuitive enough,
and capable enough to meet their needs.  Ideally, the tool will become
even more intuitive, self-teaching, etc.  in the future.
</p>


</div>


<a name="tutorial"></a>
<div style="height: 20px;"></div>
<div class="row" data-target="tutorial">  
<h2>Get Started</h2>

<p>
Assuming you have <a href="download.html">downloaded</a> ACL2s, we
will now guide you through the process of creating a new ACL2s/Lisp
file, typing definitions into that file, opening up an associated ACL2
session, sending definitions to the session, querying the session,
etc.
</p>

<h3>Unpack..</h3>  
<p>Simply unpack/<a href="http://www.7-zip.org/">unzip (7z)</a> the
prepackaged Eclipse install tree that you downloaded. It includes all
of ACL2 Sedan and works out of the box.  Make sure you unpack it to a
path which has <b>no spaces</b> and where you have <b>write
permissions</b> (for example /Users/peterd/tools); do this as the user
who will be running Eclipse (i.e. avoid sudo).
</p>

<p>
<b>Note</b>: The ACL2s/eclipse installation is (and should be) separate and
disjoint from any other versions of Eclipse you have installed.
</p>

<p>
Once you have unpacked, navigate into the unpacked folder (remember this
path). Now double-click on Eclipse icon
<img src="../icons/eclipse.png" width=24 height=24> or
enter <tt>./eclipse</tt> in the command line (on Linux); every time you run
ACL2s, you need to repeat this step. You may find it useful to create
a shortcut to it named "ACL2s" in your Desktop to make this more
convenient.
</p>

<h3>Get Set..</h3>
<p> The first time you run Eclipse, it will prompt you for a
"workspace" location. This is where Eclipse will save your
configuration and layout and is the default location for your ACL2s
projects and their associated files. Please <b>choose a fresh
workspace</b> (e.g. /Users/yourname/acl2s-workspace) that is different
from the workspace you use for Java or other eclipse projects.

<p>
Note: ACL2 does not understand network share paths. If the default is
on a network share path, you should "Map network drive" in Windows and
use a path on that drive.
</p>

<p>
If you get a welcome window, you can click the "Go to workbench" icon
to get to the Eclipse "workbench".
</p>

<p>To familiarize yourself with some Eclipse vocabulary and navigating
the workbench, we recommend going through
the <a href="http://help.eclipse.org/luna/index.jsp?topic=%2Forg.eclipse.platform.doc.user%2FgettingStarted%2Fqs-01.htm&cp=0_1_0">Basic
Tutorial</a> section of the Workbench User Guide.
</p>

<p>
<b>Create a project</b>: Select <b>File</b> | <b>New</b>
| <b>Project...</b>  and select <b>Project</b> from the
group <b>General</b>.  Give a name to the project that will contain
your ACL2 developments and click <b>Finish</b>.
</p><p>
<b>Open the "ACL2 Development" perspective</b>:  Select
<b>Window</b> | <b>Open Perspective</b> | <b>ACL2 Development</b>.
You could have instead clicked on the
<img src="new_persp.gif" width=16 height=16> icon in the top-right corner.
The new perspective will change the layout of your workbench.
</p>

<p>
<b>Create a new Lisp file</b> for getting the feel of Eclipse and our
plugin.  Select <b>File</b> | <b>New</b> | <b>ACL2s/Lisp file</b>.
The "Directory" should already indicate the project you just created.
If not, browse to the project you just created.  Pick a file name like
"test.lisp" or leave the default.  Use "ACL2s" for the session mode
and click <b>Finish</b>.
</p>

<p>
You can now type some ACL2 code in the editor.  Type in this
definition to get the feel of the auto-indenting, paren-matching, and
syntax-based coloring:

; Computes the nth fibonacci number (maybe?)
@({
(defun fib (n)
  (if (and (integerp n) 
           (< n 2))
      (+ (fib (- n 1)) (fib (- n 2)))
    1))
})

<p>
Upon creating the new file, an <em>editor</em> has now opened in the
<em>editor area</em></a> of the <em>workbench</em>.
Around the editor area are <em>views</em>,
such as the <em>Project Explorer</em> view to the left and <em>Outline</em> view
to the right.  From their title areas, these can be dragged around, tiled,
minimized, etc.  You probably also noticed that <tt>(defun fib (n)</tt> showed up in
the Outline view, which you can use to navigate the top-level forms of your
file.
</p>

<p>
In the Project Explorer view, which is a tree view of projects and
files, expand your project to reveal a few files:
</p>
<ul>
<li><tt>.project</tt> - a file used by Eclipse to store project-specific
settings.
<li><tt>test.lisp</tt> or whatever you called it.  This will contain ACL2
code your write.
<li><tt>test.lisp.a2s</tt> - a file created automatically when you opened
<tt>test.lisp</tt>.  This file will store the history of ACL2 sessions
you open to develop <tt>test.lisp</tt>.
</ul>

<p>
<b>Open <tt>test.lisp.a2s</tt></b> by double-clicking it in the
Project Explorer.  Alternatively, hit Ctrl+Shift+o
(Mac: <img src="mac-command.gif" width="14" height="13"
alt="Command">+Shift+o) in the editor for <tt>test.lisp</tt>.  This is
the key sequence for switching between corresponding .lisp and
.lisp.a2s editors, opening the other if necessary.  You should now be
in an editor that has a little message "No session running" at the top
and won't let you type anything.  This editor is read-only when no
session is running.
</p>

<h3>Go...</h3>
<p>
<b>Start a session</b> for testing our code in <tt>test.lisp</tt> by
clicking the
<img src="../icons/acl2_restart.gif" width="16" height="16" alt="restart session">
icon in the toolbar.
</p>

<div class="modal" id="modal1">
  <div class="content">
    <a class="close switch" gumby-trigger="|#modal1"><i class="icon-cancel" /></i></a>
    <div class="row">
      <div class="ten columns centered">
        <h3>First-time ACL2s initialization process</h3>
        <p><em>The first time you start a session,</em> there is some
            bookkeeping that ACL2s must take care of.  This will
            happen automatically (except for a couple confirmation
            dialogs), but the process could take several minutes
            (5-10).
      </p>

      <p> First, the ACL2 Image for Eclipse will need to fix .cert
        files for the absolute path of Eclipse on your computer.  If
        you move Eclipse, this step will automatically be repeated. Be
        patient and let it finish this one-time bookkeeping task, it
        might take around 5 minutes.
      </p>
      
      <p> Second, the ACL2s <em>system books</em>, our visible and invisible
        extensions to ACL2, need to be certified and compiled by ACL2.
        This step could be required again if you change your ACL2
        version or when you update ACL2s to a new version.
      </p>
        <!-- <p class="btn primary medium"> -->
        <!--   <a href="#" class="switch" gumby-trigger="|#modal1">Close Modal</a> -->
        <!-- </p> -->
      </div>
    </div>
  </div>
</div>
<p class="medium btn info"><a href="index.html#" class="switch" gumby-trigger="#modal1">Note: ACL2s initialization...</a></p>




<p>
After this bookkeeping, you should be able to click the "restart
session" icon on the toolbar and have ACL2 start up, resulting in the
"<tt>ACL2 &gt;</tt>" prompt.
</p>

<p>
<b>Type an "immediate command" for ACL2</b>, such as
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
<code>(* 21 2)</code> was classified by the plugin as "VALUE"
input, because it's just computation that returns a value.  Another
example is a "QUERY" such as <code>:pe strip-cars</code>, which
prints out information about the current history or "world", in this
case the definition of the function "strip-cars".
<code>(defun successor (x) (1+ x))</code> is an "EVENT" because it
(potentially) changes the history.
See <a href="index.html#guide_classifications">Command Classifications</a> in
the guide for more detail.
For "EVENT" inputs, ACL2s pops up a
dialog asking what to do about the fact that we did something logically
relevant from the command line rather than from our source code.  Read
the dialog and for now choose "Insert".
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
<code>(defun successor (x) (1+ x))</code> form we submitted in the
session editor has been "inserted" above what we had typed previously!
Also, that form is "above the line" and read-only.  This is
part of the intrinsic linkage between <tt>somename.lisp</tt> and
<tt>somename.lisp.a2s</tt>: the forms "above the line" in the .lisp
editor are those used to get the ACL2 session in the .lisp.a2s editor
in its current state.  To maintain this invariant, we have to do one of
two things in the case of executing something history-relevant in the
session editor: insert it at the line in the lisp editor or undo it.
These are the options the "Relevant input at command line" dialog gave us.
Note that "QUERY"s and "VALUE"s do not modify the
history, so we don't need to insert those above the line.
</p>

<p>
<b>Try moving the line</b> past the definition we gave
for <tt>fib</tt> by pressing the "advance todo" button on the toolbar
(<img src="../icons/advance.gif" width="16" height="16"> or
Ctrl+Shift+I on PC or
<img src="mac-command.gif" width="14" height="13" alt="Command">+Shift+I
on Mac).
Watch carefully and you will see the definition for <tt>fib</tt> flash green.
Because it did not turn from green to gray, our definition of <tt>fib</tt> was
rejected by ACL2.  Also, if the "Proof Tree" view is open (probably
left), it might show some information about a failed termination
proof that caused ACL2 to reject the definition.
</p>


<div class="modal" id="modal2">
  <div class="content">
    <a class="close switch" gumby-trigger="|#modal2"><i class="icon-cancel" /></i></a>
<div class="row">
  <div class="ten columns centered">
    <p> The plugin models two "lines" in a .lisp file: the "completed
      line" and the "todo line".  These "lines" are only visible as the
      boundary between regions with different highlighting.  The
      "completed line" is at the last point of gray (or blue)
      highlighting.  The "todo line" is at the last point of <b>any</b>
      highlighting: gray, blue or green.
    </p>

    <p> Above the "completed line" is the (potentially empty) "completed
      region," which has forms that ACL2 has--get this--completed.
      Between the two lines are forms that we want ACL2 to work on
      completing (hence "todo").  This (potentially empty) region, the
      "todo region", has green highlighting.  We can call the rest of
      the buffer the "working region", which is the freely editable
      part.
    </p>
  </div>
</div>
</div>
</div>
<p class="medium btn info"><a href="index.html#" class="switch" gumby-trigger="#modal2">More Details: Meaning of green and gray highlighting?</a></p>



<p>So what was the meaning of the flash of green highlighting?
Clicking "advance todo" moved the "todo line" from between
  <code>(defun successor ...)</code> and <code>(defun fib
...)</code>  to after <code>(defun fib ...)</code>.  With
at least one form in the "todo region", the session started processing
the first (and only) one.  If you look at the session output, you see
that the attempt to admit our <code>fib</code> function failed.  The
attempt to prove termination failed.  If the next "todo" form fails,
the plugin moves the todo line back to the point of the completed
line, "cancelling" the todo operations and prompting the user to fix
the rejected form.
</p>

<p>
<b>Fix our <code>fib</code> definition</b>: the previous one had
parameters to the <code>&lt;</code> comparison swapped.  ACL2 admits
this one:
<pre><code class="lisp">
; Computes the nth fibonacci number
(defun fib (n)
  (if (and (integerp n) 
           (< 2 n))
      (+ (fib (- n 1)) (fib (- n 2)))
    1))
</code></pre>

Now clicking "advance todo" should result in the definition flashing
green while it is in the todo region and turning gray after being
accepted.

</div>

<!-- <ul> -->
<!-- <li><a href="#intro">Introduction/Motivation</a> -->
<!-- <li><a href="#reqs">Requirements/Platforms</a> -->
<!-- <li><a href="#install">Installation</a> and setup -->
<!-- <li><a href="#update">Updating</a> -->
<!-- <li><a href="#tutorial">Beginning Tutorial</a> -->
<!-- <li><a href="#license">Source code and Licensing</a> for ACL2s -->
<!-- <li><a href="#impl">Notes</a> for ACL2 hackers -->
<!-- <li><a href="#contact">Contact info</a> -->
<!-- </ul> -->


<div style="height: 60px;"></div>

<div class="row" data-target="license">
<a name="license"></a>
<h3>Source code and Licensing for ACL2s</h3>
<p>
ACL2s is open-source software, and comes with ABSOLUTELY NO WARRANTY.
Copyright 2008 Georgia Tech Research Corporation and Northeastern University.
</p><p>
All parts are available under the Eclipse Public License v1.0 with a GPL
exception, and the "acl2s-hooks" and "acl2s-modes" parts are dual-licensed
under the GNU General Public License v2.0 as well.
</p><p>
<a href="http://acl2s.ccs.neu.edu/acl2s/src/">Here is the source code download
directory</a>, which contains source code for ACL2, for distributed
Common Lisps, and for the ACL2s Eclipse plugin.  The "ACL2s hooks" and 
"ACL2s modes" parts already includes source code, and are available from
<a href="http://acl2s.ccs.neu.edu/acl2s/update/plugins/">the update site
plugins directory</a>.
</p>

</div>


<div class="row left-center" data-target="contact">
<a name="contact"></a>
<h3>Contact info</h3>
<p>
Email Harsh Raju Chamarthi(<img src="harshrc.jpg" width="165"
height="19">) and Pete Manolios(<img src="pete.jpg" width="165"
height="18">) with bugs and other questions.
</p>

<p>
Up to version 0.97, the main developer has
been <a href="http://www.peterd.org/">Peter Dillinger</a>, advised
by <a href="http://www.ccs.neu.edu/home/pete/contact.html">Pete
Manolios</a>.  Since then, ACL2s is maintained by
<a href="http://www.ccs.neu.edu/home/harshrc">Harsh Raju Chamarthi</a>, 
advised by Pete Manolios.
CCG termination analysis is by Pete Manolios and Daron Vroon.
</p>
</div>

<script src="http://ajax.googleapis.com/ajax/libs/jquery/1.9.1/jquery.min.js"></script>
<script>
//<![CDATA[
window.jQuery || document.write('<script src=/jquery-1.9.1.min.js><\/script>')
//]]>
")
