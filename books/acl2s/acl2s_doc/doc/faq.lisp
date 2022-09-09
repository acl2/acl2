
(defxdoc ACL2s FAQ
  :parents (acl2::acl2-sedan acl2::macro-libraries acl2s::defunc)
  :short "Frequently Asked Questions"
  :long
  "
<h3>General</h3>

<a name="faq_3264"></a>
<table class="rounded striped">
<tr> <td>Q:</td>
     <td><strong>Is my OS 32 bit or 64 bit?</strong></td> </tr>
<tr> <td valign=top>A:</td>
     <td>For Linux and MacOS, if you see "x86_64" or "amd64" in the
output of shell command <code>uname -a</code> in your terminal, you have a
64bit OS, otherwise a 32 bit one.  For other operating systems, please
visit their respective FAQ
pages: <a href="http://support.microsoft.com/kb/827218">Windows</a>.
</td></tr>
</table>
</div>

<div class="left-center" data-target="faq_section_eclipse">
<h3>Eclipse-related</h3>

<a name="faq_eclipse"></a>
<table class="rounded striped">
<tr> <td>Q:</td>
     <td><strong>What is Eclipse?</strong></td> </tr>
<tr> <td>A:</td>
     <td>Eclipse is a highly modularized, extensible, free
development environment for a variety of programming languages.  See <a
href="http://www.eclipse.org">www.eclipse.org</a>.  Eclipse is written
in Java and has an especially well developed development environment
for Java.</td></tr>
</table><br>


<a name="faq_eclipse_lingo"></a>
<table class="rounded striped">
<tr> <td>Q:</td>
     <td><strong>Where do I learn about all this Eclipse lingo?</strong></td> </tr>
<tr> <td>A:</td>
     <td>See the <a href="http://help.eclipse.org/luna/index.jsp?topic=%2Forg.eclipse.platform.doc.user%2FgettingStarted%2Fqs-01.htm&cp=0_1_0">"Basic Tutorial" section of the <em>Workbench User Guide</em></a>.
</td></tr>
</table><br>


<a name="faq_eclipse_running"></a>
<table class="rounded striped">
<tr> <td>Q:</td>
     <td><strong>How do I run Eclipse--with the right options?</strong></td> </tr>
<tr> <td>A:</td>
     <td>See the "Running Eclipse" section of the 3.5 Release Notes.
To view details about how a currently-running Eclipse was invoked, go to
<b>Help</b> | <b>About Eclipse SDK</b> and click "Configuration Details".
</td></tr>
</table><br>


<a name="faq_eclipse_java_version"></a>
<table class="rounded striped">
<tr> <td >Q:</td>
     <td><strong>How do I tell what Java version Eclipse is running under, and if its 64bit?</strong></td> </tr>
<tr> <td>A:</td>
     <td>Inside Eclipse, go to <b>Help</b> | <b>About Eclipse SDK</b> and
click "Installation Details".  Under "Configuration" tab are the "eclipse.commands"
property and the "java.runtime.*" properties, you will find the relevant information. 
You can also find out under "-arch" your machine architecture, for
example, "X86_64" will indicate that you are running a 64bit Eclipse. 
"java.vm.name" will tell you if the Java being used is a 64bit JVM.
</td></tr>
</table><br>


<a name="faq_eclipse_docs"></a>
<table class="rounded striped">
<tr> <td>Q:</td>
     <td><strong>Where is Eclipse documentation?</strong></td> </tr>
<tr> <td>A:</td>
     <td><a href="http://www.eclipse.org/documentation/main.html">http://www.eclipse.org/documentation/main.html</a>
</td></tr>
</table><br>


<a name="faq_eclipse_multiuser"></a>
<table class="rounded striped">
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

<div class="left-center" data-target="faq_section_acl2">
  <h3>ACL2-related</h3>

  <a name="faq_acl2"></a>
<table class="rounded striped">
<tr> <td>Q:</td>
     <td><strong>What is ACL2?</strong></td> </tr>
<tr> <td>A:</td>
     <td>ACL2 is a programming language, logic, and theorem
prover/checker based on Common Lisp.  See <a
href="http://www.cs.utexas.edu/~moore/acl2/">the ACL2 home page</a> for more
information.</td></tr>
</table>

<a name="faq_car"></a>
<table class="rounded striped">
<tr> <td>Q:</td>
     <td><strong>What is CAR?</strong></td> </tr>
<tr> <td>A:</td>
     <td><u>CAR</u> is an abbreviation we sometimes use to refer to this
(print) book:
<blockquote>
<strong>Computer-Aided Reasoning: An Approach</strong>.<br>
Matt Kaufmann, Panagiotis Manolios, and J Strother Moore.<br>
Kluwer Academic Publishers, June, 2000. (ISBN 0-7923-7744-3)
</blockquote>
See <a href="http://www.cs.utexas.edu/users/moore/publications/acl2-books/car/index.html">J
Moore's page about the book</a> for description and <b>affordable</b>
ordering information.
</tr>
</table>

<a name="faq_acl2_book"></a>
<table class="rounded striped">
<tr> <td >Q:</td>
     <td><strong>What is an ACL2 book?</strong></td> </tr>
<tr> <td >A:</td>
     <td>Basically, an ACL2 book is a bunch of ACL2 definitions (functions,
theorems, proof rules, etc.) that can be easily imported into other ACL2
work.  See <a
href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____BOOKS">:DOC books</a> and
<a href="user_guide.html#guide_book">our guide to book development in ACL2s</a>
for more information.</td></tr>
</table><br>

<a name="faq_acl2_image_outside"></a>
<table class="rounded striped">
<tr> <td>Q:</td>
     <td><strong>Can I use the ACL2 image downloaded by Eclipse outside of Eclipse?</strong></td> </tr>
<tr> <td>A:</td>
     <td>Absolutely!  From the ACL2 perspective, it has everything you would
have building ACL2 yourself. Use the following executable script
<code>myeclipse/plugins/acl2_image.<em>something</em>/run_acl2</code>
instead of the usual <code>saved_acl2</code>
</td></tr>
</table>

<a name="impl_acl2_path"></a>
<table class="rounded striped">
<tr> <td>Q:</td>
<td><strong>Can I use my own version of ACL2? i.e. Finding ACL2 on user's system:</strong></td>
</tr>
<tr> <td>A:</td>
<td>
<p>
This used to be a pain, but it's much simpler now.  First, we have a
preference in the Eclipse preferences (under <b>ACL2s</b> &gt; <b>ACL2</b>)
that allows one to specify the directory that contains your ACL2 image,
whether it's "saved_acl2", "run_acl2", or "bin/acl2.exe" under that
directory.
</p>
<p>

If you don't specify that preference, we check to
see if an "ACL2 Image" is installed in Eclipse, in which case we attempt
to use that.
</p>
<p>
Next we check the environment variable ACL2_HOME for the directory.
Next the java property acl2.home.  Then if none of those is fruitful,
we just try executing "acl2" and see what happens.
</p>
</td></tr>
</table>
</div>

<div class="left-center" data-target="faq_section_java">
<h3>Java-related</h3>

<a name="faq_already_java"></a>
<table class="rounded striped">
<tr> <td>Q:</td>
     <td><strong>Do I already have Java?  What version?</strong></td> </tr>
<tr> <td>A:</td>
     <td>The simple answer is to type <code>java -version</code> at
your operating system's command prompt/terminal/shell.  You might
still have Java if the command is rejected.
See also <a href="faq.html#faq_eclipse_running">How do I run Eclipse--with the
right options?</a> and <a href="faq.html#faq_5.0">Is there a difference
between Java SDK 1.5.0 and 5.0?</a> for more info.
</td></tr>
</table>


<a name="faq_sdk"></a>
<table class="rounded striped">
<tr> <td>Q:</td>
     <td><strong>Do I need the Java SDK or is the JRE fine?</strong></td> </tr>
<tr> <td>A:</td>
     <td>The SDK is only needed if you plan on ever doing any Java
development. The (smaller) JRE should be opted if there is a
choice. It is recommended to have separate eclipse installations
(directories) for Java development and ACL2 development.
</td></tr>
</table><br>


<a name="faq_5.0"></a>
<table class="rounded striped">
<tr> <td>Q:</td>
     <td><strong>Is there a difference between Java SDK 1.5.0 and 5.0?</strong></td> </tr>
<tr> <td>A:</td>
     <td>No.  "5.0" is the version number adjusted for marketing-hype.  See
<a href="http://java.sun.com/j2se/1.5.0/docs/relnotes/version-5.0.html">
"Version 1.5.0 or 5.0?"</a> on Sun's site. Similarily, there is no
difference between Java version "6.0" and JDK/JRE 1.6.0 etc etc.
</td></tr>
</table><br>


<a name="faq_netbeans"></a>
<table class="rounded striped">
<tr> <td>Q:</td>
     <td><strong>What is Netbeans?</strong></td> </tr>
<tr> <td>A:</td>
     <td>Netbeans is a Java development environment that feels much like
Eclipse but is more Java-specific.  You do not need it.
</td></tr>
</table><br>


<a name="faq_oldjava"></a>
<table class="rounded striped">
<tr> <td >Q:</td>
     <td><strong>Can I use a version 1.* of Java?</strong></td> </tr>
<tr> <td >A:</td>
     <td>ACL2s Eclipse plugin uses 1.5
<a href="http://java.sun.com/j2se/1.5.0/docs/relnotes/features.html#lang">language constructs</a> and
<a href="http://java.sun.com/j2se/1.5.0/docs/relnotes/features.html#base_libs">APIs</a>.
You are likely to encounter problems if you use a Java runtime that is
older than "5.0". Moreover due to
a <a href="http://java-performance.info/changes-to-string-java-1-7-0_06/">bug</a>
in JRE 1.7, ACL2s will not work with it. We recommend the use of JRE
1.6 or 1.8.
</td></tr>
</table><br>
</div>

<div class="left-center" data-target="faq_section_acl2s">
<h3>ACL2s-related</h3>

<a name="faq_restrictions"></a>
<table class="rounded striped">
<tr> <td>Q:</td>
     <td><strong>Why won't ACL2s let me do &lt;blah&gt; in a session?</strong></td> </tr>
<tr> <td>A:</td>
     <td><p>In order for the plugin to follow what's going on in ACL2, we
must impose some small limitations.  One, for example, is that it will not let
you break into raw Lisp.  For those interested in this dangerous,
low-level form of interaction, however,
<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____SET-RAW-MODE">raw
mode</a> is supported (because it uses ACL2's reader).  
</p><p>
Another subtle limitation is that--aside from
<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2_____WORMHOLE">wormholes</a>--<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____LD">ld</a>
will only let you read from
<a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2_____star_STANDARD-OI_star_">*standard-oi*</a> at ld level 1.  The reason has to do with undoing and
also <a href="http://www.cs.utexas.edu/users/moore/acl2/v8-0/manual/index.html?topic=ACL2____LD-ERROR-ACTION">ld-error-action</a>.  Another example is that
<tt>good-bye</tt> and other exit commands are disabled to the user,
to encourage use of the user interface operation "Stop session" instead.
</p><p>
For more details, see <a href="http://acl2s.ccs.neu.edu/acl2s/doc/impl.html#impl_hooks">How/what ACL2 functionality is
modified for ACL2s</a>.
</td></tr>
</table><br>

<a name="faq_acl2s_emacs"></a>
<table class="rounded striped">
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
    <ol>
    <li>Open a shell in emacs, start the ACL2 session: <code><em>my_eclipse</em>/plugins/acl2_image.<em>something</em>/run_acl2</code>
    <li>In the ACL2 session, submit the following 3 commands:
</p>
 @({
   (add-include-book-dir :acl2s-modes "my_eclipse/plugins/acl2s_modes_<em>something</em>/") 
   (ld "acl2s-mode.lsp" :dir :acl2s-modes)
   (reset-prehistory t)
   })
</ol>
<p>
If you want more finer control on what gets loaded, you can selectively copy paste the forms in the <tt>acl2s-mode.lsp</tt> that
you need, in the emacs session. For example, say you want a session without trust tags, then except
for the <code>(include-book "ccg" ...)</code> form, submit the rest of the events in <tt>acl2s-mode.lsp</tt>.
</p>
<p>
To reproduce other sessions modes, follow the above, but replace acl2s-mode.lsp by the corresponding session mode file, e.g. acl2s-beginner.lsp
</p>
</td></tr>
</table><br>


<a name="faq_ccg_emacs"></a>
<table class="rounded striped">
<tr> <td>Q:</td>
     <td><strong>Can I use CCG termination analysis and Counterexample
     generation in Emacs (ACL2 session)?</strong></td> </tr>
<tr> <td>A:</td>
<td>
<p>To enable CCG termination analysis, submit the following two commands
  in your emacs ACL2 session.
@({
 (include-book "acl2s/ccg/ccg" :ttags ((:ccg)) :dir :system :load-compiled-file nil)
 (ld "acl2s/ccg/ccg-settings.lsp" :dir :system)
})
</p>
<p>To enable automated counterexample generation, submit the
  following two commands in your emacs ACL2 session.
@({
 (include-book "acl2s/cgen/top" :dir :system :ttags :all)
 (acl2s-defaults :set testing-enabled T)
})
</p>
</td></tr>
</table><br>

</div>

<div class="left-center" data-target="faq_section_installation">
  <a name="faq_section_installation"></a>
<h3>Installation Issues</h3>
<a name="faq_installation_problems"></a>
<table class="rounded striped">
<tr> <td>Q:</td>
     <td><strong>I am having trouble installing/running ACL2s, what should I do?</strong></td> </tr>
<tr> <td>A:</td>
     <td>
<h5>Case: Standard prepackaged installation</h5>
<ul class="disc"> 

<li><b><sf>ACL2 appears to be stuck on starting (Anti-virus software is getting in the way):</sf></b> Do whatever is necessary to give eclipse/plugins/acl2_image*/run_acl2.exe appropriate privileges. In particular, if on Avast Anti-virus, go to settings and uncheck the DeepScreen feature.
</li>

<!-- <li><b>Uncommon Windows Issue</b>If in the .a2s session editor you -->
<!--   find at the top (screen) the following lines: -->
<!--   <pre> -->
<!--     Can't allocate required TLS indexes. -->
<!--     First available index value was 31</pre> -->

<!--   This is -->
<!--   an <a href="http://trac.clozure.com/ccl/ticket/1022">issue</a> with -->
<!--   Clozure Common Lisp. It appears that this happens when the Windows -->
<!--   platform in question has many programs and updates installed. A -->
<!--   possible workaround is to install from scratch a Windows or Linux OS -->
<!--   on a VirtualBox and install ACL2s on it. -->
<!-- </li> -->
<li><b>Old Linux distros</b> On linux machines whose glibc version is older
than 2.15 the current prepackaged tarball does not work. Please contact
the ACL2s maintainer to provide you with a custom ACL2s build.
</li>

</ul>
<br>
<h5> Case: Non-standard Installation:</h5>
<ul class="disc">

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
<br><font size=2>
1. You only installed ACl2s plugin and not the ACL2 image and you forgot to specify the build path in <em>Windows->Preferences->ACL2s->ACL2</em>.
</font>
<br><font size=2>
2. You are using an older ACL2 version, again check the build path in <em>Windows->Preferences->ACL2s->ACL2</em> and modify it to point to a newer version.
</font>
<br><font size=2>
3. You are using a workspace on network share path. Switch to a workspace on local path.
</font>
<br><font size=2>
4. Certain exectuable scripts e.g. run_acl2, dx86cl64, wx86cl64.exe etc in your acl2_image* plugin do not have executable permissions.
</font>

</li>

<li><strong><sf>Java issues:</sf></strong> We recommend JRE version 1.8 (also known as Java 8.0).
Either Java is not
installed (not in PATH) or you are using a version of JRE 1.7 that
has a
<a href="http://java-performance.info/changes-to-string-java-1-7-0_06/">bug</a>
in its string library.</li>

</ul>
</td></tr>
</table><br>
</div>


      </section>
    </div>
  </div>")
 
