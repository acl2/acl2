; XDOC Documentation System for ACL2
; Copyright (C) 2009-2011 Centaur Technology
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


; topics.lisp
;
; This is the actual xdoc documentation for the xdoc system.  We put the topics
; here, instead of in top.lisp, in a probably silly effort to minimize the load
; time of top.lisp.

(in-package "XDOC")
(include-book "base")


(defxdoc xdoc
  :short "<em>XDOC</em> is a tool for documenting ACL2 libraries, and is
intended as a replacement for ACL2 facilities such as <tt>defdoc</tt>,
<tt>:doc</tt>, and so on."

  :long "<p>To use the XDOC system, the first step is:</p>

<code>
 (include-book \"xdoc/top\" :dir :system)
</code>

<p>This is a regular ACL2 book that loads quickly, requires no ttags, and
provides a (nearly) complete interface to the XDOC system, including:</p>

<ul>
<li>@(see defxdoc), the basic command for adding documentation, which is the
XDOC replacement for ACL2's <tt>defdoc</tt> command.</li>
<li>The <tt>:xdoc</tt> and <tt>:xdoc!</tt> commands for viewing documentation
within the terminal, which are the XDOC replacements for ACL2's <tt>:doc</tt>
and <tt>:doc!</tt> commands.</li>
<li>The @(see save) command, which exports all XDOC documentation as XML files
that can be viewed in a web browser or transformed into formats like HTML.</li>
</ul>

<p>The <tt>:xdoc</tt> command actually consults both the XDOC database, and the
existing ACL2 documentation, so you can always use <tt>:xdoc foo</tt> without
having to know which documentation system was used to document the topic.</p>")


(defxdoc defxdoc
  :parents (xdoc)
  :short "Add documentation to the @(see xdoc) database."

  :long "<p><tt>Defxdoc</tt> is the XDOC alternative to ACL2's built-in
<tt>defdoc</tt> command.  The general usage is:</p>

<code>
 (defxdoc name
   :parents (topic1 topic2 ...)
   :short \"short description\"
   :long \"longer description\")
</code>

<p>All of the keyword arguments are optional.</p>

<ul>
<li><tt>name</tt> is the name of this documentation topic, and should be a
symbol.</li>
<li><tt>parents</tt> let you associate this documentation with other topics.  A
topic can have many parents, but circular parents are not allowed and will lead
to errors when generating documentation.</li>
<li><tt>short</tt> should be a short description of this topic and should be
suitable for inlining in other pages.  (For instance, it is displayed in the
full index, and as \"hover\" text in the listing frames.)</li>
<li><tt>long</tt> should be the full, detailed documentation for this
topic.</li>
</ul>

<p>The <tt>short</tt> and <tt>long</tt> strings may be written using the XDOC
@(see markup) language, and may also use @(see preprocessor) commands to insert
function definitions, theorems, topic links, and so on.</p>

<p>See also <tt>books/xdoc/topics.lisp</tt> for several examples of using
XDOC.</p>

<h3>Notes for Advanced Users</h3>

<p>XDOC just stores its documentation in an ordinary ACL2 table, so if you
want to do something like automatically generate documentation from macros,
you might decide to bypass @(srclink defxdoc) and just manipulate the table
directly.</p>

<p>It is not possible to directly use <tt>defxdoc</tt> from raw Lisp, but
@(see defxdoc-raw) is an alternative which can be used instead.</p>")


(defxdoc markup
  :parents (xdoc)
  :short "XDOC documentation strings are mainly written in a simple XML markup
language."

  :long "<p>XML is basically similar to HTML, but requires that tags begin and
end in balance.</p>

<h3>Formatting Text</h3>

<p>Various tags allow you to control the font:</p>
<ul>
 <li><b>&lt;b&gt;bold&lt;/b&gt;</b></li>
 <li><i>&lt;i&gt;italics&lt;/i&gt;</i></li>
 <li><u>&lt;u&gt;underline&lt;/u&gt;</u></li>
 <li><tt>&lt;tt&gt;typewriter text&lt;/tt&gt;</tt></li>
 <li><color rgb=\"#ff0000\">&lt;color rgb=&quot;#ff0000&quot;&gt;colored text&lt;/color&gt;</color></li>
 <li><sf>&lt;sf&gt;sans-serif&lt;/sf&gt;</sf></li>
</ul>

<h3>Displaying Source Code</h3>

<p>The @(see preprocessor) allows you to insert function definitions, theorems,
etc., from the ACL2 world.  But sometimes you want to write other kinds of code
fragments as examples.</p>

<ul>

<li>Use the <tt>&lt;tt&gt;</tt> tag for short, inline pieces of code,
such as <tt>(+ 1 x)</tt>.</li>

<li>Use the <tt>&lt;code&gt;</tt> tag for longer code examples that should be
indented and \"preformatted,\" i.e., newlines and spaces should be
preserved.</li>

</ul>

<p>Within <tt>&lt;code&gt;</tt> blocks, lisp forms should usually be
<b>indented one space</b> to prevent Emacs problems.  For instance:</p>

<code>
 (defdoc foo
   :long \"&lt;h3&gt;How to format &amp;lt;code&amp;gt; blocks&lt;/h3&gt;

 &lt;p&gt;GOOD -- the form is indented one space:&lt;/p&gt;
 &lt;code&gt;
  (my-lisp-form (foo ...)
                (bar ...))
 &lt;/code&gt;

 &lt;p&gt;BAD -- the form is directly on the left-margin:&lt;/p&gt;
 &lt;code&gt;
 (my-lisp-form (foo ...)
               (bar ...))
 &lt;/code&gt;\")
</code>

<p>Without this space, Emacs can become confused and think that
<tt>(my-lisp-form ...)</tt>, rather than <tt>(defdoc foo ...)</tt>, is the
top-level expression, which can ruin syntax highlighting and also commands like
<tt>C-t e</tt> for sending s-expressions to the <tt>*shell*</tt> window.</p>




<h3>Hyperlinks</h3>

<p><i>Internal links</i> between documentation topics and <i>Emacs
tags-search links</i> into the source code are handled by the @(see
preprocessor).</p>

<p>It is also posible to add <i>external links</i> to web pages with ordinary
HTML-style links, e.g.,</p>

<code>
&lt;a href=\"http://www.centtech.com/\"&gt;Centaur Technology&lt;/a&gt;
</code>

<p>Produces a link to <a href=\"http://www.centtech.com/\">Centaur
Technology</a>.</p>


<h3>Structuring Documents</h3>

<p>For section headings, <tt>&lt;h1&gt;</tt> creates the biggest heading,
<tt>&lt;h2&gt;</tt> the next biggest, and so on.  The smallest heading is
<tt>&lt;h5&gt;</tt>.</p>

<p>Paragraphs should be wrapped in <tt>&lt;p&gt;</tt> and <tt>&lt;/p&gt;</tt>
tags.</p>

<p><tt>&lt;br/&gt;</tt> can be used<br/>
to write haikus and so on<br/>
but is discouraged</p>

<p>Bulleted and numbered lists work as in HTML.  The list itself begins with
<tt>&lt;ul&gt;</tt> (for bulleted lists) or <tt>&lt;ol&gt;</tt> (for numbered lists).
Each list element is an <tt>&lt;li&gt;</tt> tag.  For instance,</p>

<code>
&lt;ul&gt;
  &lt;li&gt;one&lt;/li&gt;
  &lt;li&gt;two&lt;/li&gt;
  &lt;li&gt;three&lt;/li&gt;
&lt;/ul&gt;
</code>

<p>Produces:</p>

<box>
<ul>
  <li>one</li>
  <li>two</li>
  <li>three</li>
</ul>
</box>

<p>You can also use definition lists, which are comprised
of <tt>&lt;dl&gt;</tt>, <tt>&lt;dt&gt;</tt>, and <tt>&lt;dd&gt;</tt> tags.  For
instance,</p>

<code>
&lt;dl&gt;
  &lt;dt&gt;Inputs&lt;/dt&gt;
  &lt;dd&gt;&lt;tt&gt;x&lt;/tt&gt;, the list we are traversing&lt;/dd&gt;
  &lt;dd&gt;&lt;tt&gt;max&lt;/tt&gt;, limit on how many we can accumulate&lt;/dd&gt;
  &lt;dd&gt;&lt;tt&gt;acc&lt;/tt&gt;, accumulator for our results&lt;/dd&gt;
&lt;/dl&gt;
</code>

<p>Produces:</p>

<box>
<dl>
  <dt>Inputs</dt>
  <dd><tt>x</tt>, the list we are traversing</dd>
  <dd><tt>max</tt>, limit on how many we can accumulate</dd>
  <dd><tt>acc</tt>, accumulator for our results</dd>
</dl>
</box>

<p>These framed boxes are generated with the <tt>&lt;box&gt;</tt> tag.</p>

<p>It's relatively easy to add new tags.  We'll probably add some kind of image
support in the future, and maybe other tags that users want.</p>")


(defxdoc preprocessor
  :parents (xdoc)
  :short "In addition to its @(see markup) language, XDOC includes a
preprocessor which can be used to interpret certain directives of the form
<tt>@@(...)</tt>."

  :long "<h3>Functions and Theorems</h3>

<p>To insert function definitions (or pieces of definitions) into your
documentation, you can use:</p>

<ul>
 <li><tt>@@(def fn)</tt>, insert the definition of the function (or macro)
     <i>fn</i></li>
 <li><tt>@@(body fn)</tt>, just the body of <i>fn</i></li>
 <li><tt>@@(formals fn)</tt>, just the formals of <i>fn</i></li>
 <li><tt>@@(measure fn)</tt>, just the measure of <i>fn</i></li>
 <li><tt>@@(call fn)</tt>, a generic function call of <i>fn</i></li>
</ul>

<p>We expect that <tt>def</tt> and <tt>body</tt> directives will
expand to large code fragments, so they are automatically wrapped in
<tt>&lt;code&gt;</tt> blocks and other formatting.</p>

<p>The <tt>call</tt> directive is automatically wrapped in &lt;tt&gt;
tags, i.e., <tt>@@(call fib)</tt> might become &lt;tt&gt;(fib x)&lt;/tt&gt;.
An alternative is to use <tt>@@(ccall fib)</tt>, for \"code call,\" which
inserts &lt;code&gt; tags instead.</p>

<p>The other directives just become plain text, and you can wrap whatever
formatting commands you like around them and use them inline in paragraphs,
etc.</p>

<p>You can also insert theorems:</p>

<ul>
 <li><tt>@@(thm name)</tt>, expands to the statement of the theorem <i>name</i></li>
</ul>

<p>As with <tt>def</tt> and <tt>body</tt> directives, <tt>thm</tt> directives
automatically insert <tt>&lt;code&gt;</tt> blocks.</p>

<h3>Documentation Links</h3>

<p>The easiest way to link between topics is to use <tt>@@(see name)</tt>,
which expands into a link to <tt>name</tt>.  The text shown to the reader is
just the name of the topic, in lower case.  Note also that <tt>@@(csee
name)</tt> can be used for links whose first letter should be capitalized.</p>

<p>For most purposes, <tt>@@(see name)</tt> is adequate and it is also
recommended.  Finer-grained control (e.g., changing the link text) is also
possible, but requires some considerations for mangling file names, etc.
Basically, <tt>@@(see name)</tt> expands to:</p>

<code>
&lt;see topic=\"mangled-topic-name\"&gt;printed-topic-name&lt;/see&gt;
</code>

<p>Where:</p>

<ul>
<li><tt>mangled-topic-name</tt> is a canonical, url/file-name friendly,
   human-hostile mangling of <tt>name</tt>'s package and symbol names, and</li>

<li><tt>printed-topic-name</tt> is an XML-escaped (i.e., \"&lt;\" becomes
   \"&amp;lt;\") variant of <tt>name</tt> which, depending on the package of the
   current topic's name, may or may not include the package portion of
   <tt>name</tt>.</li>
</ul>

<p>So, to support custom links, we provide</p>

<ul>
 <li><tt>@@(url name)</tt>, which expands to <tt>mangled-topic-name</tt></li>
 <li><tt>@@(sym name)</tt>, which expands to <tt>printed-topic-name</tt></li>
 <li><tt>@@(csym name)</tt>, like <tt>sym</tt>, but with the first letter capitalized</li>
</ul>

<p>and these can be used to write your own <tt>&lt;see&gt;</tt> tags.</p>


<h3>Emacs Links</h3>

<p>The <tt>@@(srclink name)</tt> directive inserts a source-code link for users
who have configured their web browser as described in @(see emacs-links).</p>

<p>It is often unnecessary to use <tt>srclink</tt> directly, because these
links are automatically inserted by the <tt>@@(def fn)</tt> and <tt>@@(thm
foo)</tt> directives.  One good reason to use <tt>srclink</tt> is to link to
macros like @(srclink defxdoc), which often are written using backquote and
hence do not display nicely.</p>

<p>Source links are sometimes inappropriate, e.g., for definitions or theorems
that are generated by macros.  You can suppress the automatic source links on
<tt>def</tt> and <tt>thm</tt> commands by using <tt>@@(gdef fn)</tt> or
<tt>@@(gthm foo)</tt> instead, which stand for \"generated def\" and
\"generated thm.\"</p>



<h3>Escaping of @</h3>

<p>Since <tt>@@(</tt> is intercepted by the preprocessor, you may occasionally
need to escape it.  You can write <tt>@@@@</tt> to generate a single <tt>@</tt>
sign.</p>

<p>Besides <tt>@@(</tt> and <tt>@@@@</tt>, the preprocessor leaves any other uses
of <tt>@</tt> in tact.  So, most uses of <tt>@</tt>, such as in email
addresses, do not need to be escaped.</p>")


(defxdoc save
  :parents (xdoc)
  :short "Saves the XDOC database as <tt>.xml</tt> files (which can also be
translated into HTML or other formats)."

  :long "<p>Once you have documented your library with @(see defxdoc), you may
wish to create a manual that can be viewed from a web browser.</p>


<h3>Saving a Manual</h3>

<p>The <tt>xdoc::save</tt> command allows you to save all of the documented
topics as <tt>.xml</tt> files.  Here's an example:</p>

<code>
 (xdoc::save \"/home/jared/mylib-manual\")
</code>

<p>The argument is the name of a directory where the documentation should be
saved.  If the directory does not exist, it will be created.  If there are
files in the directory, they <color rgb=\"#ff0000\">may be
overwritten</color>.</p>


<h3>Structure of a Manual</h3>

<p>The resulting <tt>mylib-manual</tt> directory includes:</p>

<ul>

<li><tt>xml/</tt>, a subdirectory with a <tt>.xml</tt> file for each topic and
some supporting files, and</li>

<li><tt>Makefile</tt>, a Makefile for converting these files into other
formats, and</li>

<li><tt>preview.html</tt>, a web page that lets you directly view the XML files
using your web browser.</li>

</ul>

<p>Many web browsers can now directly display XML files.  So, you may be able
to view <tt>preview.html</tt> without any additional steps.</p>


<h3>HTML and Other Formats</h3>

<p>You can generate a plain HTML or TEXT version of your manual by using
<tt>make html</tt> or <tt>make text</tt>.  We might add support for TEXINFO or
other formats in the future.</p>

<p>After running <tt>make html</tt>, you may wish to open <tt>frames2.html</tt>
and <tt>frames3.html</tt>, which allow you to navigate the HTML manual much
like <tt>preview.html</tt> allows you to navigate the XML version.</p>

<p>Converting to HTML is a good idea because it ensures that all of your tags
are balanced on every page.  Without this sanity check, your manual might
contain errors that will prevent some topics from being loaded in a web
browser.</p>")


(defxdoc emacs-links
  :parents (xdoc)
  :short "Instructions for integrating XDOC web pages with Emacs."

  :long "<p>@(csee preprocessor) directives such as <tt>@@(def
get-xdoc-table)</tt> result in the introduction of special links for Emacs.  It
is possible to configure your web browser so that clicking on these links will
cause Emacs to directly open up the appropriate source file and jump to the
named function.  Here is what such a link looks like:</p>

@(def get-xdoc-table)

<p>How does this work?</p>

<ul>

 <li>These Emacs links point to <tt>xdoc-link</tt> files.</li>

 <li>We instruct your web browser to send these files to Emacs.</li>

 <li>We instruct Emacs to carry out a tags search instead of loading these
files.</li>

</ul>

<p>The net effect is that clicking on these links will send you directly to the
desired function in the source code.  This can be <em>really</em> slick, and
depending on your web browser, it may not be too hard to set up.</p>


<h2>Configuring Emacs</h2>

<h4>Loading the XDOC Elisp</h4>

<p>The XDOC directory includes a file called <tt>xdoc.el</tt>, which tells
emacs what to do with these <tt>xdoc-link</tt> files.  To tell emacs to load
this file at startup, you can just add a command to your <tt>.emacs</tt> file
such as:</p>

<code>
 (load \"/path/to/xdoc/xdoc.el\")
</code>


<h4>Managing your TAGS tables</h4>

<p>For emacs to make sense of the links you follow, it will need to have the
appropriate <a
href=\"http://www.gnu.org/software/emacs/manual/html_node/emacs/Tags.html\">tags
tables</a> loaded for all of the libraries you are using.</p>

<p>If you aren't familiar with tags, you basically just need to:</p>
<ul>
  <li>Occasionally generate <tt>TAGS</tt> files for your libraries,
      using the command <tt>etags *.lisp</tt> or similar.</li>

  <li>Tell Emacs to \"visit\" these tags tables with
      <tt>visit-tags-table</tt>.</li>
</ul>

<h5>Jared's Approach:</h5>

<ul>

<li>I add a <tt>TAGS</tt> target to my Makefiles, so that when I build my
library the <tt>etags *.lisp</tt> command is re-run and the <tt>TAGS</tt>
file is kept up to date.  The Makefile syntax is:

<code>
TAGS: $(wildcard *.lisp)
      etags *.lisp
</code></li>

<li>Then, in my <tt>.emacs</tt> file, I have a series of commands like the
following:

<code>
 (ignore-errors (visit-tags-table \"/path/to/acl2/TAGS\"))
 (ignore-errors (visit-tags-table \"/path/to/acl2/books/xdoc/TAGS\"))
 (ignore-errors (visit-tags-table \"/path/to/my/stuff/TAGS\"))
</code>

This ensures that the relevant <tt>TAGS</tt> files are loaded every time I
start Emacs.  The use of <tt>ignore-errors</tt> prevents Emacs from complaining
if one of these <tt>TAGS</tt> files was deleted in a \"make clean\" or
similar.</li>

<li>One final addition to the <tt>.emacs</tt> file is:

<code>
 (setq tags-revert-without-query t)
</code>

which tells Emacs to go ahead and reload these files when they are rebuilt
by Make, instead of prompting you if you want to reload them.</li>

</ul>


<h4>Setting up Emacsclient (recommended)</h4>

<p>You can set things up so that links open up in <b>new instances</b> of
Emacs, or in <b>new buffers</b> of an already-running Emacs.  If you want
everything to open up in a new instance of Emacs, you can skip this section.
But I prefer to use a single Emacs for everything, and just have links open up
in new buffers.</p>

<p>This is quite easy.  First, add <tt>(server-start)</tt> to your
<tt>.emacs</tt> file and restart Emacs.</p>

<p>Next, to ensure everything is working properly, launch a separate terminal
and type:</p>

<code>
emacsclient --no-wait my-file
</code>

<p>If all is well, <tt>my-file</tt> will be loaded into your already-running
emacs as a new buffer.</p>



<h2>Configuring the Web Browser</h2>

<p>The last thing we need to do is instruct your web browser to send
<tt>xdoc-link</tt> files to Emacs.  How this is done depends on your
web browser.</p>

<h4>Firefox (works)</h4>

<p><b>Note:</b> I have not yet found a way to get Firefox to call
<tt>emacsclient</tt> with the <tt>--no-wait</tt> option.  To work around this,
I wrote a trivial script called <tt>emacsclient-wrapper.sh</tt>, which is
included in the XDOC directory.</p>

<ol>

<li>Install the <a
href=\"https://addons.mozilla.org/en-US/firefox/addon/4498\">MIME Edit</a>
firefox plugin.  This is quite easy, but requires firefox to be restarted.</li>

<li>Use MIME-EDIT to tell firefox to give <tt>.xdoc-link</tt> files to emacs:

<ul>
  <li>Choose (from the menu bar): <tt>Tools</tt>, <tt>MIME Edit</tt></li>
  <li>Pick the <tt>Edit</tt> tab</li>
  <li>Click <tt>New Type</tt></li>
  <li>MIME Type: <u>application/acl2-xdoc-link</u></li>
  <li>Description: <u>Link to ACL2 Source Code</u></li>
  <li>Extension: <u>xdoc-link</u></li>
  <li>When encountered, open file with <u>/path/to/emacsclient-wrapper.sh</u></li>
</ul>

</li>
</ol>

<h4>Safari (not working yet)</h4>

<p>I am mainly unfamiliar with MacOS, so perhaps someone can figure this out.
I did not see any mechanism to edit MIME types directly within Safari.  However,
there is a free program called <a href=\"http://mac.clauss-net.de/misfox/\">MisFox</a>
program which allows you to set up file mappings.  But its \"choose\" dialog for
picking the program refuses to accept <tt>emacsclient</tt> or a wrapper script, for
whatever reason that I do not understand.</p>

<p>I lost access to the Mac laptop I was using, maybe somemone else can figure
this out.</p>

<h4>Internet Explorer</h4>

<p>Someone else will have to figure this out.</p>


<h2>Possibly Necessary: Configuring the Web Server</h2>

<p>This step shouldn't be needed if you're viewing the documentation on your
hard drive.  But if you are using a web server like Apache to serve your
documentation, you may need to use something like:</p>

<code>
AddType application/x-acl2-xdoc-link .xdoc-link
</code>

<p>to your <tt>httpd.conf</tt> or an <tt>.htaccess</tt> file as appropriate.
Without this step, your web server might report that <tt>.xdoc-link</tt> files
are just text files to the web browser, and the web browser will not load them
with the content-handler.</p>")

