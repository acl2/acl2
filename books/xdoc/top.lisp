; XDOC Documentation System for ACL2
; Copyright (C) 2009-2010 Centaur Technology
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

(in-package "XDOC")
(include-book "defxdoc")
(include-book "save")

(defxdoc xdoc
  :short "<em>XDOC</em> is a new mechanism for documenting ACL2 libraries, and
is intended as a replacement for ACL2 facilities such as <tt>defdoc</tt>,
<tt>:doc</tt>, and so on.")


(defxdoc defxdoc
  :parents (xdoc)
  :short "Add some new documentation to the @(see xdoc) database."

  :long "<p><tt>Defxdoc</tt> is the XDOC alternative to ACL2's built-in
<tt>defdoc</tt> command.  To use <tt>defxdoc</tt>, the first step is to include
the <tt>xdoc/defxdoc</tt> book, e.g.,</p>

<code>
(include-book \"xdoc/defxdoc\" :dir :system)
</code>

<p>This book is quite minimal so that it will not interfere with your
libraries.  Once the book is loaded, you can begin documenting your functions
using the <tt>defxdoc</tt> command.</p>

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

 <li><tt>parents</tt> let you associate this documentation with other topics.
A topic can have many parents, but circular parents are not allowed and will
lead to errors when generating documentation.</li>

 <li><tt>short</tt> should be a short description of this topic and should be
suitable for inlining in other pages.  (For instance, it is displayed in the
full index, and as \"hover\" text in the listing frames.)</li>

 <li><tt>long</tt> should be the full, detailed documentation for this
topic.</li>

</ul>

<p>The <tt>short</tt> and <tt>long</tt> strings may be written using the XDOC
@(see markup) language, and may also use @(see preprocessor) commands to insert
function definitions, theorems, topic links, and so on.</p>

<h3>Notes for Advanced Users</h3>

<p>XDOC just stores its documentation in an ordinary ACL2 table, so if you
want to do something like automatically generate documentation from macros,
you might decide to bypass @(srclink defxdoc) and just manipulate the table
directly.</p>")



(defxdoc markup
  :parents (defxdoc)
  :short "XDOC documentation strings are mainly written in a simple XML markup
language.  XML is basically similar to HTML, but is very insistent that tags
begin and end in balance."

  :long "<h3>Formatting Text</h3>

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

<p>The <tt>&lt;tt&gt;</tt> tag is intended for short, inline pieces of code,
such as <tt>(+ 1 x)</tt>.  In contrast, the <tt>&lt;code&gt;</tt> tag is
intended for longer code examples that should be indented and \"preformatted,\"
i.e., newlines and spaces should be preserved.</p>

<p>Note that the @(see preprocessor) allows you to insert function definitions,
theorems, etc., from the ACL2 world, so typically <tt>&lt;code&gt;</tt> is only
needed for examples. </p>

<h3>Adding Hyperlinks</h3>

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

<p>Paragraphs should begin and end with the <tt>&lt;p&gt;</tt> tag.  (You can also
do individual line breaks with <tt>&lt;br/&gt;</tt>.)</p>

<p>For section headings, <tt>&lt;h1&gt;</tt> creates the biggest heading,
<tt>&lt;h2&gt;</tt> the next biggest, and so on.  The smallest heading is
<tt>&lt;h5&gt;</tt>.</p>

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

<p>These framed boxes are generated with the <tt>&lt;box&gt;</tt> tag.</p>")


(defxdoc preprocessor
  :parents (defxdoc)
  :short "In addition to its @(see markup) language, XDOC includes a
preprocessor which can be used to interpret certain directives of the form
<tt>@@(...)</tt>."

  :long "<h3>Functions and Theorems</h3>

<p>To insert function definitions (or pieces of definitions) into your
documentation, you can use:</p>

<ul>
 <li><tt>@@(def fn)</tt>, expands to the definition of the function (or macro)
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
<li><tt>mangled-topic-name</tt> is a canonical, url and file-name friendly
   mangling of <tt>name</tt>'s package and symbol names, and</li>

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

<p>and these can be used to form a custom <tt>&lt;see&gt;</tt> tag.</p>


<h3>Emacs Links</h3>

<p>The <tt>@@(srclink name)</tt> directive inserts a source-code link for users
who have configured their web browser as described in @(see
emacs-web-integration).</p>

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



(defxdoc manual-generation
  :parents (xdoc)

  :short "To construct a manual for your library, the XDOC database can be
saved into <tt>.xml</tt> files, which can then be translated into HTML and
other formats."

  :long "<p>The <tt>defxdoc</tt> command only adds documentation to the
database.  To actually generate a nice manual for your library, there are two
steps.</p>

<ol>
  <li>Save the XDOC database into <tt>.xml</tt> files, then</li>
  <li>Use an XSLT transformer to convert the files into HTML, TEXT, or some
other format.</li>
</ol>

<p>Both of these topics are covered here.</p>

<h3>Saving the XML Files</h3>

<p>The first step in generating a manual is to save the XDOC database into XML
files.  The basic commands for doing this are:</p>

<code>
;; 1. Load your own library.
(include-book \"your-library\")

;; 2. Load the save command.
(include-book \"xdoc/save\" :dir :system)

;; 3. Run the save command to produce the .xml files.
(xdoc::save &lt;dir&gt;)
</code>

<p>where <tt>&lt;dir&gt;</tt> is the directory you want the documentation
written to.  Note that:</p>

<ul>
  <li> <tt>&lt;dir&gt;</tt> must already exist in order for
this to work, and</li>
  <li> files in <tt>dir</tt> <color rgb=\"#ff0000\">may be overwritten!</color></li>
</ul>

<h3>Transforming the XML Files</h3>

<p>Once the documentation has been saved, you can view the resulting <tt>.xml</tt>
files directly in a web browser.</p>

<p>Future work includes providing tools to translate these XML files into other
formats, and for viewing them with some kind of <tt>:xdoc</tt> command from
directly within ACL2.</p>")


(defxdoc emacs-web-integration
  :parents (xdoc)

  :short "Instructions for integrating XDOC web pages with Emacs."

  :long "<p>@(csee preprocessor) directives such as <tt>@@(def
get-xdoc-table)</tt> result in the introduction of special links for Emacs.
With a little work, you can configure your web browser so that clicking on
these links will cause Emacs to directly open up the appropriate source file
and jump to the named function.  Here is what such a link looks like:</p>

@(def get-xdoc-table)

<p>How does this work?</p>

<ul>

 <li>Emacs links are actually links to <tt>xdoc-link</tt> files.</li>

 <li>We instruct your web browser to send these files to Emacs.</li>

 <li>We instruct Emacs to carry out a tags search instead of loading these
files.</li>

</ul>

<p>The net effect is that clicking on these links will send you directly
to the desired function in the source code.  This is really cool, and it
is not too hard to set up.</p>


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
      using the command <tt>etags *.lisp</tt>.</li>

  <li>Tell Emacs to \"visit\" these tags tables with
      <tt>visit-tags-table</tt>.</li>
</ul>

<p>Here's how I do it:</p>

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
But I greatly prefer to use a single Emacs for everything, and just have links
open up in new buffers.</p>

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

<h4>Internet Explorer</h4>

<p>BOZO figure this out</p>



")



