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
(include-book "import-acl2doc")  ;; For base acl2 documentation
(program)

(defxdoc xdoc
  :short "<i>XDOC</i> is a tool for documenting ACL2 libraries, and is
intended as a replacement for ACL2 facilities such as @('defdoc'), @(':doc'),
and so on."

  :long "<p>To use the XDOC system, the first step is:</p>

@({
 (include-book \"xdoc/top\" :dir :system)
})

<p>This is a regular ACL2 book that loads quickly, requires no ttags, and
provides a (nearly) complete interface to the XDOC system, including:</p>

<ul>

<li>@(see defxdoc), the basic command for adding documentation, which is the
XDOC replacement for ACL2's @('defdoc') command.</li>

<li>The @(':xdoc') command for viewing documentation within the terminal, which
is the XDOC replacement for ACL2's @(':doc') command.</li>

<li>The @(see save) command, which exports all XDOC documentation as XML files
that can be viewed in a web browser or transformed into formats like HTML.</li>

</ul>

<p>The @(':xdoc') command consults the XDOC database <b>and</b> ACL2's
@(':doc') database, so you can always use @(':xdoc foo') without having to know
which documentation system was used to document the topic.</p>")


(defxdoc defxdoc
  :parents (xdoc)
  :short "Add documentation to the @(see xdoc) database."

  :long "<box><p>Note: @('defxdoc') is very basic.  You will usually want to
use @(see defsection) instead.</p></box>

<p>@('Defxdoc') is the XDOC alternative to ACL2's built-in @('defdoc') command.
The general form is:</p>

@({
 (defxdoc name
   :parents (topic1 topic2 ...)
   :short \"short description\"
   :long \"longer description\")
})

<p>All of the keyword arguments are optional.</p>

<ul>

<li>@('name') is the name of this documentation topic, and should be a
symbol.</li>

<li>@('parents') let you associate this documentation with other topics.  A
topic can have many parents, but circular parents are not allowed and will lead
to errors when generating documentation.</li>

<li>@('short') should be a short description of this topic and should be
suitable for inlining in other pages.  For instance, it is displayed in the
full index, and as \"hover\" text in the navigation page.</li>

<li>@('long') should be the full, detailed documentation for this topic.</li>

</ul>

<p>The @('short') and @('long') strings may be written using the XDOC @(see
markup) language, and may also use @(see preprocessor) commands to insert
function definitions, theorems, topic links, and so on.</p>

<p>Many examples of using XDOC can be found throughout the <tt>acl2/books</tt>
directory.  See for instance the @(see acl2::str) or @(see acl2::osets)
libraries.</p>

<h3>Note for Advanced Users</h3>

<p>XDOC just stores its documentation in an ordinary ACL2 table, so if you want
to do something like automatically generate documentation from macros, you
might decide to bypass @('defxdoc') and just manipulate the table directly.</p>

<p>It is not possible to directly use @('defxdoc') from raw Lisp, but you can
use @(see defxdoc-raw) instead.</p>")


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

<p>The raw markup options are:</p>

<ul>

<li>Use the @('<tt>') tag for short, inline pieces of code, such as <tt>(+ 1
x)</tt>.</li>

<li>Use the @('<code>') tag for longer code examples that should be indented
and \"preformatted,\" i.e., newlines and spaces should be preserved.</li>

</ul>

<p><b>However</b>, it's often better to use the preprocessor's
<tt>@@('...')</tt> and <tt>@@({...})</tt> macros.  These are nice because they
automatically escape special HTML characters like &lt; into &amp;lt;, and also
automatically add hyperlinks to documented functions.</p>

<p>If you do decide to write raw @('<code>') blocks, your lisp forms should
usually be <b>indented one space</b> to prevent Emacs problems.  For
instance:</p>

@({
 (defxdoc foo
   :long \"<h3>How to format @('<code>') blocks</h3>

 <p>GOOD -- the form is indented one space:</p>
 <code>
  (my-lisp-form (foo ...)
                (bar ...))
 </code>

 <p>BAD -- the form is directly on the left-margin:</p>
 <code>
 (my-lisp-form (foo ...)
               (bar ...))
 </code>
})

<p>Without this leading space, Emacs can become confused and think that
@('(my-lisp-form ...)'), rather than @('(defxdoc foo ...)'), is the top-level
expression.  This can ruin syntax highlighting and also commands like @('C-t
e') for sending s-expressions to the @('*shell*') window.</p>




<h3>Hyperlinks</h3>

<p><i>Internal links</i> between documentation topics and <i>Emacs
tags-search links</i> into the source code are handled by the @(see
preprocessor).</p>

<p>You can add <i>external links</i> to web pages with ordinary HTML-style
links, e.g.,</p>

@({
<a href=\"http://www.centtech.com/\">Centaur Technology</a>
})

<p>Produces a link to <a href=\"http://www.centtech.com/\">Centaur
Technology</a>.</p>


<h3>Structuring Documents</h3>

<p>For section headings,</p>
<ul>
 <li>@('<h1>') creates the biggest heading,</li>
 <li>@('<h2>') the next biggest,</li>
 <li>... and so on ...</li>
 <li>@('<h5>') is the smallest heading.</li>
</ul>

<p>@('<p>') tags should be put around paragraphs.</p>

<blockquote>@('<blockquote>') can be used to create indented paragraphs like
this one.  (Let's put enough text here to make it word-wrap.  Mumble mumble
mumble.  Mumble.  Mumble mumble.)</blockquote>

<p>@('<br/>') can be used<br/>
to write haikus and so on<br/>
but is discouraged</p>

<p>Bulleted and numbered lists work as in HTML.  The list itself begins with
@('<ul>') (for bulleted lists) or @('<ol>') (for numbered lists).  Each list
element is an @('<li>') tag.  For instance,</p>

@({
<ul>
  <li>one</li>
  <li>two</li>
  <li>three</li>
</ul>
})

<p>Produces:</p>

<box>
<ul>
  <li>one</li>
  <li>two</li>
  <li>three</li>
</ul>
</box>

<p>You can also use definition lists, which are comprised of @('<dl>'),
@('<dt>'), and @('<dd>') tags.  For instance,</p>

@({
<dl>
  <dt>Inputs</dt>
  <dd><tt>x</tt>, the list we are traversing</dd>
  <dd><tt>max</tt>, limit on how many we can accumulate</dd>
  <dd><tt>acc</tt>, accumulator for our results</dd>
</dl>
})

<p>Produces:</p>

<box>
<dl>
  <dt>Inputs</dt>
  <dd><tt>x</tt>, the list we are traversing</dd>
  <dd><tt>max</tt>, limit on how many we can accumulate</dd>
  <dd><tt>acc</tt>, accumulator for our results</dd>
</dl>
</box>

<p>These framed boxes are generated with the @('<box>') tag.</p>

<p>It's relatively easy to add new tags.  We'll probably add some kind of image
support in the future, and maybe other tags that users want.</p>")


(defxdoc preprocessor
  :parents (xdoc)
  :short "In addition to its @(see markup) language, XDOC includes a
preprocessor which can be used to interpret certain directives of the form
@('@(...)')."

  :long "<h3>Functions and Theorems</h3>

<p>To look up function definitions (or pieces of definitions) from the ACL2
world and insert them into your documentation, you can use:</p>

<ul>
 <li>@('@(def fn)'), insert the definition of <i>fn</i><br/>
     (also works for theorems, macros, ...)</li>
 <li>@('@(body fn)'), just the body of <i>fn</i></li>
 <li>@('@(formals fn)'), just the formals of <i>fn</i></li>
 <li>@('@(measure fn)'), just the measure of <i>fn</i></li>
 <li>@('@(call fn)'), a generic function call of <i>fn</i></li>
</ul>

<p>We expect that @('def') and @('body') directives will expand to large code
fragments, so they are automatically wrapped in @('<code>') blocks.</p>

<p>The @('call') directive is automatically wrapped in @('<tt>') tags, i.e.,
@('@(call fib)') might become @('<tt>(fib x)</tt>').  An alternative is to use
@('@(ccall fib)'), for \"code call,\" which inserts @('<code>') tags instead;
this could be more appropriate for functions with many arguments.</p>

<p>The other directives just become plain text, and you can wrap whatever
formatting commands you like around them and use them inline in paragraphs,
etc.</p>

<h3>Adding Examples or Code Fragments</h3>

<p>There's a special syntax to put in \"raw\" text.  This is especially
useful for examples and code fragments.</p>

<ul>
<li><tt>@@('...')</tt> inserts @('...') into @('<tt>') tags.</li>
<li><tt>@@({...})</tt> inserts @('...') into @('<code>') tags.</li>
</ul>

<p>These have a special feature for automatically linking to documented topics.
For instance, <tt>@@('consp x')</tt> produces @('(consp x)'), and
<tt>@@({ (consp x) })</tt> produces:</p>

@({
 (consp x)
})


<h3>Documentation Links</h3>

<p>The easiest way to link between topics is to use @('@(see name)'), which
expands into a link to @('name').  The text shown to the reader is just the
name of the topic, in lower case.  Note also that @('@(csee name)') can be used
for links whose first letter should be capitalized.</p>

<p>For most purposes, @('@(see name)') is adequate and it is also recommended.
Finer-grained control (e.g., changing the link text) is also possible, but then
you have to understand how file names get mangled.  The basic story is that
@('@(see name)') expands to:</p>

@({
<see topic=\"mangled-topic-name\">printed-topic-name</see>
})

<p>Where:</p>

<ul>

<li>@('mangled-topic-name') is a canonical, url/file-name friendly,
human-hostile mangling of @('name')'s package and symbol names, and</li>

<li>@('printed-topic-name') is an XML-escaped variant of @('name'), e.g., where
@('<') becomes @('&lt;'), etc.; depending on the package of the current topic's
name, it may or may not include the package portion of @('name').</li>

</ul>

<p>So, to support custom links, we provide</p>

<ul>
 <li>@('@(url name)'), which expands to @('mangled-topic-name')</li>
 <li>@('@(sym name)'), which expands to @('printed-topic-name')</li>
 <li>@('@(csym name)'), like @('sym'), but with the first letter capitalized</li>
</ul>

<p>You can use these to write your own @('<see>') tags.  You should probably
<i>never</i> write a @('<see>') tag yourself without using @('@(url ...)').</p>


<h3>Emacs Links</h3>

<p>The @('@(srclink name)') directive inserts a source-code link for users who
have configured their web browser as described in @(see emacs-links).</p>

<p>It is often unnecessary to use @('srclink') directly, because these links
are automatically inserted by @('@(def fn)').  One good reason to use
@('srclink') is to link to macros like @(srclink defxdoc), which often are
written using backquote and hence do not display nicely.</p>

<p>Source links are sometimes inappropriate, e.g., for definitions or theorems
that are generated by macros.  You can suppress the automatic source links on
@('def') commands by using @('@(gdef fn)') instead.  This stands for
\"generated definition.\"</p>


<h3>Escaping of @</h3>

<p>Since @('@(') is intercepted by the preprocessor, you may occasionally need
to escape it.  You can write @('@@') to generate a single @('@') sign.</p>

<p>Besides @('@(') and @('@@'), the preprocessor leaves any other uses of
@('@') in tact.  So, most uses of @('@'), such as in email addresses, do not
need to be escaped.</p>")


(defxdoc save
  :parents (xdoc)
  :short "Saves the XDOC database as @('.xml') files (which can also be
translated into HTML or other formats)."

  :long "<p>Once you have documented your library with @(see defxdoc), you may
wish to create a manual that can be viewed from a web browser.</p>


<h3>Saving a Manual</h3>

<p>The @('xdoc::save') command allows you to save all of the documented topics
as @('.xml') files.  Here's an example:</p>

@({
 (xdoc::save \"/home/jared/mylib-manual\")
})

<p>The argument is the name of a directory where the documentation should be
saved.  If the directory does not exist, it will be created.  If there are
files in the directory, they <color rgb=\"#ff0000\">may be
overwritten</color>.</p>


<h3>Structure of a Manual</h3>

<p>The resulting @('mylib-manual') directory includes:</p>

<ul>

<li>@('xml/'), a subdirectory with a @('.xml') file for each topic and some
supporting files, and</li>

<li>@('Makefile'), a Makefile for converting these files into other formats,
and</li>

<li>@('preview.html'), a web page that lets you directly view the XML files
using your web browser.</li>

</ul>

<p>Many web browsers can now directly display XML files.  So, you may be able
to view @('preview.html') without any additional steps.</p>


<h3>HTML and Other Formats</h3>

<p>You can generate a plain HTML or TEXT version of your manual by using
@('make html') or @('make text') from within the directory target of the above
mentioned @('xdoc::save') command (in this example, the @('mylib-manual')
directory).  We might add support for TEXINFO or other formats in the
future.</p>

<p>After running @('make html'), you may wish to open @('frames2.html') and
@('frames3.html'), which allow you to navigate the HTML manual much like
@('preview.html') allows you to navigate the XML version.  These pages accept
an optional argument named <tt>topic</tt> that tells the browser to
automatically go to a particular topic.  For example, one can go to the
<tt>XDOC::save</tt> topic by using the url
<tt>frames3.html?topic=XDOC____SAVE.html</tt>.</p>

<p>Converting to HTML is a good idea because it ensures that all of your tags
are balanced on every page.  Without this sanity check, your manual might
contain errors that will prevent some topics from being loaded in a web
browser.</p>

<p>Creating the HTML code requires Xalan-C++.  Xalan is distributed with many
Linux distributions.  For example, on Ubuntu, one can run <tt>sudo apt-get
install xalan</tt> to install it.  Alternatively, see <a
href=\"http://xml.apache.org/xalan-c/\">Apache Xalan</a> to download.  We have
accomodated the various versions of Xalan that we know about and use, but we
welcome modifications to file <tt>support/Makefile-trans</tt> if you wish to
use a version we do not currently support.</p>")


(defxdoc emacs-links
  :parents (xdoc)
  :short "Instructions for integrating XDOC web pages with Emacs."

  :long "<p>@(csee preprocessor) directives such as @('@(def get-xdoc-table)')
result in the introduction of special links for Emacs.  It is possible to
configure your web browser so that clicking on these links will cause Emacs to
directly open up the appropriate source file and jump to the named function.
Here is what such a link looks like:</p>

@(def get-xdoc-table)

<p>How does this work?</p>

<ul>

<li>These Emacs links point to @('xdoc-link') files.</li>

<li>We instruct your web browser to send these files to Emacs.</li>

<li>We instruct Emacs to carry out a tags search instead of loading these
files.</li>

</ul>

<p>The net effect is that clicking on these links will send you directly to the
desired function in the source code.  This can be <i>really</i> slick, and
depending on your web browser, it may not be too hard to set up.</p>


<h2>Configuring Emacs</h2>

<h4>Loading the XDOC Elisp</h4>

<p>The XDOC directory includes a file called @('xdoc.el'), which tells emacs
what to do with these @('xdoc-link') files.  To tell emacs to load this file at
startup, you can just add a command to your @('.emacs') file such as:</p>

@({
 (load \"/path/to/xdoc/xdoc.el\")
})


<h4>Managing your TAGS tables</h4>

<p>For emacs to make sense of the links you follow, it will need to have the
appropriate <a
href=\"http://www.gnu.org/software/emacs/manual/html_node/emacs/Tags.html\">tags
tables</a> loaded for all of the libraries you are using.</p>

<p>If you aren't familiar with tags, you basically just need to:</p>

<ul>

<li>Occasionally generate @('TAGS') files for your libraries, using the command
@('etags *.lisp') or similar.</li>

<li>Tell Emacs to \"visit\" these tags tables with @('visit-tags-table').</li>

</ul>

<h5>Jared's Approach:</h5>

<ul>

<li>I add a @('TAGS') target to my Makefiles, so that when I build my library
the @('etags *.lisp') command is re-run and the @('TAGS') file is kept up to
date.  The Makefile syntax is:

@({
TAGS: $(wildcard *.lisp)
      etags *.lisp
})</li>

<li>Then, in my @('.emacs') file, I have a series of commands like the
following:

@({
 (ignore-errors (visit-tags-table \"/path/to/acl2/TAGS\"))
 (ignore-errors (visit-tags-table \"/path/to/acl2/books/xdoc/TAGS\"))
 (ignore-errors (visit-tags-table \"/path/to/my/stuff/TAGS\"))
})

This ensures that the relevant @('TAGS') files are loaded every time I start
Emacs.  The use of @('ignore-errors') prevents Emacs from complaining if one of
these @('TAGS') files was deleted in a \"make clean\" or similar.</li>

<li>One final addition to the @('.emacs') file is:

@({
 (setq tags-revert-without-query t)
})

which tells Emacs to go ahead and reload these files when they are rebuilt by
Make, instead of prompting you if you want to reload them.</li>

</ul>


<h4>Setting up Emacsclient (recommended)</h4>

<p>You can set things up so that links open up in <b>new instances</b> of
Emacs, or in <b>new buffers</b> of an already-running Emacs.  If you want
everything to open up in a new instance of Emacs, you can skip this section.
But I prefer to use a single Emacs for everything, and just have links open up
in new buffers.</p>

<p>This is quite easy.  First, add @('(server-start)') to your @('.emacs') file
and restart Emacs.</p>

<p>Next, to ensure everything is working properly, launch a separate terminal
and type:</p>

@({
emacsclient --no-wait my-file
})

<p>If all is well, @('my-file') will be loaded into your already-running emacs
as a new buffer.</p>



<h2>Configuring the Web Browser</h2>

<p>The last thing we need to do is instruct your web browser to send
@('xdoc-link') files to Emacs.  How this is done depends on your web
browser.</p>

<p>Here are old instructions for Firefox, but I don't believe mime-edit still
exists/works, so you may need to do something else now.</p>

<p><b>Note:</b> I have not yet found a way to get Firefox to call
@('emacsclient') with the @('--no-wait') option.  To work around this, I wrote
a trivial script called @('emacsclient-wrapper.sh'), which is included in the
XDOC directory.</p>

<ol>

<li>Install the <a
href=\"https://addons.mozilla.org/en-US/firefox/addon/4498\">MIME Edit</a>
firefox plugin.  This is quite easy, but requires firefox to be restarted.</li>

<li>Use MIME-EDIT to tell firefox to give @('.xdoc-link') files to emacs:

<ul>
  <li>Choose (from the menu bar): @('Tools'), @('MIME Edit')</li>
  <li>Pick the @('Edit') tab</li>
  <li>Click @('New Type')</li>
  <li>MIME Type: <u>application/acl2-xdoc-link</u></li>
  <li>Description: <u>Link to ACL2 Source Code</u></li>
  <li>Extension: <u>xdoc-link</u></li>
  <li>When encountered, open file with <u>/path/to/emacsclient-wrapper.sh</u></li>
</ul>

</li>
</ol>

<h2>Possibly Necessary: Configuring the Web Server</h2>

<p>This step shouldn't be needed if you're viewing the documentation on your
hard drive.  But if you are using a web server like Apache to serve your
documentation, you may need to use something like:</p>

@({
AddType application/x-acl2-xdoc-link .xdoc-link
})

<p>to your @('httpd.conf') or an @('.htaccess') file as appropriate.  Without
this step, your web server might report that @('.xdoc-link') files are just
text files to the web browser, and the web browser will not load them with the
content-handler.</p>")



(defxdoc extract-keyword-from-args
  :parents (defsection) ; bozo hrmn, where should this go, really?
  :short "Get the value for a keyword argument like @(':foo value')."

  :long "<p>@(call extract-keyword-from-args) is given @('kwd'), which should
be a keyword symbol, and a list of @('args') which are typically the @('&rest
args') given to a macro.  It scans the list of @('args'), looking for the
indicated keyword, and returns @('(kwd . value)'), or @('nil') if no such
keyword is found.  For instance,</p>

@({
 (extract-keyword-from-args :bar '(:foo 3 :bar 5 :baz 7))
   -->
 (:bar . 5)
})

<p>This function is mainly useful for writing macros that mix @('&rest') parts
with keyword arguments.  See also @(see throw-away-keyword-parts).</p>

@(def extract-keyword-from-args)")


(defxdoc throw-away-keyword-parts
  :parents (defsection) ; bozo hrmn, where should this go, really?
  :short "Throw away any keyword arguments and their values from a macro
argument list."

  :long "<p>@(call throw-away-keyword-parts) is given a list of arguments that
are typically the @('&rest args') given to a macro.  It scans the arguments for
any keyword symbols such as @(':foo'), and throws away both the keyword and the
argument that follows it.  For instance,</p>

@({
 (throw-away-keyword-parts '(x y z :foo 3 :bar 5 blah blah blah))
   -->
 '(x y z blah blah blah)
})

<p>This function is mainly useful for writing macros that mix @('&rest') parts
with keyword arguments.  See also @(see extract-keyword-from-args).</p>

@(def throw-away-keyword-parts)")


(defxdoc defsection
  :parents (xdoc)
  :short "Fancy @('(encapsulate nil ...)') with a name and @(see xdoc)
support."

  :long "<p>The main reasons to use @('defsection') instead of @('(encapsulate
nil ...)')</p>

<ul>
 <li>It is easier to identify in the @(':pbt') history,</li>
 <li>It indents more nicely than @('encapsulate') in a vanilla emacs,</li>
 <li>It settles the question of where to put the @(see defxdoc) command, and</li>
 <li>It can automatically add the definitions/theorems you supply into the
     documentation for your section.</li>
</ul>

<p>General form:</p>

@({
 (defsection name
    [:parents   parents]
    [:short     short]
    [:long      long]
    [:autodoc   autodoc]
    [:extension topic]
    ... events ...)
})

<p>For example,</p>

@({
 (defsection foo
   :parents (parent1 parent2 ...)
   :short \"@(call foo) is like @(see bar), but better when...\"
   :long \"<p>The main difference is ...</p>\"

   (defund foo (x) ...)
   (local (in-theory (enable foo)))
   (defthm foo-thm1 ...)
   (defthm foo-thm2 ...))
})

<h3>Ordinary Sections</h3>

<p>The @(':parents'), @(':short'), and @(':long') keywords are optional.  If
any of these keywords are provided, they will be used to introduce a @(see
defxdoc) command; otherwise no documentation will be generated.</p>

<p>By default, the @(':long') string you give will be automatically extended
with a \"Definitions and Theorems\" part that lists all the (non-local)
definitions and theorems introduced in the section.  This makes it easy to keep
the documentation up-to-date as you add and remove theorems to the section.  In
the above example, the @(':long') field would be extended with:</p>

@({
 <h3>Definition and Theorems</h3>
 @(def foo)
 @(thm foo-thm1)
 @(thm foo-thm2)
})

<p>If you do not want this automatic documentation, you can turn it off with
@(':autodoc nil').</p>

<p>By the way, I particularly like to use the above style, where a @('defund')
is immediately followed by a local @('enable'), because if I want to add a new
theorem, say @('foo-thm3'), then I can just re-submit the defsection without
undoing the previous one, and all of the enabling and disabling still happens
correctly.</p>

<h3>Extended Sections</h3>

<p>The @(':extension') keyword allows you to say that this section is a
continuation of a previously introduced concept.  When @(':extension topic') is
provided, then @('topic') must be the name of a previously documented @(see
xdoc) section, and you are not allowed to use @(':parents') or @(':short')
since the topic already exists.</p>

<p>The main purpose of an @(':extension') section is to add additional
documentation, either via the @(':long') string or via the automatic
documentation generation features of @('defsection').  The documentation
obtained this way is just appended onto the existing @(':long') for the
topic.</p>

<p>For example, if we have already given the section @('foo') with basic
theorems, above we now want to add a bunch of additional \"advanced\" theorems
about it, we might write something like this:</p>

@({
 (defsection advanced-theorems-about-foo
   :extension foo
   (defthm foo-thm3 ...)
   (defthm foo-thm4 ...))
})

<p>This will then append the definitions of @('foo-thm3') and @('foo-thm4')
onto the end of the documentation for @('foo').</p>")


(defxdoc defsection-progn
  :parents (xdoc)
  :short "Fancy @('(progn ...)') with a name and @(see xdoc) support."

  :long "<p>The @('defsection-progn') macro is like @(see defsection) except
that it generates a @('(progn ...)') instead of an @('(encapsulate nil
...)').</p>

<p>This has a number of consequences, mostly having to do with the scope of
@('local') events within the section.  A @('defsection-progn') basically does
not introduce a new scope, whereas a @('defsection') does.</p>")


(defxdoc undocumented
  :short "Placeholder for undocumented topics.")


(defxdoc test-of-entities
  :parents (xdoc)
  :short "Placeholder topic for testing out HTML entity support in XDOC."
  :long "<p>Here are the entities that XDOC allows:</p>

<p>Normal XML entities:</p>
<ul>
<li>@('&amp;')   becomes &amp;</li>
<li>@('&lt;')    becomes &lt;</li>
<li>@('&gt;')    becomes &gt;</li>
<li>@('&quot;')  becomes &quot;</li>
<li>@('&apos;')  becomes &apos;</li>
</ul>

<p>Additional entities allowed by XDOC:</p>
<ul>
<li>@('&nbsp;')  becomes &nbsp; (this one can be hard to see)</li>
<li>@('&mdash;') becomes &mdash;</li>
<li>@('&rarr;')  becomes &rarr;</li>
</ul>")
