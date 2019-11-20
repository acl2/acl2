; XDOC Documentation System for ACL2
; Copyright (C) 2009-2015 Centaur Technology
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


; topics.lisp
;
; This is the actual xdoc documentation for the xdoc system.  We put the topics
; here, instead of in top.lisp, in a probably silly effort to minimize the load
; time of top.lisp.

(in-package "XDOC")
(include-book "top")

(defxdoc xdoc
  :parents (documentation)
  :short "<i>XDOC</i> is a tool for documenting ACL2 books.  You can use it to
access documentation about ACL2 and its books, to document your own books, and
to create custom web-based manuals."

  :long "<p>Below we cover how to use XDOC to build manuals or document your
own @(see acl2::books).  If you just want to browse the documentation, you
probably don't need to read any of this!  Instead, see @(see
documentation).</p>

<h3>Starting Points</h3>

<p>A good, tutorial-style introduction to XDOC can be found in:</p>

<blockquote>
Jared Davis and Matt Kaufmann.  <a
href='http://dx.doi.org/10.4204/EPTCS.152.2'>Industrial Strength Documentation
for ACL2</a>.  ACL2 Workshop 2014.  EPTCS 152.  Pages 9-25.
</blockquote>

<p>See <i>Building the Manual</i> under @(see acl2::books-certification) for
information on building the ACL2+Books manual.  See @(see testing) for easy
instructions for how to test your XDOC strings.</p>


<p>To use XDOC to document your own books, the first step is:</p>

@({
 (include-book \"xdoc/top\" :dir :system)
})

<p>This book loads very quickly and requires no ttags.  It gives you @(see
defxdoc) and @(see defsection), the basic commands for adding documentation.
It also installs a new @(':doc') command, via @(see ld-keyword-aliases), so
that you can see new documentation from the terminal.</p>

<p>For a possibly more convenient way to construct XDOC strings, do the
following:</p>

@({
 (include-book \"xdoc/constructors\" :dir :system)
})

<p>This book includes @('[books]/xdoc/top.lisp'), and in addition provides
utilities to construct well-formed XDOC strings in a modular way.  See <see
topic='@(url xdoc::constructors)'>the documentation</see> for more details.</p>

<p>Once you have documented your books, you may wish to create a manual that
can be viewed from a web browser or from the acl2-doc Emacs-based browser (see
acl2::acl2-doc).  You can do this quite easily with XDOC's @(see save) command.
This command can be embedded in an ordinary ACL2 book, so that your manual is
automatically regenerated when you build your project.</p>


<h3>New Features</h3>

<p>XDOC now supports @(see katex-integration) for writing LaTeX-like formulas
like
@($
\\left( \\sum_{i=0}^{n} \\sqrt{f(i)} \\right) < \\frac{n^2}{k}
$)
within your documentation.</p>

<p>When writing documentation, you can now optionally have XDOC topics
automatically displayed as you submit new @(see defxdoc) forms&mdash;just
add:</p>

@({
 (include-book \"xdoc/debug\" :dir :system)
})

<p>to your @(see acl2::acl2-customization) file, or include it while you are
developing your book.  Afterward, each @(see defxdoc) form you submit will be
immediately shown at the terminal, giving you a quick, text-mode preview that
may help you to diagnose any markup problems.</p>")

(defxdoc missing-parents-test
  :short "A topic with no @(':parents')."
  :long "<p>This topic has no @(':parents') and is just meant to ensure that
@(see missing-parents) is working correctly.</p>")

(local (set-default-parents xdoc))

(defxdoc defxdoc
  :short "Add documentation to the @(see xdoc) database."

  :long "<box><p>Note: @('defxdoc') is very basic.  You will usually want to
use @(see defsection) or @(see std::define) instead.</p></box>

<p>@('Defxdoc') is the XDOC alternative to ACL2's built-in @('defdoc')
command.</p>

<p>General form:</p>

@({
 (defxdoc name
   [:parents parents]
   [:short   short]
   [:long    long])
})

<p>Example:</p>

@({
 (defxdoc duplicity
   :parents (std/lists defsort count no-duplicatesp)
   :short \"@(call duplicity) counts how many times the
            element @('a') occurs within the string @('x').\"
   :long \"<p>This function is similar to ACL2's built-in
          @('count') function but is more limited:</p>  ...\")
})

<p>The @('name') of each documentation topic must be a symbol.  All of the
keyword arguments are optional:</p>

<ul>

<li>@('parents') let you associate this documentation with other topics.  A
topic may have many parents, but circular chains of parents are not allowed and
will lead to errors when generating manuals.  If no @(':parents') are given
explicitly, the <see topic='@(url set-default-parents)'>default parents</see>
will be used.</li>

<li>@('short') should be a short description of this topic that is suitable for
inlining in other pages.  For instance, it may be displayed in subtopic listing
and in \"hover\" text on navigation pages.</li>

<li>@('long') should be the full, detailed documentation for this topic.</li>

</ul>

<p>The @('short') and @('long') strings may be written using the XDOC @(see
markup) language, and may also use @(see preprocessor) commands to insert
function definitions, theorems, topic links, and so on.</p>

<p>Many examples of using XDOC can be found throughout the ACL2 books.  See for
instance the @(see acl2::std), @(see acl2::std/strings) or @(see
acl2::std/osets) libraries.</p>

<h3>Note for Advanced Users</h3>

<p>XDOC just stores its documentation in an ordinary ACL2 table, so if you want
to do something like automatically generate documentation from macros, you
might decide to bypass @('defxdoc') and just manipulate the table directly.</p>

<p>It is not possible to directly use @('defxdoc') from raw Lisp, but you can
use @(see defxdoc-raw) instead.</p>")


(defxdoc markup
  :short "The <a href='http://en.wikipedia.org/wiki/Xml'>XML</a> markup
language that is the basis of XDOC documentation strings."

  :long "<p>XDOC uses an XML markup language that is similar to a subset of <a
href='http://en.wikipedia.org/wiki/HTML'>HTML</a>.  Note that unlike HTML,
beginning and ending tags are case-sensitive and must match exactly.  As in
HTML, you must escape characters like @('<') in text to distinguish them from
tags.</p>

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
etc., from the ACL2 world.  This can help you avoid having to copy and paste
definitions into your documentation, which can help to keep your documentation
up to date.</p>

<p>But sometimes you want to write other kinds of code fragments as examples.
The raw markup options are:</p>

<ul>

<li>Use the @('<tt>') tag for short, inline pieces of code, such as <tt>(+ 1
x)</tt>.</li>

<li>Use the @('<code>') tag for longer code examples that should be indented
and \"preformatted,\" i.e., newlines and spaces should be preserved.</li>

</ul>

<p><b>However</b>, it's often better to use the preprocessor's
<tt>@@('...')</tt> and <tt>@@({...})</tt> macros, respectively.  These are nice
because they automatically escape special HTML characters like &lt; into
&amp;lt; and also automatically add hyperlinks to documented functions.</p>

<p>(Implementation Note.  The @('<tt>') and @('<code>') tags in XDOC do not
correspond to the @('<tt>') and @('<code>') tags in HTML.  In fact, @('<tt>')
is rendered with an HTML @('<span>'), and @('<code>') is rendered with an HTML
@('<pre>').)</p>

<p>Whenever you include Lisp code fragments in your documentation, you should
usually keep everything <b>indented one space</b> to prevent Emacs problems.
For instance:</p>

@({
|(defxdoc foo
|  :long \"<h3>How to format @('<code>') blocks</h3>
|
|<p>GOOD -- the form is indented one space:</p>
|<code>
| (my-lisp-form (foo ...)
|               (bar ...))
|</code>
|
|<p>BAD -- the form is directly on the left-margin:</p>
|<code>
|(my-lisp-form (foo ...)
|              (bar ...))
|</code>
})

<p>Without this leading space, Emacs can become confused and think that
@('(my-lisp-form ...)'), rather than @('(defxdoc foo ...)'), is the top-level
expression.  This can ruin syntax highlighting and also commands like @('C-t
e') for sending s-expressions to the @('*shell*') window.</p>




<h3>Hyperlinks</h3>

<p><i>Internal links</i> between documentation topics and <i>Emacs tags-search
links</i> into the source code are handled by the @(see preprocessor).</p>

<p>You can add <i>external links</i> to web pages with ordinary HTML-style
links, e.g.,</p>

@({
<a href=\"http://www.centtech.com/\">Centaur Technology</a>
})

<p>Produces a link to <a href=\"http://www.centtech.com/\">Centaur
Technology</a>.</p>


<h3>Typesetting Mathematics (Experimental)</h3>

<p>XDOC's fancy web viewer now has some support for LaTeX-like mathematics.
For instance, you can write formulas such as</p>

@([
     c = \\pm\\sqrt{b^2 + a^2}
])

<p>See @(see katex-integration) for details.</p>


<h3>Images and other Resources</h3>

<p>Documentation topics can include inline images and (via hyperlinks) can
refer to other kinds of files, like PDF files.  You have to tell XDOC where to
find these files; see @(see add-resource-directory).  After setting up a
suitable resource directory, you can use @('img') tags such as:</p>

@({
    <img src='res/centaur/centaur-logo.png'/>
})

<p>to produce output such as:</p>

<img src='res/centaur/centaur-logo.png'/>


<h3>Structuring Documents</h3>

<h1>@('<h1>') creates the biggest heading</h1>
<h2>@('<h2>') the next biggest</h2>
<h3>@('<h3>') a medium size heading (a good default)</h3>
<h4>@('<h4>') a smaller heading</h4>
<h5>@('<h5>') a very small heading</h5>

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

<p>A subset of HTML tables is implemented, including @('<table>'), @('<tr>'),
@('<th>'), and @('<td>').  To encourage portability, this is a somewhat limited
facility&mdash;you cannot control widths, padding, etc. on table cells. Here is
an example table:</p>

<table>
<tr> <th>Color</th> <th>Land</th>   <th>Power Source</th> </tr>

<tr> <td>White</td> <td>Plains</td>
     <td>Goodness, order and light, all that is richeous and holy.  Adversary
         of evil and chaos.</td>
</tr>

<tr> <td>Blue</td>  <td>Islands</td>
     <td>Air and water, knowledge and control, illusion and sleight of hand.
         Adversary of chaos and nature.</td>
</tr>

<tr> <td>Black</td>  <td>Swamps</td>
     <td>Evil, darkness and despair, ambition and will, suffering and death.
         Adversary of nature and goodness.</td>
</tr>

<tr> <td>Red</td>  <td>Mountains</td>
     <td>Fire and chaos, impulsiveness and fury, freedom and whimsy.
         Adversary of goodness and control.</td>
</tr>

<tr> <td>Green</td> <td>Forests</td>
     <td>Life and nature, growth and fertility.  Adversary of control and
         death.</td>
</tr>
</table>


<p>It's relatively easy to add new tags.  There is undocumented support for
images and icons, but this is currently awkward.  In the future, we may add
other tags that users request.</p>")

(defpointer syntax markup)


(defxdoc preprocessor
  :short "In addition to its @(see markup) language, XDOC includes a
preprocessor which can be used to interpret certain directives of the form
@('@(...)')."

  :long "<h3>Functions and Theorems</h3>

<p>To look up function definitions (or pieces of definitions) from the ACL2
world and insert them into your documentation, you can use:</p>

<table>

<tr>  <td>@('@(def fn)')</td>
      <td>insert the definition of <i>fn</i><br/>
          (also works for theorems, macros, ...)</td>
</tr>

<tr> <td>@('@(body fn)')</td>
     <td>just the body of <i>fn</i></td> </tr>

<tr> <td>@('@(formals fn)')</td>
     <td>just the formals of <i>fn</i></td> </tr>

<tr> <td>@('@(measure fn)')</td>
     <td>just the measure of <i>fn</i></td> </tr>

<tr> <td>@('@(call fn)')</td>
     <td>a generic function call of <i>fn</i></td> </tr>

</table>

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

<p>There is special syntax to put in raw or verbatim text.  This is especially
useful for examples and code fragments, where you don't want to have to escape
special character like @('<') with @('&lt;').</p>

<ul>
<li><tt>@@('...')</tt> inserts @('...') into @('<tt>') XDOC tags.</li>
<li><tt>@@({...})</tt> inserts @('...') into @('<code>') XDOC tags.</li>
</ul>

<p>These have a special feature for automatically linking to documented topics.
For instance, <tt>@@('(consp x)')</tt> produces @('(consp x)'), and
<tt>@@({ (consp x) })</tt> produces:</p>

@({
 (consp x)
})

<h3>Evaluating Lisp from Doc Strings</h3>

<p>The preprocessor has a special backtick syntax for dynamically evaluating
ACL2 expressions.  This can be used to inject constants and examples into your
documentation.  For instance:</p>

<ul>
<li>@('@(`(+ 1 2 3)`)')          produces @(`(+ 1 2 3)`)</li>
<li>@('@(`(mv 'a 10 state)`)')   produces @(`(mv 'a 10 state)`)</li>
<li>@('@(`acl2::*pkg-witness-name*`)') produces @(`acl2::*pkg-witness-name*`)</li>
</ul>

<p>By default, the backtick syntax introduces @('<tt>') tags and automatically
escapes any special XML characters like @('<').  Sometimes this isn't what you
want.  When the result of your evaluation is large, you can use a spcial
@(':code') prefix to insert @('<code>') tags instead.  For instance:
@('@(`(:code (make-list 100))`)') produces:</p>

@(`(:code (make-list 100))`)

<p>(Advanced) Introducing @('<tt>') tags also doesn't work well for certain,
sophisticated uses of evaluation, e.g., to generate hyperlinks, etc.  The
special @(':raw') prefix can be used to insert exactly the contents of a
string, with no automatic escaping.  For instance:
  @('  @(`(:raw \"a &lt; b\")`)  ') produces
       @(`(:raw \"a &lt; b\")`).
Note that it is quite easy to use @(':raw') incorrectly; you have to escape
things properly yourself!</p>

<h3>Emacs Links</h3>

<p>The @('@(srclink name)') directive inserts a source-code link for users who
have configured their web browser as described in @(see emacs-links).  For
documentation in the acl2-doc browser @(see acl2::acl2-doc) or at the terminal,
the name is enclosed in angle brackets (@('<name>')), which essentially
represent a source-code link when using the acl2-doc `@('/')' command.</p>

<p>It is often unnecessary to use @('srclink') directly, because these links
are automatically inserted by @('@(def fn)').  One good reason to use
@('srclink') is to link to macros like @(srclink defxdoc), which often are
written using backquote and hence do not display nicely.</p>

<p>Source links are sometimes inappropriate, e.g., for definitions or theorems
that are generated by macros.  You can suppress the automatic source links on
@('def') commands by using @('@(gdef fn)') instead.  This stands for
\"generated definition.\"</p>


<h3>Documentation Links</h3>

<p>The easiest way to link between topics is to use @('@(see name)'), which
expands into a link to @('name').  The text shown to the reader is just the
name of the topic, in lower case.  Note also that @('@(csee name)') can be used
for links whose first letter should be capitalized; that @('@(tsee name)') can
be used for links that should appear in type-writer font; and that @('@(see?
name)') is useful for macros, since a link is inserted if @('name') is
documented but otherwise @('name') simply appears in typewriter font.</p>

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
<i>never</i> write a @('<see>') tag yourself without using @('@(url ...)').
Some examples:</p>

<ul>
<li>@('@(url defxdoc)') expands to @(url defxdoc)</li>
<li>@('@(sym defxdoc)') expands to @(sym defxdoc)</li>
<li>@('@(csym defxdoc)') expands to @(csym defxdoc)</li>
</ul>

<h3>Escaping of @</h3>

<p>Since @('@(') is intercepted by the preprocessor, you may occasionally need
to escape it.  You can write @('@@') to generate a single @('@') sign.</p>

<p>Besides @('@(') and @('@@'), the preprocessor leaves any other uses of
@('@') in tact.  So, most uses of @('@'), such as in email addresses, do not
need to be escaped.</p>")


(defxdoc save
  :short "Saves the XDOC database into files for web browsers, etc."

  :long "<p>Once you have documented your books with @(see defxdoc), you may
wish to create a manual that can be viewed from a web browser or from the
acl2-doc Emacs-based browser (see @(see acl2::acl2-doc)).</p>

<h4>Basic Example</h4>

@({
 ;; my-manual.lisp - a book that creates a manual
 (in-package \"MYPKG\")

 (include-book \"my-library1\") ;; load books I want in the manual
 (include-book \"my-library2\") ;; (documented with xdoc)

 (include-book \"xdoc/save\" :dir :system)  ;; load xdoc::save

 (defxdoc acl2::top           ;; create a \"top\" topic
   :short \"My Manual\"
   :long \"<p>This manual explains how to use my books...</p>\")

 (xdoc::save \"./mylib-manual\" :error t)  ;; write the manual
})

<p>Notes about this example:</p>

<ul>

<li>The @('xdoc::save') command will export all currently-loaded, documented
topics.  Because of this, you can mostly control what goes into the manual
<b>just by including books</b>, but see below for additional notes about how to
control what goes in a manual.</li>

<li>The @('save') command is a macro that expands into @(see
acl2::embedded-event-form)s.  Typically, you just put it into a new book (e.g.,
@('my-manual.lisp') above) so that your manual will be regenerated as part of
building your project.</li>

<li>The @('save') requires certain <see topic='@(url defttag)'>trust
tags</see>.  You may need to enable trust tags in your build system to certify
the @('my-manual') book.  For instance, @('cert.pl') users may need a
@('.acl2') file with a line such as:

@({
    ; cert-flags: ? t :ttags :all
})</li>

<li>After saving a manual, you should be able to view it by going to, e.g.,
@('mylib-manual/index.html') in your web browser.  If you want to share your
manual with others, you should read about @(see deploying-manuals).</li>

</ul>


<h4>General Form</h4>

@({
    (save <target-dir>
          [:redef-okp  bool]               ;; default is nil
          [:zip-p      bool]               ;; default is t
          [:logo-image path]               ;; default is nil
          [:error      bool]               ;; default is nil
          [:broken-links-limit nil-or-nat] ;; default is nil
          )
})

<p>The only (required) argument to the @('save') command is the name of a
directory where the want the manual to go.  All arguments are evaluated.
As might be expected:</p>

<ul>

<li>If the target directory does not exist, it will be created.</li>

<li>If the target directory already exists, it <color rgb=\"#ff0000\">will be
overwritten</color>.</li>

</ul>

<h5>Option Summary</h5>

<dl>

<dt>@('redef-okp')</dt>

<dd>By default, the @('save') command will complain if any topic is defined
more than once.  This is often annoying when you are developing books,
especially if your books are slow to certify and you don't want to have your
build fail just because of a documentation problem.  So, if you want to
suppress this error (and turn it into a printed warning), you can set
@(':redef-okp t').</dd>

<dt>@('zip-p')</dt>

<dd>To support the <a href='download/'>Download this Manual</a>
feature (normally accessed from the toolbar button) the @('save') command will
zip up the manual to create @('.tar.gz'), @('.tar.bz2'), and @('.zip') files.
If you don't care about generating these files and want to avoid the time to
build them, you can set @(':zip-p nil').</dd>

<dt>@(':logo-image')</dt>

<dd>You can provide a custom image to use as the logo for the @(see top) topic.
The path you provide should be relative to whatever book contains the @('save')
command.</dd>

<dt>@(':error')</dt>

<dd>The value is @('t') or @('nil'), to indicate whether or not (respectively)
to cause an error upon encountering a syntax error in xdoc source (marked with
\"xdoc error\").</dd>

<dt>@(':broken-links-limit')</dt>

<dd>The value is @('nil') by default.  Otherwise, it is a natural number
specifying the maximum allowed number of broken links; if the ``broken topic
link'' report shows more broken links than that limit, an error occurs.</dd>

</dl>


<h3>Avoiding Unwanted Documentation</h3>

<p>By default, the @('save') command will generate a manual that covers the
documentation for all books that you have loaded.  This usually works well
as long as you know all of the books that you need to include.</p>

<p>One caveat is that @('xdoc/save') includes some supporting books that are,
themselves, documented.  Accordingly, you may find that your manual includes
documentation from libraries like @(see acl2::std/strings) and @(see
oslib::oslib) in your output even if you haven't loaded these libraries
yourself.  If you really want precise control over what goes into your manual,
then, you may want to do something like this:</p>

@({
 ;; nothing-extra-manual.lisp - manual with nothing extra
 (in-package \"MYPKG\")

 (include-book \"my-library1\") ;; load books I want in the manual
 (include-book \"my-library2\") ;; (documented with xdoc)

 (make-event ;; save current documentation
  `(defconst *just-my-documentation*
     ',(xdoc::get-xdoc-table (w state))))

 (include-book \"xdoc/save\" :dir :system)

 ;; clobber any docs that were added due to xdoc/save
 (table xdoc::xdoc 'xdoc::doc *just-my-documentation*)

 (defxdoc acl2::top           ;; create a \"top\" topic
   :short \"My Manual\"
   :long \"<p>This manual explains how to use my books...</p>\")

 (xdoc::save \"./mylib-manual\" :error t)
})")

(defxdoc save-rendered
  :parents (XDOC)
  :short "Saves the XDOC database into a file for the acl2-doc browser"
  :long "<p>Also see @(see save-rendered-event) for a corresponding macro that
  provides additional functionality.</p>

 @({
 General Form:

 (save-rendered outfile
                header
                topic-list-name
                error
                state)
 })

 <p>where @('outfile') is the pathname for the output file, @('header') is to
 be written to the top of @('outfile') (typically as a comment), and the value
 of @('topic-list-name') is a symbol that can be the first argument of @(tsee
 defconst), hence of the form @('*c*').  The value of @('error') should be
 @('t') or @('nil') to indicate whether or not (respectively) to cause an error
 upon encountering a syntax error in xdoc source (marked by \"xdoc error\").
 Upon success this call returns the error-triple @('(mv nil (value-triple :ok)
 state)'); probably the value is unimportant except that it allows an
 @('xdoc::save-rendered') call to be placed inside @('make-event'), as
 displayed below.</p>

 <p>For example, the following form may be found in community book
 @('books/doc/top.lisp').  Its evaluation creates the output file
 @('books/system/doc/rendered-doc-combined.lsp\"').  That file starts with a
 comment from the string, @('*rendered-doc-combined-header*'), then contains
 @('(in-package \"ACL2\")'), and concludes with a form @('(defconst
 *ACL2+BOOKS-DOCUMENTATION* '<big-alist>)'), where @('<big-alist>') is an alist
 representing the XDOC database.</p>

 @({
 (make-event
  (time$
   (xdoc::save-rendered
    (extend-pathname (cbd)
                     \"../system/doc/rendered-doc-combined.lsp\"
                     state)
    *rendered-doc-combined-header*
    '*acl2+books-documentation*
    t ; cause error upon encountering xdoc error
    state)))
 })

 <p>The output file is typically used by the acl2-doc Emacs-based browser for
 XDOC.  See @(see acl2::acl2-doc), specifically the discussion of custom
 manuals, which explains that the @('filename') argument of Emacs function
 @('extend-acl2-doc-manual-alist') is exactly the output file created by
 @('xdoc::save-rendered').</p>")

(defxdoc save-rendered-event
  :parents (XDOC)
  :short "Event that invokes @(tsee save-rendered), supporting extra functionality"
  :long "<p>See @(see save-rendered) for relevant background.</p>

 @({
 General Form:

 (save-rendered-event outfile
                      header
                      topic-list-name
                      error
                      &key
                      script-file script-args timep)
 })

 <p>where the four required arguments correspond to the same arguments of
 @(tsee save-rendered).  Although @('save-rendered') and
 @('save-rendered-event') have similar effects &mdash; indeed,
 @('save-rendered-event') invokes @('save-rendered') with the same first four
 arguments &mdash; @('save-rendered-event') is a macro that generates an event
 form (using @(tsee make-event)) that can be placed in a book.  All arguments
 are evaluated.  The keyword arguments of @('save-rendered-event') provide
 additional functionality, as follows.</p>

 <p>Suppose @(':script-file') is supplied with a non-@('nil') value.  Then
 there must be an active trust tag (see @(see defttag).  The value of
 @(':script-file') should be a string that names a file to be executed as a
 shell command, using @(tsee sys-call).  The argument list of that command is
 provided by the value of @(':script-args').  For an example, see the call of
 @('xdoc::save-rendered-event') in community book @('doc/top.lisp').</p>

 <p>If @(':timep') is non-@('nil') then the entire computation will be wrapped
 in a call of @(tsee time$).</p>")

(defxdoc deploying-manuals
  :parents (save)
  :short "How to distribute XDOC manuals for other people to use."

  :long "<p>After you have documented your books with XDOC and created a
manual, you may wish to share your manual with coworkers, collaborators,
customers, sponsors, etc.  The best way to do this may depend on many
factors.</p>

<p>By default, the manuals created by @(see save) use only client-side
JavaScript code.  This makes deployment very easy: you can just copy the files
to wherever you like, and you don't even need a web server.</p>

<p>This approach&mdash;just copying the default manual&mdash;is well-suited
for:</p>

<ul>
<li>Browsing from your local hard-drive, or</li>
<li>Browsing from a fast NFS drive or intranet server</li>
</ul>

<p>But the default manuals will <b>perform badly on slow connections</b>.  So,
if your users are going to read the manual over, e.g., VPNs or public web
sites, then you may wish to read on.</p>


<h3>Server-Supported Manuals</h3>

<p>The basic reason that the default manuals are slow is that they work by
simply loading the data for <b>every</b> topic, at startup.  As of October
2013, this comes to around 25 MB of data for the basic @('doc/top.lisp')
manual.  It's no big deal to load 25 MB from a local hard drive or a fast
intranet connection, but it can be quite slow over the internet.</p>

<p>The XDOC manuals created by @('save') can be reconfigured to just load the
@(':long') sections as they are accessed.  This results in a much
faster-loading manual, and is how, for instance, the <a
href='http://fv.centtech.com/acl2/latest/doc/'>online XDOC manual</a> at
Centaur is deployed.</p>

<p>This option requires a small amount of configuration, and you may need to
coordinate with your network administrator to get certain software
installed.</p>

<p>If you want to use our scripts directly, you will need a web server that
supports <a href='http://www.perl.org'>Perl</a> scripts with the CGI, DBI, and
DBD::SQLite modules installed.  If for some reason this poses a problem, you
may find that you can easily port these scripts to other popular languages,
like PHP or Ruby, with SQLite support.</p>


<h4>Step 1: Create the Database</h4>

<p>In the manual directory you created with the @(see save) command, you should
find a Perl script named @('xdata2sql.pl').  When you run this script, you
should see something like the following output:</p>

@({
$ cd my-library/manual
$ perl xdata2sql.pl
-------------------------------------------------------------------------------

xdata2sql.pl: Convert xdata.js into xdata.db (an sqlite3 database)

   NOTE: Most folks don't need to run this at all!
         If you just want to:
          - browse an XDOC manual on your local hard drive, or
          - share an XDOC manual on your fast intranet
         then ignore this script and just see index.html.

The main use for this script is to share XDOC manuals on the internet.  In this
scenario, just having the web browser load in the entire (generally 20+ MB)
xdata.js file is not very practical, because some users will have slow
connections and will take too long to load the file.

There are many ways to solve this.  Our approach is to convert xdata.js into an
sqlite3 database, and then use a server-side script that will allow us to
access topics only as they are requested.

-------------------------------------------------------------------------------

; Converting xdata.js

; Reading file
; Checking file
; Parsing JSON data.
; Creating new xdata.db.
; Creating xdoc_data table.
; Populating xdoc_data table.
; All done.

To actually use the database, see xdataget.pl.
})

<p>After this step, you should have a new file named @('xdata.db') in your
manual directory.  This is an SQLite3 database that has the information for
your XDOC topics.  It should be roughly as large as @('xdata.js').</p>

<p>If you are missing some required Perl modules, then instead of the above
output you may see a message such as</p>

@({
    Can't locate DBI.pm in @INC ...
})

<p>In this case, you may need to ask your systems administrator to install the
missing modules.</p>


<h4>Step 2: Set up the Web Server</h4>

<p>Once you have created the @('xdata.db') file, you will need to copy both it
and a different script, @('xdataget.pl'), to some directory in your web
server.</p>

<p>Typically, for @('xdataget.pl') to work at all, it will need to have its
executable bit set, and it may need to be in a special directory within your
web server, typically named @('cgi-bin').</p>

<p>To make sure the script is working, you should now load it in your web
browser by going to, e.g., @('http://my-server/cgi-bin/xdataget.pl').  If
everything is working, you should see a page that looks like this:</p>

@({
     {\"results\":[

     ]}
})

<p>If, instead, you see a message like <i>Internal Server Error</i>, then you
may have a permissions problem, or your web server's version of Perl may be
missing a require library, or something else may be wrong; ask your systems
administrator for help.</p>

<p>You may also wish to load, e.g.,:</p>

@({
    http://my-server/cgi-bin/xdataget.pl?keys=ACL2____TOP
})

<p>and make sure that you can see some text from your top topic.</p>


<h4>Step 3: Configure the Manual to use the Server</h4>

<p>The final step is to edit the file @('config.js') in your manual.
This file contains comments with the example syntax.  Basically you
just need to change:</p>

@({
    var XDATAGET = \"\";
})

<p>To have the right URL for your xdataget.pl script, e.g., into:</p>

@({
    var XDATAGET = \"http://my-server/cgi-bin/xdataget.pl\";
})

<p>At this point, your manual should load topic data dynamically as needed.
The result should be much faster for users on slow connections.</p>")

(defxdoc emacs-links
  :short "Instructions for integrating XDOC web pages with <a
  href='http://www.gnu.org/software/emacs/'>Emacs</a>."

  :long "<p>@(csee preprocessor) directives such as @('@(def get-xdoc-table)')
result in the introduction of special links for Emacs.  Here's what these links
look like:</p>

@(def get-xdoc-table)

<p>Depending on your environment, it <b>may</b> be easy to configure your web
browser so that clicking on these links will cause Emacs to directly open up
the appropriate source file and jump to the named function.</p>

<p>The basic idea is:</p>

<ul>

<li>Each Emacs link generates a <a
href='https://en.wikipedia.org/wiki/Data_URI_scheme'>Data URIs</a> that tells
your web browser to download a new, generated file whose <a
href='https://en.wikipedia.org/wiki/Internet_media_type'>MIME type</a> is
@('application/x-acl2-xdoc-link').</li>

<li>You configure your web browser to send @('application/x-acl2-xdoc-link')
files to Emacs.</li>

<li>You configure your Emacs to carry out a tags search instead of loading
these files.</li>

</ul>

<p>The net effect is that clicking on these links will send you directly to the
desired function in the source code.  This is <b>really slick</b> if you can
get it working.</p>


<h2>Configuring Emacs</h2>

<h4>Loading the XDOC Elisp</h4>

<p>The XDOC directory includes a file called @('xdoc.el'), which tells emacs
what to do with these xdoc-link files.  To tell emacs to load this file at
startup, you can just add a command to your @('.emacs') file like:</p>

@({
 (load \"/path/to/acl2/books/xdoc/xdoc.el\")
})

<p>This file will be loaded automatically if you load the file of emacs
utilities that comes with ACL2:</p>

@({
 (load \"/path/to/acl2/emacs/emacs-acl2.el\")
})

<h4>Managing your TAGS tables</h4>

<p>For emacs to make sense of the links you follow, it will need to have the
appropriate <a
href=\"https://www.gnu.org/software/emacs/manual/html_node/emacs/Tags-Tables.html\">tags
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
Emacs, or in <b>new buffers</b> of an already-running Emacs.</p>

<p>If you want everything to open up in a new instance of Emacs, you can skip
this section.  But I prefer to use a single Emacs for everything, and just have
links open up in new buffers.</p>

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

<p>The last thing we need to do is instruct your web browser to send xdoc-link
files to Emacs.</p>

<p>How to do this depends on your web browser and/or operating system.  In some
cases it may be hard to pass command-line options to emacs directly, so you may
find it useful to use the script @('emacsclient-wrapper.sh'), found in the xdoc
directory.</p>

<p>The basic starting point is probably to try to click on an emacs link like
@(srclink append) and try to tell your browser to open it with the
@('emacsclient-wrapper.sh') script.  If your browser opens it with some other
program, you might need to edit the default file associations of your operating
system or window manager.</p>")


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
  :short "Fancy @('(encapsulate nil ...)') with a name and @(see xdoc) support."

  :long "<h4>General Form</h4>

@({
 (defsection name
    [:parents   parents]
    [:short     short]
    [:long      long]
    [:autodoc   autodoc]
    [:extension topic]
    ... events and commentary ...)
})

<h4>Example</h4>

@({
 (defsection foo
   :parents (parent1 parent2 ...)
   :short \"@(call foo) is like @(see bar), but better when...\"
   :long \"<p>The main differences between @('foo') and @('bar') are ...</p>\"

   (defund foo (x) ...)
   (local (in-theory (enable foo)))
   (defthm foo-thm1 ...)
   (defthm foo-thm2 ...)

   \"<p>NOTE: the next theorem is really useful, but we keep it disabled
   because it gets too expensive when...</p>\"

   (defthmd foo-thm3 ...))
})

<box><p>Note: this example might be better written as a @(see std::define),
which is much like a @('defsection') but has additional features.</p></box>

<h3>Overview</h3>

<p>Like an @(see encapsulate), a @('defsection') introduces a new scope for
@(see local) events.  This is often useful when you are trying to prove a
theorem that requires some lemmas: by proving the lemmas locally, you can
prevent them from affecting the rest of your book.</p>

<p>It is often useful to organize books into sections.  There are a few minor
reasons you might prefer using @('defsection') for this, instead of plain
@('encapsulate')s.  For instance,</p>

<ul>

<li>It is easier to identify in the @(':pbt') history, and</li>

<li>It indents more nicely than @('encapsulate') in a vanilla emacs.</li>

</ul>

<p>But the main reasons to use @('defsection') are its documentation features.
The definitions and theorems within a section can be <b>automatically</b>
included in the documentation page for that section, along with any running
commentary.  This helps to avoid copying-and-pasting code into the manual, and
keeps it up-to-date as the code changes.</p>


<h3>Ordinary Sections</h3>

<p>The @(':parents'), @(':short'), and @(':long') keywords are optional.  If
any of these keywords are provided, they will be used to introduce a @(see
defxdoc) command; otherwise no documentation will be generated.</p>

<p>By default, the @(':long') string you give will be automatically extended
with a \"Definitions and Theorems\" part that lists all of the (non-local,
non-redundant) definitions and theorems introduced in the section.</p>

<p>For instance, in the above example, the @(':long') field would be extended
with:</p>

@({
 <h3>Definition and Theorems</h3>

 @(def foo)
 @(thm foo-thm1)
 @(thm foo-thm2)

 <p>NOTE: the next theorem is really useful, but we keep it disabled
   because it gets too expensive when...</p>

 @(thm foo-thm3)
})

<p>If you do not want this automatic documentation, you can turn it off with
@(':autodoc nil').</p>


<h3>Extended Sections</h3>

<p>The @(':extension') keyword allows you to say that this section is a
continuation of a previously introduced concept.</p>

<p>When @(':extension topic') is provided, then @('topic') must be the name of
a previously documented @(see xdoc) section, and you are not allowed to use
@(':parents') or @(':short') since the topic already exists.  Note that whereas
topics can have multiple parents, you can only extend a single topic at a
time.</p>

<p>The main purpose of an @(':extension') section is to add additional
documentation, either via the @(':long') string or via the automatic events and
commentary.  The documentation obtained this way is just appended onto the
existing @(':long') for the topic.</p>

<p>For example, say we have already defined the above @('foo') section in some
\"basic\" book.  We might then want to add some additional \"advanced\"
theorems about it in some other book.  We could do this via:</p>

@({
 (defsection advanced-theorems-about-foo
   :extension foo

   \"<p>Additional theorems are also available in the @('advanced') book.  (We
     don't include these in the basic book since they take a long time to
     prove.)</p>\"

   (defthm foo-thm4 ...)
   (defthm foo-thm5 ...))
})

<p>This will result in the commentary and definitions of @('foo-thm4') and
@('foo-thm5') being added onto the end of the documentation for @('foo').</p>")


(defxdoc defsection-progn
  :short "Fancy @('(progn ...)') with a name and @(see xdoc) support."

  :long "<p>The @('defsection-progn') macro is like @(see defsection) except
that it generates @({(progn ...)}) instead of an @({(encapsulate nil ...)})</p>

<p>This has a number of consequences, mostly having to do with the scope of
@('local') events within the section.  In short, a @('defsection-progn') does
not introduce a new local scope, but a @('defsection') does.</p>")


(defxdoc undocumented
  :short "Placeholder for documentation topics that lack good @(':parents')."

  :long "<p>Many @(see acl2::macros) such as @(see std::deflist) and other
@(see acl2::std/util) macros can automatically generate @(see xdoc)
documentation topics.</p>

<p>When someone uses these macros but doesn't give any @(':parents') for the
resulting documentation, we put the resulting documentation here.  This seems
better than just dropping the documentation completely, since at least you can
at least see the boilerplate documentation and any embedded documentation that
the programmer did provide.</p>

<p>As ongoing documentation improvement work, most topics here can benefit from
being given more appropriate @(':parents').</p>")

(defxdoc missing-parents
  :short "Placeholder for documentation topics that lack @(':parents')."

  :long "<p>If a @(see defxdoc) form ends up having no parents, it ends up
being put here.  See also @(see undocumented).</p>

<p>Historic note.  We used to put these topics directly underneath @(see top)
instead.  But we found that during development, this sometimes led to a
strange-looking hierarchy where ``random'' topics were presented as top-level
topics just because they were new or being moved around or because @(see
set-default-parents) forms weren't quite in the right places.  To avoid this,
we now move these topics to @('missing-parents') and print notes about them
when a manual is saved with @(see xdoc::save).</p>")

(defxdoc set-default-parents
  :short "Set up default parents to use for @(see xdoc)."

  :long "<p>When documenting a book of inter-related functions, you may
sometimes wish to use the same @(':parents') across many @(see defxdoc) or
@(see defsection) commands.  This can sometimes get tedious.</p>

<p>The macro @(call set-default-parents) can be used to set up a default list
of parent topics to be automatically used by commands such as @(see defxdoc)
and @(see defsection).</p>

<p>Basic Example:</p>

@({
   (local (set-default-parents fox-p))

   (defxdoc make-fox           ;; use default :parents, (fox-p)
     :short ...
     :long ...)

   (defsection feed-fox        ;; use default :parents, (fox-p)
     :short ...
     :long ...)

   (defsection chase-mouse     ;; use explicit :parents, (fox-p mouse-p)
     :parents (fox-p mouse-p)
     :short ...
     :long ...)

   (local (set-default-parents fox-p hawk-p))

   (defsection bother-hawk     ;; use default :parents, (fox-p hawk-p)
     :short ...
     :long ...)

   (local (set-default-parents nil))

   (defxdoc zebra-p            ;; use default :parents, nil
     :short ...
     :long ...)
})

<p>Note that @('set-default-parents') is just a macro that expands to a @(see
table) event.  It's good practice to only <b>locally</b> set the default
parents&mdash;otherwise the default parents can \"leak\" from your book and
lead you to inadvertently set the parents of other, unrelated topics.</p>")


(defxdoc xdoc-extend
  :short "Extend an existing XDOC topic with additional content."
  :long "<p>Basic example:</p>

@({
     (defxdoc foo
       :short \"Example of xdoc-extend.\"
       :long \"<p>Foo is very important.</p>\")

     (xdoc::xdoc-extend foo
       \"<p>Note: you can't use Foo with Bar.</p>\")
})

<p>is roughly equivalent to just writing:</p>

@({
     (defxdoc foo
       :short \"Example of xdoc-extend.\"
       :long \"<p>Foo is very important.</p>
               <p>Note: you can't use Foo with Bar.</p>\")
})

<p>@(call xdoc-extend) requires that @('name') is an existing XDOC topic, e.g.,
it may have been introduced with @(see defxdoc), @(see defsection), or similar.
We just look up that topic and extend its @(':long') string by appending the
new @('long') fragment to it.</p>

<p>This mechanism is barbaric and fragile.  For instance:</p>

<ul>

<li>You can't put the new content anywhere except at the end of the current
@('long') string.  (But see @(see xdoc-prepend) if you want to extend the
beginning of a topic).</li>

<li>If you extend a topic several times in different books, the resulting text
may differ depending on the particular @(see include-book) order that happens
to be used.</li>

</ul>

<p>Nevertheless, judiciously used, it can be a useful tool for connecting
together related content that must be kept in separate files, e.g., for
bootstrapping or other reasons.</p>")


(defxdoc xdoc-prepend
  :short "Extend an existing XDOC topic with additional content, at the front."

  :long "<p>@(call xdoc-prepend) is very much like @(see xdoc-extend), except
that it extends the @(':long') string for @('name') at the front, instead of at
the back.</p>

<p>Basic example:</p>

@({
     (defxdoc foo
       :short \"Example of xdoc-prepend.\"
       :long \"<p>Foo is very important.</p>\")

     (xdoc::xdoc-prepend foo
       \"<p>Never use Foo, use Bar instead!</p>\")
})

<p>is roughly equivalent to just writing:</p>

@({
     (defxdoc foo
       :short \"Example of xdoc-prepend.\"
       :long \"<p>Never use Foo, use Bar instead!</p>
               <p>Foo is very important.</p>\")
})

<p>See @(see xdoc-extend) for related commentary.</p>")


(defxdoc order-subtopics
  :short "Control the ordering of subtopics in the XDOC display."

  :long "<p>@(call order-subtopics) allows you to specify what order the
subtopics of @('name') will be presented in.  For instance:</p>

@({
    (xdoc::order-subtopics mini-tutorial
      (example syntax semantics gotchas references))
})

<p>By default, XDOC shows subtopics in an alphabetical order.  For most
reference-manual material this is generally fine.  But, especially for tutorial
guides, you sometimes intend your topics to be read in some particular order,
and alphabetizing things gets in the way.</p>

<p>The @('order-subtopics') command lets you specify the exact subtopic
ordering that should be used for a particular topic.  One general form is:</p>

@({
    (xdoc::order-subtopics parent
      (subtopic1 subtopic2 ... subtopicn))
})

<p>You don't have to give a complete order.  Any subtopics that aren't
mentioned will be listed last, in the usual alphabetical order.</p>

<p>A second general form has an optional argument of @('t').  This specifies
that the order for unspecified child topics is the order in which the topics
were defined, rather than alphabetical.</p>

@({
    (xdoc::order-subtopics parent
      (subtopic1 subtopic2 ... subtopicn)
      t)
})

<p>A special case of that second general form lists no subtopics, thus
specifying simply that all children are to be listed in the order in which they
were defined.</p>

@({
    (xdoc::order-subtopics parent
      nil
      t)
})

<p>We require @('parent') to refer to some defined topic, but the subtopics
don't need to be defined at @('order-subtopics') time.  This makes it easy to
keep the subtopic ordering close to the defxdoc command, e.g., you can
write:</p>

@({
     (defxdoc mini-tutorial ...))
     (order-subtopics mini-tutorial (example syntax ...))

     (defxdoc example ...)
     (defxdoc syntax ...)
})

<p>We do at least warn about undefined topics when you @(see save) a
manual.</p>")

#||

(in-package "ACL2")

(include-book "debug")
(defconst *foo* 3)

(include-book
 "centaur/vl/util/print" :dir :system)

(defxdoc basic-test
  :short "Hello"
  :long "<p>1 + 2 = @(`(+ 1 2)`)</p>

<p>*foo* is @(`*foo*`)</p>

<p>parse error is @(`(+ 1 2) (+ 2 3)`)</p>

<p>parse error 2 is @(`(undefined::blah)`)</p>

<p>1 + 2 + 3 = @(`(+ 1 2 3)`)</p>

<p>(mv 1 2 3 state) is @(`(mv 1 2 3 state)`)</p>

<p>(mv 1 2 3 state vl::ps) is @(`(mv 1 2 3 state vl::ps)`)</p>

<p>(repeat 'a 100) is @(`(:code (repeat 'a 100))`)</p>

")

||#


(defxdoc xdoc-tests
  :short "Topics that exist only to test XDOC functionality.")

(local (set-default-parents xdoc-tests))

(defxdoc test-of-entities
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
<li>@('&lsquo;') becomes &lsquo;</li>
<li>@('&rsquo;') becomes &rsquo;</li>
<li>@('&ldquo;') becomes &ldquo;</li>
<li>@('&rdquo;') becomes &rdquo;</li>
</ul>

<p>Test of `single' and ``double'' smart quoting for legacy topics.</p>

<p>Test of &lsquo;single&rsquo; and &ldquo;double&rdquo; smart quoting for
regular old entities.</p>

<p>Test of <tt>`single' and ``double''</tt> quotes in a @('<tt>') tag and in
a @('<code>') tag:</p>

<code>`single' and ``double''</code>

<p>Test of @(' `single' and ``double'' ') quotes in inline preprocessor stuff,
and in preprocessor blocks here:</p>

@({ `single' and ``double'' quotes ! })

<p>Test of primes in math: @($ foo' $) and</p>

@([ foo' ])

<p>That should probably about do it.</p>")

(order-subtopics xdoc-tests
  (order-test-w
   order-test-o
   order-test-r
   order-test-z-intentionally-missing
   order-test-k
   order-test-s))

(defxdoc order-test-s :short "S")
(defxdoc order-test-w :short "W")
(defxdoc order-test-r :short "R")
(defxdoc order-test-o :short "O")
(defxdoc order-test-k :short "K")

(defxdoc xdoc-test-order-subtopics-flg
  :short "Parent topic for testing chronological order of subtopics.")

(order-subtopics xdoc-test-order-subtopics-flg
                 (order-test-flg-move-to-front)
                 t)

(local (set-default-parents xdoc-test-order-subtopics-flg))

(defxdoc order-test-flg-w :short "W")
(defxdoc order-test-flg-o :short "O")(defxdoc order-test-flg-o :short "O")
(defxdoc order-test-flg-move-to-front :short "Move to front")
(defxdoc order-test-flg-r :short "R")
(defxdoc order-test-flg-k :short "K")
(defxdoc order-test-flg-s :short "S")

(local (set-default-parents xdoc))

(defxdoc katex-integration
  :short "Support for LaTeX-like typesetting of mathematics in XDOC
topics. (experimental)"

  :long "<box><p><b>Experimental.</b> This whole thing is experimental.  Jared
reserves the right to decide it is a bad idea and remove support for
it.</p></box>

<p>The <a href='https://www.khanacademy.org/'>Khan Academy</a> has developed a
very nice Javascript library, <a
href='https://github.com/Khan/KaTeX'>KaTeX</a>, for rendering mathematical
formulas in the web browser.  We have now integrated KaTeX into XDOC's fancy
web-based viewer, allowing you to typeset basic formulas.</p>


<h3>Basic Usage</h3>

<box><p><b><color rgb='#ff0000'>ESCAPING WARNING</color></b>. LaTeX-style
formulas may be especially hard to type in ordinary ACL2 string literals
because you have to escape all the backslashes.  For instance, you have to
remember to write @('\\\\sqrt{x}') instead of @('\\sqrt{x}').  You can avoid
this headache by using the @(see acl2::fancy-string-reader). In the rest of
this document, we will use the concrete xdoc syntax without the escapes for
simplicity.</p></box>

<p>To typeset block-style formulas, you can use the @('@([...])') @(see
preprocessor) directive, e.g.,:</p>

@({
    @([
       c = \\pm\\sqrt{a^2 + b^2}
    ])
})

<p>Produces an indented block of mathematics:</p>

@([
    c = \\pm\\sqrt{a^2 + b^2}
])

<p>You can also write inline math using @('@($...$)') directive, for
instance:</p>

@({
     The product @($a \\times b$) is even.
})

<p>Produces text such as: the product @($a \\times b$).</p>


<h3>Tips and Tricks</h3>

<h5>Fast Preview.</h5>

<p>The <a href='formula.html'>KaTeX Preview</a> page lets you interactively
type in your formula and see how it will be typeset.  It may be especially
helpful since KaTeX only supports a particular subset of LaTeX.</p>

<h5>Invalid Formulas.</h5>

<p>Invalid formulas will display as an ugly error message.  For instance, here
is an invalid @('@([ ... ])') style formula:</p>

@([
      { there is no closing brace
])

<p>And here is an invalid @('@($...$)') style formula,
@($
      { there is no closing brace
$), embedded in a paragraph.</p>

<h3>Miscellaneous Notes</h3>

<p>The preprocessor directives expand into @('<math>') and @('<mathfrag>')
tags.  But you will probably want to stick to the preprocessor syntax, rather
than directly using @('<math>') tags, because if you try to use raw @('<math>')
tags then you have to remember to escape XML characters like @('<') with
@('&lt;'), which just isn't very readable.</p>

<p>All of this is fundamentally limited to the web-based viewer.  It seems very
unlikely that @('<math>') formulas will ever look nice when shown at the
terminal with @(':doc') or in the ACL2-Doc Emacs viewer.</p>")


(defxdoc defpointer
  :short "Define an alias for a documentation topic."

  :long "<p>Examples:</p>

@({
    (defpointer acl2s acl2-sedan)
    (defpointer guard-hints xargs t)
})

<p>General Form:</p>

@({
    (defpointer new-topic target-topic [keyword-p])
})

<p>This is a simple macro that expands to a @(see defxdoc) form.  It introduces
a new @(see xdoc) topic, @('new-topic'), that merely links to
@('target-topic').  The new topic will only be listed under @(see
pointers).</p>

<p>A common practice when documenting keyword symbols is to create a
doc topic in in the \"ACL2\" package or some other relevant package,
rather than the \"KEYWORD\" package to which the keyword symbol
rightfully belongs.  In keeping with this practice, the @('keywordp')
argument to @('defpointer'), if non-nil, adds a clarification that the
doc topic is really about the keyword symbol with the same name as
@('new-topic'), rather than @('new-topic') itself.</p>")


(defxdoc add-resource-directory
  :short "Tell @(see xdoc) about directories of resources (e.g., images, PDF
files, etc.) that should be copied into manuals."

  :long "<p>Occasionally you may wish to include images or other files within
an XDOC documentation topic.  For this to work, XDOC's @(see save) command
needs to know about these files so that it can copy them into the manual it
produces.  The @('add-resource-directory') command lets you tell XDOC which
directories to copy and what to name them.</p>

<h3>Example</h3>

<p>Suppose that in the @('vl') library there are some images that we want to
include in the manual.  We can put these images into a directory, say
@('images'), and then do:</p>

@({
    (xdoc::add-resource-directory \"vl\" \"images\")
})

<p>This will cause the @(see xdoc::save) command to copy everything from the
@('images') directory into the @('res/vl') directory of our manual.  To refer
to these images, we can then write @(see markup) such as:</p>

@({
    <img src=\"res/vl/logo.jpg\"/>
})

<p>These resource directories might also contain files other than images, for
instance, PDF files.  You can at provide hyperlinks to these files by just
linking into the @('res') directory, for instance:</p>

@({
    <a href=\"res/vl/slides.pdf\">See the Slides!</a>
})


<h3>General form</h3>

@({
    (xdoc::add-resource-directory dirname path)
})


<ul>

<li><b>dirname</b> controls where the directory will be placed in within the
manual's @('res') directory.  In the example above, the @('dirname') is
@('\"vl\"') so the files will be copied into @('\"res/vl\"').</li>

<li><b>path</b> controls where the files will be copied from.  We recommend
always using a simple path such as the name of an immediate subdirectory.</li>

</ul>

<h3>Working example</h3>

<p>The directory @('books/xdoc/centaur') contains a @('centaur-logo.png') file.
The file @('xdoc/topics.lisp') adds this directory as a resource directory.  If
all is well, you should see the logo below:</p>

<img src='res/centaur/centaur-logo.png'/>")

(add-resource-directory "centaur" "centaur")

(defxdoc testing
  :short "Testing new or revised XDOC strings"
  :long "<p>Contributors to the XDOC manual should check that their XDOC
 strings are well-formed.  This topic shows an easy way to check
 well-formedness of XDOC strings, without the need to build the manual.  Also
 discussed is a way to check for the absence of broken links by building the
 manual.</p>

 <p>To test a topic, first submit a suitable @(tsee in-package) form if
 necessary, and then to test your topic named, say, @('FOO'):</p>

 @({
 (include-book \"xdoc/top\" :dir :system)
 (defxdoc ...) ; or whatever form you have that includes an XDOC string
 :doc foo ; a bit noisy and slow the first time, but could do this twice
 })

 <p>The output should be free of obvious errors.  Otherwise, you can use the
 error message to debug the error; then submit your form and @(':doc foo')
 again.</p>

 <p>A XDOC feature (the second ``NEW'' feature in the @(see xdoc)
 documentation) avoids the need to invoke @(':doc') explicitly.  In brief: you
 can simply include community-book @('xdoc/debug'), for example by putting its
 include-book form in your acl2-customization file (see @(see
 acl2::acl2-customization)).</p>

 <p>Checking for broken links requires you to build the manual; for
 instructions, see the section ``Building the manual'' in the topic @(see
 acl2::books-certification).  This build will create a file
 @('books/doc/top.cert.out').  Search in that file for the word ``broken'' and
 you will find the following report of a broken link:</p>

 @({
 ;;; ACL2____SOME-BROKEN-LINK:
 ;;;    from ACL2-DOC
 })

 <p>If any other broken links are reported, you can modify the parent topic
 (e.g., @('ACL2-DOC') just above &mdash; but please leave that one in place!)
 to fix the indicated broken link.</p>

 <p>The @(':short') and @(':long') strings, if supplied, must consist entirely
 of standard characters (see @(see standard-char-p)), except that tabs are also
 allowed.  Making this check requires you to build the manual (as described
 just above).</p>")

(defpointer build-the-manual xdoc)
