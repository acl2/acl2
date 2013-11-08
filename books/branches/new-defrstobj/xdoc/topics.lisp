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

(defxdoc xdoc
  :short "<i>XDOC</i> is a tool for documenting ACL2 books.  You can use it to
access documentation about ACL2 and its books, to document your own books, and
to create custom web-based manuals.  It is intended as a replacement for ACL2
facilities like @(see defdoc), @(':doc'), and so on."

  :long "<h3>Getting the Documentation</h3>

<p>Most of the documentation below is about using XDOC to document your own
@(see acl2::books).  If you just want to browse the documentation, you probably
don't need to read any of this!  Instead, see either:</p>

<ul>

<li><b>The online version.</b> If you expect to have an internet connection
while using the documentation, you may be happy with the <a
href='http://fv.centtech.com/acl2/latest/doc/'>online XDOC manual</a> hosted by
<a href='http://www.centtech.com/'>Centaur Technology</a>.  This version covers
the latest released version of ACL2 and the corresponding version of the <a
href='http://code.google.com/p/acl2-books/'>ACL2 Community Books</a>.</li>

<li><b>A local version.</b> If you sometimes work without an internet
connection, or are using development snapshots of ACL2 and need up-to-date
documentation, you can build a local version of the documentation.  You first
need to build ACL2(h), then certify the @('centaur/doc') book as follows:

@({
  cd acl2-sources/books
  make USE_QUICKLISP=1 centaur/doc.cert
})

After this is built, the manual should be available at:

@({acl2-sources/books/centaur/manual/index.html})</li>

</ul>


<h3>Documenting your Books</h3>

<box><p><b><color rgb='#ff0000'>NEW</color></b> (experimental): When writing
documentation, you can now optionally have XDOC topics automatically displayed
as you submit new @(see defxdoc) forms&mdash;just add:</p>

@({
 (include-book \"xdoc/debug\" :dir :system)
})

<p>to your @(see acl2::acl2-customization) file, or include it while you are
developing your book.  Afterward, each @(see defxdoc) form you submit will be
immediately shown at the terminal, giving you a quick, text-mode preview that
may help you to diagnose any markup problems.</p></box>

<p>To use XDOC to document your own books, the first step is:</p>

@({
 (include-book \"xdoc/top\" :dir :system)
})

<p>This book loads very quickly and requires no ttags, and gives you:</p>

<ul>

<li>@(see defxdoc) and @(see defsection), the basic commands for adding
documentation &mdash; these are the XDOC alternatives to ACL2's @(see defdoc)
command.</li>

<li>A new @(':doc') command.  The book installs a new <see topic='@(url
ld-keyword-aliases)'>LD keyword alias</see> so that you (and your users) can
see both ordinary ACL2 documentation and XDOC documentation from the terminal
by just using @(':doc'), without thinking about which documentation system was
used to document which topic.</li>

</ul>

<p>Once you have documented your books, you may wish to create a manual that
can be viewed from a web browser.  You can do this quite easily with XDOC's
@(see save) command.  This command can be embedded in an ordinary ACL2 book, so
that your manual is automatically regenerated when you build your
project.</p>")

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
instance the @(see acl2::std), @(see acl2::str) or @(see acl2::osets)
libraries.</p>

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
href='http://en.wikipedia.org/wiki/HTML'>HTML</a>.  Note that in XML, beginning
and ending tags really need to be balanced.</p>

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
&amp;lt;, and also automatically add hyperlinks to documented functions.</p>

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


<h3>Structuring Documents</h3>

<p>For section headings,</p>
<ul>
 <li>@('<h1>') creates the biggest heading:<h1>H1 Example</h1></li>
 <li>@('<h2>') the next biggest:<h2>H2 Example</h2></li>
 <li>@('<h3>') a medium-sized heading:<h3>H3 Example</h3></li>
 <li>@('<h4>') the second smallest:<h4>H4 Example</h4></li>
 <li>@('<h5>') the smallest heading:<h5>H5 Example</h5></li>
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

<p>There's a special syntax to put in \"raw\" text.  This is especially useful
for examples and code fragments, where you don't want to have to escape special
character like &lt; with &amp;lt;</p>

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

<p>You can also dynamically evaluate ACL2 expressions using the preprocessor's
backtick syntax.  This may be useful for injecting constants and examples into
your documentation.  For instance:</p>

<ul>
<li>@('@(`(+ 1 2 3)`)')          produces @(`(+ 1 2 3)`)</li>
<li>@('@(`(mv 'a 10 state)`)')   produces @(`(mv 'a 10 state)`)</li>
<li>@('@(`acl2::*pkg-witness-name*`)') produces @(`acl2::*pkg-witness-name*`)</li>
</ul>

<p>By default, the backtick syntax introduces @('<tt>') tags and automatically
escaped any special XML characters like &lt;.  Sometimes this isn't what you
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
Note that it is quite easy to use @(':raw') incorrectly; you need to know the
right kind of escaping to use.</p>

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

<h3>Escaping of @</h3>

<p>Since @('@(') is intercepted by the preprocessor, you may occasionally need
to escape it.  You can write @('@@') to generate a single @('@') sign.</p>

<p>Besides @('@(') and @('@@'), the preprocessor leaves any other uses of
@('@') in tact.  So, most uses of @('@'), such as in email addresses, do not
need to be escaped.</p>")


(defxdoc save
  :short "Saves the XDOC database into files for web browsers, etc."

  :long "<p>Once you have documented your books with @(see defxdoc), you may
wish to create a manual that can be viewed from a web browser.</p>

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

 (xdoc::save \"./mylib-manual\")  ;; write the manual
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
          [:type      type]      ;; default is :fancy
          [:import    import]    ;; default is t
          <classic-options>)
})

<p>The only (required) argument to the @('save') command is the name of a
directory where the want the manual to go.  As might be expected:</p>

<ul>

<li>If the target directory does not exist, it will be created.</li>

<li>Any existing files in the target directory <color rgb=\"#ff0000\">may be
overwritten</color>.</li>

</ul>

<p>XDOC can generate two kinds of manuals.  By default, it generates a
so-called <i>fancy</i> manual, with a rich JavaScript interface that has, e.g.,
jump-to and search capabilities.  Alternately you can generate a much more
plain @(see classic-manual) by using @(':type :classic'), but we may move to
deprecate classic manuals in the future.</p>


<h3>Avoiding Unwanted Documentation</h3>

<p>By default, the @('save') command will automatically import:</p>
<ul>
<li>the documentation for the ACL2 theorem prover</li>
<li>any @(see defdoc) style documentation from books you have loaded</li>
<li>the documentation for @('xdoc') itself.</li>
</ul>

<p>You can turn off <b>most</b> of this by setting @(':import nil') in your
@('save') command.</p>

<p>However, you may find that even after setting @(':import nil'), some
extraneous documentation is still being included!  For instance, you may find
documentation from libraries like @(see str) and @(see oslib) in your
output.</p>

<p>This is because @('xdoc/save') includes some supporting books that are,
themselves, documented.  If you really want precise control over what goes into
your manual, then, you may want to do something like this:</p>

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

 (xdoc::save \"./mylib-manual\" :import nil)
})")


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
2013, this comes to around 25 MB of data for the basic @('centaur/doc.lisp')
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


(defxdoc classic-manual
  :parents (save)
  :short "Description of @(':type :classic') manuals."

  :long "<box><p><b>Note</b>: we generally discourage the use of classic
manuals.  We may deprecate them in the future.</p></box>

<p>If you run @(see save) with @(':type :classic'), it will write out
a manual in the \"classic\" format.  In this case, the resulting manual
directory will include:</p>

<ul>

<li>@('xml/'), a subdirectory with a @('.xml') file for each topic and some
supporting files, and</li>

<li>@('Makefile'), a Makefile for converting these files into other formats,
and</li>

<li>@('preview.html'), a web page that lets you directly view the XML files
using your web browser.</li>

</ul>

<p>Many web browsers can directly display XML files, so you may be able to view
@('preview.html') without any additional steps.</p>


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
    ... events ...)
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
   (defthm foo-thm2 ...))
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
included in the documentation page for that section.  This helps to avoid
copying-and-pasting code into the manual, and keeps it up-to-date as the code
changes.</p>


<h3>Ordinary Sections</h3>

<p>The @(':parents'), @(':short'), and @(':long') keywords are optional.  If
any of these keywords are provided, they will be used to introduce a @(see
defxdoc) command; otherwise no documentation will be generated.</p>

<p>By default, the @(':long') string you give will be automatically extended
with a \"Definitions and Theorems\" part that lists all the (non-local)
definitions and theorems introduced in the section.  In the above example, the
@(':long') field would be extended with:</p>

@({
 <h3>Definition and Theorems</h3>
 @(def foo)
 @(thm foo-thm1)
 @(thm foo-thm2)
})

<p>If you do not want this automatic documentation, you can turn it off with
@(':autodoc nil').</p>


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
  :short "Fancy @('(progn ...)') with a name and @(see xdoc) support."

  :long "<p>The @('defsection-progn') macro is like @(see defsection) except
that it generates @({(progn ...)}) instead of an @({(encapsulate nil ...)})</p>

<p>This has a number of consequences, mostly having to do with the scope of
@('local') events within the section.  In short, a @('defsection-progn') does
not introduce a new local scope, but a @('defsection') does.</p>")


(defxdoc undocumented
  :short "Placeholder for undocumented topics.")


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
</ul>")



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
