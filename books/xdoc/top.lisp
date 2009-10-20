; XDOC Documentation System for ACL2
; Copyright (C) 2009 Centaur Technology
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "XDOC")
(include-book "defxdoc")
(include-book "save")

(defxdoc xdoc 
  :short 
  "<p><em>XDOC</em> is a new mechanism for documenting ACL2 libraries, and is
intended as a replacement for ACL2 facilities such
as <tt>defdoc</tt>, <tt>:doc</tt>, and so on.</p>"
  :long
  "<h3>Note: Experimental</h3>

<p>This is all very preliminary.  I reserve the right to make broad changes 
to how it works, the markup, etc., for the time being.</p>

<h3>Writing Documentation</h3>

<p>To begin using XDOC, the first step is to include the <tt>xdoc/xdoc</tt>
book in your library, e.g.,</p>

<code>(include-book \"xdoc/xdoc\" :dir :system)</code>

<p>This book is intentionally quite minimal.  It loads quickly, mainly keeps to
the <tt>XDOC</tt> package, and adds no theorems.  In short, it has a light
footprint and should not interfere with your library.</p>

<p>Once the book is loaded, you can document your own functions using the 
<tt>defxdoc</tt> command.</p>

<code>(defxdoc name
  :parents (topic1 topic2 ...)
  :short \"short description\"
  :long \"longer description\"
  )</code>

<p>All of the keyword arguments are optional.</p>

<ul>
 <li><tt>name</tt> is the name of this documentation topic</li>
 <li><tt>parents</tt> let you associate this documentation with other topics</li>
 <li><tt>short</tt> should be a short description, suitable for inlining in 
     other pages</li>
 <li><tt>long</tt> should be a longer description that contains the detailed
     documentation</li>
</ul>

<p>To understand how to format the <tt>short</tt> and <tt>long</tt> strings,
see:</p>

<dl>
 <dt>@(csee markup)</dt>
 <dd>Describes our basic formatting commands</dd>

 <dt>@(csee preprocessor)</dt>
 <dd>The preprocessor is used to insert function definitions, theorems, topic 
     links, etc.</dd>
</dl>


<h3>Saving Documentation</h3>

<p>The <tt>defxdoc</tt> command only adds documentation to the database.  To
actually see the documentation, you need to carry out the preprocessing and
save the resulting <tt>.xml</tt> files to disk.</p>

<code>(include-book \"xdoc/save\" :dir :system)
(xdoc::save dir)</code>

<p>where <tt>dir</tt> is the directory you want the documentation written
to.  Note that files in <tt>dir</tt> may be overwritten!</p>


<h3>Viewing Documentation</h3>

<p>Once the documentation has been saved, you can view the resulting <tt>.xml</tt> 
files directly in a web browser.</p>

<p>Future work includes providing tools to translate these XML files into other
formats, and for viewing them with some kind of <tt>:xdoc</tt> command from 
directly within ACL2.</p>")


(defxdoc markup
  :parents (xdoc)
  :short
  "<p>XDOC documentation strings are mainly written in a simple XML markup
language.  XML is basically similar to HTML, but is very insistent that tags
begin and end in balance.</p>"
  :long 
  "<h3>Formatting Text</h3>

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

<h3>Hyperlinks</h3>

<p>Links between documentation topics are handled by the @(see preprocessor).
To link to external resources, you can use ordinary HTML-style links, e.g.,</p>

<code>&lt;a href=\"http://www.centtech.com/\"&gt;Centaur Technology&lt;/a&gt;</code>

<p>Produces a link to <a href=\"http://www.centtech.com/\">Centaur
Technology</a>.</p>

<h3>Document Structure</h3>

<p>Paragraphs should begin and end with the <tt>&lt;p&gt;</tt> tag.  (You can also 
do individual line breaks with <tt>&lt;br/&gt;</tt>.)</p>

<p>For section headings, <tt>&lt;h1&gt;</tt> creates the biggest heading,
<tt>&lt;h2&gt;</tt> the next biggest, and so on.  The smallest heading is
<tt>&lt;h5&gt;</tt>.</p>

<p>Bulleted and numbered lists work as in HTML.  The list itself begins with
<tt>&lt;ul&gt;</tt> (for bulleted lists) or <tt>&lt;ol&gt;</tt> (for numbered lists).
Each list element is an <tt>&lt;li&gt;</tt> tag.  For instance,</p>

<code>&lt;ul&gt;
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

<code>&lt;dl&gt;
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
  :parents (xdoc)
  :short
  "<p>In addition to its @(see markup) language, XDOC includes a preprocessor
which can be used to interpret certain directives of the form
<tt>@@(...)</tt>.</p>"
  :long
  "<h3>Functions and Theorems</h3>

<p>To insert function definitions (or pieces of definitions) into your
documentation, you can use:</p>
<ul>
 <li><tt>@@(def fn)</tt>, expands to the definition of the function <i>fn</i></li>
 <li><tt>@@(body fn)</tt>, just the body of <i>fn</i></li>
 <li><tt>@@(formals fn)</tt>, just the formals of <i>fn</i></li>
 <li><tt>@@(measure fn)</tt>, just the measure of <i>fn</i></li>
</ul>

<p>We expect that <tt>def</tt> and <tt>body</tt> directives will
expand to large code fragments, so they are automatically wrapped in
<tt>&lt;code&gt;</tt> blocks.  The other directives just become text, and 
you can wrap whatever formatting commands you like around them and use
them inline in paragraphs, etc.</p>

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

<code>&lt;see topic=\"mangled-topic-name\"&gt;printed-topic-name&lt;/see&gt;</code>

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



<h3>Escaping of @</h3>

<p>Since <tt>@@(</tt> is intercepted by the preprocessor, you may occasionally 
need to escape it.  You can write <tt>@@@@</tt> to generate a single <tt>@</tt>
sign.</p>

<p>Besides <tt>@@(</tt> and <tt>@@@@</tt>, the preprocessor leaves any other uses
of <tt>@</tt> in tact.  So, most uses of <tt>@</tt>, such as in email
addresses, do not need to be escaped.</p>")


