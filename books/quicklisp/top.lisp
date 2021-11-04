; ACL2 Quicklisp Interface
; Copyright (C) 2008-2014 Centaur Technology
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
; Contributing author: Alessandro Coglio <coglio@kestrel.edu>

(in-package "ACL2")
(include-book "base")
(include-book "bordeaux")
(include-book "bt-semaphore")
(include-book "cl-fad")
; (include-book "external-program") ; removed Nov 2017
(include-book "fastnumio")
(include-book "html-template")
(include-book "hunchentoot")
(include-book "osicat")
(include-book "shellpool")
(include-book "uiop")
(include-book "cffi")

(defsection quicklisp
  :parents (interfacing-tools)
  :short "An ACL2 connection to the <a
href='http://www.quicklisp.org'>Quicklisp</a> system for installing Lisp
libraries."

  :long "<h3>About Quicklisp</h3>

<p>Quicklisp is a Common Lisp equivalent to tools like <a
href='http://www.cpan.org/'>CPAN</a> for <a
href='http://www.perl.org/'>Perl</a>, or <a
href='http://rubygems.org/'>RubyGems</a> for <a
href='http://www.ruby-lang.org/'>Ruby</a>.  It lets you to easily install and
load the latest versions of Common Lisp libraries (and their dependencies).</p>

<p>To make it easy to use Quicklisp from ACL2 we have developed some wrapper
books in the @('books/quicklisp') directory.  These books serve as the
basis for other libraries such as @(see oslib) and the ACL2 @(see bridge).
Naturally, all of these books require @(see trust-tag)s.</p>

<p>Every ANSI-compliant host Common Lisp suitable for ACL2 should support the
use of Quicklisp, where occasionally libraries may need to be installed.  As of
late 2016, all host Common Lisp implementations suitable for ACL2 are
sufficiently ANSI-compliant for the use of Quicklisp except for GCL.</p>

<p>Because of this, if you want to use the Quicklisp books or any libraries
that depend on them, you may <b>need to manually enable</b> the Quicklisp
build.  Please see the instructions in @(see books-certification) for the most
up-to-date details about how to do this.</p>

<p>In order to certify the Quicklisp books, OpenSSL may need to be installed in
the system.  At least one instance was observed in which the certification of
the Quicklisp books on MacOS Catalina with SBCL failed initially, but worked
after installing OpenSSL via Homebrew (using the command @('brew install
openssl')).  The initial certification error did not explicitly mention
OpenSSL, but rather a @('SIGABRT'); thus, if this kind of certification error
is observed, installing OpenSSL may solve the problem.  Additionally, on a Mac
Arm64 (e.g. M1) machine, you may need to create symlinks to Homebrew's OpenSSL
library files in @('/usr/local/lib') (using the command ``@('ln -s
/opt/homebrew/opt/openssl/lib/*.dylib /usr/local/lib')'').  Note that Homebrew,
which is a package/application manager for Mac, can be installed from <a
href='https://brew.sh'>https://brew.sh</a>, following the simple instructions
there.</p>

<h3>Using the Quicklisp Books</h3>

<p>Most ACL2 users will have no reason to <i>directly</i> load the Quicklisp
books in @('books/quicklisp').  Instead, you will want to load
higher-level ACL2 libraries like @(see oslib) or the ACL2 @(see bridge).  This
is because the Quicklisp books only deal with getting the appropriate Common
Lisp libraries loaded&mdash;they do not, by themselves, introduce ACL2 wrapper
functions for actually using the associated Lisp libraries.</p>

<p>However, if you are an advanced user who wants to use Common Lisp libraries
to develop your own ACL2 extensions, then you will typically want to:</p>

<ol>

<li>Include the books for whichever libraries you want to use.  For instance,
to load <a href='http://weitz.de/cl-fad/'>CL-FAD</a> and <a
href='https://common-lisp.net/project/osicat/'>OSICAT</a> you could do:

@({
    (include-book \"quicklisp/cl-fad\" :dir :system)
    (include-book \"quicklisp/osicat\" :dir :system)
})</li>

<li>Add your own @(see trust-tag)s, drop into raw Lisp with @(see include-raw),
and implement your extension.  How exactly to do this is, alas, far beyond the
scope of this documentation, but we do try to give some hints below.</li>

</ol>


<h3>Finding Quicklisp Libraries</h3>

<p>If you don't know much about Quicklisp and are wanting to find out about the
available libraries, the following may be useful:</p>

<ul>

<li><a href='http://www.cliki.net/'>CLiki</a> is a Common Lisp wiki.  See
especially the page about <a
href='http://www.cliki.net/Current%20recommended%20libraries'>recommended
libraries</a>.</li>

<li><a href='http://quickdocs.org/'>Quickdocs</a> purports to provide
documentation for all of the libraries in Quicklisp.</li>

</ul>


<h3>Adding Quicklisp Libraries</h3>

<p>The books in @('quicklisp') only wrap up a few Common Lisp libraries
that we have found to be useful.  But it should be very easy to experiment with
any other Quicklisp libraries.</p>

<p>Basic steps:</p>

<ul>

<li>Edit @('quicklisp/update-libs.lsp') and add the libraries you want
to the list.</li>

<li>Run the @('update-libs.sh') script.  This should download the new libraries
into your @('quicklisp/bundle') directory.</li>

<li>Extend @('quicklisp/base-raw.lsp') to load the new library and
certify it.  This @('base') book really is just a way to get the bundle loaded
into an ACL2 session so that the libraries can be found as needed.  It
also (locally) loads the libraries that we expect to use, which ensures
everything gets downloaded at the same time, and avoids potential problems with
simultaneously compiling Common Lisp libraries during parallel builds.</li>

<li>Add a new @('quicklisp/yourlib.lisp') book, styled after the other
books in the Quicklisp directory.  The book doesn't really need to live in the
@('quicklisp') directory, but keeping them there makes it easy to see what we
are depending on and, if necessary, to change the way the wrappers work.</li>

<li>Include your new book in @('quicklisp/top.lisp'), just for
completeness.  (Hrmn, actually this book probably isn't very useful for
anything.)</li>

</ul>

<p>Note that you can also develop your own Common Lisp libraries or do one-off
hacking using the @('local-projects') feature of the bundle directory.  See the
documentation for <a
href='http://www.quicklisp.org/beta/bundles.html'>Quicklisp Bundles</a> for
more information.</p>


<h3>Developing ACL2 Extensions</h3>

<p>After you've added a Common Lisp library, how do you actually use it from
ACL2?  As an example, say we want to make use of the <a
href='http://common-lisp.net/project/cl-json/'>CL-JSON</a> library.</p>

<p>Normally you would do something like this:</p>

@({
    ; ** my-book.lisp
    (in-package \"MY-PKG\")

    ; ** Load the library (after adding it as described above)
    (include-book \"quicklisp/cl-json\" :dir :system)

    ; ** [OPTIONAL] develop a logical story so you can use the
    ; ** library from proper ACL2 functions...
    (defun foo (x y z)
      (declare (xargs :guard ...))
      (progn$
       (er hard? 'foo \"Raw lisp definition not installed?\")
       (logical-story-of-foo x y z)))

    ; ** Add a ttag since we're going to use include-raw
    (defttag :my-book)

    ; ** Tell cert.pl that we're going to be loading raw Lisp code
    ;; (depends-on \"my-book-raw.lsp\")

    ; ** Actually include the raw Lisp code for our book
    (include-raw \"my-book-raw.lsp\"
                 :do-not-compile t
                 :host-readtable t)
})

<p>You usually need to use the @(':host-readtable') option because real Common
Lisp libraries will use things (packages, floats, etc.) that ACL2's reader will
reject.  You usually need to use @(':do-not-compile') because otherwise you
tend to not have the right packages around at compile time.  You may be able to
work around that using @('eval-when').</p>

<p>The corresponding raw file, then would look something like this:</p>

@({
    ; ** my-book-raw.lsp
    (in-package \"MY-PKG\")

    ; ** Redefine our interface functions, freely using cl-json
    ; ** functionality
    (defun foo (x y z)
      (cl-json:...))
})")
