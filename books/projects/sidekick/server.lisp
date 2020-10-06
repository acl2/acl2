; ACL2 Sidekick
; Copyright (C) 2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "SIDEKICK")
(include-book "quicklisp/hunchentoot" :dir :system)
(include-book "io")
(include-book "std/util/defconsts" :dir :system)
(include-book "oslib/catpath" :dir :system)
(include-book "session")
(include-book "disassemble")
(include-book "lookup")
(include-book "webcommand")
(include-book "lint")
(include-book "eventdata")
(include-book "explore")
(include-book "centaur/misc/tshell" :dir :system)
(defttag :sidekick)
(set-state-ok t)
(program)

(defconsts *sidekick-dir* (cbd))

(define start (&key (port maybe-natp))
  :parents (sidekick)
  :short "Start the ACL2 sidekick web server."
  (declare (ignorable port))
  (raise "Under the hood definition not installed."))

(define stop ()
  :parents (sidekick)
  :short "Stop the ACL2 sidekick web server."
  (raise "Under the hood definition not installed."))

; (depends-on "server-raw.lsp")
(include-raw "server-raw.lsp"
             :host-readtable t)


(xdoc::add-resource-directory "sidekick" "screenshots")

(defxdoc sidekick
  :parents (acl2::projects)
  :short "The ACL2 Sidekick is a graphical add-on for ACL2.  It extends your
ACL2 session with a web server so that you can interact with ACL2 through your
browser.  You use the Sidekick along with&mdash;not instead of&mdash;Emacs or
your favorite ACL2 development environment."

  :long "<p><b>Note</b>: the Sidekick is <b>highly experimental</b> software
and at this point is mostly a proof of concept.</p>

<p>Screenshots:</p>
<ul>
<li><a href='res/sidekick/emacs.png'>Sidekick with Emacs</a></li>
<li><a href='res/sidekick/eclipse.png'>Sidekick with Eclipse/ACL2(s)</a></li>
</ul>

<h3>Basic Setup</h3>

<p>The Sidekick has been tested on <a href='http://ccl.clozure.com'>CCL</a> on
Linux with Firefox or Chromium as the browser.  It might possibly work on other
Lisps, most likely SBCL and LispWorks.</p>

<p>To build the Sidekick, build ACL2 as usual and then certify at least the
@('basic') and @(see acl2::quicklisp) books, e.g.,</p>

@({
    $ cd acl2
    $ make LISP=ccl
    $ cd acl2/books
    $ make USE_QUICKLISP=1 basic quicklisp
})

<p>Then certify the sidekick books:</p>

@({
    $ cd acl2/books/projects/sidekick
    $ cert.pl top     # should produce top.cert
})

<p>The Sidekick should now be ready.  To try it out, go to the
@('projects/sidekick/demo') directory and follow along with @('demo.lsp').</p>


<h4>Sidekick Images</h4>

<p>For instant startup times, you can build an ACL2 image with the Sidekick
built in.</p>

@({
    $ cd acl2/books/projects/sidekick
    $ make           # should produce a 'sidekick' executable
    $ ./sidekick
})

<p>You can then use this @('sidekick') executable instead of invoking your
normal @('saved_acl2') image when doing interactive development.</p>


<h4>Browser Launching</h4>

<p>You can tell the Sidekick to automatically launch a web browser when it
boots up by setting the @('SIDEKICK_BROWSER') environment variable.  For
instance:</p>

@({
    $ export SIDEKICK_BROWSER=\"firefox\"
})

<p>Whatever command you supply will simply be invoked, in the background, with
the argument @('http://localhost:9000/') (or similar).</p>


<h4>Other Ports</h4>

<p>The Sidekick will try to listen on port 9000 by default, but this can be
adjusted using SIDEKICK_PORT.  For instance:</p>

@({
    $ export SIDEKICK_PORT=9001
})

<p>You can also explicitly start the sidekick on a different port by using,
e.g., @('(sidekick::start 9001)').</p>")
