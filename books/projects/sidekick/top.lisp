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
(include-book "server")
(program)

(defxdoc sidekick
  :short "A supplemental, web-based, graphical interface to ACL2 (very
experimental)."

  :long "<box><p><b>Note</b>: This is extremely preliminary.  It has been
tested on CCL.  It might possibly work on other Lisps, most likely SBCL and
LispWorks.  Contact Jared Davis with any feedback or enhancements.</p></box>

<p>The ACL2 Sidekick is an add-on that allows you to interact with an ordinary
ACL2 session using a web-based interface.  This interface is <b>not</b> any
kind of replacement for Emacs or your editor of choice.  It is merely meant to
supplement the usual ACL2 read-eval-print loop with graphical capabilities.</p>

<h3>Usage</h3>

<ol>

<li>Certify the sidekick books, e.g., with
@({
    $ cd books
    $ make sidekick USE_QUICKLISP=1
})</li>

<li>Run (or add to your @(see acl2-customization) file):
@({
    (include-book \"projects/sidekick/top\")
})</li>

<li>Launch ACL2 as normal, point your web browser to @('http://localhost:9000')</li>

</ol>")

(make-event
 (b* (((when (f-get-global 'acl2::certify-book-info state))
       ;; Certifying the top book, don't start sidekick.
       (value '(value-triple :invisible)))
      ((mv & no-autoload state) (getenv$ "SIDEKICK_NO_AUTOLOAD" state))
      ((when (and (stringp no-autoload)
                  (not (equal no-autoload ""))))
       (value '(value-triple :invisible))))
   (start)
   (value '(value-triple :invisible)))
 :check-expansion t)
