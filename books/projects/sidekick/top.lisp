; ACL2 Sidekick
; Copyright (C) 2014 Kookamara LLC
;
; Contact:
;   Kookamara LLC
;   11410 Windermere Meadows, Austin TX, 78759, USA.
;   http://www.kookamara.com/
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
