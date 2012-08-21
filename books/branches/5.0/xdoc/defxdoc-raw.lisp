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

; defxdoc-raw.lisp
;
; This book requires a TTAG.  You should typically not need to include it
; directly unless you want to document some raw-lisp code with xdoc.

(in-package "XDOC")
(include-book "base")
(set-state-ok t)

(defttag :xdoc)

(remove-untouchable 'read-acl2-oracle t)

(defun all-xdoc-topics (state)
  (declare (xargs :mode :program))
  (prog2$
   (er hard? 'all-xdoc-topics "all-xdoc-topics not yet defined.")
   (mv-let (err val state)
     (read-acl2-oracle state)
     (declare (ignore err))
     (mv val state))))


(acl2::progn!
 (set-raw-mode t)

 (defparameter *raw-xdoc-list* nil)

 (defun defxdoc-raw-fn (name parents short long)
   (let* ((pkg   (package-name *package*))
          (entry (list (cons :name name)
                       (cons :base-pkg (acl2::pkg-witness pkg))
                       (cons :parents parents)
                       (cons :short short)
                       (cons :long long))))
     (push entry *raw-xdoc-list*)
     nil))

 (defxdoc-raw defxdoc-raw
   :parents (xdoc)
   :short "Add documentation in raw mode."
   :long "<p><tt>Defxdoc-raw</tt> allows you to document raw-lisp code with
XDOC.  It isn't possible to do this with the ordinary @(see defxdoc) command
because <tt>defxdoc</tt> is a macro that expands to a <tt>make-event</tt>, and
<tt>make-event</tt> is not permitted in raw Lisp.</p>

<p><tt>Defxdoc-raw</tt> is not available just by including <tt>xdoc/top</tt>,
because it requires a ttag.  So, to use it you will need:</p>
<code>
 (include-book \"xdoc/defxdoc-raw\" :dir :system)
</code>

<p><tt>Defxdoc-raw</tt> takes the same arguments as @(see defxdoc), but adds
its documentation to a Lisp variable rather than to the XDOC table.  Note that
the <tt>:xdoc</tt> and @(see save) commands already know about this table, so
to the end-user, documentation added by <tt>defxdoc-raw</tt> is not any
different than documentation added by <tt>defxdoc</tt>.</p>")

 (defun all-xdoc-topics (state)
   (if (not (acl2::live-state-p state))
       (prog2$ (er hard? 'all-xdoc-topics "all-xdoc-topics requires a live state.")
               (mv nil state))
     (mv (append *raw-xdoc-list*
                 (get-xdoc-table (w state)))
         state))))


