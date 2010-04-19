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

(defttag xdoc-raw)

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

   :long "<p>New XDOC documentation topics should normally be added with @(see
defxdoc).  Unfortunately, this isn't possible from Raw Lisp, because
<tt>defxdoc</tt> expands to a <tt>make-event</tt>, and <tt>make-event</tt>
can't be used from raw lisp.  So, to document raw lisp code, we provide
<tt>defxdoc-raw</tt>.</p>

<p><tt>Defxdoc-raw</tt> takes the same arguments as <tt>defxdoc</tt>, but
adds its documentation to a Lisp variable rather than to the usual table.
Because of this, <tt>defxdoc-raw</tt> is not an event.</p>

<p>Using <tt>defxdoc-raw</tt> requires a ttag.  Because of this, it is not
included in the ordinary <tt>defxdoc</tt> book, and you will need to separately
include it, e.g., via:</p>

<code>
 (include-book \"xdoc/defxdoc-raw\" :dir :system :ttags :all)
</code>"))


