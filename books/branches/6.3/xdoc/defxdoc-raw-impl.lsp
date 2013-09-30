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

; defxdoc-raw-impl.lsp - raw Lisp version of all-xdoc-topics/defxdoc-raw-fn.

(in-package "XDOC")
(defvar *raw-xdoc-list* nil)

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

  :long "<p>@('Defxdoc-raw') allows you to document raw-lisp code with XDOC.
It isn't possible to do this with the ordinary @(see defxdoc) command because
@('defxdoc') is a macro that expands to a @('make-event'), and @('make-event')
is not permitted in raw Lisp.</p>

<p>@('Defxdoc-raw') is not available just by including @('xdoc/top'), because
it requires a ttag.  So, to use it you will need:</p>

@({
 (include-book \"xdoc/defxdoc-raw\" :dir :system)
})

<p>@('Defxdoc-raw') takes the same arguments as @(see defxdoc), but adds its
documentation to a Lisp variable rather than to the XDOC table.  Note that the
@(':xdoc') and @(see save) commands already know about this table, so to the
end-user, documentation added by @('defxdoc-raw') is not any different than
documentation added by @('defxdoc').</p>")

(defun all-xdoc-topics (state)
  (if (not (acl2::live-state-p state))
      (prog2$ (er hard? 'all-xdoc-topics "all-xdoc-topics requires a live state.")
              (mv nil state))
    (mv (append *raw-xdoc-list*
                (get-xdoc-table (w state)))
        state)))
