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

; defxdoc-raw-impl.lsp - raw Lisp version of all-xdoc-topics/defxdoc-raw-fn.

(in-package "XDOC")
(defvar *raw-xdoc-list* nil)

(defun defxdoc-raw-fn (name parents short long pkg)
  (let* ((pkg   (or pkg (package-name *package*)))
         (entry (list (cons :from "[defxdoc-raw]")
                      (cons :name name)
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
              (value nil))
    (value (append *raw-xdoc-list*
                   (get-xdoc-table (w state))))))
