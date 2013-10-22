; cert.pl build system
; Copyright (C) 2008-2011 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>
;
; NOTE: This file is not part of the standard ACL2 books build process; it is
; part of an experimental build system.  The ACL2 developers do not maintain
; this file.

(in-package "ACL2")

; make_cert.lsp
;
; See make_cert.sh.  This file just gives us a way to make ACL2 exit with a
; different status code depending upon whether certification was successful or
; failed.  This way we don't have to ask a file system that might occasionally
; suffer from NFS lag.

(defun horrible-include-book-exit (name state)
  (declare (xargs :mode :program :stobjs state))

; This function exits with code 43 if the file 'name' has been included.
; Otherwise, it exits with code 0.

  (mv-let (full-name dir-name familiar-name)
    (parse-book-name (cbd) name ".lisp" 'horrible-include-book-exit state)
    (declare (ignore dir-name familiar-name))
    (if (assoc-equal full-name (global-val 'include-book-alist (w state)))
        (exit 43)
      (exit 0))))
