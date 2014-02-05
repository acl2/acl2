; Quicklisp setup for Centaur books
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "ACL2")
(include-book "tools/include-raw" :dir :system)
; cert_param: (uses-quicklisp)

(defttag :quicklisp)

(value-triple (cw "~%~%~
***********************************************************************~%~
*****                                                             *****~%~
*****                  IF YOUR BUILD FAILS                        *****~%~
*****                                                             *****~%~
***** The include-raw form here can fail if you try to certify    *****~%~
***** this book without first getting quicklisp installed.  You   *****~%~
***** need to run 'make' first.                                   *****~%~
*****                                                             *****~%~
***** See books/centaur/README.html for detailed directions for   *****~%~
***** properly building the Centaur books.                        *****~%~
*****                                                             *****~%~
***********************************************************************~%~
~%"))

; (depends-on "inst/setup.lisp")
(include-raw "inst/setup.lisp"
             :do-not-compile t
             :host-readtable t)

; (depends-on "base-raw.lsp")
(local (include-raw "base-raw.lsp" :host-readtable t))