; Quicklisp setup for Centaur books
; Copyright (C) 2008-2012 Centaur Technology
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
; (depends-on "setup.lisp")


; Quicklisp (www.quicklisp.org) is a tool for installing Common Lisp libraries,
; somewhat like CPAN for Perl, GEMS for Ruby.
;
; This file is a way to get Quicklisp loaded in an ACL2 session.  It doesn't
; load anything beyond Quicklisp itself, so, e.g., to load an actual Quicklisp
; package, you'll need to do something like:
;
;   (ql:quickload "cl-json")
;
; In your own ACL2 book.  Obviously doing this will require a ttag.  For that
; matter, even loading this Quicklisp book requires a ttag.

(defttag :quicklisp)
(include-raw "setup.lisp" :do-not-compile t :host-readtable t)