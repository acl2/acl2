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


; all.lisp -- most users should ignore this book and include top.lisp instead.
;
; Unlike top.lisp, this book depends on everything else in xdoc except for
; bookdoc.dat.  It may be useful as a target in some Makefiles that want to
; ensure that all of XDOC gets built.  Note that your Makefile will probably
; also want to generate bookdoc.dat.

(in-package "XDOC")

(include-book "base")
(include-book "top")
(include-book "defxdoc-raw")
(include-book "names")

(include-book "display")
(include-book "import-acl2doc")
(include-book "mkdir")
(include-book "mkdir-raw")
(include-book "parse-xml")
(include-book "preprocess")
(include-book "save-classic")
(include-book "topics")
(include-book "write-acl2-xdoc")


