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
(include-book "tools/include-raw" :dir :system)
; (depends-on "defxdoc-raw-impl.lsp")
(set-state-ok t)

(defttag :xdoc)

(defun all-xdoc-topics (state)
  (declare (xargs :mode :program))
  (prog2$
   (er hard? 'all-xdoc-topics "all-xdoc-topics not yet defined.")
   (mv-let (err val state)
     (read-acl2-oracle state)
     (declare (ignore err))
     (mv val state))))

(acl2::include-raw "defxdoc-raw-impl.lsp")
