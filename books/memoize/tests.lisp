; Memoize Library
; Copyright (C) 2013 Centaur Technology
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
;
; This library is a descendant of the memoization scheme developed by Bob Boyer
; and Warren A. Hunt, Jr. which was incorporated into the HONS version of ACL2,
; sometimes called ACL2(h).

; File tests-raw.lsp loads timer.lsp (via top.lisp), which references
; most-positive-mfixnum, which is only defined in #+hons.  I (Matt K.) added
; this directive when an attempt failed to compile this certified book, using
; ACL2 (not ACL2(h)).
; cert_param: (hons-only)

(in-package "MEMOIZE")
(include-book "top")

(defttag :memoize-tests)

(progn!
 (set-raw-mode t)
 (load "tests-raw.lsp"))

; (depends-on "tests-raw.lsp")



