; VL Verilog Toolkit
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "VL")
(include-book "progutils")
(include-book "tools/include-raw" :dir :system)
(include-book "std/util/define" :dir :system)
; (depends-on "shell-raw.lsp")

(defconst *vl-shell-help* "
vl shell:  Starts an interactive VL command loop (for experts).

Usage:     vl shell    (there are no options)

VL is built atop the ACL2 theorem prover.  The VL shell gives you access to the
ACL2 command loop, with all of the VL functions already built in.

This is mainly useful for VL developers who want to debug problems or explore
adding new functionality.

")

(define vl-shell ((argv string-listp) &key (state 'state))
  :returns state
  :ignore-ok t
  (progn$ (die "Raw lisp definition not installed?")
          state))


(defttag :vl-shell)
(acl2::include-raw "shell-raw.lsp")

