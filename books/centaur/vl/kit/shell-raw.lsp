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

(in-package "ACL2")

(defun vl::vl-shell-fn (argv state)
  (declare (ignore argv))
  (format t "VL Verilog Toolkit
Copyright (C) 2008-2013 Centaur Technology <http://www.centtech.com>

  This program is free software; you can redistribute it and/or modify it under
  the terms of the GNU General Public License as published by the Free Software
  Foundation; either version 2 of the License, or (at your option) any later
  version.  This program is distributed in the hope that it will be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
  FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
  more details.  You should have received a copy of the GNU General Public
  License along with this program; if not, write to the Free Software
  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301,
  USA.

,-------------------------,
|  VL Interactive Shell   |     This is an interactive ACL2 shell with VL pre-
|     (for experts)       |     loaded.  To learn about ACL2 (and hence how to
|                         |     use this shell) see the ACL2 homepage:
|   Type :quit to quit    |      http://www.cs.utexas.edu/users/moore/acl2
`-------------------------'

")

  (f-put-global 'ld-verbose nil state)
  ;; well, this doesn't seem to actually work and get us into an interactive
  ;; LP shell.  But at least we get into a raw-lisp shell, which is probably
  ;; fine for now.
  (lp)
  state)

