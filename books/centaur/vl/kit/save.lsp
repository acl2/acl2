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
(ld "cert.acl2")
(in-package "VL")
(include-book "top")
(set-deferred-ttag-notes t state)
(set-gag-mode :goals)

;; (encapsulate
;;   ()
;;   (defttag vl-lint)
;;   (remove-untouchable acl2::writes-okp nil))
;; (assign acl2::writes-okp t)

:q

(save-exec "../bin/vl" "VL Verilog Toolkit")
