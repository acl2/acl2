; Arithmetic-3 Library
; Copyright (C) 2004 Robert Krug <rkrug@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.
;
; This program is distributed in the hope that it will be useful but WITHOUT
; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
; FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
; details.
;
; You should have received a copy of the GNU General Public License along with
; this program; if not, write to the Free Software Foundation, Inc., 51
; Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

(in-package "ACL2")

; In order to avoid seeing the following message twice, be sure that there is
; no compiled file for top.lisp.  The standard "make" procedure ensures this
; through top.acl2.
(value-triple
 (cw "~%To turn on non-linear arithmetic:~|~%~Y01"
     '(set-default-hints '((nonlinearp-default-hint
                            stable-under-simplificationp hist pspv)))
     nil)
 :on-skip-proofs t)
