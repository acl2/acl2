; Arithmetic-5 Library
; Copyright (C) 2009 Robert Krug <rkrug@cs.utexas.edu>
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; banner.lisp
;;;
;;; This file contains a message about how to enable non-linear
;;; arithmetic.  It is displayed upon including this library.  In
;;; order to avoid seeing the message twice, be sure that there is no
;;; compiled file for top.lisp.  The standard "make" procedure ensures
;;; this through top.acl2.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 (prog2$
  (observation-cw
   'non-linear-arithmetic
   "To turn on non-linear arithmetic, execute :~|~%~Y02~|~%~
    or :~|~%~Y12~|~%~
    See the README for more about non-linear arithmetic and ~
    general information about using this library."
   '(set-default-hints '((nonlinearp-default-hint
                          stable-under-simplificationp
                          hist pspv)))
   '(set-default-hints '((nonlinearp-default-hint++ 
                          id stable-under-simplificationp
                          hist nil)))
   nil)
  '(value-triple nil))
 :check-expansion t)

