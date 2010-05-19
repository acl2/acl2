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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; default-hint.lisp
;;;
;;; This book contains the definition of the default hint we
;;; will be using to control nonlinear arithmetic.  We put it
;;; into this seperate file for ease of maintenance.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defun nonlinearp-default-hint (stable-under-simplificationp hist pspv)
  (cond (stable-under-simplificationp
         (if (not (access rewrite-constant
                          (access prove-spec-var pspv :rewrite-constant)
                          :nonlinearp))
             (prog2$
              (cw "~%~%[Note: We now enable non-linear arithmetic.]~%~%")
              '(:computed-hint-replacement t
                                           :nonlinearp t))
           nil))
        ((access rewrite-constant
                 (access prove-spec-var pspv :rewrite-constant)
                 :nonlinearp)
         (if (not (equal (caar hist) 'SETTLED-DOWN-CLAUSE))
             (prog2$
              (cw "~%~%[Note: We now disable non-linear arithmetic.]~%~%")
              '(:computed-hint-replacement t
                                           :nonlinearp nil))
           nil))
        (t
         nil)))
