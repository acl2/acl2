; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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

; There doesn't seem to be any mechanism for just printing the contents of a
; string without any formatting using cw.  Using ~s mostly works, but it will
; insert its own line breaks.  Using ~f fixes that, but puts quotes around the
; string.  So, here we introduce a routine that just prints the contents of a
; string without any automatic line breaks and without the surrounding quotes.
; This can be combined usefully with our printer (see print.lisp).

(defun cw-unformatted (x)
  (declare (xargs :guard (stringp x))
           (ignore x))
  (er hard? 'cw-unformatted "Raw lisp definition not installed?"))

(defttag cw-unformatted)
(progn!
 (set-raw-mode t)
 (defun cw-unformatted (x)
   (write-string x)
   nil))
(defttag nil)


#|| 
;; Alternate implementation doesn't need a trust tag...

(defun cw-princ$ (str)
  ;; Same as princ$ to *standard-co*, but doesn't require state.
  (declare (xargs :guard t))
  (mbe :logic nil
       :exec
       (wormhole 'cw-raw-wormhole
                 '(lambda (whs) whs)
                 nil
                 `(let ((state (princ$ ',str *standard-co* state)))
                    (value :q))
                 :ld-prompt nil
                 :ld-pre-eval-print nil
                 :ld-post-eval-print nil
                 :ld-verbose nil)))


||#