; compact-print.lisp
; Copyright (C) 2011  University of Texas at Austin

; This program is free software; you can redistribute it and/or modify it under
; the terms of Version 2 of the GNU General Public License as published by the
; Free Software Foundation.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

(in-package "ACL2")
; (depends-on "compact-print-raw.lsp")

; compact-print.lisp
;
; This file is DEPRECATED.  It is provided only so that former users of
; compact-print and compact-read can still access them.
;
; This file was derived from the original Hons and Memoization code developed
; by Bob Boyer and Warren Hunt.  This code was formerly part of the
; experimental Hons version of ACL2.
;
; Jared split these functions out of memoize-raw.lisp when he added the new
; serialization code to ACL2.  He suggests using the new ACL2 commands
; serialize-read and serialize-write instead of these routines.

(include-book "tools/include-raw" :dir :system)


(make-event
 (prog2$ (cw "Note: Using compact-print is deprecated; see :doc serialize ~
              for a replacement.~%")
         '(value-triple :invisible))
 :check-expansion t)


(defttag compact-print)
(include-raw "compact-print-raw.lsp")


#||

; Well, it seems to work...

(include-book ;; newline to fool dependency scanner
 "compact-print")

:q

(let* ((x (cons 1 2))
       (y (cons x x)))
  (compact-print-file y "foo"))

(compact-read-file "foo")

||#