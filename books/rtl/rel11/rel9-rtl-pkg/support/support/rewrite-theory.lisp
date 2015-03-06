; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic 
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc. 
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.
;
; This program is distributed in the hope that it will be useful but WITHOUT ANY
; WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
; PARTICULAR PURPOSE.  See the GNU General Public License for more details.
;
; You should have received a copy of the GNU General Public License along with
; this program; see the file "gpl.txt" in this directory.  If not, write to the
; Free Software Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA
; 02110-1335, USA.
;
; Author: David M. Russinoff (david@russinoff.com)

; This little utility, rewrite-theory, was written by Matt Kaufmann.

(in-package "RTL")

(program)

(defun collect-rewrites (runes ans)
  (cond
   ((endp runes) (reverse ans))
   ((eq (caar runes) :rewrite)
    (collect-rewrites (cdr runes) (cons (car runes) ans)))
   (t
    (collect-rewrites (cdr runes) ans))))

(defun rewrite-theory-fn (from to wrld)
; Returns all rewrite rules introduced after FROM, up to and including TO.
  (let ((diff (acl2::set-difference-theories-fn
               (acl2::universal-theory-fn to wrld)
               (acl2::universal-theory-fn from wrld)
               t ;; Tue Oct 31 09:22:52 2006. Hanbing. changed to accomodate
                 ;; the changes in ACL2 3.0.1
               wrld)))
    (collect-rewrites diff nil)))

(defmacro rewrite-theory (from &optional (to ':here))
  ; Returns all rewrite rules introduced after FROM up to and including TO.
  (list 'rewrite-theory-fn from to 'world))

