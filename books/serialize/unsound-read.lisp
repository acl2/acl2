; Serializing ACL2 Objects
; Copyright (C) 2009 by Centaur Technology 
;
; Contact: Jared Davis <jared@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "SERIALIZE")
(include-book "serialize" :ttags (:serialize))

(defttag :unsound-read)

; We use this stub in the logical definition, so that you can't
; directly reason about the value of unsound-read.

(defstub unsound-read-fn-logical-def (filename honsp verbosep) 
  t)
  
(defun unsound-read-fn (filename honsp verbosep)
  (declare (xargs :guard (and (stringp filename)
                              (booleanp honsp)
                              (booleanp verbosep))))
  (prog2$
   (er hard? 'unsound-read-fn "Raw-lisp definition not installed??")
   (unsound-read-fn-logical-def filename honsp verbosep)))

(defmacro unsound-read (filename &key honsp verbosep)
  `(unsound-read-fn ,filename ,honsp ,verbosep))

#-gcl
(ACL2::progn!
 (set-raw-mode t)
 (let ((f (compile-file
           (ACL2::extend-pathname (cbd) "unsound-read-raw.lsp" state))))
   (ACL2::load-compiled f)))
