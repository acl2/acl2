; ACL2 Parser for Java
; Copyright (C) 2013 Battelle Memorial Institute
;
; Contact:
;  David Rager, ragerdl@cs.utexas.edu
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
; Original author: David Rager <ragerdl@cs.utexas.edu>

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)
(include-book "std/util/bstar" :dir :system)

(defmacro defprimitive (name args body &key default parents short long)
  (b* ((xdoc::mksym-package-symbol
        (if (equal (symbol-package-name name) "COMMON-LISP")
            'ACL2::an-obscure-symbol-that-should-never-be-used-787
          name)))
    `(progn
       (defsection ,name
         :parents ,parents
         :short ,short
         :long ,long

         (defnd ,(xdoc::mksym name '-p) ,args
           ,body)
         (defnd ,(xdoc::mksym 'make- name) ()
           ,default)))))

(local
 (defprimitive foo (x)
   (and (integerp x)
        (> x 4))
   :default 7))
