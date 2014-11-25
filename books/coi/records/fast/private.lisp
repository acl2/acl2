;
; Linear Memories as Binary Trees
; Copyright (C) 2005 by Jared Davis <jared@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.
;
; This program is distributed in the hope that it will be useful, but WITHOUT
; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
; FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
; details.
;
; You should have received a copy of the GNU General Public License along with
; this program; if not, write to the Free Software Foundation, Inc., 675 Mass
; Ave, Cambridge, MA 02139, USA.
;



; private.lisp
;
; This file provides the "private" macro, which is used in memory.lisp to
; provide auxilliary/implementation functions that a user should not be allowed
; to work with directly.  The macro is generic and may be of use to the authors
; of other libraries.

(in-package "MEM")

(include-book "xdoc/top" :dir :system)
(defmacro defxdoc (&rest args)
  `(acl2::defxdoc ,@args))

;;; The following legacy doc string was replaced Nov. 2014 by the
;;; auto-generated defxdoc form just below.
; (defdoc private
;   ":Doc-Section private
;   redundantly define, then serverely restrict the usage of some function~/
;   ~bv[]
;   Example:
;      (private foo (x y) 
;         (if (atom x) 
;             ...))
;   ~ev[]
;   ~c[private] is a macro which may be useful for authors of libraries, or
;   to users who want to enforce severe discipline upon themselves.~/
; 
;   The macro is similar to defund (~l[defund]) in that it first introduces
;   a defun and then immediately disables its definition.  However, ~c[private]
;   goes further -- it also disables the resulting type-prescription rule and 
;   sets up theory invariants that prohibit the user from ever enabling the 
;   definition or the type prescription.
; 
;   Why would we want such a thing?  A nice way to develop libraries is to use
;   redundant definitions (~l[set-enforce-redundancy]) in an interface file, 
;   so that users never even see the local lemmas and so forth that you used
;   to get the proofs to go through.  This gives you the freedom to change 
;   and remove those definitions at will.
; 
;   Unfortunately, you cannot do the same for functions, because ACL2 needs
;   the functions available in the interface book if they are ever used.  With
;   ~c[private], you can identify functions that you want to keep control over
;   and that the user should either (1) not be using at all, or (2) only be
;   reasoning about using the theorems your have provided.
; 
;   To use private, simply copy your ~c[(defun foo ...)] form into your interface
;   file, then replace ~c[defun] with ~c[private].")

(defxdoc mem::private
  :parents (mem::private)
  :short "Redundantly define, then serverely restrict the usage of some function"
  :long "@({
  Example:
     (private foo (x y)
        (if (atom x)
            ...))
 })

 <p>@('private') is a macro which may be useful for authors of libraries, or to
 users who want to enforce severe discipline upon themselves.</p>

 <p>The macro is similar to defund (See @(see defund)) in that it first
 introduces a defun and then immediately disables its definition.  However,
 @('private') goes further -- it also disables the resulting type-prescription
 rule and sets up theory invariants that prohibit the user from ever enabling
 the definition or the type prescription.</p>

 <p>Why would we want such a thing?  A nice way to develop libraries is to use
 redundant definitions (See @(see set-enforce-redundancy)) in an interface
 file, so that users never even see the local lemmas and so forth that you used
 to get the proofs to go through.  This gives you the freedom to change and
 remove those definitions at will.</p>

 <p>Unfortunately, you cannot do the same for functions, because ACL2 needs the
 functions available in the interface book if they are ever used.  With
 @('private'), you can identify functions that you want to keep control over
 and that the user should either (1) not be using at all, or (2) only be
 reasoning about using the theorems your have provided.</p>

 <p>To use private, simply copy your @('(defun foo ...)') form into your
 interface file, then replace @('defun') with @('private').</p>")

(defmacro private (&rest def)
  (declare (xargs :guard (and (true-listp def)
                              (symbolp (car def))
                              (symbol-listp (cadr def)))))
  `(progn 

     ;; First introduce the function itself
     (defun ,@def)

     ;; Now disable the :definition and :type-prescription rules
     (with-output :off summary 
                  (in-theory (disable (:definition ,(car def))
                                      (:type-prescription ,(car def)))))

     ;; Now create a theory invariant named foo-is-private, which will cause an
     ;; error if the user ever tries to enable these rules
     (with-output :off summary
                  (theory-invariant 
                   (and (not (active-runep '(:definition ,(car def))))
			(not (active-runep '(:type-prescription ,(car def)))))
                   :key ,(intern-in-package-of-symbol
                          (concatenate 'string (symbol-name (car def))
                                       "-IS-PRIVATE")
                          (car def))))

     ;; And finally just use the name of the function as our return value
     (ACL2::value-triple ',(car def))))
