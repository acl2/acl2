; set-defuns.lisp -- definitions in the theory of sets
; Copyright (C) 1997  Computational Logic, Inc.

; This book is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This book is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this book; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:  Bill Bevier (bevier@cli.com)
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

(in-package "ACL2")

; 
; This theory includes functions which treat lists as sets. 
; In the theory of lists and the theory of alists, we 
; provide three versions of each function based on three different
; notions of equality: EQL, EQ and EQUAL. In this theory, however,
; we provide only the EQUAL version. The main reason for this is 
; mundane: Many of the function names (e.g. UNION and INTERSECTION)
; are not defined in ACL2, but are blocked from our use because they're 
; in the Common Lisp package.

; ------------------------------------------------------------
; Functions
; ------------------------------------------------------------

; Function Name            In    Result 
;   (supporting function)  ACL2  Type
; ----------------------   ----  -----
;
; adjoin-equal             N     set
; intersection-equal       N     set
; set-difference-equal     Y     set
; union-equal              Y     set
; 
; memberp-equal            N     boolean
; subsetp-equal            Y     boolean
; set-equal                N     boolean
; setp-equal               N     boolean

(defun adjoin-equal (x l)
  (declare (xargs :guard (true-listp l)))
  (if (member-equal x l)
      l
    (cons x l)))

(defun memberp-equal (x l)
  (DECLARE (XARGS :GUARD (TRUE-LISTP L)))
  (consp (member-equal x l)))

; Intersection-equal was added to ACL2 in Version 4.0.

(defun set-equal (a b)
  (declare (xargs :guard (and (true-listp a)
			      (true-listp b))))
  (and (subsetp-equal a b)
       (subsetp-equal b a)))

(defun setp-equal (l)
  (declare (xargs :verify-guards t))
  (and (true-listp l)
       (no-duplicatesp-equal l)))


